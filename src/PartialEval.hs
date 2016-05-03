{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving, LambdaCase,
             TupleSections #-}

module PartialEval where

import           GhcPlugins
import           SimplCore

-- FIXME: This is not exported by GHC HEAD.
import           TrieMap

import           Data.Bifunctor              (second)
import           Data.List                   (find)

import           Control.Monad.Reader
import           Control.Monad.State.Strict
import           Control.Monad.Writer.Strict

peval :: ModGuts -> CoreM ModGuts
peval guts@ModGuts{ mg_binds = binds } = do
    (binds', _) <- peval_pgm binds -- FIXME
    return guts{ mg_binds = binds' }

-- | A specialized function value in the map of function specializations.
data SpecFn = SpecFn
  { _args :: !(VarEnv (DeBruijn CoreExpr))
      -- ^ Map from static arguments to their values in the specialized function
  , _spec :: !Id
      -- ^ Id of the function specialized to the arguments in the map
  }

-- TODO: Ideally, this would be a map from (Var, VarEnv CoreExpr) to Ids, but
-- that's tricky as we don't have any instances for VarEnv. So after looking up
-- the function Id here, we do linear search to find the specialized function.
type PEvalState = VarEnv [SpecFn]

newtype RevList a = RevList [a]

rev :: RevList a -> [a]
rev (RevList lst) = reverse lst

registerTopFn :: MonadWriter (RevList CoreBind) w => CoreBind -> w ()
registerTopFn bind = tell (RevList [bind])

instance Monoid (RevList a) where
    mempty = RevList []
    mappend (RevList lst1) (RevList lst2) = RevList (lst2 ++ lst1)

newtype PE a = PE { unwrapPE ::
                      StateT PEvalState
                        (ReaderT [CoreBind]
                          (WriterT (RevList CoreBind) CoreM)) a }
  deriving (Functor, Applicative, Monad,
            MonadState PEvalState,
            MonadReader [CoreBind],
            MonadWriter (RevList CoreBind),
            MonadIO)

instance MonadUnique PE where
    getUniqueSupplyM = PE (lift (lift (lift getUniqueSupplyM)))

instance HasDynFlags PE where
    getDynFlags = PE (lift (lift (lift getDynFlags)))

peval_pgm :: [CoreBind] -> CoreM ([CoreBind], RevList CoreBind)
peval_pgm binds =
    runWriterT $
      runReaderT
        (evalStateT (unwrapPE (mapM peval_top_bind binds)) emptyVarEnv)
        binds

peval_top_bind :: CoreBind -> PE CoreBind
peval_top_bind (NonRec bndr rhs) = NonRec bndr <$> peval_expr rhs
peval_top_bind (Rec binds)       = Rec <$> mapM (\(bndr, rhs) -> (bndr,) <$> peval_expr rhs) binds

--------------------------------------------------------------------------------
-- Evaluate expression -- the main routine

peval_expr :: CoreExpr -> PE CoreExpr
peval_expr app@App{}
  = do let (fn0, as0) = collectArgs app
       fn <- peval_expr fn0
       as <- mapM peval_expr as0

       case fn of
         Var v ->
           -- Is this a known function?
           lookupKnownFun v >>= \case
             Nothing -> return (mkApps fn as)
             Just (fn_args, rhs) -> do
               let
                 arg_binds, static_arg_binds, dynamic_arg_binds :: [(Id, CoreExpr)]
                 arg_binds = zipErr fn_args as
                 (static_arg_binds, dynamic_arg_binds) = span (isValue . snd) arg_binds

               if null dynamic_arg_binds
                 then do
                   let ret = mkApps fn as
                   pprTrace "peval_expr"
                     (text "Found app with static args:" $$ ppr ret)
                     (return ret)

                 else do
                   -- Do we have a specialization for these static args?
                   specs_map <- get
                   case lookupVarEnv specs_map v of
                     Nothing -> do
                       (spec_fn_id, spec_fn_bind) <- specialize v (fn_args, rhs) as static_arg_binds
                       return (mkApps (Var spec_fn_id) (map snd dynamic_arg_binds))

                     Just specs -> do
                       let args_map = mkVarEnv (map (second deBruijnize) static_arg_binds)
                       case find (\SpecFn { _args = spec_args } -> spec_args == args_map) specs of
                         Nothing -> do
                           (spec_fn_id, spec_fn_bind)
                             <- specialize v (fn_args, rhs) as static_arg_binds
                           return (mkApps (Var spec_fn_id) (map snd dynamic_arg_binds))

                         Just (SpecFn { _spec = spec }) ->
                           return (mkApps (Var spec) (map snd dynamic_arg_binds))

         _ -> return (mkApps fn as)

peval_expr e@Var{}
  = return e

peval_expr e@Lit{}
  = return e

peval_expr (Lam arg body)
  = Lam arg <$> peval_expr body

peval_expr (Let bs body)
  = Let <$> peval_top_bind bs <*> peval_expr body

peval_expr (Case scrt b ty alts)
  = Case <$> peval_expr scrt <*> pure b <*> pure ty <*> peval_alts alts

peval_expr (Cast expr co)
  = Cast <$> peval_expr expr <*> pure co

peval_expr (Tick tick expr)
  = Tick tick <$> peval_expr expr

peval_expr e@Type{}
  = return e

peval_expr e@Coercion{}
  = return e

peval_alts :: [CoreAlt] -> PE [CoreAlt]
peval_alts = mapM peval_alt

peval_alt :: CoreAlt -> PE CoreAlt
peval_alt (lhs, bndrs, rhs) = (lhs, bndrs,) <$> peval_expr rhs

--------------------------------------------------------------------------------

specialize :: Id -> ([Id], CoreBind) -> [CoreExpr] -> [(Id, CoreExpr)] -> PE (Id, CoreBind)
specialize orig_fn_id (fn_args, rhs) all_args static_arg_binds = do
    let
      orig_fn_ty = varType orig_fn_id
      new_fn_ty  = dropStaticArgTys all_args orig_fn_ty
    spec_fn_id <- mkSysLocalM (mkFastString (getOccString (idName orig_fn_id))) new_fn_ty

    modify (\specs_map ->
            extendVarEnv specs_map orig_fn_id
              [SpecFn (mkVarEnv (map (second deBruijnize) static_arg_binds)) spec_fn_id])

    -- specialize (simplify the function body using static arguments)
    dflags <- getDynFlags
    spec_fun_rhs <-
      liftIO (simplifyCoreBind dflags (substStaticArgs (mkVarEnv static_arg_binds) rhs))
    spec_fun_rhs' <- peval_top_bind spec_fun_rhs

    registerTopFn spec_fun_rhs'

    return (spec_fn_id, spec_fun_rhs')

--------------------------------------------------------------------------------

isValue :: CoreExpr -> Bool
isValue = undefined

--------------------------------------------------------------------------------

dropStaticArgTys :: [CoreExpr] -> Type -> Type
dropStaticArgTys args ty =
    let (arg_tys, ret_ty) = splitFunTys ty
     in if length arg_tys /= length args
          then pprPanic "dropStaticArgTys"
                 (text "arg_tys:" <+> ppr arg_tys $$
                  text "args:" <+> ppr args)
          else mkFunTys (go (zip args arg_tys)) ret_ty
  where
    go [] = []
    go ((arg, arg_ty) : rest)
      | isValue arg = go rest
      | otherwise   = arg_ty : go rest

--------------------------------------------------------------------------------

-- need to drop args too
substStaticArgs :: VarEnv CoreExpr -> CoreBind -> CoreBind
substStaticArgs statics (NonRec b rhs)
  = NonRec b (substStaticArgs_rhs statics rhs)
substStaticArgs statics (Rec bs)
  = Rec (map (\(b, rhs) -> (b, substStaticArgs_rhs statics rhs)) bs)

substStaticArgs_rhs :: VarEnv CoreExpr -> CoreExpr -> CoreExpr
substStaticArgs_rhs statics e0 = go e0
  where
    go e@(Var v)
      | Just e' <- lookupVarEnv statics v
      = e'
      | otherwise
      = e

    go e@Lit{}
      = e

    go (App e1 e2)
      = App (go e1) (go e2)

    go (Lam arg body)
      | arg `elemVarEnv` statics
      = go body
      | otherwise
      = Lam arg (go body)

    go (Let b e)
      = Let (go_bind b) (go e)

    go (Case scrt b ty alts)
      = Case (go scrt) b ty (go_alts alts)

    go (Cast e co)
      = Cast (go e) co

    go (Tick tick e)
      = Tick tick (go e)

    go e@Type{}
      = e

    go e@Coercion{}
      = e

    go_bind :: CoreBind -> CoreBind
    go_bind = substStaticArgs statics

    go_alts :: [CoreAlt] -> [CoreAlt]
    go_alts = map go_alt

    go_alt (lhs, bndrs, rhs)
      = (lhs, bndrs, go rhs)

--------------------------------------------------------------------------------

simplifyCoreBind :: DynFlags -> CoreBind -> IO CoreBind
simplifyCoreBind dflags (NonRec bndr rhs)
  = NonRec bndr <$> simplifyExpr dflags rhs
simplifyCoreBind dflags (Rec bndrs)
  = Rec <$> mapM (\(bndr, rhs) -> (bndr,) <$> simplifyExpr dflags rhs) bndrs

-- | Return arguments of the function and its definition.
lookupKnownFun :: Id -> PE (Maybe ([Id], CoreBind))
lookupKnownFun var = do
    binds <- ask
    return (searchFun binds)
  where
    searchFun :: [CoreBind] -> Maybe ([Id], CoreBind)
    searchFun [] = Nothing

    searchFun (b@(NonRec bndr rhs) : rest)
      | bndr == var = Just (collectLamArgs rhs, b)
      | otherwise   = searchFun rest

    searchFun (b@(Rec ((bndr, rhs) : _)) : rest)
      | bndr == var = Just (collectLamArgs rhs, b)
      | otherwise   = searchFun rest

    searchFun (Rec [] : _)
      = pprPanic "searchFun" (text "Rec with empty list of bindings")

collectLamArgs :: CoreExpr -> [Id]
collectLamArgs (Lam b rhs)
  = b : collectLamArgs rhs
collectLamArgs _
  = -- I think in practice we can be a bit more flexible and collect args in
    -- cases like
    --
    --   let x = ...
    --    in \y -> ...
    []

--------------------------------------------------------------------------------

zipErr :: [a] -> [b] -> [(a, b)]
zipErr [] []
  = []
zipErr (x : xs) (y : ys)
  = (x, y) : zipErr xs ys
zipErr _ _
  = error "zipErr"
