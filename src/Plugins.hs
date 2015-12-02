{-# LANGUAGE TupleSections #-}

module Plugins (plugin) where

--------------------------------------------------------------------------------

import           Class                 (classMethods)
import           CoreLint              (lintPassResult)
import           GhcPlugins
import           InstEnv               (instanceDFunId)
import           MkId                  (unsafeCoerceId)
import           PprCore
import           PrelNames             (numClassName)
import           TcEnv                 (tcLookupClass, tcLookupInstance)
import           TcRnMonad             (initTcForLookup)
import           TysPrim               (intPrimTy)

import           Control.Monad

import qualified Data.ByteString       as BS
import qualified Data.ByteString.Char8 as BSC

--------------------------------------------------------------------------------
-- Some problems with plugins:
--
-- - It's not possible to run a plugin pass _after_ CorePrep.
-- - It's not possible to run a plugin pass _before_ RULEs apply.
-- - Apparently there are different Desugarer passes, one of them does
--   optimizations <- investigate this further.

plugin :: Plugin
plugin = defaultPlugin{installCoreToDos = installPlugin}
  where
    installPlugin :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
    installPlugin _ todos = do
      liftIO $ putStrLn "installing the plugin"
      pprTrace "TODOs:" (ppr todos) (return ())
      return ( CoreDoPluginPass "Implementing functions" implementFuns
             : CoreDoPluginPass "Evaluate unlines" evalUnlines
             : CoreDoPluginPass "Remove rebuilding" removeRebuilding
             -- TODO: Figure out why removing rest of the TODOs are causing a
             -- linker error.
             -- (I think only happens when `removeRebuilding` is used)
             -- : []
             : todos
             )

--------------------------------------------------------------------------------

applyActions :: Monad m => [a -> m a] -> a -> m a
applyActions []         a = return a
applyActions (ac : acs) a = ac a >>= applyActions acs

implementFuns :: ModGuts -> CoreM ModGuts
implementFuns guts@ModGuts{ mg_binds = binds, mg_rdr_env = rdrEnv } = do
    liftIO $ putStrLn "Implementing functions..."
    binds' <- applyActions [mapM (implementAddOne rdrEnv), mapM (implementFac rdrEnv)] binds
    hscEnv <- getHscEnv
    lint (CoreDoPluginPass "Implementing functions" implementFuns) binds'
    return guts{ mg_binds = binds' }

evalUnlines :: ModGuts -> CoreM ModGuts
evalUnlines guts@ModGuts{ mg_binds = binds } = do
    liftIO $ putStrLn "Evaluating unlines..."
    pprTrace "evalUnllines" (pprCoreBindingsWithSize binds) (return ())
    binds' <- mapM evalUnlines' binds
    lint (CoreDoPluginPass "Evaluate unlines" evalUnlines) binds'
    return guts{ mg_binds = binds' }

removeRebuilding :: ModGuts -> CoreM ModGuts
removeRebuilding guts@ModGuts{ mg_binds = binds } = do
    liftIO $ putStrLn "Trying to remove rebuilding..."
    -- pprTrace "removeRebuilding" (pprCoreBindingsWithSize binds) (return ())
    binds' <- mapM rmrBinds binds
    lint (CoreDoPluginPass "Remove rebuilding" removeRebuilding) binds'
    return guts{ mg_binds = binds' }

lint :: CoreToDo -> CoreProgram -> CoreM ()
lint pass pgm = do
    hscEnv <- getHscEnv
    liftIO $ lintPassResult hscEnv pass pgm

--------------------------------------------------------------------------------

implementAddOne :: GlobalRdrEnv -> CoreBind -> CoreM CoreBind

implementAddOne rdrEnv (NonRec bndr _)
  | isId bndr
  , "addOne" <- occNameString (nameOccName (varName bndr))
  = do hscEnv <- getHscEnv
       arg <- newLocalId "i" intTy

       -------------------------------------------------------------------------
       -- One way of finding (+): Using RdrEnv

       -- let plusOccName = mkVarOcc "+"

       -- plusName :: Name <- case lookupOccEnv rdrEnv plusOccName of
       --   Just rdrElts ->
       --     case filter ((==) "+" . occNameString . getOccName . gre_name) rdrElts of
       --       [] -> error "Can't find plus"
       --       [x] -> return (gre_name x)
       --       _ -> error "Found more than one plus"
       --   Nothing -> error "Can't find plus"

       -- plusId <- liftIO (initTcForLookup hscEnv (tcLookupId plusName))

       -------------------------------------------------------------------------

       numClass   <- liftIO (initTcForLookup hscEnv (tcLookupClass numClassName))
       intNumInst <- liftIO (initTcForLookup hscEnv (tcLookupInstance numClass [intTy]))

       -------------------------------------------------------------------------
       -- Probably a better way of finding (+): Search it in Num class

       let methods  = classMethods numClass
           [plusId] = filter ((==) "+" . occNameString . nameOccName . varName) methods

       -------------------------------------------------------------------------

       dflags <- getDynFlags
       let int1 = mkIntExprInt dflags 1

       return $ NonRec bndr $ Lam arg $
                  mkApps (Var plusId) [Type intTy, Var (instanceDFunId intNumInst), int1, Var arg]

implementAddOne _ b = return b

--------------------------------------------------------------------------------

implementFac :: GlobalRdrEnv -> CoreBind -> CoreM CoreBind
implementFac rdrEnv (NonRec bndr _)
  | isId bndr
  , "factorial" <- occNameString (nameOccName (varName bndr))
  = do hscEnv <- getHscEnv
       arg <- newLocalId "i" intTy

       -------------------------------------------------------------------------

       numClass   <- liftIO (initTcForLookup hscEnv (tcLookupClass numClassName))
       intNumInst <- liftIO (initTcForLookup hscEnv (tcLookupInstance numClass [intTy]))

       let methods   = classMethods numClass
           [multId]  = filter ((==) "*" . occNameString . nameOccName . varName) methods
           [minusId] = filter ((==) "-" . occNameString . nameOccName . varName) methods

       -------------------------------------------------------------------------

       -- binder for first case expression on Int
       scrt1Binder <- newLocalId "scrt1" intTy
       -- binder for second case expression on Int's argument
       scrt2Binder <- newLocalId "scrt2" intPrimTy
       -- these are not used, just to put something in Case's second argument

       dflags <- getDynFlags
       let int1 = mkIntExprInt dflags 1

       let argMinusOne =
             mkApps (Var minusId)
               [ Type intTy, Var (instanceDFunId intNumInst), Var arg, int1 ]

           recCall =
             mkApps (Var bndr) [ argMinusOne ]

           argTimesRec =
             mkApps (Var multId)
               [ Type intTy, Var (instanceDFunId intNumInst), Var arg, recCall ]

       argInt <- newLocalId "i" intPrimTy

       let intLitAlts = [ (DEFAULT, [], argTimesRec)
                        , (LitAlt (mkMachInt dflags 0), [], int1)
                        ]

           -- case i of ...
           compareIntLitCase = Case (Var argInt) scrt2Binder intTy intLitAlts
           -- compareIntLitCase = mkWildCase (Var argInt) intPrimTy intTy intLitAlts

           -- I# i -> ...
           compareIntAlt = (DataAlt intDataCon, [argInt], compareIntLitCase)


       let caseAlts = [ compareIntAlt ]

           -- case arg of ...
           caseExpr = Case (Var arg) scrt1Binder intTy caseAlts
           -- caseExpr = mkWildCase (Var arg) intTy intTy caseAlts

       return $ Rec [(bndr, Lam arg caseExpr)]

implementFac _ bndr = return bndr

--------------------------------------------------------------------------------

evalUnlines' :: CoreBind -> CoreM CoreBind
evalUnlines' (NonRec bndr rhs) = NonRec bndr <$> evalUnlinesExpr rhs
evalUnlines' (Rec bs)          = Rec <$> mapM (\(bndr, rhs) -> (bndr,) <$> evalUnlinesExpr rhs) bs

evalUnlinesExpr :: CoreExpr -> CoreM CoreExpr
evalUnlinesExpr e@Var{} = return e
evalUnlinesExpr e@Lit{} = return e

evalUnlinesExpr e@(App (Var v) arg)
  | occNameString (nameOccName (varName v)) == "unlines"
  = do liftIO (putStrLn "Found a unlines!")
       case tryCollectList arg of

         Just listArgs -> do
           pprTrace "list args:" (ppr listArgs) (return ())
           case mapM tryExtractString listArgs of
             Nothing -> return e
             Just ss -> do
               pprTrace "strings:" (hsep . map pprHsBytes $ ss) (return ())
               mkStringExprFS $ mkFastStringByteString $ BS.intercalate (BSC.pack "\n") ss

         Nothing -> do
           pprTrace "can't parse list args" empty (return e)

evalUnlinesExpr (App e1 e2)    = App <$> evalUnlinesExpr e1 <*> evalUnlinesExpr e2
evalUnlinesExpr (Lam arg body) = Lam arg <$> evalUnlinesExpr body
evalUnlinesExpr (Let bs body)  = Let <$> evalUnlines' bs <*> evalUnlinesExpr body
evalUnlinesExpr (Case scrt bndr ty alts) = do
    scrt' <- evalUnlinesExpr scrt
    alts' <- mapM evalUnlinesAlt alts
    return $ Case scrt' bndr ty alts'
evalUnlinesExpr (Cast e c) = Cast <$> evalUnlinesExpr e <*> pure c
evalUnlinesExpr (Tick t e) = Tick t <$> evalUnlinesExpr e
evalUnlinesExpr e@Type{} = return e
evalUnlinesExpr e@Coercion{} = return e

evalUnlinesAlt :: CoreAlt -> CoreM CoreAlt
evalUnlinesAlt = return

--------------------------------------------------------------------------------
-- | There's a very surprising inefficiency in GHC generated code. Suppose we
-- have this Either implementation:
--
--   data Either1 a b = Left1 a | Right1 b
--
--   instance Functor (Either1 a) where
--     fmap _ (Left1 a)  = Left1 a
--     fmap f (Right1 a) = Right1 (f a)
--
-- First case of `fmap` allocates a new `Left1` whenever it's applied! We can't
-- manually eliminate this because second argument of `fmap` and RHS of this
-- function has different types(`Either a b` and `Either a c` respectively).
-- Core-to-Core "common subexpression elimination" pass can't do anything,
-- because internally there's no "common subexpression":
--
--   -- RHS size: {terms: 14, types: 17, coercions: 0}
--   Main.$fFunctorEither1_$cfmap
--     :: forall a_aOH a1_avU b_avV.
--        (a1_avU -> b_avV) -> Either1 a_aOH a1_avU -> Either1 a_aOH b_avV
--   Main.$fFunctorEither1_$cfmap =
--     \ (@ a_aOH) (@ a1_aOL) (@ b_aOM)
--       (ds_dR3 :: a1_aOL -> b_aOM) (ds1_dR4 :: Either1 a_aOH a1_aOL) ->
--       case ds1_dR4 of _ {
--         Left1 x_avi -> Main.Left1 @ a_aOH @ b_aOM x_avi;
--         Right1 y_avk -> Main.Right1 @ a_aOH @ b_aOM (ds_dR3 y_avk)
--       }
--
-- Relevant Trac ticket: https://ghc.haskell.org/trac/ghc/ticket/9291
--
-- In this very simple pass we just pattern-match against this very specific
-- case, and use an `unsafeCoerce#` instead of building same value with
-- different type. This is a PoC.
--
rmrBinds :: CoreBind -> CoreM CoreBind
rmrBinds (NonRec bndr rhs) =
    NonRec bndr <$> rmrExpr rhs
rmrBinds (Rec bndrs)       =
    Rec <$> mapM (\(bndr, rhs) -> (bndr,) <$> rmrExpr rhs) bndrs

rmrExpr :: CoreExpr -> CoreM CoreExpr
rmrExpr e@Var{} = return e

rmrExpr e@Lit{} = return e

rmrExpr (App e1 e2) =
    App <$> rmrExpr e1 <*> rmrExpr e2

rmrExpr (Lam arg body) = Lam arg <$> rmrExpr body

rmrExpr (Let binds body) = Let <$> rmrBinds binds <*> rmrExpr body

rmrExpr e@(Case scrt bndr ty alts) = do
    scrt' <- rmrExpr scrt

    used_bndr <- newLocalId "rmr" (idType bndr)

    (alts', updateOccInfo_) <- unzip <$> mapM (rmrAlt (idType bndr) used_bndr ty) alts

    let updateOccInfo = or updateOccInfo_
    let bndr' = if updateOccInfo then used_bndr else bndr
    let ret = Case scrt' bndr' ty alts'

    -- FIXME: This pass works fine, but annoyingly some Core-to-Core pass later
    -- reverse our transformation. As an example, the next line prints this:
    --
    --   case ds_d33s of rmr_s34I {
    --     Nothing1 ->
    --       unsafeCoerce# @ (Maybe1 a_a2fs) @ (Maybe1 b_a2ft) rmr_s34I;
    --     Just1 a_aKP -> Just1 @ b_a2ft (ds_d33r a_aKP)
    --   }
    --
    -- Which is exactly what we're expecting. But -ddump-simpl prints this:
    --
    --   case ds_d33s of _ [Occ=Dead] {
    --     Nothing1 ->
    --       (Main.Nothing1 @ b_a33M)
    --       `cast` ((Maybe1
    --                  (UnivCo mkUnsafeCo representational b_a33M a1_a33L))_R
    --               :: Maybe1 b_a33M ~R# Maybe1 a1_a33L);
    --     Just1 a2_aKP -> Main.Just1 @ a1_a33L eta_a33N
    --     }
    --
    -- What kind of transformation could do that? This I have no ideas.
    --
    -- Works fine for some other types, like 'Either'.
    --
    -- To be explored later.
    --
    when updateOccInfo $
      pprTrace "rmrExpr" (text "before:" <+> ppr e $$
                          text "after:" <+> ppr ret) (return ())

    return ret

rmrExpr (Cast expr c) = Cast <$> rmrExpr expr <*> pure c

rmrExpr (Tick t e) = Tick t <$> rmrExpr e

rmrExpr e@Type{} = return e

rmrExpr e@Coercion{} = return e

rmrAlt :: Type -> CoreBndr -> Type -> CoreAlt -> CoreM (CoreAlt, Bool)
rmrAlt lhs_ty lhs_bndr expr_ty alt@(DataAlt lhs_con, bndrs, rhs)
  | (Var f, args) <- collectArgs rhs
  , let non_ty_args = dropWhile isTypeArg args
  , Just rhs_con  <- isDataConWorkId_maybe f
  , lhs_con == rhs_con
  , length bndrs == length non_ty_args
  , collectIds non_ty_args == bndrs
  = return ((DataAlt lhs_con, bndrs, mkUnsafeCoerce lhs_ty expr_ty (Var lhs_bndr)),
             True)

  | otherwise
  = return (alt, False)

  where
    collectIds :: [CoreExpr] -> [Id]
    collectIds exprs = [ v | Var v <- exprs ]

occ_to_use = OneOcc False False False

mkUnsafeCoerce :: Type -> Type -> CoreExpr -> CoreExpr
mkUnsafeCoerce from to arg = mkApps (Var unsafeCoerceId) [ Type from, Type to, arg ]

--------------------------------------------------------------------------------
-- * Utils

newLocalId :: String -> Type -> CoreM Id
newLocalId str ty = do
    uniq <- getUniqueM
    return (mkSysLocal (mkFastString str) uniq ty)

tryCollectList :: CoreExpr -> Maybe [CoreExpr]
tryCollectList e@App{}
  | (Var v, [_typeArgument, arg1, arg2]) <- collectArgs e
  , occNameString (nameOccName (varName v)) == ":"
  = (arg1 :) <$> tryCollectList arg2

  | (Var v, [_typeArgument]) <- collectArgs e
  , occNameString (nameOccName (varName v)) == "[]"
  = Just []

tryCollectList e = Nothing

tryExtractString :: CoreExpr -> Maybe BS.ByteString
tryExtractString (App (Var v) (Lit (MachStr bs)))
  | occNameString (nameOccName (varName v)) == "unpackCString#"
  = Just bs
tryExtractString _ = Nothing
