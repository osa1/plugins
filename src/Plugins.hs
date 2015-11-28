{-# LANGUAGE TupleSections #-}

module Plugins (plugin) where

--------------------------------------------------------------------------------

import           Class                 (classMethods)
import           CoreLint              (lintPassResult)
import           GhcPlugins
import           InstEnv               (instanceDFunId)
import           PrelNames             (numClassName)
import           TcEnv                 (tcLookupClass, tcLookupInstance)
import           TcRnMonad             (initTcForLookup)
import           TysPrim               (intPrimTy)

import           Control.Monad

import qualified Data.ByteString       as BS
import qualified Data.ByteString.Char8 as BSC

--------------------------------------------------------------------------------

plugin :: Plugin
plugin = defaultPlugin{installCoreToDos = installPlugin}
  where
    installPlugin :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
    installPlugin _ todos = do
      liftIO $ putStrLn "installing the plugin"
      pprTrace "TODOs:" (ppr todos) (return ())
      return ( CoreDoPluginPass "Implementing functions" implementFuns
             : CoreDoPluginPass "Evaluate unlines" evalUnlines
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
evalUnlines guts@ModGuts{ mg_binds = binds, mg_rdr_env = rdrEnv } = do
    liftIO $ putStrLn "Evaluating unlines..."
    binds' <- mapM evalUnlines' binds
    lint (CoreDoPluginPass "Evaluate unlines" evalUnlines) binds'
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
