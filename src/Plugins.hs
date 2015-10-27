{-# LANGUAGE CPP, LambdaCase, ScopedTypeVariables #-}

module Plugins (plugin) where

--------------------------------------------------------------------------------

import           Class         (classMethods)
import           CoreLint      (lintPassResult)
import           GhcPlugins
import           InstEnv       (instanceDFunId)
import           PrelNames     (numClassName)
import           TcEnv         (tcLookupClass, tcLookupInstance)
import           TcRnMonad     (initTcForLookup)
import           TysPrim       (intPrimTy)

import           Control.Monad

--------------------------------------------------------------------------------

plugin :: Plugin
plugin = defaultPlugin{installCoreToDos = installPlugin}
  where
    installPlugin :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
    installPlugin _ todos = do
      liftIO $ putStrLn "installing the plugin"
      pprTrace "TODOs:" (ppr todos) (return ())
      return (CoreDoPluginPass "Implementing functions" implementFuns : todos)

implementFuns :: ModGuts -> CoreM ModGuts
implementFuns guts@ModGuts{ mg_binds = binds, mg_rdr_env = rdrEnv } = do
    liftIO $ putStrLn "running the plugin"
    binds' <- mapM (implementAddOne rdrEnv >=> implementFac rdrEnv) binds
    hscEnv <- getHscEnv
    liftIO $ lintPassResult hscEnv (CoreDoPluginPass "Implementing functions" implementFuns) binds'
    return guts{ mg_binds = binds' }

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

       -- For some reason this is failing with a panic. The reason might be
       -- int1, which is not let bound. (I don't understand why that might be a
       -- problem, but still)
       -- let app = mkApps (Var plusId) [Var (instanceDFunId intNumInst), int1, Var arg]
       -- return $ NonRec bndr (Lam arg app)

       -- This is still failing when simplifier runs on this.
       int1Binder <- newLocalId "int1" intTy
       return $ NonRec bndr (Lam arg (Let (NonRec int1Binder int1)
                                          (mkApps (Var plusId)
                                                  [Type intTy
                                                  ,Var (instanceDFunId intNumInst)
                                                  ,Var int1Binder
                                                  ,Var arg])))

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

       let argMinusOne = mkApps (Var minusId)
                                [ Type intTy
                                , Var (instanceDFunId intNumInst)
                                , Var arg
                                , int1 ]

           recCall     = mkApps (Var bndr) [ argMinusOne ]

           argTimesRec =
                 mkApps (Var multId)
                        [ Type intTy
                        , Var (instanceDFunId intNumInst)
                        , Var arg
                        , recCall ]

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
-- * Utils

newLocalId :: String -> Type -> CoreM Id
newLocalId str ty = do
    uniq <- getUniqueM
    return (mkSysLocal (mkFastString str) uniq ty)
