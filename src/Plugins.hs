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
      return [CoreDoPluginPass "Implementing functions" implementFuns]
      -- Doesn't work:
      -- return (CoreDoPluginPass "Implementing functions" implementFuns : todos)
      -- Doesn't work:
      -- return (todos ++ [CoreDoPluginPass "Implementing functions" implementFuns])

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
                                                  [Var (instanceDFunId intNumInst)
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

       scrtBinder1 <- newLocalId "scrt1" intTy
       scrtBinder2 <- newLocalId "scrt2" intTy

       dflags <- getDynFlags
       let int1 = mkIntExprInt dflags 1

       int1Binder <- newLocalId "int1" intTy
       recCallId  <- newLocalId "rec" intTy

       let argMinusOne = mkApps (Var minusId)
                                [ Var (instanceDFunId intNumInst)
                                , Var arg
                                , Var int1Binder ]

           recCall     = mkApps (Var bndr) [ argMinusOne ]

           argTimesRec =
             Let (NonRec int1Binder int1) $
               Let (NonRec recCallId recCall) $
                 mkApps (Var multId)
                        [ Var (instanceDFunId intNumInst)
                        , Var arg
                        , Var recCallId ]


       argInt <- newLocalId "i" intPrimTy

       let intLitAlts = [ (DEFAULT, [], argTimesRec)
                        , (LitAlt (MachInt 0), [], int1)
                        ]
           compareIntLitCase = Case (Var argInt) scrtBinder2 intTy intLitAlts
           compareIntAlt = (DataAlt intDataCon, [argInt], compareIntLitCase)


       let caseAlts = [ compareIntAlt ]
           caseExpr = Case (Var arg) scrtBinder1 intTy caseAlts

       return $ Rec [(bndr, Lam arg caseExpr)]

implementFac _ bndr = return bndr

--------------------------------------------------------------------------------
-- * Utils

newLocalId :: String -> Type -> CoreM Id
newLocalId str ty = do
    uniq <- getUniqueM
    return (mkSysLocal (mkFastString str) uniq ty)
