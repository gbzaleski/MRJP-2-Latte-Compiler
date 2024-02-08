{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use when" #-}
{-# HLINT ignore "Use guards" #-}
{-# HLINT ignore "Use newtype instead of data" #-}
{-# HLINT ignore "Use camelCase" #-}

-- Grzegorz B. Zaleski (418494) --

module Compiler where

import Control.Monad.Reader
import Control.Monad.Trans
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Trans.Except
import Data.Functor.Identity ()
import GHC.IO (unsafePerformIO)

import Instruction
import qualified Data.Map as M
import qualified Data.List as DL
import Data.List (intercalate, nub)
import qualified Latte.Abs as L
import Data.Maybe (fromJust, isNothing)
import Text.Printf (printf)
import Data.Char (ord)

---- TYPES -----
data Env = Env {
  env :: M.Map String Var }
    deriving Show

initEnv :: Env
initEnv = Env { env = M.empty }

type TMethod = (Type, String, [Type]) -- (retType fname [args])

data St = St {
  code :: [Instr],
  functions :: M.Map String Type, -- name retType
  classesAttrs :: M.Map String [(Type, String)], -- mapping className to her attributes
  classesMethods :: M.Map String [TMethod], -- mapping className to her methods 
  stringPool :: M.Map String Int,
  classDB :: M.Map String L.TopDef,
  info :: M.Map Loc String, -- extra information on value at registry
  vtInfo :: M.Map Loc String, -- information on vtable referance
  functionsHeader :: M.Map String [Type], -- name argumentTypes
  newLoc :: Int,
  newLabel :: Int,
  current :: Maybe Type, -- for compiling methods
  returnType :: Maybe Type -- for returns
}
  deriving Show

systemFunctions :: M.Map String Type
systemFunctions = M.fromList [
    ("printInt", TVoid),
    ("printString", TVoid),
    ("readInt", TInt),
    ("readString", TString),
    ("error", TVoid)
    ]

systemFunctionsHeader :: M.Map String [Type]
systemFunctionsHeader = M.fromList [
    ("printInt", [TInt]),
    ("printString", [TString]),
    ("readInt", []),
    ("readString", []),
    ("error", [])
    ]

initStat :: St
initStat = St {
    functions = systemFunctions,
    stringPool = M.fromList [("", 0)],
    classesAttrs = M.empty,
    classesMethods = M.empty,
    info = M.empty,
    vtInfo = M.empty,
    functionsHeader = systemFunctionsHeader,
    classDB = M.empty,
    code = [],
    newLoc = 1,
    newLabel = 1,
    current = Nothing,
    returnType = Nothing
}

-- AUXILIARY -- 
lookupf :: Ord k => k -> M.Map k a -> a
lookupf key map = fromJust $ M.lookup key map

appendInstr :: Instr -> St -> St
appendInstr ins oldSt = oldSt {code = code oldSt ++ [ins] }

incLoc :: St -> St
incLoc oldSt = oldSt {newLoc = newLoc oldSt + 1}

incLabel :: St -> St
incLabel oldSt = oldSt {newLabel = newLabel oldSt + 1}

setInfo :: Loc -> String -> St -> St
setInfo loc str oldSt = oldSt {info = M.insert loc str (info oldSt)}

setVTable :: Loc -> String -> St -> St
setVTable loc str oldSt = oldSt {vtInfo = M.insert loc str (vtInfo oldSt)}

setClassDB :: M.Map String L.TopDef -> St -> St
setClassDB db oldSt = oldSt { classDB = db }

setCurrentClass :: Type -> St -> St
setCurrentClass cur oldSt = oldSt { current = Just cur }

setReturn :: Type -> St -> St
setReturn cur oldSt = oldSt { returnType = Just cur }

cBITC_FLAG :: String
cBITC_FLAG = "bitcast_flag"

cSTR_FLAG :: String
cSTR_FLAG = "string_flag"

checkBitCast :: Var -> St -> Bool
checkBitCast (Reg _ loc) st = Just cBITC_FLAG == M.lookup loc (info st)
checkBitCast _ st = False

addNewClass :: String -> St -> St
addNewClass cname oldSt = oldSt {
  classesAttrs = M.insert cname [(TClassRef (cname++"_vtable_t"), "vt")] (classesAttrs oldSt),
  classesMethods = M.insert cname [] (classesMethods oldSt)
  }

addNewAttributes :: String -> [(Type, String)] -> St -> St
addNewAttributes cname newAttrs oldSt = let attrs = fromJust $ M.lookup cname (classesAttrs oldSt) in
  oldSt {classesAttrs = M.insert cname (attrs ++ newAttrs) (classesAttrs oldSt) }

addNewMethods :: String -> [TMethod] -> St -> St
addNewMethods cname meths oldSt = let methods = lookupf cname (classesMethods oldSt) in
  oldSt { classesMethods = M.insert cname (methods ++ meths) (classesMethods oldSt) }

declareVar :: String -> Var -> Env -> Env
declareVar tag obj oldEnv = oldEnv { env = M.insert tag obj (env oldEnv)}

debug :: Show a => String -> a -> a
debug str x = seq (unsafePerformIO $ do putStr "<"; putStr str; putStr ": "; print x; putStr ">") x

defaultLitExp :: L.Type -> L.Expr
defaultLitExp (L.Int ppos) = L.ELitInt ppos 0
defaultLitExp (L.Bool ppos) = L.ELitFalse ppos
defaultLitExp (L.Str ppos) = L.EString ppos ""
defaultLitExp (L.Class ppos tag)  = L.ECNull ppos tag

putString :: String -> St -> St
putString str oldSt =
  if isNothing (M.lookup str (stringPool oldSt)) then
    oldSt {stringPool = M.insert str (M.size (stringPool oldSt)) (stringPool oldSt)}
  else
    oldSt

type CompilerMonad = StateT St (ReaderT Env IO)

eval :: L.TopDef -> CompilerMonad ()
eval (L.CDef pos (L.Ident cname) (L.CBlock ppos cstmts)) = do
  modify $ setCurrentClass (TClassRef cname)
  mapM_ evalMethod (filter isMeth cstmts)

eval (L.CExtDef pos (L.Ident cname) (L.Ident cparentname) (L.CBlock ppos cstmts)) = do
  modify $ setCurrentClass (TClassRef cname)
  mapM_ evalMethod (filter isMeth cstmts)

eval (L.FnDef pos retType (L.Ident fname) args (L.Block ppos stmts)) = do
  let parsedArgs = map (\(L.Arg pos argtp (L.Ident tag)) -> (convertType argtp, tag)) args in do
    modify $ setReturn (convertType retType)
    modify $ appendInstr Empty
    modify $ appendInstr $ FnHeader (convertType retType) fname parsedArgs
    readFnArgs parsedArgs (stmts ++ checkRet (convertType retType) retType (lastf stmts pos) pos)
    modify $ appendInstr FnEnd
    return ()

evalMethod :: L.CStmt -> CompilerMonad ()
evalMethod (L.CMethod pos retType (L.Ident _fname) args (L.Block ppos stmts)) = do
  classTp <- gets current
  modify $ setReturn (convertType retType)
  let parsedArgs = (fromJust classTp, "self") : map (\(L.Arg pos argtp (L.Ident tag)) -> (convertType argtp, tag)) args
  let fname = getName classTp ++ "." ++ _fname
  modify $ appendInstr Empty
  modify $ appendInstr $ FnHeader (convertType retType) fname parsedArgs
  readFnArgs parsedArgs (stmts ++ checkRet (convertType retType) retType (lastf stmts pos) pos)
  modify $ appendInstr FnEnd
  return ()
  where
    getName (Just (TClassRef cname)) = cname

readFnArgs :: [(Type, String)] -> [L.Stmt] -> CompilerMonad ()
readFnArgs ((tp, aname):targs) stmts = do
  nowLoc <- gets newLoc
  modify incLoc

  modify $ appendInstr $ Alloca nowLoc tp
  modify $ appendInstr $ StoreArg tp aname nowLoc
  local (declareVar aname (Reg tp nowLoc)) (readFnArgs targs stmts)

readFnArgs [] stmts = compileFnBody stmts

passFuncs :: [L.TopDef] -> St -> St
passFuncs ((L.FnDef pos retType (L.Ident fname) args stmts):tfn) oldSt =
  passFuncs tfn oldSt {
    functions = M.insert fname (convertType retType) (functions oldSt),
    functionsHeader = M.insert fname (map convertTypeL args) (functionsHeader oldSt)}
    where
      convertTypeL :: L.Arg -> Type
      convertTypeL (L.Arg pos ltp tag) = convertType ltp

passFuncs (_:tfn) st = passFuncs tfn st
passFuncs [] st = st

mapClass :: [L.TopDef] -> M.Map String L.TopDef -> M.Map String L.TopDef
mapClass ((L.FnDef pos retType (L.Ident fname) args stmts):tdefs) cmap = mapClass tdefs cmap
mapClass (curDef@(L.CExtDef pos (L.Ident cname) ptag cstmts):tdefs) cmap =
  mapClass tdefs (M.insert cname curDef cmap)
mapClass (curDef@(L.CDef pos (L.Ident cname) cstmts):tdefs) cmap =
   mapClass tdefs (M.insert cname curDef cmap)
mapClass [] cmap = cmap

passClasses :: [L.TopDef] -> M.Map String L.TopDef -> St -> St
passClasses [] cmap st = st
passClasses ((L.FnDef pos retType (L.Ident fname) args stmts):tdefs) cmap st = passClasses tdefs cmap st

passClasses ((L.CDef pos (L.Ident cname) (L.CBlock ppos cstmts)):tdefs) cmap st =
  let attrs = getAllAttributes cstmts in
  let meths = getAllMethods cstmts in
  let updatedSt = addNewClass cname st in
  passClasses tdefs cmap (addNewMethods cname meths (addNewAttributes cname attrs updatedSt))

passClasses (curDef@(L.CExtDef pos (L.Ident cname) (L.Ident parentname) (L.CBlock ppos cstmts)):tdefs) cmap st =
  let attrs = upReachAttrs cname cmap in
  let meths = nub (upReachMethods cname cmap) in
  let updatedSt = addNewClass cname st in
  passClasses tdefs cmap (addNewMethods cname meths (addNewAttributes cname attrs updatedSt))

upReachAttrs :: String -> M.Map String L.TopDef -> [(Type, String)]
upReachAttrs basename cmap =
  case basename `lookupf` cmap of
    (L.CDef pos (L.Ident cname) (L.CBlock ppos cstmts)) -> getAllAttributes cstmts
    (L.CExtDef pos (L.Ident cname) (L.Ident parentname) (L.CBlock ppos cstmts)) ->
      upReachAttrs parentname cmap ++ getAllAttributes cstmts

upReachMethods :: String -> M.Map String L.TopDef -> [TMethod]
upReachMethods basename cmap =
 case basename `lookupf` cmap of
    (L.CDef pos (L.Ident cname) (L.CBlock ppos cstmts)) -> getAllMethods cstmts
    (L.CExtDef pos (L.Ident cname) (L.Ident parentname) (L.CBlock ppos cstmts)) ->
      upReachMethods parentname cmap ++ getAllMethods cstmts

getAllAttributes :: [L.CStmt] -> [(Type, String)]
getAllAttributes cstms = concatMap parseAttrList (filter isAttr cstms) where
  isAttr :: L.CStmt -> Bool
  isAttr (L.CDecl pos tp items) = True
  isAttr _ = False
  parseAttrList (L.CDecl pos tp items) = map (\(L.CItem ppos (L.Ident aname)) -> (convertType tp, aname)) items

getAllMethods :: [L.CStmt] -> [TMethod]
getAllMethods cstms = map parseMethod (filter isMeth cstms) where
  parseMethod (L.CMethod pos retType (L.Ident fname) args stmts) =
    (convertType retType, fname, map (\(L.Arg pos argtp tag) -> convertType argtp) args)
isMeth :: L.CStmt -> Bool
isMeth (L.CMethod pos retType (L.Ident fname) args stmts) = True
isMeth _ = False

runCompiler :: L.Program -> IO String
runCompiler (L.Program _ defs) = do
    let fnStat = passFuncs defs initStat
    let classMapUtil = mapClass defs M.empty
    let clsStat = passClasses defs classMapUtil fnStat
    dt <- runReaderT (execStateT (mapM eval defs) (setClassDB classMapUtil clsStat)) initEnv
    return $
      fileHeader ++
      unlines (map (showVTable dt) (M.toList (classesMethods dt))) ++
      unlines (map showClassType (M.toList (classesAttrs dt))) ++
      unlines (map showStringPool (M.toList (stringPool dt))) ++
      unlines (map show $ filter (not . isCustom) (scanClear (assembleAllocs (code dt)) False))

showStringPool :: (String, Int) -> String
showStringPool (str, ind) = "@stringPool" ++ show ind ++" = private unnamed_addr constant [" ++ show (1 + length str) ++ " x i8] c\"" ++ concatMap hexify str ++ "\\00\""
  where
  hexify :: Char -> String
  hexify c = "\\" ++ printf "%02X" (ord c)

showClassType :: (String, [(Type, String)]) -> String
showClassType (cname, vtable:args) = "%" ++ cname ++ " = type { " ++ intercalate ", " (show (fst vtable) : map showClassTpUtil args) ++ " }"
  where
    showClassTpUtil (tp, _) = show tp

showVTable :: St -> (String, [TMethod]) -> String
showVTable st (cname, funs) =
  let vtp = "%" ++ cname ++ "_vtable_t = " ++ "type {\n" ++ intercalate ",\n" (map (showFn st cname) funs) ++ "\n}\n" in
  let vtp_obj = "@" ++ cname ++ "_vtable = global %" ++ cname ++ "_vtable_t {\n" ++ intercalate ",\n" (map (showFnObj st cname) funs) ++ "\n}\n" in
    (vtp ++ vtp_obj)

showFn :: St -> String -> TMethod -> String
showFn st cname (retType, fname, args) =
  if isHereFn cname fname st then
    tab ++ show retType ++ "(%" ++ cname ++ "*" ++ concatMap (\ele -> ", " ++ show ele ) args ++ ")*"
  else showFn st (getParentName cname st) (retType, fname, args)

showFnObj :: St -> String -> TMethod -> String
showFnObj st cname (retType, fname, args) =
  if isHereFn cname fname st then
    tab ++ show retType ++ "(%" ++ cname ++ "*" ++ concatMap (\ele -> ", " ++ show ele ) args ++ ")* @" ++ cname ++ "." ++ fname
  else showFnObj st (getParentName cname st) (retType, fname, args)

isHereFn :: String -> String -> St -> Bool
isHereFn cname fname st = checkMethLevel fname (lookupf cname (classDB st))

checkMethLevel :: String -> L.TopDef -> Bool
checkMethLevel fname (L.CDef pos (L.Ident cname) (L.CBlock ppos cstmts)) = True
checkMethLevel fname (L.CExtDef pos tag ptag (L.CBlock ppos cstmts)) = any (isThisMth fname) cstmts

isThisMth :: String -> L.CStmt -> Bool
isThisMth fname (L.CMethod pos tp (L.Ident methname) args block) = methname == fname
isThisMth fname _ = False

getParentName :: String -> St -> String
getParentName cname st =
  case lookupf cname (classDB st) of
    (L.CExtDef pos tag (L.Ident pname) (L.CBlock ppos cstmts)) -> pname
    _ -> error "Compiler failure!"

compileFnBody :: [L.Stmt] -> CompilerMonad ()

compileFnBody (L.Empty pos:tstmts) = compileFnBody tstmts

compileFnBody (L.BStmt pos (L.Block ppos bstmts):tstmts) = do
  local id (compileFnBody bstmts)
  compileFnBody tstmts

compileFnBody (L.Decl pos varType ((L.NoInit ipos (L.Ident tag)):restItems):tstmts) =
  compileFnBody $ L.Decl pos varType (L.Init ipos (L.Ident tag) (defaultLitExp varType):restItems):tstmts

compileFnBody ((L.Decl pos varType ((L.Init _ (L.Ident tag) e):restItems)):tstmts) = do
  val <- compileExpr e
  nowLoc <- gets newLoc
  modify incLoc
  let convVarType = convertType varType
  if convVarType == TString then do
    modify $ appendInstr $ Alloca nowLoc convVarType
    if isReg val then do
      loadLoc <- gets newLoc
      modify incLoc
      modify $ appendInstr $ Load loadLoc convVarType (getLoc val)
      modify $ appendInstr $ Store convVarType (Reg convVarType loadLoc) nowLoc
      local (declareVar tag (Reg convVarType nowLoc)) (compileFnBody (L.Decl pos varType restItems:tstmts))
    else do -- constString
      modify $ appendInstr $ StoreString val nowLoc
      local (declareVar tag (Reg convVarType nowLoc)) (compileFnBody (L.Decl pos varType restItems:tstmts))
  else do
    isBitCast <- gets (checkBitCast val)
    if not (isClass convVarType) then do
      modify $ appendInstr $ Alloca nowLoc convVarType
      modify $ appendInstr $ Store convVarType val nowLoc
      local (declareVar tag (Reg convVarType nowLoc)) (compileFnBody (L.Decl pos varType restItems:tstmts))
    else if isBitCast then do
      modify $ appendInstr $ Alloca nowLoc convVarType
      val <- runCastCheck val convVarType
      modify $ appendInstr $ Store convVarType val nowLoc
      local (declareVar tag (Reg convVarType nowLoc)) (compileFnBody (L.Decl pos varType restItems:tstmts))
    else do
      loadLoc <- gets newLoc
      modify incLoc

      modify $ appendInstr $ Alloca nowLoc convVarType
      modify $ appendInstr $ Load loadLoc (getType val) (getLoc val)
      val <- runCastCheck (Reg (getType val) loadLoc) convVarType
      modify $ appendInstr $ Store convVarType val nowLoc
      local (declareVar tag (Reg (getType val) nowLoc)) (compileFnBody (L.Decl pos varType restItems:tstmts))

compileFnBody (L.Decl pos varType []:tstmts) = compileFnBody tstmts

compileFnBody ((L.Ass pos (L.Ident tag) e):tstmts) = do
  retrv <- asks (M.lookup tag . env)
  if isNothing retrv then do
    compileFnBody $ L.CAss pos (L.EVar pos (L.Ident "self")) (L.Ident tag) e:tstmts
  else do
    val <- compileExpr e

    if getType val == TString then do
      if isReg val then do
        nowLoc <- gets newLoc
        modify incLoc
        modify $ appendInstr $ Load nowLoc TString (getLoc val)
        modify $ appendInstr $ Store TString (Reg TString nowLoc) (getLoc (fromJust retrv))
        compileFnBody tstmts
      else do
        modify $ appendInstr $ Store TString val (getLoc (fromJust retrv))
        compileFnBody tstmts
    else if isClass (getType val) then do
      isBitCast <- gets (checkBitCast val)
      if isBitCast then do
        val <- runCastCheck val (getType (fromJust retrv))
        modify $ appendInstr $ Store (getType val) val (getLoc (fromJust retrv))
        compileFnBody tstmts
      else do
        nowLoc <- gets newLoc
        modify incLoc
        modify $ appendInstr $ Load nowLoc (getType val) (getLoc val)
        val2 <- runCastCheck (Reg (getType val) nowLoc) (getType (fromJust retrv))
        modify $ appendInstr $ Store (getType (fromJust retrv)) val2 (getLoc (fromJust retrv))
        compileFnBody tstmts
    else do
      modify $ appendInstr $ Store (getType val) val (getLoc (fromJust retrv))
      compileFnBody tstmts

compileFnBody (L.Incr pos tag:tstmts) =
  compileFnBody (L.Ass pos tag (L.EAdd pos (L.EVar pos tag) (L.Plus pos) (L.ELitInt pos 1)):tstmts)

compileFnBody (L.Decr pos tag:tstmts) =
  compileFnBody (L.Ass pos tag (L.EAdd pos (L.EVar pos tag) (L.Minus pos) (L.ELitInt pos 1)):tstmts)

compileFnBody ((L.Ret pos (L.ELitTrue ppos)):tstmts) = do
  modify $ appendInstr $ Ret TBool (ConstInt 1)

compileFnBody ((L.Ret pos (L.ELitFalse ppos)):tstmts) = do
  modify $ appendInstr $ Ret TBool (ConstInt 0)

compileFnBody ((L.Ret pos e):tstmts) = do
  val <- compileExpr e
  if isClass (getType val) then do
    retType <- gets (fromJust . returnType)
    isBitCast <- gets (checkBitCast val)
    if isBitCast then do
        val <- runCastCheck (Reg (getType val) (getLoc val)) retType 
        modify $ appendInstr $ Ret retType val
    else do
      nowLoc <- gets newLoc
      modify incLoc
      modify $ appendInstr $ Load nowLoc (getType val) (getLoc val)
      val <- runCastCheck (Reg (getType val) nowLoc) retType 
      modify $ appendInstr $ Ret retType val
  else if isReg val && getType val /= TString then do
    modify $ appendInstr $ Ret (getType val) val
  else if isReg val && getType val == TString then do
    nowLoc <- gets newLoc
    modify incLoc
    modify $ appendInstr $ Load nowLoc TString (getLoc val)
    modify $ appendInstr $ Ret TString (Reg TString nowLoc)
  else do
    modify $ appendInstr $ Ret (getType val) val

compileFnBody ((L.VRet pos):tstmts) = do
  modify $ appendInstr VRet

compileFnBody ((L.Cond pos e_cond stmts):tstmts) = do
  val <- compileExpr e_cond
  ifLabelLoc <- gets newLabel
  modify incLabel
  thenLabelLoc <- gets newLabel
  modify incLabel

  modify $ appendInstr $ BrCond (getLoc val) ifLabelLoc thenLabelLoc

  modify $ appendInstr $ Label ifLabelLoc
  local id (compileFnBody [stmts])
  modify $ appendInstr $ Br thenLabelLoc

  modify $ appendInstr $ Label thenLabelLoc
  compileFnBody tstmts

compileFnBody ((L.CondElse pos e_cond stmts else_stmts):tstmts) = do
  val <- compileExpr e_cond
  ifLabelLoc <- gets newLabel
  modify incLabel
  elseLabelLoc <- gets newLabel
  modify incLabel
  thenLabelLoc <- gets newLabel
  modify incLabel

  modify $ appendInstr $ BrCond (getLoc val) ifLabelLoc elseLabelLoc

  modify $ appendInstr $ Label ifLabelLoc
  local id (compileFnBody [stmts])
  modify $ appendInstr $ Br thenLabelLoc

  modify $ appendInstr $ Label elseLabelLoc
  local id (compileFnBody [else_stmts])
  modify $ appendInstr $ Br thenLabelLoc

  modify $ appendInstr $ Label thenLabelLoc
  compileFnBody tstmts


compileFnBody ((L.While pos e_cond stmts):tstmts) = do
  condLabelLoc <- gets newLabel
  modify incLabel
  whileBodyLabelLoc <- gets newLabel
  modify incLabel
  thenLabelLoc <- gets newLabel
  modify incLabel

  modify $ appendInstr $ Br condLabelLoc

  modify $ appendInstr $ Label whileBodyLabelLoc
  local id (compileFnBody [stmts])
  modify $ appendInstr $ Br condLabelLoc

  modify $ appendInstr $ Label condLabelLoc
  val <- compileExpr e_cond
  modify $ appendInstr $ BrCond (getLoc val) whileBodyLabelLoc thenLabelLoc

  modify $ appendInstr $ Label thenLabelLoc
  compileFnBody tstmts

compileFnBody ((L.SExp pos e):tstmts) = do
  val <- compileExpr e
  compileFnBody tstmts

compileFnBody ((L.CAss pos e1 (L.Ident tag) e2):tstmts) = do
  val1 <- compileExpr e1
  val2 <- compileExpr e2

  preLoc <- gets newLoc
  modify incLoc
  nowLoc <- gets newLoc
  modify incLoc

  isBitCast <- gets (checkBitCast val1)
  modify $ appendInstr $ if isBitCast then Custom "; Overriding load - attr" else Load preLoc (getType val1) (getLoc val1)

  let cname = (\(TClassRef n) -> n) (getType val1)
  attrs <- gets (lookupf cname . classesAttrs)
  let (ind, tp) = findAttr tag 0 attrs

  modify $ appendInstr $ GetElement nowLoc (getType val1) (if isBitCast then getLoc val1 else preLoc) ind
  if getType val2 == TString then do
    if isReg val2 then do
      loadLoc <- gets newLoc
      modify incLoc
      modify $ appendInstr $ Load loadLoc TString (getLoc val2)
      modify $ appendInstr $ Store TString (Reg TString loadLoc) nowLoc
      compileFnBody tstmts
    else do
      modify $ appendInstr $ StoreString val2 nowLoc
      compileFnBody tstmts
  else do
    isBitCast <- gets (checkBitCast val2)
    if isClass tp && not isBitCast then do
      loadLoc <- gets newLoc
      modify incLoc
      modify $ appendInstr $ Load loadLoc (getType val2) (getLoc val2)
      val2 <- runCastCheck (Reg (getType val2) loadLoc) tp
      modify $ appendInstr $ Store tp val2 nowLoc
      compileFnBody tstmts
    else do
      val2 <- runCastCheck val2 tp
      modify $ appendInstr $ Store tp val2 nowLoc
      compileFnBody tstmts

compileFnBody ((L.CIncr pos tag e):tsmts) =
  let e2 = L.EAdd pos (L.EAttr pos tag e) (L.Plus pos) (L.ELitInt pos 1) in
  compileFnBody (L.CAss pos tag e e2:tsmts)

compileFnBody ((L.CDecr pos tag e):tsmts) =
  let e2 = L.EAdd pos (L.EAttr pos tag e) (L.Minus pos) (L.ELitInt pos 1) in
  compileFnBody (L.CAss pos tag e e2:tsmts)

compileFnBody [] = return ()

--- EXPRESSION ---
compileExpr :: L.Expr -> CompilerMonad Var
compileExpr (L.ELitInt _ val) = do
  return (ConstInt val)

compileExpr (L.ELitTrue pos) = do
  nowLoc <- gets newLoc
  modify incLoc
  modify $ appendInstr $ BoolInit nowLoc 1
  return (Reg TBool nowLoc)

compileExpr (L.ELitFalse pos) = do
  nowLoc <- gets newLoc
  modify incLoc
  modify $ appendInstr $ BoolInit nowLoc 0
  return (Reg TBool nowLoc)

compileExpr (L.EString _ str) = do
  modify $ putString str
  strInd <- gets (lookupf str . stringPool)
  let strLen = length str + 1 -- for \00
  return (ConstString strInd strLen)

compileExpr (L.EVar pos (L.Ident tag)) = do
  var <- asks (M.lookup tag . env)
  if isNothing var then do -- self scope
    compileExpr (L.EAttr pos (L.EVar pos (L.Ident "self")) (L.Ident tag))
  else do
    let tp = getType (fromJust var)
    if tp == TString || isClass tp
      then return $ fromJust var
    else do
      nowLoc <- gets newLoc
      modify incLoc
      modify $ appendInstr $ Load nowLoc tp (getLoc (fromJust var))
      return (Reg tp nowLoc)

compileExpr (L.EMul pos e1 op e2) = compileExprBinOpUtil e1 e2 opStr
  where
  opStr = case op of
    (L.Times _) -> "mul"
    (L.Div _) -> "sdiv"
    (L.Mod _) -> "srem"

compileExpr (L.EAdd pos e1 op e2) = compileExprBinOpUtil e1 e2 opStr
  where
  opStr = case op of
    (L.Plus _) -> "add"
    (L.Minus _) -> "sub"

compileExpr (L.ERel pos e1 op e2) = compileExprRelOp e1 e2 opStr
  where
  opStr = case op of
    (L.LTH _) -> "icmp slt"
    (L.LE _) -> "icmp sle"
    (L.GTH _) -> "icmp sgt"
    (L.GE _) -> "icmp sge"
    (L.EQU _) -> "icmp eq"
    (L.NE _) -> "icmp ne"

compileExpr (L.Neg pos (L.ELitInt ppos val)) = compileExpr (L.ELitInt ppos (-val))

compileExpr (L.Neg pos e) = compileExprBinOpUtil (L.ELitInt pos 0) e "sub"

compileExpr (L.Not pos e) = do
  var1 <- compileExpr (L.ELitTrue pos)
  var2 <- compileExpr e
  nowLoc <- gets newLoc
  modify incLoc
  modify $ appendInstr $ BinOp nowLoc "sub" (getType var1) var1 var2
  return (Reg TBool nowLoc)

compileExpr (L.EApp pos (L.Ident tag) args) = do
  retTypeRaw <- gets (M.lookup tag . functions)
  if isNothing retTypeRaw then do
    compileExpr $ L.ECMeth pos (L.EVar pos (L.Ident "self")) (L.Ident tag) args
  else do
    let retType = fromJust retTypeRaw
    compiledArgs <- mapM compileExpr args
    preloadedArgs <- mapM loadify compiledArgs
    headerTypes <- gets (lookupf tag . functionsHeader)
    loadedArgs <- zipWithM runCastCheck preloadedArgs headerTypes

    nowLoc <- gets newLoc
    modify incLoc

    if retType == TVoid then do
      modify $ appendInstr $ CallVoidFun retType tag loadedArgs
      return (Reg retType nowLoc)
    else if retType == TString then do
      preLoc <- gets newLoc
      modify incLoc

      modify $ appendInstr $ Alloca preLoc TString
      modify $ appendInstr $ CallFun nowLoc retType tag loadedArgs
      modify $ appendInstr $ Store TString (Reg TString nowLoc) preLoc

      return (Reg TString preLoc)
    else do
      modify $ appendInstr $ CallFun nowLoc retType tag loadedArgs
      modify $ setInfo nowLoc cBITC_FLAG
      return (Reg retType nowLoc)

compileExpr (L.EOr pos e1 e2) = do  -- (a or b)
  labelTrue <- gets newLabel
  modify incLabel
  labelFirstFalse <- gets newLabel
  modify incLabel
  labelBothFalse <- gets newLabel
  modify incLabel
  labelThen <- gets newLabel
  modify incLabel

  condLoc <- gets newLoc
  modify incLoc
  nowLoc <- gets newLoc
  modify incLoc
  var1 <- compileExpr e1

  -- a == True?
  modify $ appendInstr $ Alloca condLoc TBool
  modify $ appendInstr $ BrCond (getLoc var1) labelTrue labelFirstFalse

  -- a == False && b == True?
  modify $ appendInstr $ Label labelFirstFalse
  var2 <- compileExpr e2 -- Lazy execution
  modify $ appendInstr $ BrCond (getLoc var2) labelTrue labelBothFalse

  -- return False
  modify $ appendInstr $ Label labelBothFalse
  modify $ appendInstr $ StoreFalse condLoc
  modify $ appendInstr $ Br labelThen

  -- return True 
  modify $ appendInstr $ Label labelTrue
  modify $ appendInstr $ StoreTrue condLoc
  modify $ appendInstr $ Br labelThen

  -- returning result 
  modify $ appendInstr $ Label labelThen
  modify $ appendInstr $ Load nowLoc TBool condLoc
  return (Reg TBool nowLoc)

compileExpr (L.EAnd pos e1 e2) = do  -- (a and b)
  labelFirstTrue <- gets newLabel
  modify incLabel
  labelBothTrue <- gets newLabel
  modify incLabel
  labelFalse <- gets newLabel
  modify incLabel
  labelThen <- gets newLabel
  modify incLabel

  condLoc <- gets newLoc
  modify incLoc
  nowLoc <- gets newLoc
  modify incLoc
  var1 <- compileExpr e1

  -- a == True?
  modify $ appendInstr $ Alloca condLoc TBool
  modify $ appendInstr $ BrCond (getLoc var1) labelFirstTrue labelFalse

  -- a == True && b == True?
  modify $ appendInstr $ Label labelFirstTrue
  var2 <- compileExpr e2 -- Lazy execution
  modify $ appendInstr $ BrCond (getLoc var2) labelBothTrue labelFalse

  -- return True
  modify $ appendInstr $ Label labelBothTrue
  modify $ appendInstr $ StoreTrue condLoc
  modify $ appendInstr $ Br labelThen

  -- return False
  modify $ appendInstr $ Label labelFalse
  modify $ appendInstr $ StoreFalse condLoc
  modify $ appendInstr $ Br labelThen

  -- returning result 
  modify $ appendInstr $ Label labelThen
  modify $ appendInstr $ Load nowLoc TBool condLoc
  return (Reg TBool nowLoc)

compileExpr (L.ECNull pos (L.Ident cname)) = do
  let tp = TClassRef cname
  modify $ setInfo (-1) cBITC_FLAG
  return (Reg tp (-1))

compileExpr (L.ECNew pos (L.Ident cname)) = do
  nowLoc <- gets newLoc
  modify incLoc
  callocLoc <- gets newLoc
  modify incLoc
  bitCastLoc <- gets newLoc
  modify incLoc

  let tp = TClassRef cname
  classSize <- gets (length . lookupf cname . classesAttrs)

  modify $ appendInstr $ Calloc callocLoc (classSize * 8)
  modify $ appendInstr $ Bitcast bitCastLoc callocLoc tp
  modify $ setInfo bitCastLoc cBITC_FLAG
  modify $ setVTable bitCastLoc cname

  -- Store VTable
  vTableLoc <- gets newLoc
  modify incLoc
  modify $ appendInstr $ GetElement vTableLoc tp bitCastLoc 0
  modify $ appendInstr $ StoreVTable cname vTableLoc

  -- Init empty strings
  attrs <- gets (lookupf cname . classesAttrs)
  initStringAttr attrs 0 bitCastLoc tp

  return (Reg tp bitCastLoc)

compileExpr (L.EAttr pos e (L.Ident tag)) = do
  val <- compileExpr e

  preLoc <- gets newLoc
  modify incLoc
  nowLoc <- gets newLoc
  modify incLoc

  isBitCast <- gets (checkBitCast val)
  modify $ appendInstr $ if isBitCast then Custom "; Overriding load - attr" else Load preLoc (getType val) (getLoc val)

  let cname = (\(TClassRef n) -> n) (getType val)
  attrs <- gets (lookupf cname . classesAttrs)
  let (ind, tp) = findAttr tag 0 attrs

  modify $ appendInstr $ GetElement nowLoc (getType val) (if isBitCast then getLoc val else preLoc) ind

  if isClass tp || tp == TString then do
    return (Reg tp nowLoc)
  else do
    resLoc <- gets newLoc
    modify incLoc

    modify $ appendInstr $ Load resLoc tp nowLoc
    return (Reg tp resLoc)

compileExpr (L.ECMeth pos e (L.Ident mthname) args) = do
  val <- compileExpr e
  preLoc <- gets newLoc
  modify incLoc
  vTableLoc <- gets newLoc
  modify incLoc
  loadVTableLoc <- gets newLoc
  modify incLoc
  methLoc <- gets newLoc
  modify incLoc
  loadMethLoc <- gets newLoc
  modify incLoc
  nowLoc <- gets newLoc
  modify incLoc

  let cname = (\(TClassRef n) -> n) (getType val)
  meths <- gets (lookupf cname . classesMethods)
  let (ind, retType, argTypes) = findMeth mthname 0 meths
  let vtable_tp = TClassRef $ cname ++ "_vtable_t"
  let class_tp = TClassRef cname

  cdb <- gets classDB
  let headerTypes = digHeader cname mthname cdb
  compiledArgs <- mapM compileExpr args
  preloadedArgs <- mapM loadify compiledArgs

  isBitCast <- gets (checkBitCast val)
  modify $ appendInstr $ if isBitCast then Custom "; Overriding load - meth" else Load preLoc (getType val) (getLoc val)

  -- read VTable
  modify $ appendInstr $ GetElement vTableLoc class_tp (if isBitCast then getLoc val else preLoc) 0

  -- load VTable
  modify $ appendInstr $ Load loadVTableLoc vtable_tp vTableLoc

  -- read method
  modify $ appendInstr $ GetElement methLoc vtable_tp loadVTableLoc ind

  -- load method
  modify $ appendInstr $ LoadMeth loadMethLoc retType headerTypes methLoc

  -- call method
  let self_arg = Reg class_tp (if isBitCast then getLoc val else preLoc)
  loadedArgs <- zipWithM runCastCheck (self_arg : preloadedArgs) headerTypes

  if retType == TVoid then do
    modify $ appendInstr $ CallVoidMeth retType loadMethLoc loadedArgs
    return (Reg retType nowLoc)
  else if retType == TString then do
    preLoc <- gets newLoc
    modify incLoc

    modify $ appendInstr $ Alloca preLoc TString
    modify $ appendInstr $ CallMeth nowLoc retType loadMethLoc loadedArgs
    modify $ appendInstr $ Store TString (Reg TString nowLoc) preLoc
    return (Reg TString preLoc)
  else do
    modify $ appendInstr $ CallMeth nowLoc retType loadMethLoc loadedArgs
    modify $ setInfo nowLoc cBITC_FLAG
    return (Reg retType nowLoc)


findAttr :: String -> Int -> [(Type, String)] -> (Int, Type)
findAttr tag i ((tp, ntag):tattrs) = if ntag == tag then (i, tp) else findAttr tag (i+1) tattrs

findMeth :: String -> Int -> [TMethod] -> (Int, Type, [Type])
findMeth tag i ((rtp, ntag, args):tmeths) = if ntag == tag then (i, rtp, args) else findMeth tag (i+1) tmeths

isClass :: Type -> Bool
isClass (TClassRef _) = True
isClass _ = False

initStringAttr :: [(Type, String)] -> Int -> Loc -> Type -> CompilerMonad ()
initStringAttr ((TString, aname):tattrs) ind loc tp = do
  strLoc <- gets newLoc
  modify incLoc
  modify $ appendInstr $ GetElement strLoc tp loc ind
  modify $ appendInstr $ StoreString (ConstString 0 1) strLoc
  initStringAttr tattrs (ind+1) loc tp

initStringAttr (a:tattrs) ind loc tp = initStringAttr tattrs (ind+1) loc tp

initStringAttr [] ind loc tp = return ()

compileExprBinOpUtil :: L.Expr -> L.Expr -> String -> CompilerMonad Var
compileExprBinOpUtil e1 e2 opStr = do
  var1 <- compileExpr e1
  var2 <- compileExpr e2
  nowLoc <- gets newLoc
  modify incLoc

  if getType var1 /= TString then do
    modify $ appendInstr $ BinOp nowLoc opStr (getType var1) var1 var2
    return (Reg (getType var1) nowLoc)
  else if getType var1 == TString && opStr == "add" then do
      preLoc <- gets newLoc
      modify incLoc

      if isReg var1 && isReg var2 then do
        leftLoc <- gets newLoc
        modify incLoc
        rightLoc <- gets newLoc
        modify incLoc

        modify $ appendInstr $ Load leftLoc TString (getLoc var1)
        modify $ appendInstr $ Load rightLoc TString (getLoc var2)
        modify $ appendInstr $ Alloca preLoc TString
        modify $ appendInstr $ CallFun nowLoc TString "__addStrings" [Reg TString leftLoc, Reg TString rightLoc]
        modify $ appendInstr $ Store TString (Reg TString nowLoc) preLoc
        return (Reg TString preLoc)

      else if not (isReg var1) && not (isReg var2) then do
        modify $ appendInstr $ Alloca preLoc TString
        modify $ appendInstr $ CallFun nowLoc TString "__addStrings" [var1, var2]
        modify $ appendInstr $ Store TString (Reg TString nowLoc) preLoc
        return (Reg TString preLoc)

      else if not (isReg var1) && isReg var2 then do
        rightLoc <- gets newLoc
        modify incLoc

        modify $ appendInstr $ Load rightLoc TString (getLoc var2)
        modify $ appendInstr $ Alloca preLoc TString
        modify $ appendInstr $ CallFun nowLoc TString "__addStrings" [var1, Reg TString rightLoc]
        modify $ appendInstr $ Store TString (Reg TString nowLoc) preLoc
        return (Reg TString preLoc)

      else if isReg var1 && not (isReg var2) then do
        leftLoc <- gets newLoc
        modify incLoc

        modify $ appendInstr $ Load leftLoc TString (getLoc var1)
        modify $ appendInstr $ Alloca preLoc TString
        modify $ appendInstr $ CallFun nowLoc TString "__addStrings" [Reg TString leftLoc, var2]
        modify $ appendInstr $ Store TString (Reg TString nowLoc) preLoc
        return (Reg TString preLoc)

      else error "Compiler failure!"
  else error "Compiler failure!"

compileExprRelOp :: L.Expr -> L.Expr -> String -> CompilerMonad Var
compileExprRelOp e1 e2 opStr = do
  var1 <- compileExpr e1
  var2 <- compileExpr e2
  nowLoc <- gets newLoc
  modify incLoc
  resLoc <- gets newLoc
  modify incLoc

  if isClass (getType var1) then do
    let tp = getType var1
    isBitCast1 <- gets (checkBitCast var1)
    isBitCast2 <- gets (checkBitCast var2)
    let condLeftKeep = isNullReg var1 || isBitCast1
    let condRightKeep = isNullReg var2 || isBitCast2

    if not condLeftKeep && condRightKeep then do
      leftLoc <- gets newLoc
      modify incLoc
      modify $ appendInstr $ Load leftLoc tp (getLoc var1)
      var2 <- runCastCheck var2 tp
      modify $ appendInstr $ BinOp nowLoc opStr tp (Reg tp leftLoc) var2
      return (Reg TBool nowLoc)

    else if condLeftKeep && not condRightKeep then do
      rightLoc <- gets newLoc
      modify incLoc
      modify $ appendInstr $ Load rightLoc (getType var2) (getLoc var2)
      var2 <- runCastCheck (Reg (getType var2) rightLoc) tp
      modify $ appendInstr $ BinOp nowLoc opStr tp var1 var2
      return (Reg TBool nowLoc)

    else if not condLeftKeep && not condRightKeep then do
      leftLoc <- gets newLoc
      modify incLoc
      rightLoc <- gets newLoc
      modify incLoc
      modify $ appendInstr $ Load leftLoc tp (getLoc var1)
      modify $ appendInstr $ Load rightLoc (getType var2) (getLoc var2)
      val <- runCastCheck (Reg (getType var2) rightLoc) tp
      modify $ appendInstr $ BinOp nowLoc opStr tp (Reg tp leftLoc) val
      return (Reg TBool nowLoc)

    else if condLeftKeep && condRightKeep then do
      var2 <- runCastCheck var2 tp
      modify $ appendInstr $ BinOp nowLoc opStr tp var1 var2
      return (Reg TBool nowLoc)

    else error "Compiler failure!"

  else if getType var1 /= TString then do
    modify $ appendInstr $ BinOp nowLoc opStr (getType var1) var1 var2
    return (Reg TBool nowLoc)
  else do
    if isReg var1 && isReg var2 then do
      leftLoc <- gets newLoc
      modify incLoc
      rightLoc <- gets newLoc
      modify incLoc

      modify $ appendInstr $ Load leftLoc TString (getLoc var1)
      modify $ appendInstr $ Load rightLoc TString (getLoc var2)
      modify $ appendInstr $ CallFun nowLoc TInt "__eqStrings" [Reg TString leftLoc, Reg TString rightLoc]
      modify $ appendInstr $ CastIntEq resLoc nowLoc (opStr == "icmp eq")
      return (Reg TBool resLoc)

    else if not (isReg var1) && not (isReg var2) then do
      modify $ appendInstr $ CallFun nowLoc TInt "__eqStrings" [var1, var2]
      modify $ appendInstr $ CastIntEq resLoc nowLoc (opStr == "icmp eq")
      return (Reg TBool resLoc)

    else if not (isReg var1) && isReg var2 then do
      rightLoc <- gets newLoc
      modify incLoc
      modify $ appendInstr $ Load rightLoc TString (getLoc var2)
      modify $ appendInstr $ CallFun nowLoc TInt "__eqStrings" [var1, Reg TString rightLoc]
      modify $ appendInstr $ CastIntEq resLoc nowLoc (opStr == "icmp eq")
      return (Reg TBool resLoc)

    else if isReg var1 && not (isReg var2) then do
      leftLoc <- gets newLoc
      modify incLoc
      modify $ appendInstr $ Load leftLoc TString (getLoc var1)
      modify $ appendInstr $ CallFun nowLoc TInt "__eqStrings" [Reg TString leftLoc, var2]
      modify $ appendInstr $ CastIntEq resLoc nowLoc (opStr == "icmp eq")
      return (Reg TBool resLoc)

    else error "Compiler failure!"

checkRet :: Type -> L.Type -> L.Stmt -> Pos -> [L.Stmt]
checkRet retType orgType (L.VRet ppos) pos = [L.Empty pos]
checkRet retType orgType (L.Ret ppos _) pos = [L.Empty pos]
checkRet TVoid orgType _ pos = [L.VRet pos]
checkRet retType orgType _ pos = [L.Ret pos (defaultLitExp orgType)]

loadify :: Var -> CompilerMonad Var
loadify (Reg TString loc) = do
  loadLoc <- gets newLoc
  modify incLoc
  modify $ appendInstr $ Load loadLoc TString loc
  return (Reg TString loadLoc)
loadify reg@(Reg tp@(TClassRef cname) loc) = do
  isBitCast <- gets (checkBitCast reg)
  if isNullReg reg || isBitCast then do
    return reg
  else do
    loadLoc <- gets newLoc
    modify incLoc
    modify $ appendInstr $ Load loadLoc tp loc
    return (Reg tp loadLoc)
loadify _arg = return _arg

runCastCheck :: Var -> Type -> CompilerMonad Var
runCastCheck val retType = do
  if not (isClass (getType val)) || not (isClass retType) || getType val == retType then
    return val
  else do
    recastLoc <- gets newLoc
    modify incLoc
    modify $ appendInstr $ Recast recastLoc val retType
    return (Reg retType recastLoc)

getCstmts :: L.TopDef -> [L.CStmt]
getCstmts (L.CDef pos (L.Ident cname) (L.CBlock ppos cstmts)) = cstmts
getCstmts (L.CExtDef pos tag ptag (L.CBlock ppos cstmts)) = cstmts

convertMthArgs :: String -> [L.CStmt]-> [Type]
convertMthArgs cname [L.CMethod pos retType ftag args stmts] =
  TClassRef cname : map (\(L.Arg pos argtp (L.Ident tag)) -> convertType argtp) args

digHeader :: String -> String -> M.Map String L.TopDef -> [Type]
digHeader cname mthname cdb =
  let level = lookupf cname cdb in
    if checkMethLevel mthname level then
      convertMthArgs cname $ filter (isThisMth mthname) (getCstmts level)
    else
      digHeader (getParentNameDB cname cdb) mthname cdb

getParentNameDB :: String -> M.Map String L.TopDef -> String
getParentNameDB cname cst =
  case lookupf cname cst of
    (L.CExtDef pos tag (L.Ident pname) (L.CBlock ppos cstmts)) -> pname
    _ -> error "Compiler failure!"

lastf :: [L.Stmt] -> Pos -> L.Stmt
lastf [] pos = L.Empty pos
lastf stmts _ = last stmts