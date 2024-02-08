{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use when" #-}
{-# HLINT ignore "Use guards" #-}
{-# LANGUAGE InstanceSigs #-}

module TypeChecker where

import Control.Monad.Reader
import Control.Monad.Trans
import Control.Monad.Except
import Control.Monad.Trans.Except
import Data.Functor.Identity ()

import qualified Data.Map as M
import qualified Data.List as DL
import Data.List (intercalate, nub)
import qualified Latte.Abs as L
import Data.Maybe (fromJust, isNothing, isJust)
import GHC.IO (unsafePerformIO)

---- STRUCTURES ----
data TypeCheckerEnv = Env {
    env :: M.Map String Type,           -- functions and all declared variables
    declaredVariables :: [String],      -- variables declared in current block
    insideFunction :: Maybe Type,       -- function indicator
    classData :: M.Map String L.TopDef} -- class extension parametres
    deriving Show

type TypeCheckerMonad a = ExceptT String (Reader TypeCheckerEnv) a

type Pos = L.BNFC'Position

-- AUXILIARY -------
posShow :: Pos -> String
posShow (Just (line, col)) = show line ++ ":" ++ show col ++ ": "
posShow _ = "?:?: "

initEnv :: TypeCheckerEnv
initEnv = Env {
        env = M.fromList [
            ("printInt", TFun TVoid [TInt]),
            ("printString", TFun TVoid [TString]),
            ("readInt", TFun TInt []),
            ("readString", TFun TString []),
            ("error", TFun TVoid [])
            ],
        declaredVariables = [],
        insideFunction = Nothing,
        classData = M.empty
    }

appendFunction :: String -> Type -> TypeCheckerEnv -> TypeCheckerEnv
appendFunction fname fn oldEnv = oldEnv { env = M.insert fname fn (env oldEnv) }

saveClassData :: String -> L.TopDef -> TypeCheckerEnv -> TypeCheckerEnv
saveClassData cname cdata oldEnv = oldEnv { classData = M.insert cname cdata (classData oldEnv) }

appendClass :: String -> Type -> TypeCheckerEnv -> TypeCheckerEnv
appendClass cname ctp oldEnv = oldEnv { env = M.insert cname ctp (env oldEnv) }

appendObject :: String -> Type -> TypeCheckerEnv -> TypeCheckerEnv
appendObject tag obj oldEnv = oldEnv { env = M.insert tag obj (env oldEnv), declaredVariables = tag : declaredVariables oldEnv}

clearForNewScope :: TypeCheckerEnv -> TypeCheckerEnv
clearForNewScope oldEnv = oldEnv {declaredVariables = map fst $ filter (isFun . snd) $ M.toList $ env oldEnv}

setSelf :: String -> TypeCheckerEnv -> TypeCheckerEnv
setSelf cname oldEnv = oldEnv { env = M.insert "self" (TClassRef cname) (env oldEnv) }

isFun :: Type -> Bool
isFun (TFun _ _) = True
isFun _ = False

setFunction :: Type -> TypeCheckerEnv -> TypeCheckerEnv
setFunction retType oldEnv = oldEnv {insideFunction = Just retType}

isMember :: Eq t => t -> [t] -> Bool
isMember y = foldr (\x -> (||) (y == x)) False

defaultLitExp :: L.Type -> L.Expr
defaultLitExp (L.Int ppos) = L.ELitInt ppos 0
defaultLitExp (L.Bool ppos) = L.ELitFalse ppos
defaultLitExp (L.Str ppos) = L.EString ppos ""
defaultLitExp (L.Class ppos (L.Ident tag)) = L.ECNull ppos (L.Ident tag)
defaultLitExp _ = error "Typechecker failure!"

assertType :: Pos -> Type -> Type -> String -> TypeCheckerMonad Type
assertType pos givenTypeRaw expectedType actionDescr = do
    dt <- asks classData
    let givenType = upreach givenTypeRaw expectedType givenTypeRaw dt in
        if givenType == expectedType || (actionDescr == "equality operator" && upreach expectedType givenTypeRaw expectedType dt == givenTypeRaw)
            then return givenType
            else throwError $ posShow pos ++ "Types mismatch at " ++ actionDescr ++ " - expected: " ++ show expectedType ++ " got: " ++ show givenType

upreach :: Type -> Type -> Type -> M.Map String L.TopDef -> Type
upreach (TClassRef givTpName) (TClassRef expTpName) (TClassRef curTpName) dataset =
    if curTpName == expTpName
        then TClassRef curTpName
    else if curTpName == ""
        then TClassRef givTpName
    else let result = fromJust $ M.lookup curTpName dataset in
            case result of
               (L.CExtDef pos (L.Ident cname) (L.Ident parentname) (L.CBlock ppos curCstmts))
                 -> upreach (TClassRef givTpName) (TClassRef expTpName) (TClassRef parentname) dataset
upreach givTp _ _ _ = givTp

assertTypeLst :: Pos -> [Type] -> [Type] -> String -> TypeCheckerMonad Type
assertTypeLst pos (h1:t1) (h2:t2) actionDescr = do
    assertType pos h1 h2 actionDescr
    assertTypeLst pos t1 t2 actionDescr
assertTypeLst _ _ _ _ = return TVoid

---- TYPES -----
data Type
    = TInt                      -- int
    | TString                   -- string
    | TBool                     -- boolean
    | TFun Type [Type]          -- function - (returned type) [args]
    | TVoid                     -- auxiliary type for void function
    | TClass String [(String, Type)] [(String, Type)]
                                -- class - (parent class name) [attribute types] [methods]
    | TClassRef String          -- reference to class by name
    | TCVoid                    -- auxiliary type for void non extended class
    deriving (Eq, Ord)

instance Show Type where
    show :: Type -> String
    show TInt = "int"
    show TString = "string"
    show TBool = "boolean"
    show TVoid = "void"
    show TCVoid = "null(class)"
    show (TClassRef tag) = "@[" ++ tag ++ "]"
    show (TFun retType args) = "function (" ++ intercalate ", " (map show args) ++ ") -> " ++ show retType
    show (TClass parentClass attrs funcs) =
        "class " ++ (if parentClass == "" then "" else "from " ++ show parentClass ++ " ") ++ " @.["
        ++ intercalate ", " (map show attrs) ++ "]\t"
        ++ intercalate ", " (map show funcs)

convertType :: L.Type -> Type
convertType (L.Int _)  = TInt
convertType (L.Str _)  = TString
convertType (L.Bool _) = TBool
convertType (L.Void _) = TVoid
convertType (L.Class _ (L.Ident tag)) = TClassRef tag
convertType _ = error "Typechecker failure!"

---- EXPRESSIONS ----
getTypeExp :: L.Expr -> TypeCheckerMonad Type
getTypeExp (L.ELitInt pos val) =
    if -2147483648 <= val && val <= 2147483647
        then return TInt
    else throwError $ posShow pos ++ "Int number too large!"
getTypeExp (L.ELitTrue _) = return TBool
getTypeExp (L.ELitFalse _) = return TBool
getTypeExp (L.EString _ _) = return TString

getTypeExp (L.Neg pos e) = do
    expVal <- getTypeExp e
    assertType pos expVal TInt "negating number"
    return TInt

getTypeExp (L.Not pos e) = do
    expVal <- getTypeExp e
    assertType pos expVal TBool "negating boolean"
    return TBool

getTypeExp (L.EAdd pos e1 (L.Plus _) e2) = do
    expVal1 <- getTypeExp e1
    expVal2 <- getTypeExp e2
    if expVal1 /= expVal2
        then throwError $ posShow pos ++ "Addition on different types!"
    else if expVal1 /= TInt && expVal2 /= TString
        then throwError $ posShow pos ++ "Addition " ++ show expVal1 ++ " to " ++ show expVal1 ++ " is forbidden!"
    else return expVal1

getTypeExp (L.EAdd pos e1 _ e2) = do
    expVal1 <- getTypeExp e1
    assertType pos expVal1 TInt "first arg for arithmetics"
    expVal2 <- getTypeExp e2
    assertType pos expVal2 TInt "second arg for arithmetics"
    return TInt

getTypeExp (L.EMul pos e1 _ e2) = getTypeExp (L.EAdd pos e1 (L.Minus pos) e2)

getTypeExp (L.ERel pos e1 (L.EQU _) e2) = do
    expVal1 <- getTypeExp e1
    expVal2 <- getTypeExp e2
    assertType pos expVal1 expVal2 "equality operator"
    if expVal1 == TVoid || expVal2 == TVoid
        then throwError $ posShow pos ++ "Void is not a usable type!"
        else return TBool

getTypeExp (L.ERel pos e1 (L.NE ipos) e2) = getTypeExp (L.ERel pos e1 (L.EQU ipos) e2)

getTypeExp (L.ERel pos e1 _ e2) = do
    expVal1 <- getTypeExp e1
    assertType pos expVal1 TInt "first arg for comparison"
    expVal2 <- getTypeExp e2
    assertType pos expVal2 TInt "second arg for comparison"
    return TBool

getTypeExp (L.EOr pos e1 e2) = do
    expVal1 <- getTypeExp e1
    assertType pos expVal1 TBool "first arg for logic operation"
    expVal2 <- getTypeExp e2
    assertType pos expVal2 TBool "second arg for logic operation"
    return TBool

getTypeExp (L.EAnd pos e1 e2) = getTypeExp (L.EOr pos e1 e2)

getTypeExp (L.EVar pos (L.Ident tag)) = do
    expType <- asks (M.lookup tag . env)
    maybe (throwError $ posShow pos ++ "Usage of undeclared variable " ++ tag ++ "!") return expType

getTypeExp (L.EApp pos (L.Ident tag) args) = do
    if tag == "main"
        then throwError $ posShow pos ++ "Calling main() function is forbidden!"
    else do
        expType <- asks (M.lookup tag . env)
        evalArgs <- mapM getTypeExp args
        case expType of
            Just (TFun retType argTypes) -> do
                if length args /= length argTypes
                    then throwError $ posShow pos ++ "Incorrect number of arguments!"
                    else do
                        assertTypeLst pos evalArgs argTypes "function application!"
                        return retType
            _ -> throwError $ posShow pos ++ "Usage of undeclared function " ++ tag ++ "!"

getTypeExp (L.ECMeth pos e (L.Ident tag) args) = do
    eTyped <- getTypeExp e
    envi <- asks env
    case e of 
        L.ECNull pos (L.Ident tag) -> throwError $ posShow pos ++ "Method on a null pointer!"
        _ -> case eTyped of
            TClassRef cname -> do
                curClass <- asks (M.lookup cname . env)
                case curClass of
                    Just (TClass parentname attrs meths) ->
                        let fn = filter (\(n, b) -> n == tag) (upreachMeth parentname envi meths) in
                            case fn of
                        [(_, TFun retType argTypes)] -> do
                            if length args /= length argTypes
                                then throwError $ posShow pos ++ "Incorrect number of arguments!"
                            else do
                                evalArgs <- mapM getTypeExp args
                                assertTypeLst pos evalArgs argTypes "method application!"
                                return retType

                        _ -> throwError $ posShow pos ++ "Method " ++ tag ++ " is not defined!"
                    _ -> throwError $ posShow pos ++ "Class does not exist!"
            _ -> throwError $ posShow pos ++ "Calling method can only be done on class object!"

getTypeExp (L.EAttr pos e (L.Ident tag)) = do
    eTyped <- getTypeExp e
    envi <- asks env
    case e of 
        L.ECNull pos (L.Ident tag) -> throwError $ posShow pos ++ "Attribute on a null pointer!"
        _ -> case eTyped of
            TClassRef cname -> do
                curClass <- asks (M.lookup cname . env)
                case curClass of
                    Just (TClass parentname attrs meths) ->
                            case filter (\(n, tp) -> n == tag) (upreachAttr parentname envi attrs) of
                        [(tag, attrType)] -> return attrType
                        _ -> throwError $ posShow pos ++ "Attribute " ++ tag ++ " is not defined!"
                    _ -> throwError $ posShow pos ++ "Class does not exist!"
            _ -> throwError $ posShow pos ++ "Accessing attribute can only be done on class object!"

getTypeExp (L.ECNew pos (L.Ident tag)) = do
    expClass <- asks (M.lookup tag . env)
    case expClass of
        Just (TClass parentname attrs meths) -> return $ TClassRef tag
        _ -> throwError $ posShow pos ++ "Class " ++ tag ++ " does not exist!"

getTypeExp (L.ECNull pos (L.Ident tag)) = do
    expClass <- asks (M.lookup tag . env)
    case expClass of
        Just (TClass parentname attrs meths) -> return $ TClassRef tag
        _ -> throwError $ posShow pos ++ "Class " ++ tag ++ " does not exist!"

upreachAttr :: String -> M.Map String Type -> [(String, Type)] -> [(String, Type)]
upreachAttr "" env acc = acc
upreachAttr cname env acc =
    let (TClass parentname attrs meths) = fromJust (M.lookup cname env) in
        upreachAttr parentname env (acc ++ attrs)

upreachMeth :: String -> M.Map String Type -> [(String, Type)] -> [(String, Type)]
upreachMeth "" env acc = nub acc
upreachMeth cname env acc =
    let (TClass parentname attrs meths) = fromJust (M.lookup cname env) in
        upreachMeth parentname env (acc ++ meths)

---- STATEMENTS ----
typeCheckStmtsBlock :: [L.Stmt] -> TypeCheckerMonad ()

typeCheckStmtsBlock ((L.Empty _):tstmts) = typeCheckStmtsBlock tstmts

typeCheckStmtsBlock ((L.BStmt _ (L.Block _ bstmts)):tstmts) = do
    local clearForNewScope (typeCheckStmtsBlock bstmts)
    typeCheckStmtsBlock tstmts

typeCheckStmtsBlock ((L.Decl pos varType ((L.NoInit ipos (L.Ident tag)):restItems)):tstmts) = do
    if convertType varType == TVoid
        then throwError $ posShow pos ++ "Void is not a usable type!"
    else typeCheckStmtsBlock (L.Decl pos varType (L.Init ipos (L.Ident tag) (defaultLitExp varType):restItems):tstmts)

typeCheckStmtsBlock ((L.Decl pos varType ((L.Init _ (L.Ident tag) e):restItems)):tstmts) = do
    if convertType varType == TVoid
        then throwError $ posShow pos ++ "Void is not a usable type!"
    else if tag == "self"
        then throwError $ posShow pos ++ "Variable cannot be named \'self\'!"
    else do
        expType <- getTypeExp e
        assertType pos expType (convertType varType) $ "initialising variable " ++ tag
        alreadyDeclared <- asks (isMember tag . declaredVariables)
        if alreadyDeclared
            then throwError $ posShow pos ++ "Variable " ++ tag ++ " is already declared!"
        else local (appendObject tag (convertType varType)) (typeCheckStmtsBlock (L.Decl pos varType restItems:tstmts))

typeCheckStmtsBlock (L.Decl pos varType []:tstmts) = typeCheckStmtsBlock tstmts

typeCheckStmtsBlock ((L.Ass pos (L.Ident tag) e):tstmts) = do
    expType <- getTypeExp e
    curType <- asks (M.lookup tag . env)
    dt <- asks classData
    if isNothing curType
        then throwError $ posShow pos ++ "Variable " ++ tag ++ " is not declared!"
    else do
        assertType pos expType (fromJust curType) $ "updating variable " ++ tag
        typeCheckStmtsBlock tstmts

typeCheckStmtsBlock ((L.CAss pos e1 (L.Ident tag) e2):tstmts) = do
    eTyped <- getTypeExp e1
    eTypedNewValue <- getTypeExp e2
    envi <- asks env
    dt <- asks classData
    case e1 of 
        L.ECNull pos (L.Ident tag) -> throwError $ posShow pos ++ "Assigning on null pointer!"
        _ -> case eTyped of
            TClassRef cname -> do
                curClass <- asks (M.lookup cname . env)
                case curClass of
                    Just (TClass parentname attrs meths) ->
                            case filter (\(n, tp) -> n == tag) (upreachAttr parentname envi attrs)  of
                        [(tag, attrType)] -> do
                            assertType pos eTypedNewValue attrType $ "updating attribute " ++ tag
                            typeCheckStmtsBlock tstmts
                        _ -> throwError $ posShow pos ++ "Attribute " ++ tag ++ " is not defined!"
                    _ -> throwError $ posShow pos ++ "Class does not exist!"
            _ -> throwError $ posShow pos ++ "Accessing attribute for value assignment can only be done on class object!"

typeCheckStmtsBlock (L.Incr pos (L.Ident tag):tstmts) = do
    curType <- asks (M.lookup tag . env)
    if isNothing curType
        then throwError $ posShow pos ++ "Variable " ++ tag ++ " is not declared!"
    else if curType /= Just TInt then
        throwError $ posShow pos ++ "Only int variable can be incremented/decremented!"
    else typeCheckStmtsBlock tstmts

typeCheckStmtsBlock (L.Decr pos (L.Ident tag):tstmts) =
    typeCheckStmtsBlock (L.Incr pos (L.Ident tag):tstmts)

typeCheckStmtsBlock (L.CIncr pos e (L.Ident tag):tstmts) = do
    eTyped <- getTypeExp e
    envi <- asks env
    case eTyped of
        TClassRef cname -> do
            curClass <- asks (M.lookup cname . env)
            case curClass of
                Just (TClass parentname attrs meths) ->
                        case filter (\(n, tp) -> n == tag) (upreachAttr parentname envi attrs)  of
                    [(tag, attrType)] -> if
                        attrType == TInt then typeCheckStmtsBlock tstmts
                            else throwError $ posShow pos ++ "Only int attribute can be incremented/decremented!"
                    _ -> throwError $ posShow pos ++ "Attribute " ++ tag ++ " is not defined!"
                _ -> throwError $ posShow pos ++ "Class does not exist!"
        _ -> throwError $ posShow pos ++ "Accessing attribute for incrementing/decrementing can only be done on class object!"

typeCheckStmtsBlock (L.CDecr pos e (L.Ident tag):tstmts) =
    typeCheckStmtsBlock (L.CIncr pos e (L.Ident tag):tstmts)

typeCheckStmtsBlock ((L.Ret pos e):tstmts) = do
    expType <- getTypeExp e
    functionType <- asks insideFunction
    if functionType == Just TVoid
        then throwError $ posShow pos ++ "Return in void function"
    else case functionType of
         Nothing -> throwError $ posShow pos ++ "Return outside of function"
         Just ty -> do
            assertType pos expType ty "Returning value from a function!"
            typeCheckStmtsBlock tstmts

typeCheckStmtsBlock ((L.VRet pos):tstmts) = do
    let expType = TVoid
    functionType <- asks insideFunction
    case functionType of
      Nothing -> throwError $ posShow pos ++ "Return outside of function"
      Just ty -> if ty == expType
          then typeCheckStmtsBlock tstmts
          else throwError $ posShow pos ++ "Returning " ++ show expType ++ " in " ++ show ty ++ " function!"

typeCheckStmtsBlock ((L.Cond pos e_cond stmts):tstmts) = do
    condType <- getTypeExp e_cond
    if condType /= TBool
        then throwError $ posShow pos ++ "Only boolean can be used as if statement condition!"
    else do
        local clearForNewScope (typeCheckStmtsBlock [stmts])
        typeCheckStmtsBlock tstmts

typeCheckStmtsBlock ((L.CondElse pos e_cond stmts else_stmts):tstmts) = do
    condType <- getTypeExp e_cond
    if condType /= TBool
        then throwError $ posShow pos ++ "Only boolean can be used as if statement condition!"
    else do
        local clearForNewScope (typeCheckStmtsBlock [stmts])
        local clearForNewScope (typeCheckStmtsBlock [else_stmts])
        typeCheckStmtsBlock tstmts

typeCheckStmtsBlock ((L.While pos e_cond stmts):tstmts) = do
    condType <- getTypeExp e_cond
    if condType /= TBool
        then throwError $ posShow pos ++ "Only boolean can be used as while statement condition!"
    else do
        local clearForNewScope (typeCheckStmtsBlock [stmts])
        typeCheckStmtsBlock tstmts

typeCheckStmtsBlock ((L.SExp pos e):tstmts) = do
    _ <- getTypeExp e
    typeCheckStmtsBlock tstmts

typeCheckStmtsBlock [] = return ()

typeCheck :: L.Program -> TypeCheckerMonad ()
typeCheck (L.Program _ functions) = do
    let ftwice = checkRedefinition functions (map fst $ M.toList $ env initEnv)
    let ctwice = checkRedefinitionClass functions []
    let wrongExtension = checkClassExtension functions (map getCName functions)
    let collision = filter (/="") $ DL.intersect (map getCName functions) (map getFnName functions)
    if isMember "self" (map getCName functions)
        then throwError $ "Class cannot be named \'self\'!"
    else if isMember "self" (map getFnName functions)
        then throwError $ "Function cannot be named self!"
    else if isJust ftwice
        then throwError $ "Function " ++ fromJust ftwice ++ " is redefined!"
    else if isJust ctwice
        then throwError $ "Class " ++ fromJust ctwice ++ " is redefined!"
    else if isJust wrongExtension
        then throwError $ "Class " ++ fst (fromJust wrongExtension) ++ " cannot extend " ++ snd (fromJust wrongExtension) ++ "!"
    else if collision /= []
        then throwError $ "Naming collision - both class and function " ++ head collision ++ " are forbidden!"
    else if checkMain functions
        then do
            mapM_ checkNow functions
    else throwError "No int main() function in programme!"
    where
    checkNow f = do
        typeCheckFunction f
        checkMethodOverride f
        checkLocalRedefinition f
        return ()

checkMain :: [L.TopDef] -> Bool
checkMain ((L.FnDef pos (L.Int ppos) (L.Ident "main") [] stmts):tfn) = True
checkMain (_:tfn) = checkMain tfn
checkMain [] = False

checkRedefinition :: [L.TopDef] -> [String] -> Maybe String
checkRedefinition [] allFnNames = Nothing
checkRedefinition ((L.FnDef pos retType (L.Ident fname) args stmts):tfn) allFnNames =
    if isMember fname allFnNames
        then Just fname
    else checkRedefinition tfn (fname:allFnNames)
checkRedefinition (_:tfn) allFnNames = checkRedefinition tfn allFnNames

checkRedefinitionClass :: [L.TopDef] -> [String] -> Maybe String
checkRedefinitionClass [] allCNames = Nothing

checkRedefinitionClass ((L.CDef pos (L.Ident cname) cstmts):tc) allCNames =
    if isMember cname allCNames
        then Just cname
    else checkRedefinitionClass tc (cname:allCNames)

checkRedefinitionClass ((L.CExtDef pos (L.Ident cname) (L.Ident cparentname) cstmts):tc) allCNames =
    checkRedefinitionClass (L.CDef pos (L.Ident cname) cstmts:tc) allCNames

checkRedefinitionClass (_:tc) allCNames = checkRedefinitionClass tc allCNames

checkClassExtension :: [L.TopDef] -> [String] -> Maybe (String, String)
checkClassExtension ((L.CExtDef pos (L.Ident cname) (L.Ident cparentname) cstmts):tc) allCNames =
    if isMember cparentname allCNames && cname /= cparentname
        then checkClassExtension tc allCNames
    else Just (cname, cparentname)

checkClassExtension [] allCNames = Nothing

checkClassExtension (_:tc) allCNames = checkClassExtension tc allCNames

getCName :: L.TopDef -> String
getCName (L.CExtDef pos (L.Ident cname) (L.Ident cparentname) cstmts) = cname
getCName (L.CDef pos (L.Ident cname) cstmts) = cname
getCName _ = ""

getFnName :: L.TopDef -> String
getFnName (L.FnDef pos retType (L.Ident fname) args stmts) = fname
getFnName _ = ""

typeCheckFunction :: L.TopDef -> TypeCheckerMonad ()
typeCheckFunction (L.FnDef pos retType (L.Ident fname) args stmts) =
    typeCheckFunctionUtil pos fname (map (\(L.Arg pos argtp (L.Ident tag)) -> (tag, convertType argtp)) args) (convertType retType) stmts

typeCheckFunction (L.CDef pos (L.Ident cname) (L.CBlock ppos cstmts)) = do
    let attributes = concatMap parseDecl cstmts
    let meths = filter isMethod cstmts
    let collision = map (\(L.CMethod pos retType (L.Ident tag) args stmts) -> tag) meths `DL.intersect` map fst attributes
    if length (nub (map fst attributes)) /= length attributes then
        throwError $ posShow pos ++ "Class " ++ cname ++ " has a redeclaration for the same attribute!"
    else if collision /= [] then
        throwError $ posShow pos ++ "Class " ++ cname ++ " has a both method and attribute named " ++ head collision ++ "!"
    else if isMember "self" (map fst attributes) then
        throwError $ posShow pos ++ "Attribute cannot be named \'self\'!"
    else do
        mapM_ (checkAttribute pos) attributes
        let methods = filter isMethod cstmts
        local (setSelf cname . appendMethods methods . appendAttributes attributes) (checkMethods methods)
        return ()

typeCheckFunction (L.CExtDef pos (L.Ident cname) (L.Ident parentname) stmts) = do
    dt <- asks classData
    checkCycleClass dt cname pos parentname
    let overData = extendData cname dt
    typeCheckFunction (L.CDef pos (L.Ident cname) (L.CBlock pos overData))

extendData :: String ->  M.Map String L.TopDef -> [L.CStmt]
extendData tag dataset =
    if tag == "" then []
    else
        let result = fromJust $ M.lookup tag dataset in
            case result of
               (L.CExtDef pos (L.Ident cname) (L.Ident parentname) (L.CBlock ppos curCstmts)) -> curCstmts ++ extendData parentname dataset

checkCycleClass :: M.Map String L.TopDef -> String -> Pos -> String -> TypeCheckerMonad ()
checkCycleClass dataset curname pos parentname =
    if curname == parentname
        then throwError $ posShow pos ++ "Class " ++ curname ++ " is extended in cycle!"
    else if parentname /= ""
        then let result = fromJust $ M.lookup parentname dataset in
             case result of
                (L.CExtDef respos (L.Ident rescname) (L.Ident resparentname) (L.CBlock ppos curCstmts)) -> checkCycleClass dataset curname pos resparentname
        else return ()

parseDecl :: L.CStmt -> [(String, Type)]
parseDecl (L.CDecl pos tp args) = map (\(L.CItem ppos (L.Ident tag)) -> (tag, convertType tp)) args
parseDecl _ = []

isMethod :: L.CStmt -> Bool
isMethod (L.CMethod pos tp (L.Ident tag) args (L.Block ppos stmts)) = True
isMethod _ = False

checkAttribute :: Pos -> (String, Type) -> TypeCheckerMonad ()
checkAttribute pos (aname, TClassRef classtype) = do
    reffedTyped <- asks (M.lookup classtype . env)
    if isNothing reffedTyped
        then throwError $ posShow pos ++ "Attribute class " ++ classtype ++ " is not declared!"
    else return ()

checkAttribute pos (aname, TVoid) =
    throwError $ posShow pos ++ "Attribute " ++ aname ++ " cannot be void!"

checkAttribute pos _ = return ()

appendMethods :: [L.CStmt] -> TypeCheckerEnv -> TypeCheckerEnv
appendMethods ((L.CMethod pos retType (L.Ident tag) args stmts):tm) env =
    appendMethods tm (appendFunction tag curFn env) where
        curFn = TFun (convertType retType) $ map (\(L.Arg pos argtp tag) -> convertType argtp) args
appendMethods [] env = env

appendAttributes :: [(String, Type)] -> TypeCheckerEnv -> TypeCheckerEnv
appendAttributes ((aname, atp):t) oldEnv = oldEnv { env = M.insert aname atp (env (appendAttributes t oldEnv)) }
appendAttributes [] env = env

checkMethods :: [L.CStmt] -> TypeCheckerMonad ()
checkMethods ((L.CMethod pos retType (L.Ident tag) args stmts):tm) = do
    typeCheckFunction (L.FnDef pos retType (L.Ident tag) args stmts)
    checkMethods tm

checkMethods [] = return ()

checkLocalRedefinition :: L.TopDef -> TypeCheckerMonad ()
checkLocalRedefinition (L.FnDef pos retType (L.Ident fname) args stmts) = return ()
checkLocalRedefinition (L.CDef pos tag (L.CBlock ppos cstmts)) =
    checkLocalRedefinition (L.CExtDef pos tag tag (L.CBlock ppos cstmts))

checkLocalRedefinition (L.CExtDef pos tag ptag (L.CBlock ppos cstmts)) = do
    let methNames = map (\(L.CMethod pos retType (L.Ident tag) args stmts) -> tag) $ filter isMethod cstmts
    checkRedef methNames pos

checkRedef :: [String] -> Pos -> TypeCheckerMonad ()
checkRedef (fname:tf) pos =
    if fname `elem` tf
        then  throwError $ posShow pos ++ "Method " ++ fname ++ " is redeclared!"
    else checkRedef tf pos
checkRedef _ pos = return ()

checkMethodOverride :: L.TopDef -> TypeCheckerMonad ()
checkMethodOverride (L.FnDef pos retType (L.Ident fname) args stmts) = return ()
checkMethodOverride (L.CDef pos (L.Ident cname) (L.CBlock ppos cstmts)) = return ()
checkMethodOverride (L.CExtDef pos (L.Ident cname) (L.Ident "") stmts) = return ()

checkMethodOverride (L.CExtDef pos (L.Ident cname) (L.Ident parentname) stmts) = do
    curEnv <- asks env
    dt <- asks classData
    let currentFns = M.fromList $ (\(TClass n ats ms) -> ms) $ fromJust (M.lookup cname curEnv)
    let keys = map fst $ (\(TClass n ats ms) -> ms) $ fromJust (M.lookup cname curEnv)
    let parentFns = M.fromList $ (\(TClass n ats ms) -> ms) $ fromJust (M.lookup parentname curEnv)
    let fnCompareList = filter (\((key, f1), f2) -> isJust f1 && isJust f2 && f1 /= f2) $ map (\key -> ((key, M.lookup key currentFns), M.lookup key parentFns)) keys
    let upperName = (\(L.CExtDef pos (L.Ident cname) (L.Ident uparentname) stmts) -> uparentname) $ fromJust $ M.lookup parentname dt
    if fnCompareList == []
        then checkMethodOverride (L.CExtDef pos (L.Ident cname) (L.Ident upperName) stmts)
    else let (fname, fsgn) = fst $ head fnCompareList in
        throwError $ posShow pos ++ "Changing header at function " ++ fname ++ " to " ++ show (fromJust fsgn) ++ " during overriding function is forbidden!"

typeCheckFunctionUtil :: Pos -> String -> [(String, Type)] -> Type -> L.Block -> TypeCheckerMonad ()
typeCheckFunctionUtil pos fname args retType (L.Block _ stmts)
  | length (nub (map fst args)) /= length args = throwError $ posShow pos ++ "Function with a repeating argument name!"
  | isMember TVoid (map snd args) = throwError $ posShow pos ++ "Void is not a usable type!"
  | isMember "self" (map fst args) = throwError $ posShow pos ++ "Argument cannot be named \'self\'!"
  | otherwise = do
        checkUndecleredArgs args pos
        local (setFunction retType . flip (foldr (uncurry appendObject)) (map (\(n, t) -> (n,t)) args)) $ typeCheckStmtsBlock stmts
        when (retType /= TVoid && checkReturn stmts == RetBlank) $ throwError $ posShow pos ++ "Function " ++ fname ++ " without a return statement!"

checkUndecleredArgs :: [(a, Type)] -> Pos -> TypeCheckerMonad ()
checkUndecleredArgs ((aname, TClassRef classtype):targs) pos = do 
    reffedTyped <- asks (M.lookup classtype . env)
    if isNothing reffedTyped
        then throwError $ posShow pos ++ "Function with non-existent classtype as argument!"
    else checkUndecleredArgs targs pos 
checkUndecleredArgs (_: targs) pos = checkUndecleredArgs targs pos
checkUndecleredArgs [] pos = return ()

---- RUN -----
runTypeCheck :: L.Program -> Either String ()
runTypeCheck p@(L.Program _ defs) =
    runReader (runExceptT (typeCheck p)) (readHeaders defs initEnv)

readHeaders :: [L.TopDef] -> TypeCheckerEnv -> TypeCheckerEnv
readHeaders (L.FnDef pos retType (L.Ident fname) args stmts:t) env =
     readHeaders t (appendFunction fname curFn env) where
     curFn = TFun (convertType retType) $ map (\(L.Arg pos argtp tag) -> convertType argtp) args

readHeaders (L.CDef pos (L.Ident cname) stmts:t) env = readHeaders (L.CExtDef pos (L.Ident cname) (L.Ident "") stmts:t) env

readHeaders (cobj@(L.CExtDef pos (L.Ident cname) (L.Ident parentname) (L.CBlock ppos cstmts)):t) env =
    readHeaders t (appendClass cname curClass (saveClassData cname cobj env))
        where
        curClass = TClass parentname attributes (map parseMethod methods)
        attributes = concatMap parseDecl cstmts
        methods = filter isMethod cstmts
        parseMethod (L.CMethod pos retType (L.Ident tag) args stmts) =
            (tag, TFun (convertType retType) (map (\(L.Arg pos argtp tag) -> convertType argtp) args))

readHeaders [] env = env

----- RETURNS -----
data RetFlag
    = RetBlank
    | FReturn
    deriving (Eq, Ord, Show)

checkReturn :: [L.Stmt] -> RetFlag
checkReturn ((L.BStmt _ (L.Block _ bstmts)):tstmts) = checkReturn (bstmts ++ tstmts)

checkReturn ((L.Ret pos e):tstmts) = FReturn

checkReturn ((L.VRet pos):tstmts) = FReturn

checkReturn ((L.While pos e_cond stmts):tstmts) =
    case e_cond of
        (L.ELitTrue _)  -> FReturn
        (L.ELitFalse _) -> checkReturn tstmts
        _               -> checkReturn tstmts

checkReturn ((L.Cond pos e_cond stmts):tstmts) =
    case e_cond of
        (L.ELitTrue _)  -> checkReturn (stmts : tstmts)
        (L.ELitFalse _) -> checkReturn tstmts
        _               -> checkReturn tstmts

checkReturn ((L.CondElse pos e_cond stmts else_stmts):tstmts) =
    case e_cond of
        (L.ELitTrue _)  -> checkReturn (stmts : tstmts)
        (L.ELitFalse _) -> checkReturn (else_stmts : tstmts)
        _               ->
            let down_flag = checkReturn tstmts in
            let if_flag = checkReturn [stmts] in
            let else_flag = checkReturn [else_stmts] in
            if down_flag == FReturn || (if_flag == FReturn && else_flag == FReturn)
                then FReturn
                else RetBlank

checkReturn (_:tstmts) = checkReturn tstmts

checkReturn [] = RetBlank



