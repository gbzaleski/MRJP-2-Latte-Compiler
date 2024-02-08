{-# LANGUAGE InstanceSigs #-}

module Instruction where

import Data.List ( intercalate )
import qualified Latte.Abs as L

type Pos = L.BNFC'Position
type Loc = Int

data Var
     = Reg Type Loc
     | ConstInt Integer
     | ConstBool Bool
     | ConstString Int Int -- Index at Stringpool, Length for allocation
     deriving (Eq, Ord)

instance Show Var where
     show :: Var -> String
     show (Reg _ loc) =
          if loc >= 0 then "%t" ++ show loc
          else "null"
     show (ConstInt i) = show i
     show (ConstBool b) = show b
     show (ConstString ind len) =
          "getelementptr inbounds([" ++ show len ++ " x i8], [" ++ show len ++ " x i8]* @stringPool" ++ show ind ++ ", i32 0, i32 0)"

isReg :: Var -> Bool
isReg (Reg tp loc) = True
isReg _  = False

isNullReg :: Var -> Bool
isNullReg (Reg _ loc) = loc < 0
isNullReg w = error $ "Compiler failure " ++ show w

getLoc :: Var -> Loc
getLoc (Reg tp loc) = loc
getLoc w = error $ "Compiler failure " ++ show w

getType :: Var -> Type
getType (Reg tp loc) = tp
getType (ConstInt _) = TInt
getType (ConstBool _) = TBool
getType (ConstString _ len) = TString

data Type
    = TInt                      -- int
    | TString                   -- string
    | TBool                     -- boolean
    | TVoid                     -- auxiliary type for void function
    | TClassRef String
    deriving (Eq, Ord)

instance Show Type where
  show :: Type -> String
  show TInt = "i32"
  show TString = "i8*"
  show TBool = "i1"
  show TVoid = "void"
  show (TClassRef cname) = "%" ++ cname ++ "*"

convertType :: L.Type -> Type
convertType (L.Int _)  = TInt
convertType (L.Str _)  = TString
convertType (L.Bool _) = TBool
convertType (L.Void _) = TVoid
convertType (L.Class _ (L.Ident tag)) = TClassRef tag
convertType _ = error "Compiler failure!"

data Instr
    = Empty
    | FnHeader Type String [(Type, String)] -- define i32 @f(i32 %w)
    | FnEnd
    | Alloca Loc Type                       -- %t5 = alloca i32
    | Store Type Var Loc                    -- store i32 %t4, i32* %t1 -- store [val], where
    | Load Loc Type Loc                     -- %t4 = load i32, i32* %t1
    | Ret Type Var                          -- ret i32 %t8
    | VRet
    | IntInit Loc Integer                   -- %t3 = add i32 5, 0    
    | BoolInit Loc Int                      -- %t3 = add i1 1, 0
    | BinOp Loc String Type Var Var         -- %t4 = add i32 %t3, %t5
    | Label Loc                             -- Label3: 
    | Br Loc                                -- br label %Label3
    | BrCond Loc Loc Loc                    -- br i1 %c0, label %L3, label %L2 -- br cond, ifTrue, ifElse
    | CallFun Loc Type String [Var]         -- %t7 = call i32 @f(i32 %t4, i32 %t6)
    | CallVoidFun Type String [Var]         -- call void @printInt (i32 %t4)
    | StoreArg Type String Loc              -- store i32 %a, i32* %t1
    | StoreString Var Loc                   -- store i8* getelementptr inbounds([5 x i8], [5 x i8]* @stringPool, i32 0, i32 0), i8** %t1
    | StoreTrue Loc                         -- store i1 1, i1* %t7
    | StoreFalse Loc                        -- store i1 0, i1* %t7
    | Custom String                         -- custom line
    | CastIntEq Loc Loc Bool                -- %t2 = icmp eq i32 %t3, 0
    | Calloc Loc Int                        -- %t4 = call i8* @__calloc(i32 12)
    | Bitcast Loc Loc Type                  -- %t5 = bitcast i8* %t4 to %pair*
    | GetElement Loc Type Loc Int           -- %t9 = getelementptr inbounds %pair, %pair* %t8, i32 0, i32 1
    | BinOpPtr Loc String Type Var Var      -- %t11 = icmp eq %pair* %t9, %t5
    | StoreVTable String Loc                -- store %Base_vtable_t* @Base_vtable, %Base_vtable_t** %t5
    | LoadMeth Loc Type [Type] Loc          -- %t6 = load i32(%Base*)*, i32(%Base*)** %t4
    | CallMeth Loc Type Loc [Var]           -- %t14 = call i32 %t6(%Base* %t1)
    | CallVoidMeth Type Loc [Var]           -- call void %t6(%Base* %t1)
    | Recast Loc Var Type                   -- %t4 = bitcast %Extended* %t3 to %Base*
    deriving (Eq, Ord)

instance Show Instr where
    show :: Instr -> String
    show Empty = ""
    show (FnHeader retType fname args) =
        "define " ++ show retType ++ " @" ++ fname ++ "(" ++ intercalate ", " (map showArgHeader args) ++ ") {"
    show FnEnd = "}"
    show (Alloca loc tp) = tab ++ "%t" ++ show loc ++ " = alloca " ++ show tp
    show (Store tp (Reg _ loc1) loc2) = let el1 = if loc1 >= 0 then " %t" ++ show loc1 else " null" in
         tab ++ "store " ++ show tp ++ el1 ++ ", " ++ show tp ++ "* %t" ++ show loc2
    show (Store tp constval loc2) =
          tab ++ "store " ++ show tp ++ " " ++ show constval ++ ", " ++ show tp ++ "* %t" ++ show loc2
    show (Load loc1 tp loc2) = tab ++ "%t" ++ show loc1 ++ " = load " ++ show tp ++ ", " ++ show tp ++ "* %t" ++ show loc2
    show (Ret tp loc) = tab ++ "ret " ++ show tp ++ " " ++ show loc
    show VRet = tab ++ "ret void"
    show (IntInit loc initVal) = tab ++ "%t" ++ show loc ++ " = add i32 0, " ++ show initVal
    show (BoolInit loc initVal) = tab ++ "%t" ++ show loc ++ " = add i1 0, " ++ show initVal
    show (BinOp loc1 binOpStr tp loc2 loc3) =
         tab ++ "%t" ++ show loc1 ++ " = " ++ binOpStr ++ " " ++ show tp ++ " " ++ show loc2 ++ ", " ++ show loc3
    show (Label loc) = "Label" ++ show loc ++ ":"
    show (Br loc) = tab ++ "br label %Label" ++ show loc
    show (BrCond locCond loc1 loc2) = tab ++ "br i1 %t" ++ show locCond ++ ", label %Label" ++ show loc1 ++ ", label %Label" ++ show loc2
    show (CallFun loc tp fname args) =
         tab ++ "%t" ++ show loc ++ " = call " ++ show tp ++ " @" ++ fname ++ "(" ++ intercalate ", " (map showArgCall args) ++ ")"
    show (CallVoidFun tp fname args) =
         tab ++ "call " ++ show tp ++ " @" ++ fname ++ "(" ++ intercalate ", " (map showArgCall args) ++ ")"
    show (StoreArg tp aname loc) = tab ++ "store " ++ show tp ++ " %" ++ aname ++ ", " ++ show tp ++ "* %t" ++ show loc
    show (StoreString (ConstString strInd len) loc) =
         tab ++ "store i8* getelementptr inbounds([" ++ show len ++ " x i8], [" ++ show len ++ " x i8]* @stringPool" ++ show strInd ++ ", i32 0, i32 0), i8** %t" ++ show loc
    show (StoreTrue loc) = tab ++ "store i1 1, i1* %t" ++ show loc
    show (StoreFalse loc) = tab ++ "store i1 0, i1* %t" ++ show loc
    show (Custom code) = tab ++ code
    show (CastIntEq loc1 loc2 c) = tab ++ "%t" ++ show loc1 ++ " = icmp eq i32 %t" ++ show loc2 ++ ", " ++ if c then "1" else "0"
    show (Calloc loc siz) = tab ++ "%t" ++ show loc ++ " = call i8* @__calloc(i32 " ++ show siz ++ ")"
    show (Bitcast loc1 loc2 tp) = tab ++ "%t" ++ show loc1 ++ " = bitcast i8* %t" ++ show loc2 ++ " to " ++ show tp
    show (GetElement loc1 tp loc2 ind) =
          tab ++ "%t" ++ show loc1 ++ " = getelementptr inbounds " ++ init (show tp) ++ ", " ++ show tp ++ " %t" ++ show loc2 ++ ", i32 0, i32 " ++ show ind
    show (BinOpPtr loc1 binOpStr tp loc2 loc3) =
          tab ++ "%t" ++ show loc1 ++ " = " ++ binOpStr ++ " " ++ show tp ++ "* " ++ show loc2 ++ ", " ++ show loc3
    show (StoreVTable cname loc) =
          tab ++ "store" ++ " %" ++ cname ++ "_vtable_t* " ++ "@" ++ cname ++ "_vtable" ++ ", " ++ "%" ++ cname ++ "_vtable_t**" ++ " %t" ++ show loc
    show (LoadMeth loc1 rtp argtps loc2) = let content = intercalate ", " (map show argtps) in
          tab ++ "%t" ++ show loc1 ++ " = load " ++ show rtp ++ "(" ++ content ++ ")*, " ++ show rtp ++ "(" ++ content ++ ")**" ++ " %t" ++ show loc2
    show (CallMeth loc1 tp loc2 args) =
          tab ++ "%t" ++ show loc1 ++ " = call " ++ show tp ++ " %t" ++ show loc2 ++ "(" ++ intercalate ", " (map showArgCall args) ++ ")"
    show (CallVoidMeth tp loc args) =
          tab ++ "call " ++ show tp ++ " %t" ++ show loc ++ "(" ++ intercalate ", " (map showArgCall args) ++ ")"
    show (Recast loc1 (Reg oldTp loc2) newTp) =
          tab ++ "%t" ++ show loc1 ++ " = bitcast " ++ show oldTp ++ " %t" ++ show loc2 ++ " to " ++ show newTp

retrieveForPrint :: Var -> String
retrieveForPrint (ConstInt i) = show i
retrieveForPrint (ConstBool b) = show b

showArgHeader :: (Type, String) -> String
showArgHeader (tp, aname) = show tp ++ " %" ++ aname

showArgCall :: Var -> String
showArgCall (Reg tp loc) = show tp ++ if loc >= 0 then " %t" ++ show loc else " null"
showArgCall (ConstInt val) = show TInt ++ " " ++ show val
showArgCall str@(ConstString strInd len) = "i8* " ++ show str

scanClear :: [Instr] -> Bool -> [Instr]
scanClear ((Ret tp val):tins) False = (Ret tp val) : (scanClear tins True)
scanClear (VRet : tins) False = VRet : (scanClear tins True)
scanClear (FnEnd : tins) _ = FnEnd : (scanClear tins False)
scanClear ((Label p) : tins) _ = (Label p) : (scanClear tins False)
scanClear (i:tins) True = scanClear tins True
scanClear (i:tins) False = i : scanClear tins False
scanClear [] _ = []

assembleAllocs :: [Instr] -> [Instr]
assembleAllocs ((FnHeader retType fname args):tins) =
     let (body, rest) = cutBody tins [] in
          (FnHeader retType fname args) : (filter isAlloca body) ++ reverse (filter (not . isAlloca) body) ++ assembleAllocs rest
assembleAllocs (w:tins) = w : assembleAllocs tins
assembleAllocs [] = []

cutBody :: [Instr] -> [Instr] -> ([Instr], [Instr])
cutBody (FnEnd : tins) app = (FnEnd : app, tins)
cutBody (i : tins) app = cutBody tins (i : app)

isCustom :: Instr -> Bool
isCustom (Custom _ ) = True
isCustom _ = False

isAlloca :: Instr -> Bool
isAlloca (Alloca loc tp) = True
isAlloca _ = False

tab :: String
tab = "  "

fileHeader :: String
fileHeader = unlines [
    "; Grzegorz B. Zaleski (418494) ;",
    "",
    "declare void @printInt(i32)",
    "declare i32 @readInt()",
    "declare void @error()",
    "declare void @printString(i8*)",
    "declare i8* @readString()",
    "declare i8* @__addStrings(i8*, i8*)",
    "declare i32 @__eqStrings(i8*, i8*)",
    "declare i8* @__calloc(i32)",
    ""
    ]
