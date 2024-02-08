{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use when" #-}
{-# HLINT ignore "Use guards" #-}
module ASTOpti where

import qualified Latte.Abs as L

type Pos = L.BNFC'Position

optimiseProgramme :: L.Program -> L.Program
optimiseProgramme (L.Program pos defs) =
    let parsed = map optiBody defs in
        if parsed == defs
            then L.Program pos parsed
            else optimiseProgramme $ L.Program pos parsed

optiBody :: L.TopDef -> L.TopDef
optiBody (L.FnDef pos retType (L.Ident fname) args (L.Block ppos stmts)) = let o_stmts = map optiStmt stmts in
    L.FnDef pos retType (L.Ident fname) args (L.Block ppos o_stmts)

optiBody (L.CDef pos (L.Ident cname) (L.CBlock ppos cstmts)) = let o_cstmts = map optiCStmt cstmts in
    L.CDef pos (L.Ident cname) (L.CBlock ppos cstmts)

optiBody (L.CExtDef pos (L.Ident cname) ptag (L.CBlock ppos cstmts)) = let o_cstmts = map optiCStmt cstmts in
    L.CExtDef pos (L.Ident cname) ptag (L.CBlock ppos o_cstmts)

optiCStmt :: L.CStmt -> L.CStmt
optiCStmt (L.CMethod pos tp tag args (L.Block ppos stmts)) = let o_stmts = map optiStmt stmts in
    L.CMethod pos tp tag args (L.Block ppos o_stmts)
optiCStmt cstmt = cstmt

optiStmt :: L.Stmt -> L.Stmt
optiStmt (L.BStmt pos (L.Block ppos stmts)) = L.BStmt pos (L.Block ppos (map optiStmt stmts))

optiStmt (L.Cond pos e stmt) =
    case optiExpr e of
        (L.ELitTrue _) -> optiStmt stmt
        (L.ELitFalse _) -> L.Empty pos
        val -> L.Cond pos val (optiStmt stmt)

optiStmt (L.CondElse pos e stmt_true stmt_else) =
    case optiExpr e of
        (L.ELitTrue _) -> optiStmt stmt_true
        (L.ELitFalse _) -> optiStmt stmt_else
        val -> L.CondElse pos val (optiStmt stmt_true) (optiStmt stmt_else)

optiStmt (L.While pos e stmt) =
    case optiExpr e of
        t@(L.ELitTrue ppos) -> L.While pos t (optiStmt stmt)
        (L.ELitFalse _) -> L.Empty pos
        val -> L.While pos val (optiStmt stmt)

optiStmt (L.Ass pos tag e2) = L.Ass pos tag (optiExpr e2)

optiStmt (L.CAss pos e1 (L.Ident etag) e2) = 
    case optiExpr e1 of 
        L.ECNew _ tag -> L.Empty pos
        o1 -> L.CAss pos o1 (L.Ident etag) (optiExpr e2) 

optiStmt (L.Ret pos e) = L.Ret pos (optiExpr e)

optiStmt (L.Decl pos tp items) = L.Decl pos tp (map optiItem items)
    where
    optiItem :: L.Item -> L.Item
    optiItem (L.Init pos tag e) = L.Init pos tag (optiExpr e)
    optiItem i = i

optiStmt (L.SExp pos e) = L.SExp pos (optiExpr e)

optiStmt stmt = stmt

optiExpr :: L.Expr -> L.Expr
optiExpr (L.Neg pos e) = 
    case optiExpr e of 
        (L.ELitInt _ n) -> L.ELitInt pos (-n)
        el -> L.Neg pos el

optiExpr (L.Not pos e) =
    case optiExpr e of
        L.ELitTrue _ -> L.ELitFalse pos
        L.ELitFalse _ -> L.ELitTrue pos
        ev -> L.Not pos ev

optiExpr e@(L.EMul pos e1 op e2) =
    case (op, optiExpr e1, optiExpr e2) of
        (L.Times _, L.ELitInt _ a, L.ELitInt _ b) -> L.ELitInt pos (a * b)
        (_, el, er@(L.ELitInt _ 0))               -> L.EMul pos el op er
        (L.Div _, L.ELitInt _ a, L.ELitInt _ b)   -> L.ELitInt pos (a `div` b)
        (L.Mod _, L.ELitInt _ a, L.ELitInt _ b)   -> L.ELitInt pos (a `rem` b) -- `mod` doesnt work for (-5) % 3
        (_, el, er)                               -> L.EMul pos el op er

optiExpr (L.EAdd pos e1 op e2) =
    case (op, optiExpr e1, optiExpr e2) of
        (L.Plus _, L.ELitInt _ a, L.ELitInt _ b) -> L.ELitInt pos (a + b)
        (L.Plus _, L.EString _ a, L.EString _ b) -> L.EString pos (a ++ b)
        (L.Minus _, L.ELitInt _ a, L.ELitInt _ b) -> L.ELitInt pos (a - b)
        (_, el, er) -> L.EAdd pos el op er

optiExpr (L.EAnd pos e1 e2) =
    case (optiExpr e1, optiExpr e2) of
        (L.ELitTrue _, L.ELitTrue _)   -> L.ELitTrue pos
        (L.ELitFalse _, L.ELitTrue _)  -> L.ELitFalse pos
        (L.ELitTrue _, L.ELitFalse _)  -> L.ELitFalse pos
        (L.ELitFalse _, L.ELitFalse _) -> L.ELitFalse pos
        (el, er) -> L.EAnd pos el er

optiExpr (L.EOr pos e1 e2) =
    case (optiExpr e1, optiExpr e2) of
        (L.ELitTrue _, L.ELitTrue _)   -> L.ELitTrue pos
        (L.ELitFalse _, L.ELitTrue _)  -> L.ELitTrue pos
        (L.ELitTrue _, L.ELitFalse _)  -> L.ELitTrue pos
        (L.ELitFalse _, L.ELitFalse _) -> L.ELitFalse pos
        (el, er) -> L.EOr pos el er

optiExpr (L.ERel pos e1 op e2) =
    case (optiExpr e1, optiExpr e2) of
    (L.ELitInt _ a, L.ELitInt _ b) ->
        case op of
            L.LTH _ -> pack (a < b) pos
            L.LE _ -> pack (a <= b) pos
            L.GTH _ -> pack (a > b) pos
            L.GE _ -> pack (a >= b) pos
            L.EQU _ -> pack (a == b) pos
            L.NE _ -> pack (a /= b) pos
    (L.EString _ a, L.EString _ b) ->
        case op of
            L.EQU _ -> pack (a == b) pos
            L.NE _ -> pack (a /= b) pos
            w -> error "Compilator failure"
    (L.ELitTrue _, L.ELitTrue _) -> 
        case op of 
            L.EQU _ -> L.ELitTrue pos 
            L.NE _ -> L.ELitFalse pos
            w -> error "Compilator failure"
    (L.ELitTrue _, L.ELitFalse _) -> 
        case op of 
            L.EQU _ -> L.ELitFalse pos 
            L.NE _ -> L.ELitTrue pos
            w -> error "Compilator failure"
    (L.ELitFalse _, L.ELitTrue _) -> 
        case op of 
            L.EQU _ -> L.ELitFalse pos 
            L.NE _ -> L.ELitTrue pos
            w -> error "Compilator failure"
    (L.ELitFalse _, L.ELitFalse _) -> 
        case op of 
            L.EQU _ -> L.ELitTrue pos 
            L.NE _ -> L.ELitFalse pos
            w -> error "Compilator failure"
    (el, L.ELitTrue _) -> 
        case op of 
            L.EQU _ -> el -- == true
            L.NE _ -> optiExpr $ L.Not pos el -- != true
            w -> error "Compilator failure"
    (el, L.ELitFalse _) -> 
        case op of 
            L.EQU _ -> optiExpr $ L.Not pos el -- == false
            L.NE _ -> el -- != false
            w -> error "Compilator failure"
    (L.ELitTrue _, er) -> 
        case op of 
            L.EQU _ -> er
            L.NE _ -> optiExpr $ L.Not pos er
            w -> error "Compilator failure"
    (L.ELitFalse _, er) -> 
        case op of 
            L.EQU _ -> optiExpr $ L.Not pos er
            L.NE _ -> er
            w -> error "Compilator failure"
    (el, er) -> L.ERel pos el op er
    where
        pack :: Bool -> Pos -> L.Expr
        pack True = L.ELitTrue
        pack False = L.ELitFalse

optiExpr (L.EApp pos tag args) = L.EApp pos tag (map optiExpr args)

optiExpr (L.ECMeth pos e (L.Ident tag) args) = L.ECMeth pos (optiExpr e) (L.Ident tag) (map optiExpr args)
    
optiExpr e = e
