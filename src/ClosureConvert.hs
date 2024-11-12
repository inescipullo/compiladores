module ClosureConvert where

import IR
import Lang
import MonadFD4
import Subst
import Control.Monad.Writer

freshen :: Name -> StateT Int (Writer [IrDecl]) Name
freshen name = do 
    n <- get
    put (n+1)
    return $ name ++ "_" ++ (show n)

changeArgs :: Name -> [(Name, Ty)] -> Ir -> Ir
changeArgs = go 1
  where
    go :: Int -> Name -> [(Name, Ty)] -> Ir -> Ir
    go _ clos [] b = b
    go i clos ((n, ty):ns) b = 
        IrLet n (ty2tyir ty) 
            (IrAccess (IrVar clos) (ty2tyir ty) i) 
            (go (i + 1) clos ns b)

ret2tyir :: Ty -> IrTy
ret2tyir (FunTy _ _ t) = ty2tyir t
ret2tyir (NatTy _) = undefined

ty2tyir :: Ty -> IrTy
ty2tyir (NatTy _) = IrInt
ty2tyir (FunTy _ _ _) = IrClo

closureConvert :: TTerm -> StateT Int (Writer [IrDecl]) Ir
closureConvert (V _ (Bound i)) = error $ "Bound en closureConvert " ++ (show i)
closureConvert (V _ (Free s)) = return $ IrVar s
closureConvert (V _ (Global s)) = return $ IrGlobal s
closureConvert (Const _ c) = return $ IrConst c
closureConvert (Print _ s t) = do -- asi porque si no queda mal el orden
    t' <- closureConvert t
    printname <- freshen "_print_"
    return $ IrLet printname IrInt t' (IrPrint s (IrVar printname))
closureConvert (IfZ _ c t1 t2) = do 
    cir <- closureConvert c 
    t1ir <- closureConvert t1
    t2ir <- closureConvert t2 
    return $ IrIfZ cir t1ir t2ir
closureConvert (BinaryOp _ op t1 t2) = do 
    t1ir <- closureConvert t1
    t2ir <- closureConvert t2
    return $ IrBinaryOp op t1ir t2ir
closureConvert (Let _ n ty def body) = do
    name <- freshen $ "_let_" ++ n 
    defir <- closureConvert def 
    bodyir <- closureConvert (open name body) --
    return $ IrLet name (ty2tyir ty) defir bodyir
closureConvert (App _ ft xt) = do
    clos <- closureConvert ft
    t2ir <- closureConvert xt
    fun <- freshen "_fun"
    let t2' = IrCall (IrAccess (IrVar fun) IrClo 0) [IrVar fun, t2ir] IrInt
    return $ IrLet fun IrClo clos t2' 
closureConvert (Lam (_,fty) name ty sc@(Sc1 t)) = do 
    namefun <- freshen $ "_lam_" ++ name 
    namearg <- freshen $ "_arg_" ++ name 
    nameclos <- freshen $ "_clos_" ++ name
    body' <- closureConvert (open namearg sc)
    let freevars = freeVarsWithTy t
    let body = changeArgs nameclos freevars body'
    let decl = IrFun namefun (ret2tyir fty) [(nameclos, IrClo), (namearg, ty2tyir ty)] body -- con la currificacion como saco el tipo de los args? 
    tell [decl]
    let listIr = map (IrVar . fst) freevars
    return $ MkClosure namefun listIr
closureConvert (Fix _ f fty x xty sc@(Sc2 t)) = do
    namefun <- freshen $ "_fix_" ++ f
    namearg <- freshen $ "_arg_" ++ x
    nameclos <- freshen $ "_clos_" ++ f
    body' <- closureConvert (open2 nameclos namearg sc)
    let freevars = freeVarsWithTy t
    let body = changeArgs nameclos freevars body'
    let decl = IrFun namefun (ty2tyir fty) [(nameclos, IrClo), (namearg, (ty2tyir xty))] body 
    tell [decl]
    let listIr = map (IrVar . fst) freevars
    return $ MkClosure namefun listIr

decl2declir :: Decl TTerm -> StateT Int (Writer [IrDecl]) IrDecl
decl2declir (Decl _ n t b) = IrVal n (ty2tyir t) <$> closureConvert b

runCC :: [Decl TTerm] -> IrDecls
runCC ds = 
    let ((decls, _), ccs) = runWriter (runStateT (mapM decl2declir ds) 0) 
    in IrDecls (ccs ++ decls)

ccWrite :: String -> FilePath -> IO ()
ccWrite c filename = writeFile filename c