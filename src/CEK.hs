module CEK (evalCEK) where

import Lang
import MonadFD4
import Common (Pos)
import Eval (semOp)
import Subst (substN)

data Val = 
    VConst (Pos,Ty) Const
    | VClos (Pos,Ty) Clos 
    
data Clos = 
    VClosFix Env Name Ty Name Ty TTerm 
    | VClosFun Env Name Ty TTerm

type Env = [Val] -- vamos a usar indices de de Bruijn

-- regla que consume la clausura y extiende el entorno, basta 
-- con agg al head (0 apunta a la variable mas reciente y se
-- introduce un nuevo binding por lo que las otras pasan a ser +1)

data Frame = 
    FApp2 Env TTerm 
    | FClos Clos
    | FIfZ Env TTerm TTerm 
    | FBinaryOp1 BinaryOp Env TTerm
    | FBinaryOp2 BinaryOp Val
    | FPrint String
    -- no agg un frame correspondiente a let porque hago una conversion a app de fun

type Kont = [Frame]

search :: MonadFD4 m => TTerm -> Env -> Kont -> m Val
search (Print _ s t) rho k = search t rho (FPrint s:k)
search (BinaryOp _ op t u) rho k = search t rho (FBinaryOp1 op rho u:k)
search (IfZ _ c t e) rho k = search c rho (FIfZ rho t e:k)
search (App _ t u) rho k = search t rho (FApp2 rho u:k)
search (V _ (Bound i)) rho k = destroy (rho !! i) k
search (V (p,_) (Free x)) _ _ = failPosFD4 p $ "Variable libre en search de máquina CEK "++x
search (V (p,_) (Global x)) rho k = do
    t <- lookupDecl x
    case t of
        Nothing -> failPosFD4 p $ "Variable global no declarada en search de máquina CEK "++x
        Just t' -> search t' rho k
search (Const i c) _ k = destroy (VConst i c) k
search (Lam i x xty (Sc1 t)) rho k = destroy (VClos i (VClosFun rho x xty t)) k
search (Fix i f fty x xty (Sc2 t)) rho k = destroy (VClos i (VClosFix rho f fty x xty t)) k
search (Let i x xty e sct) rho k = search (App i (Lam i x xty sct) e) rho k -- conversion let a fun se podria charlar

-- hay patterns que faltan donde deberiamos tirar errores mas descriptivos
destroy :: MonadFD4 m => Val -> Kont -> m Val
destroy v [] = 
    return v
destroy v@(VConst _ (CNat n)) (FPrint s:k) = do
    printFD4 $ s ++ show n
    destroy v k
destroy n@(VConst _ (CNat _)) (FBinaryOp1 op rho u:k) = 
    search u rho (FBinaryOp2 op n:k)
destroy (VConst _ (CNat n')) (FBinaryOp2 op (VConst i (CNat n)):k) =
    destroy (VConst i (CNat (semOp op n n'))) k
destroy (VConst _ (CNat 0)) (FIfZ rho t e:k) = search t rho k
destroy (VConst _ (CNat _)) (FIfZ rho t e:k) = search e rho k
destroy (VClos _ clos) (FApp2 rho t:k) = search t rho (FClos clos:k)
destroy v (FClos (VClosFun rho x xty t):k) = search t (v:rho) k
-- ver si alguno de estos no va
destroy v@(VConst i _) (FClos (VClosFix rho f fty x xty t):k) = search t (v:VClos i (VClosFix rho f fty x xty t):rho) k -- quiero que la x quede arriba pq es lo mas adentro en bindings, el f despues (o mas abajo en la lista)
destroy v@(VClos i _) (FClos (VClosFix rho f fty x xty t):k) = search t (v:VClos i (VClosFix rho f fty x xty t):rho) k
-- caso let? entra directo al hacer la conversion de let a fun
destroy (VConst (p,_) (CNat _)) (FApp2 _ _:_) = failPosFD4 p $ "El primer argumento de una aplicación debe ser una clausura (una función)."
destroy (VConst (p,_) (CNat _)) (FBinaryOp2 op (VClos _ _):_) = failPosFD4 p $ "El segundo argumento de la operación binaria "++show op++" debe evaluar a una constante."
destroy (VClos (p,_) _) (FPrint _:_) = failPosFD4 p $ "El argumento de un print debe evaluar a una constante."
destroy (VClos (p,_) _) (FBinaryOp1 op _ _:_) = failPosFD4 p $ "El primer argumento de la operación binaria "++show op++" debe evaluar a una constante."
destroy (VClos (p,_) _) (FBinaryOp2 op _:_) = failPosFD4 p $ "El segundo argumento de la operación binaria "++show op++" debe evaluar a una constante."
destroy (VClos (p,_) _) (FIfZ _ _ _:__) = failPosFD4 p $ "El primer argumento de un IfZ debe evaluar a una constante."


val2tterm :: Val -> TTerm
val2tterm (VConst i c) = Const i c
val2tterm (VClos i (VClosFun rho x xty t)) = substN (map val2tterm rho) (Lam i x xty (Sc1 t))
val2tterm (VClos i (VClosFix rho f fty x xty t)) = substN (map val2tterm rho) (Fix i f fty x xty (Sc2 t))

evalCEK :: MonadFD4 m => TTerm -> m TTerm
evalCEK t = do
    val <- search t [] []
    return $ val2tterm val