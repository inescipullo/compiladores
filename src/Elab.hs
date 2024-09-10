{-|
Module      : Elab
Description : Elabora un término fully named a uno locally closed.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo permite elaborar términos y declaraciones para convertirlas desde
fully named (@STerm) a locally closed (@Term@)
-}

module Elab ( elab, elabDecl) where

import Lang
import Subst
import MonadFD4

-- | 'elab' transforma variables ligadas en índices de de Bruijn
-- en un término dado. 
elab :: STerm -> Term
elab = elab' []

elab' :: [Name] -> STerm -> Term
elab' env (SV p v) =
  -- Tenemos que ver si la variable es Global o es un nombre local
  -- En env llevamos la lista de nombres locales.
  if v `elem` env 
    then  V p (Free v)
    else V p (Global v)

elab' _ (SConst p c) = Const p c
elab' env (SLam p (v,ty) t) = Lam p v ty (close v (elab' (v:env) t))
elab' env (SFix p (f,fty) (x,xty) t) = Fix p f fty x xty (close2 f x (elab' (x:f:env) t))
-- aca los tipos con listas de binders los voy a traer en listas unarias, si no fallo con monadfd4
-- tambien lo mismo con las listas de vars

elab' env (SIfZ p c t e)         = IfZ p (elab' env c) (elab' env t) (elab' env e)
-- Operadores binarios
elab' env (SBinaryOp i o t u) = BinaryOp i o (elab' env t) (elab' env u)
-- Operador Print
elab' env (SPrint i str t) = Print i str (elab' env t)
-- Aplicaciones generales
elab' env (SApp p h a) = App p (elab' env h) (elab' env a)
elab' env (SLet p (v,vty) def body) =  
  Let p v vty (elab' env def) (close v (elab' (v:env) body))

-- | desazucareo lo nuevo

-- | convierto multibinders en binders simples
demultibinding :: [([Name],Ty)] -> [([Name],Ty)]
demultibinding [] = []
demultibinding ((vs,ty):bs) = map (\v -> ([v],ty)) vs ++ demultibinding bs

-- | si tengo argumentos es una fun
let2fun :: STerm -> STerm
let2fun (SLet p b bs def body) = SLam p (head bs) (SLet p b (tail bs) def body)
-- revisar bastante
-- va a ser recursiva
let2fun x = x

-- | resticciones en cant de binders 
-- | sfix necesita dos args
-- | slet necesita 1 arg
checkCantArgs :: MonadFD4 m => STerm -> m STerm
checkCantArgs fix@(SFix p (x:y:xs) t) = return fix
checkCantArgs (SFix p _ _) = failPosFD4 p "Fix necesita al menos dos argumentos"
checkCantArgs (SLet p b [] def body) = failPosFD4 p "Let necesita al menos un argumento"
checkCantArgs (SLet p True [x] def body) = failPosFD4 p "Let rec necesita al menos dos argumentos"
checkCantArgs x = return x

-- | eta expandir sprintun
printun2fun :: STerm -> STerm
printun2fun (SPrintUn p str) = SLam p [([x],Nat)] (SPrint p str (SV p x))
printun2fun x = x 

elabDecl :: Decl STerm -> Decl Term
elabDecl = fmap elab
