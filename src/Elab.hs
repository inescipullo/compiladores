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
elab :: MonadFD4 m => STerm -> m Term
elab sterm = 
  do sterm' <- desugar (multibinders2binders sterm)
     elab' [] sterm'

elab' :: MonadFD4 m => [Name] -> STerm -> m Term
elab' env (SV p v) =
  -- Tenemos que ver si la variable es Global o es un nombre local
  -- En env llevamos la lista de nombres locales.
  if v `elem` env
    then return $ V p (Free v)
    else return $ V p (Global v)

elab' _ (SConst p c) = return (Const p c)
elab' env (SLam p [([v],ty)] t) = 
  do t' <- elab' (v:env) t
     return $ Lam p v ty (close v t')

elab' env (SLam p _ t) = failPosFD4 p "Error elaborando a Term. Lam debería tener un solo argumento."
elab' env (SFix p [([f],fty), ([x],xty)] t) = 
  do t' <- elab' (x:f:env) t
     return $ Fix p f fty x xty (close2 f x t')
elab' env (SFix p _ _) = failPosFD4 p "Error elaborando a Term. Fix debería tener dos argumentos."
-- aca los tipos con listas de binders los voy a traer en listas unarias, si no fallo con monadfd4
-- tambien lo mismo con las listas de vars

elab' env (SIfZ p c t e)         = 
  do c' <- elab' env c
     t' <- elab' env t
     e' <- elab' env e
     return $ IfZ p c' t' e'
-- Operadores binarios
elab' env (SBinaryOp i o t u) = 
  do t' <- elab' env t
     u' <- elab' env u
     return $ BinaryOp i o t' u'
-- Operador Print
elab' env (SPrint i str t) = 
  do t' <- elab' env t
     return $ Print i str t'
elab' env (SPrintUn i str) = failPosFD4 i "Error elaborando a Term. PrintUn no puede ser convertido a Term."
-- Aplicaciones generales
elab' env (SApp p h a) = 
  do h' <- elab' env h
     a' <- elab' env a
     return $ App p h' a'

-- Lets
elab' env (SLet p b [([v],vty)] def body) =
  do def' <- elab' env def
     body' <- elab' (v:env) body
     return $ Let p v vty def' (close v body')
elab' env (SLet p True _ _ _) = failPosFD4 p "Error elaborando a Term. Let no puede ser recursivo."
elab' env (SLet p _ _ _ _) = failPosFD4 p "Error elaborando a Term. Let debería tener un solo argumento."


-- | convierto multibinders en binders simples
demultibinding :: [([Name],Ty)] -> [([Name],Ty)]
demultibinding [] = []
demultibinding ((vs,ty):bs) = map (\v -> ([v],ty)) vs ++ demultibinding bs

-- | convierto terminos con multibinders en terminos con binders simples
multibinders2binders :: STerm -> STerm
multibinders2binders (SLam p bs t) = SLam p (demultibinding bs) (multibinders2binders t)
multibinders2binders (SFix p bs t) = SFix p (demultibinding bs) (multibinders2binders t)
multibinders2binders (SLet p b bs def body) = SLet p b (demultibinding bs) (multibinders2binders def) (multibinders2binders body)
multibinders2binders (SApp p t1 t2) = SApp p (multibinders2binders t1) (multibinders2binders t2)
multibinders2binders (SPrint p s t) = SPrint p s (multibinders2binders t)
multibinders2binders (SBinaryOp p op t1 t2) = SBinaryOp p op (multibinders2binders t1) (multibinders2binders t2)
multibinders2binders (SIfZ p t1 t2 t3) = SIfZ p (multibinders2binders t1) (multibinders2binders t2) (multibinders2binders t3)
multibinders2binders x = x

-- | armo los tipos de las funciones una vez que tengo los binders simples
buildFunType :: [([Name],Ty)] -> Ty -> Ty
buildFunType [] t = t
buildFunType ((_,ty):bs) t = FunTy ty (buildFunType bs t)

-- | Conversión a funciones originales
-- | Si tengo argumentos es una fun. Si no tiene la cantidad correcta de argumentos, falla
desugar :: MonadFD4 m => STerm -> m STerm
desugar (SLet p b [] def body) = failPosFD4 p "Error sacando azúcar. Let necesita al menos un argumento, ninguno dado."
desugar (SLet p False [x] def body) = 
  do def' <- desugar def
     body' <- desugar body
     return (SLet p False [x] def' body') 
desugar (SLet p True [x] def body) = failPosFD4 p "Error sacando azúcar. Let rec necesita al menos dos argumentos, uno dado."
-- Let rec
desugar (SLet p True (([f], fty):x:xs) def body) =
  do def' <- desugar (SFix p (([f], buildFunType (x:xs) fty):x:xs) def) -- no convierto el tipo pq dsp lo hago recursivamente
     body' <- desugar body
     return (SLet p False [([f], buildFunType (x:xs) fty)] def' body')
-- Let fun
desugar (SLet p False (([f], fty):xs) def body) =
  do def' <- desugar (SLam p xs def)
     body' <- desugar body
     return (SLet p False [([f], buildFunType xs fty)] def' body')
desugar (SLet p _ (x:_) _ _) = failPosFD4 p "Error sacando azúcar. Falló el demultibinding. No debería haber multibinding ni el primer argumento de SLet debe no estar en un multibinder."

desugar (SLam p [] t) = failPosFD4 p "Error sacando azúcar. Lam necesita al menos un argumento, ninguno dado."
desugar (SLam p [x] t) = 
  do t' <- desugar t
     return (SLam p [x] t')
desugar (SLam p (([f], fty):xs) t) = 
  do t' <- desugar (SLam p xs t)
     return (SLam p [([f], fty)] t')

desugar (SFix p [] t) = failPosFD4 p "Error sacando azúcar. Fix necesita al menos dos argumentos, ninguno dado."
desugar (SFix p [x] t) = failPosFD4 p "Error sacando azúcar. Fix necesita al menos dos argumentos, uno dado."
desugar (SFix p [([f], fty), y] t) = 
  do t' <- desugar t
     return (SFix p [([f], fty), y] t')
desugar (SFix p (([f], fty):x:xs) t) = 
  do t' <- desugar (SLam p xs t)
     return (SFix p [([f], fty), x] t') -- no hago el build aca pq en la regla de sugar del fix ya tiene el tipo fty construido

desugar (SPrintUn p str) = return (SLam p [(["x"],NatTy)] (SPrint p str (SV p "x")))

desugar (SApp p h a) = 
  do h' <- desugar h
     a' <- desugar a
     return (SApp p h' a')
desugar (SIfZ p c t e) =
  do c' <- desugar c
     t' <- desugar t
     e' <- desugar e
     return (SIfZ p c' t' e')
desugar (SBinaryOp p o t u) =
  do t' <- desugar t
     u' <- desugar u
     return (SBinaryOp p o t' u')
desugar (SPrint p str t) =
  do t' <- desugar t
     return (SPrint p str t')
desugar x = return x

elabDecl :: MonadFD4 m => SDecl STerm -> m (Decl Term)
elabDecl s = elabDecl' (multibinders2bindersDecl s)

multibinders2bindersDecl :: SDecl STerm -> SDecl STerm
multibinders2bindersDecl (SDecl p r n ty binds body) = SDecl p r n ty (demultibinding binds) (multibinders2binders body)

elabDecl' :: MonadFD4 m => SDecl STerm -> m (Decl Term)
elabDecl' (SDecl p False x ty [] t) = 
  do t' <- elab t
     return $ Decl p x ty t'
elabDecl' (SDecl p False f fty xs t) = 
  do t' <- elab (SLam p xs t)
     return $ Decl p f (buildFunType xs fty) t'
elabDecl' (SDecl p True f fty [] t) = failPosFD4 p "Error elaborando a Decl. Let rec sin argumentos."
elabDecl' (SDecl p True f fty xs t) = 
  do t' <- elab (SFix p (([f], buildFunType xs fty):xs) t)
     return $ Decl p f (buildFunType xs fty) t'


