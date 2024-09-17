{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use record patterns" #-}
{-|
Module      : PPrint
Description : Pretty printer para FD4.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module PPrint (
    pp,
    ppTy,
    ppName,
    ppDecl,
    t2doc
    ) where

import Lang
import Subst ( open, open2 )
import Common ( Pos )

import Data.Text ( unpack )
import Prettyprinter.Render.Terminal
  ( renderStrict, italicized, color, colorDull, Color (..), AnsiStyle )
import Prettyprinter
    ( (<+>),
      annotate,
      defaultLayoutOptions,
      layoutSmart,
      nest,
      sep,
      parens,
      Doc,
      Pretty(pretty) )
import MonadFD4 ( gets, MonadFD4 )
import Global ( GlEnv(glb) )
import Data.List (delete)
--import Control.Monad.RWS (Last(getLast))

freshen :: [Name] -> Name -> Name
freshen ns n = let cands = n : map (\i -> n ++ show i) [0..] 
               in head (filter (`notElem` ns) cands)

-- | 'openAll' convierte términos locally nameless
-- a términos fully named abriendo todos las variables de ligadura que va encontrando
-- Debe tener cuidado de no abrir términos con nombres que ya fueron abiertos.
-- Estos nombres se encuentran en la lista ns (primer argumento).
openAll :: (i -> Pos) -> [Name] -> Tm i Var -> STerm
openAll gp ns (V p v) = case v of 
      Bound i ->  SV (gp p) $ "(Bound "++show i++")" --este caso no debería aparecer
                                               --si el término es localmente cerrado
      Free x -> SV (gp p) x
      Global x -> SV (gp p) x
openAll gp ns (Const p c) = SConst (gp p) c
openAll gp ns (Lam p x ty t) = 
  let x' = freshen ns x 
  in SLam (gp p) [([x'],ty)] (openAll gp (x':ns) (open x' t))
openAll gp ns (App p t u) = SApp (gp p) (openAll gp ns t) (openAll gp ns u)
openAll gp ns (Fix p f fty x xty t) = 
  let 
    x' = freshen ns x
    f' = freshen (x':ns) f
  in SFix (gp p) ([([f'],fty),([x'],xty)]) (openAll gp (x:f:ns) (open2 f' x' t))
openAll gp ns (IfZ p c t e) = SIfZ (gp p) (openAll gp ns c) (openAll gp ns t) (openAll gp ns e)
openAll gp ns (Print p str t) = SPrint (gp p) str (openAll gp ns t)
openAll gp ns (BinaryOp p op t u) = SBinaryOp (gp p) op (openAll gp ns t) (openAll gp ns u)
openAll gp ns (Let p v ty m n) = 
    let v'= freshen ns v 
    in  SLet (gp p) False [([v'],ty)] (openAll gp ns m) (openAll gp (v':ns) (open v' n))

--Colores
constColor :: Doc AnsiStyle -> Doc AnsiStyle
constColor = annotate (color Red)
opColor :: Doc AnsiStyle -> Doc AnsiStyle
opColor = annotate (colorDull Green)
keywordColor :: Doc AnsiStyle -> Doc AnsiStyle
keywordColor = annotate (colorDull Green) -- <> bold)
typeColor :: Doc AnsiStyle -> Doc AnsiStyle
typeColor = annotate (color Blue <> italicized)
typeOpColor :: Doc AnsiStyle -> Doc AnsiStyle
typeOpColor = annotate (colorDull Blue)
defColor :: Doc AnsiStyle -> Doc AnsiStyle
defColor = annotate (colorDull Magenta <> italicized)
nameColor :: Doc AnsiStyle -> Doc AnsiStyle
nameColor = id

-- | Pretty printer de nombres (Doc)
name2doc :: Name -> Doc AnsiStyle
name2doc n = nameColor (pretty n)

-- |  Pretty printer de nombres (String)
ppName :: Name -> String
ppName = id

-- | Pretty printer para tipos (Doc)
ty2doc :: Ty -> Doc AnsiStyle
ty2doc NatTy     = typeColor (pretty "Nat")
ty2doc (FunTy x@(FunTy _ _) y) = sep [parens (ty2doc x), typeOpColor (pretty "->"),ty2doc y]
ty2doc (FunTy x y) = sep [ty2doc x, typeOpColor (pretty "->"),ty2doc y] 

-- | Pretty printer para tipos (String)
ppTy :: Ty -> String
ppTy = render . ty2doc

c2doc :: Const -> Doc AnsiStyle
c2doc (CNat n) = constColor (pretty (show n))

binary2doc :: BinaryOp -> Doc AnsiStyle
binary2doc Add = opColor (pretty "+")
binary2doc Sub = opColor (pretty "-")

collectApp :: STerm -> (STerm, [STerm])
collectApp = go [] where
  go ts (SApp _ h tt) = go (tt:ts) h
  go ts h = (h, ts)

parenIf :: Bool -> Doc a -> Doc a
parenIf True = parens
parenIf _ = id

-- t2doc at t :: Doc
-- at: debe ser un átomo
-- | Pretty printing de términos (Doc)
t2doc :: Bool     -- Debe ser un átomo? 
      -> STerm    -- término a mostrar
      -> Doc AnsiStyle
-- Uncomment to use the Show instance for STerm
{- t2doc at x = text (show x) -}
t2doc at (SV _ x) = name2doc x
t2doc at (SConst _ c) = c2doc c
t2doc at (SLam _ args t) =
  parenIf at $
  sep [sep [ keywordColor (pretty "fun")
           , multibinders2doc args
           , opColor(pretty "->")]
      , nest 2 (t2doc False t)]

t2doc at t@(SApp _ _ _) =
  let (h, ts) = collectApp t in
  parenIf at $
  t2doc True h <+> sep (map (t2doc True) ts)

t2doc at (SFix _ args m) =
  parenIf at $
  sep [ sep [keywordColor (pretty "fix")
                  , multibinders2doc args
                  , opColor (pretty "->") ]
      , nest 2 (t2doc False m)
      ]
t2doc at (SIfZ _ c t e) =
  parenIf at $
  sep [keywordColor (pretty "ifz"), nest 2 (t2doc False c)
     , keywordColor (pretty "then"), nest 2 (t2doc False t)
     , keywordColor (pretty "else"), nest 2 (t2doc False e) ]

t2doc at (SPrintUn _ str) =
  parenIf at $
  sep [keywordColor (pretty "print"), pretty (show str)]

t2doc at (SPrint _ str t) =
  parenIf at $
  sep [keywordColor (pretty "print"), pretty (show str), t2doc True t]

t2doc at (SLet _ is_rec args t t') =
  parenIf at $
  sep [
    sep [keywordColor (pretty "let")
       , if is_rec then keywordColor (pretty "rec") else mempty
       , multibinders2doclet args
       , opColor (pretty "=") ]
  , nest 2 (t2doc False t)
  , keywordColor (pretty "in")
  , nest 2 (t2doc False t') ]

t2doc at (SBinaryOp _ o a b) =
  parenIf at $
  t2doc True a <+> binary2doc o <+> t2doc True b

binding2doc :: (Name, Ty) -> Doc AnsiStyle
binding2doc (x, ty) =
  parens (sep [name2doc x, pretty ":", ty2doc ty])

multibinding2doc :: ([Name], Ty) -> Doc AnsiStyle
multibinding2doc ([x], ty) = binding2doc (x, ty)
multibinding2doc (x:xs, ty) = parens (sep (map name2doc (x:xs) ++ [pretty ":", ty2doc ty]))
multibinding2doc ([], ty) = error "No debería entrar en este caso nunca"

multibinders2doc :: [([Name], Ty)] -> Doc AnsiStyle
multibinders2doc [] = mempty
multibinders2doc [x] = multibinding2doc x
multibinders2doc (x:xs) = sep [multibinding2doc x, multibinders2doc xs]

multibinders2doclet :: [([Name], Ty)] -> Doc AnsiStyle
multibinders2doclet [] = mempty
multibinders2doclet (([], _):_) = error "Sin nombres de argumentos para un tipo en multibinders2doclet" -- nunca deberia entrar aca
multibinders2doclet (([x], ty):xs) = sep [name2doc x, multibinders2doc xs, pretty ":", ty2doc ty] 
multibinders2doclet ((x:s, ty):xs) = sep [name2doc x, multibinders2doc ((s, ty):xs), pretty ":", ty2doc ty]

-- | Pretty printing de términos (String)
pp :: MonadFD4 m => TTerm -> m String
-- Uncomment to use the Show instance for Term
{- pp = show -}
pp t = do
       gdecl <- gets glb
       return (render . t2doc False $ binders2multibinders (resugar (openAll fst (map declName gdecl) t)))

-- | Agrego azúcar sintáctico a un término antes de imprimirlo
resugar :: STerm -> STerm
resugar (SLam p args (SLam p' args' t)) = resugar (SLam p (args++args') t)
resugar (SLam p [(["x"],NatTy)] (SPrint p' str (SV p'' "x"))) | p==p' && p==p'' = SPrintUn p str
resugar (SLam p args t) = SLam p args (resugar t)

resugar (SFix p args (SLam p' args' t)) = resugar (SFix p (args++args') t)
resugar (SFix p args t) = SFix p args (resugar t)

resugar (SLet p False [([f],FunTy ty1 ty2)] (SLam p' [([x],ty1')] t) t') | ty1==ty1' = 
  resugar (SLet p False [([f],ty2),([x],ty1)] t t')
resugar (SLet p False (([f],FunTy ty1 ty2):xs) (SLam p' (([x],ty1'):xs') t) t') | ty1==ty1' = 
  resugar (SLet p False ((([f],ty2):xs)++[([x],ty1)]) (SLam p' xs' t) t')

resugar (SLet p False [([f],FunTy ty1 ty2)] (SFix p' [([_],FunTy ty1' ty2'),([x],ty1'')] t) t') | ty1==ty1' && ty1==ty1'' && ty2==ty2' = 
  resugar (SLet p True [([f],ty2),([x],ty1)] t t')

resugar (SLet p True (([f],FunTy ty2 ty3):([x1],ty1):xs) (SLam p' [([x2],ty2')] t) t') | ty2==ty2' = 
  resugar (SLet p True (([f],ty3):([x1],ty1):xs++[([x2],ty2)]) t t')
resugar (SLet p True (([f],FunTy ty2 ty3):([x1],ty1):xs) (SLam p' (([x2],ty2'):xs2) t) t') | ty2==ty2' = 
  resugar (SLet p True (([f],ty3):([x1],ty1):xs++[([x2],ty2)]) (SLam p' xs2 t) t')

resugar (SLet p is_rec args def body) = SLet p is_rec args (resugar def) (resugar body)

resugar (SApp p t u) = SApp p (resugar t) (resugar u)
resugar (SIfZ p c t e) = SIfZ p (resugar c) (resugar t) (resugar e)
resugar (SBinaryOp p op t u) = SBinaryOp p op (resugar t) (resugar u)
resugar (SPrint p str t) = SPrint p str (resugar t)
resugar x = x


-- | Convierto binders simples en multibinders
remultibinding :: [([Name], Ty)] -> [([Name], Ty)]
remultibinding [] = []
remultibinding [x] = [x]
remultibinding ((x1,ty1):(x2,ty2):xs) = 
  if ty1 == ty2 then remultibinding ((x1++x2,ty1):xs) else (x1,ty1):remultibinding ((x2,ty2):xs)

-- | Convierto terminos con binders simples en terminos con multibinders
binders2multibinders :: STerm -> STerm
binders2multibinders (SLam p bs t) = SLam p (remultibinding bs) (binders2multibinders t)
binders2multibinders (SFix p bs t) = SFix p (remultibinding bs) (binders2multibinders t)
binders2multibinders (SLet p b bs def body) = SLet p b (remultibinding bs) (binders2multibinders def) (binders2multibinders body)
binders2multibinders (SApp p t1 t2) = SApp p (binders2multibinders t1) (binders2multibinders t2)
binders2multibinders (SPrint p s t) = SPrint p s (binders2multibinders t)
binders2multibinders (SBinaryOp p op t1 t2) = SBinaryOp p op (binders2multibinders t1) (binders2multibinders t2)
binders2multibinders (SIfZ p t1 t2 t3) = SIfZ p (binders2multibinders t1) (binders2multibinders t2) (binders2multibinders t3)
binders2multibinders x = x

render :: Doc AnsiStyle -> String
render = unpack . renderStrict . layoutSmart defaultLayoutOptions

getLastType :: Ty -> Ty
getLastType (FunTy _ t) = getLastType t
getLastType t = t

resugarDecl :: Decl STerm -> SDecl STerm
resugarDecl (Decl p f ty (SLam _ args t)) =
  SDecl p False f (getLastType ty) args t
resugarDecl (Decl p f ty (SFix _ (([f'], ty'):args) t)) | f == f' =
  SDecl p True f' (getLastType ty) args t
resugarDecl (Decl p x ty t) = 
  SDecl p False x ty [] t 

-- | Pretty printing de declaraciones
ppDecl :: MonadFD4 m => Decl TTerm -> m String
ppDecl (Decl p x ty t) = do 
  gdecl <- gets glb
  let body = binders2multibinders $ resugar (openAll fst (delete x (map declName gdecl)) t)
  let (SDecl p' is_rec x' ty' args' t') = resugarDecl (Decl p x ty body)
  return (render $ sep [defColor (pretty "let")
                       , if is_rec then defColor (pretty "rec") else mempty
                       , name2doc x' 
                       , multibinders2doc args'
                       , pretty ":"
                       , ty2doc ty'
                       , defColor (pretty "=")] 
                   <+> nest 2 (t2doc False t'))
                         

