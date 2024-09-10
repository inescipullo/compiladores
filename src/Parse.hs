{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}
{-|
Module      : Parse
Description : Define un parser de términos FD40 a términos fully named.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module Parse (tm, Parse.parse, decl, runP, P, program, declOrTm) where

import Prelude hiding ( const )
import Lang hiding (getPos)
import Common
import Text.Parsec hiding (runP,parse)
--import Data.Char ( isNumber, ord )
import qualified Text.Parsec.Token as Tok
import Text.ParserCombinators.Parsec.Language --( GenLanguageDef(..), emptyDef )
import qualified Text.Parsec.Expr as Ex
import Text.Parsec.Expr (Operator, Assoc)
import Control.Monad.Identity (Identity)

type P = Parsec String ()

-----------------------
-- Lexer
-----------------------
-- | Analizador de Tokens
lexer :: Tok.TokenParser u
lexer = Tok.makeTokenParser langDef

langDef :: LanguageDef u
langDef = emptyDef {
         commentLine    = "#",
         reservedNames = ["let", "rec","fun", "fix", "then", "else","in",
                           "ifz", "print","Nat","type"],
         reservedOpNames = ["->",":","=","+","-"]
        }

whiteSpace :: P ()
whiteSpace = Tok.whiteSpace lexer

natural :: P Integer
natural = Tok.natural lexer

stringLiteral :: P String
stringLiteral = Tok.stringLiteral lexer

parens :: P a -> P a
parens = Tok.parens lexer

identifier :: P String
identifier = Tok.identifier lexer

reserved :: String -> P ()
reserved = Tok.reserved lexer

reservedOp :: String -> P ()
reservedOp = Tok.reservedOp lexer

tyIdentifier :: P String
tyIdentifier = Tok.lexeme lexer $ do
  c  <- upper
  cs <- many (identLetter langDef)
  return (c:cs)

-----------------------
-- Parsers
-----------------------

num :: P Int
num = fromInteger <$> natural

var :: P Name
var = identifier

getPos :: P Pos
getPos = do pos <- getPosition
            return $ Pos (sourceLine pos) (sourceColumn pos)

tyatom :: P Ty
tyatom = (reserved "Nat" >> return NatTy)
         <|> parens typeP

typeP :: P Ty
typeP = try (do
          x <- tyatom
          reservedOp "->"
          y <- typeP
          return (FunTy x y))
      <|> tyatom

const :: P Const
const = CNat <$> num

printOp :: P STerm
printOp = do i <- getPos
             reserved "print"
             str <- option "" stringLiteral
             try (do a <- atom
                     return (SPrint i str a))
              <|>
              return (SPrintUn i str)

binary :: String -> BinaryOp -> Assoc -> Operator String () Identity STerm
binary s f = Ex.Infix (reservedOp s >> return (SBinaryOp NoPos f))

table :: [[Operator String () Identity STerm]]
table = [[binary "+" Add Ex.AssocLeft,
          binary "-" Sub Ex.AssocLeft]]

expr :: P STerm
expr = Ex.buildExpressionParser table tm

atom :: P STerm
atom =     (flip SConst <$> const <*> getPos)
       <|> flip SV <$> var <*> getPos
       <|> parens expr
       <|> printOp

-- parsea un par (variable : tipo)
binding :: P ([Name], Ty)
binding = do v <- var
             reservedOp ":"
             ty <- typeP
             return ([v], ty)

multibinding :: P ([Name], Ty)
multibinding = do x <- many1 var
                  reservedOp ":"
                  ty <- typeP
                  return (x, ty)

multibinders0 :: P [([Name], Ty)]
multibinders0 = try (do (x,ty) <- parens multibinding
                        xs <- multibinders0
                        return ((x,ty):xs))
                <|>
                return []

-- parsea una lista de multibindings
multibinders :: P [([Name], Ty)]
multibinders = do (x,ty) <- parens multibinding -- por lo menos un argumento
                  xs <- multibinders0
                  return ((x,ty):xs)

multibindersfix :: P [([Name], Ty)]
multibindersfix = do f <- parens binding -- el primer argumento es la funcion, que no puede tener multibinding
                     args <- multibinders
                     return (f:args)

lam :: P STerm
lam = do i <- getPos
         reserved "fun"
         args <- multibinders
         reservedOp "->"
         t <- expr
         return (SLam i args t)

-- Nota el parser app también parsea un solo atom.
app :: P STerm
app = do i <- getPos
         f <- atom
         args <- many atom
         return (foldl (SApp i) f args)

ifz :: P STerm
ifz = do i <- getPos
         reserved "ifz"
         c <- expr
         reserved "then"
         t <- expr
         reserved "else"
         e <- expr
         return (SIfZ i c t e)

fix :: P STerm
fix = do i <- getPos
         reserved "fix"
         args <- multibindersfix
         reservedOp "->"
         t <- expr
         return (SFix i args t)

letargs :: P [([Name], Ty)]
letargs = try (do f <- var
                  args <- multibinders
                  reservedOp ":"
                  ty <- typeP
                  return (([f],ty):args))
          <|>
          try (do x <- parens binding -- para permitir un unico argumento con parentesis
                  return [x])
          <|>
          try (do x <- binding -- para permitir un unico argumneto sin parentesis
                  return [x])

isrec :: P Bool
isrec = try (reserved "rec" >> return True) <|> return False

letexp :: P STerm
letexp = do
  i <- getPos
  reserved "let"
  esrec <- isrec
  args <- letargs
  reservedOp "="
  def <- expr
  reserved "in"
  body <- expr
  return (SLet i esrec args def body)

-- | Parser de términos
tm :: P STerm
tm = app <|> lam <|> ifz <|> printOp <|> fix <|> letexp

declargs :: P ((Name, Ty), [([Name], Ty)])
declargs = try (do  name <- var
                    args <- multibinders
                    reservedOp ":"
                    ty <- typeP
                    return ((name, ty), args))
            <|>
            do name <- var
               reservedOp ":"
               ty <- typeP
               return ((name, ty), [])
-- para pensar: va con multibinders0 y sin el choice? como podria evitar parsear funciones mal escritas? (sin argumentos) mepa que no tiene mucho sentido

-- | Parser de declaraciones
decl :: P SDecl
decl = do
     i <- getPos
     reserved "let"
     esrec <- isrec
     ((name, ty), args) <- declargs
     reservedOp "=" 
     t <- expr
     return (SDecl i esrec name ty args t)

-- | Parser de programas (listas de declaraciones) 
program :: P [SDecl]
program = many decl

-- | Parsea una declaración a un término
-- Útil para las sesiones interactivas
declOrTm :: P (Either SDecl STerm)
declOrTm =  try (Left <$> decl) <|> (Right <$> expr)

-- Corre un parser, chequeando que se pueda consumir toda la entrada
runP :: P a -> String -> String -> Either ParseError a
runP p s filename = runParser (whiteSpace *> p <* eof) () filename s

--para debugging en uso interactivo (ghci) de terms
parse :: String -> STerm
parse s = case runP expr s "" of
            Right t -> t
            Left e -> error ("no parse: " ++ show s)

-- para debugging en uso interactivo (ghci) de declaraciones
parse2 :: String -> SDecl
parse2 s = case runP decl s "" of
            Right t -> t
            Left e -> error ("no parse: " ++ show s)