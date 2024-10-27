{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-|
Module      : Bytecompile
Description : Compila a bytecode. Ejecuta bytecode.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo permite compilar módulos a la Macchina. También provee
una implementación de la Macchina para ejecutar el bytecode.
-}
module Bytecompile
  (Bytecode, runBC, bcWrite, bcRead, bytecompileModule, showBC)
 where

import Lang
import Subst
import MonadFD4

import qualified Data.ByteString.Lazy as BS
import Data.Binary ( Word32, Binary(put, get), decode, encode )
import Data.Binary.Put ( putWord32le )
import Data.Binary.Get ( getWord32le, isEmpty )

import Data.List (intercalate)
import Data.Char
import Eval (semOp)

type Opcode = Int
type Bytecode = [Int]

data Val = I Int 
          | Fun Environment Bytecode 
          | RA Environment Bytecode deriving Show

type Environment = [Val]
type Stack = [Val]
data EFix = FixFun EFix Bytecode Environment

newtype Bytecode32 = BC { un32 :: [Word32] }

{- Esta instancia explica como codificar y decodificar Bytecode de 32 bits -}
instance Binary Bytecode32 where
  put (BC bs) = mapM_ putWord32le bs
  get = go
    where go =
           do
            empty <- isEmpty
            if empty
              then return $ BC []
              else do x <- getWord32le
                      BC xs <- go
                      return $ BC (x:xs)

{- Estos sinónimos de patrón nos permiten escribir y hacer
pattern-matching sobre el nombre de la operación en lugar del código
entero, por ejemplo:

   f (CALL : cs) = ...

 Notar que si hubieramos escrito algo como
   call = 5
 no podríamos hacer pattern-matching con `call`.

 En lo posible, usar estos códigos exactos para poder ejectutar un
 mismo bytecode compilado en distintas implementaciones de la máquina.
-}
pattern NULL     = 0
pattern RETURN   = 1
pattern CONST    = 2
pattern ACCESS   = 3
pattern FUNCTION = 4
pattern CALL     = 5
pattern ADD      = 6
pattern SUB      = 7
pattern FIX      = 9
pattern STOP     = 10
pattern SHIFT    = 11
pattern DROP     = 12
pattern PRINT    = 13
pattern PRINTN   = 14
pattern JUMP     = 15
pattern IFZ      = 16
pattern TAILCALL = 17

--función util para debugging: muestra el Bytecode de forma más legible.
showOps :: Bytecode -> [String]
showOps [] = []
showOps (NULL:xs)        = "NULL" : showOps xs
showOps (RETURN:xs)      = "RETURN" : showOps xs
showOps (CONST:i:xs)     = ("CONST " ++  show i) : showOps xs
showOps (ACCESS:i:xs)    = ("ACCESS " ++ show i) : showOps xs
showOps (FUNCTION:i:xs)  = ("FUNCTION len=" ++ show i) : showOps xs
showOps (CALL:xs)        = "CALL" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (SUB:xs)         = "SUB" : showOps xs
showOps (FIX:xs)         = "FIX" : showOps xs
showOps (STOP:xs)        = "STOP" : showOps xs
showOps (JUMP:i:xs)      = ("JUMP off=" ++ show i) : showOps xs
showOps (SHIFT:xs)       = "SHIFT" : showOps xs
showOps (DROP:xs)        = "DROP" : showOps xs
showOps (PRINT:xs)       = let (msg,_:rest) = span (/=NULL) xs
                           in ("PRINT " ++ show (bc2string msg)) : showOps rest
showOps (PRINTN:xs)      = "PRINTN" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (IFZ:i:xs)       = ("IFZ off=" ++ show i) : showOps xs
showOps (TAILCALL:xs)    = "TAILCALL" : showOps xs
showOps (x:xs)           = show x : showOps xs

showBC :: Bytecode -> String
showBC = intercalate "; " . showOps

bcc :: MonadFD4 m => TTerm -> m Bytecode
bcc (V _ (Bound i)) = return [ACCESS, i]
bcc (V _ (Free x)) = failFD4 $ "Variable libre en bytecode "++x
bcc (V _ (Global x)) = failFD4 $ "Variable global en bytecode "++x
bcc (Const _ (CNat n)) = return [CONST, n]
bcc (Lam _ _ _ (Sc1 t)) = do t' <- bct t  -- bct agrega un RETURN al final
                             return $ [FUNCTION, length t'] ++ t'
bcc (App _ t1 t2) = do t1' <- bcc t1
                       t2' <- bcc t2
                       return $ t1'++ t2'++ [CALL]
bcc (Print _ s t)  = do t' <- bcc t
                        return $ t' ++ [PRINT] ++ string2bc s ++ [NULL] ++ [PRINTN]
bcc (BinaryOp _ Add t1 t2) = do t1' <- bcc t1
                                t2' <- bcc t2
                                return $ t1'++ t2' ++ [ADD]
bcc (BinaryOp _ Sub t1 t2) = do t1' <- bcc t1
                                t2' <- bcc t2
                                return $ t1'++ t2' ++ [SUB]
bcc (Fix _ _ _ _ _ (Sc2 t)) = do t' <- bct t
                                 return $ [FUNCTION, length t'] ++ t' ++ [FIX]
bcc (IfZ _ c t1 t2) = do c' <- bcc c
                         t1' <- bcc t1
                         t2' <- bcc t2
                         return $ c'++ [IFZ, length t1' + 2] ++ t1' ++ [JUMP, length t2'] ++ t2'
-- esto de length me genera dudas con el hecho de si puede ser interpretado como algo tipo CALL = 5
-- en teoria no pq siempre voy a encontrar antes un IFZ que una longitud
bcc (Let _ _ _ t1 (Sc1 t2)) = do t1' <- bcc t1
                                 t2' <- bcc t2
                                 return $ t1' ++ [SHIFT] ++ t2' ++ [DROP]

bct :: MonadFD4 m => TTerm -> m Bytecode
bct (App _ t1 t2) = do t1' <- bcc t1
                       t2' <- bcc t2
                       return $ t1'++ t2'++ [TAILCALL]
bct (IfZ _ c t1 t2) = do c' <- bcc c
                         t1' <- bct t1
                         t2' <- bct t2
                         return $ c' ++ [IFZ, length t1'] ++ t1' ++ t2'
bct (Let _ _ _ t1 (Sc1 t2)) = do t1' <- bcc t1
                                 t2' <- bct t2
                                 return $ t1' ++ [SHIFT] ++ t2'
bct t = do t' <- bcc t
           return $ t' ++ [RETURN]

-- ord/chr devuelven los codepoints unicode, o en otras palabras
-- la codificación UTF-32 del caracter.
string2bc :: String -> Bytecode
string2bc = map ord

bc2string :: Bytecode -> String
bc2string = map chr

global2free :: Module -> Module
global2free = map (\ (Decl i n ty t) -> Decl i n ty (rename t))
                where rename (V i (Global n)) =  V i (Free n)
                      rename t@(V _ _) = t
                      rename t@(Const _ _) = t
                      rename (Lam i n ty (Sc1 t)) = Lam i n ty (Sc1 (rename t))
                      rename (App i t1 t2) = App i (rename t1) (rename t2)
                      rename (Print i s t) = Print i s (rename t)
                      rename (BinaryOp i b t1 t2) = BinaryOp i b (rename t1) (rename t2)
                      rename (Fix i x xty f fty (Sc2 t)) = Fix i x xty f fty (Sc2 (rename t))
                      rename (IfZ i t1 t2 t3) = IfZ i (rename t1) (rename t2) (rename t3)
                      rename (Let i x xty t1 (Sc1 t2)) = Let i x xty (rename t1) (Sc1 (rename t2))

module2tterm :: MonadFD4 m => Module -> m TTerm
module2tterm [] = failFD4 "Modulo vacío"
module2tterm [Decl _ _ _ t] = return t
module2tterm (Decl p n ty t:m) = do t' <- module2tterm m
                                    return $ Let (p,ty) n ty t (close n t')
-- Creo que el tipo que se la pasa a info esta mal, pero no se usa. Se podría armar una función para
-- construir el tipo correcto, pero a esta altura ya se paso por el TypeChecker y los tipos más adelante
-- se descartan, así no vale la pena.

bytecompileModule :: MonadFD4 m => Module -> m Bytecode
bytecompileModule m = let m' = global2free m
                      in do t <- module2tterm m'
                            bc <- bcc t
                            return $ bc ++ [STOP]

-- | Toma un bytecode, lo codifica y lo escribe un archivo
bcWrite :: Bytecode -> FilePath -> IO ()
bcWrite bs filename = BS.writeFile filename (encode $ BC $ fromIntegral <$> bs)

---------------------------
-- * Ejecución de bytecode
---------------------------

-- | Lee de un archivo y lo decodifica a bytecode
bcRead :: FilePath -> IO Bytecode
bcRead filename = (map fromIntegral <$> un32) . decode <$> BS.readFile filename

runBC :: MonadFD4 m => Bytecode -> m ()
runBC bc = runBC' bc [] []

runBC' :: MonadFD4 m => Bytecode -> Environment -> Stack -> m ()
runBC' (CONST:n:c) e s = runBC' c e (I n:s) 
runBC' (ADD:c) e (I n:I m:s) = runBC' c e (I (semOp Add m n):s)
runBC' (SUB:c) e (I n:I m:s) = runBC' c e (I (semOp Sub m n):s)
runBC' (ACCESS:i:c) e s = runBC' c e (e!!i:s)
runBC' (CALL:c) e (v:Fun ef cf:s) = runBC' cf (v:ef) (RA e c:s)
runBC' (FUNCTION:len:c) e s = runBC' (drop len c) e (Fun e (take len c):s)
runBC' (RETURN:_) _ (v:RA e c:s) = runBC' c e (v:s)
runBC' (SHIFT:c) e (v:s) = runBC' c (v:e) s
runBC' (DROP:c) (v:e) s = runBC' c e s
runBC' (PRINTN:c) e st@(I n:s) = do printFD4 (show n)
                                    runBC' c e st
runBC' (PRINT:c) e s = let (bcstr, _:c') = span (/= NULL) c
                           str = bc2string bcstr 
                       in do printFD4NoNewLine str
                             runBC' c' e s
runBC' (FIX:c) e (Fun ef cf:s) = let efix = Fun efix cf:ef
                                 in runBC' c e (Fun efix cf:s)
runBC' (JUMP:n:c) e s = runBC' (drop n c) e s  
runBC' (IFZ:len:c) e (I b:s) = if b == 0
                                  then runBC' c e s
                                  else runBC' (drop len c) e s
runBC' (TAILCALL:_) _ (v:Fun ef cf:RA e c:s) = runBC' cf (v:ef) (RA e c:s)
runBC' (STOP:_) _ _ = return ()
runBC' c _ _ = do printFD4 (showBC c)
                  failFD4 "Bytecode mal formado"