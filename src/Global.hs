{-|
Module      : Global
Description : Define el estado global del compilador
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}
module Global where

import Lang

data GlEnv = GlEnv {
  inter :: Bool,        --  ^ True, si estamos en modo interactivo.
                        -- Este parámetro puede cambiar durante la ejecución:
                        -- Es falso mientras se cargan archivos, pero luego puede ser verdadero.
  lfile :: String,      -- ^ Último archivo cargado.
  cantDecl :: Int,      -- ^ Cantidad de declaraciones desde la última carga
  glb :: [Decl TTerm],  -- ^ Entorno con declaraciones globales
  glbT :: [(Name, Ty)]  -- ^ Entorno con pares de sinonimos de tipos
}

-- ^ Entorno de tipado de declaraciones globales
tyEnv :: GlEnv ->  [(Name,Ty)]
tyEnv g = map (\(Decl _ n t b) -> (n, t))  (glb g) -- ahora tengo el tipo

{-
 Tipo para representar las banderas disponibles en línea de comando.
-}
data Mode =
    Interactive
  | Typecheck
  | Eval
  | CEK
  | Bytecompile
  | RunVM
  | CC
  
data Conf = Conf {
    opt :: Bool,          --  ^ True, si estan habilitadas las optimizaciones.
    modo :: Mode
}

-- | Valor del estado inicial
initialEnv :: GlEnv
initialEnv = GlEnv False "" 0 [] []
