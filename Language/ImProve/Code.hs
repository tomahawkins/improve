module Language.ImProve.Code
  ( Target (..)
  , code
  ) where

import Language.ImProve.Code.Ada
import Language.ImProve.Code.C
import Language.ImProve.Code.Modelica
import Language.ImProve.Code.Simulink
import Language.ImProve.Core

-- | Code generation targets.
data Target
  = Ada
  | C
  | Modelica
  | Simulink
  deriving Eq

-- | Generate target code.
code :: Target -> Name -> Statement -> IO ()
code target name stmt = f name stmt
  where
  f = case target of
    Ada      -> codeAda
    C        -> codeC
    Modelica -> codeModelica
    Simulink -> codeSimulink

