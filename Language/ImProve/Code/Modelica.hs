module Language.ImProve.Code.Modelica (codeModelica) where

import Language.ImProve.Core

-- Modelica generation.
codeModelica :: Name -> Statement -> IO ()
codeModelica name _ = writeFile (name ++ ".mo") "// XXX"

