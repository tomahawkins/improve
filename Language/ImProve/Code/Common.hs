module Language.ImProve.Code.Common
  ( indent
  ) where

indent :: String -> String
indent = unlines . map ("\t" ++) . lines

