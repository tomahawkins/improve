module Language.ImProve.Verify (verify) where

import Language.ImProve.Core

verify :: Statement -> IO (Maybe Bool)
verify _ = putStrLn "verification not implemented yet" >> return Nothing

