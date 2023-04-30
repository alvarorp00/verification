module Main where

import LHExercises
import Data.Maybe as Maybe
import Data.Typeable as Typeable
import Data.Tuple as Tuple

main :: IO()
main = do
    putStrLn "Exercise 9.3"
    -- Get element removed
    -- (putStrLn . show) ("isJust okRemove: " ++ show (isJust LHExercises.okRemove))
    -- if isJust LHExercises.okRemove
    --     then (putStrLn . show) ("fromJust okRemove: " ++ show (fst (fromJust LHExercises.okRemove)))
    -- else (putStrLn . show) ("isNothing okRemove: " ++ show (isNothing LHExercises.okRemove))
    -- (putStrLn . show) ("isNothing badRemove: " ++ show (isNothing LHExercises.badRemove))
