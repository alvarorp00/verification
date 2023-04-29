module Main where

import LHExercises
import Data.Maybe as Maybe

main :: IO()
main = do
    putStrLn "Exercise 9.3"
    (putStrLn . show) ("isJust okRemove: " ++ show (isJust LHExercises.okRemove))
    (putStrLn . show) ("isNothing badRemove: " ++ show (isNothing LHExercises.badRemove))
