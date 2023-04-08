-- Import liquid haskell
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
module Main where

import LiquidHaskell
import Data.Set

import Demo.Lib
import Session18.Lists

main :: IO ()
main = putStrLn "Hello, Haskell!"