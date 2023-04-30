
module LHExercises where

import Data.Maybe as Maybe
import Data.Tuple as Tuple

-- import Prelude

-- Exercise 1:  Define a Skew heap in Liquid Haskell and implement
-- and verify its operation join, joining two skew heaps 
-- into one (see the dafny file to inspire you)


-- Exercise 2: Specify and define in Liquid Haskell a quicksort algorithm ensuring
-- an ordered output list and having the same set of elements as the input list


-- Exercise 3: Complete the exercise 7.10 of the LH book about the function
-- matFromList      :: [[a]] -> Maybe (Matrix a)

-- Exercise 4: Complete the exercise 7.12 of the LH book about the function
-- {-@ transpose :: m:Matrix a -> MatrixN a (mCol m) (mRow m) @-}


-- Exercise 5: Read Chapter 9 of the LH book about lazy queues and do the exercises <-- MINE  # ASSIGNMENT
-- 9.3 and 9.4


-- Exercise 6: Read Chapter 9 of the LH book about lazy queues and do the exercises
-- 9.5 and 9.6


-- For exercises 5 and 6, you can use the following definitions:

data SList a = SL { size :: Int, elems :: [a] }

-- {-@ size :: q:SList a -> {v:Nat | v = size q} @-}

{-@ measure realSize @-}
realSize      :: [a] -> Int
realSize []     = 0
realSize (_:xs) = 1 + realSize xs
-- \end{code}

{-@ data SList a = SL {
       size  :: Nat 
     , elems :: {v:[a] | realSize v = size}
     }
@-}

{-@ type SListN a N = {v:SList a | size v = N} @-}


{-@ type NEList a = {v:SList a | size v > 0} @-}

{-@ type SListLE a N = {v:SList a | size v <= N} @-}

{-@ nil          :: SListN a 0  @-}
nil              :: SList a
nil              = SL 0 []

{-@ cons         :: a -> xs:SList a -> SListN a {size xs + 1}   @-}
cons             :: a -> SList a -> SList a
cons x (SL n xs) = SL (n+1) (x:xs)


{-@ tl           :: xs:NEList a -> SListN a {size xs - 1}  @-}
tl              :: SList a -> SList a
tl (SL n (_:xs)) = SL (n-1) xs

{-@ hd           :: xs:NEList a -> a @-}
hd (SL _ (x:_))  = x 

data Queue a = Q  { front :: SList a
                  , back  :: SList a
                  }

{-@ data Queue a = Q {
      front :: SList a 
   ,  back  :: SListLE a (size front)
   }
@-}

-- Exercise 9.3

-- Write a measure to describe the queue size
{-@ measure qsize @-}
qsize :: Queue a -> Int
qsize (Q f b) = size f + size b

-- Use it to complete the definition of QueueN

-- | Queues of size `N`
{-@ type QueueN a N = {v:Queue a | qsize v == N } @-}

-- ############
-- start Victor
{-@ makeq :: f:SList a -> b:SListLE a {size f + 1} -> QueueN a {size f + size b} @-}
makeq f b
  | size b <= size f = Q f b
  | otherwise = Q (rot f b nil) nil

{-@ rot :: f:SList a -> b:SListN a {size f + 1} -> acc:SList a -> {v:SList a | size v = size f + size b + size acc } / [size f] @-}
rot f b acc
  | size f == 0 = hd b `cons` acc
  | otherwise = hd f `cons` rot (tl f) (tl b) (hd b `cons` acc)
-- end Victor
-- ##########

-- Safe remove
{-@ removeMaybe :: qi:QueueN a {qsize qi} -> mq: Maybe (a, QueueN a {qsize qi - 1}) @-}
removeMaybe qi@(Q f b)
  | size f == 0 && size b == 0 = Nothing
  | size f == 0 = Just (hd (rot b nil nil), Q (rot b nil nil) nil)
  | otherwise = Just (hd f, makeq (tl f) b)

{-@ remove :: {qi:QueueN a {qsize qi} | qsize qi > 0} -> (a, QueueN a {qsize qi - 1}) @-}
remove (Q f b) = (hd f, makeq (tl f) b)

-- {-@ okRemove :: Maybe (_, QueueN _ 1) @-}
okRemove = remove example2Q -- accept

-- badRemove = remove example0Q -- reject

{-@ emp :: QueueN _ 0 @-} 
emp = Q nil nil

{-@ example2Q :: QueueN _ 2 @-}
example2Q = Q (1 `cons` (2 `cons` nil)) nil

{-@ example0Q :: QueueN _ 0 @-}
example0Q = Q nil nil

-- Exercise 9.4
--

-- TODO
-- | Insert an element into a queue
-- {-@ insert :: x:a -> qi:Queue a -> QueueN a {qsize qi + 1} @-}
-- insert e (Q f b) = makeq f (e `cons` b)

-- {-@ replicate :: n:Nat -> a -> QueueN a n @-}
-- replicate 0 _ = emp
-- replicate n x = insert x (replicate (n-1) x)

-- {-@ okReplicate :: QueueN _ 3 @-}
-- okReplicate = replicate 3 "Yeah!"
-- -- accept

-- {-@ badReplicate :: QueueN _ 3 @-}
-- badReplicate = replicate 1 "No!"
-- -- reject