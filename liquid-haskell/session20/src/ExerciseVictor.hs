-- Exercise 6: Read Chapter 9 of the LH book about lazy queues and do the exercises
-- 9.5 and 9.6


-- For exercises 5 and 6, you can use the following definitions:

module ExerciseVictor where

data SList a = SL { size :: Int, elems :: [a] }

{-@ size :: q:SList a -> {v:Nat | v = size q} @-}

{-@ measure realSize @-}
realSize      :: [a] -> Int
realSize []     = 0
realSize (_:xs) = 1 + realSize xs

{-@ data SList a = SL {
       size  :: Nat 
     , elems :: {v:[a] | realSize v = size}
     }
  @-}

{-@ type SListN a N = {v:SList a | size v = N} @-}


{-@ type NEList a = {v:SList a | size v > 0} @-}

{-@ type SListLE a N = {v:SList a | size v <= N} @-}

{-@ nil          :: SListN a 0  @-}
nil              = SL 0 []

{-@ cons         :: a -> xs:SList a -> SListN a {size xs + 1}   @-}
cons x (SL n xs) = SL (n+1) (x:xs)


{-@ tl           :: xs:NEList a -> SListN a {size xs - 1}  @-}
tl (SL n (_:xs)) = SL (n-1) xs

{-@ hd           :: xs:NEList a -> a @-}
hd (SL _ (x:_))  = x 

{-@ okList :: SListN String 1 @-}
okList = SL 1 ["a"]
okHd = hd okList -- accepted
--badHd = hd (tl okList) -- rejected

okQ = Q okList nil -- accepted, |front| > |back|
--badQ = Q nil okList -- rejected, |front| < |back|

data Queue a = Q  { front :: SList a
                  , back  :: SList a
                  }

{-@ data Queue a = Q {
       front :: SList a 
     , back  :: SListLE a (size front)
     }
  @-}
  
  {-@ type QueueN a N = {v:Queue a | size (front v) + size (back v) = N} @-}

{-@ example0Q :: QueueN _ 0 @-}
example0Q = Q nil nil  

{-@ example1Q :: QueueN _ 1 @-}
example1Q = Q (SL 1 [0]) nil

{-@ example2Q :: QueueN _ 2 @-}
example2Q = Q (1 `cons` (2 `cons` nil)) nil

{-@ makeq :: f:SList a -> b:SListLE a {size f + 1} -> QueueN a {size f + size b} @-}
makeq f b
  | size b <= size f = Q f b
  | otherwise = Q (rot f b nil) nil

{-@ rot :: f:SList a -> b:SListN a {size f + 1} -> acc:SList a -> {v:SList a | size v = size f + size b + size acc } / [size f] @-}
rot f b acc
  | size f == 0 = hd b `cons` acc
  | otherwise = hd f `cons` rot (tl f) (tl b) (hd b `cons` acc)
  
{-@ emp :: QueueN _ 0 @-}


