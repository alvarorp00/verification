
-- Exercise 1:  Define a Skew heap in Liquid Haskell and implement
-- and verify its operation join, joining two skew heaps 
-- into one (see the dafny file to inspire you)


-- Exercise 2: Specify and define in Liquid Haskell a quicksort algorithm ensuring
-- an ordered output list and having the same set of elements as the input list


-- Exercise 3: Complete the exercise 7.10 of the LH book about the function
   matFromList      :: [[a]] -> Maybe (Matrix a)

-- Exercise 4: Complete the exercise 7.12 of the LH book about the function
   {-@ transpose :: m:Matrix a -> MatrixN a (mCol m) (mRow m) @-}


-- Exercise 5: Read Chapter 9 of the LH book about lazy queues and do the exercises <-- MINE # TODO # ASSIGNMENT
-- 9.3 and 9.4


-- Exercise 6: Read Chapter 9 of the LH book about lazy queues and do the exercises
-- 9.5 and 9.6


-- For exercises 5 and 6, you can use the following definitions:

data SList a = SL { size :: Int, elems :: [a] }

{-@ size :: q:SList a -> {v:Nat | v = size q} @-}

{-@ measure realSize @-}
realSize      :: [a] -> Int
realSize []     = 0
realSize (_:xs) = 1 + realSize xs
\end{code}

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

data Queue a = Q  { front :: SList a
                  , back  :: SList a
                  }

{-@ data Queue a = Q {
       front :: SList a 
     , back  :: SListLE a (size front)
     }
  @-}
