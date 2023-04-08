datatype List<T> = Nil | Cons(head:T, tail:List<T>)

predicate sorted(l:List<int>)
{
    match l 
       case Nil         => true
       case Cons(x, xs) => 
            match xs 
               case Nil         => true
               case Cons(y, ys) => x <= y && sorted(xs)
}

function elems<T> (l:List<T>) : multiset<T>
{
    match l
       case Nil         => multiset{}
       case Cons(x, xs) => multiset{x} + elems(xs)
}

method mergesort(l:List<int>) returns (res:List<int>)
//ensures sorted(res) 
//ensures elems(l) == elems(res)
//decreases length(l)
{
  if length(l) < 2 
       { 
         //assert sorted(l);
         //sortedSmallList(l);
         res := l;}
  else {
         //splitLengths(l);
         var (left, right) := split(l);
         var resl := mergesort(left);
         var resr := mergesort(right);
         res := merge(resl,resr);
         //assert sorted(res);
    }
}

function method length<T> (l:List<T>) : nat
{
    match l
       case Nil         => 0
       case Cons(_, xs) => 1 + length(xs)
}

function method split<T> (l:List<T>): (res: (List<T>, List<T>))
ensures elems(l) == elems(res.0) + elems(res.1)
ensures length(l) >= 2 ==>
       (length(res.0) < length(l) && length(res.1) < length(l))
ensures length(l) < 2 ==>
       (res.0 == l && res.1 == Nil)
{
   match l
      case Nil => (Nil,Nil)
      case Cons(x,Nil) => (Cons(x,Nil),Nil)
      case Cons(x,Cons(y,ys)) =>
         var (l1,l2) := split(ys);
         (Cons(x,l1),Cons(y,l2))
}

function method merge(l1:List<int>, l2:List<int>) : (res:List<int>)
requires sorted(l1) && sorted(l2)
ensures sorted (res)
ensures elems(res) == elems(l1) + elems(l2)
{
   match l1
      case Nil => l2
      case Cons(x,xs) =>
         match l2
            case Nil => l1
            case Cons(y,ys) =>
               if y < x then
                  Cons(y, merge(l1, ys))
               else
                  Cons(x, merge(xs, l2))
}


lemma splitLengths(l:List<int>)
requires length(l) >= 2 
ensures length(split(l).0) < length(l) && 
        length(split(l).1) < length(l)



lemma sortedSmallList (l:List<int>)
requires length(l) < 2
ensures  sorted(l)



function partition (l:List<int>, x:int)  : (res: (List<int>,List<int>))
ensures forall z | z in elems(res.0) :: z <= x
ensures forall z | z in elems(res.1) :: z >= x
ensures elems(l) == elems(res.0) + elems(res.1)
ensures length(res.0) <= length(l)
ensures length(res.1) <= length(l)
{
   match l
      case Nil => (Nil,Nil)
      case Cons(y,ys) =>
         var (l1,l2) := partition(ys,x);
         if y < x then
            (Cons(y,l1),l2)
         else
            (l1,Cons(y,l2))
}


function quicksort (l:List<int>): (res:List<int>)
ensures sorted(res) 
ensures elems(l) == elems(res)
decreases length(l)
{
   match l
      case Nil        => Nil
      case Cons(x,xs) => var (l1,l2) := partition(xs,x);
                         var left    := quicksort(l1);
                         var right   := quicksort(l2);
                         sortedMinimum(x,right);
                         assert (sorted(Cons(x,right)));
                         sortedConcat(left,Cons(x,right));
                         concat(left,Cons(x,right))                         
}

function method concat(l1:List<int>,l2:List<int>): (res:List<int>)
ensures elems(res) == elems(l1) + elems(l2)
{
   match l1
      case Nil => l2
      case Cons(x,xs) => Cons(x,concat(xs,l2))
}

lemma sortedMinimum (x:int, l:List<int>)
requires sorted (l)
requires forall z | z in elems(l) :: x <= z
ensures sorted(Cons(x,l))
// TODO: prove this lemma --> next lecture


lemma sortedConcat (l1:List<int>, l2:List<int>)
requires sorted(l1) && sorted(l2) 
requires forall x,y | x in elems(l1) && y in elems(l2) :: x <= y
ensures sorted(concat(l1,l2))
// TODO: prove this lemma (not mandatory) --> next lecture

/*
   Exercises on the fly
*/

// 1. Modify and verify mergesort using function splitAt n/2 instead of split

// 2. Complete the verification of quicksort

