
//Exercise 2: 5 pts
// You are given the following definitions

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

predicate sortedDec(l:List<int>)
{
    match l 
       case Nil         => true
       case Cons(x, xs) => 
            match xs 
               case Nil         => true
               case Cons(y, ys) => x >= y && sortedDec(xs)
}

function elems<T> (l:List<T>) : multiset<T>
{
   match l
      case Nil         => multiset{}
      case Cons(x, xs) => multiset{x} + elems(xs)
}

// You must implement and verify function a reverse function satisfying 
// the specification below. The implementation should use an auxiliary function
// with an accumulator parameter, so that the time cost should be in O(n)

lemma sortedHeadTailOrderLemma (l:List<int>)
requires l != Nil
requires sorted(l)
ensures forall e | e in elems(l.tail) :: e >= l.head
{}

function reverse (l:List<int>) : (res:List<int>)
requires sorted(l)
ensures  sortedDec(res)
ensures  elems(res) == elems(l)
{
   match l
      case Nil          => Nil
      case Cons(x,xs)   =>
         sortedHeadTailOrderLemma(l);
         assert elems(reverseAccum(xs, Cons(x,Nil))) == elems(xs) + elems(Cons(x,Nil));
         reverseAccum(xs, Cons(x,Nil))
}

lemma sortedDecPrependLemma (x:int, l:List<int>)
requires sortedDec(l)
requires forall e | e in elems(l) :: x >= e
ensures sortedDec(Cons(x,l))
{
   if l == Nil {
      assert sortedDec(Cons(x,l));
   } else {
      assert l.head in elems(l);
      assert x >= l.head;
   }
}

function reverseAccum(l:List<int>, lAcc:List<int>) : (res:List<int>)
requires sorted(l)
requires sortedDec(lAcc)
requires forall e1, e2 | e1 in elems(l) && e2 in elems(lAcc) :: e1 >= e2;
ensures sortedDec(res)
ensures elems(res) == elems(l) + elems(lAcc)
{
   match l
      case Nil          => lAcc
      case Cons(x,xs)   =>
         sortedHeadTailOrderLemma(l);
         assert x in elems(l);
         // assert forall e | e in elems(lAcc) :: x >= e;
         sortedDecPrependLemma(x,lAcc);
         reverseAccum(xs,Cons(x,lAcc))
}