// You are given the following definitions seen at the classroom:

datatype List<T> = Nil | Cons(head:T, tail:List<T>)


function method length<T> (l:List<T>) : nat
{
    match l
       case Nil         => 0
       case Cons(_, xs) => 1 + length(xs)
}
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

function min(x:nat, y:nat): (res:nat)
{
    if x <=y then x else y
}

function method take<T> (n: nat, l:List<T>): (res:List<T>)
ensures length(res) == min (n, length(l))
{
    match l
        case Nil         => Nil
        case Cons(y, ys) => if n == 0 then Nil
                            else Cons(y, take(n-1, ys))
}

function method drop<T> (n: nat, l:List<T>): (res:List<T>)
ensures length(res) == if length(l) < n then 0 else length(l) - n
{
    match l
        case Nil         => Nil
        case Cons(y, ys) => if n == 0 
                            then l
                            else drop(n-1, ys)
}

function method splitAt<T> (n: nat, l:List<T>): (res:(List<T>, List<T>))
ensures length(res.0) == min (n, length(l))
ensures length(res.1) == if length(l) < n then 0 else length(l) - n
ensures elems(l) == elems(res.0) + elems(res.1)
{
    match l 
        case Nil         => (Nil, Nil)
        case Cons(y, ys) => if n == 0 then (Nil, l)
                            else var (ys1, ys2) := splitAt(n-1,ys);
                                 (Cons(y,ys1), ys2)
}

function method sum(l:List<int>): (res:int)
{
    match l 
        case Nil         => 0
        case Cons(y, ys) => y + sum(ys)
}

function method reverse <T> (l:List<T>): (res:List<T>)
ensures elems(res)==elems(l)
ensures length(res) == length(l)
{
    match l
       case Nil        => Nil
       case Cons(x,xs) => concat(reverse(xs),Cons(x,Nil))
}

function method concat <T> (l1:List<T>,l2:List<T>): (res:List<T>)
ensures elems(res)==elems(l1)+elems(l2)
ensures length(res) == length(l1) + length(l2)
{
    match l1
       case Nil        => l2
       case Cons(x,xs) => Cons(x,concat(xs,l2))
}

// 3. Prove the following lemma:  # LEMMA TO BE PROVED :: 3  <------

function last<T> (l:List<T>): List<T>
requires l != Nil
ensures drop(length(l)-1,l) == last(l)
ensures last(l).tail == Nil
{
   match l
      case Cons(x,Nil) => l
      case Cons(x,xs)  => last(xs)
}

function listToSeq<T> (l:List<T>): seq<T>
requires l != Nil
ensures length(l) == |listToSeq(l)|
ensures forall i: int | 0 <= i < |listToSeq(l)| :: listToSeq(l)[i] == drop(i,l).head
ensures forall i: int | 0 <= i < |listToSeq(l)| :: listToSeq(l)[i] == splitAt(i,l).1.head
ensures forall i: int | 0 <= i < |listToSeq(l)| :: listToSeq(l)[i] == last(take(i+1,l)).head
{
   match l
      case Cons(x,Nil) => [x]
      case Cons(x,xs)  => [x] + listToSeq(xs)
}

lemma concatReverseLast<T> (l1:List<T>, l2:List<T>)
requires l1 != Nil && l2 != Nil
ensures last(concat(l1,l2)) == last(l2)
{}

lemma lastTail<T> (l:List<T>)
requires l != Nil
ensures l.head == last(reverse(l)).head
{
   match l
      case Cons(x,Nil) => 
         assert l.head == last(reverse(l)).head;
      case Cons(x,xs)  =>
         lastTail(xs);
         var l1 := concat(reverse(xs),Cons(x,Nil));
         assert reverse(l) == l1;
         concatReverseLast(reverse(xs),Cons(x,Nil));
         assert last(l1) == last(Cons(x,Nil));
}

lemma lastConcat<T> (l1: List<T>, x:T)
requires l1 != Nil
ensures last(concat(l1,Cons(x,Nil))) == Cons(x,Nil)
{}

// lemma dropKeepLast<T> (l:List<T>)
// requires l != Nil
// ensures drop(length(l)-1,l) == Cons(last(l).head,Nil)
// {}

// lemma lastDrop<T> (n:nat, l:List<T>)
// requires l != Nil
// requires length(l) > n >= 1
// ensures last(drop(length(l)-n,l)) == last(l)
// {
//    match l
//       case Cons(x,Nil) =>
//          assert last(drop(length(l)-n,l)) == last(l);
//       case Cons(x,xs)  =>
//          if (n==1) {
//             dropKeepLast(l);
//          } else {
//             assert drop(length(l)-n,Cons(x,xs)) == drop(length(xs)-n,xs);
//          }
// }

// lemma dropConcatLength<T> (l1:List<T>,l2:List<T>)
// requires l1 != Nil && l2 != Nil
// ensures drop(length(l1),concat(l1,l2)) == l2
// {}

// lemma lastReverse<T> (l:List<T>)
// requires l != Nil
// ensures reverse(l) == concat(reverse(l.tail), Cons(l.head,Nil))
// {}

// lemma dropReverse1<T> (l:List<T>)
// requires l != Nil
// ensures drop(1,reverse(l)) == reverse(take(length(l)-1,l))
// {
//    match l
//       case Cons(x,Nil) =>
//          assert drop(1,reverse(l)) == reverse(take(length(l)-1,l));
//       case Cons(x,xs)  =>
//          dropReverse1(xs);
// }

// lemma dropReverse11<T> (l:List<T>)
// requires l != Nil
// requires length(l) >= 2
// ensures drop(1,reverse(l)) == concat(drop(1,reverse(l.tail)),Cons(l.head,Nil))
// {
//    match l
//       case Cons(x,xs)  =>
//          if (length(xs) == 1) {
//             assert drop(1,xs) == Nil;
//          }
// }


// lemma dropReverse2<T> (l:List<T>)
// requires l != Nil
// ensures drop(length(l)-1,reverse(l)) == Cons(l.head,Nil)
// {
//    match l
//       case Cons(x,Nil) =>
//          assert drop(length(l)-1,reverse(l)) == Cons(l.head,Nil);
//       case Cons(x,xs)  =>
//          dropReverse2(xs);
//          dropConcatLength(reverse(xs),Cons(x,Nil));
// }

lemma concatReverse<T> (x:T, l:List<T>)
requires l != Nil
ensures reverse(Cons(x,l)) == concat(reverse(l),Cons(x,Nil))
ensures last(concat(reverse(l),Cons(x,Nil))) == Cons(x,Nil)
{
   lastConcat(reverse(l),x);
   assert last(concat(reverse(l),Cons(x,Nil))) == Cons(x,Nil);
}

lemma takeSplit<T> (n:nat, l:List<T>)
requires l != Nil
requires length(l) > n && n >= 1
ensures take(n,l) == splitAt(n,l).0
{}

lemma takeSplitReverse<T> (n:nat, l:List<T>)
requires l != Nil
requires length(l) > n && n >= 1
ensures reverse(take(n,l)) == reverse(splitAt(n,l).0)
{}

lemma dropSplit<T> (n:nat, l:List<T>)
requires l != Nil
requires length(l) > n && n >= 1
ensures drop(n,l) == splitAt(n,l).1
{}

lemma dropSplitReverse<T> (n:nat, l:List<T>)
requires l != Nil
requires length(l) > n && n >= 1
ensures drop(length(l)-n,reverse(l)) == splitAt(length(l)-n,reverse(l)).1
{
    dropSplit(length(l)-n,reverse(l));
}

lemma splitLast<T> (l:List<T>)
requires l != Nil
ensures splitAt(length(l)-1,l).1 == Cons(last(l).head,Nil)
{}

lemma splitLastReverse<T> (l:List<T>)
requires l != Nil
ensures splitAt(length(l)-1,reverse(l)).1 == splitAt(1,l).0
{
    lastTail(l);
    splitLast(reverse(l));
}

// lemma splitLemma11<T> (n:nat, l:List<T>)
// requires l != Nil
// requires length(l) > n && n >= 1
// ensures reverse(splitAt(n,l).0) == concat(reverse(splitAt(n-1,l.tail).0), Cons(l.head,Nil))
// {}

// lemma splitLemma12<T> (n:nat, l:List<T>)
// requires l != Nil
// requires length(l) > n && n >= 1
// ensures reverse(Cons(l.head,splitAt(n-1,l.tail).0)) == concat(reverse(splitAt(n-1,l.tail).0), Cons(l.head,Nil))
// {}

// lemma splitLemma2<T> (n:nat, l:List<T>)
// requires l != Nil
// requires length(l) > n && n >= 1
// ensures splitAt(n,l).0 == Cons(l.head,splitAt(n-1,l.tail).0)
// {}

lemma splitReverse<T> (n:nat, l:List<T>)
requires l != Nil
requires length(l) > n && n >= 1
ensures reverse(splitAt(n,l).0) == splitAt(length(l)-n,reverse(l)).1
{
    match l
       case Cons(x,Nil) =>
          assert reverse(splitAt(n,l).0) == splitAt(length(l)-n,reverse(l)).1;
       case Cons(x,xs)  =>
          if (n==1) {
            //  dropSplitReverse(length(l)-n,reverse(l));
            //  takeSplitReverse(n,l);
                assert splitAt(n,l).0 == Cons(x,Nil);
                assert reverse(l) == concat(reverse(l.tail), Cons(l.head,Nil));
                splitLastReverse(l);
          } else {
               splitReverse(n-1,xs);

               assert reverse(splitAt(n-1,xs).0) == splitAt(length(l)-n,reverse(xs)).1;

               assert reverse(splitAt(n,l).0) == reverse(Cons(x,splitAt(n-1,xs).0));
               assert reverse(splitAt(n,l).0) == concat(reverse(splitAt(n-1,xs).0), Cons(x,Nil));
               assert reverse(splitAt(n,l).0) == concat(splitAt(length(l)-n,reverse(xs)).1, Cons(x,Nil));

               // assert splitAt(length(l)-n,reverse(l)).1 == reverse(Cons(x,splitAt(length(l)-n,reverse(xs)).1));
          }
}

// Disclaimer: is a bit dissapointing that after the work done
// I could not prove this lemma.
// The biggest threat was passing from the
//    splitAt(length(l)-n,reverse(l)).1 to the
//    reverse(Cons(l.head,splitAt(n-1,l.tail).0))
// which would've done the job, but I could not prove it.
// I tried to prove it by induction on the length of the list,
// but still had to face the problem of the splitAt.
//
// My initial approach was to prove it directly by terms of take
// and drop, but I faced the same problem in drop: I could not
// prove that we can take an element from the tail of the list
// when the amount to drop is lower than the length of the list,
// which is trivial as not every element will be dropped; and so I moved
// to splitAt, but went into the same problem.
//
// I think biggest problem is changing my mind from proving
// mathematical properties to proving properties of the code,
// which seems to not be so trivial.
//
// Lemmas commented above are auxiliary lemmas that I tried to use
// but they're not needed at any piece of the code, the uncommented
// ones are still in use although the proof is not complete.
//
// Comments are welcome.

lemma takeReverse<T> (n: nat, l:List <T>)
requires length(l) >= n
ensures reverse(take(n,l)) == drop(length(l)-n,reverse(l))
{
   match l
      case Nil =>
         assert reverse(take(n,l)) == drop(length(l)-n,reverse(l));  // Both sides are Nil
      case Cons(x,Nil) =>
         assert reverse(take(n,l)) == drop(length(l)-n,reverse(l));  // Both sides are Cons(x,Nil)
      case Cons(x,xs) =>
         if (n==0) {
            assert reverse(take(n,l)) == drop(length(l)-n,reverse(l));
         }
         else if (n==1) {
            lastTail(l);
         } else if (length(l) == n) {
            assert reverse(take(n,l)) == drop(length(l)-n,reverse(l)) == reverse(l);
         } else {
            assert length(l) > n >= 2;
            takeReverse(n-1,xs);
            assert reverse(take(n-1,xs)) == drop(length(l)-n,reverse(xs));  // Inductive step

            // assert take(n,l) == Cons(x,take(n-1,xs));
            // assert reverse(take(n,l)) == reverse(Cons(x,take(n-1,xs)));
            concatReverse(x,take(n-1,xs));
            // assert last(reverse(Cons(x,take(n-1,xs)))) == Cons(x,Nil);
            assert reverse(Cons(x,take(n-1,xs))) == concat(reverse(take(n-1,xs)),Cons(x,Nil));  // Key point

            assert reverse(take(n,l)) == concat(drop(length(l)-n,reverse(xs)),Cons(x,Nil));

            assert drop(length(l)-n,reverse(l)) == drop(length(l)-n,reverse(Cons(x,xs)));
            assert length(l) == length(xs)+1;

            // If I can prove splitReverse(n,l) then the lemma is proved

            // splitReverse(n,l);
            // assert concat(drop(length(l)-n,reverse(xs)),Cons(x,Nil)) == drop(length(l)-n,reverse(Cons(x,xs)));
            // assert reverse(take(n,l)) == drop(length(l)-n,reverse(l));
         }
}

lemma takeReverse2<T> (n: nat, l:List <T>)
requires length(l) >= n
ensures  reverse(take(n,l)) == drop(length(l)-n,reverse(l))
{
     match l
      case Nil        =>
      case Cons(x,xs) => if n == 0 {}
           else {             
                  calc == { 
                    reverse(take(n,Cons(x,xs)));
                    reverse(Cons(x, take(n-1,xs)));
                    concat(reverse(take(n-1,xs)),Cons(x,Nil));
                      { takeReverse2(n-1,xs); }
                    concat(drop(length(xs)-(n-1),reverse(xs)),Cons(x,Nil));
                      { concatDrop(length(xs)-(n-1), reverse(xs), Cons(x,Nil)); }
                    drop(length(xs)-(n-1),concat(reverse(xs),Cons(x,Nil)));
                    drop(length(xs)+1-n, reverse(Cons(x,xs)));
                  }     
           }
}

lemma concatDrop <T> (n: nat, l1:List <T>, l2:List <T>)
requires length(l1) >= n
ensures concat(drop(n,l1), l2) == drop(n, concat(l1,l2))
{}
