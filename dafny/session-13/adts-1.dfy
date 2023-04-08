

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

// BSTs are binary trees having unique keys and sorted inorder traversal
datatype Tree<T> = Empty  |  Node (left: Tree<T>, key: T, right: Tree<T>)

// This is the BST invariant
predicate isBST (t: Tree<int>)
{
   match t
      case Empty       => true
      case Node(l,x,r) => promising(l,x,r) && isBST(l) && isBST(r)
}				

// This is the BST property at the root level
predicate promising(l:Tree<int>, x:int, r:Tree<int>) 
{
   (forall z :: z in tset(l) ==> z < x) && 
   (forall z :: z in tset(r) ==> x < z)
}	

function tset<T> (t:Tree<T>): set<T>
{
   match t
      case Empty       => {}		
      case Node(l,x,r) => tset(l)+{x}+tset(r)	
}				

function inorder<T> (t: Tree<T>): seq<T>
{
   match t
      case Empty       => []
      case Node(l,x,r) => inorder(l) + [x] + inorder(r)
}			

function rev <T> (s:seq<T>): (res:seq<T>)
{
   if s==[] then []
            else rev(s[1..]) + [s[0]]
}


predicate sortedSeq (s: seq<int>)
{
    forall i, j | 0 <= i < j < |s| :: s[i] <= s[j]
}

// Skew Heaps are just binary trees holding the so-called heap property 
datatype Skew = Empty  |  Node (left: Skew, key: int, right: Skew)

// This is the Skew Heap invariant
predicate isSkew (t: Skew)
{
   match t
      case Empty       => true
      case Node(l,x,r) => isSkew(l) && isSkew(r) &&  heap(l, x, r) 
}				

// This is the heap property at the root level
predicate heap(l:Skew, x:int, r:Skew) 
{
   forall z | z in mset(l) + mset(r) :: x <= z
}		
			
// this is the mathematical model implemented by a Skew Heap
function mset(t:Skew): multiset<int>
{
   match t
      case Empty       => multiset{}		
      case Node(l,x,r) => mset(l) + multiset{x} + mset(r)	
}				

// *********************** Home Exercises March 2023 *********************************


// 1. Prove the following lemma:

lemma sortedConcat (l1:List<int>, l2:List<int>)
requires sorted(l1) && sorted(l2) 
requires forall x,y | x in elems(l1) && y in elems(l2) :: x <= y
ensures sorted(concat(l1,l2))

// 2. Prove the following lemma:

// lemma reverseConcat<T>(head:T, tail:List<T>)
// ensures reverse(concat(tail, Cons(head, Nil))) == Cons(head, reverse(tail))
// {}

// lemma reverseIdemp<T> (l:List<T>)
// ensures reverse(reverse(l)) == l {
//     if l.Cons? {
//         calc == {
//             reverse(reverse(l));
//             reverse(concat(reverse(l.tail), Cons(l.head, Nil)));
//             { reverseConcat(l.head, reverse(l.tail)); }
//             Cons(l.head, reverse(reverse(l.tail)));
//             { reverseIdemp(l.tail); }
//             Cons(l.head, l.tail);
//             l;
//         }
//     }
// }


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

lemma dropKeepLast<T> (l:List<T>)
requires l != Nil
ensures drop(length(l)-1,l) == Cons(last(l).head,Nil)
{}

lemma lastDrop<T> (n:nat, l:List<T>)
requires l != Nil
requires length(l) > n >= 1
ensures last(drop(length(l)-n,l)) == last(l)
{
   match l
      case Cons(x,Nil) =>
         assert last(drop(length(l)-n,l)) == last(l);
      case Cons(x,xs)  =>
         if (n==1) {
            dropKeepLast(l);
         } else {
            assert drop(length(l)-n,Cons(x,xs)) == drop(length(xs)-n,xs);
         }
}

lemma dropConcatLength<T> (l1:List<T>,l2:List<T>)
requires l1 != Nil && l2 != Nil
ensures drop(length(l1),concat(l1,l2)) == l2
{}

lemma lastReverse<T> (l:List<T>)
requires l != Nil
ensures reverse(l) == concat(reverse(l.tail), Cons(l.head,Nil))
{}

lemma dropReverse1<T> (l:List<T>)
requires l != Nil
ensures drop(1,reverse(l)) == reverse(take(length(l)-1,l))
{
   match l
      case Cons(x,Nil) =>
         assert drop(1,reverse(l)) == reverse(take(length(l)-1,l));
      case Cons(x,xs)  =>
         dropReverse1(xs);
}

lemma dropReverse11<T> (l:List<T>)
requires l != Nil
requires length(l) >= 2
ensures drop(1,reverse(l)) == concat(drop(1,reverse(l.tail)),Cons(l.head,Nil))
{
   match l
      case Cons(x,xs)  =>
         if (length(xs) == 1) {
            assert drop(1,xs) == Nil;
         }
}


lemma dropReverse2<T> (l:List<T>)
requires l != Nil
ensures drop(length(l)-1,reverse(l)) == Cons(l.head,Nil)
{
   match l
      case Cons(x,Nil) =>
         assert drop(length(l)-1,reverse(l)) == Cons(l.head,Nil);
      case Cons(x,xs)  =>
         dropReverse2(xs);
         dropConcatLength(reverse(xs),Cons(x,Nil));
}

lemma concatReverse<T> (x:T, l:List<T>)
requires l != Nil
ensures reverse(Cons(x,l)) == concat(reverse(l),Cons(x,Nil))
ensures last(concat(reverse(l),Cons(x,Nil))) == Cons(x,Nil)
{
   lastConcat(reverse(l),x);
   assert last(concat(reverse(l),Cons(x,Nil))) == Cons(x,Nil);
}

lemma dropStep<T> (n:nat, l:List<T>)
requires l != Nil
requires length(l) > n && n >= 1
ensures drop(length(l)-n,l) == drop(length(l.tail)-n,l.tail)
{}

lemma dropConcatReverse<T> (n:nat, l:List<T>)
requires l != Nil
requires length(l) > n && n >= 1
ensures drop(length(l)-n,reverse(l)) ==
         concat(drop(length(l)-n,reverse(l.tail)),Cons(l.head,Nil));
{
   match l
      case Cons(x,Nil) =>
         assert drop(length(l)-n,reverse(l)) ==
                concat(drop(length(l.tail)-n+1,reverse(l.tail)),Cons(l.head,Nil));
      case Cons(x,xs)  =>
         if (n==1) {
            concatReverse(x,xs);
         }
         else {
            dropConcatReverse(n-1,xs);
            assert drop(length(l)-n,reverse(xs)) == concat(drop(length(l)-n,reverse(xs.tail)),Cons(xs.head,Nil));
            
            // concatReverse(x,xs);
            // assert last(reverse(Cons(x,xs))) == Cons(x,Nil);
            // assert last(drop(length(xs)-n+1,reverse(Cons(x,xs)))) == Cons(x,Nil);
            
            assert drop(length(l)-n,reverse(l)) == drop(length(xs)-n+1,reverse(Cons(x,xs)));
            assert length(xs) - n + 1 < length(l);

            dropStep(n,reverse(l));
            // assert drop(length(xs)-n+1,reverse(Cons(x,xs))) == concat(drop(length(xs)-n+1,reverse(xs)),Cons(x,Nil));
            
         }
}

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

            // dropConcatReverse(n,l);
            // assert concat(drop(length(l)-n,reverse(xs)),Cons(x,Nil)) == drop(length(l)-n,reverse(Cons(x,xs)));
            // assert reverse(take(n,l)) == drop(length(l)-n,reverse(l));
         }
}

// 4. Program a function mirror which gets the symmetric image of a tree along
//    a vertical axis passing through the root, and prove the following lemma:

function mirror<T>(t:Tree<T>):(res:Tree<T>)
ensures tset(res)==tset(t)

lemma reverseMirror<T> (t: Tree<T>)
ensures inorder(mirror(t)) == rev(inorder(t))

// 5. Program the function mirror of exercise 4.
//    Program the recursive traversals preorder and postorder of a binary tree, 
//    and prove the following lemma:

function preorder<T> (t: Tree<T>): seq<T>

function postorder<T> (t: Tree<T>): seq<T>

lemma reversePreorder<T> (t: Tree<T>)
ensures rev(preorder(t)) == postorder(mirror(t))

// 6. You are given the function flatten and then should program the function merge
//     which merges two sorted sequences and veryfy both merge and flatten

function merge(s1: seq<int>, s2: seq<int>): (res:seq<int>)


function flatten(t:Skew):(res:seq<int>)
requires isSkew(t)
ensures multiset(res) == mset(t)
ensures sortedSeq(res)
{
   match t
     case Empty       =>   []
     case Node(l,x,r) =>   var left := flatten(l);
                           var right := flatten(r);
                           [x] + merge(left,right)
}

