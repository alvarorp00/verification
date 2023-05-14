

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

lemma sortedHeadLE (l:List<int>)
requires l != Nil
requires sorted(l)
ensures forall e | e in elems(l) :: l.head <= e
{}

lemma sortedConcat (l1:List<int>, l2:List<int>)
requires sorted(l1) && sorted(l2) 
requires forall x,y | x in elems(l1) && y in elems(l2) :: x <= y
ensures sorted(concat(l1,l2))
{
   match l1
      case Nil          => {}
      case Cons(head1,tail1)   =>
         match l2
            case Nil          => {}
            case Cons(head2,tail2)   =>
               {
                  assert l2.head in elems(l2);
                  assert forall e | e in elems(l1) :: e <= head2;
                  sortedHeadLE(l2);
                  assert forall e | e in elems(l2) :: head2 <= e;
                  assert forall e | e in elems(tail1) :: e in elems(l1);
               }
}

// 2. Prove the following lemma:

// reverse(l) == concat(reverse(xs),Cons(x,Nil))

lemma reverseHeadConcat<T> (head:T, tail:List<T>)
ensures reverse(concat(tail, Cons(head, Nil))) == Cons(head, reverse(tail))
{}

lemma reverseIdemp<T> (l:List<T>)
ensures reverse(reverse(l)) == l
{
   match l
      case Nil             => {}
      case Cons(head,tail) =>
         {
            calc == {
               reverse(reverse(l));
               reverse(concat(reverse(tail), Cons(head,Nil)));
               ==
               {reverseHeadConcat(head, reverse(tail)); }
               l;
            }
         }
}


// 3. Prove the following lemma:  # LEMMA TO BE PROVED :: 3  <------

// reverse(l) == concat(reverse(xs),Cons(x,Nil))

lemma dropReverse<T> (l1:List<T>, l2:List<T>, n:nat)
requires length(l1) >= n
ensures concat(drop(n, l1), l2) == drop(n, concat(l1,l2))
{}

lemma takeReverse<T> (n: nat, l:List <T>)
requires length(l) >= n
ensures reverse(take(n,l)) == drop(length(l)-n,reverse(l))
{
   match l
      case Nil                => {}
      case Cons(head, tail)   =>
         if n == 0
            {}
         else
            {
               calc == {
                  reverse(take(n,Cons(head, tail)));
                  reverse(Cons(head, take(n-1, tail)));
                  concat(reverse(take(n-1, tail)), Cons(head, Nil));
                  { takeReverse(n-1, tail); }
                  concat(drop(length(tail)-(n-1), reverse(tail)), Cons(head, Nil));
                  { dropReverse(reverse(tail), Cons(head, Nil), length(tail)-(n-1)); }
                  drop(length(l)-n, reverse(l));
            }
         }
}

// 4. Program a function mirror which gets the symmetric image of a tree along
//    a vertical axis passing through the root, and prove the following lemma:

function mirror<T>(t:Tree<T>):(res:Tree<T>)
ensures tset(res)==tset(t)
{
   match t
      case Empty        => Tree.Empty
      case Node(l,x,r)  => Tree.Node(mirror(r), x, mirror(l))
}

lemma mirrorLemma<T> (t:Tree<T>)
requires t != Tree.Empty
ensures mirror(t) == Tree.Node(mirror(t.right), t.key, mirror(t.left))
{}

lemma inorderLemma<T> (t:Tree<T>)
requires t != Tree.Empty
ensures inorder(t) == inorder(t.left) + [t.key] + inorder(t.right)
{}

lemma revLemma<T> (s:seq<T>, x:T)
ensures rev([x] + s) == rev(s) + [x]
{}

lemma revLemmaSeq<T> (s1:seq<T>, s2:seq<T>, x:T)
ensures rev([x] + (s1 + s2)) == rev(s1 + s2) + [x]
{}

lemma revEmpty<T> (s:seq<T>)
ensures [] + rev(s) == rev(s)
{}

lemma revEmpty21<T> (s:seq<T>)
ensures s == s + []
{}

lemma revEmpty22<T> (s:seq<T>)
ensures s == [] + s
{}

lemma revLemmaComm1<T> (s1:seq<T>, s2:seq<T>, s3:seq<T>)
ensures s1 + (s2 + s3) == (s1 + s2) + s3
{}

lemma revLemmaComm2<T> (s1:seq<T>, s2:seq<T>, s3:seq<T>)
ensures s1 + (s2 + s3) == s1 + s2 + s3
{}

lemma revLemma2<T> (s1:seq<T>, s2:seq<T>)
ensures rev(s1) + rev(s2) == rev(s2 + s1)
{
   if |s1| == 0 {
      revEmpty21(s2);
      assert rev(s1) + rev(s2) == rev(s2 + s1);
   } else {
      if |s2| == 0 {
         revEmpty22(s1);
      } else {
         calc == {
            rev(s1) + rev(s2);
            { assert rev(s2) == rev([s2[0]] + s2[1..]); }
            { revLemma(s2[1..], s2[0]); }
            rev(s1) + rev(s2[1..]) + [s2[0]];
            { revLemma2(s1, s2[1..]); }
            { assert rev(s1) + rev(s2[1..]) == rev(s2[1..] + s1); }
            rev(s2[1..] + s1) + [s2[0]];
            { revLemmaSeq(s2[1..], s1, s2[0]); }
            rev([s2[0]] + (s2[1..] + s1));
            { revLemmaComm2([s2[0]], s2[1..], s1); }
            rev([s2[0]] + s2[1..] + s1);
            { assert [s2[0]] + s2[1..] == s2; }
            rev(s2 + s1);
         }
      }
   }
}

lemma reverseMirror<T> (t: Tree<T>)
ensures inorder(mirror(t)) == rev(inorder(t))
{
   match t
      case Empty             => {}
      case Node(l,x,r)  =>
         {
            calc == {
               inorder(mirror(t));
               { mirrorLemma(t); }
               inorder(Tree.Node(mirror(r), x, mirror(l)));
               { inorderLemma(Tree.Node(mirror(r), x, mirror(l))); }
               inorder(mirror(r)) + [x] + inorder(mirror(l));
               { reverseMirror(l); }
               { reverseMirror(r); }
               rev(inorder(r)) + [x] + rev(inorder(l));
               { revLemma(inorder(r), x); }
               rev([x] + inorder(r)) + rev(inorder(l));
               { revLemma2(([x] + inorder(r)), inorder(l)); }
               rev(inorder(l) + ([x] + inorder(r)));
               { revLemmaComm2(inorder(l), [x], inorder(r)); }
               rev(inorder(l) + [x] + inorder(r));
            }
         }
}

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