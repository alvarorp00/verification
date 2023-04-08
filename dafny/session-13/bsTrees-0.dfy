/*

Binary Search Trees (BST)
Copyright: Specified and verified by Ricardo Peña, February 2019

*/

// BSTs are binary trees having unique keys and sorted inorder traversal
datatype BST = Empty  |  Node (left: BST, key: int, right: BST)

// This is the BST invariant
predicate isBST (t: BST)
{
   match t
      case Empty       => true
      case Node(l,x,r) => promising(l,x,r) && isBST(l) && isBST(r)
}				

// This is the BST property at the root level
predicate promising(l:BST, x:int, r:BST) 
{
   (forall z :: z in tset(l) ==> z < x) && 
   (forall z :: z in tset(r) ==> x < z)
}	

function tset(t:BST): set<int>
{
   match t
      case Empty       => {}		
      case Node(l,x,r) => tset(l)+{x}+tset(r)	
}				

function inorder(t: BST): seq<int>
{
   match t
      case Empty       => []
      case Node(l,x,r) => inorder(l) + [x] + inorder(r)
}			

// It searchs whether an element is present in a BST
function method search(x:int, t:BST): (res:bool)
requires isBST(t)
ensures res == (x in tset(t))
{
   match t
      case Empty       => false
      case Node(l,y,r) => if x < y then search(x,l) else if x > y then search(x,r) else true
}

// It inserts an element in a BST 
function method insert(x:int, t:BST): (res:BST)
requires isBST(t)
ensures  isBST(res)
ensures  tset(res) == tset(t) + {x}
{
   match t
      case Empty       => Node(Empty,x,Empty)
      case Node(l,y,r) => if x < y then Node(insert(x,l),y,r) else if x > y then Node(l,y,insert(x,r)) else t
}

// It deletes an element from a BST 
function method delete(x:int, t:BST): (res:BST)
requires isBST(t)
ensures  isBST(res)
ensures  tset(res) == tset(t) - {x}
{
   match t
      case Empty       => Empty
      case Node(l,y,r) =>
         if x < y then
            Node(delete(x,l),y,r)
         else if x > y then
            Node(l,y,delete(x,r))
         else
            if l == Empty then
               r
            else if r == Empty then
               l
            else
               var (v,l') := deleteMin(r);
               Node(l,v,l')
}

// It deletes the minimum element of a non empty BST
function method deleteMin (t: BST): (res: (int, BST))
requires isBST(t) && t != Empty
ensures res.0 in tset(t) 
ensures forall x | x in tset(t)-{res.0} :: res.0 < x
ensures isBST(res.1) 
ensures tset(res.1) == tset(t) - {res.0}
{
   match t
      case Node(l,x,r) =>
         match l
            case Empty       =>  (x,r)
            case Node(_,_,_) =>  var (y,l') := deleteMin(l);
                                 assert forall z | z in tset(l') :: y < z;
                                 assert forall z | z in tset(r) :: z > y;
                                 assert forall z | z in tset(l') + {y} + tset(r) :: z in tset(t);
                                 assert y < x;
                                 (y,Node(l',x,r))
}


predicate sorted(s: seq<int>)
{
    forall i, j | 0 <= i < j < |s| :: s[i] < s[j]
}

lemma sortedInorder(t: BST)
requires isBST(t)
ensures  sorted(inorder(t))
{
  match t 
     case Empty       =>
     case Node(l,x,r) => 
            inorderPreserveSet(l);
            assert forall z | z in inorder(l) :: z in tset(l);
            assert forall z | z in inorder(l) :: z < x;
            inorderPreserveSet(r);
            assert forall z | z in inorder(r) :: z > x;
            assert inorder(t)[|inorder(l)|]==x;
            assert forall j | 0<= j < |inorder(l)| :: inorder(t)[j] in tset(l);
            assert forall j | |inorder(l)| < j < |inorder(t)| :: inorder(t)[j] in tset(r);
}

lemma inorderPreserveSet (t:BST)
ensures forall z | z in inorder(t) :: z in tset(t)
{}


/*
     Exercises on the fly
*/


// 1. Program a function mirror which gets the symmetric image of a tree along
//    a vertical axis passing through the root and prove the postcondition shown

function mirror(t:BST):(res:BST)
ensures tset(res)==tset(t)
{
   match t
      case Empty       => Empty
      case Node(l,x,r) => Node(mirror(r),x,mirror(l))
}

// 2. Program the recursive traversals preorder and postorder of a binary tree

function preorder(t:BST):(res:seq<int>)
requires isBST(t)
{
   match t
      case Empty       => []
      case Node(l,x,r) => [x] + preorder(l) + preorder(r)
}

function postorder(t:BST):(res:seq<int>)
requires isBST(t)
{
   match t
      case Empty       => []
      case Node(l,x,r) => postorder(l) + postorder(r) + [x]
}

// 3. Relate with examples the functions mirror, inorder, preorder, postorder and 
//    the reverse of a sequence
