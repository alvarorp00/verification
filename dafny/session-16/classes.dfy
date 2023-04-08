

// You are given the following definitions seen at the classroom:

/* AVLs are just binary trees having an additional height field in the nodes */
datatype AVL = Empty  |  Node (left: AVL, height: nat, key: int, right: AVL)

/* This is the AVL invariant */
predicate isAVL (t: AVL)
{
   match t
      case Empty         => true
      case Node(l,h,k,r) => h == height(t)  && isAVL(l) && isAVL(r) && 
                            promising(l, k, r) && -1 <= height(l) - height(r) <= 1
}				

/* This is the binary search tree property at the root level */
predicate promising(l:AVL, x:int, r:AVL) 
{
   (forall z :: z in tset(l) ==> z < x) && 
   (forall z :: z in tset(r) ==> x < z)
}		

function inorder(t: AVL): seq<int>
{
   match t
      case Empty         => []
      case Node(l,_,x,r) => inorder(l)+[x]+inorder(r)
}				

/* this is the mathematical model implemented by an AVL */
function tset(t:AVL): set<int>
{
   match t
      case Empty          => {}		
      case Node(l,_,x,r) => tset(l)+{x}+tset(r)	
}				

/* these are both specification and implementation methods */
function method max (x:int, y:int): int
{
  if x >= y then x else y
}				

function method abs (x: int): nat
{
  if x >= 0 then x else -x
}				

/* these are specification-oriented ghost functions */
function height(t: AVL) : nat
{
  match t 
     case Empty         => 0 
     case Node(l,_,_,r) => 1 + max (height(l), height(r)) 
}				

// It is automatically proven by structural induction
lemma heights (t: AVL)
requires isAVL(t)				
ensures height(t) == myHeight(t)
{
}				

/* These are the smart constructors, the first one visible from outside */
function method empty (): AVL
ensures isAVL(empty())
ensures tset(empty()) == {}			   // model-based postcontition
{ 
  Empty
}

function method node(l: AVL, x: int, r: AVL): AVL
requires promising(l,x,r)
requires  isAVL(l) && isAVL(r)
requires -1 <= height(l) - height(r) <= 1
ensures isAVL(node(l,x,r))
ensures tset(node(l, x, r)) == tset(l) + {x} + tset(r)	// model-based postcontition
{
    Node(l, 1 + max (myHeight(l), myHeight(r)), x, r)
}				


function method myHeight(t: AVL): nat
{
  match t 
     case Empty         => 0 
     case Node(_,h,_,_) => h
}		

function method search(x:int, t: AVL): bool
requires isAVL(t)
ensures search(x, t) == (x in tset(t))
{
   match t
      case Empty          => false
      case Node (l,_,y,r) =>  if x < y then  search (x, l)
                              else if x > y  then search (x, r)
                                              else true
}

/* Visible insertion function */
function method insert(x: int, t: AVL): AVL     
requires isAVL(t)                                     // it assumes the datatype invariant
ensures isAVL(insert(x, t))                           // it ensures the datatype invariant
ensures 0 <= height(insert(x, t)) - height(t) <= 1    // and some internal properties                  
ensures tset(insert(x,t)) == tset(t) + {x}			   // this is the model-based postcondition					 

/* O(1) method that balances the tree, if needed */
function method equil(l: AVL, x: int, r: AVL): AVL
requires promising(l, x, r)
requires isAVL(l) && isAVL(r)
requires abs(height(l)-height(r)) <= 2
ensures  isAVL(equil(l,x,r))
ensures  max(height(l), height(r)) <= height(equil(l, x, r)) <= max(height(l), height(r))+1		
ensures  tset(equil(l, x, r)) == tset(l) + {x} + tset (r)

// it implements the LL and LR rotations
function method leftUnbalance(l: AVL, x: int, r: AVL): (res: AVL)
requires height(l) == height(r) + 2
requires promising(l, x, r)
requires isAVL(l) && isAVL(r)
ensures isAVL(leftUnbalance(l, x, r))
ensures tset(leftUnbalance(l, x, r)) == tset(l) + {x} + tset (r)
ensures max(height(l), height(r)) <= height(res) <= max(height(l), height(r)) + 1		

// it implements the RR and RL rotations
function method rightUnbalance(l: AVL, x: int, r: AVL): (res: AVL)
requires height(r) == height(l) + 2
requires promising(l, x, r)
requires isAVL(l) && isAVL(r)
ensures isAVL(res)
ensures tset(res) == tset(l) + {x} + tset (r)
ensures max(height(l), height(r)) <= height(res) <= max(height(l), height(r)) + 1	

// Classes Node and List

class Node {
    var val: int;
    var next: Node?    
    ghost var repr: set<object>;
    ghost var model : seq<int>;

    predicate Valid() 
    reads this, repr
//    decreases repr
    {
        (next == null ==> model == [val]) &&
        this in repr && (next != null ==> 
                next in repr && next.repr <= repr 
                && this !in next.repr 
                && next.Valid()
                && model == [val] + next.model
        )
    }

    constructor (v: int) 
    ensures Valid()
    ensures model == [v]
    ensures repr == {this}
    {
        val  := v;
        next := null;
        repr := {this};
        model := [v];
    }

   function length() : nat
   reads this
   reads repr
   requires Valid()
   ensures length () == |model|
    {
        if next == null then 1 else 1 + next.length()
    }
     
    method append (node: Node)
    ensures model == old(model) + node.model
}

class List {
    var first : Node?;
    ghost var repr: set<object>;
   ghost var model: seq<int>;

    
    predicate Valid() 
    reads this, repr
    {
        (first == null ==> model == []) && 
        this in repr && 
        (first != null ==> first in repr && 
        (model == first.model) && 
        first.repr <= repr && 
        this !in first.repr && 
        first.Valid())
    }

    constructor () 
    ensures Valid()
    ensures fresh(repr)
    ensures model == []
    {
        first := null;
        repr := {this};
        model := [];
    }    

    function length (): nat
    reads this
    reads repr
    requires Valid()
    ensures length () == |model|
    {
        if first == null then 0 else first.length()
    }

    // This adds an element to the left of the list
    method add (v: int)
    modifies this
    requires Valid()
    ensures Valid()
    ensures model == [v] + old(model)
    {
        var node := new Node(v);  
        assert node.repr == {node};
        assert first != null ==> this !in first.repr;
        node.next :=  first;      
        node.repr := node.repr + (if first == null then {} else first.repr); 
        node.model := [v] +  (if first == null then [] else first.model);
        assert node.Valid();
        assert first != null ==> this !in node.repr;
        first := node; 
        repr := {this} + node.repr;
        model := node.model;
    }


    // This method adds an element to the end of the list
    method append(v: int)
    ensures model == old(model)+ [v]
}

method Main ()
{
    var l := new List();
    assert l.length () == 0;
    l.add(1);
    assert l.length () == 1;
    l.add(2);
    assert l.length() == 2;
    l.append(7);
    //assert l.model() == [2,1,7];
}




// ********************* Home Exercises on AVLS and classes, March 2023 ******************************


// 1. You have to program and verify the following function which computes the union of  two AVLs.
// You have to use the two auxiliary functions shown below, which you must also program and verify

function method union (t1: AVL, t2: AVL) : (res: AVL)
requires isAVL(t1) && isAVL(t2)
ensures isAVL(res)
ensures tset(res) == tset(t1) + tset(t2)

// it splits an AVL into two, respectively containing the keys smaller and greater than x. 
function method split (x: int, t:AVL) : (res: (AVL, AVL))
requires isAVL(t)
ensures isAVL(res.0) && isAVL(res.1)
ensures tset(res.0) + tset(res.1) == tset (t) - {x}
ensures forall z | z in tset(res.0) :: z < x
ensures forall z | z in tset(res.1) :: x < z

// it joins three promising pieces into a single AVL
function method union3 (l: AVL, x:int, r: AVL) : (res: AVL)
requires isAVL(l) && isAVL(r)
requires forall z | z in tset(l) :: z < x
requires forall z | z in tset(r) :: x < z
ensures isAVL(res)
ensures tset(res) == tset(l) + {x} + tset(r)


// 2. Specify, implement and verify the append methods in classes Node and List shown above
//    which adds a new element to the right of the list.


// 3. Specify, implement and verify a reverse method in the class List shown above, which reverses
//    the list


// 4. Assuming that an instance of the class List shown above is sorted, and given an integer x,
// Specify, implement and verify an insert method which inserts x in order in the list


// 5. Given an instance of the class List shown above, and an integer x,
// Specify, implement and verify a delete method which deletes the leftmost copy of x in the list,
// if one is present. Otherwise, do nothing  <-- MINE


// 6. Take the WilliamsHeap file given in Session 16, enrich it with a model function, and prove
// a postcondition in the heapsort algorithm showing that the final array is sorted. Choose as
// model for a heap the multiset of its elements.



