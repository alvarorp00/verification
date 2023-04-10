// Classes Node and List

class Node {
    var val: int;
    var next: Node?    // ? means that it is nullable
    ghost var repr: set<object>;
    ghost var model : seq<int>;

    predicate Valid() 
    reads this, repr
//    decreases repr
    {
        (next == null ==> model == [val]) &&
        this in repr && (next != null ==> 
                next in repr && next.repr <= repr && repr == {this} + next.repr
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
    modifies repr
    requires Valid()
    requires node.Valid()
    decreases repr
    ensures Valid()
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
    ensures fresh(repr - old(repr))  // since we are adding a new node, we expect a new fresh object
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
    modifies repr
    requires Valid()
    decreases repr
    ensures Valid()
    ensures model == old(model) + [v]
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
    assert l.model == [2,1,7];
}


/* METHOD TO SOLVE */

method deleteFirstVal(l:List, v:int)
modifies l, l.repr
requires l.Valid()
ensures fresh(l.repr - old(l.repr))
ensures l.Valid()
{
    if (l.first != null) {
        if (l.first.val == v) {
            l.first := l.first.next;
            l.model := [] + (if l.first == null then [] else l.first.model);
            l.repr := {l} + (if l.first == null then {} else l.first.repr);
        } else {
            if (l.first.next != null) {
                deleteFirstValNode(l.first, l.first.next, v, true);
                l.model := [] + l.first.model;
                l.repr := {l} + l.first.repr;
            }
        }
    }
}

/*
 * This method deletes the first occurrence of v in the list starting at prev.next
 * If search is true, then we are searching the first occurrence of v
 * If search is false, then we are shifting the list to the left as v was already found
*/
method deleteFirstValNode(prev:Node, next:Node, v:int, search:bool)
modifies prev, prev.repr
requires prev.Valid()
requires next.Valid()
requires prev.next == next
decreases prev.repr
ensures fresh(prev.repr - old(prev.repr))
ensures (v in prev.model) ==> (prev.repr != old(prev.repr))
ensures !search ==> (prev.repr != old(prev.repr))  // We're shifting the list to the left
ensures search && old(prev.val) == v ==> (prev.val == old(next.val))  // We're searching the first occurrence of v
ensures prev.Valid()
ensures next.Valid()
{
    if (search) {
        if (prev.val == v) {
            prev.val := next.val;
            if (next.next == null) {
                prev.next := null;
                prev.model := [prev.val];
                prev.repr := {prev};
            } else {
                deleteFirstValNode(next, next.next, v, false);
                prev.model := [prev.val] + next.model;
                prev.repr := {prev} + next.repr;
            }
        } else {
            if (next.next == null) {
                if (next.val == v) {
                    // Value found at the end of the list
                    prev.next := null;
                    prev.model := [prev.val];
                    prev.repr := {prev};
                } else {
                    // Value not found
                    next.next := null;
                    next.model := [next.val];
                    next.repr := {next};
                    
                    prev.next := next;
                    prev.model := [prev.val] + [next.val];
                    prev.repr := {prev} + {next};
                }
            } else {
                deleteFirstValNode(next, next.next, v, true);
                prev.model := [prev.val] + next.model;
                prev.repr := {prev} + next.repr;
            }
        }
    } else {  // We've already found the value
        // We don't care about val, we just shift the values to the left
        if (next.next == null) {
            prev.val := next.val;
            prev.next := null;
            prev.model := [prev.val];
            prev.repr := {prev};
        } else {
            prev.val := next.val;
            deleteFirstValNode(next, next.next, v, false);
            prev.model := [prev.val] + next.model;
            prev.repr := {prev} + next.repr;
        }

        // assert prev.Valid();
        // assert next.Valid();
    }
}
















// /* ALTERNATE VERSION */

// method deleteFirst2(l:List, v:int)
// modifies l, l.repr, l.first
// requires l.Valid()
// // requires |l.model| >= 2 // list won't be empty after deletion
// requires l.first != null
// requires l.first.next != null
// decreases l.repr
// // ensures fresh(l.repr - old(l.repr))
// ensures l.Valid()
// // ensures v !in l.model ==> l.repr == old(l.repr)
// // ensures v in l.model ==> l.repr != old(l.repr)
// {
//     var prev:Node;
//     var next:Node;
//     var b:bool;

//     if (l.first.val == v) {
//         l.repr := l.repr - {l.first};
//         l.first := l.first.next;
//         l.model := [] + l.first.model;
//     } else {
//         b, prev, next := seekValPair(l.first, l.first.next,v);

//         if (b) {
//             /*
//                 requires init.next != null == init == prev
//             */
            
//             shiftLeftDeleteRec2(l.first, prev, next);
//         } else {
//             assert v !in next.model;
//             assert v !in l.model;
//         }
//     }
// }

// /* #################### SEEKERS #################### */

// // This method returns the first node with value v
// // or the last node if no node with value v is found
// // b is true if a node with value v is found
// method seekVal_v2(n:Node, v:int) returns (b:bool, res:Node)
// requires n.Valid()
// decreases n.repr
// ensures res.Valid()
// ensures b <==> v in n.model
// {
//     b := false;
//     if n.val == v {
//         res := n;
//         b := true;
//     } else {
//         if n.next == null {
//             res := n;
//             b := false;
//         } else {
//             b, res := seekVal_v2(n.next,v);
//         }
//     }
// }

// // This method returns the first node with value v
// method seekVal(n:Node, v:int) returns (res:Node?)
// requires n.Valid()
// decreases n.repr
// ensures v in n.model ==> res != null && res.val == v
// ensures v !in n.model ==> res == null
// {
//     if n.val == v {
//         res := n;
//     } else {
//         if n.next == null {
//             res := null;
//         } else {
//             res := seekVal(n.next,v);
//         }
//     }
// }

// // This method returns the previous and
// // next node to a one with value v
// // It does not search on the left at the start
// method seekValPair(left:Node, right:Node, v:int) returns (b:bool, prev:Node, next:Node)
// requires left.Valid()
// requires right.Valid()
// requires left.next == right
// decreases left.repr
// ensures prev.Valid()
// ensures next.Valid()
// ensures prev.next == next
// ensures b <==> v in right.model
// ensures b <==> v in next.model
// ensures v in right.model ==> v in left.model // Make it clear
// ensures next in prev.repr
// ensures prev in left.repr
// ensures left != prev ==> prev.repr < left.repr
// {
//     prev := left;
//     next := right;
//     if right.val == v {  // Value found
//         // prev := left;
//         // next := right;
//         b := true;
//     } else {
//         if right.next == null {  // Value not found
//             b := false;
//         } else {  // Value not found, continue search
//             b, prev, next := seekValPair(right,right.next,v);
//         }
//     }
// }

// /* ############## SHIFT ############## */


// // This method shifts the values of the list one to the left
// // so the leftmost element (value, not node) is deleted
// method shiftLeftDeleteRec(prev:Node, next:Node)
// modifies prev.repr
// modifies next.repr
// requires prev.Valid()
// requires next.Valid()
// requires prev.next == next
// decreases prev.repr
// // ensures fresh(prev.repr - old(prev.repr))
// // ensures fresh(next.repr - old(next.repr))
// ensures prev.Valid()
// ensures next.Valid()
// ensures prev.val == old(next.val)
// ensures prev.repr < old(prev.repr)
// ensures next.next != null ==> prev.next == next
// ensures old(prev.model) == [old(prev.val)] + prev.model
// {
//     if next.next == null {
//         prev.next := null;
//         prev.val := next.val;
//         prev.model := [prev.val];
//         prev.repr := {prev};
//         assert prev.Valid();
//         assert next.Valid();
//     } else {
//         prev.val := next.val;
//         shiftLeftDeleteRec(next, next.next);
//         prev.next := next;
//         assert next.Valid();
//         prev.model := [prev.val] + next.model;
//         prev.repr := {prev} + next.repr;
//     }
// }

// method shiftLeftDeleteRec2(init:Node, prev:Node, next:Node)
// modifies init.repr
// modifies prev.repr
// modifies next.repr
// requires init.Valid()
// requires prev.Valid()
// requires next.Valid()
// requires prev.next == next
// requires prev in init.repr
// requires init != prev ==> prev.repr < init.repr
// requires init == prev ==> prev.repr == init.repr
// requires next in prev.repr
// // requires init.next != null == init == prev
// decreases init.repr
// // ensures fresh(prev.repr - old(prev.repr))
// // ensures fresh(next.repr - old(next.repr))
// ensures prev.Valid()
// ensures next.Valid()
// ensures prev.repr < old(prev.repr)
// ensures old(prev.model) == [old(prev.val)] + prev.model
// {
//     if (init == prev) {
//         // Can just happen if init == prev when calling this method
//         shiftLeftDeleteRec(prev, next);
//     } else {
//         shiftLeftDeleteRec2(init.next, prev, next);
//     }
// }

// /* ############## DELETE LAST ############## */

// // This method deletes the last element of the list
// // and returns the value of the deleted element
// method deleteLast(n:Node) returns (v:int)
// modifies n.repr
// requires n.Valid()
// requires n.next != null
// decreases n.repr
// ensures fresh(n.repr - old(n.repr))
// ensures n.Valid()
// ensures n.repr < old(n.repr)
// ensures old(n.model) == n.model + [v]
// {
//     var next:Node := n.next;
//     if next.next == null {
//         n.next := null;
//         n.model := [n.val];
//         n.repr := {n};

//         v := next.val;
//     } else {
//         v := deleteLast(next);
//         n.next := next;
//         n.model := [n.val] + next.model;
//         n.repr := {n} + next.repr;
//     }
// }


// /* ############## PREDS ############## */

// predicate isSucc(init:Node, other:Node)
// reads init, init.repr
// requires init.Valid()
// decreases init.repr
// {
//     if (init.next == null) then
//         false
//     else
//         init.next == other || isSucc(init.next, other)
// }

// /* ############## LEMMAS ############## */

// lemma succRepr(init:Node, other:Node)
// requires init.Valid()
// requires other.Valid()
// requires other in init.repr
// requires init.next == null ==> init == other
// decreases init.repr
// ensures other !in {init}
//     ==> other in init.next.repr
// {}

// lemma smallerRepr(init:Node)
// requires init.Valid()
// requires init.next != null
// ensures init.next.repr < init.repr
// {}

// lemma setMembership(init:Node, other:Node)
// requires init.Valid()
// requires other.Valid()
// requires other in init.repr
// requires isSucc(init, other)
// decreases init.repr
// ensures other.repr <= init.repr
// {
//     if other == init {
//         assert other in init.repr;
//     } else {
//         smallerRepr(init);
//         assert init.next.repr < init.repr;
//         assert other !in {init};
//         assert other in init.next.repr;
//         if (other == init.next) {
//             assert other.repr == init.next.repr;
//         } else {
//             setMembership(init.next, other);
//         }
//     }
// }

// lemma succRepr2(init:Node, other:Node)
// requires init.Valid()
// requires other.Valid()
// requires other in init.repr
// requires other != init
// requires isSucc(init, other)
// ensures other in init.repr && other != init ==> other.repr < init.repr
// {
//     if (init.next == null) {
//         assert init == other;
//     } else {
//         assert init.repr == {init} + init.next.repr;
//         succRepr(init, other);
//         assert other !in {init};
//         assert other in init.next.repr;
//         assert isSucc(other,init) ==>
//             other == init.next || isSucc(init.next, other);
//         if (other == init.next) {
//             assert other.repr == init.next.repr;
//         } else {
//             // isSucc(init.next, other);
//             setMembership(init.next, other);
//         }
//     }
// }