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

// This method checks whether the first element of the list is equal to v
// If it is, it deletes it. If not, it calls a recursive method written below.
method deleteFirstValList(l:List, v:int)
modifies l, l.repr
requires l.Valid()
ensures fresh(l.repr - old(l.repr))
// I don't know how to express more precisely the postcondition about the element removal
// --> possible idea: have a method that returns the number of occurrences of v in l.model
ensures l.Valid()
ensures (v in l.model) ==> (l.repr != old(l.repr))
ensures (v in l.model) ==> (l.length() == old(l.length()) - 1)  // This must be written below l.Valid()
{
    if (l.first != null) {
        if (l.first.val == v) {
            l.first := l.first.next;
            l.model := [] + (if l.first == null then [] else l.first.model);
            l.repr := {l} + (if l.first == null then {} else l.first.repr);
        } else {
            if (l.first.next != null) {
                deleteFirstValNode(l.first, l.first.next, v);
                l.model := [] + l.first.model;
                l.repr := {l} + l.first.repr;
            }
        }
    }
}

/*
 * This method deletes the first occurrence of v in the list starting at prev.next
 *
 * It's possibly not the best solution but I couldn't manage to come up with a better one,
 * so I tried to make it as clear as possible.
 *
 * Cost:
 *  - Best case: O(N), do a linear search and don't find v
 *  - Average case: O(2*N), do a linear search and find v, then shift the list to the left and
 *                  update the model and repr backwards.
*/
method deleteFirstValNode(prev:Node, next:Node, v:int)
modifies prev, prev.repr
requires prev.Valid()
requires next.Valid()
requires prev.next == next
decreases prev.repr
ensures fresh(prev.repr - old(prev.repr))
ensures prev.Valid()
ensures next.Valid()
ensures (v in prev.model) ==> (prev.repr != old(prev.repr))
ensures (v in prev.model) ==> (prev.length() == old(prev.length()) - 1)
{
    if (prev.val == v) {
        assert v in prev.model;
        prev.val := next.val;
        if (next.next == null) {
            prev.next := null;
            prev.model := [prev.val];
            prev.repr := {prev};
            assert old(prev.length()) == (prev.length() + 1);
        } else {
            shiftLeftRec(next, next.next);
            prev.model := [prev.val] + next.model;
            prev.repr := {prev} + next.repr;
        }
    } else {
        if (next.next == null) {
            if (next.val == v) {
                assert v in prev.model;
                // Value found at the end of the list
                prev.next := null;
                prev.model := [prev.val];
                prev.repr := {prev};
            } else {
                assert v !in prev.model;
            }
        } else {
            deleteFirstValNode(next, next.next, v);
            
            prev.model := [prev.val] + next.model;
            prev.repr := {prev} + next.repr;
        }
    }
}

method shiftLeftRec(prev:Node, next:Node)
modifies prev, prev.repr
requires prev.Valid()
requires next.Valid()
requires prev.next == next
decreases prev.repr
ensures fresh(prev.repr - old(prev.repr))
ensures prev.repr != old(prev.repr)
ensures prev.val == old(next.val)
ensures old(prev.model) == [old(prev.val)] + prev.model
ensures prev.Valid()
ensures next.Valid()
ensures prev.length() == old(prev.length()) - 1
{
    if (next.next == null) {
        prev.val := next.val;
        prev.next := null;
        prev.model := [prev.val];
        prev.repr := {prev};
    } else {
        prev.val := next.val;
        shiftLeftRec(next, next.next);
        prev.model := [prev.val] + next.model;
        prev.repr := {prev} + next.repr;
    }
}