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
    modifies repr
    requires Valid()
    requires node.Valid()
    requires forall o :: o in repr ==> o !in node.repr
    requires node !in repr
    decreases repr
    ensures Valid()
    ensures repr == old(repr) + node.repr
    ensures model == old(model) + node.model
    {
        if next == null {
            next := node;
        }
        else {
            next.append(node);
        }
        repr := repr + node.repr;
        model := model + node.model;
    }
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
    {
        var node := new Node(v);
        if first == null {
            first := node;
        } else {
            first.append(node);
        }
        repr := repr + {node};
        model := model + [v];
    }
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

method deleteFirst(l:List, v:int)
modifies l.repr
requires l.Valid()
// requires |l.model| >= 2 // list won't be empty after deletion
requires l.first != null
requires l.first.next != null
decreases l.repr
// ensures fresh(l.repr - old(l.repr))
ensures l.Valid()
// ensures v !in l.model ==> l.repr == old(l.repr)
// ensures v in l.model ==> l.repr != old(l.repr)
{
    var prev:Node;
    var next:Node;
    var b:bool;

    if (l.first.val == v) {
        l.repr := l.repr - {l.first};
        l.first := l.first.next;
        l.model := [] + l.first.model;
    } else {
        b, prev, next := seekValPair(l.first, l.first.next,v);

        if (b) {
            assert v in next.model;
            assert v in l.model;
            // shiftLeftDeleteRec(prev, next);
        } else {
            assert v !in next.model;
            assert v !in l.model;
            // pass
        }
    }
}

// This method returns the first node with value v
// or the last node if no node with value v is found
// b is true if a node with value v is found
method seekVal_v2(n:Node, v:int) returns (b:bool, res:Node)
requires n.Valid()
decreases n.repr
ensures res.Valid()
ensures b <==> v in n.model
{
    b := false;
    if n.val == v {
        res := n;
        b := true;
    } else {
        if n.next == null {
            res := n;
            b := false;
        } else {
            b, res := seekVal_v2(n.next,v);
        }
    }
}

// This method returns the first node with value v
method seekVal(n:Node, v:int) returns (res:Node?)
requires n.Valid()
decreases n.repr
ensures v in n.model ==> res != null && res.val == v
ensures v !in n.model ==> res == null
{
    if n.val == v {
        res := n;
    } else {
        if n.next == null {
            res := null;
        } else {
            res := seekVal(n.next,v);
        }
    }
}

// This method returns the previous and
// next node to a one with value v
// It does not search on the left at the start
method seekValPair(left:Node, right:Node, v:int) returns (b:bool, prev:Node, next:Node)
requires left.Valid()
requires right.Valid()
requires left.next == right
decreases left.repr
ensures prev.Valid()
ensures next.Valid()
ensures prev.next == next
ensures b <==> v in right.model
ensures b <==> v in next.model
ensures v in right.model ==> v in left.model // Make it clear
{
    prev := left;
    next := right;
    if right.val == v {  // Value found
        // prev := left;
        // next := right;
        b := true;
    } else {
        if right.next == null {  // Value not found
            b := false;
        } else {  // Value not found, continue search
            b, prev, next := seekValPair(right,right.next,v);
        }
    }
}

// This method shifts the values of the list one to the left
// so the leftmost element (value, not node) is deleted
method shiftLeftRec(prev:Node, next:Node)
modifies prev.repr
modifies next.repr
requires prev.Valid()
requires next.Valid()
requires prev.next == next
decreases prev.repr
// ensures fresh(prev.repr - old(prev.repr))
// ensures fresh(next.repr - old(next.repr))
ensures prev.Valid()
ensures next.Valid()
ensures prev.val == old(next.val)
ensures prev.repr < old(prev.repr)
ensures old(prev.model) == [old(prev.val)] + prev.model
{
    if next.next == null {
        prev.next := null;
        prev.val := next.val;
        prev.model := [prev.val];
        prev.repr := {prev};
        assert prev.Valid();
        assert next.Valid();
    } else {
        prev.val := next.val;
        shiftLeftRec(next, next.next);
        prev.next := next;
        assert next.Valid();
        prev.model := [prev.val] + next.model;
        prev.repr := {prev} + next.repr;
    }
}

// This method deletes the last element of the list
// and returns the value of the deleted element
method deleteLast(n:Node) returns (v:int)
modifies n.repr
requires n.Valid()
requires n.next != null
decreases n.repr
ensures fresh(n.repr - old(n.repr))
ensures n.Valid()
ensures n.repr < old(n.repr)
ensures old(n.model) == n.model + [v]
{
    var next:Node := n.next;
    if next.next == null {
        n.next := null;
        n.model := [n.val];
        n.repr := {n};

        v := next.val;
    } else {
        v := deleteLast(next);
        n.next := next;
        n.model := [n.val] + next.model;
        n.repr := {n} + next.repr;
    }
}

// method refreshList(l:List)
// modifies l
// ensures l.Valid()
// {
//     if l.first == null {
//         l.model := [];
//         l.repr := {l};
//     } else {

//     }
// }

// method refreshNode(n:Node)
// modifies n
// decreases n.repr
// ensures n.Valid()
// {
//     if n.next == null {
//         n.next := null;
//         n.model := [n.val];
//         n.repr := {n};
//         assert n.Valid();
//     } else {
//         refreshNode(n.next);
//         n.model := [n.val] + n.next.model;
//         n.repr := {n} + n.next.repr;
//     }
// }