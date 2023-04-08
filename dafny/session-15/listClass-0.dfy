class Node {
    var val: int;
    var next: Node?    
//    ghost var repr: set<object>;
//    ghost var model : seq<int>;

/*    predicate Valid() 
    reads this, repr
//    decreases repr
    {
//        (next == null ==> model == [val]) &&
        this in repr && (next != null ==> 
                next in repr && next.repr <= repr 
                && this !in next.repr 
                && next.Valid()
//                && model == [val] + next.model
        )
    }
*/
    constructor (v: int) 
//    ensures Valid()
//    ensures model == [v]
    {
        val  := v;
        next := null;
//        repr := {this};
//        model := [v];
    }

   function length() : nat
//   reads this
//   reads repr
//   requires Valid()
//    ensures length () == |model|
    {
        if next == null then 1 else 1 + next.length()
    }
    
    method append (node: Node)
}

class List {
    var first : Node?;
//    ghost var repr: set<object>;
//    ghost var model: seq<int>;

/*    
    predicate Valid() 
    reads this, repr
    {
//        (first == null ==> model == []) && 
        this in repr && 
        (first != null ==> first in repr && 
//        (model == first.model) && 
        first.repr <= repr && 
        this !in first.repr && 
        first.Valid())
    }
*/
    constructor () 
//    ensures Valid()
//    ensures fresh(repr)
//    ensures model == []
    {
        first := null;
//        repr := {this};
//        model := [];
    }    

    function length (): nat
//   reads this
//   reads repr
//   requires Valid()
//   ensures length () == |model|
    {
        if first == null then 0 else first.length()
    }

    // This adds an element to the left of the list
    method add (v: int)
    //modifies this
    //requires Valid()
    //ensures Valid()
    //    ensures model == [v] + old(model)
    {
        var node := new Node(v);  
        //assert node.repr == {node};
        //assert first != null ==> this !in first.repr;
        node.next :=  first;      
        //node.repr := node.repr + first.repr;//(if first == null then {} else first.repr); 
        //node.model := [v] +  (if first == null then [] else first.model);
        //assert node.Valid();
        //assert first != null ==> this !in node.repr;
        first := node; 
        //repr := {this} + node.repr;
        //model := node.model;
    }

    // This method adds an element to the end of the list
    method append(v: int)
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


