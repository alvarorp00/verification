//Author: Clara Segura
include "List.dfy"


method Replace(l:List<int>,x:int,y:int)
modifies l,l.Repr()
requires allocated(l.Repr())
ensures allocated(l.Repr())
ensures fresh(l.Repr() - old(l.Repr()))

requires l.Valid()
ensures l.Valid() && |old(l.Model())|==|l.Model()|
ensures forall i | 0 <= i < |l.Model()| :: old(l.Model()[i]) == x ==> l.Model()[i] == y
ensures forall i | 0 <= i < |l.Model()| :: old(l.Model()[i]) != x ==> l.Model()[i] == old(l.Model()[i])

ensures l.Iterators() >= old(l.Iterators())
{
    var iter := l.First();
    var b := iter.HasPeek();
    while (b)
        decreases |l.Model()| - iter.Index()
        invariant allocated(l.Repr())
        invariant fresh(l.Repr() - old(l.Repr()))

        invariant iter.Valid() && iter.Parent() == l
        // invariant 0 <= iter.Index() <= |l.Model()|
        invariant l.Valid() && |old(l.Model())| == |l.Model()|
        // invariant |old(l.Model())| == |l.Model()|
        // invariant fresh(l.Repr() - old(l.Repr()))
        
        invariant forall i | iter.Index() <= i < |old(l.Model())| :: old(l.Model()[i])==l.Model()[i]

        invariant forall i | 0 <= i < iter.Index() :: old(l.Model()[i]) == x ==> l.Model()[i] == y
        invariant forall i | 0 <= i < iter.Index() :: old(l.Model()[i]) != x ==> l.Model()[i] == old(l.Model()[i])
        
        invariant b == iter.HasPeek?()
        invariant l.Iterators() >= old(l.Iterators())
    {
        var peek := iter.Peek();
        if (peek == x) {
            iter.Set(y);
        }
        iter.Next();
        b := iter.HasPeek();
    }
}

//ensures: write the properties concerning the model
//replace each occurrence of x by y, and leave the rest unchanged 



