/*
    Final Exam, June 10th, 2021
    Exercise on algebraic datatypes

    You are given the definitions below and you are asked to represent
    sets of integers as sorted lists of integers without duplicates

    You are also given the specifications of the emptySet, singleton, union and 
    intersection functions. Your task consists of implementing and verifying 
    them. The cost of union and intersection should in O(n1+n2), being n1 and n2
    the cardinals of the sets received as arguments. 
*/

datatype List<T> = Nil | Cons(head:T, tail:List<T>)

predicate noDup <T> (l:List<T>)
{
    match l
        case Nil        => true
        case Cons(x,xs) => x !in elems(xs) && noDup(xs)
}

predicate sorted (l:List<int>)
{
    match l 
       case Nil         => true
       case Cons(x, xs) => 
            match xs 
               case Nil         => true
               case Cons(y, ys) => x <= y && sorted(xs)
}

function elems <T> (l:List<T>) : set<T>
{
    match l
       case Nil         => {}
       case Cons(x, xs) => {x} + elems(xs)
}

///////////////////////////////////////////////////////////////

function method emptySet() : (res:List<int>)
ensures elems(res) == {}
{
    Nil
}

function method singleton(x:int): (res:List<int>)
ensures elems(res) == {x} && noDup(res)
{
    Cons(x, emptySet())
}

function method insertSorted(l:List<int>, y:int) : (res:List<int>)
requires sorted(l) && noDup(l)
ensures sorted(res) && noDup(res)
ensures elems(res) == elems(l) + {y}
{
    match l
        case Nil        => singleton(y)
        case Cons(x,xs) =>
            if y < x then
                lessHeadNotElems(y,l);
                Cons(y,l)
            else
                if y == x then
                    l
                else
                    Cons(x,insertSorted(xs,y))
}


function method union (l1:List<int>,l2:List<int>): (res: List<int>)
requires sorted(l1) && sorted(l2) && noDup(l1) && noDup(l2)
ensures sorted(res) && noDup(res)
ensures elems(res) == elems(l1) + elems (l2)
decreases l2
{
    match l1
        case Nil            => l2
        case Cons(x, xs)    =>
            match l2
                case Nil            => l1
                case Cons(y, ys)    =>
                    if x < y then
                        var auxL1 := insertSorted(xs,y);
                        var auxL2 := Cons(x, auxL1);
                        union(auxL2, ys)
                    else
                        if x == y then
                            union(l1, ys)
                        else
                            assert x > y;
                            lessHeadNotElems(y,l1);
                            assert y !in elems(l1);
                            union(Cons(y,l1),ys)
}

lemma lessHeadNotElems(y:int, l:List<int>)
requires sorted(l)
requires l != Nil
ensures y < l.head ==> y !in elems(l)
{}

/////////////////////////////////

function method inters (l1:List<int>,l2:List<int>): (res: List<int>)
requires sorted(l1) && sorted(l2) && noDup(l1) && noDup(l2)
ensures sorted(res) && noDup(res)
ensures elems(res) == elems(l1) * elems (l2)
{
    match l1
        case Nil        => Nil
        case Cons(x,xs) =>
            match l2
                case Nil        => Nil
                case Cons(y,ys) =>
                    if x < y then
                        lessHeadNotElems(x,l2);
                        assert x !in elems(l2);
                        assert sorted(inters(xs,l2));
                        inters(xs,l2)
                    else
                        if x == y then
                            sortedOrder(l1);
                            Cons(x,inters(xs,ys))
                        else
                            assert y < x;
                            lessHeadNotElems(y,l1);
                            assert y !in elems(l1);
                            assert sorted(inters(l1,ys));
                            inters(l1,ys)
}

lemma sortedOrder(l:List<int>)
requires l != Nil
requires sorted(l) && noDup(l)
ensures forall e | e in elems(l.tail) :: l.head < e
{}