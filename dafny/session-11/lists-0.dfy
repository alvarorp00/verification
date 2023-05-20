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

function sum(l:List<int>): (res:int)
{
    match l 
        case Nil         => 0
        case Cons(y, ys) => y + sum(ys)
}

function insert(x: int, l:List<int>): (res:List<int>)
requires sorted(l)
ensures sorted(res)
ensures elems(res) == elems(l) + multiset{x}
{
    match l
        case Nil         => Cons(x, Nil)
        case Cons(y, ys) => if x <= y then Cons(x, l)
                            else Cons(y, insert(x, ys))
}

function isort (l:List<int>) : (res:List<int>)
ensures sorted(res)
ensures elems(res) == elems(l)
{
    match l
        case Nil         => Nil
        case Cons(x, xs) => insert(x, isort(xs))
}

function delete<T> (x: T, l:List<T>): (res:List<T>)
ensures elems(res) == elems(l) - multiset{x}
{
    match l
        case Nil         => Nil
        case Cons(y,ys)  => if x == y then ys
                            else Cons(y,delete(x,ys))
}

function search<T> (x: T, l:List<T>): (res:bool)
ensures res == (x in elems(l))
{
    match l
        case Nil        => false
        case Cons(y,ys) => if x == y then true
                           else search(x,ys)
}

function min(x:nat, y:nat): (res:nat)
{
    if x <=y then x else y
}

function take<T> (n: nat, l:List<T>): (res:List<T>)
ensures length(res) == min (n, length(l))
{
    match l
            case Nil        => Nil
            case Cons(y,ys) => if n > 0 then Cons(y, take(n-1, ys))
                               else Nil
}

function drop<T> (n: nat, l:List<T>): (res:List<T>)
ensures length(res) == if length(l) < n then 0 else length(l) - n
{
    match l
            case Nil        => Nil
            case Cons(y,ys) => if n > 0 then drop(n-1,ys)
                               else Cons(y,ys)
}

function method splitWhileNE <T(==)> (x: T, l:List<T>): (res:(List<T>, List<T>))
ensures elems(l) == elems(res.0) + elems(res.1)
{
    match l
      case Nil        => (Nil,Nil)
      case Cons(y,ys) => if x == y then (Nil, l)
                         else var (l1,l2) := splitWhileNE (x, ys);
                              (Cons(y,l1), l2)
}

/*
   Exercises on the fly
*/

// 1. write the code of this function and verify it (but do not use take and drop)

function method split<T> (n: nat, l:List<T>): (res:(List<T>, List<T>))
ensures length(res.0) == min (n, length(l))
ensures length(res.1) == if length(l) < n then 0 else length(l) - n
ensures elems(l) == elems(res.0) + elems(res.1)
{
    if n > 0 then
        match l
            case Nil        => (Nil,Nil)
            case Cons(y,ys) => var (l1,l2) := split (n-1, ys);
                               (Cons(y,l1), l2)
    else (Nil, l)
}

// 2. specify, write the code of this function, and verify it

function method reverse(l:List<int>): (res:List<int>)
ensures length(res) == length(l)
ensures elems(res) == elems(l)
{
    match l
        case Nil        => Nil
        case Cons(x,xs) =>
            concat(reverse(xs),Cons(x,Nil))

}

// 3. specify, write the code of this function, and verify it

function method concat(l1:List<int>,l2:List<int>): (res:List<int>)
ensures elems(res) == elems(l1) + elems(l2)
ensures length(res) == length(l1) + length(l2)
{
    match l1
        case Nil        => l2
        case Cons(x,xs) =>
            Cons(x,concat(xs,l2))
                    
}

