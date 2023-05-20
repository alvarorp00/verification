

//Exercise 1: 5 pts
//Given an array of positive integers we want to know if it "evenOdd", 
// i.e. if it is formed by a (possibly empty) sequence of even numbers 
//followed by a (possibly empty) sequence of odd numbers
//In that case we want to return the integer p in [0..v.Length] such that 
//all elements in v[0..p) are even and those in v[p..v.Length) are odd

//For example: 
//array v = [2, 1, 7, 5] is evenOdd, and we return p=1
//array v = [6, 2, 20]  is evenOdd, and we return p=3 
//array v = [2, 3, 8] is not evenOdd
//array v = [5, 6] is not evenOdd


predicate positive(s:seq<int>)
{
    forall k :: 0 <= k < |s| ==> s[k] >= 0
}

//1. [0.5pt] Define the following predicates 

//All the elements in v[i..j) are even
predicate even(v:array<int>,i:int,j:int)
reads v
requires 0 <= i <= j <= v.Length
{
    forall k | i <= k < j :: v[k] % 2 == 0
}

//All the elements in v[i..j) are odd
predicate odd(v:array<int>,i:int,j:int)
reads v
requires 0 <= i <= j <= v.Length
{
    forall k | i <= k < j :: v[k] % 2 == 1
}

//2. [1.5pt] Write the postcondition of method evenOdd, which returns 
// - boolean isEvenOdd, which is true if and only if array v is evenOdd as explained above
// - if isEvenOdd is true, then p is an integer in [0..v.Length] such that 
//   all elements in v[0..p) are even and those in v[p..v.Length) are odd
method evenOdd(v:array<int>) returns (isEvenOdd:bool,p:int)
requires positive(v[0..v.Length])
ensures isEvenOdd == (exists i | 0 <= i <= v.Length :: even(v,0,i) && odd(v,i,v.Length))
ensures isEvenOdd ==> (0 <= p <= v.Length)
ensures isEvenOdd ==> even(v,0,p)
ensures isEvenOdd ==> odd(v,p,v.Length)
{
    isEvenOdd := true;
    p := 0;

    if (v.Length == 0) {
        assert even(v,0,0);
        return;
    }
    
    while (p < v.Length && v[p] % 2 == 0)
        decreases v.Length - p
        invariant 0 <= p <= v.Length
        invariant forall k | 0 <= k < p :: v[k] % 2 == 0
        invariant even(v,0,p)
        invariant p == v.Length ==> even(v,0,v.Length)
        invariant isEvenOdd == even(v,0,p)
    {
        if (v[p] % 2 == 0) {
            p := p + 1;
        }
    }

    if (p == v.Length) {
        return;
    }

    assert v.Length > 0;

    var q:int := p;

    while (q < v.Length && isEvenOdd)
        decreases v.Length - q
        invariant p <= q <= v.Length
        invariant isEvenOdd == odd(v,p,q)
    {
        if (v[q] % 2 == 0) {
            isEvenOdd := false;
        }
        q := q + 1;
    }

}

//3. [3 pt] Implement and verify method evenOdd
