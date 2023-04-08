

//a valid index of the array contains x
predicate appears(v:array<int>,x:int)
reads v
{
    exists i:int :: 0 <= i && i < v.Length && v[i] == x
}

//a valid index of the array contains 0
predicate existCero(v:array<int>)
reads v
{
    exists i:int :: 0 <= i && i < v.Length && v[i] == 0
}

//all the valid indexes contain strictly positive integers
predicate allPositive(v:array<int>)
reads v
{
    forall i:int :: 0 <= i && i < v.Length ==> v[i] > 0
}

//x appears exactly once in the array
predicate exactlyOne(v:array<int>,x:int)
reads v
{
    exists i:int :: 0 <= i && i < v.Length && v[i] == x && (forall j:int :: 0 <= j && i != j && j < v.Length && v[j] != x)
}

//mathematical function to count the number of times that x appears in v in range [c,f)
function count(v:array<int>,x:int,c:int,f:int):int
reads v
decreases f-c
requires 0 <= c && c <= f && f <= v.Length
{
    if (c == f) then 0
    else if (v[c] == x) then 1 + count(v,x,c+1,f)
    else count(v,x,c+1,f)
}

//using count define exactlyOnce
predicate exactlyOne2(v:array<int>,x:int)
reads v
{
    count(v,x,0,v.Length) == 1
}

//x is the maximum element of v
predicate isMax(v:array<int>,x:int)
reads v
{
    forall i:int :: appears(v,x) && 0 <= i  && i < v.Length && v[i] <= x
}

//i is one position of the minimum of v
predicate posMin(v:array<int>,i:int)
reads v
requires 0 <= i && i < v.Length
{
    forall j:int :: 0 <= j && j < v.Length && i != j ==> v[i] <= v[j]
}

//each element in v is the double of its index
predicate allDouble(v:array<int>)
reads v
{
    forall i:int :: 0 <= i && i < v.Length ==> v[i] == i * 2
}


//v is the mirror of w
predicate mirror(v:array<int>,w:array<int>)
reads v, w
{
    if w.Length != v.Length then false
    else forall i:int :: 0 <= i && i < v.Length && i < w.Length ==> v[i] == w[w.Length - i - 1]
}

//Write a main program to experiment with these predicates

method main()
{
    var x:int; var y:int; var z:int;
    var v:array<int> := new int[10](i => i);

    x := 0;
    y := 1;
    z := 2;

    // assert appears(v,x);
}