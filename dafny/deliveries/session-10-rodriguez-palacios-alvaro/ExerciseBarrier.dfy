// Auxiliary Predicates

predicate isMax(s:seq<int>, m:int)
requires |s| > 0
{
    (forall i:int | 0 <= i < |s| :: s[i] <= m)
}

predicate isMin(s:seq<int>, m:int)
requires |s| > 0
{
    (forall i:int | 0 <= i < |s| :: s[i] >= m)
}

// Auxiliary functions

function max(s:seq<int>) : int
requires |s| > 0
ensures forall i:int | 0 <= i < |s| :: max(s) >= s[i]
ensures exists i:int | 0 <= i < |s| :: s[i] == max(s)
ensures isMax(s, max(s))
decreases |s|
{
    if (|s| == 1) then
        s[0]
    else
        if (s[0] >= max(s[1..|s|])) then
            s[0]
        else
            max(s[1..|s|])
}

function min(s:seq<int>) : int
requires |s| > 0
ensures forall i:int | 0 <= i < |s| :: min(s) <= s[i]
ensures exists i:int | 0 <= i < |s| :: s[i] == min(s)
ensures isMin(s, min(s))
decreases |s|
{
    if (|s| == 1) then
        s[0]
    else
        if (s[0] <= min(s[1..|s|])) then
            s[0]
        else
            min(s[1..|s|])
}

// ############################### //
// ############################### //
// ### BARRIER METHOD EXERCISE ### //
// ############################### //
// ############################### //

//Method barrier below receives an array and an integer p
//and returns a boolean b which is true if and only if 
//all the positions to the left of p and including also position p contain elements 
//that are strictly smaller than all the elements contained in the positions to the right of p 
//Examples:
// If v=[7,2,5,8] and p=0 or p=1 then the method must return false, 
// but for p=2 the method should return true
//1.Specify the method
//2.Implement an O(v.size()) method
//3.Verify the method

method barrier(v:array<int>,p:int) returns (b:bool)
requires v.Length > 0
requires 0 <= p < v.Length
ensures p == v.Length - 1 ==> b == true
ensures p < v.Length - 1 ==> b == (max(v[0..p+1]) < min(v[p+1..v.Length]))
{
    b := true;
    
    if (p == v.Length - 1) {
        return b;
    }
    
    var i := 1;
    var maxl := v[i-1];

    while ( i <= p )
        decreases p - i
        invariant 1 <= i <= p + 1
        // invariant isMax(v[0..i], maxl)
        invariant maxl == max(v[0..i])
    {
        if (v[i] > maxl) {
            maxl := v[i];
        }
        i := i + 1;
    }

    // assert isMax(v[0..i], maxl);

    var j := i + 1;
    var minr := v[j-1];

    while (j < v.Length)
        decreases v.Length - j
        invariant i < j <= v.Length
        // invariant isMin(v[i..j], minr)
        // invariant forall k:int | i <= k < j :: minr <= v[k]
        invariant exists k:int | i <= k < j :: v[k] == minr
        invariant minr == min(v[i..j])
    {
        if (v[j] < minr) {
            minr := v[j];
        }
        j := j + 1;
    }

    // assert isMin(v[p+1..j], minr);

    b := maxl < minr;
}

// Example of calling the method

method main()
{
    var v:array<int>;
    v:=new int[4][7,2,5,8];

    var b := barrier(v, 2);
    assert b;

    b := barrier(v, 1);
    assert !b;

    b := barrier(v, 0);
    assert !b;
}