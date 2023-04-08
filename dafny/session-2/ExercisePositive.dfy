predicate positive(s:seq<int>)
{forall u :: 0 <= u < |s| ==> s[u] >= 0}

method mpositive(v:array<int>) returns (b:bool)
ensures b == positive(v[..])
{
    var i := 0;
    while (i < v.Length && v[i] >= 0)
        invariant 0 <= i <= v.Length
        invariant positive(v[..i])
        { i := i + 1;}
}

// predicate positive(a:array<int>, i:int)
// reads a
// requires 0<=i<=a.Length
// {forall u :: 0 <= u < a.Length ==> a[u] > 0}

// method mpositive(v:array<int>) returns (b:bool)
// ensures b==positive(v, v.Length)
// {
//     var i := 0;
//     while (i < v.Length && v[i] >= 0)
//         invariant 0 <= i <= v.Length
//         invariant positive(v, i)
//         { i := i + 1;}
//     b := (i == v.Length);
// }

// method mpositive2(v:array<int>) returns (b:bool)
// ensures b == positive(v, v.Length)
// {
//     var i := 0; b := true;
//     while i < v.Length && b
//         invariant 0 <= i <= v.Length
//         invariant b == positive(v, i)
//         {
//             b := v[i] >= 0;
//             i := i + 1;
//         }

// }
