predicate positive(s:seq<int>)
{forall u :: 0 <= u < |s| ==> s[u] >= 0}

method mpositive(v:array<int>) returns (b:bool)
ensures b == positive(v[..])
{
    var i:int := 0;

    b := true;

    while (i < v.Length)
        decreases v.Length - i
        invariant 0 <= i <= v.Length
        invariant b == positive(v[..i])
        // invariant b == ( forall j | 0 <= j < i :: v[j] >= 0)
    {
        if (v[i] < 0) {
            b := false;
        }
        i := i + 1;
    }
}