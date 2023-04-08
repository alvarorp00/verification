method mmaximum(v:array<int>) returns (i:int)
requires v.Length > 0
ensures 0 <= i < v.Length 
ensures forall k | 0 <= k < v.Length :: v[i] >= v[k]
{
    i := mfirstMaximum(v);
    // i := mlastMaximum(v);
}

method mfirstMaximum(v:array<int>) returns (i:int)
requires v.Length > 0
ensures 0 <= i < v.Length 
ensures forall k | 0 <= k < v.Length :: v[i] >= v[k]
ensures forall l | 0 <= l < i :: v[i] > v[l]
{
    var j := 0;
    i := 0;

    while (j < v.Length)
        decreases v.Length - j
        invariant 0 <= j <= v.Length
        invariant 0 <= i < v.Length
        invariant forall k | 0 <= k < j :: v[i] >= v[k]
        invariant forall l | 0 <= l < i :: v[i] > v[l]
    {
        if (v[j] > v[i]) {
            i := j;
        }
        j := j + 1;
    }
}

method mlastMaximum(v:array<int>) returns (i:int)
requires v.Length > 0
ensures 0 <= i < v.Length 
ensures forall k | 0 <= k < v.Length :: v[i] >= v[k]
ensures forall l | i < l < v.Length :: v[i] > v[l]
{
    var j := 0;
    i := 0;

    while (j < v.Length)
        decreases v.Length - j
        invariant 0 <= i < v.Length
        invariant 0 <= j <= v.Length
        invariant forall k | 0 <= k < j :: v[i] >= v[k]
        invariant forall l | i < l < j :: v[i] > v[l]
    {
        if (v[j] >= v[i]) {
            i := j;
        }
        j := j + 1;
    }
}


method mmaxvalue(v:array<int>) returns (m:int)
requires v.Length > 0
ensures m in v[..]
ensures forall k::0 <= k < v.Length ==> m >= v[k]
{
    var i := mmaximum(v);
    m := v[i];
}