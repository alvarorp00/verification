method mmaximum(v:array<int>) returns (i:int) 
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]

//Algorithm 1: From left to right return the first
//Algorithm 2: From right to left return the last

method mfirstMaximum(v:array<int>) returns (i:int)
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
ensures forall l:: 0<=l<i ==> v[i]>v[l]
//Algorithm: from left to right

method mlastMaximum(v:array<int>) returns (i:int)
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
ensures forall l:: i<l<v.Length ==> v[i]>v[l]

//Algorithm : from left to right
//Algorithm : from right to left

method mmaxvalue(v:array<int>) returns (m:int)
requires v.Length > 0
ensures m in v[..]
ensures forall k | 0 <= k < v.Length :: m >= v[k]
{
    var i:int := 1;
    m := v[0];

    while (i < v.Length)
        decreases v.Length - i
        invariant 1 <= i <= v.Length
        invariant m in v[..i]
        invariant forall k | 0 <= k < i :: m >= v[k]
    {
        if (v[i] > m) {
            m := v[i];
        }
        i := i + 1;
    }
}