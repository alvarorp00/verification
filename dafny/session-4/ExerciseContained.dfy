


predicate strictSorted(s : seq<int>) {
	forall u, w :: 0 <= u < w < |s| ==> s[u] < s[w]
}


method mcontained(v:array<int>,w:array<int>,n:int,m:int) returns (b:bool)
//Specify and implement an O(m+n) algorithm that returns b
//v and w are strictly increasing ordered arrays
//b is true iff the first n elements of v are contained in the first m elements of w
requires strictSorted(v[..]) && strictSorted(w[..]) && 0 <= n <= v.Length && 0 <= m <= w.Length
ensures b == (forall i :: 0 <= i < n ==> exists j :: 0 <= j < m && v[i] == w[j])
{
	var i := 0;
	var j := 0;
	b := true;
	while (i < n && j < m && b)
		invariant 0 <= i <= n && 0 <= j <= m
		invariant b <==> (forall k :: 0 <= k < i ==> exists l :: 0 <= l < j && v[k] == w[l])
		decreases (if b then 1 else 0) + (n - i), (if b then 1 else 0) + (m - j)
	{
		if v[i] == w[j] {
			i := i + 1;
			j := j + 1;
		} else if v[i] > w[j] {
			j := j + 1;
		} else {
			b := false;
		}
	}
}