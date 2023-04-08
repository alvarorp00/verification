predicate sorted_seg(a:seq<int>, i:int, j:int) //i and j included
requires 0 <= i <= j+1 <= |a|
//reads a
{
    forall l, k :: i <= l <= k <= j ==> a[l] <= a[k]
}

// Auxiliary Predicates

predicate allEqual(a:seq<int>, i:int, j:int)
requires 0 <= i <= j+1 <= |a|
//reads a
{
    forall l, k | i <= l <= k <= j :: a[l] == a[k]
}


// Auxiliary Methods

// Puts the first occurrence of e in the first position of the array
method swapEFirst(v:array<int>, c:int, f:int, e:int)
modifies v
requires 0 <= c <= f <= v.Length-1 //There is at least one element
requires e in v[c..f+1]
ensures v[..c] == old(v[..c])
ensures v[f+1..] == old(v[f+1..])
ensures multiset(v[c..f+1]) == multiset(old(v[c..f+1]))
ensures v[c] == e
{
    var k:int := c;
    while (k <= f && v[c] != e)
        decreases f - k
        invariant c <= k <= f + 1
        invariant e in v[k..f+1]
        invariant v[..c] == old(v[..c])
        invariant v[f+1..] == old(v[f+1..])
        invariant multiset(v[c..f+1]) == multiset(old(v[c..f+1]))
    {
        if (v[k] == e) {
            v[c], v[k] := v[k], v[c];
            break;
        }
        k := k + 1;
    }
}

// To implement: mpartition2
// To verify: quicksort


// This method puts all elements smaller than e in the left part of the array
// and all elements larger than e in the right part of the array
// and returns the indices of the first and last element equal to e
method mpartition2(v:array<int>, c:int, f:int, e:int) returns (p:int,q:int)
modifies v
requires 0 <= c <= f <= v.Length-1 //There is at least one element
requires e in v[c..f+1] 
ensures c <= p <= q <= f
ensures (forall u | c <= u < p :: v[u] < e)   && 
        (forall u | p <= u <= q :: v[u] == e) &&
        (forall w | q+1 <= w <= f :: v[w] > e)
ensures multiset(v[c..f+1]) == multiset(old(v[c..f+1]))
ensures v[..c] == old(v[..c])
ensures v[f+1..] == old(v[f+1..])
ensures allEqual(v[..], p, q) && v[p] == e  // Added by me
//Implement and verify
{
    var k:int;

    p := c;
    q := f;
    
    k := f;

    swapEFirst(v, c, f, e);
    assert v[p] == e;

    k := f;
    q := c;

    var a1:int, a2:int;

    while (k > q)
        decreases k - q
        invariant c <= p <= q <= k + 1 <= f + 1
        invariant c <= p <= q <= f
        invariant forall u | c <= u < p :: v[u] < e
        invariant forall u | p <= u <= q :: v[u] == e
        invariant forall u | k < u <= f :: v[u] > e
        invariant v[..c] == old(v[..c])
        invariant v[f+1..] == old(v[f+1..])
        invariant multiset(v[c..f+1]) == multiset(old(v[c..f+1]))
    {
        if (v[k] < e) {
            q := q + 1;
            a1 := v[p];
            v[p] := v[k];
            v[k] := v[q];
            v[q] := a1;
            p := p + 1;
        } else if (v[k] > e) {
            k := k - 1;
        } else {  // v[k] == e
            q := q + 1;
            v[q], v[k] := v[k], v[q];
        }
    }
}

// Auxiliary lemmas

lemma multisetPreservesSmaller (a:seq<int>, b:seq<int>, c:int, f:int, x:int)
requires |a|==|b| && 0 <= c <= f + 1 <= |b| 
requires (forall j | c <= j <= f :: a[j] < x)
requires multiset(a[c..f+1]) == multiset(b[c..f+1])
ensures (forall j | c <= j <= f :: b[j] < x)
{
       assert forall j | c <= j <= f :: b[j] in multiset(b[c..f+1]);
}



lemma multisetPreservesGreater (a:seq<int>, b:seq<int>, c:int, f:int, x:int)
requires |a|==|b| && 0 <= c <= f + 1 <= |b| 
requires (forall j | c <= j <= f :: a[j] > x)
requires multiset(a[c..f+1]) == multiset(b[c..f+1])
ensures (forall j | c <= j <= f :: b[j] > x)
{
       assert forall j | c <= j <= f :: b[j] in multiset(b[c..f+1]);
}



lemma seqSplit(s:seq<int>, c:int, p:int, f:int)//f excluded
requires 0<=c<=p<=f+1<=|s|
ensures multiset(s[c..f+1])==multiset(s[c..p])+multiset(s[p..f+1])
{
       assert s[c..f+1] == s[c..p] + s[p..f+1];
}


// Verify quicksort
method {:timeLimitMultiplier 2} quicksort (a:array<int>, c:int, f:int)//c and f included
modifies a 
requires 0 <= c <= f+1 <= a.Length //when c==f+1 empty sequence
ensures sorted_seg(a[..],c,f) 
ensures multiset(a[c..f+1]) == old(multiset(a[c..f+1]))
ensures a[..c]==old(a[..c])
ensures a[f+1..]==old(a[f+1..])
decreases f-c
{
    if (c < f) {
        var p,q := mpartition2(a,c,f,a[c]);
            ghost var a1 := a[..] ;
            assert (forall u | c <= u < p :: a1[u] <= a1[p]);
            assert (forall u | p <= u <= q :: a1[u] == a1[p]);
            assert (forall w | q+1 <= w <= f :: a1[w] >= a1[p]);
            assert sorted_seg(a[..],p,q);
            assert sorted_seg(a1[..],p,q);
            
        quicksort(a,c,p-1);
        assert sorted_seg(a[..],c,p-1);
            ghost var a2 := a[..] ;
            assert multiset(a[c..p]) == multiset(a1[c..p]);
            assert a[p..f+1] == a1[p..f+1];
            seqSplit(a[..],c,p,f);
            seqSplit(a1,c,p,f);
            assert multiset(a[c..f+1]) == multiset(a1[c..f+1]);
            assert multiset(a[c..p]) == multiset(a[c..p]);
            multisetPreservesSmaller(a1,a[..],c,p-1,a[p]);
            assert sorted_seg(a2,c,p-1);
            
            
        quicksort(a,q+1,f);
        assert sorted_seg(a[..],q+1,f);     
            ghost var a3 := a[..];
            assert multiset(a[q+1..f+1]) == multiset(a2[q+1..f+1]);
            assert a[c..q+1] == a2[c..q+1];
            seqSplit(a[..],c,q+1,f);
            seqSplit(a2,c,q+1,f);
            multisetPreservesGreater(a2,a[..],q+1,f,a[p]);
            assert sorted_seg(a[..], q+1, f);

        assert a[..c] == old(a[..c]);
        assert a[f+1..] == old(a[f+1..]);
    }
}

 

