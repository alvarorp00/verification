function min(v:array<int>, i:int) : int
  decreases i
  reads v
  requires 1 <= i <= v.Length
  ensures forall k :: 0 <= k < i ==> v[k] >= min(v,i)
{
  if (i==1) then
    v[0]
  else if (v[i-1] <= min(v,i-1)) then
    v[i-1]
  else
    min(v,i-1)
}

function countMin(v:array<int>, x:int, i:int):int
  decreases i
  reads v
  requires 0 <= i <= v.Length
  ensures !(x in v[0..i]) ==> countMin(v,x,i) == 0
{
  if (i==0) then
    0
  else if (v[i-1]==x) then
    1 + countMin(v,x,i-1)
  else
    countMin(v,x,i-1)
}

method mCountMin(v:array<int>) returns (c:int)
  requires v.Length > 0
  ensures c == countMin(v,min(v,v.Length),v.Length)
//Implement and verify an O(v.Length) algorithm
{
  var i:int := 1;
  var j:int := i-1;  // j is the index of the minimum element
  c := 1;
  while (i < v.Length)
    decreases v.Length - i
    invariant 1 <= i <= v.Length
    invariant 0 <= j < v.Length
    invariant v[j] == min(v,i)
    invariant c == countMin(v,v[j],i)
  {
    // Case 1: v[i] < v[j]
    if (v[i] < v[j]) {
      j := i;  // update index of minimum element
      c := 1;  // reset count
    }
    // Case 2: v[i] == v[j]
    else if (v[i] == v[j]) {
      c := c+1;  // increment count
    }
    i := i+1;
  }
}