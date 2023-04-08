
 predicate isPeek(v:array<int>,i:int)
 reads v
 requires 0 <= i < v.Length
 {
    forall k :: 0 <= k < i ==> v[i] >= v[k]
}

 function peekSum(v:array<int>,i:int):int
 decreases i 
 reads v
 requires 0 <= i <= v.Length
 {
  if (i==0) then
    0
  else if isPeek(v,i-1) then
    v[i-1]+peekSum(v,i-1)
  else
    peekSum(v,i-1)
 }

 
 method mPeekSum(v:array<int>) returns (sum:int)
 requires v.Length > 0
 ensures sum == peekSum(v,v.Length)
 //Implement and verify an O(v.Length) algorithm to solve this problem
 {
    var i:int:=1;
    var j:int:=0;  // p is the index of the last peek
    sum := v[i-1];  // isPeek(v,0) is always true
    while (i < v.Length)
      decreases v.Length - i
      invariant 1 <= i <= v.Length
      invariant 0 <= j < v.Length
      invariant j < i  // at each iteration j is always less than i (i.e. j is always a peek)
      invariant forall k | 0 <= k < i :: v[j] >= v[k]
      invariant isPeek(v,j)
      invariant sum == peekSum(v,i)
    {
        if (v[i] >= v[j]) {
            sum := sum + v[i];
            j := i;
        }
        // else sum := sum;
        i:=i+1;
    }
 }