

function Sum(v:array<int>,i:int,j:int):int
reads v
requires 0<=i<=j<=v.Length
decreases j
{
    if (i==j) then 0
    else Sum(v,i,j-1)+v[j-1]
}

predicate SumMaxToRight(v:array<int>,i:int,s:int)
reads v
requires 0 <= i < v.Length
{forall l, z {:induction l} | 0 <= l <= i && z == i+1 :: Sum(v,l,z) <= s}

method segMaxSum(v:array<int>,i:int) returns (s:int,k:int)
requires v.Length>0 && 0 <= i < v.Length
ensures 0 <= k <= i && s == Sum(v,k,i+1) &&  SumMaxToRight(v,i,s)
{
 s:=v[0];
 k:=0;
 var j:=0;
 while (j < i)
 decreases i-j
 invariant 0 <= j <= i
 invariant 0 <= k <= j && s == Sum(v,k,j+1)
 invariant SumMaxToRight(v,j,s)
 {  
    if (s+v[j+1]>v[j+1]) {s:=s+v[j+1];}
    else {k:=j+1;s:=v[j+1];}

     j:=j+1;
 }

} 


function Sum2(v:array<int>,i:int,j:int):int
reads v
requires 0<=i<=j<=v.Length
decreases j-i
{
    if (i==j) then 0
    else v[i]+Sum2(v,i+1,j)
}

//Now do the same but with a loop from right to left
predicate SumMaxToRight2(v:array<int>,j:int,i:int,s:int)//maximum sum stuck to the right
reads v
requires 0 <= j <= i < v.Length
{(forall l,z {:induction l}::j<=l<=i && z == i+1 ==> Sum2(v,l,z) <= s)}

method segSumaMaxima2(v:array<int>,i:int) returns (s:int,k:int)
requires v.Length>0 && 0 <= i < v.Length
ensures 0 <= k <= i && s == Sum2(v,k,i+1) && SumMaxToRight2(v,0,i,s)
{
    var j := i;
    s := v[i];
    k := i;
    var sum := v[i];  // sum of all elements from v[i] to v[j]
    while (j > 0)
        decreases j
        invariant 0 <= j <= k <= i
        invariant sum == Sum2(v,j,i+1)
        invariant s == Sum2(v,k,i+1)
        invariant SumMaxToRight2(v,j,i,s)
    {
        sum := sum + v[j-1];
        if (sum >= s) {
            s := sum;
            k := j-1;
        }
        j := j-1;
    }
}