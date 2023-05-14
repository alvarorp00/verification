//Final Exam, June 10th, 2021
//We want to specify and verify a method that, given an array of distinct elements, 
//computes the number of elements that have a smaller element on their right. 
//Example: given the array elements [2,6,8,4,9,5,10], the method must return 3
//because elements 9, 8 and 6 have smaller elements on their right.

//Your tasks are:

//1.Define a predicate oneBiggerOnRight that given an array v and a valid index i
//on that array, determines if there exists an element on i's right that is smaller 
//than v[i]

predicate oneBiggerOnRight(v: array<int>, i:int)
reads v
requires v.Length > 0
requires 0 <= i < v.Length
{
    (exists j | i < j < v.Length :: v[j] < v[i])
}

//2.Define a function countBiggerOnRight that given an array v and a valid index i
//on that array, returns the number of elements in segment [i..v.Length] that meet 
//the property oneBiggerOnRight previously defined

function countBiggerOnRight(v : array<int>, i:int): int
reads v
requires v.Length > 0
requires 0 <= i < v.Length
decreases v.Length - i
{
    if i == v.Length - 1 then
        0
    else
        if oneBiggerOnRight(v, i) then
            1 + countBiggerOnRight(v, i+1)
        else
            countBiggerOnRight(v, i+1)
}

//3.Using function countBiggerOnRight, specify a method
//that receives an array v of distinct elements and returns  
//the number of elements that have a smaller element on the right 

predicate distinct(v:array<int>)
reads v
requires v.Length > 0
{
    forall i:int, j:int | 0 <= i < j < v.Length :: v[i] != v[j]
}

method mCountBiggerOnRight(v: array<int>) returns (c:int)
requires v.Length > 0
requires distinct(v)
ensures c == countBiggerOnRight(v, 0)
{
    var i:int := v.Length - 1;
    var m:int := v[i];
    
    c := 0;

    while (i > 0)
        decreases i
        invariant 0 <= i < v.Length
        invariant exists j | i <= j < v.Length :: m == v[j]  // It's important to demonstrate that this element (m, minimum) exists in the array
        invariant forall k | i <= k < v.Length :: m <= v[k]  // global min
        invariant c == countBiggerOnRight(v, i)
    {
        if (v[i-1] > m) {
            c := c + 1;
        } else {
            m := v[i-1];
        }
        i := i - 1;
    }
}

//4. Implement and verify an algorithm that solves this problem.
//A linear time algorithm will be better valued.  


