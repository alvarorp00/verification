//Final Exam, June 10th, 2021
//We want to specify and verify a method that, given an array of distinct elements, 
//computes the number of elements that have a smaller element on their right. 
//Example: given the array elements [2,6,8,4,9,5,10], the method must return 3
//because elements 9, 8 and 6 have smaller elements on their right.

//Your tasks are:

//1.Define a predicate oneBiggerOnRight that given an array v and a valid index i
//on that array, determines if there exists an element on i's right that is smaller 
//than v[i]

predicate oneBiggerOnRight(a: array<int>, i: int)
reads a
requires 0 <= i < a.Length
{
	exists k:nat :: i < k < a.Length && a[k] < a[i]
}


//2.Define a function countBiggerOnRight that given an array v and a valid index i
//on that array, returns the number of elements in segment [i..v.Length] that meet 
//the property oneBiggerOnRight previously defined
function countBiggerOnRight(a: array<int>, i: int): (res:int)
decreases a.Length - i
reads a
requires 0 <= i < a.Length
{
	if i == a.Length - 1 then 0
	else if oneBiggerOnRight(a, i) then 1 + countBiggerOnRight(a, i+1)
	else countBiggerOnRight(a, i + 1)
}



//3.Using function countBiggerOnRight, specify a method
//that receives an array v of distinct elements and returns  
//the number of elements that have a smaller element on the right 
method biggerOnRight(a: array<int>) returns (res: int)
requires a.Length > 0
ensures res == countBiggerOnRight(a, 0)
{
	var min :int := a[a.Length - 1];
	var idx: int := a.Length - 1;
	res:=0;
	while(idx > 0)
	decreases idx
	invariant 0 <= idx < a.Length
	invariant forall k: nat :: idx <= k < a.Length ==> min <= a[k]
	invariant exists k :: idx <= k < a.Length && a[k] == min
	invariant res == countBiggerOnRight(a, idx)

	{
		if(a[idx-1] > min){res := res + 1;}
		else {min := a[idx - 1];}
		idx := idx - 1;
	}
}



//4. Implement and verify an algorithm that solves this problem.
//A linear time algorithm will be better valued.  
