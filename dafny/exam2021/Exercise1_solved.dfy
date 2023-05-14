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
requires 0 <= i < v.Length  /// Ojo puede quedar mejor v.Length -1
reads v
{
 	exists j :int :: i < j < v.Length && v[j] < v[i]
}
//2.Define a function countBiggerOnRight that given an array v and a valid index i
//on that array, returns the number of elements in segment [i..v.Length] that meet 
//the property oneBiggerOnRight previously defined

function countBiggerOnRight(v : array<int>, i:int): int
reads v
requires 0 <= i < v.Length
decreases v.Length - i
{
	if i == v.Length -1 then 0
	else
		if oneBiggerOnRight(v, i) then 1 + countBiggerOnRight(v, i+1)
		else countBiggerOnRight(v, i + 1)
}

//3.Using function countBiggerOnRight, specify a method
//that receives an array v of distinct elements and returns  
//the number of elements that have a smaller element on the right 


//4. Implement and verify an algorithm that solves this problem.
//A linear time algorithm will be better valued.  

predicate minimum(v : array<int>, i:int, m :int)
reads v
requires v.Length > 0
requires 0 <= i <= v.Length - 1
//requires exists k : int :: i <= k < v.Length && v[k] == m
{
	forall j | i <= j <= v.Length - 1 :: m <= v[j]
}

method mcountBiggerOnRight(v: array<int>) returns (c:int)
requires v.Length > 0
ensures c == countBiggerOnRight(v, 0)
{
	var i := v.Length - 1; //This one will loop the array from left to right
	var current_min := v[v.Length - 1];
	// assert minimum(v, i, current_min);
	c := 0;
	// assert c == countBiggerOnRight(v, i);
	while (i > 0)
		decreases i
		invariant 0 <= i < v.Length;
		invariant exists k : int | i <= k < v.Length :: v[k] == current_min;
		// invariant minimum(v, i, current_min);
		invariant k | i <= k < v.Length :: current_min <= v[k]
		//invariant forall j :: i <= j <= v.Length - 1 ==> current_min <= v[i]
		invariant c == countBiggerOnRight(v, i);
	{
		if v[i - 1] > current_min
		{
			// assert c == countBiggerOnRight(v, i);
			// assert v[i -1] > current_min;			
			c :=  c + 1;
			i := i - 1;
			
			// assert c == countBiggerOnRight(v, i);
		}
		else
		{
			current_min := v[i - 1];
			i := i - 1;
			// assert c == countBiggerOnRight(v, i + 1);
			// assert v[i] == current_min;

			//calc ==
			//{
			//	minimum(v, i, v[i]);
				// It is not getting this calculation path which is exactly the definition.
			//	forall k :: i <= k <= v.Length - 1 ==> v[i] <= v[k];
		//}
		
		//assume forall k :: i <= k <= v.Length - 1 ==> v[i] <= v[k];

		// assert minimum(v, i, v[i]);
		// assert forall k :: i <= k <= v.Length - 1 ==> v[i] <= v[k];
		// assert c == countBiggerOnRight(v, i);

		}
	}
}

