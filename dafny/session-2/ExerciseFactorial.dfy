include "ExerciseExp.dfy"

function factorial(n:int):int
    decreases n
	requires n >= 0
{
if n == 0 then 1 else n*factorial(n-1)
}

lemma factorialLowerBound(n:int)
requires n > 1
ensures factorial(n) > 0
{
	if n == 2 {
		
	}
}

lemma expLowerBound(x:int, n:int)
requires x > 0
requires n >= 0
ensures exp(x,n) > 0
{}

lemma factorial_LemmaAux1 (n1:int, n2:int, n3:int, n4:int)
requires n1 > 0 && n2 > 0
requires n1 <= n3
requires n2 <= n4
ensures n1 * n2 <= n3 * n4
{}

lemma factorial_LemmaAux2 (n1:int, n2:int, n3:int, n4:int, n5:int, n6:int)
requires n1 > 0 && n2 > 0
requires n1 < n3
requires n2 < n4
requires n5 == n1 * n2
requires n6 == n3 * n4
ensures n1 * n2 <= n3 * n4
ensures n5 <= n6
{}

lemma {:induction n} factorial_Lemma(n:int)
decreases n
requires n >= 7
ensures exp(3,n) < factorial(n)
{
	if (n == 7) {
		assert exp(3,n) < factorial(n);
	} else {
		factorial_Lemma(n-1);
		assert n > 7;
		calc == {
			exp(3,n-1) < factorial(n-1);
			{ assert 3 < n; }
			{ assert exp(3,n-1) < factorial(n-1); }
			{ expLowerBound(3, n-1); }
			{ factorial_LemmaAux1(3, exp(3,n-1), n, factorial(n-1)); }
			{ assert 3 * exp(3,n-1) < n * factorial(n-1); }
			{ assert 3 * exp(3,n-1) == exp(3,n); }
			exp(3,n) < n * factorial(n-1); 
		}
	}
}

lemma expLessThan_Lemma1(x:int, n:int)
requires x > 0
requires n >= 1
ensures exp(x,n) <= exp(x,n+1)
{}

lemma expLessThan_Lemma2(x1:int, x2:int, n:int)
decreases n
requires x1 > 0 && x2 > 0
requires x1 <= x2
requires n >= 1
ensures exp(x1,n) <= exp(x2,n)
{
	if (n == 1) {
		assert x1 <= x2;
	} else {
		expLessThan_Lemma2(x1,x2,n-1);
		calc == {
			exp(x1,n-1) <= exp(x2,n-1);
			// { assert x1 <= x2; }
			{ expLowerBound(x1,n-1); }
			{ factorial_LemmaAux1(x1, exp(x1,n-1), x2, exp(x2,n-1)); }
			x1 * exp(x1,n-1) <= x2 * exp(x2,n-1);
			// { assert exp(x1,n) == x1 * exp(x1,n-1); }
			// { assert exp(x2,n) == x2 * exp(x2,n-1); }
			exp(x1,n) <= exp(x2,n);
		}
	}
}

lemma fact_Lemma(n:int)
decreases n
requires n >= 1
ensures factorial(n) <= exp(n,n)
{
	if (n == 1) {
		assert factorial(n) <= exp(n,n);
	} else {
		assert n > 1;
		fact_Lemma(n-1);
		calc == {
			factorial(n-1) <= exp(n-1,n-1);
			// { assert n * factorial(n-1) == factorial(n); }
			// { assert n - 1 <= n; }
			{ expLessThan_Lemma2(n-1,n,n-1); }
			// { assert exp(n-1,n-1) <= exp(n,n-1); }
			factorial(n-1) <= exp(n,n-1);
		}
	}
}