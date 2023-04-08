include "ExerciseExp.dfy"

function factorial(n:int):int
    decreases n
	requires n >= 0
{
if n == 0 then 1 else n*factorial(n-1)
}

lemma {:induction n} factorial_Lemma(n:int)  // TODO 
    decreases n
	requires n >= 7
	ensures exp(3,n) < factorial(n)
{
	if n == 7  // base case
	{
		assert exp(3, 7) < factorial(7);
	}
	else  // inductive case
	{
		fact_Lemma(n-1);
		
		assert exp(3, n-1) < factorial(n-1);
	}
}

lemma fact_Lemma(n:int)
    decreases n
	requires n >= 1
	ensures factorial(n) <= exp(n,n)