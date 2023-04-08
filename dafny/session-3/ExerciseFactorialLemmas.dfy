include "exp.dfy"

function factorial(n:int):int
    decreases n
	requires n >= 0
{
if n == 0 then 1 else n*factorial(n-1)
}

lemma {:induction n} {:timeLimitMultiplier 1} factorial_ineqLemma(n:int)
	decreases n
	requires n >= 2
	ensures factorial(n-1) < factorial(n)
{
	if (n==2) {  // BASE CASE
		assert factorial(1) == 1;
		assert factorial(2) == 2;
		assert factorial(1) < factorial(2);
	}
	else {
		factorial_ineqLemma(n-1);
		calc {
			factorial(n-1) < factorial(n);
			==
			{ assert factorial(n) == factorial(n-1) * n; }
			factorial(n-1) < factorial(n-1) * (n);
			==
			{ assert factorial(n-1) == factorial(n-1); }
			{ assert n > 2; }
			1 < n;
		}
		assert factorial(n-1) < factorial(n);
	}
}

lemma  factorial_Lemma(n:int)
    decreases n
	requires n >= 7
	ensures exp(3,n) < factorial(n)
{
	// Base case
	if (n == 7) {
		assert exp(3,7) < factorial(7);
	}
	else {
		assert n > 7;
		factorial_Lemma(n-1); // induction hypothesis
		calc {
			exp(3,n-1) < factorial(n-1);
			==
			{ assert exp(3,n) == exp(3,n-1) * 3; }
			exp(3,n-1) * 3 < factorial(n-1) * 3;
			==
			{ assert 3 < 7; }
			{ assert 7 < n; }
			exp(3,n-1) * 3 < factorial(n-1) * 3 && 3 < n;
			==
			{ assert exp(3,n-1) < factorial(n-1);}
			exp(3,n) < factorial(n-1) * 3 && 3 < n;
			==
			exp(3,n) < factorial(n-1) * 3;
			==
			{ factorial_ineqLemma(n-1); }
			exp(3,n) < factorial(n) * 3;
		}
		assert exp(3,n) < factorial(n);
	}
}

lemma {:induction n} {:timeLimitMultiplier 10} fact_Lemma(n:int)
    decreases n
	requires n >= 1
	ensures factorial(n) <= exp(n,n)
{
	// Base case
	if (n == 1) {
		calc {
			factorial(1) <= exp(1,1);
			==
			{ assert 1 <= 1; }
			{ assert exp(1,1) == 1; }
			1 <= 1;
		}
		assert factorial(1) <= exp(1,1);
	}
	else {
		assert n > 1;
		fact_Lemma(n-1);  // induction hypothesis  --> factorial(n-1) <= exp(n-1,n-1)
		calc {
			factorial(n-1) <= exp(n-1,n-1);
			==
			{ assert factorial(n-1) * n == factorial(n); }
			{ assert factorial(n-1) * n <= exp(n-1,n-1) * n; }
			factorial(n) <= exp(n-1,n-1) * n;
			==
			{ assert exp(n-1, n-1) * (n-1) == exp(n-1, n); }
			{ assert (n-1) <= n; }
			factorial(n) <= exp(n-1,n-1) * n && (n-1) <= n;
			==
			{ assert (n-1) <= n; }
			{ assert factorial(n) <= exp(n-1,n-1) * n; }
			factorial(n) <= exp(n-1,n-1) * n;  // we want to say fac(n) <= exp(n,n-1) * n
			==
			{ assert n-1 <= n; }
			{ exp_ineqLemmaExp(n); }
			{ assert exp(n,n-1) <= exp(n,n); }
			{ exp_ineqLemmaBase2(n-1, n, n-1); }
			{ assert exp(n-1,n-1) <= exp(n,n-1); }
			factorial(n) <= exp(n,n-1) * n;
			==
			{ assert exp(n,n-1) * n == exp(n,n); }
			factorial(n) <= exp(n,n);
		}
		assert factorial(n) <= exp(n,n);
	}
}