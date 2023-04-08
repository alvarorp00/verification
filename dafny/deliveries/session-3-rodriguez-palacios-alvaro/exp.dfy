function exp(x:int, e:int):int
    decreases e
	requires e >= 0
{
if e == 0 then 1 else x*exp(x,e-1)
}

lemma {:induction n}  exp3_Lemma(n:int) 
    decreases n
    requires n >= 1
	ensures (exp(3,n)-1)%2 == 0
{}
    
 
lemma {:induction n} mult8_Lemma(n:int)
    decreases n
	requires n >= 1
	ensures (exp(3,2*n) - 1)%8 == 0
{
    if n == 1
    {
        assert exp(3, 2) - 1 == 8;
    }
    else
    {
        mult8_Lemma(n-1); // induction hyphotesis
        assert (exp(3, 2*(n-1)) - 1) % 8 == 0;
    }
}

lemma exp_min1(n:int,m:int)
	decreases m
	requires n >= 1
	requires m >= 0
	ensures exp(n,m) >= 1
{
	if (m == 0) {
		assert exp(n,0) == 1;
	}
	else {
		assert m > 0;
		exp_min1(n,m-1);
		calc {
			exp(n,m-1) >= 1;
			==
			{ assert exp(n,m) == exp(n,m-1) * n; }
			exp(n,m-1) * n >= 1 * n;
			==
			{ assert exp(n,m-1) >= 1; }
			exp(n,m) >= 1 * n;
			==
			{ assert n >= 1; }
			exp(n,m) >= n;
		}
		assert exp(n,m) >= 1;
	}
}

lemma {:induction n} {:timeLimitMultiplier 1} exp_ineqLemmaExp(n:int)
	decreases n
	requires n >= 1
	ensures exp(n,n-1) <= exp(n,n)
{
	exp_min1(n,n-1);
	if (n == 1) {
		assert exp(1,0) == 1;
		assert exp(1,1) == 1;
		assert exp(1,0) == exp(1,1);
	}
	else if (n == 2) {
		assert exp(2,1) == 2;
		assert exp(2,2) == 4;
		assert exp(2,1) < exp(2,2);
	}
	else {
		assert n > 2;
		exp_ineqLemmaExp(n-1);
		calc {
			exp(n,n-1) < exp(n,n);
			==
			{ assert exp(n,n) == exp(n,n-1) * n; }
			exp(n,n-1) * n < exp(n,n) * n;
			==
			{ assert exp(n,n-1) * n == exp(n,n); }
			exp(n,n) < exp(n,n) * n;
			==
			{ assert exp(n,n) == exp(n,n); }
			{ assert n > 1; }
			exp(n,n) < exp(n,n) * n && n > 1;
			==
			{ assert n > 1; }
			{ assert exp(n,n) < exp(n,n) * n; }
			1 < n;
		}
		assert exp(n,n-1) <= exp(n,n);
	}
}

lemma exp_mult(n:int, m:int, n1:int, n2:int)
	requires n >= 1;
	requires m >= 1;
	requires n1 >= 1;
	requires n2 >= 1;
	requires n1 <= n2;
	ensures exp(n,m) * n1 <= exp(n,m) * n2;
{}

lemma {:induction m} {:timeLimitMultiplier 20} exp_ineqLemmaBase(n1:int, n2:int, m:int)
	decreases m
	requires n1 >= 1
	requires n2 >= 1
	requires m >= 1
	requires n1 <= n2
	ensures exp(n1,m-1) <= exp(n2,m)
{
	if (m == 1) {
		assert exp(n1, 0) == 1;
		assert exp(n2, 1) == n2;
		assert n2 >= 1;
		assert exp(n1, 0) <= exp(n2, 1);
	}
	else if (m == 2) {
		assert exp(n1, 1) == n1;
		assert exp(n2, 2) == n2 * n2;
		assert n1 <= n2 * n2;
		assert exp(n1, 1) <= exp(n2, 2);
	}
	else {
		assert m > 2;
		exp_ineqLemmaBase(n1, n2, m-1);
		calc {
			exp(n1,m-2) <= exp(n2,m-1);
			==
			{ assert exp(n1, m-1) == exp(n1, m-2) * n1; }
			exp(n1,m-2) * n1 <= exp(n2,m-1) * n1;
			==
			exp(n1,m-1) <= exp(n2,m-1) * n1;
			==
			{ assert n1 >= 1; }
			{ assert n1 <= n2; }
			{ exp_mult(n1, m-1, n1, n2); }
			exp(n1,m-1) <= exp(n2,m-1) * n2;
		}
		assert exp(n1,m-1) <= exp(n2,m);
	}
}

lemma {:induction m} {:timeLimitMultiplier 2} exp_ineqLemmaBase2(n1:int, n2:int, m:int)
	decreases m
	requires n1 >= 1
	requires n2 >= 1
	requires m >= 1
	requires n1 <= n2
	ensures exp(n1,m) <= exp(n2,m)
{
	if (m == 1) {
		assert exp(n1, 1) == n1;
		assert exp(n2, 1) == n2;
		assert n1 <= n2;
		assert exp(n1, 1) <= exp(n2, 1);
	}
	else {
		assert m > 1;
		exp_ineqLemmaBase2(n1, n2, m-1);
		calc {
			exp(n1,m-1) <= exp(n2,m-1);
			==
			{ assert exp(n1, m) == exp(n1, m-1) * n1; }
			exp(n1,m-1) * n1 <= exp(n2,m-1) * n1;
			==
			exp(n1,m) <= exp(n2,m-1) * n1;
			==
			{ assert n1 >= 1; }
			{ assert n1 <= n2; }
			{ exp_mult(n1, m-1, n1, n2); }
			exp(n1,m) <= exp(n2,m-1) * n2;
		}
		assert exp(n1,m) <= exp(n2,m);
	}
}