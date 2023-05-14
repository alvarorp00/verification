/*
    Final Exam, June 10th, 2021
    Exercise on algebraic datatypes

    You are given the definitions below and you are asked to represent
    sets of integers as sorted lists of integers without duplicates

    You are also given the specifications of the emptySet, singleton, union and 
    intersection functions. Your task consists of implementing and verifying 
    them. The cost of union and intersection should in O(n1+n2), being n1 and n2
    the cardinals of the sets received as arguments. 
*/

datatype List<T> = Nil | Cons(head:T, tail:List<T>)

predicate noDup <T> (l:List<T>)
{
    match l
        case Nil        => true
        case Cons(x,xs) => x !in elems(xs) && noDup(xs)
}

predicate sorted (l:List<int>)
{
    match l 
       case Nil         => true
       case Cons(x, xs) => 
            match xs 
               case Nil         => true
               case Cons(y, ys) => x <= y && sorted(xs)
}

function elems <T> (l:List<T>) : set<T>
{
    match l
       case Nil         => {}
       case Cons(x, xs) => {x} + elems(xs)
}

///////////////////////////////////////////////////////////////

function method emptySet() : (res:List<int>)
ensures elems(res) == {}
{
	Nil
}

function method singleton(x:int): (res:List<int>)
ensures elems(res) == {x} && noDup(res)
{
	Cons(x, Nil)
}

function method union (l1:List<int>,l2:List<int>): (res: List<int>)
requires sorted(l1) && sorted(l2) && noDup(l1) && noDup(l2)
ensures sorted(res) && noDup(res)
ensures elems(res) == elems(l1) + elems (l2)
{
	match l1
		case Nil =>
			l2
		case Cons(h1, tail1) =>
			match l2
				case Nil => l1
				case Cons(h2, tail2) =>

					if h1 < h2 then
						var resAux := union(tail1, l2);

						assert sorted(tail1) && noDup(tail1);
						assert h1 !in elems(tail1);
						assert sorted(l2) && h1 < h2;
						// if h1 < h2 ==> h1 cannot be in l2 because is sorted...

						//headIsSmallest(l1);
						//assert h1 < h2;
						//headIsSmallest(l2);
						//assert smallest(l2, h2);
						//SmallestTransitive(l1, l2, h1);
						//assert smallest(l2, h1);

						notInSortedIfSmaller(l2, h1);
						
						assert h1 !in elems(l2); 
						assert h1 !in elems(resAux);
						
						Cons(h1, resAux)

					else
						if h1 == h2 then
							var resAux := union(tail1, tail2);
							assert noDup(resAux);
							Cons(h1, resAux)
						else // h1 > h2//
							var resAux := union(l1, tail2);
							//assert sorted(tail1) && noDup(tail1);
							//assert h1 !in elems(tail1);
							//assert sorted(l1) && h1 > h2;

							notInSortedIfSmaller(l1, h2);
							assert h2 !in elems(l1); 
							assert h2 !in elems(resAux);
							Cons(h2, resAux)
}



function method inters (l1:List<int>,l2:List<int>): (res: List<int>)
requires sorted(l1) && sorted(l2) && noDup(l1) && noDup(l2)
ensures sorted(res) && noDup(res)
ensures elems(res) == elems(l1) * elems (l2)
{
	match l1
		case Nil => emptySet()
		case Cons(h1, t1) =>
			match l2
				case Nil => emptySet()
				case Cons(h2, t2) =>
					if h1 == h2
					then var resAux := inters(t1, t2);
					assert sorted(l1);
					assert sorted(l2);
					HeadNotInTail(l1);
					HeadNotInTail(l2);
					assert sorted(t1) && sorted(t2);
					// I am not able to join this two...
					assert sorted(Cons(h1, resAux));
					Cons(h1, resAux)
					else
						if h1 < h2 then
						assert sorted(t1);
						assert sorted(t2);
						inters(t1, l2)
						else // h1 > h2 //
						assert sorted(t1);
						assert sorted(t2);
						inters(l1, t2)
}


/// A lot of lemmas I tried. 

lemma headIsSmallest(l1:List<int>)
requires sorted(l1);
requires l1 != Nil;
ensures smallest(l1, l1.head);
{
	match l1
		case Nil =>
		case Cons(x, Nil) =>
			assert smallest(l1, l1.head);
		case Cons(head, tail) =>
			headIsSmallest(tail);
			assert smallest(tail, tail.head);
			assert head <= tail.head;
			SmallTransit(tail, head);
			assert smallest(tail, head);
}

predicate smallest(l1:List<int>, x:int)
{
	match l1
		case Nil => true
		case Cons(head, tail) => x <= head && smallest(tail, x)
}

lemma SmallTransit(l1:List<int>, x:int)
requires l1 != Nil;
requires sorted(l1);
requires x <= l1.head;
requires smallest(l1, l1.head);
ensures  smallest(l1, x);

lemma SmallestTransitive(l1:List<int>, l2:List<int>, x :int)
requires smallest(l1, x);
requires l1 != Nil && l2 != Nil;
requires l1.head <= l2.head;
requires sorted(l1) && sorted(l2);
ensures smallest(l2, x);
{}


lemma notInSortedIfSmaller(l:List<int>, x :int)
requires sorted(l) && l != Nil;
requires x < l.head;
ensures x !in elems(l.tail);
{
	match l
		case Nil =>
		case Cons(head, Nil) =>
			assert x !in elems(Nil);
		case Cons(head, tail) => 
			assert sorted(tail);
}

lemma HeadNotInTail(l:List<int>)
requires noDup(l);
requires l != Nil;
ensures l.head !in elems(l.tail); 
