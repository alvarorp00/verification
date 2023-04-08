//Author: Clara Segura
include "Stack.dfy"
include "Queue.dfy"
include "List.dfy"
include "Utils.dfy"


lemma compseqs<A>(s1:seq<A>,s2:seq<A>,x:A,y:A)
requires [x]+s1==[y]+s2 && |s1|==|s2|
ensures x==y && s1==s2
{ assert x!=y ==> ([x]+s1)[0] == x != y == ([y]+s2)[0];
  assert forall i::0<=i<=|s1| ==> ([x]+s1)[i]==([y]+s2)[i];
  assert  forall i::0<=i<|s1| ==> s1[i]==([x]+s1)[i+1]==([y]+s2)[i+1]==s2[i];
  
}


method FillStack(l:List<int>,s:Stack<int>)
modifies l,l.Repr(), s, s.Repr()
requires allocated(l.Repr())
requires allocated(s.Repr())
ensures fresh(l.Repr() - old(l.Repr()))
ensures allocated(l.Repr())
ensures fresh(s.Repr() - old(s.Repr()))
ensures allocated(s.Repr())

requires l.Valid() && s.Valid()
requires {s}+s.Repr() !! {l}+l.Repr()  // Stack & List are disjoint
requires s.Empty?()

ensures l.Valid() && old(l.Model())==l.Model()
ensures s.Valid() && s.Model()==Seq.Rev(l.Model())
ensures {s}+s.Repr()!! {l}+l.Repr()

ensures l.Iterators() >= old(l.Iterators())

method FillQueue(l:List<int>, q:Queue<int>)
modifies l,l.Repr(),q, q.Repr()
requires allocated(l.Repr())
requires allocated(q.Repr())
ensures fresh(l.Repr() - old(l.Repr()))
ensures allocated(l.Repr())
ensures fresh(q.Repr() - old(q.Repr()))
ensures allocated(q.Repr())

requires l.Valid() && q.Valid()
requires {q}+q.Repr()!! {l}+l.Repr()
requires q.Empty?()

ensures l.Valid() && old(l.Model())==l.Model()
ensures q.Valid() && q.Model()==l.Model()
ensures {q}+q.Repr()!! {l}+l.Repr()

ensures l.Iterators() >= old(l.Iterators())


// Optional
method Palindrome(l:List<int>,s:Stack<int>,q:Queue<int>) returns (b:bool)
modifies l,l.Repr(), s, s.Repr(), q, q.Repr()
requires allocated(l.Repr())
requires allocated(s.Repr())
requires allocated(q.Repr())
ensures fresh(l.Repr() - old(l.Repr()))
ensures allocated(l.Repr())
ensures fresh(s.Repr() - old(s.Repr()))
ensures allocated(s.Repr())
ensures fresh(q.Repr() - old(q.Repr()))
ensures allocated(q.Repr())


requires l.Valid() && s.Valid() && q.Valid()
requires {l}+l.Repr()!! {s}+s.Repr()
requires {l}+l.Repr()!! {q}+q.Repr()
requires {q}+q.Repr()!! {s}+s.Repr()
requires s.Empty?() && q.Empty?()

ensures l.Valid() 
ensures s.Valid() && q.Valid()

ensures l.Iterators() >= old(l.Iterators())


//ensures: write the properties concerning the model and result b
//l is unchanged and b is true iff l is palindrome

{
  FillStack(l,s); 
  FillQueue(l,q); 
  //loop to check that l is palindrome using s and q

}

