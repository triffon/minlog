$Id: ratsds.txt 2479 2011-05-18 06:46:37Z schwicht $
readme file for git/minlog/examples/analysis/ratsds.scm
18.05.2011
Kenji Miyamoto
miyamoto@mathematik.uni-muenchen.de

This is a README file for the case study ratsds.scm of Minlog.  It
describes the theory in the first section, and the formal proof on
Minlog in the second section.  In this case study, we extract from a
proof a program which transforms a rational number in [-1,1] into a
real number in the signed digit stream representation.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 1. Theory

We assume a basic theory of rational numbers.  From our work on
rational numbers, particularly the following lemma has a crucial role.

for all a, a in [-1,1] implies a in [-1,0] or a in [-1/2,1/2] or a in [0,1]

The representation of our real numbers in [-1,1] is the signed digit
stream, namely an infinite list of signed digits -1 or 0 or 1.  This
signed digit stream tells us an exact real number through approximated
rational intervals.  If we have no information for the approximation,
namely we have an empty list of signed digit, our real number is
somewhere in [-1,1].  One signed digit brings a piece of information
to specify where our real number is in a more accurate way.  -1 tells
that our real number is in the left hand side of the rational interval
[-1,1], ie. somewhere in [-1,0].  Similarly, 0 tells right
ie. [-1/2,1/2] and 1 tells left ie. [0,1].  To proceed determining an
accurate approximation, we consider [-1,1] again rather than
[-1,0],[-1/2,1/2], or [0,1].  It is possible by mappings
f(x):=2x+1,g(x):=2x,and h(x):=2x-1 to go back to [-1,1] from whichever
of [-1,0],[-1/2,1/2], or [0,1].

Before jumping into program extraction, we explain what the expected
result is.  Our program should take an argument representing a
rational number and generate a signed digit stream as a real number
representation for it.  It works by determining a signed digit
recursively as many as required.  Assume the given argument is "a"
representing a rational number.  We can determine a in
[-1,0],[-1/2,1/2], or [0,1], say left, middle, right.  For left, we
take -1 for the signed digit, and give 2*a+1 to the next recursion
step.  It is valid operation because determining [-1,-1/2],
[-3/4,-1/4], or [-1/2,0] as a better approximation of a is equivalent
to determining [-1,0],[-1/2,1/2],[0,1] for 2*a+1.  Similarly, we take
0,1 for these cases and give 2a or 2a-1 to the next recursion step.
That is how our extracted program works.

We prove a proposition to extract computational contents from its
proof.  The content of our proposition should claim that for all
rational number a, a is in [-1,1] implies that a is also a real number
in [-1,1].  We define a coinductive predicate CoI of arity rational
number to describe the conclusion of the implication.  The definition
of CoI is the following:

allnc a^(CoI a^ -> a^ = 0 orr exr b^(a^=(b^ +1)/2 andr CoI b^) orr
                              exr b^(a^=b^/2 andr CoI b^) orr
			      exr b^(a^=(b^ -1)/2 andr CoI b^))

Roughly speaking, for all a^ (notation for partial variables) CoI a^
implies that a^ = 0 holds, otherwise we can determine what the signed
digit to give a better approximation and also find another b^ such
that CoI b^ tells what the rest of the sighed digit stream is.

orr andr appearing in the above formula are disjunction and
conjunction with a note on the computational contents.  The ending r
stands for right, and in the case of orr and andr, we take the
computational content from the right hand side of these connectives.
The left hand side is discarded even if there is a computational
content in left.  exr has a similar meaning.  We indicate the
quantified variable by left, and the formula by right.  exr specifies
that the computational content from the formula is available, and one
from the variable is discarded.

The following is a table of the ending.

andX, orX, exX
----------------------------------------------------
      r             right side
      l             left side
      d             double side
      u             uniform: Both sides are thrown away

We don't need to specify them on Minlog, if it is obvious from the
formula.  Notations andi, ori, exi, and exnci are available.  andi and
ori automatically determine the appropriate one by examining which
side does not have a computational content.  On the other hand in exi
and exnci, we have to specify whether the quantified variable has a
computational content or not because both options are always there.
exi is to tell that the variable has a computational content, and
exnci is to tell the other case.  One cannot use this facility if it
is necessary to throw away existing computational contents.

For convenience, we also define an inductive predicate Q.

all a(-1 <= a <= 1 -> Q a)

We call the constructor of algQ cGenQ.  The type of cGenQ is
rational->algQ.  In the formalized definition of CoI, the position in
the disjunction results in a determined signed digit.  The second,
third and the fourth formulas of the disjunction are relevant to left,
middle and right, hence -1,0, and 1 in the signed digit.  One also see
the correspondence between the clause formula of CoI and the interval
algebra.  Let's prove the following proposition.

allnc a^(Q a^ -> CoI a^)

where Q is inductively defined as follows:

all a(-1 <= a <= 1 -> Q a)

Assume a^.  Apply the gfp axiom of CoI instantiated by Q.

allnc a^(Q a^ ->
            allnc a^(Q a^ -> a^ = 0 orr
 	       	        exnci b^(a^=(b^ -1)/2 andr (CoI b^ ord Q b^)) orr
			exnci b^(a^=b^/2 andr (CoI b^ ord Q b^)) orr
			exnci b^(a^=(b^ +1)/2 andr (CoI b^ ord Q b^))) ->
         CoI a^)

Applying an assumed a^ and Q a^ in the premise of the goal, the left
subgoal is the second premise in the gfp axiom.  Assume a^ and Q a^,
showing the disjunction.  From Q a^, we can determine a^ in
[-1,0],[-1/2,1/2], or [0,1] by the Split at Rational lemma.  For the
case of a^ in [-1,0], we take the second formula in the disjunction.
Let b^ be 2*a^+1, then a^=(b^ -1)/2 and also Q b^ hold.  For the case
of a^ in middle and right, we can do them similarly by letting b^ be
2*a^ and b^ be 2*a^-1, hence the proof.

Our extracted term roughly looks as follows.  We assumed a variable,
but it has nothing to do with computation due to its non-computational
quantifier.  Q a^ in the implication yields a lambda abstraction of a
variable of type algQ.  The body of this lambda term starts with
corecursion operator comes from the gfp axiom.  What we obtain by
program extraction is CoR N M where N is from the first premise of gfp
and M is from the second premise of gfp.  We showed the first premise
of the gfp axiom from the assumption in the context, namely an
abstracted variable.  Thus we name the variable x which is of type
algQ and let N be x.  The second premise was shown by giving an
appropriate b^ after the case distinction of a^ by the Split at
Rational lemma.  We again take a lambda abstraction for the
implication.  By the lemma, we obtain a conjunction which tells which
of left, middle or right is the case.  Instead of two elimination of
disjunction, we adopt the notion of if clause to simplify it.  Let
cSplit be a term from the split lemma.  We will extract M1, M2, and M3
from the part to determine b^ in the proof.

[x'](if (cSplit x') M1 M2 M3)

For M1, we took the second position of the disjunction of four
formulas, hence it starts with InR(InL(...)).  In the disjunction of
CoI b^ and Q b^, we took the right hand side, hence InR of a term to
be b^ = 2*a^+1 should fill ... in the above one.  Thus M1 :=
InR(InL(InR (cGenQ 2*a^+1))).  Similarly, M2 := InR(InR(InL(InR (cGenQ
2*a^)))) and M3 := InR(InR(InR(InR (cGenQ 2*a^-1)))) are extracted as
well.  The whole program looks: [x](CoR x ([x'](if (cSplit x') M1 M2
M3)))

This program can be applied to a term of algQ to compute a signed
digit stream.  The following is an example.

([x](CoR x ([x'](if (cSplit x') M1 M2 M3)))) (cGenQ 1/2)
-> (CoR (cGenQ 1/2) ([x'](if (cSplit x') M1 M2 M3)))
-> [ [_]CInt, [x](CIntN([id,[y](CoR y M)]x)), ...,
              [x](CIntP([id,[y](CoR y M)]x))] (if (cSplit (cGenQ 1/2) M1 M2 M3))
-> [ [_]CInt, [x](CIntN([id,[y](CoR y M)]x)), ...,
              [x](CIntP([id,[y](CoR y M)]x))] (InR(InR(InR(InR (cGenQ 0)))))
-> ([x](CIntP ([id,[y](CoR y M)]x))) (InR (cGenQ 0))
-> CIntP ([id,[y](CoR y M)] (InR (cGenQ 0)))
-> CIntP (([y](CoR y M)) (cGenQ 0))
->* CIntP(CIntZ (([y](CoR y M)) (cGenQ 0)))
-> ...

One sees the signed digit representation of a rational number 1/2 is
CIntP (CIntZ (CIntZ ( ... ))).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2. Formal Proof on Minlog

(The line numbers L12 etc. refer to the file ratsds.scm).

Loading Minlog and necessary libraries.

L12 For rational arithmetic we give additional stuff to be a
complement to existing ones in numbers.scm.  On rational numbers,
a-b+b=a and a+2*b=a+b+b hold.  We assume them as rewriting rules.

We give two global assumptions:

all a,b,c,d(a <= b -> c <= d -> a+b <= c+d)
all a,b,c(a <= b -> b <= c -> a <= c)

In our case study it is crucial to determine

   -1 <= a <= 0 or -1/2 <= a <= 1/2 or 0 <=a <= 1

for given rational number a in [-1,1].

We prove a lemma, all a,b(a<=b ori b<=a), and obtain

1. a <= -1/3 or -1/3 <= a
2. a <= 1/3 or 1/3 <= a

Then we can determine the above disjunction.  We prove two lemmas,
NegOrPos and SplitAtRational, in order to give a way to determine the
above.

L15 The statement of NegOrPos says that for all rational number a such
that a<= 0 or 0 <= a.

(set-goal "all a(a<=0 ori 0<=a)")
?_1: all a(a<=0 oru 0<=a)

L17 We do the case distinction on a to see k and p such that a=k#p,
and the case distinction once more on k to see what the outermost
constructor of k is.

(cases)
?_2:all k,p((k#p)<=0 oru 0<=(k#p))
(cases)
?_5:all p,p0((IntN p#p0)<=0 oru 0<=(IntN p#p0))
?_4:all p((0#p)<=0 oru 0<=(0#p))
?_3:all p,p0((p#p0)<=0 oru 0<=(p#p0))

L18 Those three cases are for k negative, k zero, and k positive
respectively from the upper one to the bottom one.  We start from the
bottom, namely the case for k positive.  We determine that this is the
case to be the right hand side of the disjunction.

(assume "p0" "p1")
?_6:(p0#p1)<=0 oru 0<=(p0#p1)
(intro 1)
?_7:0<=(p0#p1)
(use "Truth")
> ok, ?_7 is proved.  The active goal now is

  a12061  k12065
-----------------------------------------------------------------------------
?_4:all p((0#p)<=0 oru 0<=(0#p))

L22 The next goal is the zero case.  We take it for the left hand side
of the disjunction.

(assume "p0")
?_8:(0#p0)<=0 oru 0<=(0#p0)
(intro 0)
?_9:(0#p0)<=0
(use "Truth")
ok, ?_9 is proved.  The active goal now is

  a12061  k12065
-----------------------------------------------------------------------------
?_5:all p,p0((IntN p#p0)<=0 oru 0<=(IntN p#p0))

L25 For the last case, we can infer that 0 <= a.

(assume "p0" "p1")
?_10:(IntN p0#p1)<=0 oru 0<=(IntN p0#p1)
(intro 0)
?_11:(IntN p0#p1)<=0
(use "Truth")
ok, ?_11 is proved.  Proof finished.
(save "NegOrPos")
ok, NegOrPos has been added as a new theorem.
ok, program constant cNegOrPos: rat=>boole
of t-degree 1 and arity 0 added

L31 We generalize the above lemma by parameterising 0.

(set-goal "all a,b(a<=b ori b<=a)")
?_1: all a,b(a<=b oru b<=a)
(assume "a" "b")
?_2: a<=b oru b<=a

L34 We apply NegOrPos to obtain the proof of a-b<=0 or 0<=a-b.  First
assuming a-b<=0 or 0<=a-b and using NegOrPos.

(assert "a-b<=0 ori 0<=a-b")
?_3:a-b<=0 oru 0<=a-b -> a<=b oru b<=a
?_4:a-b<=0 oru 0<=a-b
 (use "NegOrPos")
ok, ?_4 is proved.  The active goal now is
?_3: a-b<=0 oru 0<=a-b -> a<=b oru b<=a
(assume "NegOrPos inst")
ok, we now have the new goal 
  a  b  NegOrPos inst:a-b<=0 oru 0<=a-b
-----------------------------------------------------------------------------
?_5:a<=b oru b<=a

Applying the elimination axiom of oru gives us two new goals:

a-b<=0 --> a<=b oru b<=a
0<=a-b --> a<=b oru b<=a

The elimination axiom of oru is:

A oru B -> (A --> P) -> (B --> P) -> P

Let P be a<=b oru b<=a in our case.

L37

(elim "NegOrPos inst")
?_7:0<=a-b -> a<=b oru b<=a
?_6:a-b<=0 -> a<=b oru b<=a
(drop "NegOrPos inst")
(assume "Hneg")
ok, we now have the new goal 

  a  b  Hneg:a-b<=0
-----------------------------------------------------------------------------
?_9:a<=b oru b<=a

L40 We should show a<=b since Hneg is in the context.

(intro 0)
?_10:a<=b

L41 By asserting (a-b)+b<=0+b, this goal is proven.  The assertion is
shown by RatLeMonPlus, the monotonicity of addition with respect to <=.

(assert "(a-b)+b<=0+b")
?_11:a-b+b<=0+b -> a<=b
?_12: a-b+b<=0+b
(use "RatLeMonPlus")
?_14: b<=b
?_13: a-b<=0
(use "Hneg")
?_14: b<=b
(use "Truth")
ok, ?_14 is proved.  The active goal now is
?_11: a-b+b<=0+b -> a<=b

L45 The asserted premise trivially yields the conclusion.

(assume "H0")
(use "H0")
?_7: 0<=a-b --> a<=b oru b<=a

L47 We prove the other subcase.  From the premise, we show the right
hand side of the disjunction.

(assume "Hpos")
?_16:a<=b oru b<=a
(intro 1)
?_17: b<=a

L49 By asserting 0+b<=(a-b)+b, the goal is proven as in the previous
case.

(assert "0+b<=(a-b)+b")
?_18: 0+b<=a-b+b -> b<=a
?_19: 0+b<=a-b+b
 (use "RatLeMonPlus
 (use "Hpos")
?_21: b<=b
 (use "Truth")
ok, ?_21 is proved.  The active goal now is
?_18: 0+b<=a-b+b -> b<=a

L53 The rest is trivial.

(assume "H0")
?_22: b<=a
(use "H0")
ok, ?_22 is proved.  Proof finished.

(save "SplitAtRational")
ok, SplitAtRational has been added as a new theorem.
ok, program constant cSplitAtRational: rat=>rat=>boole
of t-degree 1 and arity 0 added

L58 We represent real numbers between -1 and 1 by the following
algebra:

(add-alg "intv" '("CInt" "intv") '("CIntN" "intv=>intv")
         '("CIntZ" "intv=>intv") '("CIntP" "intv=>intv"))
ok, algebra intv added

L61 In addition, we define a predicate Q to tell rational numbers
between -1 and 1.

(add-ids (list (list "Q" (make-arity (py "rat")) "algQ"))
	 '("all a(IntN 1<=a andi a<=1 -> Q a)" "GenQ"))

ok, inductively defined predicate constant Q added

L64 To state our lemma for program extraction, we define an inductive
predicate I and another coinductive predicate CoI which is derived
from I.

(add-ids (list (list "I" (make-arity (py "rat")) "intv"))
	 '("I(0#1)" "InitI")
	 '("allnc a^(I a^ -> I((a^ -1)/2))" "GenIP")
	 '("allnc a^(I a^ -> I(a^ /2))" "GenIZ")
	 '("allnc a^(I a^ -> I((a^ +1)/2))" "GenIP"))
ok, inductively defined predicate constant I added
(add-co "I")
ok, coinductively defined predicate constant CoI added

add-co generates a closure of CoI from the definition of I in order to
define CoI.

L71 One can see the closure of CoI in the following way.

(pp (rename-variables (aconst-to-formula
		       (theorem-name-to-aconst "CoIClause"))))

allnc a^(
 CoI a^ -> 
 a^ eqd 0 orr 
 exr a^0(CoI a^0 andl a^ eqd(a^0-1)/2) ord 
 exr a^0(CoI a^0 andl a^ eqd a^0/2) ord 
 exr a^0(CoI a^0 andl a^ eqd(a^0+1)/2))

As we saw, a^ in [-1,1] implies -1 <= a^ <= 0 or -1/2 <= a^ <= 1/2 or
0 <= a^ <= 1.  We say left, middle, and right for each case for
brevity.  In the case of left, we can find a^0 in [-1,1] satisfying a^
= (a^0-1)/2, because 2*a^ +1 specifies a^0 from the condition on a^.
Conditions a^ =(a^0-1)/2, a^ =a^0/2, and a^ =(a^0+1)/2 tell which
signed digit should be the first one to represent a^ in SDS.

The position of the condition in the disjunction indicates an
appropriate constructor of intv, namely the signed digit.  The first
position indicates the first constructor CInt, the second position
indicates the second constructor CIntN, and so on.  For example, if a^
= 2/3, a^ =(a^0+1)/2 is satisfied by letting a^0 be 1/3, the signed
digit should be 1 which is CIntP in intv.  This is the computational
content of CoI.  The algebra of the realizer of CoI is isomorphic to
intv.

In LemmaA, we assume Q a^ to prove CoI a^ for all a^.  Roughly
speaking, if a^ is a rational number in [-1,1], a^ is a real number in
[-1,1] as well.

L81

(set-goal "allnc a^(Q a^ -> CoI a^)")
(assume "a^0")
ok, we now have the new goal 

  {a^0}
-----------------------------------------------------------------------------
?_2:Q a^0 -> CoI a^0

L84 Now we apply coinduction to prove it.  The greatest fixedpoint
axiom of CoI is the following:

allnc a^0(P a^0 ->
       allnc a^0(P a^0 -> a^ =0 orr
                 exr a^0(a^ =(a^0-1)/2 andr (CoI a^0 ord P a^0)) ord
		 exr a^0(a^ =a^0/2 andr (CoI a^0 ord P a^0)) ord
		 exr a^0(a^ =(a^0+1)/2 andr (CoI a^0 ord P a^0))) ->
          CoI a^0)

When the goal is in the implication form, coind takes the premise to
be a competitor.  In our case, Q substitutes P and it lets a^0 in the
beginning of the greatest fixedpoint axiom be a^0 appears in the
context.

(coind)
ok, ?_2 can be obtained from

  {a^0}  1:Q a^0
-----------------------------------------------------------------------------
?_3:allnc a^(
     Q a^ -> 
     a^ eqd 0 orr 
     exr a^0((CoI a^0 ord Q a^0) andl a^ eqd(a^0-1)/2) ord 
     exr a^0((CoI a^0 ord Q a^0) andl a^ eqd a^0/2) ord 
     exr a^0((CoI a^0 ord Q a^0) andl a^ eqd(a^0+1)/2))
(assume "a^")
  {a^0}  1:Q a^0
  {a^}
-----------------------------------------------------------------------------
?_4:Q a^ -> 
    a^ eqd 0 orr 
    exr a^0((CoI a^0 ord Q a^0) andl a^ eqd(a^0-1)/2) ord 
    exr a^0((CoI a^0 ord Q a^0) andl a^ eqd a^0/2) ord 
    exr a^0((CoI a^0 ord Q a^0) andl a^ eqd(a^0+1)/2)

L95 In order to show this goal, we apply the elimination axiom of Q
to the conclusion of the goal.  Since the goal is in the implication
form, it is simply done by elim.

(elim)
ok, ?_4 can be obtained from

  {a^0}  1:Q a^0
  {a^}  2:Q a^
-----------------------------------------------------------------------------
?_5:all a(
     IntN 1<=a andu a<=1 -> 
     a eqd 0 orr 
     exr a^0((CoI a^0 ord Q a^0) andl a eqd(a^0-1)/2) ord 
     exr a^0((CoI a^0 ord Q a^0) andl a eqd a^0/2) ord 
     exr a^0((CoI a^0 ord Q a^0) andl a eqd(a^0+1)/2))
(assume "a" "a in [-1,1]")
  {a^0}  1:Q a^0
  {a^}  2:Q a^
  a  a in [-1,1]:IntN 1<=a andu a<=1
-----------------------------------------------------------------------------
?_6:a eqd 0 orr 
    exr a^0((CoI a^0 ord Q a^0) andl a eqd(a^0-1)/2) ord 
    exr a^0((CoI a^0 ord Q a^0) andl a eqd a^0/2) ord 
    exr a^0((CoI a^0 ord Q a^0) andl a eqd(a^0+1)/2)

L97 Applying the elimination axiom of andu with a in [-1,1], we can
decompose a in [-1,1] into two individual formulas.

(elim "a in [-1,1]")
ok, ?_6 can be obtained from

  {a^0}  1:Q a^0
  {a^}  2:Q a^
  a  a in [-1,1]:IntN 1<=a andu a<=1
-----------------------------------------------------------------------------
?_7:IntN 1<=a -> 
    a<=1 -> 
    a eqd 0 orr 
    exr a^0((CoI a^0 ord Q a^0) andl a eqd(a^0-1)/2) ord 
    exr a^0((CoI a^0 ord Q a^0) andl a eqd a^0/2) ord 
    exr a^0((CoI a^0 ord Q a^0) andl a eqd(a^0+1)/2)
(drop "a in [-1,1]")
(assume "IntN 1<=a" "a<=1")
ok, we now have the new goal 

  {a^0}  1:Q a^0
  {a^}  2:Q a^
  a  IntN 1<=a:IntN 1<=a
  a<=1:a<=1
-----------------------------------------------------------------------------
?_9:a eqd 0 orr 
    exr a^0((CoI a^0 ord Q a^0) andl a eqd(a^0-1)/2) ord 
    exr a^0((CoI a^0 ord Q a^0) andl a eqd a^0/2) ord 
    exr a^0((CoI a^0 ord Q a^0) andl a eqd(a^0+1)/2)

From the condition of a, we do the case distinction on a as follows:

1. -1 <= a <= -1/3 (left)
2. -1/3 <= a <= 1/3 (middle)
3. 1/3 <= a <= 1 (right)

It is straightforward by SplitAtRational.

L100 The first case is for left.

(assert (pf "a<=(IntN 1#3) ori (IntN 1#3)<=a"))
 (use "SplitAtRational")
(assume "a<=(IntN 1#3) oru (IntN 1#3)<=a")
(elim "a<=(IntN 1#3) oru (IntN 1#3)<=a")
(drop "a<=(IntN 1#3) oru (IntN 1#3)<=a")
(assume "a<=(IntN 1#3)")
ok, we now have the new goal 

  {a^0}  1:Q a^0
  {a^}  2:Q a^
  a  IntN 1<=a:IntN 1<=a
  a<=1:a<=1
  a<=(IntN 1#3):a<=(IntN 1#3)
-----------------------------------------------------------------------------
?_16:a eqd 0 orr 
     exr a^0((CoI a^0 ord Q a^0) andl a eqd(a^0-1)/2) ord 
     exr a^0((CoI a^0 ord Q a^0) andl a eqd a^0/2) ord 
     exr a^0((CoI a^0 ord Q a^0) andl a eqd(a^0+1)/2)

L108 We choose the second case of the disjunction.

(intro 1)
ok, ?_16 can be obtained from

  {a^0}  1:Q a^0
  {a^}  2:Q a^
  a  IntN 1<=a:IntN 1<=a
  a<=1:a<=1
  a<=(IntN 1#3):a<=(IntN 1#3)
-----------------------------------------------------------------------------
?_17:exr a^0((CoI a^0 ord Q a^0) andl a eqd(a^0-1)/2) ord 
     exr a^0((CoI a^0 ord Q a^0) andl a eqd a^0/2) ord 
     exr a^0((CoI a^0 ord Q a^0) andl a eqd(a^0+1)/2)
(intro 0)
ok, ?_17 can be obtained from

  {a^0}  1:Q a^0
  {a^}  2:Q a^
  a  IntN 1<=a:IntN 1<=a
  a<=1:a<=1
  a<=(IntN 1#3):a<=(IntN 1#3)
-----------------------------------------------------------------------------
?_18:exr a^0((CoI a^0 ord Q a^0) andl a eqd(a^0-1)/2)

L110 Introduce "2*a+1" for the existential quantifier, and also
splitting andu intro two sub goals.

(intro 0 (pt "2*a+1"))
ok, ?_18 can be obtained from

  {a^0}  1:Q a^0
  {a^}  2:Q a^
  a  IntN 1<=a:IntN 1<=a
  a<=1:a<=1
  a<=(IntN 1#3):a<=(IntN 1#3)
-----------------------------------------------------------------------------
?_19:(CoI(2*a+1) ord Q(2*a+1)) andl a eqd(2*a+1-1)/2
(split)
ok, we now have the new goals 

  {a^0}  1:Q a^0
  {a^}  2:Q a^
  a  IntN 1<=a:IntN 1<=a
  a<=1:a<=1
  a<=(IntN 1#3):a<=(IntN 1#3)
-----------------------------------------------------------------------------
?_21:a eqd(2*a+1-1)/2



  {a^0}  1:Q a^0
  {a^}  2:Q a^
  a  IntN 1<=a:IntN 1<=a
  a<=1:a<=1
  a<=(IntN 1#3):a<=(IntN 1#3)
-----------------------------------------------------------------------------
?_20:CoI(2*a+1) ord Q(2*a+1)

(intro 1)
?_22:Q(2*a+1)
(intro 0)
?_23:IntN 1<=2*a+1 andu 2*a+1<=1
(intro 0)
?_24:IntN 1<=2*a+1

L115 This goal is done by the rational arithmetic.  We have
ord-field-simp-bwd to do it.

(ord-field-simp-bwd)
?_26:0<=1+a
(use-with "RatLeMonPlus"
	  (pt "1#1") (pt "1#1") (pt "IntN 1#1") (pt "a")
	  "Truth" "IntN 1<=a")
?_25:2*a+1<=1
(ord-field-simp-bwd)
?_27:a<=0
(use "RatLeTrans" (pt "IntN 1#3"))
?_29:(IntN 1#3)<=0
?_28:a<=(IntN 1#3)
(use "a<=(IntN 1#3)")
?_29:(IntN 1#3)<=0
(use "Truth")
?_21:a eqd(2*a+1-1)/2
(ord-field-simp-bwd)
ok, Simp-GA20 has been added as a new global assumption.
ok, ?_21 is proved.  The active goal now is
?_14:(IntN 1#3)<=a -> 
     a eqd 0 orr 
     exr a^0((CoI a^0 ord Q a^0) andl a eqd(a^0-1)/2) ord 
     exr a^0((CoI a^0 ord Q a^0) andl a eqd a^0/2) ord 
     exr a^0((CoI a^0 ord Q a^0) andl a eqd(a^0+1)/2)
(drop "a<=(IntN 1#3) oru (IntN 1#3)<=a")
(assume "(IntN 1#3)<=a")

;Case "(IntN 1#3)<=a"
L129 We split it at 1/3.
(assert "a<=(1#3) ori (1#3)<=a")


(assert (pf "a<=(1#3) ori (1#3)<=a"))
 (use "SplitAtRational")
(assume "a<=(1#3) oru (1#3)<=a")
(elim "a<=(1#3) oru (1#3)<=a")
ok, ?_34 can be obtained from
?_36:(1#3)<=a -> 
     a eqd 0 orr 
     exr a^0((CoI a^0 ord Q a^0) andl a eqd(a^0-1)/2) ord 
     exr a^0((CoI a^0 ord Q a^0) andl a eqd a^0/2) ord 
     exr a^0((CoI a^0 ord Q a^0) andl a eqd(a^0+1)/2)

?_35:a<=(1#3) -> 
     a eqd 0 orr 
     exr a^0((CoI a^0 ord Q a^0) andl a eqd(a^0-1)/2) ord 
     exr a^0((CoI a^0 ord Q a^0) andl a eqd a^0/2) ord 
     exr a^0((CoI a^0 ord Q a^0) andl a eqd(a^0+1)/2)

(drop "a<=(1#3) oru (1#3)<=a")
(assume "a<=(1#3)")
?_38:a eqd 0 orr 
     exr a^0((CoI a^0 ord Q a^0) andl a eqd(a^0-1)/2) ord 
     exr a^0((CoI a^0 ord Q a^0) andl a eqd a^0/2) ord 
     exr a^0((CoI a^0 ord Q a^0) andl a eqd(a^0+1)/2)
L137 Subcases for middle and right are straightforward rational
arithmetic as in the case of left.

L185 We save LemmaA to extract a term from it.

ok, ?_77 is proved.  Proof finished.
(save "LemmaA")
ok, LemmaA has been added as a new theorem.
ok, program constant cLemmaA: algQ=>intv
of t-degree 1 and arity 0 added
(define eterm (proof-to-extracted-term (theorem-name-to-proof "LemmaA")))

L189 In the proof we referred to two lemmas, NegOrPos and
SplitAtRational, with computational contents.  Minlog gives the lemmas
names cNegOrPos and cSplitAtRational which are actually constants.
Since we have already proven these lemmas in a constructive way, the
computational content from them is available.  It results in a
computation rule for each of cNegOrPos and cSplitAtRational and we can
enable these rules by animating them.

(animate "SplitAtRational")
ok, computation rule cSplitAtRational -> [a0,a1]cNegOrPos(a0-a1) added
(animate "NegOrPos")
ok, computation rule cNegOrPos -> [a0][if a0 ([k1,p2][if k1 ([p3]False) True ([p3]True)])] added

L200 Now we normalize eterm and name it neterm.
(define neterm (rename-variables (nt eterm)))
[algQ]
 (CoRec algQ=>intv)algQ
 ([algQ0]
   [if algQ0
     ([a]
      [if (a-(IntN 1#3))
        ([k,p]
         [if k
           ([p0]
...
The corecursion operator has no computation rule in Minlog, since
this term is a constant which is in normal form.  It has been
implemented in this way in order not to yield an infinite reduction
sequence.  To let the corecursion operator to expose its information,
we have another way to unfold the corecursion operator.

undelay-delayed-corec takes two arguments, a term and a natural
number.  Corecursion operators in the given term are then unfolded up
to the specified number.  Thus, it exposes approximated information by
normalization.  The resulted term generally contains corecursion
operators to carry not yet exposed information, and it can be unfolded
in the future in the same way.

L226 Here we apply undelay-delayed-corec.

(define bcorecterm (undelay-delayed-corec neterm 1))
(pp (rename-variables bcorecterm))

[algQ]
 (Rec nat=>algQ=>(algQ=>uysum
 ((intv ysum algQ)ysum(intv ysum algQ)ysum intv ysum algQ))=>intv)
 (Succ Zero)
 (CoRec algQ=>intv)
 ([n^,(algQ=>(algQ=>...

The result is one unfolding of the corecursion operator.  Our
extracted program can transform a rational number to a real number,
but it shows only the required amount of information.

L229 Transforming a rational 0 into a real number appears as an
infinite signed digit stream of 0, which is CIntZ(CIntZ(...

(pp (nt (undelay-delayed-corec
         (make-term-in-app-form neterm (pt "cGenQ 0")) 5)))
CIntZ
(CIntZ
 (CIntZ
  (CIntZ
   (CIntZ
    ((CoRec algQ=>intv)(cGenQ 0) ...)))))

It also works for other rationals in [-1,1].

L239

(pp (nt (undelay-delayed-corec
	 (make-term-in-app-form neterm (pt "cGenQ 1")) 5)))
CIntP
(CIntP
 (CIntP
  (CIntP
   (CIntP
    ((CoRec algQ=>intv)(cGenQ 1)
...

L243

(pp (nt (undelay-delayed-corec
	 (make-term-in-app-form neterm (pt "cGenQ(1#2)")) 5)))
CIntP
(CIntZ
 (CIntZ
  (CIntZ
   (CIntZ
    ((CoRec algQ=>intv)(cGenQ 0)
...

