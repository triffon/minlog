;; 2020-07-30.  examplesarithsqrttwo.scm

;; From Freek Wiedijk's "stamp collection" of formal proofs that
;; sqrt(2) is irrational (F. Wiedijk (ed.), The Seventeen Provers of
;; the World, LNAI 3600, 2006).

;; 2020-07-30.  Updated to the present nat.scm

;; We prove "all n,m(n*n=NatDouble(m*m) -> n=0)", using general induction GInd.

;; (load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(set! COMMENT-FLAG #t)

(display-pconst "NatPlus" "NatTimes")
'(
NatPlus
  comprules
0	n+0	n
1	n+Succ m	Succ(n+m)
  rewrules
0	0+n	n
1	Succ n+m	Succ(n+m)
2	n+(m+l)	n+m+l
NatTimes
  comprules
0	n*0	0
1	n*Succ m	n*m+n
  rewrules
0	0*n	0
1	Succ n*m	n*m+m
2	n*(m+l)	n*m+n*l
3	(n+m)*l	n*l+m*l
4	n*(m*l)	n*m*l
5	n*Pred m	n*m--n
6	Pred m*n	m*n--n
7	n*(m--l)	n*m--n*l
8	(m--l)*n	m*n--l*n)  

(display-pconst "NatDouble" "NatHalf")
'(
  NatDouble
  comprules
0	NatDouble 0	0
1	NatDouble(Succ n)	Succ(Succ(NatDouble n))
NatHalf
  comprules
0	NatHalf 0	0
1	NatHalf 1	0
2	NatHalf(Succ(Succ n))	Succ(NatHalf n)
)

;; "NatSquareZeroRev"
(set-goal (pf "all n(n*n=0 -> n=0)"))
(cases)
(assume "Useless")
(use "Truth")
(assume "n" "Absurd")
(use "Absurd")
;; Proof finished.
(save "NatSquareZeroRev")

;; "NatLeMonSquare"
(set-goal (pf "all n,m(n<=m -> n*n<=m*m)"))
(assume "n" "m" "n<=m")
(use "NatLeMonTimes")
(use "n<=m")
(use "n<=m")
;; Proof finished.
(save "NatLeMonSquare")

;; "NatLtMonSquareRev"
(set-goal (pf "all m,n(m*m<n*n -> m<n)"))
(assume "m" "n" "m*m<n*n")
(use "NatNotLeToLt")
(assume "n<=m")
(cut (pf "n*n<=m*m"))
(assume "n*n<=m*m")
(use-with "NatLtLeTrans" (pt "m*m") (pt "n*n") (pt "m*m")
	  "m*m<n*n" "n*n<=m*m")
(use "NatLeMonSquare")
(use "n<=m")
;; Proof finished.
(save "NatLtMonSquareRev")

;; "NatDoublePosRev"
(set-goal "all n(0<NatDouble n -> 0<n)")
(cases)
(assume "Absurd")
(use "Absurd")
(assume "n" "Useless")
(use "Truth")
;; Proof finished.
(save "NatDoublePosRev")

;; "NatSquarePos"
(set-goal "all n(0<n -> 0<n*n)")
(cases)
(assume "Absurd")
(use "Absurd")
(assume "n" "Useless")
(use "Truth")
;; Proof finished.
(save "NatSquarePos")

;; "NatDoublePlus"
(set-goal "all n,m NatDouble(n+m)=NatDouble n+NatDouble m")
(assume "n")
(ind)
(use "Truth")
(assume "n1" "Hyp")
(ng #t)
(use "Hyp")
;; Proof finished.
(save "NatDoublePlus")

;; "NatDoubleTimes1"
(set-goal "all n,m NatDouble(n*m)=NatDouble n*m")
(assume "n")
(ind)
(use "Truth")
(assume "m" "IHm")
(ng #t)
(simp "NatDoublePlus")
(simp "IHm")
(use "Truth")
;; Proof finished.
(save "NatDoubleTimes1")

;; "NatDoubleTimes2"
(set-goal "all n,m NatDouble(n*m)=n*NatDouble m")
(assume "n")
(ind)
(use "Truth")
(assume "m" "IHm")
(ng #t)
(simp "NatDoublePlus")
(simp "IHm")
(simp (pf "n*NatDouble m+n+n=n*NatDouble m+(n+n)"))
(assert "all l l+l=NatDouble l")
 (ind)
 (use "Truth")
 (assume "l" "IHl")
 (ng #t)
 (use "IHl")
(assume "Assertion")
(simp "Assertion")
(ng #t)
(use "Truth")
(ng #t)
(use "Truth")
;; Proof finished.
(save "NatDoubleTimes2")

;; "NatDoubleInj"
(set-goal "all n,m(NatDouble n=NatDouble m -> n=m)")
(ind)
(cases)
(assume "Useless")
(use "Truth")
(assume "n" "Absurd")
(use "Absurd")
(assume "n" "IHn")
(cases)
(assume "Absurd")
(use "Absurd")
(assume "n1" "Hyp")
(ng)
(use "IHn")
(use "Hyp")
;; Proof finished.
(save "NatDoubleInj")

;; "Even" and "Odd"
(add-program-constant "Even" (py "nat=>boole"))
(add-program-constant "Odd" (py "nat=>boole"))

(add-computation-rules
 "Even 0" "True"
 "Odd 0" "False"
 "Even(Succ n)" "Odd n"
 "Odd(Succ n)" "Even n")

;; "NatEvenOddTotal"
(set-goal
 "allnc n^(TotalNat n^ -> TotalBoole(Even n^) andd TotalBoole(Odd n^))")
(assume "n^" "Tn")
(elim "Tn")
(split)
(use "TotalBooleTrue")
(use "TotalBooleFalse")
(assume "n^1" "Tn1" "IHn1")
(split)
(ng #t)
(use "IHn1")
(ng #t)
(use "IHn1")
;; Proof finished.
(save "NatEvenOddTotal")

(set-totality-goal "Even")
(assume "n^" "Tn")
(use "NatEvenOddTotal")
(use "Tn")
;; Proof finished.
(save "EvenTotal")

;; "OddTotal"
(set-totality-goal "Odd")
(assume "n^" "Tn")
(use "NatEvenOddTotal")
(use "Tn")
;; Proof finished.
(save "OddTotal")

;; "NatEvenOddDoubleHalf"
(set-goal "all n((Even n ->
 NatDouble(NatHalf n)=n) andnc (Odd n -> NatDouble(NatHalf(Succ n))=Succ n))")
(ind)
(split)
(assume "Useless")
(use "Truth")
(assume "Absurd")
(use "Absurd")
(assume "n" "IHn")
(split)
(use "IHn")
(use "IHn")
;; Proof finished.
(save "NatEvenOddDoubleHalf")

;; "NatEvenOddPlusRev"
(set-goal "all n,m((Even(n+m+m) -> Even n) andnc (Odd(n+m+m) -> Odd n))")
(assume "n")
(ind)
(split)
(assume "Hyp")
(use "Hyp")
(assume "Hyp")
(use "Hyp")
(assume "n1" "IHn1")
(use "IHn1")
;; Proof finished.
(save "NatEvenOddPlusRev")

;; "NatEvenOddSquareRev"
(set-goal "all n((Even(n*n) -> Even n) andnc (Odd(n*n) -> Odd n))")
(ind)
(split)
(assume "Useless")
(use "Truth")
(assume "Absurd")
(use "Absurd")
(assume "n" "IHn")
(split)
(ng #t)
(assume "Odd(n*n+n+n)")
(use "IHn")
(use "NatEvenOddPlusRev" (pt "n"))
(use "Odd(n*n+n+n)")
(ng #t)
(assume "Even(n*n+n+n)")
(use "IHn")
(use "NatEvenOddPlusRev" (pt "n"))
(use "Even(n*n+n+n)")
;; Proof finished.
(save "NatEvenOddSquareRev")

;; "SqrtTwoAux"
(set-goal "all n,m(n*n=NatDouble(m*m) -> m*m=NatDouble(NatHalf n*NatHalf n))")
(assume "n" "m" "n*n=NatDouble(m*m)")
(simp "NatDoubleTimes1")
(use "NatDoubleInj")
(simp "<-" "n*n=NatDouble(m*m)")
(simp "NatDoubleTimes2")
(simp (pf "NatDouble(NatHalf n)=n"))
(use "Truth")
(use "NatEvenOddDoubleHalf")
(use "NatEvenOddSquareRev")
(simp "n*n=NatDouble(m*m)")
(assert "all l Even(NatDouble l)")
 (ind)
 (use "Truth")
 (assume "l" "IHl")
 (ng #t)
 (use "IHl")
(assume "Assertion")
(use "Assertion")
;; Proof finished
(save "SqrtTwoAux")

;; "SqrtTwo"
(set-goal "all n,m(n*n=NatDouble(m*m) -> n=0)")
(gind (pt "[n]n"))
(ng #t)
(assume "n" "IHn" "m" "n*n=NatDouble(m*m)")
(cases (pt "0<n"))
;; Case 0<n
(assume "0<n")
(use "NatSquareZeroRev")
(simp "n*n=NatDouble(m*m)")
(assert "m=0")
 (use "IHn" (pt "NatHalf n"))
 (use "NatLtMonSquareRev")
 (simp "n*n=NatDouble(m*m)")
 (use "NatLtDouble")
 (use "NatDoublePosRev")
 (simp "<-" "n*n=NatDouble(m*m)")
 (use "NatSquarePos")
 (use "0<n")
 (use "SqrtTwoAux")
 (use "n*n=NatDouble(m*m)")
(assume "m=0")
(simp "m=0")
(use "Truth")
;; Case 0<n -> F
(assume "0<n -> F")
(use "NatLeAntiSym")
(use "NatNotLtToLe")
(use "0<n -> F")
(use "Truth")
;; Proof finished.
(save "SqrtTwo")

(define proof (theorem-name-to-proof "SqrtTwo"))
;; (cdp proof)

(define aconsts (proof-to-aconsts proof))
(map aconst-to-name aconsts)
