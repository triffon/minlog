;; $Id: sqrttwo.scm 2353 2009-11-13 11:47:37Z schwicht $

;; From Freek Wiedijk's "stamp collection" of formal proofs that
;; sqrt(2) is irrational (F. Wiedijk (ed.), The Seventeen Provers of
;; the World, LNAI 3600, 2006).

;; We prove "all n,m(n*n=D(m*m) -> n=0)", using general induction GInd.

;; (load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(set! COMMENT-FLAG #t)

(display-pconst "NatPlus" "NatTimes")
'(
NatPlus
  comprules
	nat+0	nat
	nat1+Succ nat2	Succ(nat1+nat2)
  rewrules
	0+nat	nat
	Succ nat1+nat2	Succ(nat1+nat2)
	nat1+(nat2+nat3)	nat1+nat2+nat3
NatTimes
  comprules
	nat*0	0
	nat1*Succ nat2	nat1*nat2+nat1
  rewrules
	0*nat	0
	Succ nat1*nat2	nat1*nat2+nat2
	nat1*(nat2+nat3)	nat1*nat2+nat1*nat3
	(nat1+nat2)*nat3	nat1*nat3+nat2*nat3
	nat1*(nat2*nat3)	nat1*nat2*nat3
	nat1*Pred nat2	nat1*nat2--nat1
	Pred nat2*nat1	nat2*nat1--nat1
	nat1*(nat2--nat3)	nat1*nat2--nat1*nat3
	(nat2--nat3)*nat1	nat2*nat1--nat3*nat1
)

;; "Double"
(add-program-constant "D" (py "nat=>nat"))

(add-computation-rules
 "D 0" "0"
 "D(Succ n)" "Succ(Succ(D n))")

;; "DTotal"
(set-goal (term-to-totality-formula (pt "D")))
(assume "n^" "Tn")
(elim "Tn")
(ng #t)
(use "TotalNatZero")
(assume "n^1" "Tn1" "TDn1")
(ng #t)
(use "TotalNatSucc")
(use "TotalNatSucc")
(use "TDn1")
;; Proof finished.
(save "DTotal")

;; "Half"
(add-program-constant "H" (py "nat=>nat"))

(add-computation-rules
 "H 0" "0"
 "H 1" "0"
 "H(Succ(Succ n))" "Succ(H n)")

;; "HTotal"
(set-goal (term-to-totality-formula (pt "H")))
(assert (pf "allnc n^(TotalNat n^ -> TotalNat(H n^) & TotalNat(H(Succ n^)))"))
(assume "n^" "Tn")
(elim "Tn")
(ng #t)
(split)
(use "TotalNatZero")
(use "TotalNatZero")
(assume "n^1" "Tn1" "THn1Sn1")
(ng #t)
(split)
(use "THn1Sn1")
(use "TotalNatSucc")
(use "THn1Sn1")
(assume "Assertion" "n^" "Tn")
(use "Assertion")
(use "Tn")
;; Proof finished.
(save "HTotal")

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

;; "NatLeDouble"
(set-goal "all n n<=D n")
(ind)
(use "Truth")
(assume "n" "IHn")
(ng #t)
(use "NatLeTrans" (pt "D n"))
(use "IHn")
(use "Truth")
;; Proof finished.
(save "NatLeDouble")

;; "NatLtDouble"
(set-goal "all n(0<n -> n<D n)")
(ind)
(assume "0<0")
(use "0<0")
(assume "n" "IHn")
(assume "Useless")
(ng #t)
(use "NatLeLtTrans" (pt "D n"))
(use "NatLeDouble")
(use "Truth")
;; Proof finished.
(save "NatLtDouble")

;; "NatDoublePosRev"
(set-goal "all n(0<D n -> 0<n)")
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
(set-goal "all n,m D(n+m)=D n+D m")
(assume "n")
(ind)
(use "Truth")
(assume "n1" "Hyp")
(ng #t)
(use "Hyp")
;; Proof finished.
(save "NatDoublePlus")

;; "NatDoubleTimes1"
(set-goal "all n,m D(n*m)=D n*m")
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
(set-goal "all n,m D(n*m)=n*D m")
(assume "n")
(ind)
(use "Truth")
(assume "m" "IHm")
(ng #t)
(simp "NatDoublePlus")
(simp "IHm")
(simp (pf "n*D m+n+n=n*D m+(n+n)"))
(assert "all k k+k=D k")
 (ind)
 (use "Truth")
 (assume "k" "IHk")
 (ng #t)
 (use "IHk")
(assume "Assertion")
(simp "Assertion")
(ng #t)
(use "Truth")
(ng #t)
(use "Truth")
;; Proof finished.
(save "NatDoubleTimes2")

;; "NatDoubleInj"
(set-goal "all n,m(D n=D m -> n=m)")
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
(set-goal "allnc n^(TotalNat n^ -> TotalBoole(Even n^) & TotalBoole(Odd n^))")
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

;; "EvenTotal"
(set-goal (term-to-totality-formula (pt "Even")))
(assume "n^" "Tn")
(use "NatEvenOddTotal")
(use "Tn")
;; Proof finished.
(save "EvenTotal")

;; "OddTotal"
(set-goal (term-to-totality-formula (pt "Odd")))
(assume "n^" "Tn")
(use "NatEvenOddTotal")
(use "Tn")
;; Proof finished.
(save "OddTotal")

;; "NatEvenOddDoubleHalf"
(set-goal "all n((Even n -> D(H n)=n)&(Odd n -> D(H(Succ n))=Succ n))")
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
(set-goal "all n,m((Even(n+m+m) -> Even n)&(Odd(n+m+m) -> Odd n))")
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
(set-goal "all n((Even(n*n) -> Even n)&(Odd(n*n) -> Odd n))")
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
(set-goal "all n,m(n*n=D(m*m) -> m*m=D(H n*H n))")
(assume "n" "m" "n*n=D(m*m)")
(simp "NatDoubleTimes1")
(use "NatDoubleInj")
(simp "<-" "n*n=D(m*m)")
(simp "NatDoubleTimes2")
(simp (pf "D(H n)=n"))
(use "Truth")
(use "NatEvenOddDoubleHalf")
(use "NatEvenOddSquareRev")
(simp "n*n=D(m*m)")
(assert "all k Even(D k)")
 (ind)
 (use "Truth")
 (assume "k" "IHk")
 (ng #t)
 (use "IHk")
(assume "Assertion")
(use "Assertion")
;; Proof finished
(save "SqrtTwoAux")

;; "SqrtTwo"
(set-goal "all n,m(n*n=D(m*m) -> n=0)")
(gind (pt "[n]n"))
(ng #t)
(assume "n" "IHn" "m" "n*n=D(m*m)")
(cases (pt "0<n"))
;; Case 0<n
(assume "0<n")
(use "NatSquareZeroRev")
(simp "n*n=D(m*m)")
(assert "m=0")
 (use "IHn" (pt "H n"))
 (use "NatLtMonSquareRev")
 (simp "n*n=D(m*m)")
 (use "NatLtDouble")
 (use "NatDoublePosRev")
 (simp "<-" "n*n=D(m*m)")
 (use "NatSquarePos")
 (use "0<n")
 (use "SqrtTwoAux")
 (use "n*n=D(m*m)")
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

