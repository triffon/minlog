;; 2014-03-31.  examples/classical/euclid.scm.  Unfolding of Lin a1 a2
;; k1 k2 is blocked, as in gcd-gind.scm.  Still Lin a1 a2 k1 k2 =
;; Dist(k1*a1)(k2*a2) can be proved.

;; Classical gcd proof with gind, based on A-translation.  This is an
;; update from mod99, where the minimum principle (hence cvind and
;; rec) is used.  Now we use gind.  The resulting term is short and
;; easy to read, and also evaluation of the scheme expression form the
;; eterm is fast.  However, in spite of the orign of this example from
;; the standard classical proof involving principal ideals, the proof
;; obtained is essentially constructive.

;; Remaining problems.  (i) The coefficients k1, k2 used for the
;; linear combination of the gcd from a1, a2 become very big.  The
;; reason might be that we have kept a1,a2 fixed in our proof whereas
;; Euclid changes a1 to a2 and a2 to r(a1,a2) provided r(a1,a2)>0
;; (using the fact that this doesn't change the ideal).  (ii) In
;; neterm Lin a1 a2 k1 k2 appears many times.  An attempt to take it
;; out via let failed.

;; (load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(set! COMMENT-FLAG #t)

(add-program-constant "Dist" (py "nat=>nat=>nat"))
(add-computation-rules
 "Dist nat1 nat2" "[if (nat2<nat1) (nat1--nat2) (nat2--nat1)]")

;; DistTotal
(set-goal (rename-variables (term-to-totality-formula (pt "Dist"))))
(use "AllTotalElim")
(assume "nat1")
(use "AllTotalElim")
(assume "nat2")
(ng)
(use "BooleIfTotal")
(use "BooleTotalVar")
(use "NatTotalVar")
(use "NatTotalVar")
;; Proof finished.
(save "DistTotal")

;; DistComm
(set-goal "all nat1,nat2 Dist nat1 nat2=Dist nat2 nat1")
(assume "nat1" "nat2")
(ng #t)
(use "NatLeLtCases" (pt "nat1") (pt "nat2"))
(assume "nat1<=nat2")
(use "NatLeCases" (pt "nat1") (pt "nat2"))
(use "nat1<=nat2")
(assume "nat1<nat2")
(simp "nat1<nat2")
(assert "nat2<nat1 -> F")
 (assume "nat2<nat1")
 (use-with "NatLtTrans" (pt "nat1") (pt "nat2") (pt "nat1")
                        "nat1<nat2" "nat2<nat1")
(assume "nat2<nat1 -> F")
(simp "nat2<nat1 -> F")
(use "Truth")
(assume "nat1=nat2")
(simp "nat1=nat2")
(use "Truth")
(assume "nat2<nat1")
(simp "nat2<nat1")
(assert "nat1<nat2 -> F")
 (assume "nat1<nat2")
 (use-with "NatLtTrans" (pt "nat2") (pt "nat1") (pt "nat2")
                        "nat2<nat1" "nat1<nat2")
(assume "nat1<nat2 -> F")
(simp "nat1<nat2 -> F")
(use "Truth")
;; Proof finished.
(save "DistComm")

;; DistLemma
(set-goal "all nat1,nat2,nat3(nat1=nat2+nat3 -> nat3=Dist nat1 nat2)")
(assume "nat1" "nat2" "nat3" "nat1=nat2+nat3")
(simp "DistComm")
(ng #t)
(assert "nat1<nat2 -> F")
 (assume "nat1<nat2")
 (simphyp-with-to "nat1<nat2" "nat1=nat2+nat3" "Absurd")
 (use "Absurd")
(assume "nat1<nat2 -> F")
(simp "nat1<nat2 -> F")
(ng #t)
(simp "nat1=nat2+nat3")
(use "Truth")
;; Proof finished.
(save "DistLemma")

(add-var-name "a" "b" "c" "q" "r" "l" (py "nat"))
(add-var-name "p" (py "nat@@nat"))

(add-program-constant "Quot" (py "nat=>nat=>nat"))
(add-program-constant "Rem" (py "nat=>nat=>nat"))
(add-program-constant "QuotRem" (py "nat=>nat=>nat@@nat"))
(add-program-constant "QuotRemPair" (py "nat=>nat@@nat=>nat@@nat"))

(add-computation-rules
 "QuotRemPair m p"
 "[if (Succ right p<m) (left p@Succ right p) (Succ left p@0)]")

;; QuotRemPairTotal
(set-goal (rename-variables (term-to-totality-formula (pt "QuotRemPair"))))
(assume "m^" "Tm" "p^" "Tp")
(ng #t)
(split)
(use "BooleIfTotal")
(use "NatLtTotal")
(use "TotalNatSucc")
(use "Tp")
(use "Tm")
(use "Tp")
(use "TotalNatSucc")
(use "Tp")
(use "BooleIfTotal")
(use "NatLtTotal")
(use "TotalNatSucc")
(use "Tp")
(use "Tm")
(use "TotalNatSucc")
(use "Tp")
(use "TotalNatZero")
;; Proof finished.
(save "QuotRemPairTotal")

(add-computation-rules
 "QuotRem 0 m" "0@0"
 "QuotRem(Succ n)m" "QuotRemPair m(QuotRem n m)")

;; QuotRemTotal
(set-goal (rename-variables (term-to-totality-formula (pt "QuotRem"))))
(assume "n^" "Tn" "m^" "Tm")
(elim "Tn")
(ng #t)
(split)
(use "TotalNatZero")
(use "TotalNatZero")
(assume "n^1" "Tn1" "IH")
(assert "QuotRem(Succ n^1)m^ eqd QuotRemPair m^(QuotRem n^1 m^)")
 (use "InitEqD")
(assume "EqdHyp")
(simp "EqdHyp")
(drop "EqdHyp")
(use "QuotRemPairTotal")
(use "Tm")
(use "IH")
;; Proof finished.
(save "QuotRemTotal")

(add-computation-rules "Quot n m" "left(QuotRem n m)")

;; QuotTotal
(set-goal (rename-variables (term-to-totality-formula (pt "Quot"))))
(assume "n^" "Tn" "m^" "Tm")
(ng)
(use "QuotRemTotal")
(use "Tn")
(use "Tm")
;; Proof finished.
(save "QuotTotal")

(add-computation-rules "Rem n m" "right(QuotRem n m)")

;; RemTotal
(set-goal (rename-variables (term-to-totality-formula (pt "Rem"))))
(assume "n^" "Tn" "m^" "Tm")
(ng)
(use "QuotRemTotal")
(use "Tn")
(use "Tm")
;; Proof finished.
(save "RemTotal")

;; (pp (nt (pt "QuotRem 777 13")))

;; QuotRemCorrect
(set-goal "all m,n(0<m -> n=(Quot n m)*m+Rem n m & Rem n m<m)")
(assume "m")
(ind)
(ng)
(assume "0<m")
(split)
(use "Truth")
(use "0<m")
(assume "n" "IH" "0<m")
(use "NatLeCases" (pt "Succ(Rem n m)") (pt "m"))
(use "NatLtToSuccLe")
(use "IH")
(use "0<m")
(assume "Sr<m")
(split)
(ng)
(simp "Sr<m")
(ng)
(use-with "IH" "0<m" 'left)
(ng)
(simp "Sr<m")
(ng)
(use "Sr<m")
(assume "Sr=m")
(split)
(ng)
(simp "Sr=m")
(ng)
(assert "Succ n=left(QuotRem n m)*m+Succ right(QuotRem n m)")
  (use "IH")
  (use "0<m")
(simp "Sr=m")
(assume "u")
(use "u")
(ng)
(simp "Sr=m")
(use "0<m")
;; Proof finished.
(save "QuotRemCorrect")

;; LQ
(set-goal "all a,b(0<b -> a=Quot a b*b+Rem a b)")
(assume "a" "b" "0<b")
(use "QuotRemCorrect")
(use "0<b")
;; Proof finished.
(save "LQ")

;; LR
(set-goal "all a,b(0<b -> Rem a b<b)")
(assume "a" "b" "0<b")
(use "QuotRemCorrect")
(use "0<b")
;; Proof finished.
(save "LR")

(add-program-constant "Lin" (py "nat=>nat=>nat=>nat=>nat"))
(add-computation-rules
 "Lin a1 a2 0 k2" "k2*a2"
 "Lin a1 a2(Succ k1)k2" "Dist(Succ k1*a1)(k2*a2)")

;; LinTotal
(set-goal (rename-variables (term-to-totality-formula (pt "Lin"))))
(use "AllTotalElim")
(assume "a1")
(use "AllTotalElim")
(assume "a2")
(use "AllTotalElim")
(cases)
(use "AllTotalElim")
(assume "k2")
(ng #t)
(use "NatTotalVar")
(assume "k1")
(use "AllTotalElim")
(assume "k2")
(ng #t)
(use "BooleIfTotal")
(use "BooleTotalVar")
(use "NatTotalVar")
(use "NatTotalVar")
;; Proof finished.
(save "LinTotal")

;; LinDist
(set-goal "all a1,a2,k1,k2 Lin a1 a2 k1 k2=Dist(k1*a1)(k2*a2)")
(assume "a1" "a2")
(cases)
(assume "k2")
(use "Truth")
(assume "k1" "k2")
(use "Truth")
;; Proof finished.
(save "LinDist")

(add-program-constant "Step" (py "nat=>nat=>nat=>nat=>nat=>nat"))
(add-computation-rules
 "Step a1 a2 k1 k2 0" "1"
 "Step a1 a2 k1 k2(Succ q)" "[if (k2*a2<k1*a1) ((q+1)*k1--1) ((q+1)*k1+1)]")

;; StepTotal
(set-goal (rename-variables (term-to-totality-formula (pt "Step"))))
(use "AllTotalElim")
(assume "a1")
(use "AllTotalElim")
(assume "a2")
(use "AllTotalElim")
(assume "k1")
(use "AllTotalElim")
(assume "k2")
(use "AllTotalElim")
(cases)
(ng)
(use "NatTotalVar")
(assume "q")
(ng)
(use "BooleIfTotal")
(use "BooleTotalVar")
(use "NatTotalVar")
(use "NatTotalVar")
;; Proof finished.
(save "StepTotal")

;; LS1 or StepLemma
(set-goal "all a1,a2,k1,k2,q,r(
           a1=q*Lin a1 a2 k1 k2+r -> r=Lin a1 a2(Step a1 a2 k1 k2 q)(q*k2))")
(assume "a1" "a2" "k1" "k2")
(cases)
;; Case q=0.
(assume "r" "a1=r")
(ng)
(simp "a1=r")
(drop "a1=r")
(cases (pt "r"))
(assume "Useless")
(use "Truth")
(assume "n" "Useless")
(use "Truth")

;; Case Succ q.
(assume "q0" "r")
;; To block unfolding of (q0+1)*k we introduce a variable q for q0+1.
(assert "ex q Succ q0=q")
 (ex-intro (pt "Succ q0"))
 (use "Truth")
(assume "Exq")
(by-assume "Exq" "q" "Succ q0=q")
(simp "Succ q0=q")
(simp "LinDist")
(assume "qrProp")
(ng "qrProp")
(cases (pt "k2*a2<k1*a1"))
(assume "Case1")
(simphyp-with-to "qrProp" "Case1" "a=b1-b2+r")
(ng "a=b1-b2+r")
(drop "qrProp")
(assert "Step a1 a2 k1 k2(Succ q0)=q*k1--1")
 (ng #t)
 (simp "Case1")
 (simp "<-" "Succ q0=q")
 (use "Truth")
(simp "Succ q0=q")
(assume "Step a1 a2 k1 k2 q=q*k1--1")
(simp "Step a1 a2 k1 k2 q=q*k1--1")
(drop "Step a1 a2 k1 k2 q=q*k1--1")
(simp "LinDist")
(simp "DistComm")
(use "DistLemma")
;; We need to transform a=b1-b2+r into b2=b1-a+r (using a,b2<=b1).
(use "NatLeCases" (pt "0") (pt "k1"))
(use "Truth")
(assume "0<k1")
(assert "1*1*a1<=q*k1*a1")
 (use "NatLeMonTimes")
 (use "NatLeMonTimes")
 (simp "<-" "Succ q0=q")
 (use "Truth")
 (use "NatLtToSuccLe")
 (use "0<k1")
 (use "Truth")
(assume "a<=b1")
(assert "q*(k2*a2)<=q*(k1*a1)")
 (use "NatLeMonTimes")
 (use "Truth")
 (use "NatLtToLe")
 (use "Case1")
(assume "b2<=b1")
(ng #t)
(simp "NatMinusPlus")
(assert "a1=q*k1*a1+r--q*k2*a2")
 (simp "<-" "NatMinusPlus")
 (use "a=b1-b2+r")
 (use "b2<=b1")
(assume "a=b1+r-b2")
(assert "a1+q*k2*a2=q*k1*a1+r--q*k2*a2+q*k2*a2")
 (simp "<-" "a=b1+r-b2")
 (use "Truth")
 (simp "NatMinusPlusEq")
 (simp "NatPlusComm")
(assume "b2+a=b1+r")
(simp "<-" "b2+a=b1+r")
(use "Truth")
(use "NatLeTrans" (pt "q*k1*a1"))
(use "b2<=b1")
(use "Truth")
(use "a<=b1")
(assume "0=k1")
(assert "k2*a2<k1*a1")
 (use "Case1")
(simp "<-" "0=k1")
(assume "Absurd")
(use "Efq")
(use "Absurd")

;; ?_26:(k2*a2<k1*a1 -> F) -> r=Lin a1 a2(Step a1 a2 k1 k2 q)(q*k2)

(assume "Case2")
(simphyp-with-to "qrProp" "Case2" "a=b2-b1+r")
(ng "a=b2-b1+r")
(drop "qrProp")
(assert "Step a1 a2 k1 k2 q=q*k1+1")
 (simp "<-" "Succ q0=q")
 (ng #t)
 (simp "Case2")
 (use "Truth")

;; ?_92: Step a1 a2 k1 k2 q=q*k1+1 -> r=Lin a1 a2(Step a1 a2 k1 k2 q)(q*k2)

(assume "Step a1 a2 k1 k2 q=q*k1+1")
(simp "Step a1 a2 k1 k2 q=q*k1+1")
(drop "Step a1 a2 k1 k2 q=q*k1+1")
(simp "LinDist")
(use "DistLemma")
(ng #t)
;; We need to transform a=b2-b1+r into b1+a=b2+r (using b1<=b2).
(assert "q*(k1*a1)<=q*(k2*a2)")
 (use "NatLeMonTimes")
 (use "Truth")
 (use "NatNotLtToLe")
 (use "Case2")
(assume "b1<=b2")
(assert "a1=q*k2*a2--q*k1*a1+r")
 (use "a=b2-b1+r")
(simp "NatMinusPlus")
(assume "a=b2+r-b1")
(assert "a1+q*k1*a1=q*k2*a2+r--q*k1*a1+q*k1*a1")
 (simp "<-" "a=b2+r-b1")
 (use "Truth")
(simp "NatMinusPlusEq")
(simp "NatPlusComm")
(assume "b1+a=b2+a")
(use "b1+a=b2+a")
(use "NatLeTrans" (pt "q*k2*a2"))
(use "b1<=b2")
(use "Truth")
(use "b1<=b2")
;; Proof finished.
(save "LS1")

;; LS2
(set-goal "all a1,a2,k1,k2,q,r(
       a2=q*Lin a1 a2 k1 k2+r -> r=Lin a1 a2(q*k1)(Step a2 a1 k2 k1 q))")
(assume "a1" "a2" "k1" "k2" "q" "r")
(simp "LinDist")
(simp "LinDist")
(simp "DistComm")
(simp "<-" "LinDist")
(simp "DistComm")
(simp "<-" "LinDist")
(use "LS1")
;; Proof finished.
(save "LS2")

;; Instead of NatLeCases we use its special case NatZeroLeCases, which
;; can be proved by cases (not induction).

;; NatZeroLeCases
(set-goal "all nat((0<nat -> Pvar) -> (0=nat -> Pvar) -> Pvar)")
(cases)
(assume "Useless" "HypZero")
(use-with "HypZero" "Truth")
(assume "n" "HypSucc" "Useless")
(use-with "HypSucc" "Truth")
;; Proof finished.
(save "NatZeroLeCases")

;; We formalize a  classical existence proof (of Euclid's theorem).
;; Let a1,a2 be given and assume 0<a2.  The ideal (a1,a2) generated from
;; a1,a2 has a least positive element c, since 0<a2.  This element has a
;; representation c = Lin a1 a2 k1 k2 with k1,k2 natural numbers.  It is
;; a common divisor of a1 and a2 since otherwise the remainder r(ai,c)
;; would be a smaller positive element of the ideal.

;; Note that the number c in (a1,a2) dividing a1 and a2 is the greatest
;; common divisor since any common divisor of a1 and a2 must also be a
;; divisor of c.

;; Euclid
(set-goal "all a1,a2(0<a2 ->
      excl k1,k2(0=Rem a1(Lin a1 a2 k1 k2) !
                 0=Rem a2(Lin a1 a2 k1 k2) !
                 0<Lin a1 a2 k1 k2))")
(assume "a1" "a2" "v0" "u")
(cut "all k1,k2(0<Lin a1 a2 k1 k2 -> bot)")
 (exc-intro (pt "0") (pt "1"))
 (use "v0")
(gind (mk-term-in-abst-form (pv "k1") (pv "k2") (pt "Lin a1 a2 k1 k2")))
(ng)
(assume "k1" "k2" "u1" "u2")
(use "NatZeroLeCases" (pt "Rem a1(Lin a1 a2 k1 k2)"))
(assume "u31")

;; We take out usage of LS1
(assert "Rem a1(Lin a1 a2 k1 k2)=
         Lin a1 a2(Step a1 a2 k1 k2(Quot a1(Lin a1 a2 k1 k2)))
                  ((Quot a1(Lin a1 a2 k1 k2))*k2)")
 (use "LS1")
 (use "QuotRemCorrect")
 (use "u2")
(assume "ra1muk=mul") ;or LS1Cor
(use "u1" (pt "Step a1 a2 k1 k2(Quot a1(Lin a1 a2 k1 k2))")
     (pt "(Quot a1(Lin a1 a2 k1 k2))*k2"))
(simp "<-" "ra1muk=mul")
(use "LR")
(use "u2")
(simp "<-" "ra1muk=mul")
(use "u31")
(assume "u4")
(use "NatZeroLeCases" (pt "Rem a2(Lin a1 a2 k1 k2)"))
(assume "u32")

;; We take out usage of LS2
(assert "Rem a2(Lin a1 a2 k1 k2)=
         Lin a1 a2((Quot a2(Lin a1 a2 k1 k2))*k1)
                  (Step a2 a1 k2 k1(Quot a2(Lin a1 a2 k1 k2)))")
 (use "LS2")
 (use "QuotRemCorrect")
 (use "u2")
(assume "ra2muk=mul") ;or LS2Cor
(use "u1" (pt "(Quot a2(Lin a1 a2 k1 k2))*k1")
     (pt "Step a2 a1 k2 k1(Quot a2(Lin a1 a2 k1 k2))"))
(simp "<-" "ra2muk=mul")
(use "LR")
(use "u2")
(simp "<-" "ra2muk=mul")
(use "u32")
(assume "u3")

(use-with "u" (pt "k1") (pt "k2") "u4" "u3" "u2")
;; Proof finished.
(save "Euclid")

(define euclid-proof (theorem-name-to-proof "Euclid"))
;; (cdp (np euclid-proof))

;; (proof-to-expr-with-aconsts euclid-proof)
(map aconst-to-name (proof-to-aconsts euclid-proof))

;; ("ExclIntroTwoNc" "GInd" "NatZeroLeCases" "EqDCompat" "NatEqToEqD" "LR"
;;   "EqDCompat" "LS1" "QuotRemCorrect" "LS2" "Truth")

;; A-Translation

(min-excl-formula? (proof-to-formula euclid-proof)) ;#t

(define expanded-euclid-proof
  (rm-exc (expand-thm euclid-proof "NatZeroLeCases")))

(map aconst-to-name (proof-to-aconsts expanded-euclid-proof))

;; ("GInd" "Cases" "Truth" "EqDCompat" "NatEqToEqD" "LR"
;;   "EqDCompat" "LS1" "QuotRemCorrect" "LS2")

;; We need to block unfolding of GRecGuard (whose last argument will be
;; True) to obtain a readable term:

(set! GRECGUARD-UNFOLDING-FLAG #f)

(define min-excl-proof (np expanded-euclid-proof))
(define eterm-a
  (atr-min-excl-proof-to-structured-extracted-term min-excl-proof))

(add-var-name "f" (py "nat=>nat=>nat@@nat"))
(define neterm-a (rename-variables (nt eterm-a)))
;; (pp neterm-a)

;; [n,n0]
;;  (GRecGuard nat nat nat@@nat)(Lin n n0)0 1
;;  ([n1,n2,f]
;;    [if (right(QuotRem n(Lin n n0 n1 n2)))
;;      [if (right(QuotRem n0(Lin n n0 n1 n2)))
;;       (n1@n2)
;;       ([n3]
;;        f(left(QuotRem n0(Lin n n0 n1 n2))*n1)
;;        (Step n0 n n2 n1 left(QuotRem n0(Lin n n0 n1 n2))))]
;;      ([n3]
;;       f(Step n n0 n1 n2 left(QuotRem n(Lin n n0 n1 n2)))
;;       (left(QuotRem n(Lin n n0 n1 n2))*n2))])
;;  True

;; (ppc neterm-a)
;; [n,n0]
;;  (GRecGuard nat nat nat@@nat)(Lin n n0)0 1
;;  ([n1,n2,f]
;;    [case (right(QuotRem n(Lin n n0 n1 n2)))
;;      (0 ->
;;      [case (right(QuotRem n0(Lin n n0 n1 n2)))
;;        (0 -> n1@n2)
;;        (Succ n3 ->
;;        f(left(QuotRem n0(Lin n n0 n1 n2))*n1)
;;        (Step n0 n n2 n1 left(QuotRem n0(Lin n n0 n1 n2))))])
;;      (Succ n3 ->
;;      f(Step n n0 n1 n2 left(QuotRem n(Lin n n0 n1 n2)))
;;      (left(QuotRem n(Lin n n0 n1 n2))*n2))])
;;  True

(define expr (term-to-scheme-expr neterm-a))
;; (lambda (n)
;;   (lambda (n0)
;;     (((((natnatGrecGuard ((Lin n) n0)) 0) 1)
;;        (lambda (n1)
;;          (lambda (n2)
;;            (lambda (f)
;;              (cond
;;                [(zero? (cdr ((QuotRem n) ((((Lin n) n0) n1) n2))))
;;                 (cond
;;                   [(zero? (cdr ((QuotRem n0) ((((Lin n) n0) n1) n2))))
;;                    (cons n1 n2)]
;;                   [(positive? (cdr ((QuotRem n0) ((((Lin n) n0) n1) n2))))
;;                    ((f (* (car ((QuotRem n0) ((((Lin n) n0) n1) n2))) n1))
;;                      (((((Step n0) n) n2) n1)
;;                        (car ((QuotRem n0) ((((Lin n) n0) n1) n2)))))])]
;;                [(positive? (cdr ((QuotRem n) ((((Lin n) n0) n1) n2))))
;;                 ((f (((((Step n) n0) n1) n2)
;;                       (car ((QuotRem n) ((((Lin n) n0) n1) n2)))))
;;                   (* (car ((QuotRem n) ((((Lin n) n0) n1) n2))) n2))])))))
;;       #t)))

(define (QuotRem x)
  (lambda (y)
    (cons (quotient-safe x y) (modulo-safe x y))))

(define (Lin a1)
  (lambda (a2)
    (lambda (k1)
      (lambda (k2)
	(abs (- (* k1 a1) (* k2 a2)))))))

;;    Step(a1 a2 k1 k2 q) = q*k1-1 if k2*a2<k1*a1 and 0<q
;;                          q*k1+1 otherwise

(define (Step a1)
  (lambda (a2)
    (lambda (k1)
      (lambda (k2)
	(lambda (q)
	  (if (and (< (* k2 a2) (* k1 a1)) (> q 0))
	      (- (* q k1) 1)
	      (+ (* q k1) 1)))))))
	
(((ev expr) 66) 27)
;; (16 . 39)

(abs (- (* 66 16) (* 27 39)))
;; 3

(time (((ev expr) (* 1428 1151412)) (* 1428 103723)))
;; 0ms
;; (488545346575797591297055208 . 5423261712364010452749389539)

(abs (- (* (* 1428 1151412) 488545346575797591297055208)
	(* (* 1428 103723) 5423261712364010452749389539)))
;; 1428

(time (((ev expr)
	(* 176478618764 12074918274841)) (* 176478618764 34974982375987)))
;; 1ms

;; (185532993086244630827154332830412341947793818158543070211562340813460220753425924222486261794483960792423184200678029819957159970733315429433310407832279427486496946293312632860482701208603676477486368193239
;;   .
;;   64054234673215404826126312490371176469332895761600445428910505279082534624473340409473605046902412014730816801846174116697197908256354135172259226980862139233252320749317923445420881218662400000000000000000)

(abs (- (* (* 176478618764 12074918274841)
	   185532993086244630827154332830412341947793818158543070211562340813460220753425924222486261794483960792423184200678029819957159970733315429433310407832279427486496946293312632860482701208603676477486368193239)
	(* (* 176478618764 34974982375987)
	   64054234673215404826126312490371176469332895761600445428910505279082534624473340409473605046902412014730816801846174116697197908256354135172259226980862139233252320749317923445420881218662400000000000000000)))

;; 176478618764

