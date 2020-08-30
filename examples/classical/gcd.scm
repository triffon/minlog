;; 2014-01-07.  General unfolding of Lin a1 a2 k1 k2 is blocked, as in
;; gcd-gind.scm.  Still we have Lin a1 a2 k1 k2 = Dist(k1*a1)(k2*a2).

;; This is a modification of euclid.scm with a slightly changed proof
;; of the main theorem (called Gcd here).  This makes it possible to
;; apply both A-translation and Dialectica, and compare them.  All
;; this is due to Trifon Trifonov (cf. his thesis of 2012, LMU).

;; (load "~/git/minlog/init.scm")
(set! COMMENT-FLAG #f)
(libload "nat.scm")
(set! COMMENT-FLAG #t)

(add-var-name "k" (py "nat"))

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

(add-var-name "a" "b" "c" "q" "r" (py "nat"))
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

;; QuotRemCorrec
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
(use "EfAtom")
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

;; L1
(set-goal "all r,l(r=l -> (0<l -> F) -> r=0)")
(assume "r")
(cases)
(assume "r=0" "Useless")
(use "r=0")
(assume "n" "Useless" "Absurd")
(use "EfAtom")
(use "Absurd")
(use "Truth")
;; Proof finished.
(save "L1")

;; L2
(set-goal "all r,l,k(r=l -> r<k -> l<k)")
(assume "r" "l" "k" "r=l")
(simp "r=l")
(assume "l<k")
(use "l<k")
;; Proof finished.
(save "L2")

;; Now the Gcd proof with &, following the hand implementation.

;; GcdAnd
(set-goal "all a1,a2(0<a2 ->
                exca k1,k2(
                 0<Lin a1 a2 k1 k2 !
                 Rem a1(Lin a1 a2 k1 k2)=0 &
                 Rem a2(Lin a1 a2 k1 k2)=0))")
(assume "a1" "a2" "v0" "u")
(use-with "u" (pt "0") (pt "1") "v0" "?")
(use-with (make-proof-in-aconst-form
	   (all-formula-and-number-to-gind-aconst
	    (pf "all k1,k2(
                 0<Lin a1 a2 k1 k2 ->
                 Rem a1(Lin a1 a2 k1 k2)=0 & Rem a2(Lin a1 a2 k1 k2)=0)")
	    2))
	  (pt "a1") (pt "a2")
	  (pt "[k1,k2]Lin a1 a2 k1 k2") (pt "0") (pt "1")
	  "?" ;for progressiveness
	  (pt "True") (make-proof-in-aconst-form truth-aconst) ;for the guard
	  "v0")
(assume "k1" "k2" "u1" "u2")	
(split)

;; We first show Rem a1(Lin a1 a2 k1 k2)=0
(use "L1" (pt "Lin a1 a2
 (Step a1 a2 k1 k2(Quot a1(Lin a1 a2 k1 k2)))(Quot a1(Lin a1 a2 k1 k2)*k2)"))
(use "LS1")
(use "LQ")
(use "u2")
(assume "w")
(use-with "u" (pt "Step a1 a2 k1 k2(Quot a1(Lin a1 a2 k1 k2))")
	  (pt "Quot a1(Lin a1 a2 k1 k2)*k2") "w" "?")
(use "u1")
(use "L2" (pt "Rem a1(Lin a1 a2 k1 k2)"))
(use "LS1")
(use "LQ")
(use "u2")
(use "LR")
(use "u2")
(use "w")

;; We now show Rem a2(Lin a1 a2 k1 k2)=0
(use "L1" (pt "Lin a1 a2
 (Quot a2(Lin a1 a2 k1 k2)*k1)(Step a2 a1 k2 k1(Quot a2(Lin a1 a2 k1 k2)))"))
(use "LS2")
(use "LQ")
(use "u2")
(assume "w")
(use-with "u" (pt "Quot a2(Lin a1 a2 k1 k2)*k1")
	  (pt "Step a2 a1 k2 k1(Quot a2(Lin a1 a2 k1 k2))") "w" "?")
(use "u1")
(use "L2" (pt "Rem a2(Lin a1 a2 k1 k2)"))
(use "LS2")
(use "LQ")
(use "u2")
(use "LR")
(use "u2")
(use "w")
;; Proof finished.
(save "GcdAnd")

;; (proof-to-expr-with-aconsts (theorem-name-to-proof "GcdAnd"))

(define eterm-d-and
  (proof-to-extracted-d-term (theorem-name-to-proof "GcdAnd")))

;; We need to block unfolding of GRecGuard (whose last argument will be
;; True) to obtain a readable term:

(set! GRECGUARD-UNFOLDING-FLAG #f)
(define neterm-d-and (rename-variables (nt eterm-d-and)))
(pp neterm-d-and)

;; [n,n0]
;;  [if (0<n0 impb
;;        right(QuotRem n n0)=0 andb right(QuotRem n0 n0)=0 impb False)
;;    ((GRecGuard nat nat nat@@nat)(Lin n n0)0 1
;;    ([n1,n2,(nat=>nat=>nat@@nat)]
;;      [let p
;;        [let p
;;         (Step n n0 n1 n2 left(QuotRem n(Lin n n0 n1 n2))@
;;         left(QuotRem n(Lin n n0 n1 n2))*n2)
;;         [if (0<Lin n n0 left p right p impb
;;              right(QuotRem n(Lin n n0 left p right p))=0 andb
;;              right(QuotRem n0(Lin n n0 left p right p))=0 impb
;;              False)
;;          (left(QuotRem n0(Lin n n0 n1 n2))*n1@
;;          Step n0 n n2 n1 left(QuotRem n0(Lin n n0 n1 n2)))
;;          p]]
;;        [if (0<Lin n n0 left p right p impb
;;             right(QuotRem n(Lin n n0 left p right p))=0 andb
;;             right(QuotRem n0(Lin n n0 left p right p))=0 impb
;;             False)
;;         [let p0
;;          [let p0
;;           (Step n n0 n1 n2 left(QuotRem n(Lin n n0 n1 n2))@
;;           left(QuotRem n(Lin n n0 n1 n2))*n2)
;;           [if (Lin n n0 left p0 right p0<Lin n n0 n1 n2 impb
;;                0<Lin n n0 left p0 right p0 impb
;;                right(QuotRem n(Lin n n0 left p0 right p0))=0 andb
;;                right(QuotRem n0(Lin n n0 left p0 right p0))=0)
;;            (left(QuotRem n0(Lin n n0 n1 n2))*n1@
;;            Step n0 n n2 n1 left(QuotRem n0(Lin n n0 n1 n2)))
;;            p0]]
;;          ((nat=>nat=>nat@@nat)left p0 right p0)]
;;         p]])
;;    True)
;;    (0@1)]

(term-to-scheme-expr neterm-d-and)

;; (lambda (n)
;;   (lambda (n0)
;;     (if (or (not (< 0 n0))
;;             (or (not (and (= (cdr ((QuotRem n) n0)) 0)
;;                           (= (cdr ((QuotRem n0) n0)) 0)))
;;                 #f))
;;         (((((natnatGrecGuard ((Lin n) n0)) 0) 1)
;;            (lambda (n1)
;;              (lambda (n2)
;;                (lambda (lpar_nat=>nat=>nat@@nat_rpar)
;;                  (let ([p (let ([p (cons
;;                                      (((((Step n) n0) n1) n2)
;;                                        (car ((QuotRem n)
;;                                               ((((Lin n) n0) n1) n2))))
;;                                      (* (car ((QuotRem n)
;;                                                ((((Lin n) n0) n1) n2)))
;;                                         n2))])
;;                             (if (or (not (< 0
;;                                             ((((Lin n) n0) (car p))
;;                                               (cdr p))))
;;                                     (or (not (and (= (cdr ((QuotRem n)
;;                                                             ((((Lin n) n0)
;;                                                                (car p))
;;                                                               (cdr p))))
;;                                                      0)
;;                                                   (= (cdr ((QuotRem n0)
;;                                                             ((((Lin n) n0)
;;                                                                (car p))
;;                                                               (cdr p))))
;;                                                      0)))
;;                                         #f))
;;                                 (cons
;;                                   (* (car ((QuotRem n0)
;;                                             ((((Lin n) n0) n1) n2)))
;;                                      n1)
;;                                   (((((Step n0) n) n2) n1)
;;                                     (car ((QuotRem n0)
;;                                            ((((Lin n) n0) n1) n2)))))
;;                                 p))])
;;                    (if (or (not (< 0 ((((Lin n) n0) (car p)) (cdr p))))
;;                            (or (not (and (= (cdr ((QuotRem n)
;;                                                    ((((Lin n) n0) (car p))
;;                                                      (cdr p))))
;;                                             0)
;;                                          (= (cdr ((QuotRem n0)
;;                                                    ((((Lin n) n0) (car p))
;;                                                      (cdr p))))
;;                                             0)))
;;                                #f))
;;                        (let ([p0 (let ([p0 (cons
;;                                              (((((Step n) n0) n1) n2)
;;                                                (car ((QuotRem n)
;;                                                       ((((Lin n) n0) n1)
;;                                                         n2))))
;;                                              (* (car ((QuotRem n)
;;                                                        ((((Lin n) n0) n1)
;;                                                          n2)))
;;                                                 n2))])
;;                                    (if (or (not (< ((((Lin n) n0) (car p0))
;;                                                      (cdr p0))
;;                                                    ((((Lin n) n0) n1) n2)))
;;                                            (or (not (< 0
;;                                                        ((((Lin n) n0)
;;                                                           (car p0))
;;                                                          (cdr p0))))
;;                                                (and (= (cdr ((QuotRem n)
;;                                                               ((((Lin n)
;;                                                                   n0)
;;                                                                  (car p0))
;;                                                                 (cdr p0))))
;;                                                        0)
;;                                                     (= (cdr ((QuotRem n0)
;;                                                               ((((Lin n)
;;                                                                   n0)
;;                                                                  (car p0))
;;                                                                 (cdr p0))))
;;                                                        0))))
;;                                        (cons
;;                                          (* (car ((QuotRem n0)
;;                                                    ((((Lin n) n0) n1) n2)))
;;                                             n1)
;;                                          (((((Step n0) n) n2) n1)
;;                                            (car ((QuotRem n0)
;;                                                   ((((Lin n) n0) n1)
;;                                                     n2)))))
;;                                        p0))])
;;                          ((lpar_nat=>nat=>nat@@nat_rpar (car p0))
;;                            (cdr p0)))
;;                        p))))))
;;           #t)
;;         (cons 0 1))))

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
	
(define (display-gcd gcd-term a1 a2)

  (define (h k)
    (abs (- (* a1 (car k)) (* a2 (cdr k)))))

  (display "GCD of ")
  (display a1)
  (display " and ")
  (display a2)
  (display " is ")
  (display (h (((ev (term-to-expr gcd-term)) a1) a2)))
  ;; (display (time (h (((ev (term-to-expr gcd-term)) a1) a2))))
  (newline))
	
;; Tests

(display-gcd neterm-d-and 66 27)
(display-gcd neterm-d-and (* 1428 1151412) (* 1428 103723))
(display-gcd neterm-d-and (* 176478618764 12074918274841)
	     (* 176478618764 34974982375987))

;; An attempt to do the same proof with A-translation breaks down
;; because it does not cover conjunctions.  However, we can redo the
;; proof without conjunctions.  Here we closely follow Trifon
;; Trifonov's proposal.  The & in the goal is replaced by !.  Instead
;; of conjunction introduction we use

;; AndIntroAux or L3
(set-goal "all r1,r2(
      ((r1=0 -> bot) -> bot) ->
      ((r2=0 -> bot) -> bot) -> (r1=0 -> r2=0 -> bot) -> bot)")
(assume "r1" "r2" "u1" "u2" "u")
(use "u1")
(assume "v1")
(use "u2")
(assume "v2")
(use "u")
(use "v1")
(use "v2")
;; Proof finished.
(save "L3")

;; Moreover we need
;; L1bot
(set-goal "all r,l(r=l -> (0<l -> bot) -> (r=0 -> bot) -> bot)")
(assume "r")
(cases)
(assume "u1" "u2" "u3")
(use "u3")
(use "u1")
(assume "r1" "u1" "u2" "u3")
(use "u2")
(use "Truth")
;; Proof finished.
(save "L1bot")

;; Gcd
(set-goal "all a1,a2(
      0<a2 ->
      excl k1,k2(
       0<Lin a1 a2 k1 k2 !
       (Rem a1(Lin a1 a2 k1 k2)=0 ! Rem a2(Lin a1 a2 k1 k2)=0)))")
(assume "a1" "a2" "v0" "u")
(cut "all k1,k2(
   0<Lin a1 a2 k1 k2 ->
   (Rem a1(Lin a1 a2 k1 k2)=0 -> Rem a2(Lin a1 a2 k1 k2)=0 -> bot) -> bot)")
(assume "u1")
(use "u1" (pt "0") (pt "1"))
(use "v0")
(use "u")
(use "v0")

(gind (mk-term-in-abst-form (pv "k1") (pv "k2") (pt "Lin a1 a2 k1 k2")))

(assume "k1" "k2" "u1" "u2")
(use "L3")

;; Now we must show Rem a1(Lin a1 a2 k1 k2)=0.

(use "L1bot"
     (pt "Lin a1 a2(Step a1 a2 k1 k2(Quot a1(Lin a1 a2 k1 k2)))
                   (Quot a1(Lin a1 a2 k1 k2)*k2)"))
(use-with "LS1" (pt "a1") (pt "a2") (pt "k1") (pt "k2")
	  (pt "(Quot a1(Lin a1 a2 k1 k2))") (pt "Rem a1(Lin a1 a2 k1 k2)") "?")
(use "QuotRemCorrect")
(use "u2")
(assume "w")
(use "u1" (pt "(Step a1 a2 k1 k2(Quot a1(Lin a1 a2 k1 k2)))")
     (pt "(Quot a1(Lin a1 a2 k1 k2))*k2"))
(ng)

(use "L2" (pt "Rem a1(Lin a1 a2 k1 k2)"))
(simp-with "LS1" (pt "a1") (pt "a2") (pt "k1") (pt "k2")
	   (pt "Quot a1(Lin a1 a2 k1 k2)") (pt "Rem a1(Lin a1 a2 k1 k2)") "?")
(use "Truth")
(use "QuotRemCorrect")
(use "u2")
(use "LR")
(use "u2")
(use "w")
(use "u")
(use "w")

;; Now we must show Rem a2(Lin a1 a2 k1 k2)=0.
(use "L1bot"
     (pt "Lin a1 a2 ((Quot a2(Lin a1 a2 k1 k2))*k1)
                    (Step a2 a1 k2 k1(Quot a2(Lin a1 a2 k1 k2)))"))
(use-with "LS2" (pt "a1") (pt "a2") (pt "k1") (pt "k2")
	  (pt "Quot a2(Lin a1 a2 k1 k2)") (pt "Rem a2(Lin a1 a2 k1 k2)") "?")
(use "QuotRemCorrect")
(use "u2")
(assume "w")
(use "u1" (pt "((Quot a2(Lin a1 a2 k1 k2))*k1)")
     (pt "Step a2 a1  k2 k1(Quot a2(Lin a1 a2 k1 k2))"))
(ng)
(use "L2" (pt "Rem a2(Lin a1 a2 k1 k2)"))
(simp-with "LS2" (pt "a1") (pt "a2") (pt "k1") (pt "k2")
	   (pt "Quot a2(Lin a1 a2 k1 k2)") (pt "Rem a2(Lin a1 a2 k1 k2)") "?")
(use "Truth")
(use "QuotRemCorrect")
(use "u2")
(use "LR")
(use "u2")
(use "w")
(use "u")
(use "w")
;; Proof finished.
(save "Gcd")

(define gcd-proof (theorem-name-to-proof "Gcd"))
;; (cdp (np gcd-proof))

;; (proof-to-expr-with-aconsts gcd-proof)

;; A-Translation

;; (min-excl-proof? gcd-proof)
(min-excl-formula? (proof-to-formula gcd-proof)) ;#t

(define expanded-gcd-proof
  (expand-theorems gcd-proof (lambda (string)
			       (member string '("L3" "L1bot")))))

;; (proof-to-expr-with-aconsts expanded-gcd-proof)

(define min-excl-proof expanded-gcd-proof)
(define eterm-a
  (atr-min-excl-proof-to-structured-extracted-term min-excl-proof))

;; We need to block unfolding of GRecGuard (whose last argument will be
;; True) to obtain a readable term:

(set! GRECGUARD-UNFOLDING-FLAG #f)
(define neterm-a (rename-variables (nt eterm-a)))
(pp neterm-a)

;; [n,n0]
;;  (GRecGuard nat nat nat@@nat=>nat@@nat)(Lin n n0)0 1
;;  ([n1,n2,(nat=>nat=>nat@@nat=>nat@@nat),p]
;;    [if (Lin n n0(Step n n0 n1 n2 left(QuotRem n(Lin n n0 n1 n2)))
;;          (left(QuotRem n(Lin n n0 n1 n2))*n2))
;;      [if (Lin n n0(left(QuotRem n0(Lin n n0 n1 n2))*n1)
;;           (Step n0 n n2 n1 left(QuotRem n0(Lin n n0 n1 n2))))
;;       p
;;       ([n3]
;;        (nat=>nat=>nat@@nat=>nat@@nat)(left(QuotRem n0(Lin n n0 n1 n2))*n1)
;;        (Step n0 n n2 n1 left(QuotRem n0(Lin n n0 n1 n2)))
;;        (left(QuotRem n0(Lin n n0 n1 n2))*n1@
;;         Step n0 n n2 n1 left(QuotRem n0(Lin n n0 n1 n2))))]
;;      ([n3]
;;       (nat=>nat=>nat@@nat=>nat@@nat)
;;       (Step n n0 n1 n2 left(QuotRem n(Lin n n0 n1 n2)))
;;       (left(QuotRem n(Lin n n0 n1 n2))*n2)
;;       (Step n n0 n1 n2 left(QuotRem n(Lin n n0 n1 n2))@
;;        left(QuotRem n(Lin n n0 n1 n2))*n2))])
;;  True
;;  (0@1)

(term-to-scheme-expr neterm-a)

;; (lambda (n)
;;   (lambda (n0)
;;     ((((((natnatGrecGuard ((Lin n) n0)) 0) 1)
;;         (lambda (n1)
;;           (lambda (n2)
;;             (lambda (lpar_nat=>nat=>nat@@nat=>nat@@nat_rpar)
;;               (lambda (p)
;;                 (cond
;;                   [(zero?
;;                      ((((Lin n) n0)
;;                         (((((Step n) n0) n1) n2)
;;                           (car ((QuotRem n) ((((Lin n) n0) n1) n2)))))
;;                        (* (car ((QuotRem n) ((((Lin n) n0) n1) n2))) n2)))
;;                    (cond
;;                      [(zero?
;;                         ((((Lin n) n0)
;;                            (* (car ((QuotRem n0) ((((Lin n) n0) n1) n2)))
;;                               n1))
;;                           (((((Step n0) n) n2) n1)
;;                             (car ((QuotRem n0) ((((Lin n) n0) n1) n2))))))
;;                       p]
;;                      [(positive?
;;                         ((((Lin n) n0)
;;                            (* (car ((QuotRem n0) ((((Lin n) n0) n1) n2)))
;;                               n1))
;;                           (((((Step n0) n) n2) n1)
;;                             (car ((QuotRem n0) ((((Lin n) n0) n1) n2))))))
;;                       (((lpar_nat=>nat=>nat@@nat=>nat@@nat_rpar
;;                           (* (car ((QuotRem n0) ((((Lin n) n0) n1) n2)))
;;                              n1))
;;                          (((((Step n0) n) n2) n1)
;;                            (car ((QuotRem n0) ((((Lin n) n0) n1) n2)))))
;;                         (cons
;;                           (* (car ((QuotRem n0) ((((Lin n) n0) n1) n2)))
;;                              n1)
;;                           (((((Step n0) n) n2) n1)
;;                             (car ((QuotRem n0)
;;                                    ((((Lin n) n0) n1) n2))))))])]
;;                   [(positive?
;;                      ((((Lin n) n0)
;;                         (((((Step n) n0) n1) n2)
;;                           (car ((QuotRem n) ((((Lin n) n0) n1) n2)))))
;;                        (* (car ((QuotRem n) ((((Lin n) n0) n1) n2))) n2)))
;;                    (((lpar_nat=>nat=>nat@@nat=>nat@@nat_rpar
;;                        (((((Step n) n0) n1) n2)
;;                          (car ((QuotRem n) ((((Lin n) n0) n1) n2)))))
;;                       (* (car ((QuotRem n) ((((Lin n) n0) n1) n2))) n2))
;;                      (cons
;;                        (((((Step n) n0) n1) n2)
;;                          (car ((QuotRem n) ((((Lin n) n0) n1) n2))))
;;                        (* (car ((QuotRem n) ((((Lin n) n0) n1) n2)))
;;                           n2)))]))))))
;;        #t)
;;       (cons 0 1))))

;; Dialectica

(define goal-proof-d
  (expand-theorems-with-positive-content
    (theorem-name-to-proof "Gcd")))

;; (proof-to-expr-with-aconsts goal-proof-d)

(define eterm-d (proof-to-extracted-d-term goal-proof-d))

;; We need to block unfolding of GRecGuard (whose last argument will be
;; True) to obtain a readable term:

(set! GRECGUARD-UNFOLDING-FLAG #f)
(define neterm-d (rename-variables (nt eterm-d)))
;; (pp neterm-d)

;; [n,n0]
;;  [if (0<n0 impb
;;        right(QuotRem n n0)=0 impb right(QuotRem n0 n0)=0 impb False)
;;    ((GRecGuard nat nat nat@@nat)(Lin n n0)0 1
;;    ([n1,n2,(nat=>nat=>nat@@nat)]
;;      [let p
;;        [let p
;;         (Step n n0 n1 n2 left(QuotRem n(Lin n n0 n1 n2))@
;;         left(QuotRem n(Lin n n0 n1 n2))*n2)
;;         [if (0<Lin n n0 left p right p impb
;;              right(QuotRem n(Lin n n0 left p right p))=0 impb
;;              right(QuotRem n0(Lin n n0 left p right p))=0 impb False)
;;          (left(QuotRem n0(Lin n n0 n1 n2))*n1@
;;          Step n0 n n2 n1 left(QuotRem n0(Lin n n0 n1 n2)))
;;          p]]
;;        [if (0<Lin n n0 left p right p impb
;;             right(QuotRem n(Lin n n0 left p right p))=0 impb
;;             right(QuotRem n0(Lin n n0 left p right p))=0 impb False)
;;         [let p0
;;          [let p0
;;           (Step n n0 n1 n2 left(QuotRem n(Lin n n0 n1 n2))@
;;           left(QuotRem n(Lin n n0 n1 n2))*n2)
;;           [if (Lin n n0 left p0 right p0<Lin n n0 n1 n2 impb
;;                0<Lin n n0 left p0 right p0 impb
;;                (right(QuotRem n(Lin n n0 left p0 right p0))=0 impb
;;                 right(QuotRem n0(Lin n n0 left p0 right p0))=0 impb False)impb
;;                False)
;;            (left(QuotRem n0(Lin n n0 n1 n2))*n1@
;;            Step n0 n n2 n1 left(QuotRem n0(Lin n n0 n1 n2)))
;;            p0]]
;;          ((nat=>nat=>nat@@nat)left p0 right p0)]
;;         p]])
;;    True)
;;    (0@1)]

;; This is almost the same term as the one extracted from GcdAnd.

;; Tests

(display-gcd neterm-a 66 27)
(display-gcd neterm-d 66 27)
(display-gcd neterm-a (* 1428 1151412) (* 1428 103723))
(display-gcd neterm-d (* 1428 1151412) (* 1428 103723))
(display-gcd neterm-a (* 176478618764 12074918274841)
	     (* 176478618764 34974982375987))
(display-gcd neterm-d (* 176478618764 12074918274841)
	     (* 176478618764 34974982375987))

