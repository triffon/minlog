;; 2019-08-24.  nat.scm

;; (load "~/git/minlog/init.scm")

(display "loading nat.scm ...") (newline)

(add-algs "nat" '("Zero" "nat") '("Succ" "nat=>nat"))
(add-var-name "n" "m" "l" (py "nat")) ;l instead of k, which will be an int

(define (make-numeric-term-wrt-nat n)
  (if (= n 0)
      (pt "Zero")
      (make-term-in-app-form
       (pt "Succ")
       (make-numeric-term-wrt-nat (- n 1)))))

;; The following is in term.scm, because it is used for term-to-expr
;; (define (is-numeric-term-wrt-nat? term)
;;   (or
;;    (and (term-in-const-form? term)
;; 	(string=? "Zero" (const-to-name (term-in-const-form-to-const term))))
;;    (and (term-in-app-form? term)
;; 	(let ((op (term-in-app-form-to-op term)))
;; 	  (and (term-in-const-form? op)
;; 	       (string=? "Succ" (const-to-name
;; 				 (term-in-const-form-to-const op)))
;; 	       (is-numeric-term-wrt-nat? (term-in-app-form-to-arg term)))))))

;; (define (numeric-term-wrt-nat-to-number term)
;;   (if (equal? term (pt "Zero"))
;;       0
;;       (+ 1 (numeric-term-wrt-nat-to-number (term-in-app-form-to-arg term)))))

;; The functions make-numeric-term (used by the parser) and
;; is-numeric-term?, numeric-term-to-number (used by term-to-expr and
;; token-tree-to-string) take either pos or nat as default.

(define NAT-NUMBERS #t)

(define (make-numeric-term x)
  (if NAT-NUMBERS
      (make-numeric-term-wrt-nat x)
      (make-numeric-term-wrt-pos x)))

(define (is-numeric-term? x)
  (if NAT-NUMBERS
      (is-numeric-term-wrt-nat? x)
      (is-numeric-term-wrt-pos? x)))

(define (numeric-term-to-number x)
  (if NAT-NUMBERS
      (numeric-term-wrt-nat-to-number x)
      (numeric-term-wrt-pos-to-number x)))

(add-totality "nat")

;; This adds the c.r. predicate TotalNat with clauses
;; TotalNatZero:	TotalNat Zero
;; TotalNatSucc:	allnc nat^(TotalNat nat^ -> TotalNat(Succ nat^))

(add-totalnc "nat")
(add-co "TotalNat")
(add-co "TotalNatNc")

(add-mr-ids "TotalNat")
(add-co "TotalNatMR")

(add-eqp "nat")
(add-eqpnc "nat")
(add-co "EqPNat")
(add-co "EqPNatNc")

(add-mr-ids "EqPNat")
(add-co "EqPNatMR")

;; Code discarded 2019-05-14
;; (add-ext "nat")
;; (add-extnc "nat")

;; NatTotalVar
(set-goal "all n TotalNat n")
(use "AllTotalIntro")
(assume "n^" "Tn")
(use "Tn")
;; Proof finished
;; (cdp)
(save "NatTotalVar")

;; We collect properties of TotalNat and EqPNat, including the Nc, Co
;; and MR variants.  These are

;; EfTotalNat
;; EfTotalNatNc
;; TotalNatToCoTotal
;; TotalNatNcToCoTotalNc
;; EfCoTotalNat
;; EfCoTotalNatNc
;; EfCoTotalNatMR
;; TotalNatMRToEqD
;; TotalNatMRToTotalNcLeft
;; TotalNatMRToTotalNcRight
;; TotalNatMRRefl
;; EfCoTotalNatMR
;; TotalNatMRToCoTotalMR

;; EfEqPNat
;; EfEqPNatNc
;; EqPNatNcToEqD
;; EqPNatSym
;; EqPNatNcSym
;; EqPNatRefl
;; EqPNatNcRefl
;; EqPNatToTotalLeft
;; EqPNatNcToTotalNcLeft
;; EqPNatToTotalRight
;; EqPNatNcToTotalNcRight
;; EqPNatNcTrans
;; EqPNatNcToEq
;; EqNatToEqPNc

;; EfCoEqPNat
;; EfCoEqPNatNc
;; CoEqPNatNcToEqD
;; CoEqPNatSym
;; CoEqPNatNcSym
;; CoEqPNatRefl
;; CoEqPNatNcRefl
;; CoEqPNatToCoTotalLeft
;; CoEqPNatNcToCoTotalNcLeft
;; CoEqPNatToCoTotalRight
;; CoEqPNatNcToCoTotalNcRight
;; CoEqPNatNcTrans
;; EqPNatToCoEqP
;; EqPNatNcToCoEqPNc
;; EfEqPNatMR
;; EqPNatMRToEqDLeft
;; EqPNatMRToEqDRight
;; EqPNatNcToTotalMR
;; TotalNatMRToEqPNc
;; EqPNatMRToTotalNc
;; EqPNatMRRefl
;; EqPNatNcToEqPMR
;; EqPNatMRToEqPNcLeft
;; EqPNatMRToEqPNcRight
;; EfCoEqPNatMR
;; EqPNatMRToCoEqPMR
;; CoEqPNatNcToCoTotalMR
;; CoTotalNatMRToCoEqPNc
;; CoEqPNatMRRefl
;; CoEqPNatNcToCoEqPMR
;; CoEqPNatMRToCoEqPNcLeft
;; CoEqPNatMRToCoEqPNcRight

;; EfTotalNat
(set-goal "allnc n^(F -> TotalNat n^)")
(assume "n^" "Absurd")
(simp (pf "n^ eqd 0"))
(use "TotalNatZero")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfTotalNat")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; 0

;; EfTotalNatNc
(set-goal "allnc n^(F -> TotalNatNc n^)")
(assume "n^" "Absurd")
(simp (pf "n^ eqd 0"))
(use "TotalNatNcZero")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfTotalNatNc")

;; TotalNatToCoTotal
(set-goal "allnc n^(TotalNat n^ -> CoTotalNat n^)")
(assume "n^" "Tn")
(coind "Tn")
(assume "n^1" "Tn1")
(assert "n^1 eqd 0 ori exr n^2(TotalNat n^2 andi n^1 eqd Succ n^2)")
 (elim "Tn1")
 (intro 0)
 (use "InitEqD")
 (assume "n^2" "Tn2" "Useless")
 (intro 1)
 (intro 0 (pt "n^2"))
 (split)
 (use "Tn2")
 (use "InitEqD")
;; Assertion proved.
(assume "Disj")
(elim "Disj")
(assume "n1=0")
(intro 0)
(use "n1=0")
(assume "ExHyp")
(intro 1)
(by-assume "ExHyp" "n^2" "n2Prop")
(intro 0 (pt "n^2"))
(split)
(intro 1)
(use "n2Prop")
(use "n2Prop")
;; Proof finished.
;; (cdp)
(save "TotalNatToCoTotal")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n0]
;;  (CoRec nat=>nat)n0
;;  ([n1][if n1 (DummyL nat ysum nat) ([n2]Inr((InR nat nat)n2))])

;; TotalNatNcToCoTotalNc
(set-goal "allnc n^(TotalNatNc n^ -> CoTotalNatNc n^)")
(assume "n^" "Tn")
(coind "Tn")
(assume "n^1" "Tn1")
(assert "n^1 eqd 0 ornc exnc n^2(TotalNatNc n^2 andi n^1 eqd Succ n^2)")
 (elim "Tn1")
 (intro 0)
 (use "InitEqD")
 (assume "n^2" "Tn2" "Useless")
 (intro 1)
 (intro 0 (pt "n^2"))
 (split)
 (use "Tn2")
 (use "InitEqD")
;; Assertion proved.
(assume "Disj")
(elim "Disj")
(assume "n1=0")
(intro 0)
(use "n1=0")
(assume "ExHyp")
(intro 1)
(by-assume "ExHyp" "n^2" "n2Prop")
(intro 0 (pt "n^2"))
(split)
(intro 1)
(use "n2Prop")
(use "n2Prop")
;; Proof finished.
;; (cdp)
(save "TotalNatNcToCoTotalNc")

;; EfCoTotalNat
(set-goal "allnc n^(F -> CoTotalNat n^)")
(assume "n^" "Absurd")
(coind "Absurd")
(assume "n^1" "Useless")
(intro 0)
(simp (pf "n^1 eqd 0"))
(use "InitEqD")
(simp (pf "n^1 eqd 0"))
(use "InitEqD")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfCoTotalNat")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; (CoRec nat)(DummyL nat ysumu)

;; EfCoTotalNatNc
(set-goal "allnc n^(F -> CoTotalNatNc n^)")
(assume "n^" "Absurd")
(coind "Absurd")
(assume "n^1" "Useless")
(intro 0)
(simp (pf "n^1 eqd 0"))
(use "InitEqD")
(simp (pf "n^1 eqd 0"))
(use "InitEqD")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfCoTotalNatNc")

;; TotalNatMRToEqD
(set-goal "allnc n^1,n^2(TotalNatMR n^1 n^2 -> n^1 eqd n^2)")
(assume "n^1" "n^2" "TMRn1n2")
(elim "TMRn1n2")
;; 3,4
(use "InitEqD")
;; 4
(assume "n^3" "n^4" "Useless" "EqHyp")
(simp "EqHyp")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "TotalNatMRToEqD")

;; TotalNatMRToTotalNcLeft
(set-goal "allnc n^1,n^2(TotalNatMR n^1 n^2 -> TotalNatNc n^1)")
(assume "n^1" "n^2" "TMRHyp")
(elim "TMRHyp")
;; 3,4
(use "TotalNatNcZero")
;; 4
(assume "n^3" "n^4" "Useless")
(use "TotalNatNcSucc")
;; Proof finished.
;; (cdp)
(save "TotalNatMRToTotalNcLeft")

;; TotalNatMRToTotalNcRight
(set-goal "allnc n^1,n^2(TotalNatMR n^1 n^2 -> TotalNatNc n^2)")
(assume "n^1" "n^2" "TMRHyp")
(elim "TMRHyp")
;; 3,4
(use "TotalNatNcZero")
;; 4
(assume "n^3" "n^4" "Useless")
(use "TotalNatNcSucc")
;; Proof finished.
;; (cdp)
(save "TotalNatMRToTotalNcRight")

;; TotalNatMRRefl
(set-goal "allnc n^(TotalNat n^ -> TotalNatMR n^ n^)")
(assume "n^" "TMRHyp")
(elim "TMRHyp")
;; 3,4
(use "TotalNatZeroMR")
;; 4
(assume "n^1" "n^1" "TMRn1n1")
(use "TotalNatSuccMR")
(use "TMRn1n1")
;; Proof finished.
;; (cdp)
(save "TotalNatMRRefl")

;; EfCoTotalNatMR
(set-goal "allnc n^1,n^2(F -> CoTotalNatMR n^1 n^2)")
(assume "n^1" "n^2" "Absurd")
(coind "Absurd")
(assume "n^3" "n^4" "Useless")
(intro 0)
(simp (pf "n^3 eqd 0"))
(simp (pf "n^4 eqd 0"))
(split)
(use "InitEqD")
(use "InitEqD")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfCoTotalNatMR")

;; TotalNatMRToCoTotalMR
(set-goal "allnc n^1,n^2(TotalNatMR n^1 n^2 -> CoTotalNatMR n^1 n^2)")
(assume "n^1" "n^2" "Tn1n2")
(coind "Tn1n2")
(assume "n^3" "n^4" "Tn3n4")
(assert "n^3 eqd 0 andnc n^4 eqd0 ornc
         exr n^5,n^6(TotalNatMR n^5 n^6 andnc 
        n^3 eqd Succ n^5 andnc
        n^4 eqd Succ n^6)")
 (elim "Tn3n4")
;; 7,8
 (intro 0)
 (split)
 (use "InitEqD")
 (use "InitEqD")
;; 8
 (assume "n^5" "n^6" "Tn5n6" "Useless")
 (drop "Useless")
 (intro 1)
 (intro 0 (pt "n^5"))
 (intro 0 (pt "n^6"))
 (split)
 (use "Tn5n6")
 (split)
 (use "InitEqD")
 (use "InitEqD")
;; Assertion proved.
(assume "Disj")
(elim "Disj")
;; 22,23
(assume "Conj")
(intro 0)
(use "Conj")
;; 23
(drop "Disj")
(assume "ExHyp")
(intro 1)
(by-assume "ExHyp" "n^5" "n5Prop")
(by-assume "n5Prop" "n^6" "n5n6Prop")
(intro 0 (pt "n^5"))
(intro 0 (pt "n^6"))
(split)
(intro 1)
(use "n5n6Prop")
(use "n5n6Prop")
;; Proof finished.
;; (cdp)
(save "TotalNatMRToCoTotalMR")

;; EfEqPNat
(set-goal "allnc n^1,n^2(F -> EqPNat n^1 n^2)")
(assume "n^1" "n^2" "Absurd")
(simp (pf "n^1 eqd 0"))
(simp (pf "n^2 eqd 0"))
(use "EqPNatZero")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfEqPNat")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; 0

;; EfEqPNatNc
(set-goal "allnc n^1,n^2(F -> EqPNatNc n^1 n^2)")
(assume "n^1" "n^2" "Absurd")
(simp (pf "n^1 eqd 0"))
(simp (pf "n^2 eqd 0"))
(use "EqPNatNcZero")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfEqPNatNc")

;; EqPNatNcToEqD
(set-goal "allnc n^1,n^2(EqPNatNc n^1 n^2 -> n^1 eqd n^2)")
(assume "n^1" "n^2" "EqPn1n2")
(elim "EqPn1n2")
;; 3,4
(use "InitEqD")
;; 4
(assume "n^3" "n^4" "Useless" "IH")
(simp "IH")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "EqPNatNcToEqD")

;; EqPNatSym
(set-goal "allnc n^1,n^2(EqPNat n^1 n^2 -> EqPNat n^2 n^1)")
(assume "n^1" "n^2" "EqPn1n2")
(elim "EqPn1n2")
(use "EqPNatZero")
(assume "n^3" "n^4" "Useless" "EqPn4n3")
(use "EqPNatSucc")
(use "EqPn4n3")
;; Proof finished.
;; (cdp)
(save "EqPNatSym")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp (rename-variables neterm))
;; [n](Rec nat=>nat)n Zero([n0]Succ)

;; EqPNatNcSym
(set-goal "allnc n^1,n^2(EqPNatNc n^1 n^2 -> EqPNatNc n^2 n^1)")
(assume "n^1" "n^2" "EqPn1n2")
(elim "EqPn1n2")
(use "EqPNatNcZero")
(assume "n^3" "n^4" "Useless" "EqPn4n3")
(use "EqPNatNcSucc")
(use "EqPn4n3")
;; Proof finished.
;; (cdp)
(save "EqPNatNcSym")

;; EqPNatRefl
(set-goal "allnc n^(TotalNat n^ -> EqPNat n^ n^)")
(assume "n^" "Tn")
(elim "Tn")
(use "EqPNatZero")
(assume "n^1" "Tn1")
(use "EqPNatSucc")
;; Proof finished.
;; (cdp)
(save "EqPNatRefl")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp (rename-variables neterm))
;; [n](Rec nat=>nat)n Zero([n0]Succ)

;; EqPNatNcRefl
(set-goal "allnc n^(TotalNatNc n^ -> EqPNatNc n^ n^)")
(assume "n^" "Tn")
(elim "Tn")
(use "EqPNatNcZero")
(assume "n^1" "Tn1" "EqPHyp")
(use "EqPNatNcSucc")
(use "EqPHyp")
;; Proof finished.
;; (cdp)
(save "EqPNatNcRefl")

;; EqPNatToTotalLeft
(set-goal "allnc n^1,n^2(EqPNat n^1 n^2 -> TotalNat n^1)")
(assume "n^1" "n^2" "EqPn1n2")
(elim "EqPn1n2")
;; 3,4
(use "TotalNatZero")
;; 4
(assume "n^3" "n^4" "Useless" "IH")
(use "TotalNatSucc")
(use "IH")
;; Proof finished.
;; (cdp)
(save "EqPNatToTotalLeft")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [n](Rec nat=>nat)n Zero([n0]Succ)

;; EqPNatNcToTotalNcLeft
(set-goal "allnc n^1,n^2(EqPNatNc n^1 n^2 -> TotalNatNc n^1)")
(assume "n^1" "n^2" "EqPn1n2")
(elim "EqPn1n2")
;; 3,4
(use "TotalNatNcZero")
;; 4
(assume "n^3" "n^4" "EqPn3n4" "IH")
(use "TotalNatNcSucc")
(use "IH")
;; Proof finished.
;; (cdp)
(save "EqPNatNcToTotalNcLeft")

;; EqPNatToTotalRight
(set-goal "allnc n^1,n^2(EqPNat n^1 n^2 -> TotalNat n^2)")
(assume "n^1" "n^2" "EqPn1n2")
(elim "EqPn1n2")
;; 3,4
(use "TotalNatZero")
;; 4
(assume "n^3" "n^4" "Useless" "IH")
(use "TotalNatSucc")
(use "IH")
;; Proof finished.
;; (cdp)
(save "EqPNatToTotalRight")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [n](Rec nat=>nat)n Zero([n0]Succ)

;; EqPNatNcToTotalNcRight
(set-goal "allnc n^1,n^2(EqPNatNc n^1 n^2 -> TotalNatNc n^2)")
(assume "n^1" "n^2" "EqPn1n2")
(elim "EqPn1n2")
;; 3,4
(use "TotalNatNcZero")
;; 4
(assume "n^3" "n^4" "EqPn3n4" "IH")
(use "TotalNatNcSucc")
(use "IH")
;; Proof finished.
;; (cdp)
(save "EqPNatNcToTotalNcRight")

;; EqPNatNcTrans
(set-goal
 "allnc n^1,n^2,n^3(EqPNatNc n^1 n^2 -> EqPNatNc n^2 n^3 -> EqPNatNc n^1 n^3)")
(assume "n^1" "n^2" "n^3" "EqPn1n2" "EqPn2n3")
(simp (pf "n^1 eqd n^2"))
(simp (pf "n^2 eqd n^3"))
(use "EqPNatNcRefl")
(use "EqPNatNcToTotalNcRight" (pt "n^2"))
(use "EqPn2n3")
(use "EqPNatNcToEqD")
(use "EqPn2n3")
(use "EqPNatNcToEqD")
(use "EqPn1n2")
;; Proof finished.
;; (cdp)
(save "EqPNatNcTrans")

;; EqPNatNcToEq
(set-goal "allnc n^1,n^2(EqPNatNc n^1 n^2 -> n^1=n^2)")
(assume "n^1" "n^2" "EqPn1n2")
(elim "EqPn1n2")
(use "Truth")
(assume "n^13" "n^4" "Useless" "IH")
(use "IH")
;; Proof finished.
;; (cdp)
(save "EqPNatNcToEq")

;; EqNatToEqPNc
(set-goal "allnc n^1(TotalNatNc n^1 -> allnc n^2(TotalNatNc n^2 ->
 n^1=n^2 -> EqPNatNc n^1 n^2))")
(assume "n^1" "Tn1")
(elim "Tn1")
;; 3,4
(assume "n^2" "Tn2")
(elim "Tn2")
(assume "Useless")
(use "EqPNatNcZero")
;; 7
(assume "n^3" "Tn3" "Useless" "Absurd")
(use "EfEqPNatNc")
(use "Absurd")
;; 4
(assume "n^2" "Tn2" "IH" "n^3" "Tn3")
(elim "Tn3")
(assume "Absurd")
(use "EfEqPNatNc")
(use "Absurd")
;; 13
(assume "n^4" "Tn4" "Useless" "n2=n4")
(use "EqPNatNcSucc")
(use "IH")
(use "Tn4")
(use "n2=n4")
;; Proof finished.
;; (cdp)
(save "EqNatToEqPNc")

;; EfCoEqPNat
(set-goal "allnc n^1,n^2(F -> CoEqPNat n^1 n^2)")
(assume "n^1" "n^2" "Absurd")
(coind "Absurd")
(assume "n^3" "n^4" "Useless")
(intro 0)
(simp (pf "n^3 eqd 0"))
(simp (pf "n^4 eqd 0"))
(split)
(use "InitEqD")
(use "InitEqD")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfCoEqPNat")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; (CoRec nat)(DummyL nat ysumu)
(pp (nt (undelay-delayed-corec neterm 1)))
;; 0

;; EfCoEqPNatNc
(set-goal "allnc n^1,n^2(F -> CoEqPNatNc n^1 n^2)")
(assume "n^1" "n^2" "Absurd")
(coind "Absurd")
(assume "n^3" "n^4" "Useless")
(intro 0)
(simp (pf "n^3 eqd 0"))
(simp (pf "n^4 eqd 0"))
(split)
(use "InitEqD")
(use "InitEqD")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfCoEqPNatNc")

;; CoEqPNatNcToEqD
(set-goal "allnc n^1,n^2(CoEqPNatNc n^1 n^2 -> n^1 eqd n^2)")
(use (make-proof-in-aconst-form (finalg-to-bisim-aconst (py "nat"))))
;; Proof finished.
;; (cdp)
(save "CoEqPNatNcToEqD")

;; CoEqPNatSym
(set-goal "allnc n^1,n^2(CoEqPNat n^1 n^2 -> CoEqPNat n^2 n^1)")
(assume "n^1" "n^2" "n1~n2")
(coind "n1~n2")
(assume "n^3" "n^4" "n4~n3")
(inst-with-to
 (make-proof-in-aconst-form
  (coidpredconst-to-closure-aconst
   (predicate-form-to-predicate (pf "CoEqPNat n^2 n^1"))))
 (pt "n^4") (pt "n^3") "n4~n3" "Inst")
(elim "Inst")
;; 8,9
(drop "Inst")
(assume "Conj")
(intro 0)
(split)
(use "Conj")
(use "Conj")
;; 9
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "n^5" "n5Prop")
(by-assume "n5Prop" "n^6" "n5n6Prop")
(intro 1)
(intro 0 (pt "n^6"))
(intro 0 (pt "n^5"))
(split)
(intro 1)
(use "n5n6Prop")
(split)
(use "n5n6Prop")
(use "n5n6Prop")
;; Proof finished.
;; (cdp)
(save "CoEqPNatSym")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n]
;;  (CoRec nat=>nat)n
;;  ([n0][if (Des n0) (DummyL nat ysum nat) ([n1]Inr((InR nat nat)n1))])

;; CoEqPNatNcSym
(set-goal "allnc n^1,n^2(CoEqPNatNc n^1 n^2 -> CoEqPNatNc n^2 n^1)")
(assume "n^1" "n^2" "n1~n2")
(coind "n1~n2")
(assume "n^3" "n^4" "n4~n3")
(inst-with-to
 (make-proof-in-aconst-form
  (coidpredconst-to-closure-aconst
   (predicate-form-to-predicate (pf "CoEqPNatNc n^2 n^1"))))
 (pt "n^4") (pt "n^3") "n4~n3" "Inst")
(elim "Inst")
;; 8,9
(drop "Inst")
(assume "Conj")
(intro 0)
(split)
(use "Conj")
(use "Conj")
;; 9
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "n^5" "n5Prop")
(by-assume "n5Prop" "n^6" "n5n6Prop")
(intro 1)
(intro 0 (pt "n^6"))
(intro 0 (pt "n^5"))
(split)
(intro 1)
(use "n5n6Prop")
(split)
(use "n5n6Prop")
(use "n5n6Prop")
;; Proof finished.
;; (cdp)
(save "CoEqPNatNcSym")

;; CoEqPNatRefl
(set-goal "allnc n^(CoTotalNat n^ -> CoEqPNat n^ n^)")
(assert "allnc n^1,n^2(CoTotalNat n^1 andi n^1 eqd n^2 -> CoEqPNat n^1 n^2)")
(assume "n^1" "n^2")
(coind)
(assume "n^3" "n^4" "Conj")
(inst-with-to "Conj" 'left "CoTn3")
(inst-with-to "Conj" 'right "n3=n4")
(drop "Conj")
(simp "<-" "n3=n4")
(drop "n3=n4")
(inst-with-to "CoTotalNatClause" (pt "n^3") "CoTn3" "Inst")
(elim "Inst")
;; 16,17
(drop "Inst")
(assume "n3=0")
(intro 0)
(split)
(use "n3=0")
(use "n3=0")
;; 17
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "n^5" "n5Prop")
(intro 1)
(intro 0 (pt "n^5"))
(intro 0 (pt "n^5"))
(split)
(intro 1)
(split)
(use "n5Prop")
(use "InitEqD")
(split)
(use "n5Prop")
(use "n5Prop")
;; 2
(assume "Assertion" "n^" "CoTn")
(use "Assertion")
(split)
(use "CoTn")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "CoEqPNatRefl")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n]
;;  (CoRec nat=>nat)n
;;  ([n0][if (Des n0) (DummyL nat ysum nat) ([n1]Inr((InR nat nat)n1))])

;; CoEqPNatNcRefl
(set-goal "allnc n^(CoTotalNatNc n^ -> CoEqPNatNc n^ n^)")
(assert
 "allnc n^1,n^2(CoTotalNatNc n^1 andi n^1 eqd n^2 -> CoEqPNatNc n^1 n^2)")
(assume "n^1" "n^2")
(coind)
(assume "n^3" "n^4" "Conj")
(inst-with-to "Conj" 'left "CoTn3")
(inst-with-to "Conj" 'right "n3=n4")
(drop "Conj")
(simp "<-" "n3=n4")
(drop "n3=n4")
(inst-with-to "CoTotalNatClause" (pt "n^3") "CoTn3" "Inst")
(elim "Inst")
;; 16,17
(drop "Inst")
(assume "n3=0")
(intro 0)
(split)
(use "n3=0")
(use "n3=0")
;; 17
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "n^5" "n5Prop")
(intro 1)
(intro 0 (pt "n^5"))
(intro 0 (pt "n^5"))
(split)
(intro 1)
(split)
(use "n5Prop")
(use "InitEqD")
(split)
(use "n5Prop")
(use "n5Prop")
;; 2
(assume "Assertion" "n^" "CoTn")
(use "Assertion")
(split)
(use "CoTn")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "CoEqPNatNcRefl")

;; CoEqPNatToCoTotalLeft
(set-goal "allnc n^1,n^2(CoEqPNat n^1 n^2 -> CoTotalNat n^1)")
(assume "n^1" "n^2" "n1~n2")
(use (imp-formulas-to-coind-proof
      (pf "exr n^3 CoEqPNat n^1 n^3 -> CoTotalNat n^1")))
;; 3,4
(assume "n^3" "ExHyp3")
(by-assume "ExHyp3" "n^4" "n3~n4")
(inst-with-to "CoEqPNatClause" (pt "n^3") (pt "n^4") "n3~n4" "Inst")
(elim "Inst")
;; 11,12
(drop "Inst")
(assume "Conj")
(intro 0)
(use "Conj")
;; 12
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "n^5" "n5Prop")
(by-assume "n5Prop" "n^6" "n5n6Prop")
(intro 1)
(intro 0 (pt "n^5"))
(split)
(intro 1)
(intro 0 (pt "n^6"))
(use "n5n6Prop")
(use "n5n6Prop")
;; 4
(intro 0 (pt "n^2"))
(use "n1~n2")
;; Proof finished.
;; (cdp)
(save "CoEqPNatToCoTotalLeft")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n]
;;  (CoRec nat=>nat)n
;;  ([n0][if (Des n0) (DummyL nat ysum nat) ([n1]Inr((InR nat nat)n1))])

;; CoEqPNatNcToCoTotalNcLeft
(set-goal "allnc n^1,n^2(CoEqPNatNc n^1 n^2 -> CoTotalNatNc n^1)")
(assume "n^1" "n^2" "n1~n2")
(use (imp-formulas-to-coind-proof
      (pf "exr n^3 CoEqPNatNc n^1 n^3 -> CoTotalNatNc n^1")))
;; 3,4
(assume "n^3" "ExHyp3")
(by-assume "ExHyp3" "n^4" "n3~n4")
(inst-with-to "CoEqPNatNcClause" (pt "n^3") (pt "n^4") "n3~n4" "Inst")
(elim "Inst")
;; 11,12
(drop "Inst")
(assume "Conj")
(intro 0)
(use "Conj")
;; 12
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "n^5" "n5Prop")
(by-assume "n5Prop" "n^6" "n5n6Prop")
(intro 1)
(intro 0 (pt "n^5"))
(split)
(intro 1)
(intro 0 (pt "n^6"))
(use "n5n6Prop")
(use "n5n6Prop")
;; 4
(intro 0 (pt "n^2"))
(use "n1~n2")
;; Proof finished.
;; (cdp)
(save "CoEqPNatNcToCoTotalNcLeft")

;; CoEqPNatToCoTotalRight
(set-goal "allnc n^1,n^2(CoEqPNat n^1 n^2 -> CoTotalNat n^2)")
(assume "n^1" "n^2" "n1~n2")
(use (imp-formulas-to-coind-proof
      (pf "exr n^3 CoEqPNat n^3 n^2 -> CoTotalNat n^2")))
;; 3,4
(assume "n^3" "ExHyp3")
(by-assume "ExHyp3" "n^4" "n4~n3")
(inst-with-to "CoEqPNatClause" (pt "n^4") (pt "n^3") "n4~n3" "Inst")
(elim "Inst")
;; 11,12
(drop "Inst")
(assume "Conj")
(intro 0)
(use "Conj")
;; 12
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "n^5" "n5Prop")
(by-assume "n5Prop" "n^6" "n5n6Prop")
(intro 1)
(intro 0 (pt "n^6"))
(split)
(intro 1)
(intro 0 (pt "n^5"))
(use "n5n6Prop")
(use "n5n6Prop")
;; 4
(intro 0 (pt "n^1"))
(use "n1~n2")
;; Proof finished.
;; (cdp)
(save "CoEqPNatToCoTotalRight")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n]
;;  (CoRec nat=>nat)n
;;  ([n0][if (Des n0) (DummyL nat ysum nat) ([n1]Inr((InR nat nat)n1))])

;; CoEqPNatNcToCoTotalNcRight
(set-goal "allnc n^1,n^2(CoEqPNatNc n^1 n^2 -> CoTotalNatNc n^2)")
(assume "n^1" "n^2" "n1~n2")
(use (imp-formulas-to-coind-proof
      (pf "exr n^3 CoEqPNatNc n^3 n^2 -> CoTotalNatNc n^2")))
;; 3,4
(assume "n^4" "ExHyp3")
(by-assume "ExHyp3" "n^3" "n3~n4")
(inst-with-to "CoEqPNatNcClause" (pt "n^3") (pt "n^4") "n3~n4" "Inst")
(elim "Inst")
;; 11,12
(drop "Inst")
(assume "Conj")
(intro 0)
(use "Conj")
;; 12
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "n^5" "n5Prop")
(by-assume "n5Prop" "n^6" "n5n6Prop")
(intro 1)
(intro 0 (pt "n^6"))
(split)
(intro 1)
(intro 0 (pt "n^5"))
(use "n5n6Prop")
(use "n5n6Prop")
;; 4
(intro 0 (pt "n^1"))
(use "n1~n2")
;; Proof finished.
;; (cdp)
(save "CoEqPNatNcToCoTotalNcRight")

;; CoEqPNatNcTrans
(set-goal "allnc n^1,n^2,n^3(CoEqPNatNc n^1 n^2 -> CoEqPNatNc n^2 n^3 ->
                             CoEqPNatNc n^1 n^3)")
(assume "n^1" "n^2" "n^3" "CoEqPn1n2" "CoEqPn2n3")
(simp (pf "n^1 eqd n^2"))
(simp (pf "n^2 eqd n^3"))
(use "CoEqPNatNcRefl")
(use "CoEqPNatNcToCoTotalNcRight" (pt "n^2"))
(use "CoEqPn2n3")
(use "CoEqPNatNcToEqD")
(use "CoEqPn2n3")
(use "CoEqPNatNcToEqD")
(use "CoEqPn1n2")
;; Proof finished.
;; (cdp)
(save "CoEqPNatNcTrans")

;; EqPNatToCoEqP
(set-goal "allnc n^1,n^2(EqPNat n^1 n^2 -> CoEqPNat n^1 n^2)")
(assume "n^1" "n^2" "EqPn1n2")
(coind "EqPn1n2")
(assume "n^3" "n^4" "EqPn3n4")
(elim "EqPn3n4")
;; 5,6
(intro 0)
(split)
(use "InitEqD")
(use "InitEqD")
;; 6
(assume "n^5" "n^6" "EqPn5n6" "Disj")
(elim "Disj")
;; 11,12
(drop "Disj")
(assume "Conj")
(intro 1)
(intro 0 (pt "n^5"))
(intro 0 (pt "n^6"))
(split)
(intro 1)
(use "EqPn5n6")
(split)
(use "InitEqD")
(use "InitEqD")
;; 12
(drop "Disj")
(assume "ExHyp")
(by-assume "ExHyp" "n^7" "n7Prop")
(by-assume "n7Prop" "n^8" "n7n8Prop")
(intro 1)
(intro 0 (pt "n^5"))
(intro 0 (pt "n^6"))
(split)
(intro 1)
(use "EqPn5n6")
(split)
(use "InitEqD")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "EqPNatToCoEqP")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n]
;;  (CoRec nat=>nat)n
;;  ([n0]
;;    (Rec nat=>uysum(nat ysum nat))n0(DummyL nat ysum nat)
;;    ([n1,(uysum(nat ysum nat))]Inr((InR nat nat)n1)))

;; EqPNatNcToCoEqPNc
(set-goal "allnc n^1,n^2(EqPNatNc n^1 n^2 -> CoEqPNatNc n^1 n^2)")
(assume "n^1" "n^2" "EqPn1n2")
(coind "EqPn1n2")
(assume "n^3" "n^4" "EqPn3n4")
(elim "EqPn3n4")
;; 5,6
(intro 0)
(split)
(use "InitEqD")
(use "InitEqD")
;; 6
(assume "n^5" "n^6" "EqPn5n6" "Disj")
(elim "Disj")
;; 11,12
(drop "Disj")
(assume "Conj")
(intro 1)
(intro 0 (pt "n^5"))
(intro 0 (pt "n^6"))
(split)
(intro 1)
(use "EqPn5n6")
(split)
(use "InitEqD")
(use "InitEqD")
;; 12
(drop "Disj")
(assume "ExHyp")
(by-assume "ExHyp" "n^7" "n7Prop")
(by-assume "n7Prop" "n^8" "n7n8Prop")
(intro 1)
(intro 0 (pt "n^5"))
(intro 0 (pt "n^6"))
(split)
(intro 1)
(use "EqPn5n6")
(split)
(use "InitEqD")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "EqPNatNcToCoEqPNc")

;; EfEqPNatMR
(set-goal "allnc n^1,n^2,n^3(F -> EqPNatMR n^1 n^2 n^3)")
(assume "n^1" "n^2" "n^3" "Absurd")
(simp (pf "n^1 eqd 0"))
(simp (pf "n^2 eqd 0"))
(simp (pf "n^3 eqd 0"))
(use "EqPNatZeroMR")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfEqPNatMR")

;; EqPNatMRToEqDLeft
(set-goal "allnc n^1,n^2,n^3(EqPNatMR n^1 n^2 n^3 -> n^1 eqd n^2)")
(assume "n^1" "n^2" "n^3" "EqPHyp")
(elim "EqPHyp")
(use "InitEqD")
(assume "n^4" "n^5" "n^6" "Useless" "EqDHyp")
(simp "EqDHyp")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "EqPNatMRToEqDLeft")

;; EqPNatMRToEqDRight
(set-goal "allnc n^1,n^2,n^3(EqPNatMR n^1 n^2 n^3 -> n^2 eqd n^3)")
(assume "n^1" "n^2" "n^3" "EqPHyp")
(elim "EqPHyp")
(use "InitEqD")
(assume "n^4" "n^5" "n^6" "Useless" "EqDHyp")
(simp "EqDHyp")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "EqPNatMRToEqDRight")

;; EqPNatNcToTotalMR
(set-goal "allnc n^1,n^2(EqPNatNc n^1 n^2 -> TotalNatMR n^1 n^2)")
(assume "n^1" "n^2" "EqPn1n2")
(elim "EqPn1n2")
(use "TotalNatZeroMR")
(assume "n^3" "n^4" "Useless")
(use "TotalNatSuccMR")
;; Proof finished.
;; (cdp)
(save "EqPNatNcToTotalMR")

;; TotalNatMRToEqPNc
(set-goal "allnc n^1,n^2(TotalNatMR n^1 n^2 -> EqPNatNc n^1 n^2)")
(assume "n^1" "n^2" "TMRn1n2")
(elim "TMRn1n2")
(use "EqPNatNcZero")
(assume "n^3" "n^4" "Useless")
(use "EqPNatNcSucc")
;; Proof finished.
;; (cdp)
(save "TotalNatMRToEqPNc")

;; EqPNatMRToTotalNc
(set-goal "allnc n^1,n^2,n^3(EqPNatMR n^1 n^2 n^3 -> TotalNatNc n^3)")
(assume "n^1" "n^2" "n^3" "EqPHyp")
(elim "EqPHyp")
(use "TotalNatNcZero")
(assume "n^4" "n^5" "n^6" "Useless")
(use "TotalNatNcSucc")
;; Proof finished.
;; (cdp)
(save "EqPNatMRToTotalNc")

;; EqPNatMRRefl
(set-goal "allnc n^(TotalNatNc n^ -> EqPNatMR n^ n^ n^)")
(assume "n^" "Tn")
(elim "Tn")
(use "EqPNatZeroMR")
(assume "n^1" "IH")
(use "EqPNatSuccMR")
;; Proof finished.
;; (cdp)
(save "EqPNatMRRefl")

;; EqPNatNcToEqPMR
(set-goal "allnc n^1,n^2,n^3(EqPNatNc n^1 n^2 -> EqPNatNc n^2 n^3 ->
                             EqPNatMR n^1 n^2 n^3)")
(assume "n^1" "n^2" "n^3" "EqPn1n2" "EqPn2n3")
(simp (pf "n^1 eqd n^2"))
(simp (pf "n^2 eqd n^3"))
(use "EqPNatMRRefl")
(use "EqPNatNcToTotalNcRight" (pt "n^2"))
(use "EqPn2n3")
(use "EqPNatNcToEqD")
(use "EqPn2n3")
(use "EqPNatNcToEqD")
(use "EqPn1n2")
;; Proof finished.
;; (cdp)
(save "EqPNatNcToEqPMR")

;; EqPNatMRToEqPNcLeft
(set-goal "allnc n^1,n^2,n^3(EqPNatMR n^1 n^2 n^3 -> EqPNatNc n^1 n^2)")
(assume "n^1" "n^2" "n^3" "EqPMRHyp")
(elim "EqPMRHyp")
(use "EqPNatNcZero")
(assume "n^4" "n^5" "n^6" "Useless" "EqPn4n5")
(use "EqPNatNcSucc")
(use "EqPn4n5")
;; Proof finished.
;; (cdp)
(save "EqPNatMRToEqPNcLeft")

;; EqPNatMRToEqPNcRight
(set-goal "allnc n^1,n^2,n^3(EqPNatMR n^1 n^2 n^3 -> EqPNatNc n^2 n^3)")
(assume "n^1" "n^2" "n^3" "EqPMRHyp")
(elim "EqPMRHyp")
(use "EqPNatNcZero")
(assume "n^4" "n^5" "n^6" "Useless" "EqPn5n6")
(use "EqPNatNcSucc")
(use "EqPn5n6")
;; Proof finished.
;; (cdp)
(save "EqPNatMRToEqPNcRight")

;; EfCoEqPNatMR
(set-goal "allnc n^1,n^2,n^3(F -> CoEqPNatMR n^1 n^2 n^3)")
(assume "n^1" "n^2" "n^3" "Absurd")
(coind "Absurd")
(assume "n^4" "n^5" "n^6" "Useless")
(intro 0)
(simp (pf "n^4 eqd 0"))
(simp (pf "n^5 eqd 0"))
(simp (pf "n^6 eqd 0"))
(split)
(use "InitEqD")
(split)
(use "InitEqD")
(use "InitEqD")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfCoEqPNatMR")

;; EqPNatMRToCoEqPMR
(set-goal "allnc n^1,n^2,n^3(
 EqPNatMR n^1 n^2 n^3 -> CoEqPNatMR n^1 n^2 n^3)")
(assume "n^1" "n^2" "n^3" "Tn1n2n3")
(coind "Tn1n2n3")
(assume "n^4" "n^5" "n^6" "Tn4n5n6")
(assert "n^4 eqd 0 andnc n^5 eqd 0 andnc n^6 eqd 0 ornc
         exr n^7,n^8,n^9(EqPNatMR n^7 n^8 n^9 andnc 
         n^4 eqd Succ n^7 andnc
         n^5 eqd Succ n^8 andnc
         n^6 eqd Succ n^9)")
 (elim "Tn4n5n6")
;; 7,8
 (intro 0)
 (split)
 (use "InitEqD")
 (split)
 (use "InitEqD")
 (use "InitEqD")
;; 8
 (assume "n^7" "n^8" "n^9" "Tn7n8n9" "Useless")
 (drop "Useless")
 (intro 1)
 (intro 0 (pt "n^7"))
 (intro 0 (pt "n^8"))
 (intro 0 (pt "n^9"))
 (split)
 (use "Tn7n8n9")
 (split)
 (use "InitEqD")
 (split)
 (use "InitEqD")
 (use "InitEqD")
;; Assertion proved.
(assume "Disj")
(elim "Disj")
;; 27,28
(assume "Conj")
(intro 0)
(use "Conj")
;; 28
(drop "Disj")
(assume "ExHyp")
(intro 1)
(by-assume "ExHyp" "n^7" "n7Prop")
(by-assume "n7Prop" "n^8" "n7n8Prop")
(by-assume "n7n8Prop" "n^9" "n7n8n9Prop")
(intro 0 (pt "n^7"))
(intro 0 (pt "n^8"))
(intro 0 (pt "n^9"))
(split)
(intro 1)
(use "n7n8n9Prop")
(use "n7n8n9Prop")
;; Proof finished.
;; (cdp)
(save "EqPNatMRToCoEqPMR")

;; CoEqPNatNcToCoTotalMR
(set-goal "allnc n^1,n^2(CoEqPNatNc n^1 n^2 -> CoTotalNatMR n^1 n^2)")
(assume "n^1" "n^2" "n1~n2")
(use (make-proof-in-aconst-form
      (imp-formulas-to-gfp-aconst
       (pf "CoEqPNatNc n^1 n^2 -> CoTotalNatMR n^1 n^2"))))
;; 3,4
(use "n1~n2")
;; 4
(assume "n^3" "n^4" "n3~n4")
;; use the closure axiom for CoEqPNat
;; (pp "CoEqPNatNcClause")
(inst-with-to "CoEqPNatNcClause" (pt "n^3") (pt "n^4") "n3~n4"
	      "CoEqPNatNcClauseInst")
(elim "CoEqPNatNcClauseInst")
;; 8,9
(drop "CoEqPNatNcClauseInst")
(assume "Conj")
(intro 0)
(split)
(use "Conj")
(use "Conj")
;; 9
(drop "CoEqPNatNcClauseInst")
(assume "ExHyp")
(by-assume "ExHyp" "n^5" "n5Prop")
(by-assume "n5Prop" "n^6" "n5n6Prop")
(intro 1)
(intro 0 (pt "n^5"))
(intro 0 (pt "n^6"))
(split)
(intro 1)
(use "n5n6Prop")
(split)
(use "n5n6Prop")
(use "n5n6Prop")
;; Proof finished.
;; (cdp)
(save "CoEqPNatNcToCoTotalMR")

;; CoTotalNatMRToCoEqPNc
(set-goal "allnc n^1,n^2(CoTotalNatMR n^1 n^2 -> CoEqPNatNc n^1 n^2)")
(assume "n^1" "n^2" "CoTn1n2")
(use (make-proof-in-aconst-form
      (imp-formulas-to-gfp-aconst
       (pf "CoTotalNatMR n^1 n^2 -> CoEqPNatNc n^1 n^2"))))
;; 3,4
(use "CoTn1n2")
;; 4
(assume "n^3" "n^4" "CoTn3n4")
;; use the closure axiom for CoTotalNatMR
(inst-with-to "CoTotalNatMRClause" (pt "n^3") (pt "n^4") "CoTn3n4"
	      "CoTotalNatMRClauseInst")
(elim "CoTotalNatMRClauseInst")
;; 8,9
(drop "CoTotalNatMRClauseInst")
(assume "EqConj")
(intro 0)
(split)
(use "EqConj")
(use "EqConj")
;; 9
(drop "CoTotalNatMRClauseInst")
(assume "ExHyp")
(by-assume "ExHyp" "n^5" "n5Prop")
(by-assume "n5Prop" "n^6" "n5n6Prop")
(intro 1)
(intro 0 (pt "n^5"))
(intro 0 (pt "n^6"))
(split)
(intro 1)
(use "n5n6Prop")
(split)
(use "n5n6Prop")
(use "n5n6Prop")
;; Proof finished.
;; (cdp)
(save "CoTotalNatMRToCoEqPNc")

;; CoEqPNatMRRefl
(set-goal "allnc n^(CoTotalNatNc n^ -> CoEqPNatMR n^ n^ n^)")
(assert
 "allnc n^1,n^2,n^3(CoTotalNatNc n^1 andnc n^1 eqd n^2 andnc n^2 eqd n^3 ->
                    CoEqPNatMR n^1 n^2 n^3)")
(assume "n^1" "n^2" "n^3")
(coind)
(assume "n^4" "n^5" "n^6" "Conj")
(inst-with-to "Conj" 'left "CoTn4")
(inst-with-to "Conj" 'right "Conj34")
(inst-with-to "Conj34" 'left "n4=n5")
(inst-with-to "Conj34" 'right "n5=n6")
(drop "Conj" "Conj34")
(simp "<-" "n5=n6")
(simp "<-" "n4=n5")
(drop "n5=n6" "n4=n5")
(inst-with-to "CoTotalNatClause" (pt "n^4") "CoTn4" "Inst")
(elim "Inst")
;; 20,21
(drop "Inst")
(assume "n4=0")
(intro 0)
(split)
(use "n4=0")
(split)
(use "n4=0")
(use "n4=0")
;; 21
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "n^7" "n7Prop")
(intro 1)
(intro 0 (pt "n^7"))
(intro 0 (pt "n^7"))
(intro 0 (pt "n^7"))
(split)
(intro 1)
(split)
(use "n7Prop")
(split)
(use "InitEqD")
(use "InitEqD")
(split)
(use "n7Prop")
(split)
(use "n7Prop")
(use "n7Prop")
;; 2
(assume "Assertion" "n^" "CoTn")
(use "Assertion")
(split)
(use "CoTn")
(split)
(use "InitEqD")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "CoEqPNatMRRefl")

;; CoEqPNatNcToCoEqPMR
(set-goal "allnc n^1,n^2,n^3(CoEqPNatNc n^1 n^2 -> CoEqPNatNc n^2 n^3 ->
                             CoEqPNatMR n^1 n^2 n^3)")
(assume "n^1" "n^2" "n^3" "CoEqPn1n2" "CoEqPn2n3")
(simp (pf "n^1 eqd n^2"))
(simp (pf "n^2 eqd n^3"))
(use "CoEqPNatMRRefl")
(use "CoEqPNatNcToCoTotalNcRight" (pt "n^2"))
(use "CoEqPn2n3")
(use "CoEqPNatNcToEqD")
(use "CoEqPn2n3")
(use "CoEqPNatNcToEqD")
(use "CoEqPn1n2")
;; Proof finished.
;; (cdp)
(save "CoEqPNatNcToCoEqPMR")

;; CoEqPNatMRToCoEqPNcLeft
(set-goal "allnc n^1,n^2,n^3(CoEqPNatMR n^1 n^2 n^3 -> CoEqPNatNc n^1 n^2)")
(assume "n^1" "n^2" "n^3" "CoEqPMRn1n2n3")
(use (imp-formulas-to-coind-proof
      (pf "exr n^3 CoEqPNatMR n^1 n^2 n^3 -> CoEqPNatNc n^1 n^2")))
;; 3,4
(assume "n^4" "n^5" "ExHyp45")
(by-assume "ExHyp45" "n^6" "CoEqPMRn4n5n6")
;; (pp "CoEqPNatMRClause")
(inst-with-to "CoEqPNatMRClause"
	      (pt "n^4") (pt "n^5") (pt "n^6") "CoEqPMRn4n5n6" "Inst")
(elim "Inst")
;; 11,12
(drop "Inst")
(assume "Conj")
(intro 0)
(split)
(use "Conj")
(use "Conj")
;; 12
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "n^7" "n7Prop")
(by-assume "n7Prop" "n^8" "n7n8Prop")
(by-assume "n7n8Prop" "n^9" "n7n8n9Prop")
(intro 1)
(intro 0 (pt "n^7"))
(intro 0 (pt "n^8"))
(split)
(intro 1)
(intro 0 (pt "n^9"))
(use "n7n8n9Prop")
(split)
(use "n7n8n9Prop")
(use "n7n8n9Prop")
;; 4
(intro 0 (pt "n^3"))
(use "CoEqPMRn1n2n3")
;; Proof finished.
;; (cdp)
(save "CoEqPNatMRToCoEqPNcLeft")

;; CoEqPNatMRToCoEqPNcRight
(set-goal "allnc n^1,n^2,n^3(CoEqPNatMR n^1 n^2 n^3 -> CoEqPNatNc n^2 n^3)")
(assume "n^1" "n^2" "n^3" "CoEqPMRn1n2n3")
(use (imp-formulas-to-coind-proof
      (pf "exr n^1 CoEqPNatMR n^1 n^2 n^3 -> CoEqPNatNc n^2 n^3")))
;; 3,4
(assume "n^5" "n^6" "ExHyp56")
(by-assume "ExHyp56" "n^4" "CoEqPMRn4n5n6")
;; (pp "CoEqPNatMRClause")
(inst-with-to "CoEqPNatMRClause"
	      (pt "n^4") (pt "n^5") (pt "n^6") "CoEqPMRn4n5n6" "Inst")
(elim "Inst")
;; 11,12
(drop "Inst")
(assume "Conj")
(intro 0)
(split)
(use "Conj")
(use "Conj")
;; 12
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "n^7" "n7Prop")
(by-assume "n7Prop" "n^8" "n7n8Prop")
(by-assume "n7n8Prop" "n^9" "n7n8n9Prop")
(intro 1)
(intro 0 (pt "n^8"))
(intro 0 (pt "n^9"))
(split)
(intro 1)
(intro 0 (pt "n^7"))
(use "n7n8n9Prop")
(split)
(use "n7n8n9Prop")
(use "n7n8n9Prop")
;; 4
(intro 0 (pt "n^1"))
(use "CoEqPMRn1n2n3")
;; Proof finished.
;; (cdp)
(save "CoEqPNatMRToCoEqPNcRight")

;; This concludes the coeection of properties of TotalNat and EqPNat.

;; Program constants.

(add-program-constant "NatPlus" (py "nat=>nat=>nat"))
(add-program-constant "NatTimes" (py "nat=>nat=>nat"))
(add-program-constant "NatLt" (py "nat=>nat=>boole"))
(add-program-constant "NatLe" (py "nat=>nat=>boole"))
(add-program-constant "Pred" (py "nat=>nat"))
(add-program-constant "NatMinus" (py "nat=>nat=>nat"))
(add-program-constant "NatMax" (py "nat=>nat=>nat"))
(add-program-constant "NatMin" (py "nat=>nat=>nat"))
(add-program-constant "AllBNat" (py "nat=>(nat=>boole)=>boole"))
(add-program-constant "ExBNat" (py "nat=>(nat=>boole)=>boole"))
(add-program-constant "NatLeast" (py "nat=>(nat=>boole)=>nat"))
(add-program-constant "NatLeastUp" (py "nat=>nat=>(nat=>boole)=>nat"))

;; Tokens used by the parser.

(define (add-nat-tokens)
  (let* ((make-type-string
	  (lambda (type op-string type-strings)
	    (let* ((string (type-to-string type))
		   (l (string->list string)))
	      (if (member string type-strings)
		  (list->string (cons (char-upcase (car l)) (cdr l)))
		  (myerror op-string "unexpected type" type)))))
	 (tc ;term-creator
	  (lambda (op-string . type-strings)
	    (lambda (x y)
	      (let* ((type (term-to-type x))
		     (type-string
		      (make-type-string type op-string type-strings))
		     (internal-name (string-append type-string op-string)))
		(mk-term-in-app-form
		 (make-term-in-const-form
		  (pconst-name-to-pconst internal-name))
		 x y))))))
    (add-token "+" 'add-op (tc "Plus" "nat"))
    (add-token "*" 'mul-op (tc "Times" "nat"))
    (add-token "<" 'rel-op (tc "Lt" "nat"))
    (add-token "<=" 'rel-op (tc "Le" "nat"))
    (add-token "--" 'add-op (tc "Minus" "nat"))
    (add-token "max" 'mul-op (tc "Max" "nat"))
    (add-token "min" 'mul-op (tc "Min" "nat"))))

(add-nat-tokens)

;; (add-nat-display) updates DISPLAY-FUNCTIONS, so that it uses the
;; tokens introduced by (add-nat-tokens).

(define (add-nat-display)
  (let ((dc ;display-creator
	 (lambda (name display-string token-type)
	   (lambda (x)
	     (let ((op (term-in-app-form-to-final-op x))
		   (args (term-in-app-form-to-args x)))
	       (if (and (term-in-const-form? op)
			(string=? name (const-to-name
					(term-in-const-form-to-const op)))
			(= 2 (length args)))
		   (list token-type display-string
			 (term-to-token-tree (term-to-original (car args)))
			 (term-to-token-tree (term-to-original (cadr args))))
		   #f))))))
    (add-display (py "nat") (dc "NatPlus" "+" 'add-op))
    (add-display (py "nat") (dc "NatTimes" "*" 'mul-op))
    (add-display (py "boole") (dc "NatLt" "<" 'rel-op))
    (add-display (py "boole") (dc "NatLe" "<=" 'rel-op))
    (add-display (py "nat") (dc "NatMinus" "--" 'add-op))
    (add-display (py "nat") (dc "NatMax" "max" 'mul-op))
    (add-display (py "nat") (dc "NatMin" "min" 'mul-op))))

(add-nat-display)

;; (remove-nat-tokens) removes all tokens and from DISPLAY-FUNCTIONS
;; all items (nat proc).

(define (remove-nat-tokens)
  (remove-token "+")
  (remove-token "*")
  (remove-token "<")
  (remove-token "<=")
  (remove-token "--")
  (remove-token "max")
  (remove-token "min")
  (set! DISPLAY-FUNCTIONS
	(list-transform-positive DISPLAY-FUNCTIONS
	  (lambda (item)
	    (not (equal? (car item) (py "nat")))))))

;; NatEqToEqD
(set-goal "all n,m(n=m -> n eqd m)")
(ind)
(cases)
(assume "Useless")
(use "InitEqD")
(assume "n" "0=Sn")
(use "EfEqD")
(use "0=Sn")
(assume "n" "IH")
(cases)
(assume "Sn=0")
(use "EfEqD")
(use "Sn=0")
(assume "m" "Sn=Sm")
(assert "n eqd m")
 (use "IH")
 (use "Sn=Sm")
(assume "n=m")
(elim "n=m")
(strip)
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "NatEqToEqD")

;; BooleEqToEqD
(set-goal "all boole1,boole2(boole1=boole2 -> boole1 eqd boole2)")
(cases)
(cases)
(assume "Useless")
(use "InitEqD")
(assume "T=F")
(use "EfEqD")
(use "T=F")
(cases)
(assume "F=T")
(use "EfEqD")
(use "F=T")
(assume "Useless")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "BooleEqToEqD")

;; Computation rules for the program constants.

;; For NatPlus
(add-computation-rules
 "n+0" "n"
 "n+Succ m" "Succ(n+m)")

;; For NatTimes
(add-computation-rules
 "n*0" "0"
 "n*Succ m" "(n*m)+n")

;; For NatLt
(add-computation-rules
 "n<0" "False"
 "0<Succ n" "True"
 "Succ n<Succ m" "n<m")

;; For NatLe
(add-computation-rules
 "0<=n" "True"
 "Succ n<=0" "False"
 "Succ n<=Succ m" "n<=m")

;; For Pred
(add-computation-rules
 "Pred 0" "0"
 "Pred(Succ n)" "n")

;; For NatMinus
(add-computation-rules
 "n--0" "n"
 "n--Succ m" "Pred(n--m)")

;; For NatMax
(add-computation-rules
 "n max 0" "n"
 "0 max Succ n" "Succ n"
 "Succ n max Succ m" "Succ(n max m)")

;; For NatMin
(add-computation-rules
 "n min 0" "0"
 "0 min Succ n" "0"
 "Succ n min Succ m" "Succ(n min m)")

(add-var-name "pf" (py "nat=>boole"))

;; For AllBNat
(add-computation-rules
 "AllBNat 0 pf" "True"
 "AllBNat(Succ n)pf" "[if (AllBNat n pf) (pf n) False]")

;; (add-computation-rules
;;  "AllBNat 0 nat=>boole" "True"
;;  "AllBNat(Succ n)nat=>boole" "AllBNat n nat=>boole andb pf n")

;; For ExBNat
(add-computation-rules
 "ExBNat 0 nat=>boole" "False"
 "ExBNat(Succ n)pf" "[if (pf n) True (ExBNat n pf)]")

;; For efficiency reasons if is preferred over orb (i.e., over the
;; term (ExBNat n nat=>boole orb pf n), since it computes
;; its arguments only when necessary.

;; For NatLeast
(add-computation-rules
 "NatLeast 0 pf" "0"
 "NatLeast(Succ n)pf"
 "[if (pf 0) 0 (Succ(NatLeast n([m]pf (Succ m))))]")

;; For NatLeastUp
(add-computation-rules
 "NatLeastUp n0 n pf"
 "[if (n0<=n) (NatLeast(n--n0)([m]pf (m+n0))+n0) 0]")

;; We prove and add some properties of the program constants introduced,
;; either as rewrite rules or as theorems.

;; Properties of NatPlus

;; (term-to-t-deg (pt "NatPlus"))
;; 0

(set-totality-goal "NatPlus")
(assume "n^" "Tn" "m^" "Tm")
(elim "Tm")
(ng #t)
(use "Tn")
(assume "l^" "Tl" "IH")
(ng #t)
(use "TotalNatSucc")
(use "IH")
;; Proof finished.
;; (cdp)
(save-totality)

;; (cdp (proof-to-soundness-proof))
;; (pp (rename-variables (proof-to-formula (proof-to-soundness-proof))))
;; allnc n^,n^0(
;;  TotalNatMR n^ n^0 -> 
;;  allnc m^,n^1(
;;   TotalNatMR m^ n^1 -> 
;;   TotalNatMR(n^ +m^)((Rec nat=>nat)n^1 n^0([n^2,n^3]Succ n^3))))

;; NatPlusEqP
(set-goal "allnc n^1,n^2(EqPNat n^1 n^2 -> allnc m^1,m^2(EqPNat m^1 m^2 ->
 EqPNat(n^1+m^1)(n^2+m^2)))")
(assume "n^1" "n^2" "EqPn1n2" "m^1" "m^2" "EqPm1m2")
(elim "EqPm1m2")
;; 3,4
(ng #t)
(use "EqPn1n2")
;; 4
(assume "m^3" "m^4" "EqPm3m4" "IH")
(ng #t)
(use "EqPNatSucc")
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatPlusEqP")

(set-goal "all n 0+n=n")
(ind)
(use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "0+n" "n")

(set-goal "all n,m Succ n+m=Succ(n+m)")
(assume "n")
(ind)
(use "Truth")
(assume "m" "IH")
(use "IH")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "Succ n+m" "Succ(n+m)")

(set-goal "all n,m,l n+(m+l)=n+m+l")
(assume "n" "m")
(ind)
(use "Truth")
(assume "l" "IH")
(use "IH")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "n+(m+l)" "n+m+l")

;; NatPlusComm
(set-goal "all n,m n+m=m+n")
(assume "n")
(ind)
(use "Truth")
(assume "m" "IH")
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatPlusComm")

;; NatPlusCancelL
(set-goal "all n,m,l(n+m=n+l -> m=l)")
(ind)
(ng)
(assume "m" "l" "m=l")
(use "m=l")
;; Step
(assume "n" "IH")
(ng)
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatPlusCancelL")

;; NatPlusCancelR
(set-goal "all n,m,l(n+m=l+m -> n=l)")
(assert "all m,n,l(n+m=l+m -> n=l)")
(ind)
(assume "n" "l" "n=l")
(use "n=l")
;; Step
(assume "m" "IH")
(ng)
(use "IH")
;; Assertion proved.
(assume "Assertion" "n" "m")
(use "Assertion")
;; Proof finished.
;; (cdp)
(save "NatPlusCancelR")

;; Properties of NatTimes

(set-totality-goal "NatTimes")
(assume "n^" "Tn" "m^" "Tm")
(elim "Tm")
(ng #t)
(use "TotalNatZero")
(assume "l^" "Tl" "IH")
(ng #t)
(use "NatPlusTotal")
(use "IH")
(use "Tn")
;; Proof finished
;; (cdp)
(save-totality)

;; (cdp (proof-to-soundness-proof))
;; (proof-to-expr-with-formulas (np (proof-to-soundness-proof)))

;; Alternative, with AllTotalElim
;; (set-totality-goal "NatTimes")
;; (use "AllTotalElim")
;; (assume "n")
;; (use "AllTotalElim")
;; (ind)
;; (use "NatTotalVar")
;; (assume "m" "IH")
;; (ng #t)
;; (use "NatPlusTotal")
;; (use "IH")
;; (use "NatTotalVar")
;; ;; Proof finished.
;; (save-totality)

(set-goal "all n 0*n=0")
(ind)
(use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "0*n" "0")

;; NatCompat
(set-goal "all n,m(n=m -> all pf^(pf^ n -> pf^ m))")
(ind)
  (cases)
    (assume "0=0" "pf^" "H1")
    (use "H1")
  (assume "nat" "Absurd" "pf^" "H1")
  (use "EfAtom")
  (use "Absurd")
(assume "n" "IH")
(cases)
  (assume "Absurd" "pf^" "H1")
  (use "EfAtom")
  (use "Absurd")
(assume "m" "n=m" "pf^")
(use-with "IH" (pt "m") "n=m" (pt "[n]pf^(Succ n)"))
;; Proof finished.
;; (cdp)
(save "NatCompat")

(add-var-name "nf" (py "nat=>nat"))

;; NatEqCompat
(set-goal "all n,m(n=m -> allnc nf(nf n=nf m))")
(ind)
  (cases)
    (assume "Useless" "nf")
    (use "Truth")
  (assume "m" "Absurd" "nf")
  (use "EfAtom")
  (use "Absurd")
(assume "n" "IH")
(cases)
  (assume "Absurd" "nf")
  (use "EfAtom")
  (use "Absurd")
(assume "m" "n=m" "nf")
(use-with "IH" (pt "m") "n=m" (pt "[n]nf(Succ n)"))
;; Proof finished.
;; (cdp)
(save "NatEqCompat")

;; NatEqSym
(set-goal "all n,m(n=m -> m=n)")
(assume "n" "m" "n=m")
(simp "n=m")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "NatEqSym")

;; NatEqTrans
(set-goal "all n,m,l(n=m -> m=l -> n=l)")
(assume "n" "m" "l" "=Hyp")
(simp "<-" "=Hyp")
(assume "n=l")
(use "n=l")
;; Proof finished.
;; (cdp)
(save "NatEqTrans")

(set-goal "all n,m Succ n*m=(n*m)+m")
(assume "n")
(ind)
  (use "Truth")
(assume "m" "IH")
(ng)
(use "NatEqTrans" (pt "n*m+m+n"))
(use-with "NatEqCompat" (pt "Succ n*m") (pt "n*m+m")
	  "IH" (pt "[nat]nat+n"))
(use-with "NatEqCompat" (pt "m+n") (pt "n+m") "?"
	  (pt "[nat]n*m+nat"))
(use "NatPlusComm")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "Succ n*m" "(n*m)+m")

;; NatTimesPlusDistr
(set-goal "all n,m,l n*(m+l)=(n*m)+(n*l)")
(assume "n" "m")
(ind)
(use "Truth")
(assume "l" "IH")
(ng #t)
(simp "IH")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "NatTimesPlusDistr")
(add-rewrite-rule "n*(m+l)" "n*m+n*l")

;; NatTimesComm
(set-goal "all n,m n*m=m*n")
(assume "n")
(ind)
  (use "Truth")
(assume "m" "IH")
(ng)
(use "NatEqTrans" (pt "m*n+n"))
(use-with "NatEqCompat" (pt "n*m") (pt "m*n") "IH"
	  (pt "[nat]nat+n"))
(use "Truth")
;; Proof finished.
;; (cdp)
(save "NatTimesComm")

;; NatTimesPlusDistrLeft
(set-goal "all n,m,l (n+m)*l=(n*l)+(m*l)")
(assume "n" "m" "l")
(simp-with "NatTimesComm" (pt "n+m") (pt "l"))
(ng #t)
(simp-with "NatTimesComm" (pt "n") (pt "l"))
(simp-with "NatTimesComm" (pt "m") (pt "l"))
(use-with "Truth")
;; Proof finished.
;; (cdp)
(save "NatTimesPlusDistrLeft")
(add-rewrite-rule "(n+m)*l" "n*l+m*l")

(set-goal "all n,m,l n*(m*l)=(n*m)*l")
(ind)
  (strip)
  (use "Truth")
(assume "n" "IH1" "m" "l")
(ng)
(simp-with "IH1" (pt "m") (pt "l"))
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "n*(m*l)" "n*m*l")

;; NatTimesCancelL
(set-goal "all n,m,l(Zero<n -> n*m=n*l -> m=l)")
(assert "all n,m,l((Succ n)*m=(Succ n)*l -> m=l)")
(assume "n")
(ind)
(cases)
(strip)
(use "Truth")
(assume "l" "Absurd")
(use "Absurd")
;; Step of induction on m
(assume "m" "IHm")
(cases)
(assume "Absurd")
(use "Absurd")
(assume "l" "Hyp")
(ng)
(use "IHm")
(use "NatPlusCancelR" (pt "n"))
(use "Hyp")
(assume "Assertion")
(cases)
(assume "m" "l" "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
(assume "n" "m" "l" "Useless")
(use "Assertion")
;; Proof finished.
;; (cdp)
(save "NatTimesCancelL")

;; NatTimesCancelR
(set-goal "all n,m,l(Zero<m -> n*m=l*m -> n=l)")
(assume "n" "m" "l")
(simp "NatTimesComm")
(simp (pf "l*m=m*l"))
(use "NatTimesCancelL")
(use "NatTimesComm")
;; Proof finished.
;; (cdp)
(save "NatTimesCancelR")

;; Properties of NatLt

;; (add-totality "boole") ;moved to boole.scm
;; (pp "TotalBooleTrue")
;; (pp "TotalBooleFalse")

(set-totality-goal "NatLt")
(assume "n^" "Tn")
(elim "Tn")
(assume "m^" "Tm")
(elim "Tm")
(ng #t)
(use "TotalBooleFalse")
(assume "l^" "Tl" "Useless")
(ng #t)
(use "TotalBooleTrue")
(assume "m^" "Tm" "IH" "l^" "Tl")
(elim "Tl")
(ng #t)
(use "TotalBooleFalse")
(assume "l^0" "Tl0" "Useless")
(ng #t)
(use "IH")
(use "Tl0")
;; Proof finished.
;; (cdp)
(save-totality)

;; (cdp (proof-to-soundness-proof))
;; (proof-to-expr-with-formulas (np (proof-to-soundness-proof)))

;; ;; Alternative, with AllTotalElim
;; (set-totality-goal "NatLt")
;; (assert "allnc nat^(
;;   TotalNat nat^ -> allnc nat^0(TotalNat nat^0 -> TotalBoole(nat^0 <nat^)))")
;; (use "AllTotalElim")
;; (ind)
;; (assume "nat^2" "Useless")
;; (use "BooleTotalVar")
;; (assume "n" "IH")
;; (use "AllTotalElim")
;; (cases)
;; (use "BooleTotalVar")
;; (use "AllTotalIntro")
;; (use "IH")
;; ;; Assertion proved.
;; (assume "Assertion" "nat^1" "Tn" "nat^2" "Tm")
;; (use "Assertion")
;; (use "Tm")
;; (use "Tn")
;; ;; Proof finished.
;; (save-totality)

(set-goal "all n n<Succ n")
(ind)
  (use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "n<Succ n" "True")

(set-goal "all n (n<n)=False")
(ind)
  (use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "n<n" "False")

(set-goal "all n(Succ n<n)=False")
(ind)
  (use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "Succ n<n" "False")

;; NatLtTrans
(set-goal "all n,m,l(n<m -> m<l -> n<l)")
(ind)
  (cases)
    (assume "l" "Absurd" "0<l")
    (use "0<l")
  (assume "m")
  (cases)
    (assume "Useless" "Absurd")
    (use "Absurd")
  (assume "l" "Useless" "H1")
  (use "Truth")
(assume "n" "IH1")
(cases)
  (assume "l" "Absurd" "0<l")
  (use "EfAtom")
  (use "Absurd")
(assume "m")
(cases)
(assume "H1" "Absurd")
(use "Absurd")
(use "IH1")
;; Proof finished
;; (cdp)
(save "NatLtTrans")

;; NatNotLeToLt
(set-goal "all n,m((n<=m -> F) -> m<n)")
(ind)
(assume "m" "H1")
(use-with "H1" "Truth")
(assume "n" "IH")
(cases)
(assume "Useless")
(use "Truth")
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatNotLeToLt")

;; NatNotLtToLe
(set-goal "all n,m((n<m -> F) -> m<=n)")
(ind)
(cases)
(assume "Useless")
(use "Truth")
(assume "m" "H1")
(use-with "H1" "Truth")
(assume "n" "IH")
(cases)
(assume "Useless")
(use "Truth")
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatNotLtToLe")

;; NatLtToLe
(set-goal "all n,m(n<m -> n<=m)")
(ind)
(assume "m" "Useless")
(use "Truth")
(assume "nat" "IH")
(cases)
(assume "Absurd")
(use "Absurd")
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatLtToLe")

;; NatLeAntiSym
(set-goal "all n,m(n<=m -> m<=n -> n=m)")
(ind)
(cases)
(assume "Useless1" "Useless2")
(use "Truth")
(assume "n" "Useless" "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "n" "IHn")
(cases)
(assume "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
(assume "m")
(use "IHn")
;; Proof finished.
;; (cdp)
(save "NatLeAntiSym")

;; NatLtPlusCancelR as rewrite rule
(set-goal "all n,m,l(n+m<l+m)=(n<l)")
(assert "all n,l,m(n+m<l+m)=(n<l)")
(assume "n" "l")
(ind)
(use "Truth")
(assume "m" "IH")
(ng)
(use "IH")
;; Assertion proved.
(assume "Assertion" "n" "m" "l")
(use "Assertion")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "n+m<l+m" "n<l")

;; NatLtPlusCancelL
(set-goal "all n,m,l(n+m<n+l)=(m<l)") ;as rewrite rule
(assume "n" "m" "l")
(simp "NatPlusComm")
(simp (pf "n+l=l+n"))
(use "Truth")
(use "NatPlusComm")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "n+m<n+l" "m<l")

;; NatLtTimesCancelL
(set-goal "all n,m,l(Zero<n -> n*m<n*l -> m<l)")
(assert "all n,m,l((Succ n)*m<(Succ n)*l -> m<l)")
(assume "n")
(ind)
(cases)
(ng)
(assume "Absurd")
(use "Absurd")
(strip)
(use "Truth")
;; Step of induction on m
(assume "m" "IHm")
(cases)
(ng)
(assume "Absurd")
(use "Absurd")
(assume "l")
(ng)
(use "IHm")
;; Assertion proved.
(assume "Assertion")
(cases)
(assume "m" "l" "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
(assume "n" "m" "l" "Useless")
(use "Assertion")
;; Proof finished.
;; (cdp)
(save "NatLtTimesCancelL")

;; NatLtTimesCancelR
(set-goal "all n,m,l(Zero<m -> n*m<l*m -> n<l)")
(assume "n" "m" "l")
(simp "NatTimesComm")
(simp (pf "l*m=m*l"))
(use "NatLtTimesCancelL")
(use "NatTimesComm")
;; Proof finished.
;; (cdp)
(save "NatLtTimesCancelR")

;; Properties of NatLe

(set-totality-goal "NatLe")
(assume "n^" "Tn")
(elim "Tn")
(assume "m^" "Tm")
(elim "Tm")
(ng #t)
(use "TotalBooleTrue")
(assume "l^" "Tl" "Useless")
(ng #t)
(use "TotalBooleTrue")
(assume "m^" "Tm" "IH" "l^" "Tl")
(elim "Tl")
(ng #t)
(use "TotalBooleFalse")
(assume "l^0" "Tl0" "Useless")
(ng #t)
(use "IH")
(use "Tl0")
;; Proof finished.
;; (cdp)
(save-totality)

;; (cdp (proof-to-soundness-proof))
;; (proof-to-expr-with-formulas (np (proof-to-soundness-proof)))

;; ;; Alternative, with AllTotalElim
;; (set-totality-goal "NatLe")
;; (use "AllTotalElim")
;; (ind)
;; (assume "nat^2" "Useless")
;; (use "BooleTotalVar")
;; (assume "n" "IH")
;; (use "AllTotalElim")
;; (cases)
;; (use "BooleTotalVar")
;; (use "AllTotalIntro")
;; (use "IH")
;; ;; Proof finished.
;; (save-totality)

;; NatLeToEq
(set-goal "all n (n<=0)=(n=0)")
(cases)
(use "Truth")
(assume "n")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "NatLeToEq")
(add-rewrite-rule "n<=0" "n=0")

(set-goal "all n n<=n")
(ind)
  (use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "n<=n" "True")

(set-goal "all n,m n<=n+m")
(ind)
  (assume "m")
  (use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "n<=n+m" "True")

(set-goal "all n(Succ n<=n)=False")
(ind)
  (use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "Succ n<=n" "False")

(set-goal "all n n<=Succ n")
(ind)
  (use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "n<=Succ n" "True")

;; NatLeTrans
(set-goal "all n,m,l(n<=m -> m<=l -> n<=l)")
(ind)
  (strip)
  (use "Truth")
(assume "n" "IH")
(cases)
  (assume "l" "Absurd" "H1")
  (use "EfAtom")
  (use "Absurd")
(assume "m")
(cases)
  (assume "H1" "Absurd")
  (use "Absurd")
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatLeTrans")

;; NatLtLeTrans
(set-goal "all n,m,l(n<m -> m<=l -> n<l)")
(ind)
(cases)
  (assume "l" "Absurd" "H1")
  (use "EfAtom")
  (use "Absurd")
(assume "m")
(cases)
  (assume "H1" "Absurd")
  (use "Absurd")
(strip)
(use "Truth")
(assume "n" "IH")
(cases)
  (assume "l" "Absurd" "H1")
  (use "EfAtom")
  (use "Absurd")
(assume "m")
(cases)
  (assume "H1" "Absurd")
  (use "Absurd")
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatLtLeTrans")

;; NatLeLtTrans
(set-goal "all n,m,l(n<=m -> m<l -> n<l)")
(ind)
(cases)
  (assume "l" "Useless" "0<l")
  (use "0<l")
(assume "m")
(cases)
  (prop)
(assume "l")
(prop)
(assume "n" "IH")
(cases)
  (assume "l" "Absurd" "H1")
  (use "EfAtom")
  (use "Absurd")
(assume "m")
(cases)
  (assume "H1" "Absurd")
  (use "Absurd")
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatLeLtTrans")

;; NatLtSuccToLe
(set-goal "all n,m(n<Succ m -> n<=m)")
(ind)
  (strip)
  (use "Truth")
(assume "n" "IH")
(cases)
  (assume "Absurd")
  (use "Absurd")
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatLtSuccToLe")

;; NatLtLtSuccTrans
(set-goal "all n,m,l(n<m -> m<Succ l -> n<l)")
(assume "n" "m" "l" "n<m" "m<Succ l")
(use "NatLtLeTrans" (pt "m"))
(use "n<m")
(use "NatLtSuccToLe")
(use "m<Succ l")
;; Proof finished.
;; (cdp)
(save "NatLtLtSuccTrans")

;; NatLeToLtSucc
(set-goal "all n,m(n<=m -> n<Succ m)")
(ind)
  (strip)
  (use "Truth")
(assume "n" "IH")
(cases)
  (assume "Absurd")
  (use "Absurd")
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatLeToLtSucc")

;; NatLtToSuccLe
(set-goal "all n,m(n<m -> Succ n<=m)")
(ind)
  (cases)
  (assume "Absurd")
  (use "EfAtom")
  (use "Absurd")
  (assume "m" "Useless")
  (use "Truth")
(assume "n" "IH")
  (cases)
  (assume "Absurd")
  (use "EfAtom")
  (use "Absurd")
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatLtToSuccLe")

;; NatSuccLeToLt
(set-goal "all n,m(Succ n<=m -> n<m)")
(ind)
  (cases)
  (assume "Absurd")
  (use "EfAtom")
  (use "Absurd")
  (assume "m" "Useless")
  (use "Truth")
(assume "n" "IH")
  (cases)
  (assume "Absurd")
  (use "EfAtom")
  (use "Absurd")
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatSuccLeToLt")

;; NatLtSuccCases
(set-goal "all n,m(n<Succ m -> (n<m -> Pvar) -> (n=m -> Pvar) -> Pvar)")
(assume "n" "m" "LtSuccHyp")
(cases (pt "n<m"))
;; Case n<m
(assume "n<m" "THyp" "FHyp")
(use-with "THyp" "Truth")
;; Case n<m -> F
(assume "n<m -> F" "THyp" "FHyp")
(use "FHyp")
(use "NatLeAntiSym")
(use "NatLtSuccToLe")
(use "LtSuccHyp")
(use "NatNotLtToLe")
(use "n<m -> F")
;; Proof finished.
;; (cdp)
(save "NatLtSuccCases")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [n,n0,beta,beta_0][if (n<n0) beta beta_0]

(animate "NatLtSuccCases")

(define sproof (proof-to-soundness-proof))
;; (cdp sproof)
;; (pp (rename-variables (nf (proof-to-formula sproof))))

;; allnc n,m(
;;  n<Succ m -> 
;;  allnc beta^(
;;   (n<m -> (Pvar beta)^ beta^) -> 
;;   allnc beta^0(
;;    (n=m -> (Pvar beta)^ beta^0) -> (Pvar beta)^[if (n<m) beta^ beta^0])))

;; (define nsproof (np sproof))
;; (cdp nsproof)
;; (proof-to-expr-with-formulas nsproof)

(set-goal (rename-variables (nf (proof-to-formula sproof))))
(use-with sproof)
;; Proof finished.
;; (cdp)
(save "NatLtSuccCasesSound")

;; (pp "NatLtSuccCasesSound")

;; allnc n,m(
;;  n<Succ m -> 
;;  allnc beta^(
;;   (n<m -> (Pvar beta)^ beta^) -> 
;;   allnc beta^0(
;;    (n=m -> (Pvar beta)^ beta^0) -> (Pvar beta)^[if (n<m) beta^ beta^0])))

;; Remark.  (use sproof) does not work:
;; use2-closed-proof-intern
;; more terms expected, to be substituted for
;; n
;; m
;; alpha185^1340
;; alpha185^1341

;; NatLeCases
(set-goal "all n,m(n<=m -> (n<m -> Pvar) -> (n=m -> Pvar) -> Pvar)")
(assume "n" "m" "n<=m")
(cases (pt "n<m"))
;; Case n<m
(assume "n<m" "THyp" "FHyp")
(use-with "THyp" "Truth")
;; Case n<m -> F
(assume "n<m -> F" "THyp" "FHyp")
(use "FHyp")
(use "NatLeAntiSym")
(use "n<=m")
(use "NatNotLtToLe")
(use "n<m -> F")
;; Proof finished.
;; (cdp)
(save "NatLeCases")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [n,n0,beta,beta_0][if (n<n0) beta beta_0]

(animate "NatLeCases")

(define sproof (proof-to-soundness-proof))
;; (cdp sproof)
(pp (rename-variables (nf (proof-to-formula sproof))))

;; allnc n,m(
;;  n<=m -> 
;;  allnc beta^(
;;   (n<m -> (Pvar beta)^ beta^) -> 
;;   allnc beta^0(
;;    (n=m -> (Pvar beta)^ beta^0) -> (Pvar beta)^[if (n<m) beta^ beta^0])))

;; NatLeLtCases
(set-goal "all n,m((n<=m -> Pvar) -> (m<n -> Pvar) -> Pvar)")
(assume "n" "m")
(cases (pt "n<=m"))
;; Case n<=m
(assume "n<=m" "THyp" "FHyp")
(use-with "THyp" "Truth")
;; Case n<=m -> F
(assume "n<=m -> F" "THyp" "FHyp")
(use "FHyp")
(use "NatNotLeToLt")
(use "n<=m -> F")
;; Proof finished.
;; (cdp)
(save "NatLeLtCases")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [n,n0,beta,beta_0][if (n<=n0) beta beta_0]

(animate "NatLeLtCases")

;; (define sproof (proof-to-soundness-proof))
;; (cdp sproof)
;; (pp (rename-variables (nf (proof-to-formula sproof))))

;; allnc n,m,beta^(
;;  (n<=m -> (Pvar beta)^ beta^) -> 
;;  allnc beta^0(
;;   (m<n -> (Pvar beta)^ beta^0) -> (Pvar beta)^[if (n<=m) beta^ beta^0]))

;; (define nsproof (np sproof))
;; (cdp nsproof)
;; (proof-to-expr-with-formulas nsproof)

;; NatLeLin
(set-goal "all n,m((n<=m -> Pvar) -> (m<=n -> Pvar) -> Pvar)")
(assume "n" "m")
(cases (pt "n<=m"))
;; Case n<=m
(assume "n<=m" "THyp" "FHyp")
(use-with "THyp" "Truth")
;; Case n<=m -> F
(assume "n<=m -> F" "THyp" "FHyp")
(use "FHyp")
(use "NatLtToLe")
(use "NatNotLeToLt")
(use "n<=m -> F")
;; Proof finished.
;; (cdp)
(save "NatLeLin")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [n,n0,beta,beta_0][if (n<=n0) beta beta_0]

(animate "NatLeLin")

;; (define sproof (proof-to-soundness-proof))
;; (cdp sproof)
;; (pp (rename-variables (nf (proof-to-formula sproof))))

;; allnc n,m,beta^(
;;  (n<=m -> (Pvar beta)^ beta^) -> 
;;  allnc beta^0(
;;   (m<=n -> (Pvar beta)^ beta^0) -> (Pvar beta)^[if (n<=m) beta^ beta^0]))

;; (define nsproof (np sproof))
;; (cdp nsproof)
;; (proof-to-expr-with-formulas nsproof)

;; NatLtToLePred
(set-goal "all n,m(n<m -> n<=Pred m)")
(assume "n")
(cases)
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "m" "n<Succ m")
(use "NatLtSuccToLe")
(use "n<Succ m")
;; Proof finished.
;; (cdp)
(save "NatLtToLePred")

;; NatLePred
(set-goal "all n,m (Pred n<=m)=(n<=Succ m)")
(cases)
(strip)
(use "Truth")
(strip)
(use "Truth")
;; Proof finished.
;; (cdp)
(save "NatLePred")

;; NatLtMonPred
(set-goal "all n,m(0<n -> n<m -> Pred n<Pred m)")
(cases)
(assume "m" "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
(assume "n")
(cases)
(assume "Useless" "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "m" "Useless" "n<m")
(use "n<m")
;; Proof finished.
;; (cdp)
(save "NatLtMonPred")

;; NatLePlusCancelR
(set-goal "all n,m,l(n+m<=l+m)=(n<=l)") ;as rewrite rule
(assume "n")
(ind)
(assume "l")
(use "Truth")
;; Step
(assume "m" "IH")
(ng)
(use "IH")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "n+m<=l+m" "n<=l")

;; NatLePlusCancelL
(set-goal "all n,m,l(n+m<=n+l)=(m<=l)") ;as rewrite rule
(assume "n" "m" "l")
(simp "NatPlusComm")
(simp (pf "n+l=l+n"))
(use "Truth")
(use "NatPlusComm")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "n+m<=n+l" "m<=l")

;; NatLeTimesCancelL
(set-goal "all n,m,l(Zero<n -> n*m<=n*l -> m<=l)")
(assert "all n,m,l((Succ n)*m<=(Succ n)*l -> m<=l)")
(assume "n")
(ind)
(cases)
(ng)
(assume "Absurd")
(use "Absurd")
(strip)
(use "Truth")
;; Step of induction on m
(assume "m" "IHm")
(cases)
(ng)
(assume "Absurd")
(use "Absurd")
(assume "l")
(ng)
(use "IHm")
;; Assertion proved.
(assume "Assertion")
(cases)
(assume "m" "l" "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
(assume "n" "m" "l" "Useless")
(use "Assertion")
;; Proof finished.
;; (cdp)
(save "NatLeTimesCancelL")

;; NatLeTimesCancelR
(set-goal "all n,m,l(Zero<m -> n*m<=l*m -> n<=l)")
(assume "n" "m" "l")
(simp "NatTimesComm")
(simp (pf "l*m=m*l"))
(use "NatLeTimesCancelL")
(use "NatTimesComm")
;; Proof finished.
;; (cdp)
(save "NatLeTimesCancelR")

;; Properties of NatMinus and Pred

(set-totality-goal "Pred")
(assume "n^" "Tn")
(elim "Tn")
(ng #t)
(use "TotalNatZero")
(assume "m^" "Tm" "Useless")
(ng #t)
(use "Tm")
;; Proof finished.
;; (cdp)
(save-totality)

;; (cdp (proof-to-soundness-proof))
;; (proof-to-expr-with-formulas (np (proof-to-soundness-proof)))

;; ;; Alternative, with AllTotalElim
;; (set-totality-goal "Pred")
;; (use "AllTotalElim")
;; (cases)
;; (use "NatTotalVar")
;; (assume "nat")
;; (use "NatTotalVar")
;; ;; Proof finished.
;; (save-totality)

;; PredEqP
(set-goal "allnc n^,m^(EqPNat n^ m^ -> EqPNat(Pred n^)(Pred m^))")
(assume "n^" "m^" "EqPnm")
(elim "EqPnm")
;; 3,4
(use "EqPNatZero")
;; 4
(assume "n^1" "m^1" "EqPn1m1" "IH")
(ng)
(use "EqPn1m1")
;; Proof finished.
;; (cdp)
(save "PredEqP")

(set-totality-goal "NatMinus")
(assume "n^" "Tn" "m^" "Tm")
(elim "Tm")
(ng #t)
(use "Tn")
(assume "l^" "Tl" "IH")
(ng #t)
(use "PredTotal")
(use "IH")
;; Proof finished.
;; (cdp)
(save-totality)

;; (cdp (proof-to-soundness-proof))
;; (proof-to-expr-with-formulas (np (proof-to-soundness-proof)))

;; ;; Alternative, with AllTotalElim
;; (set-totality-goal "NatMinus")
;; (use "AllTotalElim")
;; (assume "n")
;; (use "AllTotalElim")
;; (ind)
;; (use "NatTotalVar")
;; (assume "m" "IH")
;; (ng #t)
;; (use "PredTotal")
;; (use "IH")
;; ;; Proof finished.
;; (save-totality)

;; NatMinusEqP
(set-goal "allnc n^1,n^2(EqPNat n^1 n^2 -> allnc m^1,m^2(EqPNat m^1 m^2 ->
 EqPNat(n^1--m^1)(n^2--m^2)))")
(assume "n^1" "n^2" "EqPn1n2" "m^1" "m^2" "EqPm1m2")
(elim "EqPm1m2")
;; 3,4
(ng #t)
(use "EqPn1n2")
;; 4
(assume "m^3" "m^4" "EqPm3m4" "IH")
(ng #t)
(use "PredEqP")
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatMinusEqP")

(set-goal "all n,m Pred(Succ n--m)=n--m")
(assume "n")
(ind)
  (use "Truth")
(assume "m" "IH")
(ng)
(simp-with "IH")
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "Pred(Succ n--m)" "n--m")

(set-goal "all n n--n=0")
(ind)
  (use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "n--n" "0")

(set-goal "all n Succ n--n=1")
(ind)
  (use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "Succ n--n" "1")

;; Properties of NatMax

(set-totality-goal "NatMax")
(assume "n^" "Tn")
(elim "Tn")
(assume "m^" "Tm")
(elim "Tm")
(ng #t)
(use "TotalNatZero")
(assume "l^" "Tl" "Useless")
(ng #t)
(use "TotalNatSucc")
(use "Tl")
(assume "m^" "Tm" "IH" "l^" "Tl")
(elim "Tl")
(ng #t)
(use "TotalNatSucc")
(use "Tm")
(assume "l^0" "Tl0" "Useless")
(ng #t)
(use "TotalNatSucc")
(use "IH")
(use "Tl0")
;; Proof finished.
;; (cdp)
(save-totality)

;; (cdp (proof-to-soundness-proof))
;; (proof-to-expr-with-formulas (np (proof-to-soundness-proof)))

;; ;; Alternative, with AllTotalElim
;; (set-totality-goal "NatMax")
;; (assert "allnc nat^(
;;   TotalNat nat^ -> allnc nat^0(TotalNat nat^0 -> TotalNat(nat^0 max nat^)))")
;; (use "AllTotalElim")
;; (ind)
;; (assume "nat^2" "Tm")
;; (use "Tm")
;; (assume "n" "IH")
;; (use "AllTotalElim")
;; (cases)
;; (use "NatTotalVar")
;; (use "AllTotalIntro")
;; (assume "nat^2" "Tm")
;; (ng #t)
;; (use "TotalNatSucc")
;; (use "IH")
;; (use "Tm")
;; ;; Assertion proved.
;; (assume "Assertion" "nat^1" "Tn" "nat^2" "Tm")
;; (use "Assertion")
;; (use "Tm")
;; (use "Tn")
;; ;; Proof finished.
;; (save-totality)

;; NatMaxEqP
(set-goal "allnc n^1,m^1(EqPNat n^1 m^1 -> allnc n^2,m^2(EqPNat n^2 m^2 ->
 EqPNat(n^1 max n^2)(m^1 max m^2)))")
(assume "n^1" "m^1" "EqPn1m1" "n^2" "m^2" "EqPn2m2")
(simp "<-" (pf "n^1 eqd m^1"))
(simp "<-" (pf "n^2 eqd m^2"))
(use "EqPNatRefl")
(use "NatMaxTotal")
(use "EqPNatToTotalLeft" (pt "m^1"))
(use "EqPn1m1")
(use "EqPNatToTotalLeft" (pt "m^2"))
(use "EqPn2m2")
;; 6
(use "EqPNatNcToEqD")
(use "EqPn2m2")
;; 4
(use "EqPNatNcToEqD")
(use "EqPn1m1")
;; Proof finished.
;; (cdp)
(save "NatMaxEqP")

(set-goal "all n 0 max n=n")
(cases)
  (use "Truth")
(strip)
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "0 max n" "n")

(set-goal "all n n max n = n")
(ind)
  (use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "n max n" "n")

(set-goal "all n,m,l(n max (m max l)=n max m max l)")
(ind)
  (strip)
  (use "Truth")
(assume "n" "IH")
(cases)
  (strip)
  (use "Truth")
(assume "m")
(cases)
  (use "Truth")
(use "IH")
;; Proof finished.
;; (cdp)
(add-rewrite-rule
 "n max (m max l)" "n max m max l")

;; NatMaxComm
(set-goal "all n,m n max m = m max n")
(ind)
  (strip)
  (use "Truth")
(assume "n" "IH")
(cases)
  (use "Truth")
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatMaxComm")

;; NatMaxUB1
(set-goal "all n,m n<=n max m")
(ind)
  (assume "m")
  (use "Truth")
(assume "n" "IH")
(cases)
  (use "Truth")
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatMaxUB1")

;; NatMaxUB2
(set-goal "all n,m m<=n max m")
(ind)
  (assume "m")
  (use "Truth")
(assume "n" "IH")
(cases)
  (use "Truth")
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatMaxUB2")

;; NatMaxLUB
(set-goal "all n,m,l(n<=l -> m<=l -> n max m<=l)")
(ind)
(cases)
(strip)
(use "Truth")
(assume "m" "l" "Useless1" "Hyp")
(use "Hyp")
(assume "n" "IHn")
(cases)
(cases)
(assume "Absurd" "Useless")
(use "Absurd")
(assume "l" "Hyp" "Useless")
(use "Hyp")
(assume "m")
(cases)
(assume "Absurd" "Useless")
(use "Absurd")
(assume "l")
(ng #t)
(use "IHn")
;; Proof finished
;; (cdp)
(save "NatMaxLUB")

;; NatMaxEq1
(set-goal "all n,m(m<=n -> n max m=n)")
(assume "n" "m" "m<=n")
(use "NatLeAntiSym")
(use "NatMaxLUB")
(use "Truth")
(use "m<=n")
(use "NatMaxUB1")
;; Proof finished.
;; (cdp)
(save "NatMaxEq1")

;; NatMaxEq2
(set-goal "all n,m(n<=m -> n max m=m)")
(assume "n" "m" "n<=m")
(use "NatLeAntiSym")
(use "NatMaxLUB")
(use "n<=m")
(use "Truth")
(use "NatMaxUB2")
;; Proof finished.
;; (cdp)
(save "NatMaxEq2")

;; Properties of NatMin

(set-totality-goal "NatMin")
(assume "n^" "Tn")
(elim "Tn")
(assume "m^" "Tm")
(elim "Tm")
(ng #t)
(use "TotalNatZero")
(assume "l^" "Tl" "Useless")
(ng #t)
(use "TotalNatZero")
(assume "m^" "Tm" "IH" "l^" "Tl")
(elim "Tl")
(ng #t)
(use "TotalNatZero")
(assume "l^0" "Tl0" "Useless")
(ng #t)
(use "TotalNatSucc")
(use "IH")
(use "Tl0")
;; Proof finished.
;; (cdp)
(save-totality)

;; (cdp (proof-to-soundness-proof))
;; (proof-to-expr-with-formulas (np (proof-to-soundness-proof)))

;; ;; Alternative, with AllTotalElim
;; (set-totality-goal "NatMin")
;; (assert "allnc nat^(
;;   TotalNat nat^ -> allnc nat^0(TotalNat nat^0 -> TotalNat(nat^0 min nat^)))")
;; (use "AllTotalElim")
;; (ind)
;; (assume "m^" "Tm")
;; (use "NatTotalVar")
;; (assume "n" "IH")
;; (use "AllTotalElim")
;; (cases)
;; (use "NatTotalVar")
;; (use "AllTotalIntro")
;; (assume "m^" "Tm")
;; (ng #t)
;; (use "TotalNatSucc")
;; (use "IH")
;; (use "Tm")
;; ;; Assertion proved.
;; (assume "Assertion" "nat^1" "Tn" "m^" "Tm")
;; (use "Assertion")
;; (use "Tm")
;; (use "Tn")
;; ;; Proof finished.
;; (save-totality)
 
(set-goal "all n 0 min n=0")
(cases)
  (use "Truth")
(strip)
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "0 min n" "0")

(set-goal "all n n min n = n")
(ind)
  (use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "n min n" "n")

(set-goal "all n,m,l(n min (m min l)=n min m min l)")
(ind)
  (strip)
  (use "Truth")
(assume "n" "IH")
(cases)
  (strip)
  (use "Truth")
(assume "m")
(cases)
  (use "Truth")
(use "IH")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "n min (m min l)" "n min m min l")

;; NatMinComm
(set-goal "all n,m n min m = m min n")
(ind)
  (strip)
  (use "Truth")
(assume "n" "IH")
(cases)
  (use "Truth")
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatMinComm")

;; NatMinLB1
(set-goal "all n,m n min m<=n")
(ind)
  (assume "m")
  (use "Truth")
(assume "n" "IH")
(cases)
  (use "Truth")
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatMinLB1")

;; NatMinLB2
(set-goal "all n,m n min m<=m")
(ind)
  (assume "m")
  (use "Truth")
(assume "n" "IH")
(cases)
  (use "Truth")
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatMinLB2")

;; NatMinGLB
(set-goal "all n,m,l(l<=n -> l<=m -> l<=n min m)")
(ind)
(assume "m" "l" "Hyp" "Useless")
(use "Hyp")
(assume "n" "IH")
(cases)
(assume "l" "Useless1" "Hyp")
(use "Hyp")
(assume "m")
(cases)
(strip)
(use "Truth")
(use "IH")
;; Proof finished
;; (cdp)
(save "NatMinGLB")

;; NatMinEq1
(set-goal "all n,m(n<=m -> n min m=n)")
(assume "n" "m" "n<=m")
(use "NatLeAntiSym")
(use "NatMinLB1")
(use "NatMinGLB")
(use "Truth")
(use "n<=m")
;; Proof finished.
;; (cdp)
(save "NatMinEq1")

;; NatMinEq2
(set-goal "all n,m(m<=n -> n min m=m)")
(assume "n" "m" "m<=n")
(use "NatLeAntiSym")
(use "NatMinLB2")
(use "NatMinGLB")
(use "m<=n")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "NatMinEq2")

;; NatIfTotal
(set-goal "allnc n^(TotalNat n^ ->
 allnc alpha^,(nat=>alpha)^(Total alpha^ ->
 allnc m^(TotalNat m^ -> Total((nat=>alpha)^ m^)) ->
 Total[if n^ alpha^ (nat=>alpha)^]))")
(assume "n^" "Tn" "alpha^" "(nat=>alpha)^" "Talpha" "Tf")
(elim "Tn")
(use "Talpha")
(assume "m^" "Tm" "Useless")
(ng #t)
(use "Tf")
(use "Tm")
;; Proof finished.
;; (cdp)
(save "NatIfTotal")

;; (define sproof (proof-to-soundness-proof))
;; (cdp sproof)
;; (pp (rename-variables (nf (proof-to-formula sproof))))

;; allnc n^,n^0(
;;  TotalNatMR n^ n^0 -> 
;;  allnc alpha^,(nat=>alpha)^0,x^(
;;   TotalMR alpha^ x^ -> 
;;   allnc (nat=>alpha)^1(
;;    allnc m^,n^1(
;;     TotalNatMR m^ n^1 -> TotalMR((nat=>alpha)^0 m^)((nat=>alpha)^1 n^1)) -> 
;;    TotalMR[if n^ alpha^ (nat=>alpha)^0][if n^0 x^ (nat=>alpha)^1])))

;; (define nsproof (np sproof))
;; (cdp nsproof)
;; (proof-to-expr-with-formulas nsproof)

;; NatEqTotal
(set-goal "allnc n^(
 TotalNat n^ -> allnc m^(TotalNat m^ -> TotalBoole(n^ =m^)))")
(assume "n^" "Tn")
(elim "Tn")
(assume "m^" "Tm")
(elim "Tm")
(use "TotalBooleTrue")
(assume "l^" "Useless1" "Useless2")
(use "TotalBooleFalse")
(assume "l^" "Tl" "IHl" "l^0" "Tl0")
(elim "Tl0")
(use "TotalBooleFalse")
(assume "l^1" "Tl1" "Useless")
(use "IHl")
(use "Tl1")
;; Proof finished.
;; (cdp)
(save "NatEqTotal")

;; (cdp (proof-to-soundness-proof))
;; (proof-to-expr-with-formulas (np (proof-to-soundness-proof)))

;; ;; Alternative, with AllTotalElim
;; (set-goal "allnc n^(
;;  TotalNat n^ -> allnc m^(TotalNat m^ -> TotalBoole(n^ =m^)))")
;; (use "AllTotalElim")
;; (ind)
;; ;; 3,4
;; (use "AllTotalElim")
;; (cases)
;; (use "BooleTotalVar")
;; (assume "m")
;; (use "BooleTotalVar")
;; ;; 4
;; (assume "n" "IH")
;; (use "AllTotalElim")
;; (cases)
;; (use "BooleTotalVar")
;; (assume "m")
;; (use "IH")
;; (use "NatTotalVar")
;; ;; Proof finished.
;; (save "NatEqTotal")

;; The following would fit better into a file lib/boole.scm

;; EqFalseToNeg
(set-goal "all boole(boole=False -> boole -> F)")
(cases)
(assume "Absurd" "Useless")
(use "Absurd")
(assume "Useless" "Absurd")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EqFalseToNeg")

;; NegToEqFalse
(set-goal "all boole((boole -> F) -> boole=False)")
(cases)
(assume "Absurd")
(use-with "Absurd" "Truth")
(assume "Useless")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "NegToEqFalse")

;; BooleAeqToEq
(set-goal "all boole1,boole2(
 (boole1 -> boole2) -> (boole2 -> boole1) -> boole1=boole2)")
(cases)
(cases)
(strip)
(use "Truth")
(assume "Absurd" "Useless")
(use-with "Absurd" "Truth")
(cases)
(assume "Useless" "Absurd")
(use-with "Absurd" "Truth")
(strip)
(use "Truth")
;; Proof finished.
;; (cdp)
(save "BooleAeqToEq")

;; BooleEqToAeqLeft
(set-goal "all boole1,boole2(boole1=boole2 -> boole1 -> boole2)")
(cases)
(cases)
(strip)
(use "Truth")
(assume "Absurd" "Useless")
(use "Absurd")
(cases)
(strip)
(use "Truth")
(assume "Useless" "Absurd")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "BooleEqToAeqLeft")

;; BooleEqToAeqRight
(set-goal "all boole1,boole2(boole1=boole2 -> boole2 -> boole1)")
(cases)
(strip)
(use "Truth")
(cases)
(assume "Absurd" "Useless")
(use "Absurd")
(assume "Useless" "Absurd")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "BooleEqToAeqRight")

;; OrIntroLeft
(set-goal "all boole1,boole2(boole1 -> boole1 orb boole2)")
(cases)
(strip)
(use "Truth")
(cases)
(strip)
(use "Truth")
(assume "Absurd")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "OrIntroLeft")

;; OrIntroRight
(set-goal "all boole1,boole2(boole2 -> boole1 orb boole2)")
(cases)
(strip)
(use "Truth")
(cases)
(strip)
(use "Truth")
(assume "Absurd")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "OrIntroRight")

;; OrElim
(set-goal "all boole1,boole2(
 boole1 orb boole2 -> (boole1 -> Pvar) -> (boole2 -> Pvar) -> Pvar)")
(cases)
(assume "boole1" "Useless1" "Hyp" "Useless2")
(use-with "Hyp" "Truth")
(cases)
(assume "Useless1" "Useless2" "Hyp")
(use-with "Hyp" "Truth")
(ng #t)
(assume "Absurd" "Hyp1" "Hyp2")
(use-with "Hyp1" "Absurd")
;; Proof finished.
;; (cdp)
(save "OrElim")

(define sproof (proof-to-soundness-proof))
;; (cdp sproof)
;; (proof-to-expr-with-formulas sproof)
;; (define nsproof (np sproof))
;; (proof-to-expr-with-formulas nsproof)

(set-goal (rename-variables (nf (proof-to-formula sproof))))
(use-with sproof)
;; Proof finished.
;; (cdp)
(save "OrElimSound")

;; IfAndb
(set-goal "all boole1,boole2 [if boole1 boole2 False]=(boole1 andb boole2)")
(cases)
(assume "boole1")
(use "Truth")
(assume "boole1")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "IfAndb")

;; IfOrb
(set-goal "all boole1,boole2 [if boole1 True boole2]=(boole1 orb boole2)")
(cases)
(assume "boole1")
(use "Truth")
(assume "boole1")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "IfOrb")

;; Properties of AllBNat

;; AllBNatTotal
(set-goal (rename-variables (term-to-totality-formula (pt "AllBNat"))))

;; allnc n^(
;;  TotalNat n^ -> 
;;  allnc pf^(
;;   allnc n^0(TotalNat n^0 -> TotalBoole(pf^ n^0)) -> 
;;   TotalBoole(AllBNat n^ pf^)))

(assume "n^" "Tn" "pf^" "Tpf")
(elim "Tn")
;; 3,4
(ng #t)
(use "TotalBooleTrue")
;; 4
(assume "n^1" "Tn1" "IH")
(ng #t)
(use "BooleIfTotal")
(use "IH")
(use "Tpf")
(use "Tn1")
(use "TotalBooleFalse")
;; Proof finished.
;; (cdp)
(save-totality)

;; AllBNatTotal has been added as a new theorem.
;; ok, computation rule AllBNat 0 nat=>boole -> True added
;; ok, computation rule AllBNat(Succ n)nat=>boole ->
;;  [if (AllBNat n nat=>boole) (nat=>boole n) False] added

;; (term-to-t-deg (pt "AllBNat"))
;; 1

;; (define pconst (term-in-const-form-to-const (pt "AllBNat")))
;; (cdp (pconst-to-totality-proof pconst))
;; ok

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [n,pf](Rec nat=>boole)n True([n0,boole][if boole (pf n0) False])

;; Moreover we have extensionality of AllBNat:

;; AllBNatExt
(set-goal
 (rename-variables (terms-to-eqp-formula (pt "AllBNat") (pt "AllBNat"))))

;; allnc n^(
;;  TotalNat n^ -> 
;;  allnc pf^,pf^0(
;;   allnc n^0(TotalNat n^0 -> EqPBoole(pf^ n^0)(pf^0 n^0)) -> 
;;   EqPBoole(AllBNat n^ pf^)(AllBNat n^ pf^0)))

;; Code discarded 2019-07-11.  Change of changesmlfin.scm taken back.
;; Implicit use of theorems has been done before (e.g., rewrite rules)

;; ;; 2019-07-10.  After change of changesmlfin.scm

;; ;; ?_1:allnc n^,n^0(
;; ;;      EqPNat n^ n^0 -> 
;; ;;      allnc pf^,pf^0(
;; ;;       allnc n^1,n^2(EqPNat n^1 n^2 -> EqPBoole(pf^ n^1)(pf^0 n^2)) -> 
;; ;;       EqPBoole(AllBNat n^ pf^)(AllBNat n^0 pf^0)))

;; ;; Idea: Use AllEqPNatIntro

;; (pp (pf "allnc n^(TotalNat n^ -> (Pvar nat nat)n^ n^) ->
;;          allnc n^1,n^2(EqPNat n^1 n^2 -> (Pvar nat nat)n^1 n^2)"))

;; ;; and its inverse AllEqPNatElim

(assume "n^" "Tn" "pf^1" "pf^2" "ExtHyp")
(elim "Tn")
;; 3,4
(ng #t)
(use "EqPBooleTrue")
;; 4
(assume "n^1" "Tn1" "IH")
(ng #t)
(assert "AllBNat n^1 pf^1 eqd AllBNat n^1 pf^2")
 (use "EqPBooleToEqD")
 (use "IH")
(assume "EqDAllBNatHyp")
(simp "EqDAllBNatHyp")
(assert "pf^1 n^1 eqd pf^2 n^1")
 (use "EqPBooleToEqD")
 (use "ExtHyp")
 (use "Tn1")
(assume "EqDpfHyp")
(simp "EqDpfHyp")
(use "EqPBooleRefl")
(use "BooleIfTotal")
(use "EqPBooleToTotalRight" (pt "AllBNat n^1 pf^1"))
(use "IH")
(use "EqPBooleToTotalRight" (pt "pf^1 n^1"))
(use "ExtHyp")
(use "Tn1")
(use "TotalBooleFalse")
;; Proof finished.
;; (cdp)
(save "AllBNatExt")

(animate "EqPBooleRefl")
;; ok, computation rule cEqPBooleRefl -> [boole0]boole0 added
(animate "EqPBooleToTotalRight")
;; ok, computation rule cEqPBooleToTotalRight -> [boole0]boole0 added

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n,pf](Rec nat=>boole)n True([n0,boole][if boole (pf n0) False])

;; Todo: reformulate n.c. theorems on EqPBoole with n.c. premises.  Done
;; (search-about 'all "EqPBoole")

;; AllBNatExtEqD
(set-goal "allnc n^(TotalNatNc n^ -> 
 allnc pf^,pf^0(
  allnc n^0(TotalNatNc n^0 -> pf^ n^0 eqd pf^0 n^0) ->
  AllBNat n^ pf^ eqd AllBNat n^ pf^0))")
(assume "n^" "Tn" "pf^1" "pf^2" "ExtHyp")
(elim "Tn")
;; 3,4
(ng #t)
(use "InitEqD")
;; 4
(assume "n^1" "Tn1" "IH")
(ng #t)
(simp "IH")
(simp "ExtHyp")
(use "InitEqD")
(use "Tn1")
;; Proof finished.
;; (cdp)
(save "AllBNatExtEqD")

;; Same for nc

;; AllBNatTotalNc
(set-goal (rename-variables (term-to-totalnc-formula (pt "AllBNat"))))

;; allnc n^(
;;      TotalNatNc n^ -> 
;;      allnc pf^(
;;       allnc n^0(TotalNatNc n^0 -> TotalBooleNc(pf^ n^0)) -> 
;;       TotalBooleNc(AllBNat n^ pf^)))

(assume "n^" "Tn" "pf^" "Tpf")
(elim "Tn")
;; 3,4
(ng #t)
(use "TotalBooleNcTrue")
;; 4
(assume "n^1" "Tn1" "IH")
(ng #t)
(elim "IH")
(ng #t)
(use "Tpf")
(use "Tn1")
(ng #t)
(use "TotalBooleNcFalse")
;; Proof finished.
;; (cdp)
(save "AllBNatTotalNc")

;; Moreover we have extensionality of AllBNatNc:

;; AllBNatExtNc
(set-goal
 (rename-variables (terms-to-eqpnc-formula (pt "AllBNat") (pt "AllBNat"))))

;; allnc n^(
;;      TotalNatNc n^ -> 
;;      allnc pf^,pf^0(
;;       allnc n^0(TotalNatNc n^0 -> EqPBooleNc(pf^ n^0)(pf^0 n^0)) -> 
;;       EqPBooleNc(AllBNat n^ pf^)(AllBNat n^ pf^0)))

(assume "n^" "Tn" "pf^1" "pf^2" "ExtHyp")
(elim "Tn")
;; 3,4
(ng #t)
(use "EqPBooleNcTrue")
;; 4
(assume "n^1" "Tn1" "IH")
(ng #t)
(assert "AllBNat n^1 pf^1 eqd AllBNat n^1 pf^2")
 (use "EqPBooleNcToEqD")
 (use "IH")
(assume "EqDAllBNatHyp")
(simp "EqDAllBNatHyp")
(assert "pf^1 n^1 eqd pf^2 n^1")
 (use "EqPBooleNcToEqD")
 (use "ExtHyp")
 (use "Tn1")
(assume "EqDpfHyp")
(simp "EqDpfHyp")
(use "EqPBooleNcRefl")
(elim "IH")
(ng #t)
(use "EqPBooleNcToTotalNcRight" (pt "pf^1 n^1"))
(use "ExtHyp")
(use "Tn1")
(ng #t)
(use "TotalBooleNcFalse")
;; Proof finished.
;; (cdp)
(save "AllBNatExtNc")

;; NatLeastTotal
(set-goal (rename-variables (term-to-totality-formula (pt "NatLeast"))))

;; allnc n^(
;;      TotalNat n^ -> 
;;      allnc pf^(
;;       allnc n^0(TotalNat n^0 -> TotalBoole(pf^ n^0)) -> 
;;       TotalNat(NatLeast n^ pf^)))

(assume "n^" "Tn")
(elim "Tn")
;; 3,4
(ng #t)
(strip)
(use "TotalNatZero")
;; 4
(assume "n^1" "Tn1" "IH" "pf^" "Tpf")
(ng #t)
(use "BooleIfTotal")
(use "Tpf")
(use "TotalNatZero")
(use "TotalNatZero")
(use "TotalNatSucc")
(use "IH")
(assume "n^2" "Tn2")
(ng #t)
(use "Tpf")
(use "TotalNatSucc")
(use "Tn2")
;; Proof finished.
;; (cdp)
(save-totality)

;; ok, NatLeastTotal has been added as a new theorem.
;; ok, computation rule NatLeast 0 nat=>boole -> 0 added
;; ok, computation rule NatLeast(Succ n)nat=>boole ->
;;  [if (nat=>boole 0) 0 (Succ(NatLeast n([m]nat=>boole(Succ m))))] added

;; (term-to-t-deg (pt "NatLeast"))
;; 1

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n]
;;  (Rec nat=>(nat=>boole)=>nat)n([pf]0)
;;  ([n0,((nat=>boole)=>nat),pf]
;;    [if (pf 0) 0 (Succ(((nat=>boole)=>nat)([n1]pf(Succ n1))))])

;; Moreover we have extensionality of NatLeast:

;; NatLeastExt
(set-goal
 (rename-variables (terms-to-eqp-formula (pt "NatLeast") (pt "NatLeast"))))

;; allnc n^(
;;      TotalNat n^ -> 
;;      allnc pf^,pf^0(
;;       allnc n^0(TotalNat n^0 -> EqPBoole(pf^ n^0)(pf^0 n^0)) -> 
;;       EqPNat(NatLeast n^ pf^)(NatLeast n^ pf^0)))

(assume "n^" "Tn")
(elim "Tn")
;; 3,4
(ng #t)
(strip)
(use "EqPNatZero")
;; 4
(assume "n^1" "Tn1" "IH" "pf^1" "pf^2" "EqPHyp")
(ng #t)
(use "BooleIfEqP")
(use "EqPHyp")
(use "TotalNatZero")
(use "EqPNatZero")
(use "EqPNatSucc")
(use "IH")
(ng #t)
(assume "n^2" "Tn2")
(use "EqPHyp")
(use "TotalNatSucc")
(use "Tn2")
;; Proof finished.
;; (cdp)
(save "NatLeastExt")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n0]
;;  (Rec nat=>(nat=>boole)=>nat)n0([pf2]0)
;;  ([n2,((nat=>boole)=>nat)_3,pf4]
;;    (cBooleIfEqP nat)(pf4 0)0(Succ(((nat=>boole)=>nat)_3([n5]pf4(Succ n5)))))

(animate "BooleIfEqP")
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n]
;;  (Rec nat=>(nat=>boole)=>nat)n([pf]0)
;;  ([n0,((nat=>boole)=>nat),pf]
;;    [if (pf 0) 0 (Succ(((nat=>boole)=>nat)([n1]pf(Succ n1))))])

;; NatLeastExtEqD
(set-goal "allnc n^(TotalNatNc n^ -> 
 allnc pf^,pf^0(
  allnc n^0(TotalNatNc n^0 -> pf^ n^0 eqd pf^0 n^0) ->
  NatLeast n^ pf^ eqd NatLeast n^ pf^0))")
(assume "n^" "Tn")
(elim "Tn")
;; 3,4
(ng #t)
(strip)
(use "InitEqD")
;; 4
(assume "n^1" "Tn1" "IH" "pf^1" "pf^2" "EqDHyp")
(ng #t)
(simp "EqDHyp")
(inst-with-to "IH" (pt "[n]pf^1(Succ n)") (pt "[n]pf^2(Succ n)") "Inst")
(simp "Inst")
(use "InitEqD")
(assume "n^2" "Tn2")
(use "EqDHyp")
(use "TotalNatSucc")
(use "Tn2")
(use "TotalNatNcZero")
;; Proof finished.
;; (cdp)
(save "NatLeastExtEqD")

;; Same for nc

;; Need BooleIfTotalNc (to be added to ets.scm)

;; BooleIfTotalNc
(set-goal "allnc boole^(
 TotalBooleNc boole^ -> 
 allnc alpha^0,alpha^1(
  TotalNc alpha^0 -> TotalNc alpha^1 -> TotalNc[if boole^ alpha^0 alpha^1]))")
(assume "boole^" "Tb" "alpha^1" "alpha^2" "Tx1" "Tx2")
(elim "Tb")
(use "Tx1")
(use "Tx2")
;; Proof finished.
;; (cdp)
(save "BooleIfTotalNc")

;; NatLeastTotalNc
(set-goal (rename-variables (term-to-totalnc-formula (pt "NatLeast"))))

;; allnc n^(
;;      TotalNatNc n^ -> 
;;      allnc pf^(
;;       allnc n^0(TotalNatNc n^0 -> TotalBooleNc(pf^ n^0)) -> 
;;       TotalNatNc(NatLeast n^ pf^)))

(assume "n^" "Tn")
(elim "Tn")
;; 3,4
(ng #t)
(strip)
(use "TotalNatNcZero")
;; 4
(assume "n^1" "Tn1" "IH" "pf^" "Tpf")
(ng #t)
(use "BooleIfTotalNc")
(use "Tpf")
(use "TotalNatNcZero")
(use "TotalNatNcZero")
(use "TotalNatNcSucc")
(use "IH")
(ng #t)
(assume "n^2" "Tn2")
(use "Tpf")
(use "TotalNatSucc")
(use "Tn2")
;; Proof finished.
;; (cdp)
(save "NatLeastTotalNc")

;; NatLeastExtNc
(set-goal
 (rename-variables (terms-to-eqpnc-formula (pt "NatLeast") (pt "NatLeast"))))

;; allnc n^(
;;      TotalNatNc n^ -> 
;;      allnc pf^,pf^0(
;;       allnc n^0(TotalNatNc n^0 -> EqPBooleNc(pf^ n^0)(pf^0 n^0)) -> 
;;       EqPNatNc(NatLeast n^ pf^)(NatLeast n^ pf^0)))

(assume "n^" "Tn")
(elim "Tn")
;; 3,4
(ng #t)
(strip)
(use "EqPNatNcZero")
;; 4
(assume "n^1" "Tn1" "IH" "pf^1" "pf^2" "EqPHyp")
(ng #t)
(use "BooleIfEqPNc")
(use "EqPHyp")
(use "TotalNatNcZero")
(use "EqPNatZero")
(use "EqPNatSucc")
(use "IH")
(assume "n^2" "Tn2")
(ng #t)
(use "EqPHyp")
(use "TotalNatNcSucc")
(use "Tn2")
;; Proof finished.
;; (cdp)
(save "NatLeastExtNc")

;; NatLeastBound
(set-goal "all n,pf NatLeast n pf<=n")
(ind)
(ng #t)
(strip)
(use "Truth")
(assume "n" "IH" "pf")
(ng #t)
(cases (pt "pf 0"))
(assume "pf 0")
(ng #t)
(use "Truth")
(assume "pf 0 -> F")
(ng #t)
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatLeastBound")

;; NatLeastLeIntro
(set-goal "all n,m,pf(pf m -> (NatLeast n pf)<=m)")
(ind)
(strip)
(use "Truth")
(assume "n" "IH")
(cases)
(assume "pf" "g0")
(ng #t)
(simp "g0")
(use "Truth")
(assume "m" "pf" "g(Sn)")
(ng #t)
(cases 'auto)
(strip)
(use "Truth")
(strip)
(ng #t)
(use-with "IH" (pt "m") (pt "[nat](pf(Succ nat))") "?")
(ng #t)
(use "g(Sn)")
;; Proof finished.
;; (cdp)
(save "NatLeastLeIntro")

;; NatLeastLtElim
(set-goal "all n,pf(NatLeast n pf<n -> pf(NatLeast n pf))")
(ind)
(assume "pf")
(ng #t)
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "n" "IH" "pf")
(ng #t)
(cases (pt "pf 0"))
(assume "g0" "Useless")
(use "g0")
(assume "pf 0 -> F")
(ng #t)
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatLeastLtElim")

;; EqPNatNcPlus
(set-goal "allnc n^1,n^2,m^(
 TotalNat m^ -> EqPNat n^1 n^2 -> EqPNatNc(n^1+m^)(n^2+m^))")
(assume "n^1" "n^2" "m^" "Tm")
(elim "Tm")
;; 3,4
(ng #t)
(assume "n1=n2")
(use "n1=n2")
;; 4
(assume "m^1" "Tm1" "IH" "n1=n2")
(ng #t)
(use "EqPNatNcSucc")
(use "IH")
(use "n1=n2")
;; Proof finished.
;; (cdp)
(save "EqPNatNcPlus")

(set-totality-goal "NatLeastUp")

;; allnc n^(
;;      TotalNat n^ -> 
;;      allnc n^0(
;;       TotalNat n^0 -> 
;;       allnc pf^(
;;        allnc n^1(TotalNat n^1 -> TotalBoole(pf^ n^1)) -> 
;;        TotalNat(NatLeastUp n^ n^0 pf^))))

(assume "n^1" "Tn1" "n^2" "Tn2" "pf^" "Tpf")
(ng #t)
(use "BooleIfTotal")
(use "NatLeTotal")
(use "Tn1")
(use "Tn2")
(use "NatPlusTotal")
(use "NatLeastTotal")
(use "NatMinusTotal")
(use "Tn2")
(use "Tn1")
(ng #t)
(assume "n^3" "Tn3")
(use "Tpf")
(use "NatPlusTotal")
(use "Tn3")
(use "Tn1")
(use "Tn1")
(use "TotalNatZero")
;; Proof finished.
;; (cdp)
(save-totality)

;; ok, NatLeastUpTotal has been added as a new theorem.
;; ok, computation rule NatLeastUp n0 n nat=>boole ->
;;  [if (n0<=n) (NatLeast(n--n0)([m]nat=>boole(m+n0))+n0) 0] added

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n,n0,pf][if (n<=n0) (NatLeast(n0--n)([n1]pf(n1+n))+n) 0]

;; Moreover we have extensionality of NatLeastUp:

;; NatLeastUpExt
(set-goal
 (rename-variables (terms-to-eqp-formula (pt "NatLeastUp") (pt "NatLeastUp"))))

;; allnc n^(
;;      TotalNat n^ -> 
;;      allnc n^0(
;;       TotalNat n^0 -> 
;;       allnc pf^,pf^0(
;;        allnc n^1(TotalNat n^1 -> EqPBoole(pf^ n^1)(pf^0 n^1)) -> 
;;        EqPNat(NatLeastUp n^ n^0 pf^)(NatLeastUp n^ n^0 pf^0))))

(assume "n^1" "Tn1" "n^2" "Tn2" "pf^1" "pf^2" "EqPpf")
(ng #t)
(assert "EqPNat(NatLeast(n^2--n^1)([n]pf^1(n+n^1)))
               (NatLeast(n^2--n^1)([n]pf^2(n+n^1)))")
 (use "NatLeastExt")
 (use "NatMinusTotal")
 (use "Tn2")
 (use "Tn1")
 (ng #t)
 (assume "n^3" "Tn3")
 (use "EqPpf")
 (use "NatPlusTotal")
 (use "Tn3")
 (use "Tn1")
;; Assertion proved.
(assume "EqPHyp")
(assert "(NatLeast(n^2--n^1)([n]pf^1(n+n^1)))eqd
         (NatLeast(n^2--n^1)([n]pf^2(n+n^1)))")
 (use "EqPNatNcToEqD")
 (use "EqPHyp")
;; Assertion proved.
(assume "EqDHyp")
(simp "EqDHyp")
(use "EqPNatRefl")
(use "BooleIfTotal")
(use "NatLeTotal")
(use "Tn1")
(use "Tn2")
(use "NatPlusTotal")
(use "NatLeastTotal")
(use "NatMinusTotal")
(use "Tn2")
(use "Tn1")
(ng #t)
(assume "n^3" "Tn3")
(use "EqPBooleToTotalRight" (pt "pf^1(n^3+n^1)"))
(use "EqPpf")
(use "NatPlusTotal")
(use "Tn3")
(use "Tn1")
(use "Tn1")
(use "TotalNatZero")
;; Proof finished.
;; (cdp)
(save "NatLeastUpExt")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [n,n0,pf]cEqPNatRefl[if (n<=n0) (NatLeast(n0--n)([n1]pf(n1+n))+n) 0]

;; Same for nc

;; NatLeastUpTotalNc

(set-goal (rename-variables (term-to-totalnc-formula (pt "NatLeastUp"))))

;; allnc n^(
;;      TotalNatNc n^ -> 
;;      allnc n^0(
;;       TotalNatNc n^0 -> 
;;       allnc pf^(
;;        allnc n^1(TotalNatNc n^1 -> TotalBooleNc(pf^ n^1)) -> 
;;        TotalNatNc(NatLeastUp n^ n^0 pf^))))

(assume "n^1" "Tn1" "n^2" "Tn2" "pf^" "Tpf")
(ng #t)
(use "BooleIfTotal")
(use "NatLeTotal")
(use "Tn1")
(use "Tn2")
(use "NatPlusTotal")
(use "NatLeastTotal")
(use "NatMinusTotal")
(use "Tn2")
(use "Tn1")
(ng #t)
(assume "n^3" "Tn3")
(use "Tpf")
(use "NatPlusTotal")
(use "Tn3")
(use "Tn1")
(use "Tn1")
(use "TotalNatZero")
;; Proof finished.
;; (cdp)
(save "NatLeastUpTotalNc")

;; NatLeastUpExtNc
(set-goal (rename-variables
            (terms-to-eqpnc-formula (pt "NatLeastUp") (pt "NatLeastUp"))))

;; ?^1:allnc n^(
;;      TotalNatNc n^ -> 
;;      allnc n^0(
;;       TotalNatNc n^0 -> 
;;       allnc pf^,pf^0(
;;        allnc n^1(TotalNatNc n^1 -> EqPBooleNc(pf^ n^1)(pf^0 n^1)) -> 
;;        EqPNatNc(NatLeastUp n^ n^0 pf^)(NatLeastUp n^ n^0 pf^0))))

(assume "n^1" "Tn1" "n^2" "Tn2" "pf^1" "pf^2" "EqPpf")
(ng #t)
(assert "EqPNatNc(NatLeast(n^2--n^1)([n]pf^1(n+n^1)))
                 (NatLeast(n^2--n^1)([n]pf^2(n+n^1)))")
 (use "NatLeastExt")
 (use "NatMinusTotal")
 (use "Tn2")
 (use "Tn1")
 (ng #t)
 (assume "n^3" "Tn3")
 (use "EqPpf")
 (use "NatPlusTotal")
 (use "Tn3")
 (use "Tn1")
;; Assertion proved.
(assume "EqPHyp")
(assert "NatLeast(n^2--n^1)([n]pf^1(n+n^1))eqd
         NatLeast(n^2--n^1)([n]pf^2(n+n^1))")
 (use "EqPNatNcToEqD")
 (use "EqPHyp")
;; Assertion proved.
(assume "EqDHyp")
(simp "EqDHyp")
(use "EqPNatNcRefl")
(use "BooleIfTotalNc")
(use "NatLeTotal")
(use "Tn1")
(use "Tn2")
(use "NatPlusTotal")
(use "NatLeastTotal")
(use "NatMinusTotal")
(use "Tn2")
(use "Tn1")
(ng #t)
(assume "n^3" "Tn3")
(use "EqPBooleToTotalRight" (pt "pf^1(n^3+n^1)"))
(use "EqPpf")
(use "NatPlusTotal")
(use "Tn3")
(use "Tn1")
(use "Tn1")
(use "TotalNatZero")
;; Proof finished.
;; (cdp)
(save "NatLeastUpExtNc")

;; We postpone proofs of the NatLeastUpBound NatLeastUpLBound
;; NatLeastUpLeIntro NatLeastUpLtElim NatLeastUpZero since they use
;; monotonicity properties of NatLt which are only proved later.

;; We add some further rewrite rules and theorems.  The order is
;; somewhat delicate, since the proofs can depend on which rewrite
;; rules are present, and also which program constants have been proved
;; to be total.

(set-goal "all n,m n<=m+n")
(ind)
  (assume "n")
  (use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "n<=m+n" "True")

(set-goal "all n,m (n+m<n)=False")
(assert "all l,l0(l+l0<l -> F)")
 (ind)
 (assume "l" "Absurd")
 (use "Absurd")
 (assume "l" "IH")
 (cases)
 (assume "Absurd")
 (use "Absurd")
 (assume "l0")
 (ng #t)
 (assume "Succ(l+l0)<l")
 (use "IH" (pt "l0"))
 (use "NatLtTrans" (pt "Succ(l+l0)"))
 (use "Truth")
 (use "Succ(l+l0)<l")
(assume "Prop" "n" "m")
(use "AtomFalse")
(use "Prop")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "n+m<n" "False")

(set-goal "all n Pred n<=n")
(cases)
(use "Truth")
(assume "n")
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "Pred n<=n" "True")

(set-goal "all n 0--n=0")
(ind)
  (use "Truth")
(assume "n" "IH")
(ng #t)
(simp "IH")
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "0--n" "0")

(set-goal "all n,m n--m<=n")
(assume "n")
(ind)
  (use "Truth")
(assume "m" "IH")
(ng #t)
(use "NatLeTrans" (pt "n--m"))
(use "Truth")
(use "IH")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "n--m<=n" "True")

(set-goal "all n,m n+m--m=n")
(assume "n")
(ind)
  (use "Truth")
(assume "m" "IH")
(ng #t)
(use "IH")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "n+m--m" "n")

(set-goal "all n,m m+n--m=n")
(assume "n")
(ind)
  (use "Truth")
(assume "m" "IH")
(ng #t)
(use "IH")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "m+n--m" "n")

(set-goal "all n,m n*Pred m=n*m--n")
(assume "n")
(ind)
  (use "Truth")
(assume "m" "IH")
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "n*Pred m" "n*m--n")

(set-goal "all n,m Pred m*n=m*n--n")
(assume "n")
(ind)
  (use "Truth")
(assume "m" "IH")
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "Pred m*n" "m*n--n")

(set-goal "all n,m,l n--m--l=n--(m+l)")
(assume "n" "m")
(ind)
  (use "Truth")
(assume "l" "IH")
(ng #t)
(simp "IH")
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "n--m--l" "n--(m+l)")

(set-goal "all n,m,l n*(m--l)=n*m--n*l")
(assume "n" "m")
(ind)
  (use "Truth")
(assume "l" "IH")
(ng #t)
(simp "IH")
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "n*(m--l)" "n*m--n*l")

(set-goal "all n,m,l (m--l)*n=m*n--l*n")
(assume "n" "m")
(ind)
  (use "Truth")
(assume "l" "IH")
(ng #t)
(simp "IH")
(use "Truth")
;; Proof finished.
;; (cdp)
(add-rewrite-rule "(m--l)*n" "m*n--l*n")

;; SuccNatMinus
(set-goal "all m,n(m<n -> Succ(n--m)=Succ(n)--m)")
(ind)
(ng)
(strip)
(use "Truth")
(assume "m" "IH")
(cases)
(ng)
(assume "Absurd")
(use "Absurd")
(assume "n")
(use "IH")
;; Proof finished.
;; (cdp)
(save "SuccNatMinus")

;; NatLeMonPlus
(set-goal "all n,m,l,l0(n<=m -> l<=l0 -> n+l<=m+l0)")
(assume "n" "m")
(ind)
(ind)
(assume "n<=m" "Useless")
(use "n<=m")
(assume "l0" "IHl0")
(assume "n<=m" "Useless")
(use "NatLeTrans" (pt "m+l0"))
(use "IHl0")
(use "n<=m")
(use "Truth")
(use "Truth")
(assume "l" "IHl")
(cases)
(assume "Useless" "Absurd")
(use "EfAtom")
(use "Absurd")
(use "IHl")
;; Proof finished.
;; (cdp)
(save "NatLeMonPlus")

;; NatLeMonTimes
(set-goal "all n,m,l,l0(n<=m -> l<=l0 -> n*l<=m*l0)")
(assume "n" "m")
(ind)
(ind)
(assume "Useless1" "Useless2")
(use "Truth")
(assume "l0" "IHl0")
(assume "Useless1" "Useless2")
(use "Truth")
(assume "l" "IHl")
(cases)
(assume "Useless" "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "l0" "n<=m" "l<=l0")
(ng)
(use "NatLeMonPlus")
(use "IHl")
(use "n<=m")
(use "l<=l0")
(use "n<=m")
;; Proof finished.
;; (cdp)
(save "NatLeMonTimes")

;; NatLeMonPred
(set-goal "all n,m(n<=m -> Pred n<=Pred m)")
(cases)
(assume "m" "Useless")
(use "Truth")
(assume "n")
(cases)
(assume "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "m" "n<=m")
(use "n<=m")
;; Proof finished.
;; (cdp)
(save "NatLeMonPred")

;; NatLeMonMinus
(set-goal "all n,m,l,l0(n<=m -> l<=l0 -> n--l0<=m--l)")
(assume "n" "m" "l" "l0" "n<=m" "l<=l0")
(use "NatLeTrans" (pt "m--l0"))
;; ?_3: n--l0<=m--l0
(ind (pt "l0"))
(use "n<=m")
(assume "nat" "IH")
(ng #t)
(use "NatLeMonPred")
(use "IH")
;; ?_4: m--l0<=m--l
(assert "all nat5,nat6,nat7(nat5<=nat6 -> nat7--nat6<=nat7--nat5)")
 (ind)
 (assume "nat5" "nat6" "Useless")
 (use "Truth")
 (assume "nat5" "IH5")
 (cases)
 (assume "nat6" "Absurd")
 (use "EfAtom")
 (use "Absurd")
 (assume "nat6")
 (cases)
 (assume "Useless")
 (use "Truth")
 (assume "nat7")
 (ng)
 (use "IH5")
(assume "NatLeMonMinusRight")
(use "NatLeMonMinusRight")
(use "l<=l0")
;; Proof finished.
;; (cdp)
(save "NatLeMonMinus")

;; NatLeMonMax
(set-goal "all n,m,l,l0(n<=m -> l<=l0 -> n max l<=m max l0)")
(ind)
;; 2,3
(assume "m")
(cases)
(strip)
(use "Truth")
(assume "n" "l" "Useless" "Sn<=l")
(ng)
(use "NatLeTrans" (pt "l"))
(use "Sn<=l")
(use "NatMaxUB2")
;; 3
(assume "n" "IH")
(cases)
;; 13,14
(assume "l" "l0" "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
(assume "n1")
(cases)
(cases)
(ng)
(assume "n<=n1" "Useless")
(use "n<=n1")
(ng)
(assume "n2" "n<=n1" "Useless")
(use "NatLeTrans" (pt "n1"))
(use "n<=n1")
(use "NatMaxUB1")
(assume "n2")
(cases)
(assume "Useless" "Absurd")
(use "EfAtom")
(use "Absurd")
(ng)
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatLeMonMax")

;; NatPlusMinus
(set-goal "all n,m,l(l<=m -> n+(m--l)=n+m--l)")
(assume "n" "m")
(ind)
(assume "Useless")
(use "Truth")
(assume "l" "IH" "l+1<=m")
(ng #t)
(assert "all l0,l1(0<l1 -> l0+Pred l1=Pred(l0+l1))")
 (assume "l0")
 (cases)
 (assume "Absurd")
 (use "EfAtom")
 (use "Absurd")
 (assume "l1" "Useless")
 (use "Truth")
(assume "NatPlusPred")
(simp "<-" "IH")
(use "NatPlusPred")
(drop "IH" "NatPlusPred")
(use "NatLtLeTrans" (pt "Succ l--l"))
(use "Truth")
(use "NatLeMonMinus")
(use "l+1<=m")
(use "Truth")
(use "NatLeTrans" (pt "Succ l"))
(use "Truth")
(use "l+1<=m")
;; Proof finished.
;; (cdp)
(save "NatPlusMinus")

;; NatMinusPlus
(set-goal "all n,m,l(l<=n -> n--l+m=n+m--l)")
(assume "n" "m")
(ind)
(assume "Useless")
(use "Truth")
(assume "l" "IH" "l+1<=n")
(ng #t)
(assert "all l1,l0(0<l0 -> Pred l0+l1=Pred(l0+l1))")
 (assume "l1")
 (cases)
 (assume "Absurd")
 (use "EfAtom")
 (use "Absurd")
 (assume "l0" "Useless")
 (use "Truth")
(assume "NatPlusPred")
(simp "<-" "IH")
(use "NatPlusPred")
(drop "IH" "NatPlusPred")
(use "NatLtLeTrans" (pt "Succ l--l"))
(use "Truth")
(use "NatLeMonMinus")
(use "l+1<=n")
(use "Truth")
(use "NatLeTrans" (pt "Succ l"))
(use "Truth")
(use "l+1<=n")
;; Proof finished.
;; (cdp)
(save "NatMinusPlus")

;; NatMinusPlusEq
(set-goal "all n,m(m<=n -> n--m+m=n)")
(assume "n" "m" "m<=n")
(simp "NatMinusPlus")
(use "Truth")
(use "m<=n")
;; Proof finished.
;; (cdp)
(save "NatMinusPlusEq")

;; NatMinusMinus
(set-goal  "all n,m,l(l<=m -> m<=n+l -> n--(m--l)=n+l--m)")
(assume "n")
(ind)
(cases)
(assume "Useless1" "Useless2")
(use "Truth")
(assume "m" "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
(assume "m" "IHm")
(cases)
(assume "Useless1" "Useless2")
(use "Truth")
(assume "l" "l<=m" "m<=n+l")
(ng)
(use "IHm")
(use "l<=m")
(use "m<=n+l")
;; Proof finished.
;; (cdp)
(save "NatMinusMinus")

;; NatLtMonPlus1
(set-goal "all n,m,l,l0(n<m -> l<=l0 -> n+l<m+l0)")
(ind)
(cases)
(assume "l" "l0")
(ng #t)
(assume "Absurd" "Useless")
(use "EfAtom")
(use "Absurd")
(assume "m" "l" "l0" "Useless" "l<=l0")
(ng #t)
(use "NatLeToLtSucc")
(use "NatLeTrans" (pt "l0"))
(use "l<=l0")
(ng #t)
(use "Truth")
(assume "n" "IH")
(ng #t)
(cases)
(assume "l" "l0")
(ng #t)
(use "Efq")
(ng #t)
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatLtMonPlus1")

;; NatLtMonPlus2
(set-goal "all n,m,l,l0(n<=m -> l<l0 -> n+l<m+l0)")
(assume "n" "m")
(ind)
(cases)
(ng #t)
(assume "Useless" "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "l" "n<=m" "Useless")
(ng #t)
(use "NatLeToLtSucc")
(use "NatLeTrans" (pt "m"))
(use "n<=m")
(ng #t)
(use "Truth")
(assume "l" "IH")
(ng #t)
(cases)
(assume "n<=m")
(ng #t)
(use "Efq")
(ng #t)
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatLtMonPlus2")

;; NatLtMonMinusLeft
(set-goal "all n,m,l(m<l -> n<=m -> m--n<l--n)")
(ind)
(ng #t)
(assume "m" "l" "m<l" "Useless")
(use "m<l")
(assume "n" "IH")
(cases)
(ng #t)
(assume "l" "Useless" "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "m")
(cases)
(ng #t)
(assume "Absurd" "Useless")
(use "Absurd")
(assume "l")
(ng #t)
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatLtMonMinusLeft")

;; NatLtMonMinus
(set-goal "all n,m,l,l0(n<m -> l<=l0 -> l0<n -> n--l0<m--l)")
(assume "n" "m" "l" "l0" "n<m" "l<=l0" "l0<n")
(use "NatLtLeTrans" (pt "m--l0"))
;; n--l0<m--l0
(use "NatLtMonMinusLeft")
(use "n<m")
(use "NatLtToLe")
(use "l0<n")
;; m--l0<=m--l
(assert "all nat5,nat6,nat7(nat5<=nat6 -> nat7--nat6<=nat7--nat5)")
 (ind)
 (assume "nat5" "nat6" "Useless")
 (use "Truth")
 (assume "nat5" "IH5")
 (cases)
 (assume "nat6" "Absurd")
 (use "EfAtom")
 (use "Absurd")
 (assume "nat6")
 (cases)
 (assume "Useless")
 (use "Truth")
 (assume "nat7")
 (ng)
 (use "IH5")
(assume "NatLeMonMinusRight")
(use "NatLeMonMinusRight")
(use "l<=l0")
;; Proof finished.
;; (cdp)
(save "NatLtMonMinus")

;;  NatLeastUpBound
(set-goal "all n0,n,pf NatLeastUp n0 n pf<=n")
(assume "n0" "n" "pf")
(ng #t)
(cases (pt "n0<=n"))
(assume "n0<=n")
(ng #t)
(use "NatLeTrans" (pt "n--n0+n0"))
(use "NatLeMonPlus")
(use "NatLeastBound")
(use "Truth")
(simp "NatMinusPlusEq")
(use "Truth")
(use "n0<=n")
(strip)
(use "Truth")
;; Proof finished.
;; (cdp)
(save "NatLeastUpBound")

;; NatLeastUpLBound
(set-goal "all n0,n,pf(n0<=n -> n0<=NatLeastUp n0 n pf)")
(assume "n0" "n" "pf" "n0<=n")
(ng #t)
(simp "n0<=n")
(ng #t)
(use "Truth")
;; Proof finished.
;; (cdp)
(save "NatLeastUpLBound")

;; NatLeastUpLeIntro
(set-goal "all n0,n,m,pf(
 n0<=m -> pf m -> NatLeastUp n0 n pf<=m)")
(assume "n0" "n" "m" "pf" "n0<=m" "pf m")
(ng #t)
(cases (pt "n0<=n"))
(assume "n0<=n")
(ng #t)
(assert "NatLeast(n--n0)([nat]pf(nat+n0))<=m--n0")
 (use "NatLeastLeIntro")
 (ng #t)
 (simp "NatMinusPlusEq")
 (use "pf m")
 (use "n0<=m")
(assume "Assertion")
(assert
 "NatLeast(n--n0)([nat]pf(nat+n0))+n0<=m--n0+n0")
 (use "NatLeMonPlus")
 (use "Assertion")
 (use "Truth")
 (simp "NatMinusPlusEq")
(assume "Hyp")
(use "Hyp")
(use "n0<=m")
(strip)
(use "Truth")
;; Proof finished.
;; (cdp)
(save "NatLeastUpLeIntro")

;; NatLeastUpLtElim
(set-goal "all n0,n,pf(
 n0<=NatLeastUp n0 n pf ->
 NatLeastUp n0 n pf<n ->
 pf(NatLeastUp n0 n pf))")
(assume "n0" "n" "pf" "n0<=m" "m<n")
(ng #t)
(assert "n0<=n")
 (use "NatLeTrans" (pt "NatLeastUp n0 n pf"))
 (use "n0<=m")
 (use "NatLtToLe")
 (use "m<n")
(assume "n0<=n")
(simp "n0<=n")
(ng #t)
(use-with "NatLeastLtElim"
	  (pt "n--n0")
	  (pt "[nat](pf(nat+n0))") "?")
(ng "m<n")
(simphyp-with-to "m<n" "n0<=n" "SimpHyp")
(ng "SimpHyp")
(assert
 "NatLeast(n--n0)([nat]pf(nat+n0))+n0--n0<n--n0")
 (use "NatLtMonMinusLeft")
 (use "SimpHyp")
 (ng #t)
 (use "Truth")
(ng #t)
(assume "Hyp")
(use "Hyp")
;; Proof finished.
;; (cdp)
(save "NatLeastUpLtElim")

;; NatLeastUpZero
(set-goal "all n,pf
 NatLeastUp Zero n pf=NatLeast n pf")
(assume "n" "nat=>boole")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "NatLeastUpZero")
(add-rewrite-rule "NatLeastUp Zero n pf" "NatLeast n pf")

;; For totality of (Rec nat=>alpha) we need a general forms (with
;; alpha for nat) of

;; (pp "EqPNatRefl")
;; allnc n^(TotalNat n^ -> EqPNat n^ n^)

;; This is provable for closed finitary types (Lemma 3.3.1 ss19/ml).
;; We could take the general forms as global assumption, where alpha
;; ranges over closed finitary types.

;; (term-to-t-deg (pt "(Rec nat=>alpha)"))
;; 1

(add-var-name "x" (py "alpha"))
(add-var-name "f" (py "nat=>alpha=>alpha"))

(set-goal (rename-variables (term-to-totality-formula (pt "(Rec nat=>alpha)"))))
(assume "n^" "Tn" "x^" "Tx" "f^" "Tf")
(elim "Tn")
;; 3,4
(ng #t)
(use "Tx")
;; 4
(assume "n^1" "Tn1" "IH")
(ng #t)
(use "Tf")
(use "Tn1")
(use "IH")
;; Proof finished.
;; (cdp)
;; (save-totality) ;does not work here
(save "NatRecTotal")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

(animate "NatRecTotal")

;; NatRecExt
(set-goal (rename-variables (terms-to-eqp-formula
			     (pt "(Rec nat=>alpha)")
			     (pt "(Rec nat=>alpha)"))))

;; allnc n^(
;;      TotalNat n^ -> 
;;      allnc x^,x^0(
;;       EqP x^ x^0 -> 
;;       allnc f^,f^0(
;;        allnc n^0(
;;         TotalNat n^0 -> 
;;         allnc x^1,x^2(
;;          EqP x^1 x^2 -> EqP(f^ n^0 x^1)(f^0 n^0 x^2))) -> 
;;        EqP((Rec nat=>alpha)n^ x^ f^)((Rec nat=>alpha)n^ x^0 f^0))))

(assert "allnc x^,x^0(
     EqP x^ x^0 -> 
     allnc f^,f^0(
      allnc n^(
       TotalNat n^ -> 
       allnc x^1,x^2(
        EqP x^1 x^2 -> EqP(f^ n^ x^1)(f^0 n^ x^2))) -> 
      allnc n^(
       TotalNat n^ -> 
       EqP((Rec nat=>alpha)n^ x^ f^)((Rec nat=>alpha)n^ x^0 f^0))))")
(assume "x^1" "x^2" "EqPx1x2" "f^1" "f^2" "EqPf1f2" "n^" "Tn")
(elim "Tn")
;; 5,6
(ng #t)
(use "EqPx1x2")
;; 6
(assume "n^1" "Tn1" "IH")
(ng #t)
(use "EqPf1f2")
(use "Tn1")
(use "IH")
;; Assertion proved.
(assume "Assertion"
	"n^" "Tn" "x^1" "x^2" "EqPx1x2" "f^1" "f^2" "EqPf1f2")
(use "Assertion")
(use "EqPx1x2")
(use "EqPf1f2")
(use "Tn")
;; Proof finished.
;; (cdp)
(save "NatRecExt")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; (Rec nat=>alpha)

(animate "NatRecExt")
;; ok, computation rule (cNatRecExt alpha) -> (Rec nat=>alpha) added

;; NatDouble
(add-program-constant "NatDouble" (py "nat=>nat"))

(add-computation-rules
 "NatDouble Zero" "Zero"
 "NatDouble(Succ n)" "Succ(Succ(NatDouble n))")

(set-totality-goal "NatDouble")
(assume "n^" "Tn")
(elim "Tn")
(use "TotalNatZero")
(assume "m^" "Tm" "IH")
(ng #t)
(use "TotalNatSucc")
(use "TotalNatSucc")
(use "IH")
;; Proof finished.
;; (cdp)
(save-totality)

;; (cdp (proof-to-soundness-proof))
;; (pp (rename-variables (proof-to-formula (proof-to-soundness-proof))))
;; allnc n^,n^0(
;;  TotalNatMR n^ n^0 -> 
;;  TotalNatMR(NatDouble n^)((Rec nat=>nat)n^0 0([n^1,n^2]Succ(Succ n^2))))

;; NatMaxDouble
(set-goal "all n,m NatDouble n max NatDouble m=NatDouble(n max m)")
(ind)
(assume "m")
(ng)
(use "Truth")
(assume "n" "IH")
(cases)
(ng)
(use "Truth")
(ng)
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatMaxDouble")

;; NatMinDouble
(set-goal "all n,m NatDouble n min NatDouble m=NatDouble(n min m)")
(ind)
(assume "m")
(ng)
(use "Truth")
(assume "n" "IH")
(cases)
(ng)
(use "Truth")
(ng)
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatMinDouble")

(add-program-constant "NatEven" (py "nat=>boole"))

(add-computation-rules
 "NatEven Zero" "True"
 "NatEven(Succ Zero)" "False"
 "NatEven(Succ(Succ n))" "NatEven n")

(set-totality-goal "NatEven")
(assert "allnc n^(TotalNat n^ ->
         TotalBoole(NatEven(Succ n^)) andd
         TotalBoole(NatEven(Succ(Succ n^))))")
 (assume "n^" "Tn")
 (elim "Tn")
 (ng #t)
 (split)
 (use "TotalBooleFalse")
 (use "TotalBooleTrue")
 (assume "m^" "Tm" "IH")
 (ng)
 (split)
 (use "IH")
 (use "IH")
(assume "NatEvenTotalAux")
(ng)
(assume "n^" "Tn")
(use "NatEvenTotalAux")
(use "Tn")
;; Proof finished.
;; (cdp)
(save-totality)

;; NatEvenDouble
(set-goal "all n NatEven(NatDouble n)")
(ind)
(ng #t)
(use "Truth")
(assume "n" "IH")
(ng #t)
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatEvenDouble")

;; NatEvenSucc
(set-goal "all n(NatEven n -> NatEven(Succ n) -> F)")
(ind)
(ng #t)
(assume "Useless" "Absurd")
(use "Absurd")
(assume "n" "IH" "ESn" "ESSn")
(ng "ESSn")
(use "IH")
(use "ESSn")
(use "ESn")
;; Proof finished.
;; (cdp)
(save "NatEvenSucc")

;; NatOddSuccToEven
(set-goal "all n((NatEven(Succ n) -> F) ->NatEven n)")
(ind)
(ng #t)
(strip)
(use "Truth")
(assume "n" "IH" "OSSn")
(cases (pt "NatEven(Succ n)"))
(strip)
(use "Truth")
(assume "OSn")
(use "OSSn")
(ng #t)
(use "IH")
(use "OSn")
;; Proof finished
;; (cdp)
(save "NatOddSuccToEven")

(add-program-constant "NatHalf" (py "nat=>nat"))

(add-computation-rules
 "NatHalf Zero" "Zero"
 "NatHalf(Succ Zero)" "Zero"
 "NatHalf(Succ(Succ n))" "Succ(NatHalf n)")

(set-totality-goal "NatHalf")
(assert "allnc n^(TotalNat n^ -> TotalNat(NatHalf n^) andd
                                 TotalNat(NatHalf(Succ n^)))")
 (assume "n^" "Tn")
 (elim "Tn")
 (ng #t)
 (split)
 (use "TotalNatZero")
 (use "TotalNatZero")
 (assume "m^" "Tm" "IH")
 (split)
 (use "IH")
 (ng #t)
 (use "TotalNatSucc")
 (use "IH")
(assume "NatHalfTotalAux")
(assume "n^" "Tn")
(use "NatHalfTotalAux")
(use "Tn")
;; Proof finished.
;; (cdp)
(save-totality)

;; NatHalfDouble
(set-goal "all n NatHalf(NatDouble n)=n")
(ind)
(ng #t)
(use "Truth")
(assume "n" "IH")
(ng #t)
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatHalfDouble")

;; NatHalfSuccDouble
(set-goal "all n NatHalf(Succ(NatDouble n))=n")
(ind)
(ng #t)
(use "Truth")
(assume "n" "IH")
(ng #t)
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatHalfSuccDouble")

;; NatPlusDouble
(set-goal "all n,m NatDouble n+NatDouble m=NatDouble(n+m)")
(assume "n")
(ind)
(use "Truth")
(assume "m" "IH")
(ng #t)
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatPlusDouble")

;; NatDoubleLt
(set-goal "all n,m (NatDouble n<NatDouble m)=(n<m)")
(ind)
(ng)
(cases)
(use "Truth")
(strip)
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
(ng)
(use "Truth")
(ng)
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatDoubleLt")

;; NatDoubleLe
(set-goal "all n,m (NatDouble n<=NatDouble m)=(n<=m)")
(ind)
(ng)
(strip)
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
(ng)
(use "Truth")
(ng)
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatDoubleLe")

;; NatLt0Double
(set-goal "all n(Zero<n -> Zero<NatDouble n)")
(cases)
(assume "Absurd")
(use "Absurd")
(strip)
(use "Truth")
;; Proof finished
;; (cdp)
(save "NatLt0Double")

;; NatLeDouble
(set-goal "all n n<=NatDouble n")
(ind)
(use "Truth")
(assume "n" "IH")
(ng)
(use "NatLeTrans" (pt "NatDouble n"))
(use "IH")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "NatLeDouble")

;; NatLtDouble
(set-goal "all n(Zero<n -> n<NatDouble n)")
(ind)
(assume "Absurd")
(use "Absurd")
;; Step
(assume "n" "IH" "Useless")
(ng)
(use "NatLeLtTrans" (pt "NatDouble n"))
(use "NatLeDouble")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "NatLtDouble")

;; NatDoubleMinus
(set-goal "all n,m NatDouble(n--m)=NatDouble n--NatDouble m")
(ind)
;; 2-3
(ng)
(strip)
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
;; 7,8
(ng)
(use "Truth")
;; 8
(ng)
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatDoubleMinus")

;; NatLtSZeroSOne 
;; NatLtSOneSZero
;; NatLtSOneSOne

;; NatLeSZeroSOne
;; NatLeSOneSZero
;; NatLeSOneSOne

;; NatLtOneSZero
;; NatLtOneSOne

;; NatLeSZeroOne
;; NatLtSZeroOne

;; moved here from numbers.scm.  The terminology comes from pos: Double
;; for NatDouble, SOne for Succ(NatDouble)

;; NatLtDoubleSuccDouble
(set-goal "all n,m (NatDouble n<Succ(NatDouble m))=(n<=m)")
(ind) ;2-3
(assume "m")
(ng #t)
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
(ng #t)
(use "Truth")
(assume "m")
(ng #t)
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatLtDoubleSuccDouble")

;; NatLtSuccDoubleDouble
(set-goal "all n,m (Succ(NatDouble n)<NatDouble m)=(n<m)")
(ind) ;2-3
(cases)
(ng #t)
(use "Truth")
(assume "m")
(ng #t)
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
(ng #t)
(use "Truth")
(assume "m")
(ng #t)
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatLtSuccDoubleDouble")

;; NatLtSuccDoubleSuccDouble
(set-goal "all n,m
 (Succ(NatDouble n)<Succ(NatDouble m))=(n<m)")
(ind) ;2-3
(cases)
(ng #t)
(strip)
(use "Truth")
(assume "m")
(ng #t)
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
(ng #t)
(use "Truth")
(assume "m")
(ng #t)
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatLtSuccDoubleSuccDouble")

;; NatLeDoubleSuccDouble
(set-goal "all n,m (NatDouble n<=Succ(NatDouble m))=(n<=m)")
(ind) ;2-3
(assume "m")
(ng #t)
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
(ng #t)
(use "Truth")
(assume "m")
(ng #t)
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatLeDoubleSuccDouble")

;; NatLeSuccDoubleDouble
(set-goal "all n,m (Succ(NatDouble n)<=NatDouble m)=(n<m)")
(ind) ;2-3
(cases)
(ng #t)
(use "Truth")
(assume "m")
(ng #t)
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
(ng #t)
(use "Truth")
(assume "m")
(ng #t)
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatLeSuccDoubleDouble")

;; NatLeSuccDoubleSuccDouble
(set-goal "all n,m
 (Succ(NatDouble n)<=Succ(NatDouble m))=(n<=m)")
(ind) ;2-3
(ng #t)
(strip)
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
(ng #t)
(use "Truth")
(assume "m")
(ng #t)
(use "IH")
;; Proof finished.
;; (cdp)
(save "NatLeSuccDoubleSuccDouble")

;; NatLtOneDouble
(set-goal "all n(Zero<n -> Succ Zero<NatDouble n)")
(cases)
(assume "Absurd")
(use "Absurd")
(ng #t)
(strip)
(use "Truth")
;; Proof finished.
;; (cdp)
(save "NatLtOneDouble")

;; NatLtOneSuccDouble
(set-goal "all n(Zero<n -> Succ Zero<Succ(NatDouble n))")
(assume "n" "0<n")
(use "NatLtTrans" (pt "NatDouble n"))
(use "NatLtOneDouble")
(use "0<n")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "NatLtOneSuccDouble")

;; NatLeDoubleOne
(set-goal "all n(Zero<n -> NatDouble n<=Succ Zero -> F)")
(cases)
(assume "Absurd" "Useless")
(use "Absurd")
(ng #t)
(assume "n" "Useless" "Absurd")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "NatLeDoubleOne")

;; NatLtDoubleOne
(set-goal "all n(Zero<n -> NatDouble n<Succ Zero -> F)")
(cases)
(assume "Absurd" "Useless")
(use "Absurd")
(ng #t)
(assume "n" "Useless" "Absurd")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "NatLtDoubleOne")

;; Reason to have a local efq assumption in CVIndPvar: soundness proof
;; does not normalize for Efq a global assumption.  Check

;; CVIndPvar
(set-goal "(F -> allnc n^(Pvar nat)n^) ->
  all n(all m(m<n -> (Pvar nat)m) -> (Pvar nat)n) ->
  all n (Pvar nat)n")
(assume "efq" "Prog")
(assert "all n,m(m<n -> (Pvar nat)m)")
 (ind)
 (assume "m" "Absurd")
 (use "efq")
 (use "Absurd")
 (assume "n" "IHn" "m" "m<Succ n")
 (use "NatLtSuccCases" (pt "m") (pt "n"))
 (use "m<Succ n")
 (use "IHn")
 (assume "m=n")
 (simp "m=n")
 (use "Prog")
 (use "IHn")
(assume "Assertion" "n")
(use "Assertion" (pt "Succ n"))
(use "Truth")
;; Proof finished.
;; (cdp)
(save "CVIndPvar")

;; (define sproof (proof-to-soundness-proof))
;; (define nsproof (np sproof))
;; (cdp nsproof)
;; (proof-to-expr-with-formulas nsproof)

;; In CVInd we do not need an Efq assumption since EfEqD is avaiable
;; (pp "EfEqD")
;; F -> all alpha^,alpha^0 alpha^ eqd alpha^0

;; CVInd
(set-goal "all pf(all n(all m(m<n -> pf m) -> pf n) -> all n pf n)")
(assume "pf" "Prog")
(assert "all n,m(m<n -> pf m)")
 (ind)
 (assume "m" "Absurd")
 (use "EfAtom")
 (use "Absurd")
 (assume "n" "IHn" "m" "m<Succ n")
 (use "NatLtSuccCases" (pt "m") (pt "n"))
 (use "m<Succ n")
 (use "IHn")
 (assume "m=n")
 (simp "m=n")
 (use "Prog")
 (use "IHn")
(assume "Assertion" "n")
(use "Assertion" (pt "Succ n"))
(use "Truth")
;; Proof finished.
;; (cdp)
(save "CVInd")

;; NatHalfLt
(set-goal "all n(Zero<n -> NatHalf n<n)")
(assert "all n((Zero<n -> NatHalf n<n) andnc NatHalf(Succ n)<Succ n)")
(use "CVIndPvar")
(assume "Absurd" "n^")
(split)
(strip)
(use "EfAtom")
(use "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "n" "Prog")
(split)
(cases (pt "n"))
(assume "Useless" "Absurd")
(use "Absurd")
(assume "l" "n=Sl" "Useless")
(use-with "Prog" (pt "l") "?" 'right)
(simp "n=Sl")
(use "Truth")
;; 14
(cases (pt "n"))
(ng #t)
(strip)
(use "Truth")
(assume "l" "n=Sl")
(ng #t)
(cases (pt "l"))
(ng #t)
(strip)
(use "Truth")
(assume "m" "l=Sm")
(simp "<-" "l=Sm")
(use "NatLtTrans" (pt "l"))
(use "Prog")
(simp "n=Sl")
(use "Truth")
(simp "l=Sm")
(use "Truth")
(use "Truth")
;; Assertion proved.
(assume "NatHalfLtAux" "n")
(use "NatHalfLtAux")
;; Proof finished.
;; (cdp)
(save "NatHalfLt")

;; NatHalfLtSucc
(set-goal "all n NatHalf n<Succ n")
(use "CVInd")
(assume "n" "Prog")
(cases (pt "n"))
(ng #t)
(strip)
(use "Truth")
(assume "m" "n=Sm")
(cases (pt "m"))
(ng #t)
(strip)
(use "Truth")
(assume "l" "m=Sl")
(ng #t)
(use "NatLtTrans" (pt "Succ l"))
(use "Prog")
(use "NatLtTrans" (pt "m"))
(simp "m=Sl")
(use "Truth")
(simp "n=Sm")
(use "Truth")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "NatHalfLtSucc")

;; NatDoubleHalfEven
(set-goal "all n(NatEven n -> NatDouble(NatHalf n)=n)")
(assert "all n((NatEven n -> NatDouble(NatHalf n)=n) andnc
               (NatEven(Succ n) -> NatDouble(NatHalf(Succ n))=Succ n))")
(ind)
(split)
(ng #t)
(strip)
(use "Truth")
(ng #t)
(assume "Absurd")
(use "Absurd")
(assume "n" "IHn")
(split)
(use "IHn")
(ng #t)
(use "IHn")
;; Assertion proved.
(assume "NatDoubleHalfEvenAux" "n")
(use "NatDoubleHalfEvenAux")
;; Proof finished.
;; (cdp)
(save "NatDoubleHalfEven")

;; NatDoubleHalfOdd
(set-goal "all n((NatEven n -> F) -> Succ(NatDouble(NatHalf n))=n)")
(assert "all n(
   ((NatEven n -> F) -> Succ(NatDouble(NatHalf n))=n) andnc
   ((NatEven(Succ n) -> F) -> Succ(NatDouble(NatHalf(Succ n)))=Succ n))")
(ind)
(split)
(ng #t)
(assume "Absurd")
(use "Absurd")
(use "Truth")
(ng #t)
(strip)
(use "Truth")
(assume "n" "IHn")
(split)
(use "IHn")
(ng #t)
(use "IHn")
;; Assertion proved.
(assume "NatDoubleHalfOddAux" "n")
(use "NatDoubleHalfOddAux")
;; Proof finished.
;; (cdp)
(save "NatDoubleHalfOdd")

;; NatLtZeroHalfEven
(set-goal "all n(Zero<n -> NatEven n -> Zero<NatHalf n)")
(cases)
(assume "Absurd" "Useless")
(use "Absurd")
(cases)
(assume "Useless" "Absurd")
(use "Absurd")
(assume "n" "Useless1" "Useless2")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "NatLtZeroHalfEven")

;; NatLtZeroHalfFinally
(set-goal "all n(Zero<n -> (n=Succ Zero -> F) -> Zero<NatHalf n)")
(cases)
(ng #t)
(assume "Absurd" "Useless")
(use "Absurd")
(cases)
(ng #t)
(assume "Useless" "Absurd")
(use "Absurd")
(use "Truth")
(ng #t)
(strip)
(use "Truth")
;; Proof finished.
;; (cdp)
(save "NatLtZeroHalfFinally")

;; For use with grec we add

(define natlt-obj (nbe-term-to-object (pt "NatLt") '()))

;; For the translation to Haskell we add

(add-program-constant "TranslationNatMinusPosDiff" (py "nat=>nat=>nat"))

;; 2019-05-22.  Done up to this point.

;; The following are derivable from what we have
;; ;; TotalNatMRToEqD
;; (set-goal "allnc n^,m^(TotalNatMR m^ n^ -> n^ eqd m^)")
;; (assume "n^" "m^" "TMRHyp")
;; (elim "TMRHyp")
;; ;; 3,4
;; (use "InitEqD")
;; ;; 4
;; (assume "n^1" "m^1" "Useless" "EqHyp")
;; (simp "EqHyp")
;; (use "InitEqD")
;; ;; Proof finished.
;; ;; (cdp)
;; (save "TotalNatMRToEqD")

;; ;; TotalNatMRToTotalNc
;; (set-goal "allnc n^,m^(TotalNatMR m^ n^ -> TotalNatNc n^)")
;; (assume "n^" "m^" "TMRHyp")
;; (elim "TMRHyp")
;; ;; 3,4
;; (use "TotalNatNcZero")
;; ;; 4
;; (assume "n^1" "m^1" "TMRm1n1Hyp")
;; (use "TotalNatNcSucc")
;; ;; Proof finished.
;; ;; (cdp)
;; (save "TotalNatMRToTotalNc")

;; ;; TotalNatToTotalMR
;; (set-goal "allnc n^(TotalNat n^ -> TotalNatMR n^ n^)")
;; (assume "n^" "Tn")
;; (elim "Tn")
;; ;; 3,4
;; (use "TotalNatZeroMR")
;; ;; 4
;; (assume "n^1" "Tn1")
;; (use "TotalNatSuccMR")
;; ;; Proof finished.
;; ;; (cdp)
;; (save "TotalNatToTotalMR")

;; (display-default-varnames)

;; f: 	nat=>alpha=>alpha
;; x: 	alpha
;; nf: 	nat=>nat
;; pf: 	nat=>boole
;; n: 	nat

(remove-var-name "f")
(remove-var-name "x")
(remove-var-name "pf")
(remove-var-name "nf")

;; We keep the var names n m l of type nat
