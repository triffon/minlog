;; 2019-08-23.  listext.scm

(if (not (assoc "nat" ALGEBRAS))
    (myerror "First execute (libload \"nat.scm\")"))

(if (not (assoc "list" ALGEBRAS))
    (myerror "First execute (libload \"list.scm\")"))

(display "loading listext.scm ...") (newline)

(add-var-name "x" (py "alpha"))
(add-var-name "xs" (py "list alpha"))

;; 1-1-1-2.  Properties
;; ====================

;; 1-1-1-2-1.  Ex falso
;; ====================

;; For each of the 8 idpcs in 1-1-1-1 we have an ex-falso property

;; EfRTotalList
;; EfNTotalList
;; EfNTotalListNc
;; EfTotalList
;; EfANTotalList
;; EfSTotalList
;; EfTotalListNc
;; EfSTotalListNc

;; EfRTotalList
(set-goal "allnc xs^(F -> (RTotalList (cterm (x^) (Pvar alpha) x^))xs^)")
(assume "xs^" "Absurd")
(simp (pf "xs^ eqd (Nil alpha)"))
(use "RTotalListNil")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfRTotalList")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; (Nil gamma)

;; EfNTotalList
(set-goal "allnc xs^(F -> (NTotalList (cterm (x^) (Pvar alpha)^ x^))xs^)")
(assume "xs^" "Absurd")
(simp (pf "xs^ eqd (Nil alpha)"))
(use "NTotalListNil")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfNTotalList")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; 0

;; EfNTotalListNc
(set-goal "allnc xs^(F -> (NTotalListNc (cterm (x^) (Pvar alpha)^ x^))xs^)")
(assume "xs^" "Absurd")
(simp (pf "xs^ eqd (Nil alpha)"))
(use "NTotalListNcNil")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfNTotalListNc")

;; EfTotalList
(set-goal "allnc xs^(F -> TotalList xs^)")
(assume "xs^" "Absurd")
(simp (pf "xs^ eqd (Nil alpha)"))
(use "TotalListNil")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfTotalList")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; (Nil alpha)

;; EfANTotalList
(set-goal "allnc xs^(F -> ANTotalList xs^)")
(assume "xs^" "Absurd")
(simp (pf "xs^ eqd (Nil alpha)"))
(use "ANTotalListNil")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfANTotalList")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; 0

;; EfSTotalList
(set-goal "allnc xs^(F -> STotalList xs^)")
(assume "xs^" "Absurd")
(simp (pf "xs^ eqd (Nil alpha)"))
(use "STotalListNil")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfSTotalList")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; 0

;; EfTotalListNc
(set-goal "allnc xs^(F -> TotalListNc xs^)")
(assume "xs^" "Absurd")
(simp (pf "xs^ eqd (Nil alpha)"))
(use "TotalListNcNil")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfTotalListNc")

;; EfSTotalListNc
(set-goal "allnc xs^(F -> STotalListNc xs^)")
(assume "xs^" "Absurd")
(simp (pf "xs^ eqd (Nil alpha)"))
(use "STotalListNcNil")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfSTotalListNc")

;; 1-1-1-2-2.   Monotonicity
;; =========================

;; ListRTotalMon
(set-goal "allnc x^((Pvar alpha)_1 x^ -> (Pvar alpha)_2 x^) ->
 allnc xs^((RTotalList (cterm (x^) (Pvar alpha)_1 x^))xs^ ->
           (RTotalList (cterm (x^) (Pvar alpha)_2 x^))xs^)")
(assume "MonHyp" "xs^")
(elim)
(intro 0)
(assume "x^" "Yx" "xs^1" "Useless" "RTZxs1")
(intro 1)
(use "MonHyp")
(use "Yx")
(use "RTZxs1")
;; Proof finished.
;; (cdp)
(save "ListRTotalMon")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [(alpha604=>alpha603),(list alpha604)]
;;  (Rec list alpha604=>list alpha603)(list alpha604)(Nil alpha603)
;;  ([alpha604,(list alpha604)_0](Cons alpha603)((alpha604=>alpha603)alpha604))

;; For ListNTotalMon we first had (by an oversight):
;; (set-goal "allnc x^((Pvar alpha)_1 x^ -> (Pvar alpha)_2 x^) ->
;;  allnc xs^((NTotalList (cterm (x^) (Pvar alpha)_1 x^))xs^ ->
;;            (NTotalList (cterm (x^) (Pvar alpha)_2 x^))xs^)")
;; with an unsharp psubst: NTotalList has n.c. parameter pvars
;; This resulted in an error at save: Succ occurs.
;; With the new idpredconst-name-and-types-and-cterms-to-idpredconst
;; the error should be detected earlier, at parse time.
;; After change of check-aconst the error is discovered by cdp already.

;; ListNTotalMon
(set-goal "allnc x^((Pvar alpha)^1 x^ -> (Pvar alpha)^2 x^) ->
 allnc xs^((NTotalList (cterm (x^) (Pvar alpha)^1 x^))xs^ ->
           (NTotalList (cterm (x^) (Pvar alpha)^2 x^))xs^)")
(assume "MonHyp" "xs^")
(elim)
(intro 0)
(assume "x^" "Yx" "xs^1" "NTYxs1" "NTZxs1")
(intro 1)
(use "MonHyp")
(use "Yx")
(use "NTZxs1")
;; Proof finished.
;; (cdp)
(save "ListNTotalMon")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n](Rec nat=>nat)n 0([n0]Succ)

;; ListNTotalMonNc
(set-goal "allnc x^((Pvar alpha)^1 x^ -> (Pvar alpha)^2 x^) ->
 allnc xs^((NTotalListNc (cterm (x^) (Pvar alpha)^1 x^))xs^ ->
           (NTotalListNc (cterm (x^) (Pvar alpha)^2 x^))xs^)")
(assume "MonHyp" "xs^")
(elim)
(intro 0)
(assume "x^" "Yx" "xs^1" "Useless" "NTZxs1")
(intro 1)
(use "MonHyp")
(use "Yx")
(use "NTZxs1")
;; Proof finished.
;; (cdp)
(save "ListNTotalMonNc")

;; 1-1-1-2-3.  Connections
;; =======================

;; NTotalListToNTotalNc
;; RTotalListToRTotalNc
;; STotalListToSTotalNc

;; ANTotalListToSTotal
(set-goal "allnc xs^(ANTotalList xs^ -> STotalList xs^)")
(assume "xs^" "ANTxs")
(elim "ANTxs")
;; 3,4
(use "STotalListNil")
;; 4
(assume "x^1" "Tx1" "xs^1" "ANTxs1")
(use "STotalListCons")
;; Proof finished.
;; (cdp)
(save "ANTotalListToSTotal")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [n](Rec nat=>nat)n 0([n0]Succ)

;; TotalListNcToSTotalNc
(set-goal "allnc xs^(TotalListNc xs^ -> STotalListNc xs^)")
(assume "xs^" "Txs")
(elim "Txs")
;; 3,4
(use "STotalListNcNil")
;; 4
(assume "x^1" "Tx1" "xs^1" "Txs1")
(use "STotalListNcCons")
;; Proof finished.
;; (cdp)
(save "TotalListNcToSTotalNc")

;; 1-1-2.  CoTotal
;; ===============

;; 1-1-2-2.  Properties
;; ====================

;; 1-1-2-2-1.  Monotonicity
;; ========================

;; ListCoRTotalMon
(set-goal "allnc x^((Pvar alpha)_1 x^ -> (Pvar alpha)_2 x^) ->
 allnc xs^((CoRTotalList (cterm (x^) (Pvar alpha)_1 x^))xs^ ->
           (CoRTotalList (cterm (x^) (Pvar alpha)_2 x^))xs^)")
(assume "MonHyp" "xs^" "CoRHyp1")
(coind "CoRHyp1")
(assume "xs^1" "CoRHyp2")
(inst-with-to
 "CoRTotalListClause"
 (make-cterm (pv "x^") (pf "(Pvar alpha)_1 x^"))
 (pt "xs^1") "CoRHyp2" "Inst")
(elim "Inst")
;; 7,8
(drop "Inst")
(assume "xs1=Nil")
(intro 0)
(use "xs1=Nil")
;; 8
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^2" "x2Prop")
(inst-with-to "x2Prop" 'left "Px2")
(inst-with-to "x2Prop" 'right "ExHyp2")
(drop "x2Prop")
(by-assume "ExHyp2" "xs^2" "x2xs2Prop")
(intro 1)
(intro 0 (pt "x^2"))
(split)
(use "MonHyp")
(use "Px2")
(intro 0 (pt "xs^2"))
(split)
(intro 1)
(use "x2xs2Prop")
(use "x2xs2Prop")
;; Proof finished.
;; (cdp)
(save "ListCoRTotalMon")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [(alpha604=>alpha603),(list alpha604)]
;;  (CoRec list alpha604=>list alpha603)(list alpha604)
;;  ([(list alpha604)_0]
;;    [if (DesYprod(list alpha604)_0)
;;      (DummyL alpha603 yprod(list alpha603 ysum list alpha604))
;;      ([(alpha604 yprod list alpha604)]
;;       Inr((alpha604=>alpha603)clft(alpha604 yprod list alpha604)pair
;;           (InR (list alpha604) (list alpha603))
;;           crht(alpha604 yprod list alpha604)))])

;; ListCoNTotalMon
(set-goal "allnc x^((Pvar alpha)^1 x^ -> (Pvar alpha)^2 x^) ->
 allnc xs^((CoNTotalList (cterm (x^) (Pvar alpha)^1 x^))xs^ ->
           (CoNTotalList (cterm (x^) (Pvar alpha)^2 x^))xs^)")
(assume "MonHyp" "xs^" "CoNHyp1")
(coind "CoNHyp1")
(assume "xs^1" "CoNHyp2")
(inst-with-to
 "CoNTotalListClause"
 (make-cterm (pv "x^") (pf "(Pvar alpha)^1 x^"))
 (pt "xs^1") "CoNHyp2" "Inst")
(elim "Inst")
;; 7,8
(drop "Inst")
(assume "xs1=Nil")
(intro 0)
(use "xs1=Nil")
;; 8
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^2" "x2Prop")
(inst-with-to "x2Prop" 'left "Px2")
(inst-with-to "x2Prop" 'right "ExHyp2")
(drop "x2Prop")
(by-assume "ExHyp2" "xs^2" "x2xs2Prop")
(intro 1)
(intro 0 (pt "x^2"))
(split)
(use "MonHyp")
(use "Px2")
(intro 0 (pt "xs^2"))
(split)
(intro 1)
(use "x2xs2Prop")
(use "x2xs2Prop")
;; Proof finished.
;; (cdp)
(save "ListCoNTotalMon")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n]
;;  (CoRec nat=>nat)n
;;  ([n0]e[if (Des n0) (DummyL nat ysum nat) ([n1]Inr((InR nat nat)n1))])

;; ListCoNTotalMonNc
(set-goal "allnc x^((Pvar alpha)^1 x^ -> (Pvar alpha)^2 x^) ->
 allnc xs^((CoNTotalListNc (cterm (x^) (Pvar alpha)^1 x^))xs^ ->
           (CoNTotalListNc (cterm (x^) (Pvar alpha)^2 x^))xs^)")
(assume "MonHyp" "xs^" "CoNHyp1")
(coind "CoNHyp1")
(assume "xs^1" "CoNHyp2")
(inst-with-to
 "CoNTotalListNcClause"
 (make-cterm (pv "x^") (pf "(Pvar alpha)^1 x^"))
 (pt "xs^1") "CoNHyp2" "Inst")
(elim "Inst")
;; 7,8
(drop "Inst")
(assume "xs1=Nil")
(intro 0)
(use "xs1=Nil")
;; 8
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^2" "x2Prop")
(inst-with-to "x2Prop" 'left "Px2")
(inst-with-to "x2Prop" 'right "ExHyp2")
(drop "x2Prop")
(by-assume "ExHyp2" "xs^2" "x2xs2Prop")
(intro 1)
(intro 0 (pt "x^2"))
(split)
(use "MonHyp")
(use "Px2")
(intro 0 (pt "xs^2"))
(split)
(intro 1)
(use "x2xs2Prop")
(use "x2xs2Prop")
;; Proof finished.
;; (cdp)
(save "ListCoNTotalMonNc")

;; 1-1-2-2-2.  Total implies CoTotal
;; =================================

;; For the 8 variants of TotalList defined in 1-1-1-1 we prove that the
;; original predicates are contained in their duals.  Their ex-falso
;; theorems then will follow from the ones for totality.

;; RTotalListToCoRTotal
;; NTotalListToCoNTotal
;; NTotalListNcToCoNTotalNc
;; TotalListToCoTotal
;; ANTotalListToCoANTotal
;; STotalListToCoSTotal
;; TotalListNcToCoTotalNc
;; STotalListNcToCoSTotalNc

;; RTotalListToCoRTotal
(set-goal "allnc xs^((RTotalList (cterm (x^) (Pvar alpha)x^))xs^ ->
 (CoRTotalList (cterm (x^) (Pvar alpha)x^))xs^)")
(assume "xs^" "Txs")
(coind "Txs")
(assume "xs^1" "Txs1")
(assert "xs^1 eqd (Nil alpha) ori
         exr x^2,xs^2((Pvar alpha)x^2 andi
                      (RTotalList (cterm (x^) (Pvar alpha)x^))xs^2 andi
                      xs^1 eqd x^2::xs^2)")
 (elim "Txs1")
 (intro 0)
 (use "InitEqD")
 (assume "x^2" "Px2" "xs^2" "Txs2" "Useless")
 (intro 1)
 (intro 0 (pt "x^2"))
 (intro 0 (pt "xs^2"))
 (split)
 (use "Px2")
 (split)
 (use "Txs2")
 (use "InitEqD")
;; Assertion proved.
(assume "Disj")
(elim "Disj")
(assume "xs1=Nil")
(intro 0)
(use "xs1=Nil")
(assume "ExHyp")
(intro 1)
(by-assume "ExHyp" "x^2" "x2Prop")
(by-assume "x2Prop" "xs^2" "x2xs2Prop")
(intro 0 (pt "x^2"))
(intro 0 (pt "xs^2"))
(use "x2xs2Prop")
(intro 0 (pt "xs^2"))
(split)
(intro 1)
(use "x2xs2Prop")
(use "x2xs2Prop")
;; Proof finished.
;; (cdp)
(save "RTotalListToCoRTotal")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [(list gamma)]
;;  (CoRec list gamma=>list gamma)(list gamma)
;;  ([(list gamma)_0]
;;    [if (list gamma)_0
;;      (DummyL gamma yprod(list gamma ysum list gamma))
;;      ([gamma,(list gamma)_1]
;;       Inr(clft(gamma pair(list gamma)_1)pair
;;           (InR (list gamma) (list gamma))crht(gamma pair(list gamma)_1)))])

;; NTotalListToCoNTotal
(set-goal "allnc xs^((NTotalList (cterm (x^) (Pvar alpha)^ x^))xs^ ->
 (CoNTotalList (cterm (x^) (Pvar alpha)^ x^))xs^)")
(assume "xs^" "Txs")
(coind "Txs")
(assume "xs^1" "Txs1")
(assert "xs^1 eqd (Nil alpha) ori
         exr x^2,xs^2((Pvar alpha)^ x^2 andi
                      (NTotalList (cterm (x^) (Pvar alpha)^ x^))xs^2 andi
                      xs^1 eqd x^2::xs^2)")
 (elim "Txs1")
 (intro 0)
 (use "InitEqD")
 (assume "x^2" "Px2" "xs^2" "Txs2" "Useless")
 (intro 1)
 (intro 0 (pt "x^2"))
 (intro 0 (pt "xs^2"))
 (split)
 (use "Px2")
 (split)
 (use "Txs2")
 (use "InitEqD")
;; Assertion proved.
(assume "Disj")
(elim "Disj")
;; 19,20
(assume "xs1=Nil")
(intro 0)
(use "xs1=Nil")
;; 20
(assume "ExHyp")
(intro 1)
(by-assume "ExHyp" "x^2" "x2Prop")
(by-assume "x2Prop" "xs^2" "x2xs2Prop")
(intro 0 (pt "x^2"))
(intro 0 (pt "xs^2"))
(use "x2xs2Prop")
(intro 0 (pt "xs^2"))
(split)
(intro 1)
(use "x2xs2Prop")
(use "x2xs2Prop")
;; Proof finished.
;; (cdp)
(save "NTotalListToCoNTotal")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n]
;;  (CoRec nat=>nat)n
;;  ([n0][if n0 (DummyL nat ysum nat) ([n1]Inr((InR nat nat)n1))])

;; NTotalListNcToCoNTotalNc
(set-goal "allnc xs^((NTotalListNc (cterm (x^) (Pvar alpha)^ x^))xs^ ->
 (CoNTotalListNc (cterm (x^) (Pvar alpha)^ x^))xs^)")
(assume "xs^" "Txs")
(coind "Txs")
(assume "xs^1" "Txs1")
(assert "xs^1 eqd (Nil alpha) ornc
         exr x^2,xs^2((Pvar alpha)^ x^2 andi
                      (NTotalListNc (cterm (x^) (Pvar alpha)^ x^))xs^2 andi
                      xs^1 eqd x^2::xs^2)")
 (elim "Txs1")
 (intro 0)
 (use "InitEqD")
 (assume "x^2" "Px2" "xs^2" "Txs2" "Useless")
 (intro 1)
 (intro 0 (pt "x^2"))
 (intro 0 (pt "xs^2"))
 (split)
 (use "Px2")
 (split)
 (use "Txs2")
 (use "InitEqD")
;; Assertion proved.
(assume "Disj")
(elim "Disj")
;; 19,20
(assume "xs1=Nil")
(intro 0)
(use "xs1=Nil")
;; 20
(assume "ExHyp")
(intro 1)
(by-assume "ExHyp" "x^2" "x2Prop")
(by-assume "x2Prop" "xs^2" "x2xs2Prop")
(intro 0 (pt "x^2"))
(intro 0 (pt "xs^2"))
(use "x2xs2Prop")
(intro 0 (pt "xs^2"))
(split)
(intro 1)
(use "x2xs2Prop")
(use "x2xs2Prop")
;; Proof finished.
;; (cdp)
(save "NTotalListNcToCoNTotalNc")

;; TotalListToCoTotal
(set-goal "allnc xs^(TotalList xs^ -> CoTotalList xs^)")
(assume "xs^" "Txs")
(coind "Txs")
(assume "xs^1" "Txs1")
(assert "xs^1 eqd (Nil alpha) ori
         exr x^2,xs^2(Total x^2 andi TotalList xs^2 andi xs^1 eqd x^2::xs^2)")
 (elim "Txs1")
 (intro 0)
 (use "InitEqD")
 (assume "x^2" "Tx2" "xs^2" "Txs2" "Useless")
 (intro 1)
 (intro 0 (pt "x^2"))
 (intro 0 (pt "xs^2"))
 (split)
 (use "Tx2")
 (split)
 (use "Txs2")
 (use "InitEqD")
;; Assertion proved.
(assume "Disj")
(elim "Disj")
(assume "xs1=Nil")
(intro 0)
(use "xs1=Nil")
(assume "ExHyp")
(intro 1)
(by-assume "ExHyp" "x^2" "x2Prop")
(by-assume "x2Prop" "xs^2" "x2xs2Prop")
(intro 0 (pt "x^2"))
(split)
(use "x2xs2Prop")
(intro 0 (pt "xs^2"))
(split)
(intro 1)
(use "x2xs2Prop")
(use "x2xs2Prop")
;; Proof finished.
;; (cdp)
(save "TotalListToCoTotal")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [xs]
;;  (CoRec list alpha=>list alpha)xs
;;  ([xs0]
;;    [if xs0
;;      (DummyL alpha yprod(list alpha ysum list alpha))
;;      ([x,xs1]
;;       Inr(clft(x pair xs1)pair
;;           (InR (list alpha) (list alpha))crht(x pair xs1)))])

;; ANTotalListToCoANTotal
(set-goal "allnc xs^(ANTotalList xs^ -> CoANTotalList xs^)")
(assume "xs^" "Txs")
(coind "Txs")
(assume "xs^1" "Txs1")
(assert "xs^1 eqd (Nil alpha) ori
         exr x^2,xs^2(TotalNc x^2 andi ANTotalList xs^2 andi
                      xs^1 eqd x^2::xs^2)")
 (elim "Txs1")
 (intro 0)
 (use "InitEqD")
 (assume "x^2" "Tx2" "xs^2" "Txs2" "Useless")
 (intro 1)
 (intro 0 (pt "x^2"))
 (intro 0 (pt "xs^2"))
 (split)
 (use "Tx2")
 (split)
 (use "Txs2")
 (use "InitEqD")
;; Assertion proved.
(assume "Disj")
(elim "Disj")
(assume "xs1=Nil")
(intro 0)
(use "xs1=Nil")
(assume "ExHyp")
(intro 1)
(by-assume "ExHyp" "x^2" "x2Prop")
(by-assume "x2Prop" "xs^2" "x2xs2Prop")
(intro 0 (pt "x^2"))
(split)
(use "x2xs2Prop")
(intro 0 (pt "xs^2"))
(split)
(intro 1)
(use "x2xs2Prop")
(use "x2xs2Prop")
;; Proof finished.
;; (cdp)
(save "ANTotalListToCoANTotal")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n]
;;  (CoRec nat=>nat)n
;;  ([n0][if n0 (DummyL nat ysum nat) ([n1]Inr((InR nat nat)n1))])

;; STotalListToCoSTotal
(set-goal "allnc xs^(STotalList xs^ -> CoSTotalList xs^)")
(assume "xs^" "Txs")
(coind "Txs")
(assume "xs^1" "Txs1")
(assert "xs^1 eqd (Nil alpha) ori
         exr x^2,xs^2(STotalList xs^2 andi xs^1 eqd x^2::xs^2)")
 (elim "Txs1")
 (intro 0)
 (use "InitEqD")
 (assume "x^2" "xs^2" "Txs2" "Useless")
 (intro 1)
 (intro 0 (pt "x^2"))
 (intro 0 (pt "xs^2"))
 (split)
 (use "Txs2")
 (use "InitEqD")
;; Assertion proved.
(assume "Disj")
(elim "Disj")
;; 17,18
(drop "Disj")
(assume "xs1=Nil")
(intro 0)
(use "xs1=Nil")
;; 18
(drop "Disj")
(assume "ExHyp")
(intro 1)
(by-assume "ExHyp" "x^2" "x2Prop")
(by-assume "x2Prop" "xs^2" "x2xs2Prop")
(intro 0 (pt "x^2"))
(intro 0 (pt "xs^2"))
(split)
(intro 1)
(use "x2xs2Prop")
(use "x2xs2Prop")
;; Proof finished.
;; (cdp)
(save "STotalListToCoSTotal")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n]
;;  (CoRec nat=>nat)n
;;  ([n0][if n0 (DummyL nat ysum nat) ([n1]Inr((InR nat nat)n1))])

;; TotalListNcToCoTotalNc
(set-goal "allnc xs^(TotalListNc xs^ -> CoTotalListNc xs^)")
(assume "xs^" "Txs")
(coind "Txs")
(assume "xs^1" "Txs1")
(assert "xs^1 eqd (Nil alpha) ornc
       exr x^2,xs^2(TotalNc x^2 andi TotalListNc xs^2 andi xs^1 eqd x^2::xs^2)")
 (elim "Txs1")
 (intro 0)
 (use "InitEqD")
 (assume "x^2" "Tx2" "xs^2" "Txs2" "Useless")
 (intro 1)
 (intro 0 (pt "x^2"))
 (intro 0 (pt "xs^2"))
 (split)
 (use "Tx2")
 (split)
 (use "Txs2")
 (use "InitEqD")
;; Assertion proved.
(assume "Disj")
(elim "Disj")
(assume "xs1=Nil")
(intro 0)
(use "xs1=Nil")
(assume "ExHyp")
(intro 1)
(by-assume "ExHyp" "x^2" "x2Prop")
(by-assume "x2Prop" "xs^2" "x2xs2Prop")
(intro 0 (pt "x^2"))
(split)
(use "x2xs2Prop")
(intro 0 (pt "xs^2"))
(split)
(intro 1)
(use "x2xs2Prop")
(use "x2xs2Prop")
;; Proof finished.
;; (cdp)
(save "TotalListNcToCoTotalNc")

;; STotalListNcToCoSTotalNc
(set-goal "allnc xs^(STotalListNc xs^ -> CoSTotalListNc xs^)")
(assume "xs^" "Txs")
(coind "Txs")
(assume "xs^1" "Txs1")
(assert "xs^1 eqd (Nil alpha) ornc
         exnc x^2,xs^2(STotalListNc xs^2 andi xs^1 eqd x^2::xs^2)")
 (elim "Txs1")
 (intro 0)
 (use "InitEqD")
 (assume "x^2" "xs^2" "Txs2" "Useless")
 (intro 1)
 (intro 0 (pt "x^2"))
 (intro 0 (pt "xs^2"))
 (split)
 (use "Txs2")
 (use "InitEqD")
;; Assertion proved.
(assume "Disj")
(elim "Disj")
;; 17,18
(drop "Disj")
(assume "xs1=Nil")
(intro 0)
(use "xs1=Nil")
;; 18
(drop "Disj")
(assume "ExHyp")
(intro 1)
(by-assume "ExHyp" "x^2" "x2Prop")
(by-assume "x2Prop" "xs^2" "x2xs2Prop")
(intro 0 (pt "x^2"))
(intro 0 (pt "xs^2"))
(split)
(intro 1)
(use "x2xs2Prop")
(use "x2xs2Prop")
;; Proof finished.
;; (cdp)
(save "STotalListNcToCoSTotalNc")
 
;; 1-1-2-2-3.  Ex falso
;; ====================

;; For each dual of the 8 idpcs in 1-2-1-1 we have an ex-falso property

;; EfCoRTotalList
;; EfCoNTotalList
;; EfCoNTotalListNc
;; EfCoTotalList
;; EfCoANTotalList
;; EfCoSTotalList
;; EfCoTotalListNc
;; EfCoSTotalListNc

;; EfCoRTotalList
(set-goal "allnc xs^(F -> (CoRTotalList (cterm (x^) (Pvar alpha)x^))xs^)")
(assume "xs^" "Absurd")
(use "RTotalListToCoRTotal")
(use "EfRTotalList")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfCoRTotalList")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; (cRTotalListToCoRTotal gamma)(cEfRTotalList gamma)

(animate "RTotalListToCoRTotal")
(animate "EfRTotalList")

(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; (CoRec list gamma=>list gamma)(Nil gamma)
;; ([(list gamma)]
;;   [if (list gamma)
;;     (DummyL gamma yprod(list gamma ysum list gamma))
;;     ([gamma,(list gamma)_0]
;;      Inr(clft(gamma pair(list gamma)_0)pair
;;          (InR (list gamma) (list gamma))crht(gamma pair(list gamma)_0)))])

(pp (nt (undelay-delayed-corec neterm 1)))
;; (Nil gamma)

(deanimate "RTotalListToCoRTotal")
(deanimate "EfRTotalList")

;; EfCoNTotalList
(set-goal "allnc xs^(F -> (CoNTotalList (cterm (x^) (Pvar alpha)^ x^))xs^)")
(assume "xs^" "Absurd")
(use "NTotalListToCoNTotal")
(use "EfNTotalList")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfCoNTotalList")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; cNTotalListToCoNTotal cEfNTotalList

(animate "NTotalListToCoNTotal")
(animate "EfNTotalList")

(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; (CoRec nat=>nat)0([n][if n (DummyL nat ysum nat) ([n0]Inr((InR nat nat)n0))])

(pp (nt (undelay-delayed-corec neterm 1)))
;; 0

(deanimate "NTotalListToCoNTotal")
(deanimate "EfNTotalList")

;; EfCoNTotalListNc
(set-goal "allnc xs^(F -> (CoNTotalListNc (cterm (x^) (Pvar alpha)^ x^))xs^)")
(assume "xs^" "Absurd")
(use "NTotalListNcToCoNTotalNc")
(use "EfNTotalListNc")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfCoNTotalListNc")

;; EfCoTotalList
(set-goal "allnc xs^(F -> CoTotalList xs^)")
(assume "xs^" "Absurd")
(use "TotalListToCoTotal")
(use "EfTotalList")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfCoTotalList")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; (cTotalListToCoTotal alpha)(cEfTotalList alpha)

(animate "TotalListToCoTotal")
(animate "EfTotalList")

(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; (CoRec list alpha=>list alpha)(Nil alpha)
;; ([xs]
;;   [if xs
;;     (DummyL alpha yprod(list alpha ysum list alpha))
;;     ([x,xs0]
;;      Inr(clft(x pair xs0)pair(InR (list alpha) (list alpha))crht(x pair xs0)))])

(pp (nt (undelay-delayed-corec neterm 1)))
;; (Nil alpha)

(deanimate "TotalListToCoTotal")
(deanimate "EfTotalList")

;; EfCoANTotalList
(set-goal "allnc xs^(F -> CoANTotalList xs^)")
(assume "xs^" "Absurd")
(use "ANTotalListToCoANTotal")
(use "EfANTotalList")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfCoANTotalList")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; cANTotalListToCoANTotal cEfANTotalList

(animate "ANTotalListToCoANTotal")
(animate "EfANTotalList")

(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; (CoRec nat=>nat)0([n][if n (DummyL nat ysum nat) ([n0]Inr((InR nat nat)n0))])

(pp (nt (undelay-delayed-corec neterm 1)))
;; 0

(deanimate "ANTotalListToCoANTotal")
(deanimate "EfANTotalList")

;; EfCoSTotalList
(set-goal "allnc xs^(F -> CoSTotalList xs^)")
(assume "xs^" "Absurd")
(use "STotalListToCoSTotal")
(use "EfSTotalList")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfCoSTotalList")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; cSTotalListToCoSTotal cEfSTotalList

(animate "STotalListToCoSTotal")
(animate "EfSTotalList")

(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; (CoRec nat=>nat)0([n][if n (DummyL nat ysum nat) ([n0]Inr((InR nat nat)n0))])

(pp (nt (undelay-delayed-corec neterm 1)))
;; 0

(deanimate "STotalListToCoSTotal")
(deanimate "EfSTotalList")

;; EfCoTotalListNc
(set-goal "allnc xs^(F -> CoTotalListNc xs^)")
(assume "xs^" "Absurd")
(use "TotalListNcToCoTotalNc")
(use "EfTotalListNc")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfCoTotalListNc")

;; EfCoSTotalListNc
(set-goal "allnc xs^(F -> CoSTotalListNc xs^)")
(assume "xs^" "Absurd")
(use "STotalListNcToCoSTotalNc")
(use "EfSTotalListNc")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfCoSTotalListNc")

;; 1-2.  TotalMR and CoTotalMR
;; ===========================

;; 1-2-1.  TotalMR
;; ===============

;; 1-2-1-2.  Properties
;; ====================

;; 1-2-1-2-1.  Ex falso
;; ====================

;; EfRTotalListMR
;; EfNTotalListMR
;; EfTotalListMR
;; EfANTotalListMR
;; EfSTotalListMR

;; EfRTotalListMR
(set-goal "allnc xs^,(list gamma)^(F -> 
 (RTotalListMR (cterm (x^0,gamma^1) (Pvar alpha gamma)^ x^0 gamma^1))
 xs^ (list gamma)^)")
(assume "xs^" "(list gamma)^" "Absurd")
(simp (pf "xs^ eqd (Nil alpha)"))
(simp (pf "(list gamma)^ eqd (Nil gamma)"))
(use "RTotalListNilMR")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfRTotalListMR")

;; EfNTotalListMR
(set-goal
 "allnc xs^,n^(F -> (NTotalListMR (cterm (x^) (Pvar alpha)^ x^))xs^ n^)")
(assume "xs^" "n^" "Absurd")
(simp (pf "xs^ eqd (Nil alpha)"))
(simp (pf "n^ eqd 0"))
(use "NTotalListNilMR")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfNTotalListMR")

;; EfTotalListMR
(set-goal "allnc xs^1,xs^2(F -> TotalListMR xs^1 xs^2)")
(assume "xs^1" "xs^2" "Absurd")
(simp (pf "xs^1 eqd (Nil alpha)"))
(simp (pf "xs^2 eqd (Nil alpha)"))
(use "TotalListNilMR")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfTotalListMR")

;; EfANTotalListMR
(set-goal "allnc xs^,n^(F -> ANTotalListMR xs^ n^)")
(assume "xs^" "n^" "Absurd")
(simp (pf "xs^ eqd (Nil alpha)"))
(simp (pf "n^ eqd 0"))
(use "ANTotalListNilMR")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfANTotalListMR")

;; EfSTotalListMR
(set-goal "allnc xs^,n^(F -> STotalListMR xs^ n^)")
(assume "xs^" "n^" "Absurd")
(simp (pf "xs^ eqd (Nil alpha)"))
(simp (pf "n^ eqd 0"))
(use "STotalListNilMR")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfSTotalListMR")

;; 1-2-1-2-2.  Monotonicity
;; ========================

;; ListRTotalMonMR
;; ListNTotalMonMR

;; ListRTotalMonMR
(set-goal "allnc x^,gamma^(
     (Pvar alpha gamma)^1 x^ gamma^ -> (Pvar alpha gamma)^2 x^ gamma^) -> 
    allnc xs^,(list gamma)^(
     (RTotalListMR (cterm (x^,gamma^) (Pvar alpha gamma)^1 x^ gamma^))xs^
     (list gamma)^ -> 
     (RTotalListMR (cterm (x^,gamma^) (Pvar alpha gamma)^2 x^ gamma^))xs^
     (list gamma)^)")
(assume "MonHyp" "xs^" "(list gamma)^")
(elim)
(intro 0)
(assume "x^" "gamma^" "PHyp" "xs^1" "(list gamma)^1" "Useless" "RTZHyp")
(intro 1)
(use "MonHyp")
(use "PHyp")
(use "RTZHyp")
;; Proof finished.
;; (cdp)
(save "ListRTotalMonMR")

;; ListNTotalMonMR
(set-goal "allnc x^((Pvar alpha)^1 x^ -> (Pvar alpha)^2 x^) -> 
    allnc xs^,n^(
     (NTotalListMR (cterm (x^) (Pvar alpha)^1 x^))xs^ n^ -> 
     (NTotalListMR (cterm (x^) (Pvar alpha)^2 x^))xs^ n^)")
(assume "MonHyp" "xs^" "n^")
(elim)
(intro 0)
(assume "x^" "PHyp" "xs^1" "n^1" "Useless" "Hyp")
(intro 1)
(use "MonHyp")
(use "PHyp")
(use "Hyp")
;; Proof finished.
;; (cdp)
(save "ListNTotalMonMR")

;; 1-2-1-2-3.  Connections
;; =======================

;; TotalListMRToEqD
(set-goal "allnc x^1,x^2(TotalMR x^1 x^2 -> x^1 eqd x^2) ->
 allnc xs^1,xs^2(TotalListMR xs^1 xs^2 -> xs^1 eqd xs^2)")
(assume "EqDx1x2" "xs^1" "xs^2" "TMRxs1xs2")
(elim "TMRxs1xs2")
(use "InitEqD")
(assume "x^3" "x^4" "TMRx3x4" "xs^3" "xs^4" "Useless" "EqDxs3xs4")
(simp "EqDxs3xs4")
(simp "EqDx1x2" (pt "x^4"))
(use "InitEqD")
(use "TMRx3x4")
;; Proof finished.
;; (cdp)
(save "TotalListMRToEqD")

;; 1-2-2.  CoTotalMR
;; =================

;; 1-2-2-2.  Properties
;; ====================

;; 1-2-2-2-1.  Ex falso
;; ====================

;; EfCoRTotalListMR
;; EfCoNTotalListMR
;; EfCoTotalListMR
;; EfCoANTotalListMR
;; EfCoSTotalListMR

;; EfCoRTotalListMR
(set-goal "allnc xs^,(list gamma)^(
     F -> 
     (CoRTotalListMR (cterm (x^,gamma^0) (Pvar alpha gamma)^ x^ gamma^0))xs^
     (list gamma)^)")
(assume "xs^" "(list gamma)^" "Absurd")
(coind "Absurd")
(assume "xs^1" "(list gamma)^1" "Useless")
(intro 0)
(simp (pf "xs^1 eqd (Nil alpha)"))
(simp (pf "(list gamma)^1 eqd (Nil gamma)"))
(split)
(use "InitEqD")
(use "InitEqD")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfCoRTotalListMR")

;; EfCoNTotalListMR
(set-goal
 "allnc xs^,n^(F -> (CoNTotalListMR (cterm (x^) (Pvar alpha)^ x^))xs^ n^)")
(assume "xs^" "n^" "Absurd")
(coind "Absurd")
(assume "xs^1" "n^1" "Useless")
(intro 0)
(simp (pf "xs^1 eqd (Nil alpha)"))
(simp (pf "n^1 eqd 0"))
(split)
(use "InitEqD")
(use "InitEqD")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfCoNTotalListMR")

(display-idpc "CoTotalListMR")

;; EfCoTotalListMR
(set-goal "allnc xs^1,xs^2(F -> CoTotalListMR xs^1 xs^2)")
(assume "xs^1" "xs^2" "Absurd")
(coind "Absurd")
(assume "xs^3" "xs^4" "Useless")
(intro 0)
(simp (pf "xs^3 eqd (Nil alpha)"))
(simp (pf "xs^4 eqd (Nil alpha)"))
(split)
(use "InitEqD")
(use "InitEqD")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfCoTotalListMR")

;; EfCoANTotalListMR
(set-goal "allnc xs^,n^(F -> CoANTotalListMR xs^ n^)")
(assume "xs^" "n^" "Absurd")
(coind "Absurd")
(assume "xs^1" "n^1" "Useless")
(intro 0)
(simp (pf "xs^1 eqd (Nil alpha)"))
(simp (pf "n^1 eqd 0"))
(split)
(use "InitEqD")
(use "InitEqD")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfCoANTotalListMR")

;; EfCoSTotalListMR
(set-goal "allnc xs^,n^(F -> CoSTotalListMR xs^ n^)")
(assume "xs^" "n^" "Absurd")
(coind "Absurd")
(assume "xs^1" "n^1" "Useless")
(intro 0)
(simp (pf "xs^1 eqd (Nil alpha)"))
(simp (pf "n^1 eqd 0"))
(split)
(use "InitEqD")
(use "InitEqD")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfCoSTotalListMR")

;; 1-2-2-2-2.  Monotonicity
;; ========================

;; ListCoRTotalMonMR
;; ListCoNTotalMonMR

;; ListCoRTotalMonMR
(set-goal "allnc x^,gamma^(
     (Pvar alpha gamma)^1 x^ gamma^ -> (Pvar alpha gamma)^2 x^ gamma^) -> 
    allnc xs^,(list gamma)^(
     (CoRTotalListMR (cterm (x^,gamma^) (Pvar alpha gamma)^1 x^ gamma^))xs^
     (list gamma)^ -> 
     (CoRTotalListMR (cterm (x^,gamma^) (Pvar alpha gamma)^2 x^ gamma^))xs^
     (list gamma)^)")
(assume "MonHyp" "xs^" "(list gamma)^" "CoRHyp1")
(coind "CoRHyp1")
(assume "xs^1" "(list gamma)^1" "CoRHyp2")
(inst-with-to
 "CoRTotalListMRClause"
 (make-cterm (pv "x^") (pv "gamma^") (pf "(Pvar alpha gamma)^1 x^ gamma^"))
 (pt "xs^1") (pt "(list gamma)^1") "CoRHyp2" "Inst")
(elim "Inst")
;; 7,8
(drop "Inst")
(assume "xs1=Nil")
(intro 0)
(use "xs1=Nil")
;; 8
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^2" "x2Prop")
(by-assume "x2Prop" "gamma^2" "x2y2Prop")
(inst-with-to "x2y2Prop" 'left "Px2")
(inst-with-to "x2y2Prop" 'right "ExHyp2")
(drop "x2y2Prop")
(by-assume "ExHyp2" "xs^2" "x2y2xs2Prop")
(by-assume "x2y2xs2Prop" "(list gamma)^2" "x2y2xs2ys2Prop")
(intro 1)
(intro 0 (pt "x^2"))
(intro 0 (pt "gamma^2"))
(split)
(use "MonHyp")
(use "Px2")
(intro 0 (pt "xs^2"))
(intro 0 (pt "(list gamma)^2"))
(split)
(intro 1)
(use "x2y2xs2ys2Prop")
(use "x2y2xs2ys2Prop")
;; Proof finished.
;; (cdp)
(save "ListCoRTotalMonMR")

;; ListCoNTotalMonMR
(display-idpc "CoNTotalListMR")

(set-goal "allnc x^((Pvar alpha)^1 x^ -> (Pvar alpha)^2 x^) -> 
    allnc xs^,n^(
     (CoNTotalListMR (cterm (x^) (Pvar alpha)^1 x^))xs^ n^ -> 
     (CoNTotalListMR (cterm (x^) (Pvar alpha)^2 x^))xs^ n^)")
(assume "MonHyp" "xs^" "n^" "CoNHyp1")
(coind "CoNHyp1")
(assume "xs^1" "n^1" "CoNHyp2")
(inst-with-to
 "CoNTotalListMRClause"
 (make-cterm (pv "x^") (pf "(Pvar alpha)^1 x^"))
 (pt "xs^1") (pt "n^1") "CoNHyp2" "Inst")
(elim "Inst")
;; 7,8
(drop "Inst")
(assume "xs1=Nil")
(intro 0)
(use "xs1=Nil")
;; 8
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^2" "x2Prop")
(inst-with-to "x2Prop" 'left "Px2")
(inst-with-to "x2Prop" 'right "ExHyp2")
(drop "x2Prop")
(by-assume "ExHyp2" "xs^2" "x2xs2Prop")
(by-assume "x2xs2Prop" "n^2" "x2xs2n2Prop")
(intro 1)
(intro 0 (pt "x^2"))
(split)
(use "MonHyp")
(use "Px2")
(intro 0 (pt "xs^2"))
(intro 0 (pt "n^2"))
(split)
(intro 1)
(use "x2xs2n2Prop")
(use "x2xs2n2Prop")
;; Proof finished.
;; (cdp)
(save "ListCoNTotalMonMR")

;; 1-2-2-2-3.  Total implies CoTotal
;; =================================

;; RTotalListMRToCoRTotalMR
;; NTotalListMRToCoNTotalMR
;; TotalListMRToCoTotalMR
;; ANTotalListMRToCoANTotalMR
;; STotalListMRToCoSTotalMR

;; RTotalListMRToCoRTotalMR
(set-goal "allnc xs^,(list gamma)^(
     (RTotalListMR (cterm (x^,gamma^) (Pvar alpha gamma)^ x^ gamma^))xs^
     (list gamma)^ -> 
     (CoRTotalListMR (cterm (x^,gamma^) (Pvar alpha gamma)^ x^ gamma^))xs^
     (list gamma)^)")
(assume "xs^" "(list gamma)^" "Txsys")
(coind "Txsys")
(assume "xs^1" "(list gamma)^1" "Txs1ys1")
(assert "xs^1 eqd (Nil alpha) andnc (list gamma)^1 eqd(Nil gamma) ornc
         exr x^2,gamma^2,xs^2,(list gamma)^2(
 (Pvar alpha gamma)^ x^2 gamma^2 andnc
 (RTotalListMR (cterm (x^,gamma^) (Pvar alpha gamma)^ x^ gamma^))
       xs^2 (list gamma)^2 andnc
        xs^1 eqd x^2::xs^2 andnc
        (list gamma)^1 eqd gamma^2::(list gamma)^2)")
 (elim "Txs1ys1")
 (intro 0)
 (split)
 (use "InitEqD")
 (use "InitEqD")
;; 8
 (assume "x^2" "gamma^2" "Px2y2" "xs^2" "(list gamma)^2" "Txs2ys2" "Useless")
 (drop "Useless")
 (intro 1)
 (intro 0 (pt "x^2"))
 (intro 0 (pt "gamma^2"))
 (intro 0 (pt "xs^2"))
 (intro 0 (pt "(list gamma)^2"))
 (split)
 (use "Px2y2")
 (split)
 (use "Txs2ys2")
 (split)
 (use "InitEqD")
 (use "InitEqD")
;; Assertion proved.
(assume "Disj")
(elim "Disj")
;; 26,27
(assume "NilConj")
(intro 0)
(use "NilConj")
;; 27
(drop "Disj")
(assume "ExHyp")
(intro 1)
(by-assume "ExHyp" "x^2" "x2Prop")
(by-assume "x2Prop" "gamma^2" "x2y2Prop")
(by-assume "x2y2Prop" "xs^2" "x2y2xs2Prop")
(by-assume "x2y2xs2Prop" "(list gamma)^2" "x2y2xs2ys2Prop")
(intro 0 (pt "x^2"))
(intro 0 (pt "gamma^2"))
(split)
(use "x2y2xs2ys2Prop")
(intro 0 (pt "xs^2"))
(intro 0 (pt "(list gamma)^2"))
(split)
(intro 1)
(use "x2y2xs2ys2Prop")
(use "x2y2xs2ys2Prop")
;; Proof finished.
;; (cdp)
(save "RTotalListMRToCoRTotalMR")

;; NTotalListMRToCoNTotalMR
(set-goal "allnc xs^,n^(
     (NTotalListMR (cterm (x^) (Pvar alpha)^ x^))xs^ n^ -> 
     (CoNTotalListMR (cterm (x^) (Pvar alpha)^ x^))xs^ n^)")
(assume "xs^" "n^" "Txsn")
(coind "Txsn")
(assume "xs^1" "n^1" "Txs1n1")
(assert "xs^1 eqd (Nil alpha) andnc n^1 eqd 0 ornc
         exr x^2,xs^2,n^2(
 (Pvar alpha)^ x^2 andnc
 (NTotalListMR (cterm (x^) (Pvar alpha)^ x^))xs^2 n^2 andnc
        xs^1 eqd x^2::xs^2 andnc n^1 eqd Succ n^2)")
 (elim "Txs1n1")
 ;; 7,8
 (intro 0)
 (split)
 (use "InitEqD")
 (use "InitEqD")
;; 8
 (assume "x^2" "Px2" "xs^2" "n^2" "Txs2n2" "Useless")
 (drop "Useless")
 (intro 1)
 (intro 0 (pt "x^2"))
 (intro 0 (pt "xs^2"))
 (intro 0 (pt "n^2"))
 (split)
 (use "Px2")
 (split)
 (use "Txs2n2")
 (split)
 (use "InitEqD")
 (use "InitEqD")
;; Assertion proved.
(assume "Disj")
(elim "Disj")
;; 25,26
(assume "NilConj")
(intro 0)
(use "NilConj")
;; 26
(drop "Disj")
(assume "ExHyp")
(intro 1)
(by-assume "ExHyp" "x^2" "x2Prop")
(by-assume "x2Prop" "xs^2" "x2xs2Prop")
(by-assume "x2xs2Prop" "n^2" "x2xs2n2Prop")
(intro 0 (pt "x^2"))
(split)
(use "x2xs2n2Prop")
(intro 0 (pt "xs^2"))
(intro 0 (pt "n^2"))
(split)
(intro 1)
(use "x2xs2n2Prop")
(use "x2xs2n2Prop")
;; Proof finished.
;; (cdp)
(save "NTotalListMRToCoNTotalMR")

;; TotalListMRToCoTotalMR
(set-goal "allnc xs^1,xs^2(TotalListMR xs^1 xs^2 -> CoTotalListMR xs^1 xs^2)")
(assume "xs^1" "xs^2" "Txs1xs2")
(coind "Txs1xs2")
(assume "xs^3" "xs^4" "Txs3xs4")
(assert "xs^3 eqd (Nil alpha) andnc xs^4 eqd(Nil alpha) ornc
         exr x^5,x^6,xs^5,xs^6(TotalMR x^5 x^6 andnc
         TotalListMR xs^5 xs^6 andnc 
        xs^3 eqd x^5::xs^5 andnc
        xs^4 eqd x^6::xs^6)")
 (elim "Txs3xs4")
;; 7,8
 (intro 0)
 (split)
 (use "InitEqD")
 (use "InitEqD")
;; 8
 (assume "x^5" "x^6" "Tx5x6" "xs^5" "xs^6" "Txs5xs6" "Useless")
 (drop "Useless")
 (intro 1)
 (intro 0 (pt "x^5"))
 (intro 0 (pt "x^6"))
 (intro 0 (pt "xs^5"))
 (intro 0 (pt "xs^6"))
 (split)
 (use "Tx5x6")
 (split)
 (use "Txs5xs6")
 (split)
 (use "InitEqD")
 (use "InitEqD")
;; Assertion proved.
(assume "Disj")
(elim "Disj")
;; 26,27
(assume "NilConj")
(intro 0)
(use "NilConj")
;; 27
(drop "Disj")
(assume "ExHyp")
(intro 1)
(by-assume "ExHyp" "x^5" "x5Prop")
(by-assume "x5Prop" "x^6" "x5x6Prop")
(by-assume "x5x6Prop" "xs^5" "x5x6xs5Prop")
(by-assume "x5x6xs5Prop" "xs^6" "x5x6xs5xs6Prop")
(intro 0 (pt "x^5"))
(intro 0 (pt "x^6"))
(split)
(use "x5x6xs5xs6Prop")
(intro 0 (pt "xs^5"))
(intro 0 (pt "xs^6"))
(split)
(intro 1)
(use "x5x6xs5xs6Prop")
(use "x5x6xs5xs6Prop")
;; Proof finished.
;; (cdp)
(save "TotalListMRToCoTotalMR")

;; ANTotalListMRToCoANTotalMR
(set-goal "allnc xs^,n^(ANTotalListMR xs^ n^ -> CoANTotalListMR xs^ n^)")
(assume "xs^" "n^" "Txsn")
(coind "Txsn")
(assume "xs^1" "n^1" "Txs1n1")
(assert "xs^1 eqd (Nil alpha) andnc n^1 eqd 0 ornc
         exr x^2,xs^2,n^2(
  TotalNc x^2 andnc
  ANTotalListMR xs^2 n^2 andnc xs^1 eqd x^2::xs^2 andnc n^1 eqd Succ n^2)")
 (elim "Txs1n1")
 ;; 7,8
 (intro 0)
 (split)
 (use "InitEqD")
 (use "InitEqD")
;; 8
 (assume "x^2" "Px2" "xs^2" "n^2" "Txs2n2" "Useless")
 (drop "Useless")
 (intro 1)
 (intro 0 (pt "x^2"))
 (intro 0 (pt "xs^2"))
 (intro 0 (pt "n^2"))
 (split)
 (use "Px2")
 (split)
 (use "Txs2n2")
 (split)
 (use "InitEqD")
 (use "InitEqD")
;; Assertion proved.
(assume "Disj")
(elim "Disj")
;; 25,26
(assume "NilConj")
(intro 0)
(use "NilConj")
;; 26
(drop "Disj")
(assume "ExHyp")
(intro 1)
(by-assume "ExHyp" "x^2" "x2Prop")
(by-assume "x2Prop" "xs^2" "x2xs2Prop")
(by-assume "x2xs2Prop" "n^2" "x2xs2n2Prop")
(intro 0 (pt "x^2"))
(split)
(use "x2xs2n2Prop")
(intro 0 (pt "xs^2"))
(intro 0 (pt "n^2"))
(split)
(intro 1)
(use "x2xs2n2Prop")
(use "x2xs2n2Prop")
;; Proof finished.
;; (cdp)
(save "ANTotalListMRToCoANTotalMR")

;; STotalListMRToCoSTotalMR
(set-goal "allnc xs^,n^(STotalListMR xs^ n^ -> CoSTotalListMR xs^ n^)")
(assume "xs^" "n^" "Txsn")
(coind "Txsn")
(assume "xs^1" "n^1" "Txs1n1")
(assert "xs^1 eqd (Nil alpha) andnc n^1 eqd 0 ornc
         exr x^2,xs^2,n^2(
  STotalListMR xs^2 n^2 andnc xs^1 eqd x^2::xs^2 andnc n^1 eqd Succ n^2)")
 (elim "Txs1n1")
 ;; 7,8
 (intro 0)
 (split)
 (use "InitEqD")
 (use "InitEqD")
;; 8
 (assume "x^2" "xs^2" "n^2" "Txs2n2" "Useless")
 (drop "Useless")
 (intro 1)
 (intro 0 (pt "x^2"))
 (intro 0 (pt "xs^2"))
 (intro 0 (pt "n^2"))
 (split)
 (use "Txs2n2")
 (split)
 (use "InitEqD")
 (use "InitEqD")
;; Assertion proved.
(assume "Disj")
(elim "Disj")
;; 23,24
(assume "NilConj")
(intro 0)
(use "NilConj")
;; 24
(drop "Disj")
(assume "ExHyp")
(intro 1)
(by-assume "ExHyp" "x^2" "x2Prop")
(by-assume "x2Prop" "xs^2" "x2xs2Prop")
(by-assume "x2xs2Prop" "n^2" "x2xs2n2Prop")
(intro 0 (pt "x^2"))
(intro 0 (pt "xs^2"))
(intro 0 (pt "n^2"))
(split)
(intro 1)
(use "x2xs2n2Prop")
(use "x2xs2n2Prop")
;; Proof finished.
;; (cdp)
(save "STotalListMRToCoSTotalMR")

;; 2.  Pointwise equality
;; ======================

;; Pointwise equality EqPList is a binary version of TotalList.  It is
;; interesting because (i) CoEqPList is bisimilarity, and (ii) its
;; extension to higher types (in the style of Gandy 1956, i.e., as a
;; logical relation) allows to define extensionality as its diagonal.

;; 2-1.  EqP and CoEqP
;; ===================

;; 2-1-1.  EqP
;; ===========

;; 2-1-1-2.  Properties
;; ====================

;; 2-1-1-2-1.  Ex falso
;; ====================

;; For each of the 8 idpcs in 2-1-1-1 we have an ex-falso property

;; EfREqPList
;; EfNEqPList
;; EfNEqPListNc
;; EfEqPList
;; EfANEqPList
;; EfSEqPList
;; EfEqPListNc
;; EfSEqPListNc

;; EfREqPList
(set-goal "allnc xs^1,xs^2(F ->
            (REqPList (cterm (x^1,x^2) (Pvar alpha alpha) x^1 x^2))xs^1 xs^2)")
(assume "xs^1" "xs^2" "Absurd")
(simp (pf "xs^1 eqd (Nil alpha)"))
(simp (pf "xs^2 eqd (Nil alpha)"))
(use "REqPListNil")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfREqPList")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; (Nil alpha702)

;; EfNEqPList
(set-goal "allnc xs^1,xs^2(F ->
            (NEqPList (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xs^1 xs^2)")
(assume "xs^1" "xs^2" "Absurd")
(simp (pf "xs^1 eqd (Nil alpha)"))
(simp (pf "xs^2 eqd (Nil alpha)"))
(use "NEqPListNil")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfNEqPList")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; 0

;; EfNEqPListNc
(set-goal "allnc xs^1,xs^2(F ->
          (NEqPListNc (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xs^1 xs^2)")
(assume "xs^1" "xs^2" "Absurd")
(simp (pf "xs^1 eqd (Nil alpha)"))
(simp (pf "xs^2 eqd (Nil alpha)"))
(use "NEqPListNcNil")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfNEqPListNc")

;; EfEqPList
(set-goal "allnc xs^1,xs^2(F -> EqPList xs^1 xs^2)")
(assume "xs^1" "xs^2" "Absurd")
(simp (pf "xs^1 eqd (Nil alpha)"))
(simp (pf "xs^2 eqd (Nil alpha)"))
(use "EqPListNil")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfEqPList")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; (Nil alpha)

;; EfANEqPList
(set-goal "allnc xs^1,xs^2(F -> ANEqPList xs^1 xs^2)")
(assume "xs^1" "xs^2" "Absurd")
(simp (pf "xs^1 eqd (Nil alpha)"))
(simp (pf "xs^2 eqd (Nil alpha)"))
(use "ANEqPListNil")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfANEqPList")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; 0

;; EfSEqPList
(set-goal "allnc xs^1,xs^2(F -> SEqPList xs^1 xs^2)")
(assume "xs^1" "xs^2" "Absurd")
(simp (pf "xs^1 eqd (Nil alpha)"))
(simp (pf "xs^2 eqd (Nil alpha)"))
(use "SEqPListNil")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfSEqPList")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; 0

;; EfEqPListNc
(set-goal "allnc xs^1,xs^2(F -> EqPListNc xs^1 xs^2)")
(assume "xs^1" "xs^2" "Absurd")
(simp (pf "xs^1 eqd (Nil alpha)"))
(simp (pf "xs^2 eqd (Nil alpha)"))
(use "EqPListNcNil")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfEqPListNc")

;; EfSEqPListNc
(set-goal "allnc xs^1,xs^2(F -> SEqPListNc xs^1 xs^2)")
(assume "xs^1" "xs^2" "Absurd")
(simp (pf "xs^1 eqd (Nil alpha)"))
(simp (pf "xs^2 eqd (Nil alpha)"))
(use "SEqPListNcNil")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfSEqPListNc")

;; 2-1-1-2-2.  Monotonicity
;; ========================

;; ListREqPMon
(set-goal "allnc x^1,x^2(
     (Pvar alpha alpha)_1 x^1 x^2 -> (Pvar alpha alpha)_2 x^1 x^2) -> 
    allnc xs^1,xs^2(
     (REqPList (cterm (x^1,x^2) (Pvar alpha alpha)_1 x^1 x^2))xs^1 xs^2 -> 
     (REqPList (cterm (x^1,x^2) (Pvar alpha alpha)_2 x^1 x^2))xs^1 xs^2)")
(assume "MonHyp" "xs^1" "xs^2")
(elim)
(intro 0)
(assume "x^3" "x^4" "Yx1x2" "xs^3" "xs^4" "Useless" "RTZxs3xs4")
(intro 1)
(use "MonHyp")
(use "Yx1x2")
(use "RTZxs3xs4")
;; Proof finished.
;; (cdp)
(save "ListREqPMon")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [(alpha749=>alpha751),(list alpha749)]
;;  (Rec list alpha749=>list alpha751)(list alpha749)(Nil alpha751)
;;  ([alpha749,(list alpha749)_0](Cons alpha751)((alpha749=>alpha751)alpha749))

;; ListNEqPMon
(set-goal "allnc x^1,x^2(
     (Pvar alpha alpha)^1 x^1 x^2 -> (Pvar alpha alpha)^2 x^1 x^2) -> 
    allnc xs^1,xs^2(
     (NEqPList (cterm (x^1,x^2) (Pvar alpha alpha)^1 x^1 x^2))xs^1 xs^2 -> 
     (NEqPList (cterm (x^1,x^2) (Pvar alpha alpha)^2 x^1 x^2))xs^1 xs^2)")
(assume "MonHyp" "xs^1" "xs^2")
(elim)
(intro 0)
(assume "x^3" "x^4" "Yx1x2" "xs^3" "xs^4" "Useless" "RTZxs3xs4")
(intro 1)
(use "MonHyp")
(use "Yx1x2")
(use "RTZxs3xs4")
;; Proof finished.
;; (cdp)
(save "ListNEqPMon")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n](Rec nat=>nat)n 0([n0]Succ)

;; 2-1-1-2-3.  EqP implies EqD
;; ===========================

;; NEqPListNcToEqD
(set-goal "allnc x^1,x^2((Pvar alpha alpha)^ x^1 x^2 -> x^1 eqd x^2) -> 
    allnc xs^1,xs^2(
     (NEqPListNc (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xs^1 xs^2 -> 
     xs^1 eqd xs^2)")
(assume "EqDHyp" "xs^1" "xs^2" "NEqPxs1xs2")
(elim "NEqPxs1xs2")
(use "InitEqD")
(assume "x^3" "x^4" "Px3x4" "xs^3" "xs^4" "NEqPxs3xs4" "EqDxs3xs4")
(simp "EqDxs3xs4")
(simp "EqDHyp" (pt "x^4"))
(use "InitEqD")
(use "Px3x4")
;; Proof finished.
;; (cdp)
(save "NEqPListNcToEqD")

;; EqPListNcToEqD
(set-goal "allnc x^1,x^2(EqPNc x^1 x^2 -> x^1 eqd x^2) ->
 allnc xs^1,xs^2(EqPListNc xs^1 xs^2 -> xs^1 eqd xs^2)")
(assume "EqDHyp" "xs^1" "xs^2" "EqPxs1xs2")
(elim "EqPxs1xs2")
(use "InitEqD")
(assume "x^3" "x^4" "EqPx3x4" "xs^3" "xs^4" "EqPxs3xs4" "EqDxs3xs4")
(simp "EqDxs3xs4")
(simp "EqDHyp" (pt "x^4"))
(use "InitEqD")
(use "EqPx3x4")
;; Proof finished.
;; (cdp)
(save "EqPListNcToEqD")

;; 2-1-1-2-4.  Symmetry
;; ====================

;; REqPListSym
(set-goal "allnc x^1,x^2((Pvar alpha alpha)x^1 x^2 ->
                         (Pvar alpha alpha)x^2 x^1) ->
 allnc xs^1,xs^2(
 (REqPList (cterm (x^1,x^2) (Pvar alpha alpha)x^1 x^2))xs^1 xs^2 ->
 (REqPList (cterm (x^1,x^2) (Pvar alpha alpha)x^1 x^2))xs^2 xs^1)")
(assume "SymHyp" "xs^1" "xs^2" "REqPxs1xs2")
(elim "REqPxs1xs2")
(use "REqPListNil")
(assume "x^3" "x^4" "REqPx3x4" "xs^3" "xs^4" "Useless" "REqPxs4xs3")
(use "REqPListCons")
(use "SymHyp")
(use "REqPx3x4")
(use "REqPxs4xs3")
;; Proof finished.
;; (cdp)
(save "REqPListSym")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [(alpha700=>alpha700),(list alpha700)]
;;  (Rec list alpha700=>list alpha700)(list alpha700)(Nil alpha700)
;;  ([alpha700,(list alpha700)_0](Cons alpha700)((alpha700=>alpha700)alpha700))

;; NEqPListSym
(set-goal "allnc x^1,x^2((Pvar alpha alpha)^ x^1 x^2 ->
                         (Pvar alpha alpha)^ x^2 x^1) ->
 allnc xs^1,xs^2(
 (NEqPList (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xs^1 xs^2 ->
 (NEqPList (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xs^2 xs^1)")
(assume "SymHyp" "xs^1" "xs^2" "NEqPxs1xs2")
(elim "NEqPxs1xs2")
(use "NEqPListNil")
(assume "x^3" "x^4" "NEqPx3x4" "xs^3" "xs^4" "Useless" "NEqPxs4xs3")
(use "NEqPListCons")
(use "SymHyp")
(use "NEqPx3x4")
(use "NEqPxs4xs3")
;; Proof finished.
;; (cdp)
(save "NEqPListSym")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [n](Rec nat=>nat)n 0([n0]Succ)

;; NEqPListNcSym
(set-goal "allnc x^1,x^2((Pvar alpha alpha)^ x^1 x^2 ->
                         (Pvar alpha alpha)^ x^2 x^1) ->
 allnc xs^1,xs^2(
 (NEqPListNc (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xs^1 xs^2 ->
 (NEqPListNc (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xs^2 xs^1)")
(assume "SymHyp" "xs^1" "xs^2" "NEqPxs1xs2")
(elim "NEqPxs1xs2")
(use "NEqPListNcNil")
(assume "x^3" "x^4" "NEqPx3x4" "xs^3" "xs^4" "Useless" "NEqPxs4xs3")
(use "NEqPListNcCons")
(use "SymHyp")
(use "NEqPx3x4")
(use "NEqPxs4xs3")
;; Proof finished.
;; (cdp)
(save "NEqPListNcSym")

;; EqPListSym
(set-goal "allnc x^1,x^2(EqP x^1 x^2 -> EqP x^2 x^1) ->
allnc xs^1,xs^2(EqPList xs^1 xs^2 -> EqPList xs^2 xs^1)")
(assume "SymHyp" "xs^1" "xs^2" "EqPxs1xs2")
(elim "EqPxs1xs2")
(use "EqPListNil")
(assume "x^3" "x^4" "EqPx3x4" "xs^3" "xs^4" "Useless" "EqPxs4xs3")
(use "EqPListCons")
(use "SymHyp")
(use "EqPx3x4")
(use "EqPxs4xs3")
;; Proof finished.
;; (cdp)
(save "EqPListSym")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [(alpha=>alpha),xs]
;;  (Rec list alpha=>list alpha)xs(Nil alpha)
;;  ([x,xs0](Cons alpha)((alpha=>alpha)x))

;; ANEqPListSym
(set-goal "allnc x^1,x^2(EqPNc x^1 x^2 -> EqPNc x^2 x^1) ->
allnc xs^1,xs^2(ANEqPList xs^1 xs^2 -> ANEqPList xs^2 xs^1)")
(assume "SymHyp" "xs^1" "xs^2" "ANEqPxs1xs2")
(elim "ANEqPxs1xs2")
(use "ANEqPListNil")
(assume "x^3" "x^4" "EqPx3x4" "xs^3" "xs^4" "Useless" "ANEqPxs4xs3")
(use "ANEqPListCons")
(use "SymHyp")
(use "EqPx3x4")
(use "ANEqPxs4xs3")
;; Proof finished.
;; (cdp)
(save "ANEqPListSym")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [n](Rec nat=>nat)n 0([n0]Succ)

;; SEqPListSym
(set-goal "allnc xs^1,xs^2(SEqPList xs^1 xs^2 -> SEqPList xs^2 xs^1)")
(assume "xs^1" "xs^2" "SEqPxs1xs2")
(elim "SEqPxs1xs2")
(use "SEqPListNil")
(assume "x^3" "x^4" "xs^3" "xs^4" "Useless" "SEqPxs4xs3")
(use "SEqPListCons")
(use "SEqPxs4xs3")
;; Proof finished.
;; (cdp)
(save "SEqPListSym")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp (rename-variables neterm))
;; [n](Rec nat=>nat)n 0([n0]Succ)

;; EqPListNcSym
(set-goal "allnc x^1,x^2(EqP x^1 x^2 -> EqP x^2 x^1) ->
           allnc xs^1,xs^2(EqPListNc xs^1 xs^2 -> EqPListNc xs^2 xs^1)")
(assume "SymHyp" "xs^1" "xs^2" "EqPxs1xs2")
(elim "EqPxs1xs2")
(use "EqPListNcNil")
(assume "x^3" "x^4" "EqPx3x4" "xs^3" "xs^4" "Useless" "EqPxs4xs3")
(use "EqPListNcCons")
(use "SymHyp")
(use "EqPx3x4")
(use "EqPxs4xs3")
;; Proof finished.
;; (cdp)
(save "EqPListNcSym")

;; SEqPListNcSym
(set-goal "allnc xs^1,xs^2(SEqPListNc xs^1 xs^2 -> SEqPListNc xs^2 xs^1)")
(assume "xs^1" "xs^2" "SEqPxs1xs2")
(elim "SEqPxs1xs2")
(use "SEqPListNcNil")
(assume "x^3" "x^4" "xs^3" "xs^4" "Useless" "SEqPxs4xs3")
(use "SEqPListNcCons")
(use "SEqPxs4xs3")
;; Proof finished.
;; (cdp)
(save "SEqPListNcSym")

;; For transitivity it is best to first prove that 
;; EqP xs^1 xs^2 implies totality of both arguments.
;; EqP is reflexive on total arguments
;; EqP implies EqD

;; 2-1-1-2-5.  Connections
;; =======================

;; NEqPListToNEqPNc
;; REqPListToREqPNc
;; SEqPListToSEqPNc

;; ANEqPListToSEqP
(set-goal "allnc xs^1,xs^2(ANEqPList xs^1 xs^2 -> SEqPList xs^1 xs^2)")
(assume "xs^1" "xs^2" "ANEqPxs1xs2")
(elim "ANEqPxs1xs2")
;; 3,4
(use "SEqPListNil")
;; 4
(assume "x^3" "x^4" "EqPx3x4" "xs^3" "xs^4" "ANEqPxs3xs4")
(use "SEqPListCons")
;; Proof finished.
;; (cdp)
(save "ANEqPListToSEqP")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [n](Rec nat=>nat)n 0([n0]Succ)

;; EqPListNcToSEqPNc
(set-goal "allnc xs^1,xs^2(EqPListNc xs^1 xs^2 -> SEqPListNc xs^1 xs^2)")
(assume "xs^1" "xs^2" "EqPxs1xs2")
(elim "EqPxs1xs2")
;; 3,4
(use "SEqPListNcNil")
;; 4
(assume "x^3" "x^4" "EqPx3x4" "xs^3" "xs^4" "EqPxs3xs4")
(use "SEqPListNcCons")
;; Proof finished.
;; (cdp)
(save "EqPListNcToSEqPNc")

;; 2-1-1-2-6.  Relations between Total and EqP
;; ===========================================

;; REqPListToRTotalLeft
;; NEqPListToNTotalLeft
;; NEqPListNcToNTotalNcLeft
;; EqPListToTotalLeft
;; ANEqPListToANTotalLeft
;; SEqPListToRTotalLeft
;; EqPListNcToTotalNcLeft
;; SEqPListNcToSTotalNcLeft

;; and similar for Right.  Moreover we have reflexivity theorems.

;; REqPListRefl
;; NEqPListRefl
;; NqPListReflNc
;; EqPListRefl
;; ANEqPListRefl
;; SEqPListRefl
;; EqPListNcRefl
;; SEqPListNcRefl

;; REqPListToRTotalLeft
(set-goal "allnc x^1,x^2((Pvar alpha alpha)x^1 x^2 -> (Pvar alpha)x^1) ->
 allnc xs^1,xs^2(
 (REqPList (cterm (x^1,x^2) (Pvar alpha alpha)x^1 x^2))xs^1 xs^2 ->
 (RTotalList (cterm (x^) (Pvar alpha)x^))xs^1)")
(assume "Hyp" "xs^1" "xs^2" "EqPxs1xs2")
(elim "EqPxs1xs2")
(use "RTotalListNil")
(assume "x^3" "x^4" "EqPx3x4" "xs^3" "xs^4" "Useless")
(use "RTotalListCons")
(use "Hyp" (pt "x^4"))
(use "EqPx3x4")
;; Proof finished.
;; (cdp)
(save "REqPListToRTotalLeft")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [n](Rec nat=>nat)n 0([n0]Succ)

;; NEqPListToNTotalLeft
(set-goal "allnc x^1,x^2((Pvar alpha alpha)^ x^1 x^2 -> (Pvar alpha)^ x^1) ->
 allnc xs^1,xs^2(
 (NEqPList (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xs^1 xs^2 ->
 (NTotalList (cterm (x^) (Pvar alpha)^ x^))xs^1)")
(assume "Hyp" "xs^1" "xs^2" "EqPxs1xs2")
(elim "EqPxs1xs2")
(use "NTotalListNil")
(assume "x^3" "x^4" "EqPx3x4" "xs^3" "xs^4" "Useless")
(use "NTotalListCons")
(use "Hyp" (pt "x^4"))
(use "EqPx3x4")
;; Proof finished.
;; (cdp)
(save "NEqPListToNTotalLeft")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [n](Rec nat=>nat)n 0([n0]Succ)

;; NEqPListNcToNTotalNcLeft
(set-goal "allnc x^1,x^2((Pvar alpha alpha)^ x^1 x^2 -> (Pvar alpha)^ x^1) ->
 allnc xs^1,xs^2(
 (NEqPListNc (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xs^1 xs^2 ->
 (NTotalListNc (cterm (x^) (Pvar alpha)^ x^))xs^1)")
(assume "Hyp" "xs^1" "xs^2" "EqPxs1xs2")
(elim "EqPxs1xs2")
(use "NTotalListNcNil")
(assume "x^3" "x^4" "EqPx3x4" "xs^3" "xs^4" "Useless")
(use "NTotalListNcCons")
(use "Hyp" (pt "x^4"))
(use "EqPx3x4")
;; Proof finished.
;; (cdp)
(save "NEqPListNcToNTotalNcLeft")

;; EqPListToTotalLeft
(set-goal "allnc x^1,x^2(EqP x^1 x^2 -> Total x^1) ->
           allnc xs^1,xs^2(EqPList xs^1 xs^2 -> TotalList xs^1)")
(assume "THyp" "xs^1" "xs^2" "EqPxs1xs2")
(elim "EqPxs1xs2")
(use "TotalListNil")
(assume "x^3" "x^4" "EqPx3x4" "xs^3" "xs^4" "Useless")
(use "TotalListCons")
(use "THyp" (pt "x^4"))
(use "EqPx3x4")
;; Proof finished.
;; (cdp)
(save "EqPListToTotalLeft")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [(alpha=>alpha),xs]
;;  (Rec list alpha=>list alpha)xs(Nil alpha)
;;  ([x,xs0](Cons alpha)((alpha=>alpha)x))

;; ANEqPListToANTotalLeft
(set-goal "allnc x^1,x^2(EqPNc x^1 x^2 -> TotalNc x^1) ->
           allnc xs^1,xs^2(ANEqPList xs^1 xs^2 -> ANTotalList xs^1)")
(assume "THyp" "xs^1" "xs^2" "EqPxs1xs2")
(elim "EqPxs1xs2")
(use "ANTotalListNil")
(assume "x^3" "x^4" "EqPx3x4" "xs^3" "xs^4" "Useless")
(use "ANTotalListCons")
(use "THyp" (pt "x^4"))
(use "EqPx3x4")
;; Proof finished.
;; (cdp)
(save "ANEqPListToANTotalLeft")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [n](Rec nat=>nat)n 0([n0]Succ)

;; SEqPListToSTotalLeft
(set-goal "allnc xs^1,xs^2(SEqPList xs^1 xs^2 -> STotalList xs^1)")
(assume "xs^1" "xs^2" "EqPxs1xs2")
(elim "EqPxs1xs2")
(use "STotalListNil")
(assume "x^3" "x^4" "xs^3" "xs^4" "Useless")
(use "STotalListCons")
;; Proof finished.
;; (cdp)
(save "SEqPListToSTotalLeft")

;; EqPListNcToTotalNcLeft
(set-goal "allnc x^1,x^2(EqPNc x^1 x^2 -> TotalNc x^1) ->
           allnc xs^1,xs^2(EqPListNc xs^1 xs^2 -> TotalListNc xs^1)")
(assume "THyp" "xs^1" "xs^2" "EqPxs1xs2")
(elim "EqPxs1xs2")
(use "TotalListNcNil")
(assume "x^3" "x^4" "EqPx3x4" "xs^3" "xs^4" "Useless")
(use "TotalListNcCons")
(use "THyp" (pt "x^4"))
(use  "EqPx3x4")
;; Proof finished.
;; (cdp)
(save "EqPListNcToSTotalNcLeft")

;; SEqPListNcToSTotalNcLeft
(set-goal "allnc xs^1,xs^2(SEqPListNc xs^1 xs^2 -> STotalListNc xs^1)")
(assume "xs^1" "xs^2" "EqPxs1xs2")
(elim "EqPxs1xs2")
(use "STotalListNcNil")
(assume "x^3" "x^4" "xs^3" "xs^4" "Useless")
(use "STotalListNcCons")
;; Proof finished.
;; (cdp)
(save "SEqPListNcToSTotalNcLeft")

;;The same with Right

;; REqPListToRTotalRight
(set-goal "allnc x^1,x^2((Pvar alpha alpha)x^1 x^2 -> (Pvar alpha)x^2) ->
 allnc xs^1,xs^2(
 (REqPList (cterm (x^1,x^2) (Pvar alpha alpha)x^1 x^2))xs^1 xs^2 ->
 (RTotalList (cterm (x^) (Pvar alpha)x^))xs^2)")
(assume "Hyp" "xs^1" "xs^2" "EqPxs1xs2")
(elim "EqPxs1xs2")
(use "RTotalListNil")
(assume "x^3" "x^4" "EqPx3x4" "xs^3" "xs^4" "Useless")
(use "RTotalListCons")
(use "Hyp" (pt "x^3"))
(use "EqPx3x4")
;; Proof finished.
;; (cdp)
(save "REqPListToRTotalRight")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [n](Rec nat=>nat)n 0([n0]Succ)

;; NEqPListToNTotalRight
(set-goal "allnc x^1,x^2((Pvar alpha alpha)^ x^1 x^2 -> (Pvar alpha)^ x^2) ->
 allnc xs^1,xs^2(
 (NEqPList (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xs^1 xs^2 ->
 (NTotalList (cterm (x^) (Pvar alpha)^ x^))xs^2)")
(assume "Hyp" "xs^1" "xs^2" "EqPxs1xs2")
(elim "EqPxs1xs2")
(use "NTotalListNil")
(assume "x^3" "x^4" "EqPx3x4" "xs^3" "xs^4" "Useless")
(use "NTotalListCons")
(use "Hyp" (pt "x^3"))
(use "EqPx3x4")
;; Proof finished.
;; (cdp)
(save "NEqPListToNTotalRight")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [n](Rec nat=>nat)n 0([n0]Succ)

;; NEqPListNcToNTotalNcRight
(set-goal "allnc x^1,x^2((Pvar alpha alpha)^ x^1 x^2 -> (Pvar alpha)^ x^2) ->
 allnc xs^1,xs^2(
 (NEqPListNc (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xs^1 xs^2 ->
 (NTotalListNc (cterm (x^) (Pvar alpha)^ x^))xs^2)")
(assume "Hyp" "xs^1" "xs^2" "EqPxs1xs2")
(elim "EqPxs1xs2")
(use "NTotalListNcNil")
(assume "x^3" "x^4" "EqPx3x4" "xs^3" "xs^4" "Useless")
(use "NTotalListNcCons")
(use "Hyp" (pt "x^3"))
(use "EqPx3x4")
;; Proof finished.
;; (cdp)
(save "NEqPListNcToNTotalNcRight")

;; EqPListToTotalRight
(set-goal "allnc x^1,x^2(EqP x^1 x^2 -> Total x^2) ->
           allnc xs^1,xs^2(EqPList xs^1 xs^2 -> TotalList xs^2)")
(assume "THyp" "xs^1" "xs^2" "EqPxs1xs2")
(elim "EqPxs1xs2")
(use "TotalListNil")
(assume "x^3" "x^4" "EqPx3x4" "xs^3" "xs^4" "Useless")
(use "TotalListCons")
(use "THyp" (pt "x^3"))
(use "EqPx3x4")
;; Proof finished.
;; (cdp)
(save "EqPListToTotalRight")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [(alpha=>alpha),xs]
;;  (Rec list alpha=>list alpha)xs(Nil alpha)
;;  ([x,xs0](Cons alpha)((alpha=>alpha)x))

;; ANEqPListToANTotalRight
(set-goal "allnc x^1,x^2(EqPNc x^1 x^2 -> TotalNc x^2) ->
           allnc xs^1,xs^2(ANEqPList xs^1 xs^2 -> ANTotalList xs^2)")
(assume "THyp" "xs^1" "xs^2" "EqPxs1xs2")
(elim "EqPxs1xs2")
(use "ANTotalListNil")
(assume "x^3" "x^4" "EqPx3x4" "xs^3" "xs^4" "Useless")
(use "ANTotalListCons")
(use "THyp" (pt "x^3"))
(use "EqPx3x4")
;; Proof finished.
;; (cdp)
(save "ANEqPListToANTotalRight")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [n](Rec nat=>nat)n 0([n0]Succ)

;; SEqPListToSTotalRight
(set-goal "allnc xs^1,xs^2(SEqPList xs^1 xs^2 -> STotalList xs^2)")
(assume "xs^1" "xs^2" "EqPxs1xs2")
(elim "EqPxs1xs2")
(use "STotalListNil")
(assume "x^3" "x^4" "xs^3" "xs^4" "Useless")
(use "STotalListCons")
;; Proof finished.
;; (cdp)
(save "SEqPListToSTotalRight")

;; EqPListNcToTotalNcRight
(set-goal "allnc x^1,x^2(EqPNc x^1 x^2 -> TotalNc x^2) ->
           allnc xs^1,xs^2(EqPListNc xs^1 xs^2 -> TotalListNc xs^2)")
(assume "THyp" "xs^1" "xs^2" "EqPxs1xs2")
(elim "EqPxs1xs2")
(use "TotalListNcNil")
(assume "x^3" "x^4" "EqPx3x4" "xs^3" "xs^4" "Useless")
(use "TotalListNcCons")
(use "THyp" (pt "x^3"))
(use  "EqPx3x4")
;; Proof finished.
;; (cdp)
(save "EqPListNcToSTotalNcRight")

;; SEqPListNcToSTotalNcRight
(set-goal "allnc xs^1,xs^2(SEqPListNc xs^1 xs^2 -> STotalListNc xs^2)")
(assume "xs^1" "xs^2" "EqPxs1xs2")
(elim "EqPxs1xs2")
(use "STotalListNcNil")
(assume "x^3" "x^4" "xs^3" "xs^4" "Useless")
(use "STotalListNcCons")
;; Proof finished.
;; (cdp)
(save "SEqPListNcToSTotalNcRight")

;; Now for reflexivity

;; REqPListRefl
(set-goal "allnc x^((Pvar alpha)x^ -> (Pvar alpha alpha)x^ x^) ->
 allnc xs^((RTotalList (cterm (x^) (Pvar alpha)x^))xs^ ->
 (REqPList (cterm (x^1,x^2) (Pvar alpha alpha)x^1 x^2))xs^ xs^)")
(assume "Hyp" "xs^" "Txs")
(elim "Txs")
;; 3,4
(use "REqPListNil")
;; 4
(assume "x^1" "Px1" "xs^1" "Txs1")
(use "REqPListCons")
(use "Hyp")
(use "Px1")
;; Proof finished.
;; (cdp)
(save "REqPListRefl")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [(gamma=>alpha768),(list gamma)]
;;  (Rec list gamma=>list alpha768)(list gamma)(Nil alpha768)
;;  ([gamma,(list gamma)_0](Cons alpha768)((gamma=>alpha768)gamma))

;; NEqPListRefl
(set-goal "allnc x^((Pvar alpha)^ x^ -> (Pvar alpha alpha)^ x^ x^) ->
 allnc xs^((NTotalList (cterm (x^) (Pvar alpha)^ x^))xs^ ->
 (NEqPList (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xs^ xs^)")
(assume "Hyp" "xs^" "Txs")
(elim "Txs")
;; 3,4
(use "NEqPListNil")
;; 4
(assume "x^1" "Px1" "xs^1" "Txs1")
(use "NEqPListCons")
(use "Hyp")
(use "Px1")
;; Proof finished.
;; (cdp)
(save "NEqPListRefl")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [n](Rec nat=>nat)n 0([n0]Succ)

;; NEqPListReflNc
(set-goal "allnc x^((Pvar alpha)^ x^ -> (Pvar alpha alpha)^ x^ x^) ->
 allnc xs^((NTotalListNc (cterm (x^) (Pvar alpha)^ x^))xs^ ->
 (NEqPListNc (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xs^ xs^)")
(assume "Hyp" "xs^" "Txs")
(elim "Txs")
;; 3,4
(use "NEqPListNcNil")
;; 4
(assume "x^1" "Px1" "xs^1" "Txs1")
(use "NEqPListNcCons")
(use "Hyp")
(use "Px1")
;; Proof finished.
;; (cdp)
(save "NEqPListReflNc")

;; EqPListRefl
(set-goal "allnc x^(Total x^ -> EqP x^ x^) ->
 allnc xs^(TotalList xs^ -> EqPList xs^ xs^)")
(assume "EqPHyp" "xs^" "Txs")
(elim "Txs")
(use "EqPListNil")
(assume "x^1" "Tx1" "xs^1" "Txs1")
(use "EqPListCons")
(use "EqPHyp")
(use "Tx1")
;; Proof finished.
;; (cdp)
(save "EqPListRefl")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [(alpha=>alpha),xs]
;;  (Rec list alpha=>list alpha)xs(Nil alpha)
;;  ([x,xs0](Cons alpha)((alpha=>alpha)x))

;; ANEqPListRefl
(set-goal "allnc x^(TotalNc x^ -> EqPNc x^ x^) ->
 allnc xs^(ANTotalList xs^ -> ANEqPList xs^ xs^)")
(assume "EqPHyp" "xs^" "Txs")
(elim "Txs")
(use "ANEqPListNil")
(assume "x^1" "Tx1" "xs^1" "Txs1")
(use "ANEqPListCons")
(use "EqPHyp")
(use "Tx1")
;; Proof finished.
;; (cdp)
(save "ANEqPListRefl")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [n](Rec nat=>nat)n 0([n0]Succ)

;; SEqPListRefl
(set-goal "allnc x^(TotalNc x^ -> EqPNc x^ x^) ->
 allnc xs^(STotalList xs^ -> SEqPList xs^ xs^)")
(assume "EqPHyp" "xs^" "Txs")
(elim "Txs")
(use "SEqPListNil")
(assume "x^1" "xs^1" "Txs1")
(use "SEqPListCons")
;; Proof finished.
;; (cdp)
(save "SEqPListRefl")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [n](Rec nat=>nat)n 0([n0]Succ)

;; EqPListNcRefl
(set-goal "allnc x^(TotalNc x^ -> EqPNc x^ x^) ->
 allnc xs^(TotalListNc xs^ -> EqPListNc xs^ xs^)")
(assume "EqPHyp" "xs^" "Txs")
(elim "Txs")
(use "EqPListNcNil")
(assume "x^1" "Tx1" "xs^1" "Txs1")
(use "EqPListNcCons")
(use "EqPHyp")
(use "Tx1")
;; Proof finished.
;; (cdp)
(save "EqPListNcRefl")

;; SEqPListNcRefl
(set-goal "allnc x^(TotalNc x^ -> EqPNc x^ x^) ->
 allnc xs^(STotalListNc xs^ -> SEqPListNc xs^ xs^)")
(assume "EqPHyp" "xs^" "Txs")
(elim "Txs")
(use "SEqPListNcNil")
(assume "x^1" "xs^1" "Txs1")
(use "SEqPListNcCons")
;; Proof finished.
;; (cdp)
(save "SEqPListNcRefl")

;; 2-1-2.  CoEqP
;; =============

;; 2-1-2-2.  Properties
;; ====================

;; 2-1-2-2-1.  Monotonicity
;; ========================

;; ListCoREqPMon
(set-goal "allnc x^1,x^2(
     (Pvar alpha alpha)_1 x^1 x^2 -> (Pvar alpha alpha)_2 x^1 x^2) -> 
    allnc xs^1,xs^2(
     (CoREqPList (cterm (x^1,x^2) (Pvar alpha alpha)_1 x^1 x^2))xs^1 xs^2 -> 
     (CoREqPList (cterm (x^1,x^2) (Pvar alpha alpha)_2 x^1 x^2))xs^1 xs^2)")
(assume "MonHyp" "xs^1" "xs^2" "CoRHyp1")
(coind "CoRHyp1")
(assume "xs^3" "xs^4" "CoRHyp2")
(inst-with-to
 "CoREqPListClause"
 (make-cterm (pv "x^1") (pv "x^2") (pf "(Pvar alpha alpha)_1 x^1 x^2"))
 (pt "xs^3") (pt "xs^4") "CoRHyp2" "Inst")
(elim "Inst")
;; 7,8
(drop "Inst")
(assume "NilHyp")
(intro 0)
(use "NilHyp")
;; 8
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^5" "x5Prop")
(by-assume "x5Prop" "x^6" "x5x6Prop")
(inst-with-to "x5x6Prop" 'left "Px5x6")
(inst-with-to "x5x6Prop" 'right "ExHyp2")
(drop "x5x6Prop")
(by-assume "ExHyp2" "xs^5" "x5xs5Prop")
(by-assume "x5xs5Prop" "xs^6" "x5xs5x6xs6Prop")
(intro 1)
(intro 0 (pt "x^5"))
(intro 0 (pt "x^6"))
(split)
(use "MonHyp")
(use "Px5x6")
(intro 0 (pt "xs^5"))
(intro 0 (pt "xs^6"))
(split)
(intro 1)
(use "x5xs5x6xs6Prop")
(use "x5xs5x6xs6Prop")
;; Proof finished.
;; (cdp)
(save "ListCoREqPMon")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [(alpha749=>alpha751),(list alpha749)]
;;  (CoRec list alpha749=>list alpha751)(list alpha749)
;;  ([(list alpha749)_0]
;;    [if (DesYprod(list alpha749)_0)
;;      (DummyL alpha751 yprod(list alpha751 ysum list alpha749))
;;      ([(alpha749 yprod list alpha749)]
;;       Inr((alpha749=>alpha751)clft(alpha749 yprod list alpha749)pair
;;           (InR (list alpha749) (list alpha751))
;;           crht(alpha749 yprod list alpha749)))])

;; ListCoNEqPMon
(set-goal "allnc x^1,x^2(
     (Pvar alpha alpha)^1 x^1 x^2 -> (Pvar alpha alpha)^2 x^1 x^2) -> 
    allnc xs^1,xs^2(
     (CoNEqPList (cterm (x^1,x^2) (Pvar alpha alpha)^1 x^1 x^2))xs^1 xs^2 -> 
     (CoNEqPList (cterm (x^1,x^2) (Pvar alpha alpha)^2 x^1 x^2))xs^1 xs^2)")
(assume "MonHyp" "xs^1" "xs^2" "CoNHyp1")
(coind "CoNHyp1")
(assume "xs^3" "xs^4" "CoNHyp2")
(inst-with-to
 "CoNEqPListClause"
 (make-cterm (pv "x^1") (pv "x^2") (pf "(Pvar alpha alpha)^1 x^1 x^2"))
 (pt "xs^3") (pt "xs^4") "CoNHyp2" "Inst")
(elim "Inst")
;; 7,8
(drop "Inst")
(assume "NilHyp")
(intro 0)
(use "NilHyp")
;; 8
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^5" "x5Prop")
(by-assume "x5Prop" "x^6" "x5x6Prop")
(inst-with-to "x5x6Prop" 'left "Px5x6")
(inst-with-to "x5x6Prop" 'right "ExHyp2")
(drop "x5x6Prop")
(by-assume "ExHyp2" "xs^5" "x5xs5Prop")
(by-assume "x5xs5Prop" "xs^6" "x5xs5x6xs6Prop")
(intro 1)
(intro 0 (pt "x^5"))
(intro 0 (pt "x^6"))
(split)
(use "MonHyp")
(use "Px5x6")
(intro 0 (pt "xs^5"))
(intro 0 (pt "xs^6"))
(split)
(intro 1)
(use "x5xs5x6xs6Prop")
(use "x5xs5x6xs6Prop")
;; Proof finished.
;; (cdp)
(save "ListCoNEqPMon")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n]
;;  (CoRec nat=>nat)n
;;  ([n0][if (Des n0) (DummyL nat ysum nat) ([n1]Inr((InR nat nat)n1))])

;; ListCoNEqPMonNc
(set-goal "allnc x^1,x^2(
     (Pvar alpha alpha)^1 x^1 x^2 -> (Pvar alpha alpha)^2 x^1 x^2) -> 
    allnc xs^1,xs^2(
     (CoNEqPListNc (cterm (x^1,x^2) (Pvar alpha alpha)^1 x^1 x^2))xs^1 xs^2 -> 
     (CoNEqPListNc (cterm (x^1,x^2) (Pvar alpha alpha)^2 x^1 x^2))xs^1 xs^2)")
(assume "MonHyp" "xs^1" "xs^2" "CoNHyp1")
(coind "CoNHyp1")
(assume "xs^3" "xs^4" "CoNHyp2")
(inst-with-to
 "CoNEqPListNcClause"
 (make-cterm (pv "x^1") (pv "x^2") (pf "(Pvar alpha alpha)^1 x^1 x^2"))
 (pt "xs^3") (pt "xs^4") "CoNHyp2" "Inst")
(elim "Inst")
;; 7,8
(drop "Inst")
(assume "NilHyp")
(intro 0)
(use "NilHyp")
;; 8
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^5" "x5Prop")
(by-assume "x5Prop" "x^6" "x5x6Prop")
(inst-with-to "x5x6Prop" 'left "Px5x6")
(inst-with-to "x5x6Prop" 'right "ExHyp2")
(drop "x5x6Prop")
(by-assume "ExHyp2" "xs^5" "x5xs5Prop")
(by-assume "x5xs5Prop" "xs^6" "x5xs5x6xs6Prop")
(intro 1)
(intro 0 (pt "x^5"))
(intro 0 (pt "x^6"))
(split)
(use "MonHyp")
(use "Px5x6")
(intro 0 (pt "xs^5"))
(intro 0 (pt "xs^6"))
(split)
(intro 1)
(use "x5xs5x6xs6Prop")
(use "x5xs5x6xs6Prop")
;; Proof finished.
;; (cdp)
(save "ListCoNEqPMonNc")

;; 2-1-2-2-2.  Symmetry
;; ====================

;; CoREqPListSym
(set-goal "allnc x^1,x^2((Pvar alpha alpha)x^1 x^2 -> x^1 eqd x^2) -> 
    allnc xs^1,xs^2(
     (CoREqPList (cterm (x^1,x^2) (Pvar alpha alpha)x^1 x^2))xs^1 xs^2 -> 
     (CoREqPList (cterm (x^1,x^2) (Pvar alpha alpha)x^1 x^2))xs^2 xs^1)")
(assume "EqDHyp" "xs^1" "xs^2" "xs1~xs2")
(coind "xs1~xs2")
(assume "xs^3" "xs^4" "xs4~xs3")
(inst-with-to
 (make-proof-in-aconst-form
  (coidpredconst-to-closure-aconst
   (predicate-form-to-predicate
    (pf "(CoREqPList (cterm (x^1,x^2) (Pvar alpha alpha)x^1 x^2)) xs^2 xs^1"))))
 (pt "xs^4") (pt "xs^3") "xs4~xs3" "Inst")
(elim "Inst")
;; 7,8
(drop "Inst")
(assume "Conj")
(intro 0)
(split)
(use "Conj")
(use "Conj")
;; 8
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^5" "x5Prop")
(by-assume "x5Prop" "x^6" "x5x6Prop")
(inst-with-to "x5x6Prop" 'left "Px5x6")
(inst-with-to "x5x6Prop" 'right "ExHyp2")
(drop "x5x6Prop")
(intro 1)
(intro 0 (pt "x^5"))
(intro 0 (pt "x^6"))
(split)
(use "Px5x6")
(by-assume "ExHyp2" "xs^5" "xs5Prop")
(by-assume "xs5Prop" "xs^6" "xs5xs6Prop")
(intro 0 (pt "xs^6"))
(intro 0 (pt "xs^5"))
(split)
(intro 1)
(use "xs5xs6Prop")
(split)
(simp (pf "x^5 eqd x^6"))
(use "xs5xs6Prop")
(use "EqDHyp")
(use "Px5x6")
(simp "<-" (pf "x^5 eqd x^6"))
(use "xs5xs6Prop")
(use "EqDHyp")
(use "Px5x6")
;; Proof finished.
;; (cdp)
(save "CoREqPListSym")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [(list alpha700)]
;;  (CoRec list alpha700=>list alpha700)(list alpha700)
;;  ([(list alpha700)_0]
;;    [if (DesYprod(list alpha700)_0)
;;      (DummyL alpha700 yprod(list alpha700 ysum list alpha700))
;;      ([(alpha700 yprod list alpha700)]
;;       Inr(clft(alpha700 yprod list alpha700)pair
;;           (InR (list alpha700) (list alpha700))
;;           crht(alpha700 yprod list alpha700)))])

;; CoNEqPListSym
(set-goal "allnc x^1,x^2((Pvar alpha alpha)^ x^1 x^2 -> x^1 eqd x^2) -> 
    allnc xs^1,xs^2(
     (CoNEqPList (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xs^1 xs^2 -> 
     (CoNEqPList (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xs^2 xs^1)")
(assume "EqDHyp" "xs^1" "xs^2" "xs1~xs2")
(coind "xs1~xs2")
(assume "xs^3" "xs^4" "xs4~xs3")
(inst-with-to
 (make-proof-in-aconst-form
  (coidpredconst-to-closure-aconst
   (predicate-form-to-predicate
    (pf
     "(CoNEqPList (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2)) xs^2 xs^1"))))
 (pt "xs^4") (pt "xs^3") "xs4~xs3" "Inst")
(elim "Inst")
;; 7,8
(drop "Inst")
(assume "Conj")
(intro 0)
(split)
(use "Conj")
(use "Conj")
;; 8
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^5" "x5Prop")
(by-assume "x5Prop" "x^6" "x5x6Prop")
(inst-with-to "x5x6Prop" 'left "Px5x6")
(inst-with-to "x5x6Prop" 'right "ExHyp2")
(drop "x5x6Prop")
(intro 1)
(intro 0 (pt "x^5"))
(intro 0 (pt "x^6"))
(split)
(use "Px5x6")
(by-assume "ExHyp2" "xs^5" "xs5Prop")
(by-assume "xs5Prop" "xs^6" "xs5xs6Prop")
(intro 0 (pt "xs^6"))
(intro 0 (pt "xs^5"))
(split)
(intro 1)
(use "xs5xs6Prop")
(split)
(simp (pf "x^5 eqd x^6"))
(use "xs5xs6Prop")
(use "EqDHyp")
(use "Px5x6")
(simp "<-" (pf "x^5 eqd x^6"))
(use "xs5xs6Prop")
(use "EqDHyp")
(use "Px5x6")
;; Proof finished.
;; (cdp)
(save "CoNEqPListSym")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n]
;;  (CoRec nat=>nat)n
;;  ([n0][if (Des n0) (DummyL nat ysum nat) ([n1]Inr((InR nat nat)n1))])

;; CoNEqPListNcSym
(set-goal "allnc x^1,x^2((Pvar alpha alpha)^ x^1 x^2 -> x^1 eqd x^2) -> 
    allnc xs^1,xs^2(
     (CoNEqPListNc (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xs^1 xs^2 -> 
     (CoNEqPListNc (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xs^2 xs^1)")
(assume "EqDHyp" "xs^1" "xs^2" "xs1~xs2")
(coind "xs1~xs2")
(assume "xs^3" "xs^4" "xs4~xs3")
(inst-with-to
 (make-proof-in-aconst-form
  (coidpredconst-to-closure-aconst
   (predicate-form-to-predicate
    (pf
    "(CoNEqPListNc (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2)) xs^2 xs^1"))))
 (pt "xs^4") (pt "xs^3") "xs4~xs3" "Inst")
(elim "Inst")
;; 7,8
(drop "Inst")
(assume "Conj")
(intro 0)
(split)
(use "Conj")
(use "Conj")
;; 8
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^5" "x5Prop")
(by-assume "x5Prop" "x^6" "x5x6Prop")
(inst-with-to "x5x6Prop" 'left "Px5x6")
(inst-with-to "x5x6Prop" 'right "ExHyp2")
(drop "x5x6Prop")
(intro 1)
(intro 0 (pt "x^5"))
(intro 0 (pt "x^6"))
(split)
(use "Px5x6")
(by-assume "ExHyp2" "xs^5" "xs5Prop")
(by-assume "xs5Prop" "xs^6" "xs5xs6Prop")
(intro 0 (pt "xs^6"))
(intro 0 (pt "xs^5"))
(split)
(intro 1)
(use "xs5xs6Prop")
(split)
(simp (pf "x^5 eqd x^6"))
(use "xs5xs6Prop")
(use "EqDHyp")
(use "Px5x6")
(simp "<-" (pf "x^5 eqd x^6"))
(use "xs5xs6Prop")
(use "EqDHyp")
(use "Px5x6")
;; Proof finished.
;; (cdp)
(save "CoNEqPListNcSym")

;; CoEqPListSym
(set-goal "allnc x^1,x^2(EqPNc x^1 x^2 -> x^1 eqd x^2) ->
           allnc xs^1,xs^2(CoEqPList xs^1 xs^2 -> CoEqPList xs^2 xs^1)")
(assume "EqDHyp" "xs^1" "xs^2" "xs1~xs2")
(coind "xs1~xs2")
(assume "xs^3" "xs^4" "xs4~xs3")
(inst-with-to
 (make-proof-in-aconst-form
  (coidpredconst-to-closure-aconst
   (predicate-form-to-predicate (pf "CoEqPList xs^2 xs^1"))))
 (pt "xs^4") (pt "xs^3") "xs4~xs3" "Inst")
(elim "Inst")
;; 7,8
(drop "Inst")
(assume "Conj")
(intro 0)
(split)
(use "Conj")
(use "Conj")
;; 8
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^5" "x5Prop")
(by-assume "x5Prop" "x^6" "x5x6Prop")
(inst-with-to "x5x6Prop" 'left "EqPx5x6")
(inst-with-to "x5x6Prop" 'right "ExHyp2")
(drop "x5x6Prop")
(intro 1)
(intro 0 (pt "x^5"))
(intro 0 (pt "x^6"))
(split)
(use "EqPx5x6")
(by-assume "ExHyp2" "xs^5" "xs5Prop")
(by-assume "xs5Prop" "xs^6" "xs5xs6Prop")
(intro 0 (pt "xs^6"))
(intro 0 (pt "xs^5"))
(split)
(intro 1)
(use "xs5xs6Prop")
(split)
(simp (pf "x^5 eqd x^6"))
(use "xs5xs6Prop")
(use "EqDHyp")
(use "EqPx5x6")
(simp "<-" (pf "x^5 eqd x^6"))
(use "xs5xs6Prop")
(use "EqDHyp")
(use "EqPx5x6")
;; Proof finished.
;; (cdp)
(save "CoEqPListSym")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [xs]
;;  (CoRec list alpha=>list alpha)xs
;;  ([xs0]
;;    [if (DesYprod xs0)
;;      (DummyL alpha yprod(list alpha ysum list alpha))
;;      ([(alpha yprod list alpha)]
;;       Inr(clft(alpha yprod list alpha)pair
;;           (InR (list alpha) (list alpha))crht(alpha yprod list alpha)))])

;; CoANEqPListSym
(set-goal "allnc x^1,x^2(EqPNc x^1 x^2 -> x^1 eqd x^2) ->
           allnc xs^1,xs^2(CoANEqPList xs^1 xs^2 -> CoANEqPList xs^2 xs^1)")
(assume "EqDHyp" "xs^1" "xs^2" "xs1~xs2")
(coind "xs1~xs2")
(assume "xs^3" "xs^4" "xs4~xs3")
(inst-with-to
 (make-proof-in-aconst-form
  (coidpredconst-to-closure-aconst
   (predicate-form-to-predicate (pf "CoANEqPList xs^2 xs^1"))))
 (pt "xs^4") (pt "xs^3") "xs4~xs3" "Inst")
(elim "Inst")
;; 7,8
(drop "Inst")
(assume "Conj")
(intro 0)
(split)
(use "Conj")
(use "Conj")
;; 8
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^5" "x5Prop")
(by-assume "x5Prop" "x^6" "x5x6Prop")
(inst-with-to "x5x6Prop" 'left "EqPx5x6")
(inst-with-to "x5x6Prop" 'right "ExHyp2")
(drop "x5x6Prop")
(intro 1)
(intro 0 (pt "x^5"))
(intro 0 (pt "x^6"))
(split)
(use "EqPx5x6")
(by-assume "ExHyp2" "xs^5" "xs5Prop")
(by-assume "xs5Prop" "xs^6" "xs5xs6Prop")
(intro 0 (pt "xs^6"))
(intro 0 (pt "xs^5"))
(split)
(intro 1)
(use "xs5xs6Prop")
(split)
(simp (pf "x^5 eqd x^6"))
(use "xs5xs6Prop")
(use "EqDHyp")
(use "EqPx5x6")
(simp "<-" (pf "x^5 eqd x^6"))
(use "xs5xs6Prop")
(use "EqDHyp")
(use "EqPx5x6")
;; Proof finished.
;; (cdp)
(save "CoANEqPListSym")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n]
;;  (CoRec nat=>nat)n
;;  ([n0][if (Des n0) (DummyL nat ysum nat) ([n1]Inr((InR nat nat)n1))])

;; CoSEqPListSym
(set-goal "allnc xs^1,xs^2(CoSEqPList xs^1 xs^2 -> CoSEqPList xs^2 xs^1)")
(assume "xs^1" "xs^2" "xs1~xs2")
(coind "xs1~xs2")
(assume "xs^3" "xs^4" "xs4~xs3")
(inst-with-to
 (make-proof-in-aconst-form
  (coidpredconst-to-closure-aconst
   (predicate-form-to-predicate (pf "CoSEqPList xs^2 xs^1"))))
 (pt "xs^4") (pt "xs^3") "xs4~xs3" "Inst")
(elim "Inst")
;; 7,8
(drop "Inst")
(assume "Conj")
(intro 0)
(split)
(use "Conj")
(use "Conj")
;; 8
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^5" "x5Prop")
(by-assume "x5Prop" "x^6" "x5x6Prop")
(by-assume "x5x6Prop" "xs^5" "x5x6xs5Prop")
(by-assume "x5x6xs5Prop" "xs^6" "x5x6xs5xs6Prop")
(intro 1)
(intro 0 (pt "x^6"))
(intro 0 (pt "x^5"))
(intro 0 (pt "xs^6"))
(intro 0 (pt "xs^5"))
(split)
(intro 1)
(use "x5x6xs5xs6Prop")
(split)
(use "x5x6xs5xs6Prop")
(use "x5x6xs5xs6Prop")
;; Proof finished.
;; (cdp)
(save "CoSEqPListSym")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n]
;;  (CoRec nat=>nat)n
;;  ([n0][if (Des n0) (DummyL nat ysum nat) ([n1]Inr((InR nat nat)n1))])

;; CoEqPListNcSym
(set-goal "allnc x^1,x^2(EqPNc x^1 x^2 -> x^1 eqd x^2) ->
           allnc xs^1,xs^2(CoEqPListNc xs^1 xs^2 -> CoEqPListNc xs^2 xs^1)")
(assume "EqDHyp" "xs^1" "xs^2" "xs1~xs2")
(coind "xs1~xs2")
(assume "xs^3" "xs^4" "xs4~xs3")
(inst-with-to
 (make-proof-in-aconst-form
  (coidpredconst-to-closure-aconst
   (predicate-form-to-predicate (pf "CoEqPListNc xs^2 xs^1"))))
 (pt "xs^4") (pt "xs^3") "xs4~xs3" "Inst")
(elim "Inst")
;; 7,8
(drop "Inst")
(assume "Conj")
(intro 0)
(split)
(use "Conj")
(use "Conj")
;; 8
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^5" "x5Prop")
(by-assume "x5Prop" "x^6" "x5x6Prop")
(inst-with-to "x5x6Prop" 'left "EqPx5x6")
(inst-with-to "x5x6Prop" 'right "ExHyp2")
(drop "x5x6Prop")
(intro 1)
(intro 0 (pt "x^5"))
(intro 0 (pt "x^6"))
(split)
(use "EqPx5x6")
(by-assume "ExHyp2" "xs^5" "xs5Prop")
(by-assume "xs5Prop" "xs^6" "xs5xs6Prop")
(intro 0 (pt "xs^6"))
(intro 0 (pt "xs^5"))
(split)
(intro 1)
(use "xs5xs6Prop")
(split)
(simp (pf "x^5 eqd x^6"))
(use "xs5xs6Prop")
(use "EqDHyp")
(use "EqPx5x6")
(simp "<-" (pf "x^5 eqd x^6"))
(use "xs5xs6Prop")
(use "EqDHyp")
(use "EqPx5x6")
;; Proof finished.
;; (cdp)
(save "CoEqPListNcSym")

;; CoSEqPListNcSym
(set-goal "allnc xs^1,xs^2(CoSEqPListNc xs^1 xs^2 -> CoSEqPListNc xs^2 xs^1)")
(assume "xs^1" "xs^2" "xs1~xs2")
(coind "xs1~xs2")
(assume "xs^3" "xs^4" "xs4~xs3")
(inst-with-to
 (make-proof-in-aconst-form
  (coidpredconst-to-closure-aconst
   (predicate-form-to-predicate (pf "CoSEqPListNc xs^2 xs^1"))))
 (pt "xs^4") (pt "xs^3") "xs4~xs3" "Inst")
(elim "Inst")
;; 7,8
(drop "Inst")
(assume "Conj")
(intro 0)
(split)
(use "Conj")
(use "Conj")
;; 8
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^5" "x5Prop")
(by-assume "x5Prop" "x^6" "x5x6Prop")
(by-assume "x5x6Prop" "xs^5" "x5x6xs5Prop")
(by-assume "x5x6xs5Prop" "xs^6" "x5x6xs5xs6Prop")
(intro 1)
(intro 0 (pt "x^6"))
(intro 0 (pt "x^5"))
(intro 0 (pt "xs^6"))
(intro 0 (pt "xs^5"))
(split)
(intro 1)
(use "x5x6xs5xs6Prop")
(split)
(use "x5x6xs5xs6Prop")
(use "x5x6xs5xs6Prop")
;; Proof finished.
;; (cdp)
(save "CoSEqPListNcSym")

;; 2-1-2-2-3.  EqPList implies CoEqPList, Ex falso
;; ===============================================

;; For the 8 variants of EqPList defined in 2-1-1-1 we prove that the
;; original predicates are contained in their duals.  Their ex-falso
;; theorems then follow from the ones for EqP in 2-1-1-2-1.

;; REqPListToCoREqP
;; NEqPListToCoNEqP
;; NEqPListNcToCoNEqPNc
;; EqPListToCoEqP
;; ANEqPListToCoANEqP
;; SEqPListToCoSEqP
;; EqPListNcToCoEqPNc
;; SEqPListNcToCoSEqPNc

;; REqPListToCoREqP
(set-goal "allnc xs^1,xs^2(
 (REqPList (cterm (x^1,x^2) (Pvar alpha alpha)x^1 x^2))xs^1xs^2 ->
 (CoREqPList (cterm (x^1,x^2) (Pvar alpha alpha)x^1 x^2))xs^1 xs^2)")
(assume "xs^1" "xs^2" "EqPxs1xs2")
(coind "EqPxs1xs2")
(assume "xs^3" "xs^4" "EqPxs3xs4")
(elim "EqPxs3xs4")
;; 5,6
(intro 0)
(split)
(use "InitEqD")
(use "InitEqD")
;; 6
(assume "x^5" "x^6" "Px5x6" "xs^5" "xs^6" "EqPxs5xs6" "Disj")
(elim "Disj")
;; 11,12
(drop "Disj")
(assume "NilHyp")
(intro 1)
(intro 0 (pt "x^5"))
(intro 0 (pt "x^6"))
(split)
(use "Px5x6")
(intro 0 (pt "xs^5"))
(intro 0 (pt "xs^6"))
(split)
(intro 1)
(use "EqPxs5xs6")
(split)
(use "InitEqD")
(use "InitEqD")
;; 12
(drop "Disj")
(assume "ExHyp")
(by-assume "ExHyp" "x^7" "x7Prop")
(by-assume "x7Prop" "x^8" "x7x8Prop")
(inst-with-to "x7x8Prop" 'left "Px7x8")
(inst-with-to "x7x8Prop" 'right "ExHyp78")
(drop "x7x8Prop")
(intro 1)
(by-assume "ExHyp78" "xs^7" "xs7Prop")
(by-assume "xs7Prop" "xs^8" "xs7xs8Prop")
(intro 0 (pt "x^5"))
(intro 0 (pt "x^6"))
(split)
(use "Px5x6")
(intro 0 (pt "xs^5"))
(intro 0 (pt "xs^6"))
(split)
(intro 1)
(use "EqPxs5xs6")
(split)
(use "InitEqD")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "REqPListToCoREqP")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [(list alpha700)]
;;  (CoRec list alpha700=>list alpha700)(list alpha700)
;;  ([(list alpha700)_0]
;;    (Rec list alpha700=>uysum(alpha700 yprod(list alpha700 ysum list alpha700)))
;;    (list alpha700)_0
;;    (DummyL alpha700 yprod(list alpha700 ysum list alpha700))
;;    ([alpha700,(list alpha700)_1,(uysum(alpha700 yprod(list alpha700 ysum list alpha700)))]
;;      Inr(alpha700 pair(InR (list alpha700) (list alpha700))(list alpha700)_1)))

;; NEqPListToCoNEqP
(set-goal "allnc xs^1,xs^2(
 (NEqPList (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xs^1xs^2 ->
 (CoNEqPList (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xs^1 xs^2)")
(assume "xs^1" "xs^2" "EqPxs1xs2")
(coind "EqPxs1xs2")
(assume "xs^3" "xs^4" "EqPxs3xs4")
(elim "EqPxs3xs4")
;; 5,6
(intro 0)
(split)
(use "InitEqD")
(use "InitEqD")
;; 6
(assume "x^5" "x^6" "Px5x6" "xs^5" "xs^6" "EqPxs5xs6" "Disj")
(elim "Disj")
;; 11,12
(drop "Disj")
(assume "NilHyp")
(intro 1)
(intro 0 (pt "x^5"))
(intro 0 (pt "x^6"))
(split)
(use "Px5x6")
(intro 0 (pt "xs^5"))
(intro 0 (pt "xs^6"))
(split)
(intro 1)
(use "EqPxs5xs6")
(split)
(use "InitEqD")
(use "InitEqD")
;; 12
(drop "Disj")
(assume "ExHyp")
(by-assume "ExHyp" "x^7" "x7Prop")
(by-assume "x7Prop" "x^8" "x7x8Prop")
(inst-with-to "x7x8Prop" 'left "Px7x8")
(inst-with-to "x7x8Prop" 'right "ExHyp78")
(drop "x7x8Prop")
(intro 1)
(by-assume "ExHyp78" "xs^7" "xs7Prop")
(by-assume "xs7Prop" "xs^8" "xs7xs8Prop")
(intro 0 (pt "x^5"))
(intro 0 (pt "x^6"))
(split)
(use "Px5x6")
(intro 0 (pt "xs^5"))
(intro 0 (pt "xs^6"))
(split)
(intro 1)
(use "EqPxs5xs6")
(split)
(use "InitEqD")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "NEqPListToCoNEqP")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n]
;;  (CoRec nat=>nat)n
;;  ([n0]
;;    (Rec nat=>uysum(nat ysum nat))n0(DummyL nat ysum nat)
;;    ([n1,(uysum(nat ysum nat))]Inr((InR nat nat)n1)))


;; NEqPListNcToCoNEqPNc
(set-goal "allnc xs^1,xs^2(
 (NEqPListNc (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xs^1xs^2 ->
 (CoNEqPListNc (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xs^1 xs^2)")
(assume "xs^1" "xs^2" "EqPxs1xs2")
(coind "EqPxs1xs2")
(assume "xs^3" "xs^4" "EqPxs3xs4")
(elim "EqPxs3xs4")
;; 5,6
(intro 0)
(split)
(use "InitEqD")
(use "InitEqD")
;; 6
(assume "x^5" "x^6" "Px5x6" "xs^5" "xs^6" "EqPxs5xs6" "Disj")
(elim "Disj")
;; 11,12
(drop "Disj")
(assume "NilHyp")
(intro 1)
(intro 0 (pt "x^5"))
(intro 0 (pt "x^6"))
(split)
(use "Px5x6")
(intro 0 (pt "xs^5"))
(intro 0 (pt "xs^6"))
(split)
(intro 1)
(use "EqPxs5xs6")
(split)
(use "InitEqD")
(use "InitEqD")
;; 12
(drop "Disj")
(assume "ExHyp")
(by-assume "ExHyp" "x^7" "x7Prop")
(by-assume "x7Prop" "x^8" "x7x8Prop")
(inst-with-to "x7x8Prop" 'left "Px7x8")
(inst-with-to "x7x8Prop" 'right "ExHyp78")
(drop "x7x8Prop")
(intro 1)
(by-assume "ExHyp78" "xs^7" "xs7Prop")
(by-assume "xs7Prop" "xs^8" "xs7xs8Prop")
(intro 0 (pt "x^5"))
(intro 0 (pt "x^6"))
(split)
(use "Px5x6")
(intro 0 (pt "xs^5"))
(intro 0 (pt "xs^6"))
(split)
(intro 1)
(use "EqPxs5xs6")
(split)
(use "InitEqD")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "NEqPListNcToCoNEqPNc")

;; EqPListToCoEqP
(set-goal "allnc xs^1,xs^2(EqPList xs^1 xs^2 -> CoEqPList xs^1 xs^2)")
(assume "xs^1" "xs^2" "EqPxs1xs2")
(coind "EqPxs1xs2")
(assume "xs^3" "xs^4" "EqPxs3xs4")
(elim "EqPxs3xs4")
;; 5,6
(intro 0)
(split)
(use "InitEqD")
(use "InitEqD")
;; 6
(assume "x^5" "x^6" "Px5x6" "xs^5" "xs^6" "EqPxs5xs6" "Disj")
(elim "Disj")
;; 11,12
(drop "Disj")
(assume "NilHyp")
(intro 1)
(intro 0 (pt "x^5"))
(intro 0 (pt "x^6"))
(split)
(use "Px5x6")
(intro 0 (pt "xs^5"))
(intro 0 (pt "xs^6"))
(split)
(intro 1)
(use "EqPxs5xs6")
(split)
(use "InitEqD")
(use "InitEqD")
;; 12
(drop "Disj")
(assume "ExHyp")
(by-assume "ExHyp" "x^7" "x7Prop")
(by-assume "x7Prop" "x^8" "x7x8Prop")
(inst-with-to "x7x8Prop" 'left "Px7x8")
(inst-with-to "x7x8Prop" 'right "ExHyp78")
(drop "x7x8Prop")
(intro 1)
(by-assume "ExHyp78" "xs^7" "xs7Prop")
(by-assume "xs7Prop" "xs^8" "xs7xs8Prop")
(intro 0 (pt "x^5"))
(intro 0 (pt "x^6"))
(split)
(use "Px5x6")
(intro 0 (pt "xs^5"))
(intro 0 (pt "xs^6"))
(split)
(intro 1)
(use "EqPxs5xs6")
(split)
(use "InitEqD")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "EqPListToCoEqP")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [xs]
;;  (CoRec list alpha=>list alpha)xs
;;  ([xs0]
;;    (Rec list alpha=>uysum(alpha yprod(list alpha ysum list alpha)))xs0
;;    (DummyL alpha yprod(list alpha ysum list alpha))
;;    ([x,xs1,(uysum(alpha yprod(list alpha ysum list alpha)))]
;;      Inr(x pair(InR (list alpha) (list alpha))xs1)))

;; ANEqPListToCoANEqP
(set-goal "allnc xs^1,xs^2(ANEqPList xs^1 xs^2 -> CoANEqPList xs^1 xs^2)")
(assume "xs^1" "xs^2" "ANEqPxs1xs2")
(coind "ANEqPxs1xs2")
(assume "xs^3" "xs^4" "ANEqPxs3xs4")
(elim "ANEqPxs3xs4")
;; 5,6
(intro 0)
(split)
(use "InitEqD")
(use "InitEqD")
;; 6
(assume "x^5" "x^6" "Px5x6" "xs^5" "xs^6" "ANEqPxs5xs6" "Disj")
(elim "Disj")
;; 11,12
(drop "Disj")
(assume "NilHyp")
(intro 1)
(intro 0 (pt "x^5"))
(intro 0 (pt "x^6"))
(split)
(use "Px5x6")
(intro 0 (pt "xs^5"))
(intro 0 (pt "xs^6"))
(split)
(intro 1)
(use "ANEqPxs5xs6")
(split)
(use "InitEqD")
(use "InitEqD")
;; 12
(drop "Disj")
(assume "ExHyp")
(by-assume "ExHyp" "x^7" "x7Prop")
(by-assume "x7Prop" "x^8" "x7x8Prop")
(inst-with-to "x7x8Prop" 'left "Px7x8")
(inst-with-to "x7x8Prop" 'right "ExHyp78")
(drop "x7x8Prop")
(intro 1)
(by-assume "ExHyp78" "xs^7" "xs7Prop")
(by-assume "xs7Prop" "xs^8" "xs7xs8Prop")
(intro 0 (pt "x^5"))
(intro 0 (pt "x^6"))
(split)
(use "Px5x6")
(intro 0 (pt "xs^5"))
(intro 0 (pt "xs^6"))
(split)
(intro 1)
(use "ANEqPxs5xs6")
(split)
(use "InitEqD")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "ANEqPListToCoANEqP")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n]
;;  (CoRec nat=>nat)n
;;  ([n0]
;;    (Rec nat=>uysum(nat ysum nat))n0(DummyL nat ysum nat)
;;    ([n1,(uysum(nat ysum nat))]Inr((InR nat nat)n1)))

;; SEqPListToCoSEqP
(set-goal "allnc xs^1,xs^2(SEqPList xs^1 xs^2 -> CoSEqPList xs^1 xs^2)")
(assume "xs^1" "xs^2" "SEqPxs1xs2")
(coind "SEqPxs1xs2")
(assume "xs^3" "xs^4" "SEqPxs3xs4")
(elim "SEqPxs3xs4")
;; 5,6
(intro 0)
(split)
(use "InitEqD")
(use "InitEqD")
;; 6
(assume "x^5" "x^6" "xs^5" "xs^6" "SEqPxs5xs6" "Disj")
(elim "Disj")
;; 11,12
(drop "Disj")
(assume "NilHyp")
(intro 1)
(intro 0 (pt "x^5"))
(intro 0 (pt "x^6"))
(intro 0 (pt "xs^5"))
(intro 0 (pt "xs^6"))
(split)
(intro 1)
(use "SEqPxs5xs6")
(split)
(use "InitEqD")
(use "InitEqD")
;; 12
(drop "Disj")
(assume "ExHyp")
(by-assume "ExHyp" "x^7" "x7Prop")
(by-assume "x7Prop" "x^8" "x7x8Prop")
(by-assume "x7x8Prop" "xs^7" "x7x8xs7Prop")
(by-assume "x7x8xs7Prop" "xs^8" "x7x8xs7xs8Prop")
(intro 1)
(intro 0 (pt "x^5"))
(intro 0 (pt "x^6"))
(intro 0 (pt "xs^5"))
(intro 0 (pt "xs^6"))
(split)
(intro 1)
(use "SEqPxs5xs6")
(split)
(use "InitEqD")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "SEqPListToCoSEqP")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n]
;;  (CoRec nat=>nat)n
;;  ([n0]
;;    (Rec nat=>uysum(nat ysum nat))n0(DummyL nat ysum nat)
;;    ([n1,(uysum(nat ysum nat))]Inr((InR nat nat)n1)))

;; EqPListNcToCoEqPNc
(set-goal "allnc xs^1,xs^2(EqPListNc xs^1 xs^2 -> CoEqPListNc xs^1 xs^2)")
(assume "xs^1" "xs^2" "EqPxs1xs2")
(coind "EqPxs1xs2")
(assume "xs^3" "xs^4" "EqPxs3xs4")
(elim "EqPxs3xs4")
;; 5,6
(intro 0)
(split)
(use "InitEqD")
(use "InitEqD")
;; 6
(assume "x^5" "x^6" "EqPx5x6" "xs^5" "xs^6" "EqPxs5xs6" "Disj")
(elim "Disj")
;; 11,12
(drop "Disj")
(assume "NilHyp")
(intro 1)
(intro 0 (pt "x^5"))
(intro 0 (pt "x^6"))
(split)
(use "EqPx5x6")
(intro 0 (pt "xs^5"))
(intro 0 (pt "xs^6"))
(split)
(intro 1)
(use "EqPxs5xs6")
(split)
(use "InitEqD")
(use "InitEqD")
;; 12
(drop "Disj")
(assume "ExHyp")
(by-assume "ExHyp" "x^7" "x7Prop")
(by-assume "x7Prop" "x^8" "x7x8Prop")
(inst-with-to "x7x8Prop" 'left "EqPx7x8")
(inst-with-to "x7x8Prop" 'right "ExHyp1")
(drop "x7x8Prop")
(by-assume "ExHyp1" "xs^7" "x7x8xs7Prop")
(by-assume "x7x8xs7Prop" "xs^8" "x7x8xs7xs8Prop")
(intro 1)
(intro 0 (pt "x^5"))
(intro 0 (pt "x^6"))
(split)
(use "EqPx5x6")
(intro 0 (pt "xs^5"))
(intro 0 (pt "xs^6"))
(split)
(intro 1)
(use "EqPxs5xs6")
(split)
(use "InitEqD")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "EqPListNcToCoEqPNc")

;; SEqPListNcToCoSEqPNc
(set-goal "allnc xs^1,xs^2(SEqPListNc xs^1 xs^2 -> CoSEqPListNc xs^1 xs^2)")
(assume "xs^1" "xs^2" "SEqPxs1xs2")
(coind "SEqPxs1xs2")
(assume "xs^3" "xs^4" "SEqPxs3xs4")
(elim "SEqPxs3xs4")
;; 5,6
(intro 0)
(split)
(use "InitEqD")
(use "InitEqD")
;; 6
(assume "x^5" "x^6" "xs^5" "xs^6" "SEqPxs5xs6" "Disj")
(elim "Disj")
;; 11,12
(drop "Disj")
(assume "NilHyp")
(intro 1)
(intro 0 (pt "x^5"))
(intro 0 (pt "x^6"))
(intro 0 (pt "xs^5"))
(intro 0 (pt "xs^6"))
(split)
(intro 1)
(use "SEqPxs5xs6")
(split)
(use "InitEqD")
(use "InitEqD")
;; 12
(drop "Disj")
(assume "ExHyp")
(by-assume "ExHyp" "x^7" "x7Prop")
(by-assume "x7Prop" "x^8" "x7x8Prop")
(by-assume "x7x8Prop" "xs^7" "x7x8xs7Prop")
(by-assume "x7x8xs7Prop" "xs^8" "x7x8xs7xs8Prop")
(intro 1)
(intro 0 (pt "x^5"))
(intro 0 (pt "x^6"))
(intro 0 (pt "xs^5"))
(intro 0 (pt "xs^6"))
(split)
(intro 1)
(use "SEqPxs5xs6")
(split)
(use "InitEqD")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "SEqPListNcToCoSEqPNc")

;; For each dual of the 8 idpcs in 1-2-1-1 we have an ex-falso property

;; EfCoREqPList
;; EfCoNEqPList
;; EfCoNEqPListNc
;; EfCoEqPList
;; EfCoANEqPList
;; EfCoSEqPList
;; EfCoEqPListNc
;; EfCoSEqPListNc

(display-idpc "CoREqPList")

;; EfCoREqPList
(set-goal "allnc xs^1,xs^2(F ->
 (CoREqPList (cterm (x^1,x^2) (Pvar alpha alpha)x^1 x^2))xs^1 xs^2)")
(assume "xs^1" "xs^2" "Absurd")
(use "REqPListToCoREqP")
(use "EfREqPList")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfCoREqPList")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; (cREqPListToCoREqP alpha768)(cEfREqPList alpha768)

(animate "REqPListToCoREqP")
(animate "EfREqPList")

(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; (CoRec list alpha768=>list alpha768)(Nil alpha768)
;; ([(list alpha768)]
;;   [if (list alpha768)
;;     (DummyL alpha768 yprod(list alpha768 ysum list alpha768))
;;     ([alpha768,(list alpha768)_0]
;;      Inr(alpha768 pair(InR (list alpha768) (list alpha768))(list alpha768)_0))])

(pp (nt (undelay-delayed-corec neterm 1)))
;; (Nil alpha768)

(deanimate "REqPListToCoREqP")
(deanimate "EfREqPList")

;; EfCoNEqPList
(set-goal "allnc xs^1,xs^2(F ->
 (CoNEqPList (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xs^1 xs^2)")
(assume "xs^1" "xs^2" "Absurd")
(use "NEqPListToCoNEqP")
(use "EfNEqPList")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfCoNEqPList")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; cNEqPListToCoNEqP cEfNEqPList

(animate "NEqPListToCoNEqP")
(animate "EfNEqPList")

(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; (CoRec nat=>nat)0([n][if n (DummyL nat ysum nat) ([n0]Inr((InR nat nat)n0))])

(pp (nt (undelay-delayed-corec neterm 1)))
;; 0

(deanimate "NEqPListToCoNEqP")
(deanimate "EfNEqPList")

;; EfCoNEqPListNc
(set-goal "allnc xs^1,xs^2(F ->
 (CoNEqPListNc (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xs^1 xs^2)")
(assume "xs^1" "xs^2" "Absurd")
(use "NEqPListNcToCoNEqPNc")
(use "EfNEqPListNc")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfCoNEqPListNc")

;; EfCoEqPList
(set-goal "allnc xs^1,xs^2(F -> CoEqPList xs^1 xs^2)")
(assume "xs^1" "xs^2" "Absurd")
(use "EqPListToCoEqP")
(use "EfEqPList")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfCoEqPList")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; (cEqPListToCoEqP alpha)(cEfEqPList alpha)

(animate "EqPListToCoEqP")
(animate "EfEqPList")

(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; (CoRec list alpha=>list alpha)(Nil alpha)
;; ([xs]
;;   [if xs
;;     (DummyL alpha yprod(list alpha ysum list alpha))
;;     ([x,xs0]Inr(x pair(InR (list alpha) (list alpha))xs0))])

(pp (nt (undelay-delayed-corec neterm 1)))
;; (Nil alpha)

(deanimate "EqPListToCoEqP")
(deanimate "EfEqPList")

;; EfCoANEqPList
(set-goal "allnc xs^1,xs^2(F -> CoANEqPList xs^1 xs^2)")
(assume "xs^1" "xs^2" "Absurd")
(use "ANEqPListToCoANEqP")
(use "EfANEqPList")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfCoANEqPList")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; cANEqPListToCoANEqP cEfANEqPList

(animate "ANEqPListToCoANEqP")
(animate "EfANEqPList")

(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; (CoRec nat=>nat)0([n][if n (DummyL nat ysum nat) ([n0]Inr((InR nat nat)n0))])

(pp (nt (undelay-delayed-corec neterm 1)))
;; 0

(deanimate "ANEqPListToCoANEqP")
(deanimate "EfANEqPList")

;; EfCoSEqPList
(set-goal "allnc xs^1,xs^2(F -> CoSEqPList xs^1 xs^2)")
(assume "xs^1" "xs^2" "Absurd")
(use "SEqPListToCoSEqP")
(use "EfSEqPList")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfCoSEqPList")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; cSEqPListToCoSEqP cEfSEqPList

(animate "SEqPListToCoSEqP")
(animate "EfSEqPList")

(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; (CoRec nat=>nat)0([n][if n (DummyL nat ysum nat) ([n0]Inr((InR nat nat)n0))])

(pp (nt (undelay-delayed-corec neterm 1)))
;; 0

(deanimate "SEqPListToCoSEqP")
(deanimate "EfSEqPList")

;; EfCoEqPListNc
(set-goal "allnc xs^1,xs^2(F -> CoEqPListNc xs^1 xs^2)")
(assume "xs^1" "xs^2" "Absurd")
(use "EqPListNcToCoEqPNc")
(use "EfEqPListNc")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfCoEqPListNc")

;; EfCoSEqPListNc
(set-goal "allnc xs^1,xs^2(F -> CoSEqPListNc xs^1 xs^2)")
(assume "xs^1" "xs^2" "Absurd")
(use "SEqPListNcToCoSEqPNc")
(use "EfSEqPListNc")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfCoSEqPListNc")

;; 2-1-2-2-4.  Relations between CoTotal and CoEqP
;; ===============================================

;; CoREqPListToCoRTotalLeft
;; CoNEqPListToCoNTotalLeft
;; CoNEqPListNcToCoNTotalNcLeft
;; CoEqPListToCoTotalLeft
;; CoANEqPListToCoANTotalLeft
;; CoSEqPListToCoRTotalLeft
;; CoEqPListNcToCoTotalNcLeft
;; CoSEqPListNcToCoSTotalNcLeft

;; and similar for Right.  Moreover we have reflexivity theorems.

;; CoREqPListRefl
;; CoNEqPListRefl
;; CoNqPListReflNc
;; CoEqPListRefl
;; CoANEqPListRefl
;; CoSEqPListRefl
;; CoEqPListNcRefl
;; CoSEqPListNcRefl

;; CoREqPListToCoRTotalLeft
(set-goal "allnc x^1,x^2((Pvar alpha alpha)x^1 x^2 -> (Pvar alpha)x^1) ->
 allnc xs^1,xs^2(
 (CoREqPList (cterm (x^1,x^2) (Pvar alpha alpha)x^1 x^2)) xs^1 xs^2 ->
 (CoRTotalList (cterm (x^) (Pvar alpha)x^))xs^1)")
(assume "THyp" "xs^1" "xs^2" "xs1~xs2")
(use (imp-formulas-to-coind-proof
      (pf "exr xs^3(
            CoREqPList (cterm (x^1,x^2) (Pvar alpha alpha)x^1 x^2))xs^1 xs^3 ->
           (CoRTotalList (cterm (x^) (Pvar alpha)x^))xs^1")))
;; 3,4
(assume "xs^3" "ExHyp3")
(by-assume "ExHyp3" "xs^4" "xs3~xs4")
(inst-with-to "CoREqPListClause" (pt "xs^3") (pt "xs^4") "xs3~xs4" "Inst")
(elim "Inst")
;; 11,12
(drop "Inst")
(assume "Conj")
(intro 0)
(use "Conj")
;; 12
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^5" "x5Prop")
(by-assume "x5Prop" "x^6" "x5x6Prop")
(inst-with-to "x5x6Prop" 'left "EqPx5x6")
(inst-with-to "x5x6Prop" 'right "ExHypxs")
(drop "x5x6Prop")
(by-assume "ExHypxs" "xs^5" "xs5Prop")
(by-assume "xs5Prop" "xs^6" "xs5xs6Prop")
(intro 1)
(intro 0 (pt "x^5"))
(split)
(use "THyp" (pt "x^6"))
(use "EqPx5x6")
(intro 0 (pt "xs^5"))
(split)
(intro 1)
(intro 0 (pt "xs^6"))
(use "xs5xs6Prop")
(use "xs5xs6Prop")
;; 4
(intro 0 (pt "xs^2"))
(use "xs1~xs2")
;; Proof finished.
;; (cdp)
(save "CoREqPListToCoRTotalLeft")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [(alpha768=>gamma),(list alpha768)]
;;  (CoRec list alpha768=>list gamma)(list alpha768)
;;  ([(list alpha768)_0]
;;    [if (DesYprod(list alpha768)_0)
;;      (DummyL gamma yprod(list gamma ysum list alpha768))
;;      ([(alpha768 yprod list alpha768)]
;;       Inr((alpha768=>gamma)clft(alpha768 yprod list alpha768)pair
;;           (InR (list alpha768) (list gamma))
;;           crht(alpha768 yprod list alpha768)))])

;; CoNEqPListToCoNTotalLeft
(set-goal "allnc x^1,x^2((Pvar alpha alpha)^ x^1 x^2 -> (Pvar alpha)^ x^1) ->
 allnc xs^1,xs^2(
 (CoNEqPList (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2)) xs^1 xs^2 ->
 (CoNTotalList (cterm (x^) (Pvar alpha)^ x^))xs^1)")
(assume "THyp" "xs^1" "xs^2" "xs1~xs2")
(use (imp-formulas-to-coind-proof
      (pf "exr xs^3(
           CoNEqPList (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xs^1 xs^3 ->
           (CoNTotalList (cterm (x^) (Pvar alpha)^ x^))xs^1")))
;; 3,4
(assume "xs^3" "ExHyp3")
(by-assume "ExHyp3" "xs^4" "xs3~xs4")
(inst-with-to "CoNEqPListClause" (pt "xs^3") (pt "xs^4") "xs3~xs4" "Inst")
(elim "Inst")
;; 11,12
(drop "Inst")
(assume "Conj")
(intro 0)
(use "Conj")
;; 12
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^5" "x5Prop")
(by-assume "x5Prop" "x^6" "x5x6Prop")
(inst-with-to "x5x6Prop" 'left "EqPx5x6")
(inst-with-to "x5x6Prop" 'right "ExHypxs")
(drop "x5x6Prop")
(by-assume "ExHypxs" "xs^5" "xs5Prop")
(by-assume "xs5Prop" "xs^6" "xs5xs6Prop")
(intro 1)
(intro 0 (pt "x^5"))
(split)
(use "THyp" (pt "x^6"))
(use "EqPx5x6")
(intro 0 (pt "xs^5"))
(split)
(intro 1)
(intro 0 (pt "xs^6"))
(use "xs5xs6Prop")
(use "xs5xs6Prop")
;; 4
(intro 0 (pt "xs^2"))
(use "xs1~xs2")
;; Proof finished.
;; (cdp)
(save "CoNEqPListToCoNTotalLeft")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n]
;;  (CoRec nat=>nat)n
;;  ([n0][if (Des n0) (DummyL nat ysum nat) ([n1]Inr((InR nat nat)n1))])

;; CoNEqPListNcToCoNTotalNcLeft
(set-goal "allnc x^1,x^2((Pvar alpha alpha)^ x^1 x^2 -> (Pvar alpha)^ x^1) ->
 allnc xs^1,xs^2(
 (CoNEqPListNc (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2)) xs^1 xs^2 ->
 (CoNTotalListNc (cterm (x^) (Pvar alpha)^ x^))xs^1)")
(assume "THyp" "xs^1" "xs^2" "xs1~xs2")
(use (imp-formulas-to-coind-proof
      (pf "exr xs^3(
           CoNEqPList (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xs^1 xs^3 ->
           (CoNTotalList (cterm (x^) (Pvar alpha)^ x^))xs^1")))
;; 3,4
(assume "xs^3" "ExHyp3")
(by-assume "ExHyp3" "xs^4" "xs3~xs4")
(inst-with-to "CoNEqPListClause" (pt "xs^3") (pt "xs^4") "xs3~xs4" "Inst")
(elim "Inst")
;; 11,12
(drop "Inst")
(assume "Conj")
(intro 0)
(use "Conj")
;; 12
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^5" "x5Prop")
(by-assume "x5Prop" "x^6" "x5x6Prop")
(inst-with-to "x5x6Prop" 'left "EqPx5x6")
(inst-with-to "x5x6Prop" 'right "ExHypxs")
(drop "x5x6Prop")
(by-assume "ExHypxs" "xs^5" "xs5Prop")
(by-assume "xs5Prop" "xs^6" "xs5xs6Prop")
(intro 1)
(intro 0 (pt "x^5"))
(split)
(use "THyp" (pt "x^6"))
(use "EqPx5x6")
(intro 0 (pt "xs^5"))
(split)
(intro 1)
(intro 0 (pt "xs^6"))
(use "xs5xs6Prop")
(use "xs5xs6Prop")
;; 4
(intro 0 (pt "xs^2"))
(use "xs1~xs2")
;; Proof finished.
;; (cdp)
(save "CoNEqPListNcToCoNTotalNcLeft")

;; CoEqPListToCoTotalLeft
(set-goal "allnc x^1,x^2(EqP x^1 x^2 -> Total x^1) ->
 allnc xs^1,xs^2(CoEqPList xs^1 xs^2 -> CoTotalList xs^1)")
(assume "THyp" "xs^1" "xs^2" "xs1~xs2")
(use (imp-formulas-to-coind-proof
      (pf "exr xs^3 CoEqPList xs^1 xs^3 -> CoTotalList xs^1")))
;; 3,4
(assume "xs^3" "ExHyp3")
(by-assume "ExHyp3" "xs^4" "xs3~xs4")
(inst-with-to "CoEqPListClause" (pt "xs^3") (pt "xs^4") "xs3~xs4" "Inst")
(elim "Inst")
;; 11,12
(drop "Inst")
(assume "Conj")
(intro 0)
(use "Conj")
;; 12
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^5" "x5Prop")
(by-assume "x5Prop" "x^6" "x5x6Prop")
(inst-with-to "x5x6Prop" 'left  "EqPx5x6")
(inst-with-to "x5x6Prop" 'right  "ExHypxs")
(drop "x5x6Prop")
(by-assume "ExHypxs" "xs^5" "xs5Prop")
(by-assume "xs5Prop" "xs^6" "xs5xs6Prop")
(intro 1)
(intro 0 (pt "x^5"))
(split)
(use "THyp" (pt "x^6"))
(use "EqPx5x6")
(intro 0 (pt "xs^5"))
(split)
(intro 1)
(intro 0 (pt "xs^6"))
(use "xs5xs6Prop")
(use "xs5xs6Prop")
;; 4
(intro 0 (pt "xs^2"))
(use "xs1~xs2")
;; Proof finished.
;; (cdp)
(save "CoEqPListToCoTotalLeft")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [(alpha=>alpha),xs]
;;  (CoRec list alpha=>list alpha)xs
;;  ([xs0]
;;    [if (DesYprod xs0)
;;      (DummyL alpha yprod(list alpha ysum list alpha))
;;      ([(alpha yprod list alpha)]
;;       Inr((alpha=>alpha)clft(alpha yprod list alpha)pair
;;           (InR (list alpha) (list alpha))crht(alpha yprod list alpha)))])

;; CoANEqPListToCoANTotalLeft
(set-goal "allnc x^1,x^2(EqP x^1 x^2 -> Total x^1) ->
 allnc xs^1,xs^2(CoANEqPList xs^1 xs^2 -> CoANTotalList xs^1)")
(assume "THyp" "xs^1" "xs^2" "xs1~xs2")
(use (imp-formulas-to-coind-proof
      (pf "exr xs^3 CoANEqPList xs^1 xs^3 -> CoANTotalList xs^1")))
;; 3,4
(assume "xs^3" "ExHyp3")
(by-assume "ExHyp3" "xs^4" "xs3~xs4")
(inst-with-to "CoANEqPListClause" (pt "xs^3") (pt "xs^4") "xs3~xs4" "Inst")
(elim "Inst")
;; 11,12
(drop "Inst")
(assume "Conj")
(intro 0)
(use "Conj")
;; 12
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^5" "x5Prop")
(by-assume "x5Prop" "x^6" "x5x6Prop")
(inst-with-to "x5x6Prop" 'left  "EqPx5x6")
(inst-with-to "x5x6Prop" 'right  "ExHypxs")
(drop "x5x6Prop")
(by-assume "ExHypxs" "xs^5" "xs5Prop")
(by-assume "xs5Prop" "xs^6" "xs5xs6Prop")
(intro 1)
(intro 0 (pt "x^5"))
(split)
(use "THyp" (pt "x^6"))
(use "EqPx5x6")
(intro 0 (pt "xs^5"))
(split)
(intro 1)
(intro 0 (pt "xs^6"))
(use "xs5xs6Prop")
(use "xs5xs6Prop")
;; 4
(intro 0 (pt "xs^2"))
(use "xs1~xs2")
;; Proof finished.
;; (cdp)
(save "CoANEqPListToCoANTotalLeft")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [(alpha=>alpha),n]
;;  (CoRec nat=>nat)n
;;  ([n0][if (Des n0) (DummyL nat ysum nat) ([n1]Inr((InR nat nat)n1))])

;; CoSEqPListToCoRTotalLeft
(set-goal "allnc x^1,x^2(EqP x^1 x^2 -> Total x^1) ->
 allnc xs^1,xs^2(CoSEqPList xs^1 xs^2 -> CoSTotalList xs^1)")
(assume "THyp" "xs^1" "xs^2" "xs1~xs2")
(use (imp-formulas-to-coind-proof
      (pf "exr xs^3 CoSEqPList xs^1 xs^3 -> CoSTotalList xs^1")))
;; 3,4
(assume "xs^3" "ExHyp3")
(by-assume "ExHyp3" "xs^4" "xs3~xs4")
(inst-with-to "CoSEqPListClause" (pt "xs^3") (pt "xs^4") "xs3~xs4" "Inst")
(elim "Inst")
;; 11,12
(drop "Inst")
(assume "Conj")
(intro 0)
(use "Conj")
;; 12
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^5" "x5Prop")
(by-assume "x5Prop" "x^6" "x5x6Prop")
(by-assume "x5x6Prop" "xs^5" "x5x6xs5Prop")
(by-assume "x5x6xs5Prop" "xs^6" "x5x6xs5xs6Prop")
(intro 1)
(intro 0 (pt "x^5"))
(intro 0 (pt "xs^5"))
(split)
(intro 1)
(intro 0 (pt "xs^6"))
(use "x5x6xs5xs6Prop")
(use "x5x6xs5xs6Prop")
;; 4
(intro 0 (pt "xs^2"))
(use "xs1~xs2")
;; Proof finished.
;; (cdp)
(save "CoSEqPListToCoRTotalLeft")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [(alpha=>alpha),n]
;;  (CoRec nat=>nat)n
;;  ([n0][if (Des n0) (DummyL nat ysum nat) ([n1]Inr((InR nat nat)n1))])

;; CoEqPListNcToCoTotalNcLeft
(set-goal "allnc x^1,x^2(EqPNc x^1 x^2 -> TotalNc x^1) ->
 allnc xs^1,xs^2(CoEqPListNc xs^1 xs^2 -> CoTotalListNc xs^1)")
(assume "THyp" "xs^1" "xs^2" "xs1~xs2")
(use (imp-formulas-to-coind-proof
      (pf "exr xs^3 CoEqPListNc xs^1 xs^3 -> CoTotalListNc xs^1")))
;; 3,4
(assume "xs^3" "ExHyp3")
(by-assume "ExHyp3" "xs^4" "xs3~xs4")
(inst-with-to "CoEqPListNcClause" (pt "xs^3") (pt "xs^4") "xs3~xs4" "Inst")
(elim "Inst")
;; 11,12
(drop "Inst")
(assume "Conj")
(intro 0)
(use "Conj")
;; 12
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^5" "x5Prop")
(by-assume "x5Prop" "x^6" "x5x6Prop")
(inst-with-to "x5x6Prop" 'left  "EqPx5x6")
(inst-with-to "x5x6Prop" 'right  "ExHypxs")
(drop "x5x6Prop")
(by-assume "ExHypxs" "xs^5" "xs5Prop")
(by-assume "xs5Prop" "xs^6" "xs5xs6Prop")
(intro 1)
(intro 0 (pt "x^5"))
(split)
(use "THyp" (pt "x^6"))
(use "EqPx5x6")
(intro 0 (pt "xs^5"))
(split)
(intro 1)
(intro 0 (pt "xs^6"))
(use "xs5xs6Prop")
(use "xs5xs6Prop")
;; 4
(intro 0 (pt "xs^2"))
(use "xs1~xs2")
;; Proof finished.
;; (cdp)
(save "CoEqPListNcToCoTotalNcLeft")

;; CoSEqPListNcToCoSTotalNcLeft
(set-goal "allnc x^1,x^2(EqPNc x^1 x^2 -> TotalNc x^1) ->
 allnc xs^1,xs^2(CoSEqPListNc xs^1 xs^2 -> CoSTotalListNc xs^1)")
(assume "THyp" "xs^1" "xs^2" "xs1~xs2")
(use (imp-formulas-to-coind-proof
      (pf "exr xs^3 CoSEqPListNc xs^1 xs^3 -> CoSTotalListNc xs^1")))
;; 3,4
(assume "xs^3" "ExHyp3")
(by-assume "ExHyp3" "xs^4" "xs3~xs4")
(inst-with-to "CoSEqPListNcClause" (pt "xs^3") (pt "xs^4") "xs3~xs4" "Inst")
(elim "Inst")
;; 11,12
(drop "Inst")
(assume "Conj")
(intro 0)
(use "Conj")
;; 12
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^5" "x5Prop")
(by-assume "x5Prop" "x^6" "x5x6Prop")
(by-assume "x5x6Prop" "xs^5" "x5x6xs5Prop")
(by-assume "x5x6xs5Prop" "xs^6" "x5x6xs5xs6Prop")
(intro 1)
(intro 0 (pt "x^5"))
(intro 0 (pt "xs^5"))
(split)
(intro 1)
(intro 0 (pt "xs^6"))
(use "x5x6xs5xs6Prop")
(use "x5x6xs5xs6Prop")
;; 4
(intro 0 (pt "xs^2"))
(use "xs1~xs2")
;; Proof finished.
;; (cdp)
(save "CoSEqPListNcToCoSTotalNcLeft")

;; Now the same for Right.

;; CoREqPListToCoRTotalRight
(set-goal "allnc x^1,x^2((Pvar alpha alpha)x^1 x^2 -> (Pvar alpha)x^2) ->
 allnc xs^1,xs^2(
 (CoREqPList (cterm (x^1,x^2) (Pvar alpha alpha)x^1 x^2)) xs^1 xs^2 ->
 (CoRTotalList (cterm (x^) (Pvar alpha)x^))xs^2)")
(assume "THyp" "xs^1" "xs^2" "xs1~xs2")
(use (imp-formulas-to-coind-proof
      (pf "exr xs^3(
            CoREqPList (cterm (x^1,x^2) (Pvar alpha alpha)x^1 x^2))xs^3 xs^2 ->
           (CoRTotalList (cterm (x^) (Pvar alpha)x^))xs^2")))
;; 3,4
(assume "xs^3" "ExHyp3")
(by-assume "ExHyp3" "xs^4" "xs4~xs3")
(inst-with-to "CoREqPListClause" (pt "xs^4") (pt "xs^3") "xs4~xs3" "Inst")
(elim "Inst")
;; 11,12
(drop "Inst")
(assume "Conj")
(intro 0)
(use "Conj")
;; 12
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^5" "x5Prop")
(by-assume "x5Prop" "x^6" "x5x6Prop")
(inst-with-to "x5x6Prop" 'left "EqPx5x6")
(inst-with-to "x5x6Prop" 'right "ExHypxs")
(drop "x5x6Prop")
(by-assume "ExHypxs" "xs^5" "xs5Prop")
(by-assume "xs5Prop" "xs^6" "xs5xs6Prop")
(intro 1)
(intro 0 (pt "x^6"))
(split)
(use "THyp" (pt "x^5"))
(use "EqPx5x6")
(intro 0 (pt "xs^6"))
(split)
(intro 1)
(intro 0 (pt "xs^5"))
(use "xs5xs6Prop")
(use "xs5xs6Prop")
;; 4
(intro 0 (pt "xs^1"))
(use "xs1~xs2")
;; Proof finished.
;; (cdp)
(save "CoREqPListToCoRTotalRight")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [(alpha768=>gamma),(list alpha768)]
;;  (CoRec list alpha768=>list gamma)(list alpha768)
;;  ([(list alpha768)_0]
;;    [if (DesYprod(list alpha768)_0)
;;      (DummyL gamma yprod(list gamma ysum list alpha768))
;;      ([(alpha768 yprod list alpha768)]
;;       Inr((alpha768=>gamma)clft(alpha768 yprod list alpha768)pair
;;           (InR (list alpha768) (list gamma))
;;           crht(alpha768 yprod list alpha768)))])

;; CoNEqPListToCoNTotalRight
(set-goal "allnc x^1,x^2((Pvar alpha alpha)^ x^1 x^2 -> (Pvar alpha)^ x^2) ->
 allnc xs^1,xs^2(
 (CoNEqPList (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2)) xs^1 xs^2 ->
 (CoNTotalList (cterm (x^) (Pvar alpha)^ x^))xs^2)")
(assume "THyp" "xs^1" "xs^2" "xs1~xs2")
(use (imp-formulas-to-coind-proof
      (pf "exr xs^3(
           CoNEqPList (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xs^3 xs^2 ->
           (CoNTotalList (cterm (x^) (Pvar alpha)^ x^))xs^2")))
;; 3,4
(assume "xs^3" "ExHyp3")
(by-assume "ExHyp3" "xs^4" "xs4~xs3")
(inst-with-to "CoNEqPListClause" (pt "xs^4") (pt "xs^3") "xs4~xs3" "Inst")
(elim "Inst")
;; 11,12
(drop "Inst")
(assume "Conj")
(intro 0)
(use "Conj")
;; 12
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^5" "x5Prop")
(by-assume "x5Prop" "x^6" "x5x6Prop")
(inst-with-to "x5x6Prop" 'left "EqPx5x6")
(inst-with-to "x5x6Prop" 'right "ExHypxs")
(drop "x5x6Prop")
(by-assume "ExHypxs" "xs^5" "xs5Prop")
(by-assume "xs5Prop" "xs^6" "xs5xs6Prop")
(intro 1)
(intro 0 (pt "x^6"))
(split)
(use "THyp" (pt "x^5"))
(use "EqPx5x6")
(intro 0 (pt "xs^6"))
(split)
(intro 1)
(intro 0 (pt "xs^5"))
(use "xs5xs6Prop")
(use "xs5xs6Prop")
;; 4
(intro 0 (pt "xs^1"))
(use "xs1~xs2")
;; Proof finished.
;; (cdp)
(save "CoNEqPListToCoNTotalRight")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n]
;;  (CoRec nat=>nat)n
;;  ([n0][if (Des n0) (DummyL nat ysum nat) ([n1]Inr((InR nat nat)n1))])

;; CoNEqPListNcToCoNTotalNcRight
(set-goal "allnc x^1,x^2((Pvar alpha alpha)^ x^1 x^2 -> (Pvar alpha)^ x^2) ->
 allnc xs^1,xs^2(
 (CoNEqPListNc (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2)) xs^1 xs^2 ->
 (CoNTotalListNc (cterm (x^) (Pvar alpha)^ x^))xs^2)")
(assume "THyp" "xs^1" "xs^2" "xs1~xs2")
(use (imp-formulas-to-coind-proof
      (pf "exr xs^3(
           CoNEqPList (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xs^3 xs^2 ->
           (CoNTotalList (cterm (x^) (Pvar alpha)^ x^))xs^2")))
;; 3,4
(assume "xs^3" "ExHyp3")
(by-assume "ExHyp3" "xs^4" "xs4~xs3")
(inst-with-to "CoNEqPListClause" (pt "xs^4") (pt "xs^3") "xs4~xs3" "Inst")
(elim "Inst")
;; 11,12
(drop "Inst")
(assume "Conj")
(intro 0)
(use "Conj")
;; 12
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^5" "x5Prop")
(by-assume "x5Prop" "x^6" "x5x6Prop")
(inst-with-to "x5x6Prop" 'left "EqPx5x6")
(inst-with-to "x5x6Prop" 'right "ExHypxs")
(drop "x5x6Prop")
(by-assume "ExHypxs" "xs^5" "xs5Prop")
(by-assume "xs5Prop" "xs^6" "xs5xs6Prop")
(intro 1)
(intro 0 (pt "x^6"))
(split)
(use "THyp" (pt "x^5"))
(use "EqPx5x6")
(intro 0 (pt "xs^6"))
(split)
(intro 1)
(intro 0 (pt "xs^5"))
(use "xs5xs6Prop")
(use "xs5xs6Prop")
;; 4
(intro 0 (pt "xs^1"))
(use "xs1~xs2")
;; Proof finished.
;; (cdp)
(save "CoNEqPListNcToCoNTotalNcRight")

;; CoEqPListToCoTotalRight
(set-goal "allnc x^1,x^2(EqP x^1 x^2 -> Total x^2) ->
 allnc xs^1,xs^2(CoEqPList xs^1 xs^2 -> CoTotalList xs^2)")
(assume "THyp" "xs^1" "xs^2" "xs1~xs2")
(use (imp-formulas-to-coind-proof
      (pf "exr xs^3 CoEqPList xs^3 xs^2 -> CoTotalList xs^2")))
;; 3,4
(assume "xs^3" "ExHyp3")
(by-assume "ExHyp3" "xs^4" "xs4~xs3")
(inst-with-to "CoEqPListClause" (pt "xs^4") (pt "xs^3") "xs4~xs3" "Inst")
(elim "Inst")
;; 11,12
(drop "Inst")
(assume "Conj")
(intro 0)
(use "Conj")
;; 12
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^5" "x5Prop")
(by-assume "x5Prop" "x^6" "x5x6Prop")
(inst-with-to "x5x6Prop" 'left  "EqPx5x6")
(inst-with-to "x5x6Prop" 'right  "ExHypxs")
(drop "x5x6Prop")
(by-assume "ExHypxs" "xs^5" "xs5Prop")
(by-assume "xs5Prop" "xs^6" "xs5xs6Prop")
(intro 1)
(intro 0 (pt "x^6"))
(split)
(use "THyp" (pt "x^5"))
(use "EqPx5x6")
(intro 0 (pt "xs^6"))
(split)
(intro 1)
(intro 0 (pt "xs^5"))
(use "xs5xs6Prop")
(use "xs5xs6Prop")
;; 4
(intro 0 (pt "xs^1"))
(use "xs1~xs2")
;; Proof finished.
;; (cdp)
(save "CoEqPListToCoTotalRight")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [(alpha=>alpha),xs]
;;  (CoRec list alpha=>list alpha)xs
;;  ([xs0]
;;    [if (DesYprod xs0)
;;      (DummyL alpha yprod(list alpha ysum list alpha))
;;      ([(alpha yprod list alpha)]
;;       Inr((alpha=>alpha)clft(alpha yprod list alpha)pair
;;           (InR (list alpha) (list alpha))crht(alpha yprod list alpha)))])

;; CoANEqPListToCoANTotalRight
(set-goal "allnc x^1,x^2(EqP x^1 x^2 -> Total x^2) ->
 allnc xs^1,xs^2(CoANEqPList xs^1 xs^2 -> CoANTotalList xs^2)")
(assume "THyp" "xs^1" "xs^2" "xs1~xs2")
(use (imp-formulas-to-coind-proof
      (pf "exr xs^3 CoANEqPList xs^3 xs^2 -> CoANTotalList xs^2")))
;; 3,4
(assume "xs^3" "ExHyp3")
(by-assume "ExHyp3" "xs^4" "xs4~xs3")
(inst-with-to "CoANEqPListClause" (pt "xs^4") (pt "xs^3") "xs4~xs3" "Inst")
(elim "Inst")
;; 11,12
(drop "Inst")
(assume "Conj")
(intro 0)
(use "Conj")
;; 12
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^5" "x5Prop")
(by-assume "x5Prop" "x^6" "x5x6Prop")
(inst-with-to "x5x6Prop" 'left  "EqPx5x6")
(inst-with-to "x5x6Prop" 'right  "ExHypxs")
(drop "x5x6Prop")
(by-assume "ExHypxs" "xs^5" "xs5Prop")
(by-assume "xs5Prop" "xs^6" "xs5xs6Prop")
(intro 1)
(intro 0 (pt "x^6"))
(split)
(use "THyp" (pt "x^5"))
(use "EqPx5x6")
(intro 0 (pt "xs^6"))
(split)
(intro 1)
(intro 0 (pt "xs^5"))
(use "xs5xs6Prop")
(use "xs5xs6Prop")
;; 4
(intro 0 (pt "xs^1"))
(use "xs1~xs2")
;; Proof finished.
;; (cdp)
(save "CoANEqPListToCoANTotalRight")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [(alpha=>alpha),n]
;;  (CoRec nat=>nat)n
;;  ([n0][if (Des n0) (DummyL nat ysum nat) ([n1]Inr((InR nat nat)n1))])

;; CoSEqPListToCoRTotalRight
(set-goal "allnc x^1,x^2(EqP x^1 x^2 -> Total x^2) ->
 allnc xs^1,xs^2(CoSEqPList xs^1 xs^2 -> CoSTotalList xs^2)")
(assume "THyp" "xs^1" "xs^2" "xs1~xs2")
(use (imp-formulas-to-coind-proof
      (pf "exr xs^3 CoSEqPList xs^3 xs^2 -> CoSTotalList xs^2")))
;; 3,4
(assume "xs^3" "ExHyp3")
(by-assume "ExHyp3" "xs^4" "xs4~xs3")
(inst-with-to "CoSEqPListClause" (pt "xs^4") (pt "xs^3") "xs4~xs3" "Inst")
(elim "Inst")
;; 11,12
(drop "Inst")
(assume "Conj")
(intro 0)
(use "Conj")
;; 12
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^5" "x5Prop")
(by-assume "x5Prop" "x^6" "x5x6Prop")
(by-assume "x5x6Prop" "xs^5" "x5x6xs5Prop")
(by-assume "x5x6xs5Prop" "xs^6" "x5x6xs5xs6Prop")
(intro 1)
(intro 0 (pt "x^6"))
(intro 0 (pt "xs^6"))
(split)
(intro 1)
(intro 0 (pt "xs^5"))
(use "x5x6xs5xs6Prop")
(use "x5x6xs5xs6Prop")
;; 4
(intro 0 (pt "xs^1"))
(use "xs1~xs2")
;; Proof finished.
;; (cdp)
(save "CoSEqPListToCoRTotalRight")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [(alpha=>alpha),n]
;;  (CoRec nat=>nat)n
;;  ([n0][if (Des n0) (DummyL nat ysum nat) ([n1]Inr((InR nat nat)n1))])

;; CoEqPListNcToCoTotalNcRight
(set-goal "allnc x^1,x^2(EqPNc x^1 x^2 -> TotalNc x^2) ->
 allnc xs^1,xs^2(CoEqPListNc xs^1 xs^2 -> CoTotalListNc xs^2)")
(assume "THyp" "xs^1" "xs^2" "xs1~xs2")
(use (imp-formulas-to-coind-proof
      (pf "exr xs^3 CoEqPListNc xs^3 xs^2 -> CoTotalListNc xs^2")))
;; 3,4
(assume "xs^3" "ExHyp3")
(by-assume "ExHyp3" "xs^4" "xs4~xs3")
(inst-with-to "CoEqPListNcClause" (pt "xs^4") (pt "xs^3") "xs4~xs3" "Inst")
(elim "Inst")
;; 11,12
(drop "Inst")
(assume "Conj")
(intro 0)
(use "Conj")
;; 12
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^5" "x5Prop")
(by-assume "x5Prop" "x^6" "x5x6Prop")
(inst-with-to "x5x6Prop" 'left  "EqPx5x6")
(inst-with-to "x5x6Prop" 'right  "ExHypxs")
(drop "x5x6Prop")
(by-assume "ExHypxs" "xs^5" "xs5Prop")
(by-assume "xs5Prop" "xs^6" "xs5xs6Prop")
(intro 1)
(intro 0 (pt "x^6"))
(split)
(use "THyp" (pt "x^5"))
(use "EqPx5x6")
(intro 0 (pt "xs^6"))
(split)
(intro 1)
(intro 0 (pt "xs^5"))
(use "xs5xs6Prop")
(use "xs5xs6Prop")
;; 4
(intro 0 (pt "xs^1"))
(use "xs1~xs2")
;; Proof finished.
;; (cdp)
(save "CoEqPListNcToCoTotalNcRight")

;; CoSEqPListNcToCoSTotalNcRight
(set-goal "allnc x^1,x^2(EqPNc x^1 x^2 -> TotalNc x^2) ->
 allnc xs^1,xs^2(CoSEqPListNc xs^1 xs^2 -> CoSTotalListNc xs^2)")
(assume "THyp" "xs^1" "xs^2" "xs1~xs2")
(use (imp-formulas-to-coind-proof
      (pf "exr xs^3 CoSEqPListNc xs^3 xs^2 -> CoSTotalListNc xs^2")))
;; 3,4
(assume "xs^3" "ExHyp3")
(by-assume "ExHyp3" "xs^4" "xs4~xs3")
(inst-with-to "CoSEqPListNcClause" (pt "xs^4") (pt "xs^3") "xs4~xs3" "Inst")
(elim "Inst")
;; 11,12
(drop "Inst")
(assume "Conj")
(intro 0)
(use "Conj")
;; 12
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^5" "x5Prop")
(by-assume "x5Prop" "x^6" "x5x6Prop")
(by-assume "x5x6Prop" "xs^5" "x5x6xs5Prop")
(by-assume "x5x6xs5Prop" "xs^6" "x5x6xs5xs6Prop")
(intro 1)
(intro 0 (pt "x^6"))
(intro 0 (pt "xs^6"))
(split)
(intro 1)
(intro 0 (pt "xs^5"))
(use "x5x6xs5xs6Prop")
(use "x5x6xs5xs6Prop")
;; 4
(intro 0 (pt "xs^1"))
(use "xs1~xs2")
;; Proof finished.
;; (cdp)
(save "CoSEqPListNcToCoSTotalNcRight")

;; Now for reflexivity.

;; CoREqPListRefl
(set-goal "allnc x^((Pvar alpha)x^ -> (Pvar alpha alpha)x^ x^) ->
           allnc xs^((CoRTotalList (cterm (x^) (Pvar alpha)x^))xs^ ->
 (CoREqPList (cterm (x^1,x^2) (Pvar alpha alpha)x^1 x^2))xs^ xs^)")
(assume "REqPHyp")
(assert
 "allnc xs^1,xs^2(
 (CoRTotalList (cterm (x^) (Pvar alpha)x^))xs^1 andi xs^1 eqd xs^2 ->
 (CoREqPList (cterm (x^1,x^2) (Pvar alpha alpha)x^1 x^2))xs^1 xs^2)")
(assume "xs^1" "xs^2")
(coind)
(assume "xs^3" "xs^4" "Conj")
(inst-with-to "Conj" 'left "CoTxs3")
(inst-with-to "Conj" 'right "xs3=xs4")
(drop "Conj")
(simp "<-" "xs3=xs4")
(drop "xs3=xs4")
(inst-with-to
 "CoRTotalListClause"
 (make-cterm (pv "x^") (pf "(Pvar alpha)x^"))
 (pt "xs^3") "CoTxs3" "Inst")
(elim "Inst")
;; 17,18
(drop "Inst")
(assume "xs3=Nil")
(intro 0)
(split)
(use "xs3=Nil")
(use "xs3=Nil")
;; 18
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^5" "x5Prop")
(intro 1)
(intro 0 (pt "x^5"))
(intro 0 (pt "x^5"))
(split)
(use "REqPHyp")
(use "x5Prop")
(inst-with-to "x5Prop" 'right "ExHyp6")
(drop "x5Prop")
(by-assume "ExHyp6" "xs^6" "xs6Prop")
(intro 0 (pt "xs^6"))
(intro 0 (pt "xs^6"))
(split)
(intro 1)
(split)
(use "xs6Prop")
(use "InitEqD")
(split)
(use "xs6Prop")
(use "xs6Prop")
;; 3
(assume "Assertion" "xs^" "CoTxs")
(use "Assertion")
(split)
(use "CoTxs")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "CoREqPListRefl")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [(gamma=>alpha768),(list gamma)]
;;  (CoRec list gamma=>list alpha768)(list gamma)
;;  ([(list gamma)_0]
;;    [if (DesYprod(list gamma)_0)
;;      (DummyL alpha768 yprod(list alpha768 ysum list gamma))
;;      ([(gamma yprod list gamma)]
;;       Inr((gamma=>alpha768)clft(gamma yprod list gamma)pair
;;           (InR (list gamma) (list alpha768))crht(gamma yprod list gamma)))])

;; CoNEqPListRefl
(set-goal "allnc x^((Pvar alpha)^ x^ -> (Pvar alpha alpha)^ x^ x^) ->
           allnc xs^((CoNTotalList (cterm (x^) (Pvar alpha)^ x^))xs^ ->
 (CoNEqPList (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xs^ xs^)")
(assume "NEqPHyp")
(assert
 "allnc xs^1,xs^2(
 (CoNTotalList (cterm (x^) (Pvar alpha)^ x^))xs^1 andi xs^1 eqd xs^2 ->
 (CoNEqPList (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xs^1 xs^2)")
(assume "xs^1" "xs^2")
(coind)
(assume "xs^3" "xs^4" "Conj")
(inst-with-to "Conj" 'left "CoTxs3")
(inst-with-to "Conj" 'right "xs3=xs4")
(drop "Conj")
(simp "<-" "xs3=xs4")
(drop "xs3=xs4")
(inst-with-to
 "CoNTotalListClause"
 (make-cterm (pv "x^") (pf "(Pvar alpha)^ x^"))
 (pt "xs^3") "CoTxs3" "Inst")
(elim "Inst")
;; 17,18
(drop "Inst")
(assume "xs3=Nil")
(intro 0)
(split)
(use "xs3=Nil")
(use "xs3=Nil")
;; 18
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^5" "x5Prop")
(intro 1)
(intro 0 (pt "x^5"))
(intro 0 (pt "x^5"))
(split)
(use "NEqPHyp")
(use "x5Prop")
(inst-with-to "x5Prop" 'right "ExHyp6")
(drop "x5Prop")
(by-assume "ExHyp6" "xs^6" "xs6Prop")
(intro 0 (pt "xs^6"))
(intro 0 (pt "xs^6"))
(split)
(intro 1)
(split)
(use "xs6Prop")
(use "InitEqD")
(split)
(use "xs6Prop")
(use "xs6Prop")
;; 3
(assume "Assertion" "xs^" "CoTxs")
(use "Assertion")
(split)
(use "CoTxs")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "CoNEqPListRefl")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n]
;;  (CoRec nat=>nat)n
;;  ([n0][if (Des n0) (DummyL nat ysum nat) ([n1]Inr((InR nat nat)n1))])

;; CoNEqPListReflNc
(set-goal "allnc x^((Pvar alpha)^ x^ -> (Pvar alpha alpha)^ x^ x^) ->
           allnc xs^((CoNTotalListNc (cterm (x^) (Pvar alpha)^ x^))xs^ ->
 (CoNEqPListNc (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xs^ xs^)")
(assume "NEqPHyp")
(assert
 "allnc xs^1,xs^2(
 (CoNTotalListNc (cterm (x^) (Pvar alpha)^ x^))xs^1 andi xs^1 eqd xs^2 ->
 (CoNEqPListNc (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xs^1 xs^2)")
(assume "xs^1" "xs^2")
(coind)
(assume "xs^3" "xs^4" "Conj")
(inst-with-to "Conj" 'left "CoTxs3")
(inst-with-to "Conj" 'right "xs3=xs4")
(drop "Conj")
(simp "<-" "xs3=xs4")
(drop "xs3=xs4")
(inst-with-to
 "CoNTotalListNcClause"
 (make-cterm (pv "x^") (pf "(Pvar alpha)^ x^"))
 (pt "xs^3") "CoTxs3" "Inst")
(elim "Inst")
;; 17,18
(drop "Inst")
(assume "xs3=Nil")
(intro 0)
(split)
(use "xs3=Nil")
(use "xs3=Nil")
;; 18
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^5" "x5Prop")
(intro 1)
(intro 0 (pt "x^5"))
(intro 0 (pt "x^5"))
(split)
(use "NEqPHyp")
(use "x5Prop")
(inst-with-to "x5Prop" 'right "ExHyp6")
(drop "x5Prop")
(by-assume "ExHyp6" "xs^6" "xs6Prop")
(intro 0 (pt "xs^6"))
(intro 0 (pt "xs^6"))
(split)
(intro 1)
(split)
(use "xs6Prop")
(use "InitEqD")
(split)
(use "xs6Prop")
(use "xs6Prop")
;; 3
(assume "Assertion" "xs^" "CoTxs")
(use "Assertion")
(split)
(use "CoTxs")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "CoNEqPListReflNc")

;; CoEqPListRefl
(set-goal "allnc x^(Total x^ -> EqP x^ x^) ->
           allnc xs^(CoTotalList xs^ -> CoEqPList xs^ xs^)")
(assume "EqPHyp")
(assert
 "allnc xs^1,xs^2(CoTotalList xs^1 andi xs^1 eqd xs^2 -> CoEqPList xs^1 xs^2)")
(assume "xs^1" "xs^2")
(coind)
(assume "xs^3" "xs^4" "Conj")
(inst-with-to "Conj" 'left "CoTxs3")
(inst-with-to "Conj" 'right "xs3=xs4")
(drop "Conj")
(simp "<-" "xs3=xs4")
(drop "xs3=xs4")
(inst-with-to "CoTotalListClause" (pt "xs^3") "CoTxs3" "Inst")
(elim "Inst")
;; 16,17
(drop "Inst")
(assume "xs3=Nil")
(intro 0)
(split)
(use "xs3=Nil")
(use "xs3=Nil")
;; 17
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^5" "x5Prop")
(intro 1)
(intro 0 (pt "x^5"))
(intro 0 (pt "x^5"))
(split)
(use "EqPHyp")
(use "x5Prop")
(inst-with-to "x5Prop" 'right "ExHyp6")
(drop "x5Prop")
(by-assume "ExHyp6" "xs^6" "xs6Prop")
(intro 0 (pt "xs^6"))
(intro 0 (pt "xs^6"))
(split)
(intro 1)
(split)
(use "xs6Prop")
(use "InitEqD")
(split)
(use "xs6Prop")
(use "xs6Prop")
;; 3
(assume "Assertion" "xs^" "CoTxs")
(use "Assertion")
(split)
(use "CoTxs")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "CoEqPListRefl")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [(alpha=>alpha),xs]
;;  (CoRec list alpha=>list alpha)xs
;;  ([xs0]
;;    [if (DesYprod xs0)
;;      (DummyL alpha yprod(list alpha ysum list alpha))
;;      ([(alpha yprod list alpha)]
;;       Inr((alpha=>alpha)clft(alpha yprod list alpha)pair
;;           (InR (list alpha) (list alpha))crht(alpha yprod list alpha)))])

;; CoANEqPListRefl
(set-goal "allnc x^(Total x^ -> EqP x^ x^) ->
           allnc xs^(CoANTotalList xs^ -> CoANEqPList xs^ xs^)")
(assume "EqPHyp")
(assert
 "allnc xs^1,xs^2(
 CoANTotalList xs^1 andi xs^1 eqd xs^2 -> CoANEqPList xs^1 xs^2)")
(assume "xs^1" "xs^2")
(coind)
(assume "xs^3" "xs^4" "Conj")
(inst-with-to "Conj" 'left "CoTxs3")
(inst-with-to "Conj" 'right "xs3=xs4")
(drop "Conj")
(simp "<-" "xs3=xs4")
(drop "xs3=xs4")
(inst-with-to "CoANTotalListClause" (pt "xs^3") "CoTxs3" "Inst")
(elim "Inst")
;; 17,18
(drop "Inst")
(assume "xs3=Nil")
(intro 0)
(split)
(use "xs3=Nil")
(use "xs3=Nil")
;; 18
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^5" "x5Prop")
(intro 1)
(intro 0 (pt "x^5"))
(intro 0 (pt "x^5"))
(split)
(use "EqPHyp")
(use "x5Prop")
(inst-with-to "x5Prop" 'right "ExHyp6")
(drop "x5Prop")
(by-assume "ExHyp6" "xs^6" "xs6Prop")
(intro 0 (pt "xs^6"))
(intro 0 (pt "xs^6"))
(split)
(intro 1)
(split)
(use "xs6Prop")
(use "InitEqD")
(split)
(use "xs6Prop")
(use "xs6Prop")
;; 3
(assume "Assertion" "xs^" "CoTxs")
(use "Assertion")
(split)
(use "CoTxs")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "CoANEqPListRefl")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [(alpha=>alpha),n]
;;  (CoRec nat=>nat)n
;;  ([n0][if (Des n0) (DummyL nat ysum nat) ([n1]Inr((InR nat nat)n1))])

;; CoSEqPListRefl
(set-goal "allnc xs^(CoSTotalList xs^ -> CoSEqPList xs^ xs^)")
(assert "allnc xs^1,xs^2(CoSTotalList xs^1 andi xs^1 eqd xs^2 ->
                         CoSEqPList xs^1 xs^2)")
(assume "xs^1" "xs^2")
(coind)
(assume "xs^3" "xs^4" "Conj")
(inst-with-to "Conj" 'left "CoTxs3")
(inst-with-to "Conj" 'right "xs3=xs4")
(drop "Conj")
(simp "<-" "xs3=xs4")
(drop "xs3=xs4")
(inst-with-to "CoSTotalListClause" (pt "xs^3") "CoTxs3" "Inst")
(elim "Inst")
;; 16,17
(drop "Inst")
(assume "xs3=Nil")
(intro 0)
(split)
(use "xs3=Nil")
(use "xs3=Nil")
;; 17
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^5" "x5Prop")
(by-assume "x5Prop" "xs^5" "x5xs5Prop")
(intro 1)
(intro 0 (pt "x^5"))
(intro 0 (pt "x^5"))
(intro 0 (pt "xs^5"))
(intro 0 (pt "xs^5"))
(split)
(intro 1)
(split)
(use "x5xs5Prop")
(use "InitEqD")
(split)
(use "x5xs5Prop")
(use "x5xs5Prop")
;; 2
(assume "Assertion" "xs^" "CoTxs")
(use "Assertion")
(split)
(use "CoTxs")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "CoSEqPListRefl")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n]
;;  (CoRec nat=>nat)n
;;  ([n0][if (Des n0) (DummyL nat ysum nat) ([n1]Inr((InR nat nat)n1))])


;; CoEqPListNcRefl
(set-goal "allnc x^(TotalNc x^ -> EqPNc x^ x^) ->
           allnc xs^(CoTotalListNc xs^ -> CoEqPListNc xs^ xs^)")
(assume "EqPHyp")
(assert "allnc xs^1,xs^2(CoTotalListNc xs^1 andi xs^1 eqd xs^2 ->
                         CoEqPListNc xs^1 xs^2)")
(assume "xs^1" "xs^2")
(coind)
(assume "xs^3" "xs^4" "Conj")
(inst-with-to "Conj" 'left "CoTxs3")
(inst-with-to "Conj" 'right "xs3=xs4")
(drop "Conj")
(simp "<-" "xs3=xs4")
(drop "xs3=xs4")
(inst-with-to "CoTotalListClause" (pt "xs^3") "CoTxs3" "Inst")
(elim "Inst")
;; 16,17
(drop "Inst")
(assume "xs3=Nil")
(intro 0)
(split)
(use "xs3=Nil")
(use "xs3=Nil")
;; 17
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^5" "x5Prop")
(intro 1)
(intro 0 (pt "x^5"))
(intro 0 (pt "x^5"))
(split)
(use "EqPHyp")
(use "x5Prop")
(inst-with-to "x5Prop" 'right "ExHyp6")
(drop "x5Prop")
(by-assume "ExHyp6" "xs^6" "xs6Prop")
(intro 0 (pt "xs^6"))
(intro 0 (pt "xs^6"))
(split)
(intro 1)
(split)
(use "xs6Prop")
(use "InitEqD")
(split)
(use "xs6Prop")
(use "xs6Prop")
;; 3
(assume "Assertion" "xs^" "CoTxs")
(use "Assertion")
(split)
(use "CoTxs")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "CoEqPListNcRefl")

;; CoSEqPListNcRefl
(set-goal "allnc xs^(CoSTotalListNc xs^ -> CoSEqPListNc xs^ xs^)")
(assert "allnc xs^1,xs^2(CoSTotalListNc xs^1 andi xs^1 eqd xs^2 ->
                         CoSEqPListNc xs^1 xs^2)")
(assume "xs^1" "xs^2")
(coind)
(assume "xs^3" "xs^4" "Conj")
(inst-with-to "Conj" 'left "CoTxs3")
(inst-with-to "Conj" 'right "xs3=xs4")
(drop "Conj")
(simp "<-" "xs3=xs4")
(drop "xs3=xs4")
(inst-with-to "CoSTotalListNcClause" (pt "xs^3") "CoTxs3" "Inst")
(elim "Inst")
;; 16,17
(drop "Inst")
(assume "xs3=Nil")
(intro 0)
(split)
(use "xs3=Nil")
(use "xs3=Nil")
;; 17
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^5" "x5Prop")
(by-assume "x5Prop" "xs^5" "x5xs5Prop")
(intro 1)
(intro 0 (pt "x^5"))
(intro 0 (pt "x^5"))
(intro 0 (pt "xs^5"))
(intro 0 (pt "xs^5"))
(split)
(intro 1)
(split)
(use "x5xs5Prop")
(use "InitEqD")
(split)
(use "x5xs5Prop")
(use "x5xs5Prop")
;; 2
(assume "Assertion" "xs^" "CoTxs")
(use "Assertion")
(split)
(use "CoTxs")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "CoSEqPListNcRefl")

;; 2-2.  EqPMR and CoEqPMR
;; =======================

;; 2-2-1.  EqPMR
;; =============

;; 2-2-1-2.  Properties
;; ====================

;; 2-2-1-2-1.  Ex falso
;; ====================

;; EfREqPListMR
;; EfNEqPListMR
;; EfEqPListMR
;; EfANEqPListMR
;; EfSEqPListMR

;; EfREqPListMR
(set-goal "allnc xs^1,xs^2,(list gamma)^(F -> 
(REqPListMR (cterm (x^1,x^2,gamma^1) (Pvar alpha alpha gamma)^ x^1 x^2 gamma^1))
 xs^1 xs^2 (list gamma)^)")
(assume "xs^1" "xs^2" "(list gamma)^" "Absurd")
(simp (pf "xs^1 eqd (Nil alpha)"))
(simp (pf "xs^2 eqd (Nil alpha)"))
(simp (pf "(list gamma)^ eqd (Nil gamma)"))
(use "REqPListNilMR")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfREqPListMR")

;; EfNEqPListMR
(set-goal
 "allnc xs^1,xs^2,n^(F ->
 (NEqPListMR (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xs^1 xs^2 n^)")
(assume "xs^1" "xs^2" "n^" "Absurd")
(simp (pf "xs^1 eqd (Nil alpha)"))
(simp (pf "xs^2 eqd (Nil alpha)"))
(simp (pf "n^ eqd 0"))
(use "NEqPListNilMR")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfNEqPListMR")

;; EfEqPListMR
(set-goal "allnc xs^1,xs^2,xs^3(F -> EqPListMR xs^1 xs^2 xs^3)")
(assume "xs^1" "xs^2" "xs^3" "Absurd")
(simp (pf "xs^1 eqd (Nil alpha)"))
(simp (pf "xs^2 eqd (Nil alpha)"))
(simp (pf "xs^3 eqd (Nil alpha)"))
(use "EqPListNilMR")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfEqPListMR")

;; EfANEqPListMR
(set-goal "allnc xs^1,xs^2,n^(F -> ANEqPListMR xs^1 xs^2 n^)")
(assume "xs^1" "xs^2" "n^" "Absurd")
(simp (pf "xs^1 eqd (Nil alpha)"))
(simp (pf "xs^2 eqd (Nil alpha)"))
(simp (pf "n^ eqd 0"))
(use "ANEqPListNilMR")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfANEqPListMR")

;; EfSEqPListMR
(set-goal "allnc xs^1,xs^2,n^(F -> SEqPListMR xs^1 xs^2 n^)")
(assume "xs^1" "xs^2" "n^" "Absurd")
(simp (pf "xs^1 eqd (Nil alpha)"))
(simp (pf "xs^2 eqd (Nil alpha)"))
(simp (pf "n^ eqd 0"))
(use "SEqPListNilMR")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfSEqPListMR")

;; 2-2-1-2-2.  Monotonicity
;; ========================

;; ListREqPMonMR
;; ListNEqPMonMR

;; ListREqPMonMR
(set-goal "allnc x^1,x^2,gamma^((Pvar alpha alpha gamma)^1 x^1 x^2 gamma^ ->
 (Pvar alpha alpha gamma)^2 x^1 x^2 gamma^) -> 
 allnc xs^1,xs^2,(list gamma)^(
 (REqPListMR (cterm (x^1,x^2,gamma^) (Pvar alpha alpha gamma)^1 x^1 x^2 gamma^))
 xs^1 xs^2 (list gamma)^ -> 
 (REqPListMR (cterm (x^1,x^2,gamma^) (Pvar alpha alpha gamma)^2 x^1 x^2 gamma^))
 xs^1 xs^2 (list gamma)^)")
(assume "MonHyp" "xs^1" "xs^2" "(list gamma)^")
(elim)
(intro 0)
(assume "x^3" "x^4" "gamma^" "PHyp" "xs^3" "xs^4" "(list gamma)^1" "Useless"
	"RTZHyp")
(intro 1)
(use "MonHyp")
(use "PHyp")
(use "RTZHyp")
;; Proof finished.
;; (cdp)
(save "ListREqPMonMR")

;; ListNEqPMonMR
(set-goal
 "allnc x^1,x^2((Pvar alpha alpha)^1 x^1 x^2 -> (Pvar alpha alpha)^2 x^1 x^2) ->
  allnc xs^1,xs^2,n^(
     (NEqPListMR (cterm (x^1,x^2) (Pvar alpha alpha)^1 x^1 x^2))xs^1 xs^2 n^ -> 
     (NEqPListMR (cterm (x^1,x^2) (Pvar alpha alpha)^2 x^1 x^2))xs^1 xs^2 n^)")
(assume "MonHyp" "xs^1" "xs^2" "n^")
(elim)
(intro 0)
(assume "x^3" "x^4" "PHyp" "xs^3" "xs^4" "n^1" "Useless" "Hyp")
(intro 1)
(use "MonHyp")
(use "PHyp")
(use "Hyp")
;; Proof finished.
;; (cdp)
(save "ListNEqPMonMR")

;; 2-2-1-2-3.  Connections
;; =======================

;; EqPListMRToEqDLeft
;; EqPListMRToEqDRight
;; EqPListMRToTotalNc
;; EqPListMRRefl

;; EqPListMRToEqDLeft
(set-goal "allnc x^1,x^2,x^3(EqPMR x^1 x^2 x^3 -> x^1 eqd x^2) ->
allnc xs^1,xs^2,xs^3(EqPListMR xs^1 xs^2 xs^3 -> xs^1 eqd xs^2)")
(assume "EqDHyp" "xs^1" "xs^2" "xs^3" "EqPxs1xs2xs3")
(elim "EqPxs1xs2xs3")
(use "InitEqD")
(assume
 "x^4" "x^5" "x^6" "EqPx4x5x6" "xs^4" "xs^5" "xs^6" "Useless" "EqDxs4xs5")
(simp "EqDxs4xs5")
(simp (pf "x^4 eqd x^5"))
(use "InitEqD")
(use "EqDHyp" (pt "x^6"))
(use "EqPx4x5x6")
;; Proof finished.
;; (cdp)
(save "EqPListMRToEqDLeft")

;; EqPListMRToEqDRight
(set-goal "allnc x^1,x^2,x^3(EqPMR x^1 x^2 x^3 -> x^1 eqd x^3) ->
 allnc xs^1,xs^2,xs^3(EqPListMR xs^1 xs^2 xs^3 -> xs^1 eqd xs^3)")
(assume "EqDx1x3" "xs^1" "xs^2" "xs^3" "EqPMRxs1xs2xs3")
(elim "EqPMRxs1xs2xs3")
(use "InitEqD")
(assume "x^4" "x^5" "x^6" "EqPMRx4x5x6" "xs^4" "xs^5" "xs^6" "Useless"
 "EqDxs4xs5xs6")
(simp "EqDxs4xs5xs6")
(simp "EqDx1x3" (pt "x^5") (pt "x^6"))
(use "InitEqD")
(use "EqPMRx4x5x6")
;; Proof finished.
;; (cdp)
(save "EqPListMRToEqDRight")

;; EqPListMRToTotalNc
(set-goal "allnc x^1,x^2,x^3(EqPMR x^1 x^2 x^3 -> TotalNc x^3) ->
allnc xs^1,xs^2,xs^3(EqPListMR xs^1 xs^2 xs^3 -> TotalListNc xs^3)")
(assume "THyp" "xs^1" "xs^2" "xs^3" "EqPxs1xs2xs3")
(elim "EqPxs1xs2xs3")
(use "TotalListNcNil")
(assume "x^4" "x^5" "x^6" "EqPx4x5x6" "xs^4" "xs^5" "xs^6" "Useless" "Txs6")
(use "TotalListNcCons")
(use "THyp" (pt "x^4") (pt "x^5"))
(use "EqPx4x5x6")
(use "Txs6")
;; Proof finished.
;; (cdp)
(save "EqPListMRToTotalNc")

;; EqPListMRRefl
(set-goal "allnc x^(Total x^ -> EqPMR x^ x^ x^) ->
allnc xs^(TotalListNc xs^ -> EqPListMR xs^ xs^ xs^)")
(assume "EqPHyp" "xs^1" "Txs1")
(elim "Txs1")
(use "EqPListNilMR")
(assume "x^2" "Tx2" "xs^2" "Txs2")
(use "EqPListConsMR")
(use "EqPHyp")
(use "Tx2")
;; Proof finished.
;; (cdp)
(save "EqPListMRRefl")

;; 2-2-2.  CoEqPMR
;; ===============

;; 2-2-2-2.  Properties
;; ====================

;; 2-2-2-2-1.  Ex falso
;; ====================

;; EfCoREqPListMR
;; EfCoNEqPListMR
;; EfCoEqPListMR
;; EfCoANEqPListMR
;; EfCoSEqPListMR

;; EfCoREqPListMR
(set-goal "allnc xs^1,xs^2,(list gamma)^(F -> 
(CoREqPListMR (cterm (x^1,x^2,gamma^) (Pvar alpha alpha gamma)^ x^1 x^2 gamma^))
xs^1 xs^2 (list gamma)^)")
(assume "xs^1" "xs^2" "(list gamma)^" "Absurd")
(coind "Absurd")
(assume "xs^3" "xs^4" "(list gamma)^1" "Useless")
(intro 0)
(simp (pf "xs^3 eqd (Nil alpha)"))
(simp (pf "xs^4 eqd (Nil alpha)"))
(simp (pf "(list gamma)^1 eqd (Nil gamma)"))
(split)
(use "InitEqD")
(split)
(use "InitEqD")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
(use "EfEqD")
(use "Absurd")
;; Proof finished.
;; (cdp)
(save "EfCoREqPListMR")

;; EfCoNEqPListMR
(set-goal
 "allnc xs^1,xs^2,n^(F ->
 (CoNEqPListMR (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2))xs^1 xs^2 n^)")
(assume "xs^1" "xs^2" "n^" "Absurd")
(coind "Absurd")
(assume "xs^3" "xs^4" "n^1" "Useless")
(intro 0)
(simp (pf "xs^3 eqd (Nil alpha)"))
(simp (pf "xs^4 eqd (Nil alpha)"))
(simp (pf "n^1 eqd 0"))
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
(save "EfCoNEqPListMR")

;; EfCoEqPListMR
(set-goal "allnc xs^1,xs^2,xs^3(F -> CoEqPListMR xs^1 xs^2 xs^3)")
(assume "xs^1" "xs^2" "xs^3" "Absurd")
(coind "Absurd")
(assume "xs^4" "xs^5" "xs^6" "Useless")
(intro 0)
(simp (pf "xs^4 eqd (Nil alpha)"))
(simp (pf "xs^5 eqd (Nil alpha)"))
(simp (pf "xs^6 eqd (Nil alpha)"))
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
(save "EfCoEqPListMR")

;; EfCoANEqPListMR
(set-goal "allnc xs^1,xs^2,n^(F -> CoANEqPListMR xs^1 xs^2 n^)")
(assume "xs^1" "xs^2" "n^" "Absurd")
(coind "Absurd")
(assume "xs^3" "xs^4" "n^1" "Useless")
(intro 0)
(simp (pf "xs^3 eqd (Nil alpha)"))
(simp (pf "xs^4 eqd (Nil alpha)"))
(simp (pf "n^1 eqd 0"))
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
(save "EfCoANEqPListMR")

;; EfCoSEqPListMR
(set-goal "allnc xs^1,xs^2,n^(F -> CoSEqPListMR xs^1 xs^2 n^)")
(assume "xs^1" "xs^2" "n^" "Absurd")
(coind "Absurd")
(assume "xs^3" "xs^4" "n^1" "Useless")
(intro 0)
(simp (pf "xs^3 eqd (Nil alpha)"))
(simp (pf "xs^4 eqd (Nil alpha)"))
(simp (pf "n^1 eqd 0"))
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
(save "EfCoSEqPListMR")

;; 2-2-2-2-2.  Monotonicity
;; ========================

;; ListCoREqPMonMR
;; ListCoNEqPMonMR

;; ListCoREqPMonMR
(set-goal "allnc x^1,x^2,gamma^((Pvar alpha alpha gamma)^1 x^1 x^2 gamma^ ->
                                (Pvar alpha alpha gamma)^2 x^1 x^2 gamma^) -> 
 allnc xs^1,xs^2,(list gamma)^(
(CoREqPListMR (cterm (x^1,x^2,gamma^)(Pvar alpha alpha gamma)^1 x^1 x^2 gamma^))
xs^1 xs^2 (list gamma)^ -> 
(CoREqPListMR (cterm (x^1,x^2,gamma^)(Pvar alpha alpha gamma)^2 x^1 x^2 gamma^))
xs^1 xs^2 (list gamma)^)")
(assume "MonHyp" "xs^1" "xs^2" "(list gamma)^" "CoRHyp1")
(coind "CoRHyp1")
(assume "xs^3" "xs^4" "(list gamma)^1" "CoRHyp2")
(inst-with-to
 "CoREqPListMRClause"
 (py "alpha")
 (py "gamma")
 (make-cterm (pv "x^1") (pv "x^2") (pv "gamma^")
	     (pf "(Pvar alpha alpha gamma)^1 x^1 x^2 gamma^"))
 (pt "xs^3") (pt "xs^4") (pt "(list gamma)^1") "CoRHyp2" "Inst")
(elim "Inst")
;; 7,8
(drop "Inst")
(assume "xs1=Nil")
(intro 0)
(use "xs1=Nil")
;; 8
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^5" "x5Prop")
(by-assume "x5Prop" "x^6" "x5x6Prop")
(by-assume "x5x6Prop""gamma^2" "x5x6y2Prop")
(inst-with-to "x5x6y2Prop" 'left "Px5x6")
(inst-with-to "x5x6y2Prop" 'right "ExHyp2")
(drop "x5x6y2Prop")
(by-assume "ExHyp2" "xs^5" "x5x6y2xs5Prop")
(by-assume "x5x6y2xs5Prop" "xs^6" "x5x6y2xs5xs6Prop")
(by-assume "x5x6y2xs5xs6Prop" "(list gamma)^2" "x5x6y2xs5xs6ys2Prop")
(intro 1)
(intro 0 (pt "x^5"))
(intro 0 (pt "x^6"))
(intro 0 (pt "gamma^2"))
(split)
(use "MonHyp")
(use "Px5x6")
(intro 0 (pt "xs^5"))
(intro 0 (pt "xs^6"))
(intro 0 (pt "(list gamma)^2"))
(split)
(intro 1)
(use "x5x6y2xs5xs6ys2Prop")
(use "x5x6y2xs5xs6ys2Prop")
;; Proof finished.
;; (cdp)
(save "ListCoREqPMonMR")

;; (display-idpc "CoNEqPListMR")

;; ListCoNEqPMonMR
(set-goal "allnc x^1,x^2((Pvar alpha alpha)^1 x^1 x^2 ->
                         (Pvar alpha alpha)^2 x^1 x^2) -> 
  allnc xs^1,xs^2,n^(
   (CoNEqPListMR (cterm (x^1,x^2) (Pvar alpha alpha)^1 x^1 x^2))xs^1 xs^2 n^ -> 
   (CoNEqPListMR (cterm (x^1,x^2) (Pvar alpha alpha)^2 x^1 x^2))xs^1 xs^2 n^)")
(assume "MonHyp" "xs^1" "xs^2" "n^" "CoNHyp1")
(coind "CoNHyp1")
(assume "xs^3" "xs^4" "n^1" "CoNHyp2")
(inst-with-to
 "CoNEqPListMRClause"
 (make-cterm (pv "x^1") (pv "x^2") (pf "(Pvar alpha alpha)^1 x^1 x^2"))
 (pt "xs^3") (pt "xs^4") (pt "n^1") "CoNHyp2" "Inst")
(elim "Inst")
;; 7,8
(drop "Inst")
(assume "xs1=Nil")
(intro 0)
(use "xs1=Nil")
;; 8
(drop "Inst")
(assume "ExHyp")
(by-assume "ExHyp" "x^5" "x5Prop")
(by-assume "x5Prop" "x^6" "x5x6Prop")
(inst-with-to "x5x6Prop" 'left "Px5x6")
(inst-with-to "x5x6Prop" 'right "ExHyp2")
(drop "x5x6Prop")
(by-assume "ExHyp2" "xs^5" "x5x6xs5Prop")
(by-assume "x5x6xs5Prop" "xs^6" "x5x6xs5xs6Prop")
(by-assume "x5x6xs5xs6Prop" "n^2" "x5x6xs5xs6n2Prop")
(intro 1)
(intro 0 (pt "x^5"))
(intro 0 (pt "x^6"))
(split)
(use "MonHyp")
(use "Px5x6")
(intro 0 (pt "xs^5"))
(intro 0 (pt "xs^6"))
(intro 0 (pt "n^2"))
(split)
(intro 1)
(use "x5x6xs5xs6n2Prop")
(use "x5x6xs5xs6n2Prop")
;; Proof finished.
;; (cdp)
(save "ListCoNEqPMonMR")

;; 2-2-2-2-3.  Total implies CoTotal
;; =================================

;; REqPListMRToCoREqPMR
;; NEqPListMRToCoNEqPMR
;; EqPListMRToCoEqPMR
;; ANEqPListMRToCoANEqPMR
;; SEqPListMRToCoSEqPMR

;; REqPListMRToCoREqPMR
(set-goal "allnc xs^1,xs^2,(list gamma)^(
 (REqPListMR (cterm (x^1,x^2,gamma^) (Pvar alpha alpha gamma)^ x^1 x^2 gamma^))
 xs^1 xs^2 (list gamma)^ -> 
(CoREqPListMR (cterm (x^1,x^2,gamma^) (Pvar alpha alpha gamma)^ x^1 x^2 gamma^))
xs^1 xs^2 (list gamma)^)")
(assume "xs^1" "xs^2" "(list gamma)^" "Txs1xs2ys")
(coind "Txs1xs2ys")
(assume "xs^3" "xs^4" "(list gamma)^1" "Txs3xs4ys1")
(assert "xs^3 eqd (Nil alpha) andnc
         xs^4 eqd (Nil alpha) andnc (list gamma)^1 eqd(Nil gamma) ornc
         exr x^5,x^6,gamma^2,xs^5,xs^6,(list gamma)^2(
 (Pvar alpha alpha gamma)^ x^5 x^6 gamma^2 andnc
 (REqPListMR (cterm (x^1,x^2,gamma^) (Pvar alpha alpha gamma)^ x^1 x^2 gamma^))
       xs^5 xs^6 (list gamma)^2 andnc
        xs^3 eqd x^5::xs^5 andnc
        xs^4 eqd x^6::xs^6 andnc
        (list gamma)^1 eqd gamma^2::(list gamma)^2)")
 (elim "Txs3xs4ys1")
;; 7,8
 (intro 0)
 (split)
 (use "InitEqD")
 (split)
 (use "InitEqD")
 (use "InitEqD")
;; 8
 (assume "x^5" "x^6" "gamma^2" "Px5x6" "xs^5" "xs^6" "(list gamma)^2"
	 "Txs5xs6ys2" "Useless")
 (drop "Useless")
 (intro 1)
 (intro 0 (pt "x^5"))
 (intro 0 (pt "x^6"))
 (intro 0 (pt "gamma^2"))
 (intro 0 (pt "xs^5"))
 (intro 0 (pt "xs^6"))
 (intro 0 (pt "(list gamma)^2"))
 (split)
 (use "Px5x6")
 (split)
 (use "Txs5xs6ys2")
 (split)
 (use "InitEqD")
 (split)
 (use "InitEqD")
 (use "InitEqD")
;; Assertion proved.
(assume "Disj")
(elim "Disj")
;; 32,33
(assume "NilConj")
(intro 0)
(use "NilConj")
;; 33
(drop "Disj")
(assume "ExHyp")
(intro 1)
(by-assume "ExHyp" "x^5" "x5Prop")
(by-assume "x5Prop" "x^6" "x5x6Prop")
(by-assume "x5x6Prop" "gamma^2" "x5x6y2Prop")
(by-assume "x5x6y2Prop" "xs^5" "x5x6y2xs5Prop")
(by-assume "x5x6y2xs5Prop" "xs^6" "x5x6y2xs5xs6Prop")
(by-assume "x5x6y2xs5xs6Prop" "(list gamma)^2" "x5x6y2xs5xs6ys2Prop")
(intro 0 (pt "x^5"))
(intro 0 (pt "x^6"))
(intro 0 (pt "gamma^2"))
(split)
(use "x5x6y2xs5xs6ys2Prop")
(intro 0 (pt "xs^5"))
(intro 0 (pt "xs^6"))
(intro 0 (pt "(list gamma)^2"))
(split)
(intro 1)
(use "x5x6y2xs5xs6ys2Prop")
(use "x5x6y2xs5xs6ys2Prop")
;; Proof finished.
;; (cdp)
(save "REqPListMRToCoREqPMR")

;; NEqPListMRToCoNEqPMR
(set-goal "allnc xs^1,xs^2,n^(
 (NEqPListMR (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2)) xs^1 xs^2 n^ -> 
 (CoNEqPListMR (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2)) xs^1 xs^2 n^)")
(assume "xs^1" "xs^2" "n^" "Txs1xs2n")
(coind "Txs1xs2n")
(assume "xs^3" "xs^4" "n^1" "Txs3xs4n1")
(assert "xs^3 eqd (Nil alpha) andnc
         xs^4 eqd (Nil alpha) andnc n^1 eqd 0 ornc
         exr x^5,x^6,xs^5,xs^6,n^2(
 (Pvar alpha alpha)^ x^5 x^6 andnc
 (NEqPListMR (cterm (x^1,x^2) (Pvar alpha alpha)^ x^1 x^2)) xs^5 xs^6 n^2 andnc
       xs^3 eqd x^5::xs^5 andnc xs^4 eqd x^6::xs^6 andnc n^1 eqd Succ(n^2))")
 (elim "Txs3xs4n1")
;; 7,8
 (intro 0)
 (split)
 (use "InitEqD")
 (split)
 (use "InitEqD")
 (use "InitEqD")
;; 8
 (assume "x^5" "x^6" "Px5x6" "xs^5" "xs^6" "n^2" "Txs5xs6n2" "Useless")
 (drop "Useless")
 (intro 1)
 (intro 0 (pt "x^5"))
 (intro 0 (pt "x^6"))
 (intro 0 (pt "xs^5"))
 (intro 0 (pt "xs^6"))
 (intro 0 (pt "n^2"))
 (split)
 (use "Px5x6")
 (split)
 (use "Txs5xs6n2")
 (split)
 (use "InitEqD")
 (split)
 (use "InitEqD")
 (use "InitEqD")
;; Assertion proved.
(assume "Disj")
(elim "Disj")
;; 31,32
(assume "NilConj")
(intro 0)
(use "NilConj")
;; 32
(drop "Disj")
(assume "ExHyp")
(intro 1)
(by-assume "ExHyp" "x^5" "x5Prop")
(by-assume "x5Prop" "x^6" "x5x6Prop")
(by-assume "x5x6Prop" "xs^5" "x5x6xs5Prop")
(by-assume "x5x6xs5Prop" "xs^6" "x5x6xs5xs6Prop")
(by-assume "x5x6xs5xs6Prop" "n^2" "x5x6xs5xs6n2Prop")
(intro 0 (pt "x^5"))
(intro 0 (pt "x^6"))
(split)
(use "x5x6xs5xs6n2Prop")
(intro 0 (pt "xs^5"))
(intro 0 (pt "xs^6"))
(intro 0 (pt "n^2"))
(split)
(intro 1)
(use "x5x6xs5xs6n2Prop")
(use "x5x6xs5xs6n2Prop")
;; Proof finished.
;; (cdp)
(save "NEqPListMRToCoNEqPMR")

;; EqPListMRToCoEqPMR
(set-goal "allnc xs^1,xs^2,xs^3(
 EqPListMR xs^1 xs^2 xs^3 -> CoEqPListMR xs^1 xs^2 xs^3)")
(assume "xs^1" "xs^2" "xs^3" "Txs1xs2xs3")
(coind "Txs1xs2xs3")
(assume "xs^4" "xs^5" "xs^6" "Txs4xs5xs6")
(assert "xs^4 eqd (Nil alpha) andnc
         xs^5 eqd (Nil alpha) andnc xs^6 eqd(Nil alpha) ornc
         exr x^7,x^8,x^9,xs^7,xs^8,xs^9(EqPMR x^7 x^8 x^9 andnc
         EqPListMR xs^7 xs^8 xs^9 andnc 
         xs^4 eqd x^7::xs^7 andnc
         xs^5 eqd x^8::xs^8 andnc
         xs^6 eqd x^9::xs^9)")
 (elim "Txs4xs5xs6")
;; 7,8
 (intro 0)
 (split)
 (use "InitEqD")
 (split)
 (use "InitEqD")
 (use "InitEqD")
;; 8
 (assume "x^7" "x^8" "x^9" "Tx7x8x9" "xs^7" "xs^8" "xs^9" "Txs7xs8xs9"
	 "Useless")
 (drop "Useless")
 (intro 1)
 (intro 0 (pt "x^7"))
 (intro 0 (pt "x^8"))
 (intro 0 (pt "x^9"))
 (intro 0 (pt "xs^7"))
 (intro 0 (pt "xs^8"))
 (intro 0 (pt "xs^9"))
 (split)
 (use "Tx7x8x9")
 (split)
 (use "Txs7xs8xs9")
 (split)
 (use "InitEqD")
 (split)
 (use "InitEqD")
 (use "InitEqD")
;; Assertion proved.
(assume "Disj")
(elim "Disj")
;; 32,33
(assume "NilConj")
(intro 0)
(use "NilConj")
;; 33
(drop "Disj")
(assume "ExHyp")
(intro 1)
(by-assume "ExHyp" "x^7" "x7Prop")
(by-assume "x7Prop" "x^8" "x7x8Prop")
(by-assume "x7x8Prop" "x^9" "x7x8x9Prop")
(by-assume "x7x8x9Prop" "xs^7" "x7x8x9xs7Prop")
(by-assume "x7x8x9xs7Prop" "xs^8" "x7x8x9xs7xs8Prop")
(by-assume "x7x8x9xs7xs8Prop" "xs^9" "x7x8x9xs7xs8xs9Prop")
(intro 0 (pt "x^7"))
(intro 0 (pt "x^8"))
(intro 0 (pt "x^9"))
(split)
(use "x7x8x9xs7xs8xs9Prop")
(intro 0 (pt "xs^7"))
(intro 0 (pt "xs^8"))
(intro 0 (pt "xs^9"))
(split)
(intro 1)
(use "x7x8x9xs7xs8xs9Prop")
(use "x7x8x9xs7xs8xs9Prop")
;; Proof finished.
;; (cdp)
(save "EqPListMRToCoEqPMR")

;; ANEqPListMRToCoANEqPMR
(set-goal "allnc xs^1,xs^2,n^(
 ANEqPListMR xs^1 xs^2 n^ -> CoANEqPListMR xs^1 xs^2 n^)")
(assume "xs^1" "xs^2" "n^" "Txs1xs2n")
(coind "Txs1xs2n")
(assume "xs^3" "xs^4" "n^1" "Txs3xs4n1")
(assert "xs^3 eqd (Nil alpha) andnc
         xs^4 eqd (Nil alpha) andnc n^1 eqd 0 ornc
         exr x^5,x^6,xs^5,xs^6,n^2(EqPNc x^5 x^6 andnc
         ANEqPListMR xs^5 xs^6 n^2 andnc 
         xs^3 eqd x^5::xs^5 andnc
         xs^4 eqd x^6::xs^6 andnc
         n^1 eqd Succ n^2)")
 (elim "Txs3xs4n1")
;; 7,8
 (intro 0)
 (split)
 (use "InitEqD")
 (split)
 (use "InitEqD")
 (use "InitEqD")
;; 8
 (assume "x^5" "x^6" "Tx5x6" "xs^5" "xs^6" "n^2" "Txs5xs6n2" "Useless")
 (drop "Useless")
 (intro 1)
 (intro 0 (pt "x^5"))
 (intro 0 (pt "x^6"))
 (intro 0 (pt "xs^5"))
 (intro 0 (pt "xs^6"))
 (intro 0 (pt "n^2"))
 (split)
 (use "Tx5x6")
 (split)
 (use "Txs5xs6n2")
 (split)
 (use "InitEqD")
 (split)
 (use "InitEqD")
 (use "InitEqD")
;; Assertion proved.
(assume "Disj")
(elim "Disj")
;; 31,32
(assume "NilConj")
(intro 0)
(use "NilConj")
;; 32
(drop "Disj")
(assume "ExHyp")
(intro 1)
(by-assume "ExHyp" "x^5" "x5Prop")
(by-assume "x5Prop" "x^6" "x5x6Prop")
(by-assume "x5x6Prop" "xs^5" "x5x6xs5Prop")
(by-assume "x5x6xs5Prop" "xs^6" "x5x6xs5xs6Prop")
(by-assume "x5x6xs5xs6Prop" "n^2" "x5x6xs5xs6n2Prop")
(intro 0 (pt "x^5"))
(intro 0 (pt "x^6"))
(split)
(use "x5x6xs5xs6n2Prop")
(intro 0 (pt "xs^5"))
(intro 0 (pt "xs^6"))
(intro 0 (pt "n^2"))
(split)
(intro 1)
(use "x5x6xs5xs6n2Prop")
(use "x5x6xs5xs6n2Prop")
;; Proof finished.
;; (cdp)
(save "ANEqPListMRToCoANEqPMR")

;; SEqPListMRToCoSEqPMR
(set-goal "allnc xs^1,xs^2,n^(
 SEqPListMR xs^1 xs^2 n^ -> CoSEqPListMR xs^1 xs^2 n^)")
(assume "xs^1" "xs^2" "n^" "Txs1xs2n")
(coind "Txs1xs2n")
(assume "xs^3" "xs^4" "n^1" "Txs3xs4n1")
(assert "xs^3 eqd (Nil alpha) andnc
         xs^4 eqd (Nil alpha) andnc n^1 eqd 0 ornc
         exr x^5,x^6,xs^5,xs^6,n^2(SEqPListMR xs^5 xs^6 n^2 andnc 
         xs^3 eqd x^5::xs^5 andnc
         xs^4 eqd x^6::xs^6 andnc
         n^1 eqd Succ n^2)")
 (elim "Txs3xs4n1")
;; 7,8
 (intro 0)
 (split)
 (use "InitEqD")
 (split)
 (use "InitEqD")
 (use "InitEqD")
;; 8
 (assume "x^5" "x^6" "xs^5" "xs^6" "n^2" "Txs5xs6n2" "Useless")
 (drop "Useless")
 (intro 1)
 (intro 0 (pt "x^5"))
 (intro 0 (pt "x^6"))
 (intro 0 (pt "xs^5"))
 (intro 0 (pt "xs^6"))
 (intro 0 (pt "n^2"))
 (split)
 (use "Txs5xs6n2")
 (split)
 (use "InitEqD")
 (split)
 (use "InitEqD")
 (use "InitEqD")
;; Assertion proved.
(assume "Disj")
(elim "Disj")
;; 29,30
(assume "NilConj")
(intro 0)
(use "NilConj")
;; 30
(drop "Disj")
(assume "ExHyp")
(intro 1)
(by-assume "ExHyp" "x^5" "x5Prop")
(by-assume "x5Prop" "x^6" "x5x6Prop")
(by-assume "x5x6Prop" "xs^5" "x5x6xs5Prop")
(by-assume "x5x6xs5Prop" "xs^6" "x5x6xs5xs6Prop")
(by-assume "x5x6xs5xs6Prop" "n^2" "x5x6xs5xs6n2Prop")
(intro 0 (pt "x^5"))
(intro 0 (pt "x^6"))
(intro 0 (pt "xs^5"))
(intro 0 (pt "xs^6"))
(intro 0 (pt "n^2"))
(split)
(intro 1)
(use "x5x6xs5xs6n2Prop")
(use "x5x6xs5xs6n2Prop")
;; Proof finished.
;; (cdp)
(save "SEqPListMRToCoSEqPMR")

