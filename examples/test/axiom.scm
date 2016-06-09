;; (load "~/git/minlog/init.scm")
(load "names.scm")

;; 8. and 9. Assumption variables and axioms
;; =========================================
;; (axiom.scm)

;; Tests for all-formulas-to-uninst-imp-formulas-and-tpsubst

(add-pvar-name "P" (make-arity (py "nat")))

(pp (rename-variables
     (caar (all-formulas-to-uninst-imp-formulas-and-tpsubst
	    (pf "all n P n")))))

;; all n(P184 0 -> all n0(P184 n0 -> P184(Succ n0)) -> P184 n)

(remove-pvar-name "P")

(add-pvar-name "P" (make-arity (py "list nat")))
(add-var-name "ns" (py "list nat"))

(pp (rename-variables
     (caar (all-formulas-to-uninst-imp-formulas-and-tpsubst
	    (pf "all ns P ns")))))

;; all (list alpha138)(
;;  (Pvar list alpha138)_185(Nil alpha138) ->
;;  all alpha138_0,(list alpha138)_1(
;;   (Pvar list alpha138)_185(list alpha138)_1 ->
;;   (Pvar list alpha138)_185(alpha138_0::(list alpha138)_1)) ->
;;  (Pvar list alpha138)_185(list alpha138))

(pp-subst
 (cadr (all-formulas-to-uninst-imp-formulas-and-tpsubst
	(pf "all ns P ns"))))

  ;; alpha139 -> nat
  ;; (Pvar list alpha139)_186 ->
  ;;    (cterm (ns) P ns)

;; Tests for imp-formulas-to-elim-aconst

(remove-pvar-name "P")
(add-pvar-name "P" (make-arity (py "nat")))

(define aconst (imp-formulas-to-elim-aconst (pf "Even m^ -> P m^")))
(pp (rename-variables (aconst-to-formula aconst)))
;; allnc n^(Even n^ -> P 0 -> allnc n^0(Even n^0 -> P n^0 -> P(n^0+2)) -> P n^)

(define aconst (imp-formulas-to-elim-aconst (pf "Even m^ -> T")))
(check-aconst aconst) ;#t
(check-aconst aconst #f)
;; check-aconst
;; Elim
;; computationally relevant formulas expected
;; T

;; Tests for all-formulas-to-ind-aconst

(remove-pvar-name "P")
(remove-var-name "ns")

(add-pvar-name "P" (make-arity (py "nat")))

(pp (rename-variables
     (aconst-to-formula (all-formulas-to-ind-aconst (pf "all n P n")))))

;; all n(P 0 -> all n0(P n0 -> P(Succ n0)) -> P n)

(remove-pvar-name "P")

;; Simultaneously defined algebras require simultaneous induction:

(add-pvar-name "P" (make-arity (py "tree")))
(add-pvar-name "S" (make-arity (py "tlist")))

(pp (rename-variables (aconst-to-formula (all-formulas-to-ind-aconst
					  (pf "all tlist S tlist")
					  (pf "all tree P tree")))))
;; all tlist(
;;  S Empty ->
;;  all tree0,tlist1(P tree0 -> S tlist1 -> S(Tcons tree0 tlist1)) ->
;;  P Leaf -> all tlist0(S tlist0 -> P(Branch tlist0)) -> S tlist)

(remove-pvar-name "P" "S")

;; Tests for all-formula-to-cases-aconst

(add-pvar-name "P" (make-arity (py "nat")))

(pp (rename-variables
     (aconst-to-formula (all-formula-to-cases-aconst (pf "all n P n")))))

;; all n(P 0 -> all n0 P(Succ n0) -> P n)

;; Tests for all-formula-and-number-to-gind-aconst

;; GInd: all h,x(all x(all y(h y<h x -> Q y) -> Q x) -> all p(p -> Q x))
;; with h a measure function of type alpha1 => ... => alphan => nat.

(add-var-name "h" (py "alpha=>alpha=>nat"))

(pp (rename-variables
     (aconst-to-formula
      (all-formula-and-number-to-gind-aconst (pf "all x1,x2 R x1 x2") 2))))

;; all h,x,x0(
;;  all x1,x2(all x3,x4(h x3 x4<h x1 x2 -> R x3 x4) -> R x1 x2) ->
;;  all boole(boole -> R x x0))

(remove-var-name "h")

;; Tests for intro and elim

(define idpc
  (idpredconst-name-and-types-and-cterms-to-idpredconst "Even" '() '()))

;; There are no types, since the clauses do not contain type variables,
;; and no cterms, since the clauses do not contain parameter predicate
;; variables.

(define aconst0 (number-and-idpredconst-to-intro-aconst 0 idpc))
(pp (aconst-to-formula aconst0))
;; Even 0

(define eterm0 (proof-to-extracted-term (make-proof-in-aconst-form aconst0)))
(pp (term-to-type eterm0))
;; nat
(pp eterm0)
;; 0

(define aconst1 (number-and-idpredconst-to-intro-aconst 1 idpc))
(pp (aconst-to-formula aconst1))
;; allnc n^(Even n^ -> Even(n^ +2))

(define eterm1 (proof-to-extracted-term (make-proof-in-aconst-form aconst1)))
(pp (term-to-type eterm1))
;; nat=>nat
(pp eterm1)
;; Succ

(define aconst (imp-formulas-to-elim-aconst (pf "Even m^ -> P m^")))
(pp (rename-variables (aconst-to-formula aconst)))

;; allnc n^(Even n^ -> P 0 -> allnc n^0(Even n^0 -> P n^0 -> P(n^0+2)) -> P n^)

(define eterm (proof-to-extracted-term (make-proof-in-aconst-form aconst)))
(pp (term-to-type eterm))
;; nat=>alpha157=>(nat=>alpha157=>alpha157)=>alpha157

(define idpcev
  (idpredconst-name-and-types-and-cterms-to-idpredconst "Ev" '() '()))
(define idpcod
  (idpredconst-name-and-types-and-cterms-to-idpredconst "Od" '() '()))

(define aconst0 (number-and-idpredconst-to-intro-aconst 0 idpcev))
(pp (aconst-to-formula aconst0))
;; Ev 0

(define aconst1 (number-and-idpredconst-to-intro-aconst 1 idpcev))
(pp (aconst-to-formula aconst1))
;; allnc n^(Od n^ -> Ev(n^ +1))

(define aconst2 (number-and-idpredconst-to-intro-aconst 0 idpcod))
(pp (aconst-to-formula aconst2))
;; allnc n^(Ev n^ -> Od(n^ +1))

(define eterm2 (proof-to-extracted-term (make-proof-in-aconst-form aconst2)))

(pp (term-to-type eterm2))
;; algEv=>algOd

(define aconst (imp-formulas-to-elim-aconst (pf "Ev m^ -> P1 m^")
					    (pf "Od m^ -> P2 m^")))
(pp (rename-variables (aconst-to-formula aconst)))

;; allnc n^(
;;  Ev n^ ->
;;  P1 0 ->
;;  allnc n^0(Od n^0 -> P2 n^0 -> P1(n^0+1)) ->
;;  allnc n^0(Ev n^0 -> P1 n^0 -> P2(n^0+1)) -> P1 n^)

(define eterm (proof-to-extracted-term (make-proof-in-aconst-form aconst)))
(pp (term-to-type eterm))
;; algEv=>
;; alpha12=>(algOd=>alpha13=>alpha12)=>(algEv=>alpha12=>alpha13)=>alpha12

(define idpc
  (idpredconst-name-and-types-and-cterms-to-idpredconst
   "RTotalList" (list (py "nat"))
   (list (make-cterm (pv "n^") (pf "Total n^")))))

(define aconst0 (number-and-idpredconst-to-intro-aconst 0 idpc))
(pp (aconst-to-formula aconst0))
;; (RTotalList (cterm (n^4046) Total n^4046))(Nil nat)

(define eterm0 (proof-to-extracted-term (make-proof-in-aconst-form aconst0)))
(pp (term-to-type eterm0))
;; list nat
(pp eterm0)
;; (Nil nat)

(define aconst1 (number-and-idpredconst-to-intro-aconst 1 idpc))
(pp (aconst-to-formula aconst1))
;; allnc n^4050(
;;  Total n^4050 ->
;;  allnc (list nat)^4051(
;;   (RTotalList (cterm (n^4052) Total n^4052))(list nat)^4051 ->
;;   (RTotalList (cterm (n^4053) Total n^4053))(n^4050::(list nat)^4051)))

(define eterm1 (proof-to-extracted-term (make-proof-in-aconst-form aconst1)))
(pp (term-to-type eterm1))
;; nat=>list nat=>list nat
(pp eterm1)
;; (Cons nat)

(define idpc
  (idpredconst-name-and-types-and-cterms-to-idpredconst
   "RTotalList" (list (py "alpha"))
   (list (make-cterm (pv "x^") (pf "T")))))

(define aconst0 (number-and-idpredconst-to-intro-aconst 0 idpc))
(pp (aconst-to-formula aconst0))
;; (RTotalList (cterm (n^4048) T))(Nil alpha)

(define eterm0 (proof-to-extracted-term (make-proof-in-aconst-form aconst0)))
;; ok, algebra listnc added
(pp (term-to-type eterm0))
;; listnc
(pp eterm0)
;; NilNc

(define aconst1 (number-and-idpredconst-to-intro-aconst 1 idpc))
(pp (aconst-to-formula aconst1))
;; allnc alpha^1985(
;;  T ->
;;  allnc (list alpha)^1986(
;;   (RTotalList (cterm (x^4060) T))(list alpha)^1986 ->
;;   (RTotalList (cterm (x^4060) T))(alpha^1985::(list alpha)^1986)))

(define eterm1 (proof-to-extracted-term (make-proof-in-aconst-form aconst1)))
(pp (term-to-type eterm1))
;; listnc=>listnc
(pp eterm1)
;; ConsNc

(define idpc
  (idpredconst-name-and-types-and-cterms-to-idpredconst
   "EqD" (list (py "alpha")) '()))

(define aconst0 (number-and-idpredconst-to-intro-aconst 0 idpc))
(pp (aconst-to-formula aconst0))
;; allnc alpha^ alpha^ eqd alpha^

(define aconst
  (imp-formulas-to-elim-aconst
   (pf "x^1 eqd x^2 -> R x^1 x^2")))
(pp (rename-variables (aconst-to-formula aconst)))

;; allnc x^,x^0(x^ eqd x^0 -> allnc alpha^ R alpha^ alpha^ -> R x^ x^0)

(define eterm (proof-to-extracted-term (make-proof-in-aconst-form aconst)))
(pp (term-to-type eterm))

;; alpha118=>alpha118

(remove-pvar-name "P")

(define idpc
  (idpredconst-name-and-types-and-cterms-to-idpredconst
   "OrD" '()
   (list (make-cterm (pf "A")) (make-cterm (pf "B")))))

(define aconst0 (number-and-idpredconst-to-intro-aconst 0 idpc))
(pp (aconst-to-formula aconst0))
;; A -> A ord B

(define aconst1 (number-and-idpredconst-to-intro-aconst 1 idpc))
(pp (aconst-to-formula aconst1))
;; B -> A ord B

(define eterm (proof-to-extracted-term (make-proof-in-aconst-form aconst0)))
(pp (term-to-type eterm))
;; alpha24=>alpha24 ysum alpha22

(define aconst
  (imp-formulas-to-elim-aconst
   (pf "A ord B -> C")))
(pp (aconst-to-formula aconst))
;; A ord B -> (A -> C) -> (B -> C) -> C

(define eterm (proof-to-extracted-term (make-proof-in-aconst-form aconst)))
(pp (term-to-type eterm))
;; alpha23 ysum alpha21=>(alpha23=>alpha18)=>(alpha21=>alpha18)=>alpha18

(define idpc (predicate-form-to-predicate (pf "exd n n=m")))
(idpredconst-to-string idpc)
;; "exd n n=m"

(define aconst0 (number-and-idpredconst-to-intro-aconst 0 idpc))
(pp (rename-variables (aconst-to-formula aconst0)))
;; allnc m all n(n=m -> exd n0 n0=m)

(define eterm0 (proof-to-extracted-term (make-proof-in-aconst-form aconst0)))
(pp (term-to-type eterm0))
;; nat=>nat

(define aconst (imp-formulas-to-elim-aconst (pf "exd n n=m -> l=0")))
(pp (rename-variables (aconst-to-formula aconst)))
;; allnc m,l(exd n n=m -> all n(n=m -> l=0) -> l=0)

(define idpc (predicate-form-to-predicate (pf "exd n^ n^ =m")))
(idpredconst-to-string idpc)
;; "exd n^ n^ =m"

(define aconst0 (number-and-idpredconst-to-intro-aconst 0 idpc))
(pp (rename-variables (aconst-to-formula aconst0)))
;; allnc m all n^(n^ =m -> exd n^0 n^0=m)

(define aconst (imp-formulas-to-elim-aconst (pf "exd n^ n^ =m -> l=0")))
(pp (rename-variables (aconst-to-formula aconst)))
;; allnc m,l(exd n^ n^ =m -> all n^(n^ =m -> l=0) -> l=0)

(define idpc
  (predicate-form-to-predicate
   (pf "(PiOne (cterm (x^1535,x^1534) R x^1535 x^1534))x^")))
(idpredconst-to-string idpc)
;; "(PiOne (cterm (x^1535,x^1534) R x^1535 x^1534))"

(define aconst0 (number-and-idpredconst-to-intro-aconst 0 idpc))
(pp (rename-variables (aconst-to-formula aconst0)))
;; all x^,y^(R x^ y^ -> (PiOne (cterm (x^0,x^1) R x^0 x^1))x^)

(define eterm0 (proof-to-extracted-term (make-proof-in-aconst-form aconst0)))
(pp (term-to-type eterm0))
;; alpha146=>alpha146

(define idpc
  (predicate-form-to-predicate
   (pf "(PiOne (cterm (x^1535,x^1534) T))x^")))
(idpredconst-to-string idpc)
;; "(PiOne (cterm (x^1535,x^1534) T))"

(define aconst0 (number-and-idpredconst-to-intro-aconst 0 idpc))
(pp (rename-variables (aconst-to-formula aconst0)))
;; all x^,y^(R x^ y^ -> (PiOne (cterm (x^0,x^1) T))x^)

(proof-to-extracted-term (make-proof-in-aconst-form aconst0))
;; eps

(define aconst
  (imp-formulas-to-elim-aconst
   (pf "(PiOne (cterm (x^1544,x^1543) R x^1544 x^1543))x^ -> l=0")))
(pp (rename-variables (aconst-to-formula aconst)))

;; allnc x^,l(
;;  (PiOne (cterm (x^0,x^1) R x^0 x^1))x^ -> all x^0,y^(R x^0 y^ -> l=0) -> l=0)

(define idpc
  (predicate-form-to-predicate
   (pf "(TrCl (cterm (x^1535,x^1534) R x^1535 x^1534))x^ y^")))
(idpredconst-to-string idpc)
;; "(TrCl (cterm (x^1535,x^1534) R x^1535 x^1534))"

(define aconst0 (number-and-idpredconst-to-intro-aconst 0 idpc))
(pp (rename-variables (aconst-to-formula aconst0)))
;; allnc x^,y^(R x^ y^ -> (TrCl (cterm (x^0,x^1) R x^0 x^1))x^ y^)

(define eterm0 (proof-to-extracted-term (make-proof-in-aconst-form aconst0)))
(pp (term-to-type eterm0))
;; alpha=>lnat alpha

(define aconst
  (imp-formulas-to-elim-aconst
   (pf "(TrCl (cterm (x^1535,x^1534) R x^1535 x^1534))x^ y^ -> l=0")))
(pp (rename-variables (aconst-to-formula aconst)))

;; allnc x^,x^0,l(
;;  (TrCl (cterm (x^1,x^2) R x^1 x^2))x^ x^0 ->
;;  allnc x^1,y^(R x^1 y^ -> l=0) ->
;;  allnc x^1,y^,z^(
;;   R x^1 y^ -> (TrCl (cterm (x^2,x^3) R x^2 x^3))y^ z^ -> l=0 -> l=0) ->
;;  l=0)

(define idpc
  (idpredconst-name-and-types-and-cterms-to-idpredconst
   "Acc"
   (list (py "alpha")) '()))

(define aconst0 (number-and-idpredconst-to-intro-aconst 0 idpc))
(pp (aconst-to-formula aconst0))
;; allnc rel^,x^(F -> Acc rel^ x^)

(define eterm0 (proof-to-extracted-term (make-proof-in-aconst-form aconst0)))
(pp (term-to-type eterm0))
;; itree alpha

(define aconst1 (number-and-idpredconst-to-intro-aconst 1 idpc))
(pp (aconst-to-formula aconst1))
;; allnc rel^,x^(all y^(rel^ y^ x^ -> Acc rel^ y^) -> Acc rel^ x^)

(define eterm1 (proof-to-extracted-term (make-proof-in-aconst-form aconst1)))
(pp (term-to-type eterm1))
;; (alpha=>itree alpha)=>itree alpha

(define aconst (imp-formulas-to-elim-aconst (pf "Acc rel^ x^ -> l=0")))
(pp (rename-variables (aconst-to-formula aconst)))

;; allnc rel^,x^,l(
;;  Acc rel^ x^ ->
;;  allnc rel^0,x^0(F -> l=0) ->
;;  allnc rel^0,x^0(
;;   all y^(rel^0 y^ x^0 -> Acc rel^0 y^) -> all y^(rel^0 y^ x^0 -> l=0) -> l=0) ->
;;  l=0)

(define idpc (predicate-form-to-predicate (pf "(ExDT nat (cterm (n) n=m))")))
(idpredconst-to-string idpc)
;; "exd n n=m"

(define aconst0 (number-and-idpredconst-to-intro-aconst 0 idpc))
(pp (rename-variables (aconst-to-formula aconst0)))
;; allnc m all n(n=m -> exd n0 n0=m)

(define eterm0 (proof-to-extracted-term (make-proof-in-aconst-form aconst0)))
(pp (term-to-type eterm0))
;; nat=>nat

(define aconst (imp-formulas-to-elim-aconst (pf "exd n n=m -> l=0")))
(pp (rename-variables (aconst-to-formula aconst)))
;; allnc m,l(exd n n=m -> all n(n=m -> l=0) -> l=0)

(define idpc
  (idpredconst-name-and-types-and-cterms-to-idpredconst
   "Cup" (list (py "alpha"))
   (list (make-cterm (pv "x^") (pf "Q1 x^"))
	 (make-cterm (pv "x^") (pf "Q2 x^")))))

(define aconst0 (number-and-idpredconst-to-intro-aconst 0 idpc))
(pp (rename-variables (aconst-to-formula aconst0)))
;; all x^(Q1 x^ -> (Cup (cterm (x^0) Q1 x^0) (cterm (x^0) Q2 x^0))x^)

(define aconst1 (number-and-idpredconst-to-intro-aconst 1 idpc))
(pp (rename-variables (aconst-to-formula aconst1)))
;; all x^(Q2 x^ -> (Cup (cterm (x^0) Q1 x^0) (cterm (x^0) Q2 x^0))x^)

(define eterm (proof-to-extracted-term (make-proof-in-aconst-form aconst0)))
(pp (term-to-type eterm))
;; alpha164=>alpha164 ysum alpha163

(define aconst
  (imp-formulas-to-elim-aconst
   (pf "(Cup (cterm (x^) Q1 x^) (cterm (x^) Q2 x^))x^ -> A")))
(pp (rename-variables (aconst-to-formula aconst)))

;; allnc x^(
;;  (Cup (cterm (x^0) Q1 x^0) (cterm (x^0) Q2 x^0))x^ ->
;;  all x^0(Q1 x^0 -> A) -> all x^0(Q2 x^0 -> A) -> A)

(define eterm (proof-to-extracted-term (make-proof-in-aconst-form aconst)))
(pp (term-to-type eterm))
;; alpha164 ysum alpha163=>(alpha164=>alpha404)=>(alpha163=>alpha404)=>alpha404

(define idpc
  (idpredconst-name-and-types-and-cterms-to-idpredconst
   "Cap" (list (py "alpha"))
   (list (make-cterm (pv "x^") (pf "Q1 x^"))
	 (make-cterm (pv "x^") (pf "Q2 x^")))))

(define aconst0 (number-and-idpredconst-to-intro-aconst 0 idpc))
(pp (rename-variables (aconst-to-formula aconst0)))
;; all x^(Q1 x^ -> Q2 x^ -> (Cap (cterm (x^0) Q1 x^0) (cterm (x^0) Q2 x^0))x^)

(define eterm (proof-to-extracted-term (make-proof-in-aconst-form aconst0)))
(pp (term-to-type eterm))
;; alpha164=>alpha163=>alpha164 yprod alpha163

(define aconst
  (imp-formulas-to-elim-aconst
   (pf "(Cap (cterm (x^) Q1 x^) (cterm (x^) Q2 x^))x^ -> A")))
(pp (rename-variables (aconst-to-formula aconst)))

;; allnc x^(
;;  (Cap (cterm (x^0) Q1 x^0) (cterm (x^0) Q2 x^0))x^ ->
;;  all x^0(Q1 x^0 -> Q2 x^0 -> A) -> A)

(define eterm (proof-to-extracted-term (make-proof-in-aconst-form aconst)))
(pp (term-to-type eterm))
;; alpha164 yprod alpha163=>(alpha164=>alpha163=>alpha404)=>alpha404

;; Tests for imp-formulas-to-uninst-gfp-formulas-etc

(add-ids (list (list "I" (make-arity (py "nat") (py "nat")) "algI"))
	 '("all n allnc m^(I n m^)" "InitI"))

(add-co "I")

(pp (rename-variables (caar (imp-formulas-to-uninst-gfp-formulas-etc
			     (pf "n^ eqd m^ -> CoI n^ m^")))))

;; (Pvar nat nat)_250 n^1960 n^1959 ->
;; allnc n^,n^0(
;;  (Pvar nat nat)_250 n^ n^0 -> exl n1 exu m^(n^ eqd n1 andu n^0 eqd m^)) ->
;; CoI n^1960 n^1959

;; Hence we need cases andu exl exu in the internally defined
;; and-ex-fla-to-shortened-fla in
;; imp-formulas-to-uninst-gfp-formulas-etc.  Otherwise we get an error:

;; and-ex-fla-to-shortened-fla
;; unexpected formula
;; exl n exu m^(n^1954 eqd n andu n^1953 eqd m^)
