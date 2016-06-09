;; (load "~/git/minlog/init.scm")
(load "names.scm")

;; 11. Partial proofs
;; ==================
;; (pproof.scm)

(add-co "Even")

;; Tests for use

(pp "InitEqD")
;; allnc alpha^ alpha^ eqd alpha^

(set-goal "all n n eqd n")
(assume "n")
(use "InitEqD")

;; The next example shows that error messages in use-intern in case of
;; missing terms refer to the original variable in the used formula
;; even if such variables had to be renamed.

(pp "NatEqTrans")

;; all n,m,l(n=m -> m=l -> n=l)

(set-goal (pf "all n n=n"))
(assume "n")
;; (use "NatEqTrans")

;; use
;; more terms expected, to be substituted for
;; m

(use "NatEqTrans" (pt "n1"))

;; Tests for ind

(add-pvar-name "P" (make-arity (py "nat")))

(set-goal "all n P n")
(ind)

;; ok, ?_1 can be obtained from

;;   n3627
;; -----------------------------------------------------------------------------
;; ?_3:all n(P n -> P(Succ n))



;;   n3627
;; -----------------------------------------------------------------------------
;; ?_2:P 0

(set-goal "all n^(TotalNat n^ -> P n^)")
(assume "n^" "Tn")
(elim "Tn")

;; > ok, ?_2 can be obtained from

;;   n^  Tn:TotalNat n^
;; -----------------------------------------------------------------------------
;; ?_4:allnc n^(TotalNat n^ -> P n^ -> P(Succ n^))



;;   n^  Tn:TotalNat n^
;; -----------------------------------------------------------------------------
;; ?_3:P 0

(remove-pvar-name "P")
(add-pvar-name "P" (make-arity (py "ordl")))

(set-goal "all ordl P ordl")
(ind)

;; ok, ?_1 can be obtained from

;;   ordl3634
;; -----------------------------------------------------------------------------
;; ?_4:all (nat=>ordl)(all n P((nat=>ordl)n) -> P(OrdSup(nat=>ordl)))



;;   ordl3634
;; -----------------------------------------------------------------------------
;; ?_3:all ordl(P ordl -> P(OrdSucc ordl))



;;   ordl3634
;; -----------------------------------------------------------------------------
;; ?_2:P OrdZero

(remove-pvar-name "P")
(add-pvar-name "P" (make-arity (py "list nat")))
(add-var-name "ns" (py "list nat"))

(set-goal "all ns P ns")
(ind)

;; ok, ?_1 can be obtained from

;;   ns3638
;; -----------------------------------------------------------------------------
;; ?_3:all n,ns(P ns -> P(n::ns))



;;   ns3638
;; -----------------------------------------------------------------------------
;; ?_2:P(Nil nat)

(set-goal "all ns^(STotalList ns^ -> P ns^)")
(assume "ns^" "STns")
(elim "STns")

;; ok, ?_2 can be obtained from

;;   ns^  STns:STotalList ns^
;; -----------------------------------------------------------------------------
;; ?_4:allnc n^,ns^(STotalList ns^ -> P ns^ -> P(n^ ::ns^))



;;   ns^  STns:STotalList ns^
;; -----------------------------------------------------------------------------
;; ?_3:P(Nil nat)

(remove-pvar-name "P")
(remove-var-name "ns")
(add-pvar-name "P" (make-arity (py "list alpha")))

(set-goal "all xs P xs")
(ind)

;; ok, ?_1 can be obtained from

;;   xs3653
;; -----------------------------------------------------------------------------
;; ?_3:all x,xs(P xs -> P(x::xs))



;;   xs3653
;; -----------------------------------------------------------------------------
;; ?_2:P(Nil alpha)

(remove-pvar-name "P")

;; Tests for simind

(add-pvar-name "P" (make-arity (py "tree")))
(add-pvar-name "S" (make-arity (py "tlist")))

(set-goal "all tree P tree")
(simind (pf "all tlist S tlist"))

;; ok, ?_1 can be obtained from

;;   tree3657
;; -----------------------------------------------------------------------------
;; ?_5:all tlist(S tlist -> P(Branch tlist))



;;   tree3657
;; -----------------------------------------------------------------------------
;; ?_4:P Leaf



;;   tree3657
;; -----------------------------------------------------------------------------
;; ?_3:all tree,tlist0(P tree -> S tlist0 -> S(Tcons tree tlist0))



;;   tree3657
;; -----------------------------------------------------------------------------
;; ?_2:S Empty

;; An example for simind for infltlist

(remove-pvar-name "P" "S")

(add-pvar-name "P" (make-arity (py "infltree alpha")))
(add-pvar-name "S" (make-arity (py "infltlist alpha")))

(set-goal "all (infltree alpha) P (infltree alpha)")
(simind (pf "all (infltlist alpha) S (infltlist alpha)"))

;; ok, ?_1 can be obtained from

;;   (infltree alpha)_3674
;; -----------------------------------------------------------------------------
;; ?_6:all (nat=>infltree alpha)(
;;      all n P((nat=>infltree alpha)n) ->
;;      P((InfLLim alpha)(nat=>infltree alpha)))



;;   (infltree alpha)_3674
;; -----------------------------------------------------------------------------
;; ?_5:all (infltlist alpha)(
;;      S(infltlist alpha) -> P((InfLBranch alpha)(infltlist alpha)))



;;   (infltree alpha)_3674
;; -----------------------------------------------------------------------------
;; ?_4:all x P((InfLLeaf alpha)x)



;;   (infltree alpha)_3674
;; -----------------------------------------------------------------------------
;; ?_3:all (infltree alpha),(infltlist alpha)_0(
;;      P(infltree alpha) ->
;;      S(infltlist alpha)_0 ->
;;      S((InfLTcons alpha)(infltree alpha)(infltlist alpha)_0))



;;   (infltree alpha)_3674
;; -----------------------------------------------------------------------------
;; ?_2:S(InfLEmpty alpha)

(remove-pvar-name "P" "S")

;; Tests for cases

(add-pvar-name "P" (make-arity (py "nat")))

(set-goal "all n P n")
(cases)

;; ok, ?_1 can be obtained from

;;   n3691
;; -----------------------------------------------------------------------------
;; ?_3:all n P(Succ n)



;;   n3691
;; -----------------------------------------------------------------------------
;; ?_2:P 0

(remove-pvar-name "P")
(add-pvar-name "P" (make-arity (py "ordl")))

(set-goal "all ordl P ordl")
(cases)

;; ok, ?_1 can be obtained from

;;   ordl3695
;; -----------------------------------------------------------------------------
;; ?_4:all (nat=>ordl) P(OrdSup(nat=>ordl))



;;   ordl3695
;; -----------------------------------------------------------------------------
;; ?_3:all ordl P(OrdSucc ordl)



;;   ordl3695
;; -----------------------------------------------------------------------------
;; ?_2:P OrdZero

(remove-pvar-name "P")
(add-pvar-name "P" (make-arity (py "list alpha")))

(set-goal "all xs P xs")
(cases)

;; ok, ?_1 can be obtained from

;;   xs3699
;; -----------------------------------------------------------------------------
;; ?_3:all x,xs P(x::xs)



;;   xs3699
;; -----------------------------------------------------------------------------
;; ?_2:P(Nil alpha)

(remove-pvar-name "P")

;; Tests for elim.

(set-goal "allnc n^(Even n^ -> ex m n^ =m+m)")
(assume "n^")
(elim)
(ex-intro (pt "0"))
(use "Truth")
(assume "n^1" "Even n^1" "IH")
(by-assume "IH" "m" "n^1=m+m")
(ex-intro (pt "m+1"))
(ng)
(use "n^1=m+m")
;; Proof finished.

(define eterm (proof-to-extracted-term (current-proof)))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n](Rec nat=>nat)n 0([n0]Succ)

;; Test for elim with a simultaneous inductive definition.

;; "NatEvToHalf"
(set-goal "allnc n^(Ev n^ -> ex m n^ =m+m)")
(assume "n^" "En")
(elim "En" (pf "Od n^ -> ex m n^ =m+m+1"))

;; ok, ?_2 can be obtained from

;;   {n^}  En:Ev n^
;; -----------------------------------------------------------------------------
;; ?_5:allnc n^(Ev n^ -> ex m n^ =m+m -> ex m n^ +1=m+m+1)



;;   {n^}  En:Ev n^
;; -----------------------------------------------------------------------------
;; ?_4:allnc n^(Od n^ -> ex m n^ =m+m+1 -> ex m n^ +1=m+m)



;;   {n^}  En:Ev n^
;; -----------------------------------------------------------------------------
;; ?_3:ex m 0=m+m

(ex-intro (pt "0"))
(use "Truth")

(assume "n^1" "Useless" "ExHyp")
(drop "Useless")
(by-assume "ExHyp" "m" "mProp")
(ex-intro (pt "m+1"))
(ng #t)
(use "mProp")

(assume "n^1" "Useless" "ExHyp")
(drop "Useless")
(by-assume "ExHyp" "m" "mProp")
(ex-intro (pt "m"))
(ng #t)
(use "mProp")
;; Proof finished.

(define eterm (proof-to-extracted-term (current-proof)))
(pp (rename-variables eterm))

;; [algEv]
;;  (Rec algEv=>nat algOd=>nat)algEv(([m]m)0)
;;  ([algOd0,n]([m,(nat=>nat)_1](nat=>nat)_1 m)n([m]([m0]m0)(m+1)))
;;  ([algEv0,n]([m,(nat=>nat)_1](nat=>nat)_1 m)n([m]([m0]m0)m))

(define neterm (rename-variables (nt eterm)))

(pp neterm)
;; [algEv](Rec algEv=>nat algOd=>nat)algEv 0([algOd0]Succ)([algEv0,n]n)

;; NatOdToHalf
(set-goal "allnc n^(Od n^ -> ex m n^ =m+m+1)")
(assume "n^" "On")
(elim "On" (pf "Ev n^ -> ex m n^ =m+m"))

;; ok, ?_2 can be obtained from

;;   {n^}  On:Od n^
;; -----------------------------------------------------------------------------
;; ?_5:allnc n^(Ev n^ -> ex m n^ =m+m -> ex m n^ +1=m+m+1)



;;   {n^}  On:Od n^
;; -----------------------------------------------------------------------------
;; ?_4:allnc n^(Od n^ -> ex m n^ =m+m+1 -> ex m n^ +1=m+m)



;;   {n^}  On:Od n^
;; -----------------------------------------------------------------------------
;; ?_3:ex m 0=m+m

(ex-intro (pt "0"))
(use "Truth")

(assume "n^1" "Useless" "ExHyp")
(drop "Useless")
(by-assume "ExHyp" "m" "mProp")
(ex-intro (pt "m+1"))
(ng #t)
(use "mProp")

(assume "n^1" "Useless" "ExHyp")
(drop "Useless")
(by-assume "ExHyp" "m" "mProp")
(ex-intro (pt "m"))
(use "mProp")
;; Proof finished.

(define eterm (proof-to-extracted-term (current-proof)))
(pp (rename-variables eterm))

;; [algOd]
;;  (Rec algOd=>nat algEv=>nat)algOd(([m]m)0)
;;  ([algOd0,n]([m,(nat=>nat)_1](nat=>nat)_1 m)n([m]([m0]m0)(m+1)))
;;  ([algEv0,n]([m,(nat=>nat)_1](nat=>nat)_1 m)n([m]([m0]m0)m))

(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [algOd](Rec algOd=>nat algEv=>nat)algOd 0([algOd0]Succ)([algEv0,n]n)

;; For structural totality in infltlist we define

(add-ids
 (list (list "STotalInfltlist" (make-arity (py "infltlist alpha"))
	     "algSTotalInfltlist")
       (list "STotalInfltree" (make-arity (py "infltree alpha"))
	     "algSTotalInfltree"))
 '("STotalInfltlist(InfLEmpty alpha)" "STotalInfltlistInfLEmpty")
 '("allnc (infltree alpha)^,(infltlist alpha)^0(
 STotalInfltree(infltree alpha)^ ->
 STotalInfltlist(infltlist alpha)^0 ->
 STotalInfltlist((InfLTcons alpha)(infltree alpha)^(infltlist alpha)^0))"
   "STotalInfltlistInfLTcons")
 '("allnc alpha^ STotalInfltree((InfLLeaf alpha)alpha^)"
   "STotalInfltreeInfLLeaf")
 '("allnc (infltlist alpha)^(
 STotalInfltlist(infltlist alpha)^ ->
 STotalInfltree((InfLBranch alpha)(infltlist alpha)^))"
   "STotalInfltreeInfLBranch")
 '("allnc (nat=>infltree alpha)^(
 allnc n^(STotalInfltree((nat=>infltree alpha)^ n^)) ->
 STotalInfltree((InfLLim alpha)(nat=>infltree alpha)^))"
   "STotalInfltreeInfLLim"))

;; Tests for elim with a simultaneous inductive definition.

(add-pvar-name "P" (make-arity (py "infltree alpha")))
(add-pvar-name "S" (make-arity (py "infltlist alpha")))

(set-goal "all (infltree alpha)^(STotalInfltree(infltree alpha)^ ->
                                 P(infltree alpha)^)")
(assume "(infltree alpha)^")
(elim (pf "STotalInfltlist(infltlist alpha)^ -> S(infltlist alpha)^"))

;; ok, ?_2 can be obtained from

;;   (infltree alpha)^  1:STotalInfltree(infltree alpha)^
;; -----------------------------------------------------------------------------
;; ?_7:allnc (nat=>infltree alpha)^(
;;      allnc n^ STotalInfltree((nat=>infltree alpha)^ n^) ->
;;      allnc n^ P((nat=>infltree alpha)^ n^) ->
;;      P((InfLLim alpha)(nat=>infltree alpha)^))



;;   (infltree alpha)^  1:STotalInfltree(infltree alpha)^
;; -----------------------------------------------------------------------------
;; ?_6:allnc (infltlist alpha)^(
;;      STotalInfltlist(infltlist alpha)^ ->
;;      S(infltlist alpha)^ -> P((InfLBranch alpha)(infltlist alpha)^))



;;   (infltree alpha)^  1:STotalInfltree(infltree alpha)^
;; -----------------------------------------------------------------------------
;; ?_5:allnc alpha^ P((InfLLeaf alpha)alpha^)



;;   (infltree alpha)^  1:STotalInfltree(infltree alpha)^
;; -----------------------------------------------------------------------------
;; ?_4:allnc (infltree alpha)^,(infltlist alpha)^0(
;;      STotalInfltree(infltree alpha)^ ->
;;      P(infltree alpha)^ ->
;;      STotalInfltlist(infltlist alpha)^0 ->
;;      S(infltlist alpha)^0 ->
;;      S((InfLTcons alpha)(infltree alpha)^(infltlist alpha)^0))



;;   (infltree alpha)^  1:STotalInfltree(infltree alpha)^
;; -----------------------------------------------------------------------------
;; ?_3:S(InfLEmpty alpha)

(remove-pvar-name "P" "S")

;; Tests for EqD as a uniform one-clause defined idpredconst

(pp "InitEqD")
;; allnc alpha^ alpha^ eqd alpha^

(pp "EqDCompat")

;; allnc alpha^,alpha^0(
;;  alpha^ eqd alpha^0 --> (Pvar alpha)alpha^ -> (Pvar alpha)alpha^0)

;; EqDSym
(set-goal "allnc x^1,x^2(x^1 eqd x^2 -> x^2 eqd x^1)")
(assume "x^1" "x^2" "IdHyp")
(elim "IdHyp")
(use "InitEqD")
;; Proof finished.
(save "EqDSym")

;; EqDTrans
(set-goal "allnc x^1,x^2,x^3(x^1 eqd x^2 -> x^2 eqd x^3 -> x^1 eqd x^3)")
(assume "x^1" "x^2" "x^3" "IdHyp1")
(elim "IdHyp1")
(assume "x^" "IdHyp2")
(elim "IdHyp2")
(use "InitEqD")
;; Proof finished.
(save "EqDTrans")

(pp "EfqEqD")
;; F -> all alpha^,alpha^0 alpha^ eqd alpha^0

;; Tests for constructor-eqd-imp-args-eqd-proof,
;; constructors-overlap-imp-falsity-proof , inversion and
;; simplified-inversion

;; SuccInj
(set-goal "allnc n^,m^(Succ n^ eqd Succ m^ --> n^ eqd m^)")
(assume "n^" "m^"  "Sn=Sm")
(use (constructor-eqd-imp-args-eqd-proof (pf "Succ n^ eqd Succ m^")))
(use "Sn=Sm")
;; Proof finished.
(save "SuccInj")

;; EvenInversion
(set-goal "allnc n^(Even(Succ(Succ n^)) -> Even n^)")
(assume "n^" "ESSn")
(assert "allnc n^1(Even n^1 -> n^1 eqd Succ(Succ n^) -> Even n^)")
 (assume "n^1" "En1")
 (elim "En1")
 ;Base
 (assume "0=SSn")
 (use (formula-to-efq-proof (pf "Even n^")))
 (use "EqDTrueToAtom")
 (use (constructors-overlap-imp-falsity-proof (pf "0 eqd Succ(Succ n^)"))
      (pt "n^"))
 (use "0=SSn")
 ;Step
 (assume "n^2" "En2" "Useless" "SSn2=SSn")
 (assert "Succ n^2 eqd Succ n^")
  (use "SuccInj")
  (use "SSn2=SSn")
 (assume "Sn2=Sn")
 (assert "n^2 eqd n^")
  (use "SuccInj")
  (use "Sn2=Sn")
 (assume "n2=n")
 (simp-with "<-" "n2=n")
 (use "En2")

(assume "EqDAssertion")
(use "EqDAssertion" (pt "Succ(Succ n^)"))
(use "ESSn")
(use "InitEqD")
;; Proof finished.
(save "EvenInversion")

(define proof (theorem-name-to-proof "EvenInversion"))
;; (cdp proof) ;ok
;; (proof-to-expr-with-formulas proof)
(define nproof (np proof))
;; (cdp nproof) ;ok
;; (proof-to-expr-with-formulas nproof)

(define eterm (proof-to-extracted-term proof))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)
;; [n][case n (0 -> 0) (Succ n0 -> n0)]

;; Test for inversion for a simultaneous inductive definition.
;; Context: Tait's normalization proof.  Substitutions in
;; Hancock/Joachimski style, with a trailing number.  Inductive
;; definition of "WN", simultaneously with "WNs".

(add-algs "type"
	 '("type" "Iota")
	 '("type=>type=>type" "Arrow"))

(add-infix-display-string "Arrow" "to" 'pair-op)

(add-var-name "rho" "sig" "tau" (py "type"))

(add-program-constant "Argtyp" (py "type=>type") 1)
(add-program-constant "Valtyp" (py "type=>type") 1)
(add-program-constant "Arrowtyp" (py "type=>boole") 1)

(add-computation-rule (pt "Argtyp Iota") (pt "Iota"))
(add-computation-rule (pt "Valtyp Iota") (pt "Iota"))
(add-computation-rule (pt "Argtyp(rho to sig)") (pt "rho"))
(add-computation-rule (pt "Valtyp(rho to sig)") (pt "sig"))

(add-computation-rule (pt "Arrowtyp Iota") (pt "False"))
(add-computation-rule (pt "Arrowtyp(rho to sig)") (pt "True"))

(add-algs "term"
	 '("nat=>term" "Var")
	 '("term=>term=>term" "App")
	 '("type=>term=>term" "Abs"))

;; Application for terms is via the constant App.

(add-new-application
 (lambda (type)
   (and (alg-form? type)
	(string=? "term" (alg-form-to-name type))))
 (lambda (term1 term2)
   (mk-term-in-app-form
    (make-term-in-const-form (constr-name-to-constr "App"))
    term1 term2)))

(add-new-application-syntax
 ;; predicate
 (lambda (term)
   (and (term-in-app-form? term)
	(let ((op (term-in-app-form-to-op term)))
	  (and (term-in-app-form? op)
	       (let ((opop (term-in-app-form-to-op op)))
		 (and (term-in-const-form? opop)
		      (let ((const (term-in-const-form-to-const opop)))
			(and (eq? 'constr (const-to-kind const))
			     (string=? "App" (const-to-name const))))))))))
 ;; to arg
 (lambda (term)
   (term-in-app-form-to-arg term))
 ;; to op
 (lambda (term)
   (term-in-app-form-to-arg
    (term-in-app-form-to-op term))))

(remove-var-name "r")
(add-var-name "r" "s" "t" (py "term"))
(add-var-name "rs" "ss" "ts" (py "list term"))
(add-var-name "rhos" "sigs" "taus" (py "list type")) ;used for contexts

(add-program-constant "Typ" (py "list type=>term=>type") 1)

(add-computation-rules
 "Typ(Nil type)(Var n)" "Iota"
 "Typ(rho::rhos)(Var 0)" "rho"
 "Typ(rho::rhos)(Var(Succ n))" "Typ rhos(Var n)"
 "Typ rhos(r s)" "Valtyp(Typ rhos r)"
 "Typ rhos(Abs rho r)" "rho to Typ(rho::rhos)r")

;; (add-totality "type")
;; (add-totality "term")

;; ;; "TypTotal"
;; (set-goal (term-to-totality-formula (pt "Typ")))
;; (assume "rhos^" "Trhos")
;; (elim "Trhos")
;; (assume "r^" "Tr")
;; (elim "Tr")
;; (assume "n^" "Tn")
;; (ng #t)
;; (use "TotalTypeIota")
;; (assume "r^1" "r^2" "Tr1" "Tr2" "TTyr1" "TTyr2")
;; (ng #t)
;; To be completed

(add-program-constant "Cor" (py "list type=>term=>boole") 1)

(add-computation-rules
 "Cor rhos(Var n)" "n<Lh rhos"
 "Cor rhos(r s)" "Cor rhos r and Cor rhos s and
                  Typ rhos r=(Typ rhos s to Valtyp(Typ rhos r))"
 "Cor rhos(Abs rho r)" "Cor(rho::rhos)r")

(add-program-constant "Lift" (py "term=>nat=>nat=>term") 1)

(add-var-name "k" (py "nat"))

(add-computation-rules
 "Lift(Var n)l k" "[if (n<l) (Var n) (Var(n+k))]"
 "Lift(r s)l k" "(Lift r l k)(Lift s l k)"
 "Lift(Abs rho r)l k" "Abs rho(Lift r(l+1)k)")

;; Substitution in the style of Hancock/Joachimski

(add-algs "sub"
	 '("nat=>sub" "Up")
	 '("term=>sub=>sub" "Dot"))

(add-var-name "theta" (py "sub"))

(add-program-constant "Sublift" (py "sub=>nat=>sub") 1)

(add-computation-rules
 "Sublift(Up m)n" "Up(m+n)"
 "Sublift(Dot r theta)n" "Dot(Lift r 0 n)(Sublift theta n)")

;; For convenience we view a substitution as a pair of a list of terms
;; and a number.

(add-program-constant "Mksub" (py "list term=>nat=>sub") 1)

(add-computation-rules
 "Mksub(Nil term)n" "Up n"
 "Mksub(r::rs)n" "Dot r(Mksub rs n)")

(add-program-constant "Sublist" (py "sub=>list term") 1)

(add-computation-rules
 "Sublist(Up n)" "(Nil term)"
 "Sublist(Dot r theta)" "r::(Sublist theta)")

(add-program-constant "Subup" (py "sub=>nat") 1)

(add-computation-rules
 "Subup(Up n)" "n"
 "Subup(Dot r theta)" "Subup theta")

;; Sub r theta substitutes theta in the term r

(add-program-constant "Sub" (py "term=>sub=>term") 1)

(add-computation-rules
 "Sub(Var n)(Up m)" "Var(n+m)"
 "Sub(Var 0)(Dot r theta)" "r"
 "Sub(Var(Succ n))(Dot r theta)" "Sub(Var n)theta"
 "Sub(r s)theta" "(Sub r theta)(Sub s theta)"
 "Sub(Abs rho r)theta" "(Abs rho(Sub r(Dot(Var 0)(Sublift theta 1))))")

;; Wrap n rs wraps up a list of terms to a Sublist with a parameter for lifting

(add-program-constant "Wrap" (py "nat=>list term=>sub") 1)

(add-computation-rules
 "Wrap n(Nil term)" "Up n"
 "Wrap n(r::rs)" "Dot r(Wrap n rs)")

;; Eta is the outer eta expansion
(add-program-constant "Eta" (py "type=>term=>term") 1)

(add-computation-rules
 "Eta Iota r" "r"
 "Eta(rho to sig)r" "Abs rho(Eta sig(Lift r 0 1(Eta rho(Var 0))))")

(pp (nt (pt "Eta(Iota to Iota)(Var 0)")))
(pp (nt (pt "Eta(Iota to Iota)(Var 7)")))
(pp (nt (pt "Eta((Iota to Iota)to(Iota to Iota))(Var 7)")))

;; Notice that the "1" (i.e., the totality) of Eta must be proved.
;; This is easy, by induction on types.

;; Exp is full eta expansion.  It is defined simultaneously with IExp,
;; the inner eta expansion.

(add-program-constant "Exp" (py "list type=>type=>term=>term") 1)
(add-program-constant "IExp" (py "list type=>term=>term") 1)

(add-computation-rule (pt "Exp rhos rho(Var n)") (pt "Eta rho(Var n)"))
(add-computation-rule (pt "Exp rhos rho(r s)")
		      (pt "Eta rho(IExp rhos(r s))"))
(add-computation-rule (pt "Exp rhos tau(Abs rho r)")
		      (pt "Abs rho(Exp(rho::rhos)(Valtyp tau)r)"))

(add-computation-rule (pt "IExp rhos(Var n)") (pt "Var n"))
(add-computation-rule (pt "IExp rhos(r s)")
		      (pt "IExp rhos r(Exp rhos(Typ rhos s)s)"))

;; Notice that the "1" (i.e., the totality) of Exp and IExp must be
;; proved.  This is easy, by induction on terms (simultaneously).

(pp (pt "Abs rho(Abs sig(Var 1))")) ;K
(pp (pt "Abs(rho to sig to rho)
          (Abs(rho to sig)
            (Abs rho(Var 2(Var 0)(Var 1(Var 0)))))")) ;S

(define sterm
  (pt "Abs((Iota to Iota) to Iota to (Iota to Iota))
          (Abs((Iota to Iota) to Iota)
            (Abs (Iota to Iota)(Var 2(Var 0)(Var 1(Var 0)))))"))
(define stype (mk-term-in-app-form (pt "Typ") (pt "(Nil type)") sterm))
(pp stype)
(pp (nt stype))

(pp (nt (mk-term-in-app-form (pt "Exp(Nil type)") stype sterm)))

(add-program-constant "FoldApp" (py "term => list term => term") 1)

(add-computation-rules
 "FoldApp r(Nil term)" "r"
 "FoldApp r(s::ss)" "FoldApp(r s)ss")

;; (pp (nt (pt "FoldApp r(s::t:)")))
;; => r s t

;; Inductive definition of "WN", simultaneously with "WNs".

(add-ids
 (list (list "WNs" (make-arity (py "list term") (py "list term")) "algWNs")
       (list "WN" (make-arity (py "term") (py "term")) "algWN"))
 '("WNs(Nil term)(Nil term)" "WNsNil")
 '("all r,s,rs,ss(WN r s -> WNs rs ss -> WNs(r::rs)(s::ss))" "WNsCons")
 '("all n,rs,ss(WNs rs ss -> WN(FoldApp(Var n)rs)(FoldApp(Var n)ss))" "WNVar")
 '("all rho,r,s(WN r s -> WN(Abs rho r)(Abs rho s))" "WNAbs")
 '("all rho,r,s,t,rs(WN(FoldApp(Sub r(Wrap 0(s:)))rs)t ->
     WN(FoldApp(Abs rho r)(s::rs))t)" "WNBeta"))

(set-goal "all r,s,rs,ss(WNs(r::rs)(s::ss) -> WNs rs ss)")
(assume "r" "s" "rs" "ss" "WNs(r::rs)(s::ss)")
(simplified-inversion "WNs(r::rs)(s::ss)")
(assume "r1" "s1" "rs1" "ss1")
(assume "WNs rs1 ss1" "H1" "(r::rs)=(r1::rs1)" "(s::ss)=(s1::ss1)")
(ng)
(inst-with-to "(r::rs)=(r1::rs1)" 'right "rs=rs1")
(simp "rs=rs1")
(inst-with-to "(s::ss)=(s1::ss1)" 'right "ss=ss1")
(simp "ss=ss1")
(use "WNs rs1 ss1")
;; Proof finished.
;; (cdp)
;; (cdp (np (current-proof)))

(set-goal "all r,rs,ss(WNs(r::rs)ss -> ss=(Nil term) -> F)")
(assume "r" "rs" "ss" "H1")
(simplified-inversion "H1")
(assume "r1" "s1" "rs1" "ss1" "H2" "H3" "H4" "H5")
(simp "H5")
(prop)
;; Proof finished.
;; (cdp)
;; (cdp (np (current-proof)))

;; WNTest0
(set-goal "all rs,ss(WNs rs ss -> rs=(Nil term) -> ss=(Nil term))")
(assume "rs" "ss")
(elim)
(prop)
(strip)
(prop)
;; Proof finished.
;; (cdp)

;; WNsNil
(set-goal "all ss(WNs(Nil term)ss -> ss=(Nil term))")
(assume "ss" "H1")
(simplified-inversion "H1")
(prop)
;; Proof finished.
;; (cdp)
;; (cdp (np (current-proof)))

;; "WNsApp"
(set-goal "all rs1,ss1,rs2,ss2(
                WNs rs1 ss1 -> WNs rs2 ss2 -> WNs(rs1:+:rs2)(ss1:+:ss2))")
(ind)
(cases)

(strip)
(ng)
(use 2)

(strip)
(simplified-inversion 1)

(assume "r1" "rs1" "IH")
(cases)
(strip)
(simplified-inversion 2)

(assume "s1" "ss1" "rs2" "ss2" "H")
(inversion "H")
(assume "r" "s" "rs" "ss")
(strip)
(ng)
(inst-with-to 7 'left "r1=r")
(simp "r1=r")
(inst-with-to 8 'left "s1=s")
(simp "s1=s")
(use "WNsCons")
(use 4)
(use "IH")
(inst-with-to 7 'right "rs1=rs")
(simp "rs1=rs")
(inst-with-to 8 'right "ss1=ss")
(simp "ss1=ss")
(use 5)
(use 9)
;; Proof finished
;; (save "WNsApp")
;; (cdp)
;; (cdp (np (current-proof)))

;; Inductive definition of "H" meaning "has a head normal form"

(add-ids
 (list (list "H" (make-arity (py "term")) "algH"))
 '("all n,rs H(FoldApp(Var n)rs)" "HVar")
 '("all rho,r(H r -> H(Abs rho r))" "HAbs")
 '("all rho,r,s,rs(H(FoldApp(Sub r(Wrap 0(s:)))rs) ->
     H(FoldApp(Abs rho r)(s::rs)))" "HBeta"))

(set-goal "all r,s(WN r s -> H r)")
(assume "r" "s")
(elim)
(strip)
(use "HVar")
(strip)
(use "HAbs")
(use 3)
(strip)
(use "HBeta")
(use 3)
;; Proof finished.
;; (cdp)
;; (cdp (np (current-proof)))

(define eterm (proof-to-extracted-term (current-proof)))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [r,r0,algWN]
;;  (Rec algWN=>algH)algWN([n,rs,rs0]CHVar n rs)
;;  ([rho,r1,r2,algWN0]CHAbs rho r1)
;;  ([rho,r1,r2,r3,rs,algWN0]CHBeta rho r1 r2 rs)

(remove-idpc-name "H")
(remove-idpc-name "WN")

(remove-var-name "k" "rho" "sig" "tau"
		 "r" "s" "t"
		 "rs" "ss" "ts"
		 "rhos" "sigs" "taus"
		 "theta")

(remove-alg-name "type" "term" "sub")

(add-var-name "r" (py "alpha=>alpha=>boole"))

;; Tests for coinduction.  For allnc n^(CoEven n^ -> CoEven(n^ +2)) we
;; proceed similar to inversion, but by hand.

;; CoEvenInvAux
(set-goal "allnc n^(exr m^(n^ eqd m^ +2 & CoEven m^) -> CoEven n^)")
(assume "m^" "Exm")
(coind "Exm")
(assume "n^1" "Exn1")
(by-assume "Exn1" "n^2" "n2Prop")
(intro 1)
(intro 0 (pt "n^2"))
(split)
(intro 0)
(use "n2Prop")
(use "n2Prop")
;; Proof finished.
(save "CoEvenInvAux")

;; Now we can derive the original goal.

;; CoEvenInv
(set-goal "allnc n^(CoEven n^ -> CoEven(n^ +2))")
(assume "n^" "CoEven n^")
(use "CoEvenInvAux")
(intro 0 (pt "n^"))
(split)
(use "InitEqD")
(use "CoEven n^")
;; Proof finished.
(save "CoEvenInv")

;; Tests for simultaneous coinduction.

(add-var-name "ts" (py "tlist"))
(add-var-name "t" (py "tree"))

(add-totality "tlist")
(add-co "TotalTlist")

(display-idpc "CoTotalTlist" "CoTotalTree")

;; CoTotalTlist
;; 	CoTotalTlistClause:	allnc ts^(
;;  CoTotalTlist ts^ -> 
;;  ts^ eqd Empty orr 
;;  exr t^(
;;   CoTotalTree t^ & exr ts^0(CoTotalTlist ts^0 andl ts^ eqd Tcons t^ ts^0)))
;; CoTotalTree
;; 	CoTotalTreeClause:	allnc t^(
;;  CoTotalTree t^ -> 
;;  t^ eqd Leaf orr exr ts^(CoTotalTlist ts^ andl t^ eqd Branch ts^))

;; We prove inversion properties for the constructors Branch and Tcons.

;; CoTotalTlistInvBranch
(pp (pf "allnc ts^(CoTotalTlist ts^ -> CoTotalTree(Branch ts^))"))

;; CoTotalTreeInvTcons
(pp (pf "allnc t^,ts^(
         CoTotalTree t^ -> CoTotalTlist ts^ -> CoTotalTlist(Tcons t^ ts^))"))

;; This uses the greatest-fixed-point axiom.  For TotalTlistInvBranch
;; we take as the first implication formula one with CoTotalTree in the
;; conclusion.

(pp (rename-variables
     (aconst-to-formula
      (imp-formulas-to-gfp-aconst
       (pf "exr ts^(t^ eqd Branch ts^ & CoTotalTlist ts^) -> CoTotalTree t^")
       (pf "exr t^,ts^1(
             ts^ eqd Tcons t^ ts^1 & CoTotalTree t^ & CoTotalTlist ts^1) ->
            CoTotalTlist ts^")))))

;; allnc t^(
;;  exr ts^(t^ eqd Branch ts^ & CoTotalTlist ts^) ->
;;  allnc ts^(
;;   exr t^0,ts^0(ts^ eqd Tcons t^0 ts^0 & CoTotalTree t^0 & CoTotalTlist ts^0) ->
;;   ts^ eqd Empty orr
;;   exr t^0(
;;    (CoTotalTree t^0 ord exr ts^0(t^0 eqd Branch ts^0 & CoTotalTlist ts^0)) &
;;    exr ts^0(
;;     (CoTotalTlist ts^0 ord
;;      exr t^1,ts^1(ts^0 eqd Tcons t^1 ts^1 & CoTotalTree t^1 & CoTotalTlist ts^1)) andl
;;     ts^ eqd Tcons t^0 ts^0))) ->
;;  allnc t^0(
;;   exr ts^(t^0 eqd Branch ts^ & CoTotalTlist ts^) ->
;;   t^0 eqd Leaf orr
;;   exr ts^(
;;    (CoTotalTlist ts^ ord
;;     exr t^1,ts^0(ts^ eqd Tcons t^1 ts^0 & CoTotalTree t^1 & CoTotalTlist ts^0)) andl
;;    t^0 eqd Branch ts^)) ->
;;  CoTotalTree t^)

;; CoTotalTlistInvBranchAux
(set-goal
 "allnc t^(exr ts^(t^ eqd Branch ts^ & CoTotalTlist ts^) -> CoTotalTree t^)")
(assume "t^" "Exl")
(coind "Exl" (pf "exr t^,ts^1(
                  ts^ eqd Tcons t^ ts^1 & CoTotalTree t^ & CoTotalTlist ts^1) ->
                  CoTotalTlist ts^"))
;; ?_3:allnc ts^(
;;      exr t^,ts^0(ts^ eqd Tcons t^ ts^0 & CoTotalTree t^ & CoTotalTlist ts^0) ->
;;      ts^ eqd Empty orr
;;      exr t^(
;;       (CoTotalTree t^ ord exr ts^0(t^ eqd Branch ts^0 & CoTotalTlist ts^0)) &
;;       exr ts^0(
;;        (CoTotalTlist ts^0 ord
;;         exr t^0,ts^1(
;;          ts^0 eqd Tcons t^0 ts^1 & CoTotalTree t^0 & CoTotalTlist ts^1)) andl
;;        ts^ eqd Tcons t^ ts^0)))

(drop "Exl")
(assume "ts^" "Ext1l1")
(intro 1)
(by-assume "Ext1l1" "t^1" "t1Prop")
(by-assume "t1Prop" "ts^1" "t1l1Prop")
(intro 0 (pt "t^1"))
(split)
(intro 0)
(use "t1l1Prop")
(intro 0 (pt "ts^1"))
(split)
(intro 0)
(use "t1l1Prop")
(use "t1l1Prop")

;; ?_4:allnc t^(
;;      exr ts^(t^ eqd Branch ts^ & CoTotalTlist ts^) ->
;;      t^ eqd Leaf orr
;;      exr ts^(
;;       (CoTotalTlist ts^ ord
;;        exr t^0,ts^0(
;;         ts^ eqd Tcons t^0 ts^0 & CoTotalTree t^0 & CoTotalTlist ts^0)) andl
;;       t^ eqd Branch ts^))

(drop "Exl")
(assume "t^1" "Exl1")
(intro 1)
(by-assume "Exl1" "ts^1" "l1Prop")
(intro 0 (pt "ts^1"))
(split)
(intro 0)
(use "l1Prop")
(use "l1Prop")
;; Proof finished.
(save "CoTotalTlistInvBranchAux")

;; CoTotalTlistInvBranch
(set-goal "allnc ts^(CoTotalTlist ts^ -> CoTotalTree(Branch ts^))")
(assume "ts^" "CoTl")
(use "CoTotalTlistInvBranchAux")
(intro 0 (pt "ts^"))
(split)
(use "InitEqD")
(use "CoTl")
;; Proof finished.
(save "CoTotalTlistInvBranch")

(animate "CoTotalTlistInvBranchAux")

(define eterm
  (proof-to-extracted-term (theorem-name-to-proof "CoTotalTlistInvBranch")))
(define neterm (rename-variables (nt eterm)))

(pp neterm)

;; [ts]
;;  (CoRec tlist=>tree tree@@tlist=>tlist)ts
;;  ([(tree@@tlist)]
;;    Inr((InL tree tlist)left(tree@@tlist)@
;;        (InL tlist tree@@tlist)right(tree@@tlist)))
;;  ([ts0]Inr((InL tlist tree@@tlist)ts0))

;; For CoTotalTreeInvTcons we take as the first implication formula one
;; with CoTotalTlist in the conclusion.

(pp 
 (rename-variables
  (aconst-to-formula
   (imp-formulas-to-gfp-aconst
    (pf "exr t^,ts^1(
             ts^ eqd Tcons t^ ts^1 & CoTotalTree t^ & CoTotalTlist ts^1) ->
            CoTotalTlist ts^")
    (pf "exr ts^(t^ eqd Branch ts^ & CoTotalTlist ts^) -> CoTotalTree t^")))))

;; allnc ts^(
;;  exr t^,ts^0(ts^ eqd Tcons t^ ts^0 & CoTotalTree t^ & CoTotalTlist ts^0) ->
;;  allnc ts^0(
;;   exr t^,ts^1(ts^0 eqd Tcons t^ ts^1 & CoTotalTree t^ & CoTotalTlist ts^1) ->
;;   ts^0 eqd Empty orr
;;   exr t^(
;;    (CoTotalTree t^ ord exr ts^1(t^ eqd Branch ts^1 & CoTotalTlist ts^1)) &
;;    exr ts^1(
;;     (CoTotalTlist ts^1 ord
;;      exr t^0,ts^2(ts^1 eqd Tcons t^0 ts^2 & CoTotalTree t^0 & CoTotalTlist ts^2)) andl
;;     ts^0 eqd Tcons t^ ts^1))) ->
;;  allnc t^(
;;   exr ts^0(t^ eqd Branch ts^0 & CoTotalTlist ts^0) ->
;;   t^ eqd Leaf orr
;;   exr ts^0(
;;    (CoTotalTlist ts^0 ord
;;     exr t^0,ts^1(ts^0 eqd Tcons t^0 ts^1 & CoTotalTree t^0 & CoTotalTlist ts^1)) andl
;;    t^ eqd Branch ts^0)) ->
;;  CoTotalTlist ts^)

;; CoTotalTreeInvTconsAux
(set-goal
 "allnc ts^(exr t^,ts^1(
            ts^ eqd Tcons t^ ts^1 & CoTotalTree t^ & CoTotalTlist ts^1) ->
            CoTotalTlist ts^)")
(assume "ts^" "Extl")
(coind "Extl"
       (pf "exr ts^(t^ eqd Branch ts^ & CoTotalTlist ts^) -> CoTotalTree t^"))

;; ?_3:allnc ts^(
;;      exr t^,ts^0(ts^ eqd Tcons t^ ts^0 & CoTotalTree t^ & CoTotalTlist ts^0) ->
;;      ts^ eqd Empty orr
;;      exr t^(
;;       (CoTotalTree t^ ord exr ts^0(t^ eqd Branch ts^0 & CoTotalTlist ts^0)) &
;;       exr ts^0(
;;        (CoTotalTlist ts^0 ord
;;         exr t^0,ts^1(
;;          ts^0 eqd Tcons t^0 ts^1 & CoTotalTree t^0 & CoTotalTlist ts^1)) andl
;;        ts^ eqd Tcons t^ ts^0)))

(drop "Extl")
(assume "ts^1" "Ext2l2")
(intro 1)
(by-assume "Ext2l2" "t^2" "t2Prop")
(by-assume "t2Prop" "ts^2" "t2l2Prop")
(intro 0 (pt "t^2"))
(split)
(intro 0)
(use "t2l2Prop")
(intro 0 (pt "ts^2"))
(split)
(intro 0)
(use "t2l2Prop")
(use "t2l2Prop")

;; ?_4:allnc t^(
;;      exr ts^(t^ eqd Branch ts^ & CoTotalTlist ts^) ->
;;      t^ eqd Leaf orr
;;      exr ts^(
;;       (CoTotalTlist ts^ ord
;;        exr t^0,ts^0(
;;         ts^ eqd Tcons t^0 ts^0 & CoTotalTree t^0 & CoTotalTlist ts^0)) andl
;;       t^ eqd Branch ts^))

(drop "Extl")
(assume "t^1" "Exl1")
(intro 1)
(by-assume "Exl1" "ts^1" "l1Prop")
(intro 0 (pt "ts^1"))
(split)
(intro 0)
(use "l1Prop")
(use "l1Prop")
;; Proof finished.
(save "CoTotalTreeInvTconsAux")

;; CoTotalTreeInvTcons
(set-goal "allnc t^,ts^(
         CoTotalTree t^ -> CoTotalTlist ts^ -> CoTotalTlist(Tcons t^ ts^))")
(assume "t^" "ts^" "CoTt" "CoTl")
(use "CoTotalTreeInvTconsAux")
(intro 0 (pt "t^"))
(intro 0 (pt "ts^"))
(split)
(use "InitEqD")
(split)
(use "CoTt")
(use "CoTl")
;; Proof finished.
(save "CoTotalTreeInvTcons")

(animate "CoTotalTreeInvTconsAux")

(define eterm
  (proof-to-extracted-term (theorem-name-to-proof "CoTotalTreeInvTcons")))
(define neterm (rename-variables (nt eterm)))

(pp neterm)

;; [t,ts]
;;  (CoRec tree@@tlist=>tlist tlist=>tree)(t@ts)
;;  ([(tree@@tlist)]
;;    Inr((InL tree tlist)left(tree@@tlist)@
;;        (InL tlist tree@@tlist)right(tree@@tlist)))
;;  ([ts0]Inr((InL tlist tree@@tlist)ts0))

(remove-var-name "ts" "t")

;; Tests for search.

;; (set! VERBOSE-SEARCH #t)

(set-goal "all y(all z R y z -> A) -> all y1,y2 R y1 y2 -> A")
(search)

(proof-to-expr-with-formulas (current-proof))

;; u2164: all y(all z R y z -> A)
;; u2165: all y,y0 R y y0

;; (lambda (u2164)
;;   (lambda (u2165) ((u2164 y) (lambda (z) ((u2165 y) z)))))

;; Contains y free.

;; Drinker
(set-goal "all y(((Q y -> F) -> F) -> Q y) -> exca x(Q x -> all y Q y)")
(assume "StabQ" "FHyp")
(use "FHyp" (pt "(Inhab alpha)"))
(assume "QInhab" "y")
(use "StabQ")
(assume "NotQy")
(use "FHyp" (pt "y"))
(assume "Qy" "z")
(use "StabQ")
(assume "NotQz")
(use "NotQy")
(use "Qy")
;; Proof finished.

(proof-to-expr-with-formulas (current-proof))

;; StabQ: all y(((Q y -> F) -> F) -> Q y)
;; FHyp: all x((Q x -> all y Q y) -> F)
;; QInhab: Q(Inhab alpha)
;; NotQy: Q y -> F
;; Qy: Q y
;; NotQz: Q z -> F

;; (lambda (StabQ)
;;   (lambda (FHyp)
;;     ((FHyp inhab)
;;       (lambda (QInhab)
;;         (lambda (y)
;;           ((StabQ y)
;;             (lambda (NotQy)
;;               ((FHyp y)
;;                 (lambda (Qy)
;;                   (lambda (z)
;;                     ((StabQ z) (lambda (NotQz) (NotQy Qy)))))))))))))

(set-goal "all y(((Q y -> F) -> F) -> Q y) -> exca x(Q x -> all y Q y)")
(search)
;; Proof finished.

(proof-to-expr-with-formulas (current-proof))

;; u: all y(((Q y -> F) -> F) -> Q y)
;; u0: all x((Q x -> all y Q y) -> F)
;; u1: Q x
;; u2: Q y -> F
;; u3: Q y
;; u4: Q y9416 -> F

;; (lambda (u)
;;   (lambda (u0)
;;     ((u0 x)
;;       (lambda (u1)
;;         (lambda (y)
;;           ((u y)
;;             (lambda (u2)
;;               ((u0 y)
;;                 (lambda (u3)
;;                   (lambda (y9416)
;;                     ((u y9416) (lambda (u4) (u2 u3)))))))))))))

;; Contains x free.

;; Test for mk-imp-impnc-formula

(pp (mk-imp-impnc-formula (pf "T") #f (pf "Pvar") #t (pf "bot")))
;; T -> Pvar --> bot

;; Tests for simp and simphyp-to

(add-var-name "f" (py "nat=>boole"))

(set-goal "all f,n,m(n=m -> f n -> [if (f m) False True]=f n)")
(assume "f" "n" "m" "EqHyp" "fHyp")

;;   f  n  m  EqHyp:n=m
;;   fHyp:f n
;; -----------------------------------------------------------------------------
;; ?_2:[if (f m) False True]=f n

(simp "EqHyp")

;; [if (f m) False True]=f m

(undo)
(simp "<-" "EqHyp")

;; [if (f n) False True]=f n

(undo)
(simphyp-to "fHyp" "EqHyp" "fHypSimp")

;;   f  n  m  EqHyp:n=m
;;   fHyp:f n
;;   fHypSimp:f m
;; -----------------------------------------------------------------------------
;; ?_4:[if (f m) False True]=f n
