;; (load "~/minlog/init.scm")
(load "names.scm")

; 4. Constants
; ============
; (pconst.scm)

; Tests for (constructor-type-to-step-type type alg-names-with-types)

(for-each
 (lambda (type) (pp (constructor-type-to-step-type
		     type (list (list "ltlist" (py "nat"))
				(list "ltree" (py "boole"))))))
 (map typed-constr-name-to-type
      (apply append (map alg-name-to-typed-constr-names
			 (alg-name-to-simalg-names "ltlist")))))

;; nat
;; ltree alpha=>boole=>ltlist alpha=>nat=>nat
;; alpha=>boole
;; ltlist alpha=>nat=>boole

(for-each
 (lambda (type) (pp (constructor-type-to-step-type
		     type (list (list "ltlist" (py "nat"))))))
 (map typed-constr-name-to-type
      (apply append (map alg-name-to-typed-constr-names
			 (list "ltlist")))))

;; nat
;; ltlist alpha=>nat=>nat

(for-each
 (lambda (type) (pp (constructor-type-to-step-type
		     type (list (list "ltree" (py "boole"))))))
 (map typed-constr-name-to-type
      (apply append (map alg-name-to-typed-constr-names
			 (list "ltree")))))

;; alpha=>boole
;; boole

;; Tests for rec-at when used for normalizing proofs with Elim/Intro.

(add-var-name "l" "i" "j" (py "nat"))
(add-var-name "ns" (py "list nat"))
(add-pvar-name "P" (make-arity (py "nat")))

;; PList is RTotalList instantiated with nat.

(add-ids
 (list (list "PList" (make-arity (py "list nat")) "list"))
 '("PList(Nil nat)" "PListNil")
 '("allnc n^(P n^ -> allnc ns^(PList ns^ -> PList(n^ ::ns^)))" "PListCons"))

(display-idpc "PList")
;; PList
;; 	PListNil:	(PList (cterm (n^) P n^))(Nil nat)
;; 	PListCons:	allnc n^(
;;  P n^ ->
;;  allnc ns^(
;;   (PList (cterm (n^0) P n^0))ns^ -> (PList (cterm (n^0) P n^0))(n^ ::ns^)))

;; Instantiate P with a predicate depending on a parameter m^:
;; (pp (pf "(PList (cterm (n^) ex n^1 n^1*m^ eqd n^))ns^"))

;; Check that the idpc-cterm-var m^ is generalized outside in
;; intro-aconsts

(define idpc
  (idpredconst-name-and-types-and-cterms-to-idpredconst
   "PList" '()
   (list (make-cterm (pv "n^") (pf "ex n^1 n^1*m^ eqd n^")))))

(define aconst0 (number-and-idpredconst-to-intro-aconst 0 idpc))
(pp (rename-variables (aconst-to-formula aconst0)))
;; allnc m^ (PList (cterm (n^) ex n^0 n^0*m^ eqd n^))(Nil nat)

(define aconst1 (number-and-idpredconst-to-intro-aconst 1 idpc))
(pp (rename-variables (aconst-to-formula aconst1)))
;; allnc m^,n^(
;;  ex n^0 n^0*m^ eqd n^ ->
;;  allnc ns^(
;;   (PList (cterm (n^0) ex n^1 n^1*m^ eqd n^0))ns^ ->
;;   (PList (cterm (n^0) ex n^1 n^1*m^ eqd n^0))(n^ ::ns^)))

;; Check that in the elim-aconst variables are generalized in the
;; order idpc-arg-vars idpc-cterm-vars competitor-extra-vars

;; The competitor predicate P(k^) says for a list ns^ that there is
;; l>=k^ such that no n_i in ns^ divides l

(define imp-formula
  (pf "(PList (cterm (n^0) ex n^1 n^1*m^ eqd n^0))ns^ ->
       ex l(k^ <=l & all i(i<Lh ns^ -> ex j(j*(i thof ns^) eqd l -> F)))"))

(define aconst (imp-formulas-to-elim-aconst imp-formula))
(pp (rename-variables (aconst-to-formula aconst)))

;; allnc ns^,m^,k^(
;;  (PList (cterm (n^) ex n^0 n^0*m^ eqd n^))ns^ ->
;;  ex l(k^ <=l & all i(i<Lh(Nil nat) -> ex j(j*(i thof(Nil nat))eqd l -> F))) ->
;;  allnc n^(
;;   ex n^0 n^0*m^ eqd n^ ->
;;   allnc ns^0(
;;    (PList (cterm (n^0) ex n^1 n^1*m^ eqd n^0))ns^0 ->
;;    ex l(k^ <=l & all i(i<Lh ns^0 -> ex j(j*(i thof ns^0)eqd l -> F))) ->
;;    ex l(
;;     k^ <=l & all i(i<Lh(n^ ::ns^0) -> ex j(j*(i thof n^ ::ns^0)eqd l -> F))))) ->
;;  ex l(k^ <=l & all i(i<Lh ns^ -> ex j(j*(i thof ns^)eqd l -> F))))

(remove-var-name "l" "i" "j" "ns")
(remove-pvar-name "P")

;; Tests of number-and-pconst-to-comp-aconst

(add-program-constant "Fix" (py "(alpha=>alpha)=>alpha") t-deg-zero 'const 1)

(add-var-name "f" (py "alpha=>alpha"))

(add-computation-rule "(Fix alpha)f" "f((Fix alpha)f)")
;; (pp (nt (pt "(Fix alpha)"))) ;does not terminate

(define aconst (number-and-pconst-to-comp-aconst
		0 (term-in-const-form-to-const (pt "(Fix alpha)"))))

;; (check-aconst aconst) ;ok

(pp (aconst-to-formula aconst))
;; all f^ (Fix alpha)f^ eqd f^((Fix alpha)f^)

(remove-program-constant "Fix")
(remove-var-name "f")

;; Tests for
;; (arrow-types-to-uninst-recop-types-and-tsubst . arrow-types)

(let* ((recop-types-and-tsubst
	(arrow-types-to-uninst-recop-types-and-tsubst
	 (py "ltlist unit=>nat") (py "ltree unit=>boole")))
       (recop-types (car recop-types-and-tsubst))
       (tsubst (cadr recop-types-and-tsubst)))
  (for-each pp recop-types)
  (pp-subst tsubst))

;; ltlist alpha=>
;; alpha527=>
;; (ltree alpha=>alpha526=>ltlist alpha=>alpha527=>alpha527)=>
;; (alpha=>alpha526)=>(ltlist alpha=>alpha527=>alpha526)=>alpha527
;; ltree alpha=>
;; alpha527=>
;; (ltree alpha=>alpha526=>ltlist alpha=>alpha527=>alpha527)=>
;; (alpha=>alpha526)=>(ltlist alpha=>alpha527=>alpha526)=>alpha526
;;   alpha -> unit
;;   alpha527 -> nat
;;   alpha526 -> boole

(let* ((recop-types-and-tsubst
	(arrow-types-to-uninst-recop-types-and-tsubst
	 (py "ltlist unit=>nat")))
       (recop-types (car recop-types-and-tsubst))
       (tsubst (cadr recop-types-and-tsubst)))
  (for-each pp recop-types)
  (pp-subst tsubst))

;; ltlist alpha=>alpha529=>(ltlist alpha=>alpha529=>alpha529)=>alpha529
;;   alpha -> unit
;;   alpha529 -> nat

(let* ((recop-types-and-tsubst
	(arrow-types-to-uninst-recop-types-and-tsubst
	 (py "ltree unit=>boole")))
       (recop-types (car recop-types-and-tsubst))
       (tsubst (cadr recop-types-and-tsubst)))
  (for-each pp recop-types)
  (pp-subst tsubst))

;; ltree alpha=>(alpha=>alpha530)=>alpha530=>alpha530
;;   alpha -> unit
;;   alpha530 -> boole

;; Tests for constructor-type-to-product-type

(define (alg-to-constr-types alg)
  (let* ((name (alg-form-to-name alg))
	 (names (alg-name-to-simalg-names name))
	 (typed-constr-names
	  (apply union (map alg-name-to-typed-constr-names names))))
    (map typed-constr-name-to-type typed-constr-names)))

(for-each pp (alg-to-constr-types (py "nat")))
;; nat
;; nat=>nat

(define constr-type (car (alg-to-constr-types (py "boole"))))
(define rel-alg-name-to-f-or-type-alist (list (list "boole" (py "alpha"))))

(pp (constructor-type-to-product-type
     constr-type rel-alg-name-to-f-or-type-alist))
;; unit

(define constr-type (cadr (alg-to-constr-types (py "boole"))))
(define rel-alg-name-to-f-or-type-alist (list (list "boole" (py "alpha"))))

(pp (constructor-type-to-product-type
     constr-type rel-alg-name-to-f-or-type-alist))
;; unit

(define constr-type (car (alg-to-constr-types (py "nat"))))
(define rel-alg-name-to-f-or-type-alist (list (list "nat" (py "alpha"))))

(pp (constructor-type-to-product-type
     constr-type rel-alg-name-to-f-or-type-alist))
;; unit

(define constr-type (cadr (alg-to-constr-types (py "nat"))))
(define rel-alg-name-to-f-or-type-alist (list (list "nat" (py "alpha"))))

(pp (constructor-type-to-product-type
     constr-type rel-alg-name-to-f-or-type-alist))
;; nat ysum alpha

(define constr-type (cadr (alg-to-constr-types (py "intv"))))
(define rel-alg-name-to-f-or-type-alist (list (list "intv" (py "alpha"))))

(pp (constructor-type-to-product-type
     constr-type rel-alg-name-to-f-or-type-alist))
;; intv ysum alpha

(define constr-type (cadr (alg-to-constr-types (py "list alpha"))))
(define rel-alg-name-to-f-or-type-alist (list (list "list" (py "nat"))))

(pp (constructor-type-to-product-type
     constr-type rel-alg-name-to-f-or-type-alist))
;; alpha@@(list alpha ysum nat)

(define constr-type (cadr (alg-to-constr-types (py "lbin alpha"))))
(define rel-alg-name-to-f-or-type-alist (list (list "lbin" (py "nat"))))

(pp (constructor-type-to-product-type
     constr-type rel-alg-name-to-f-or-type-alist))
;; (lbin alpha ysum nat)@@(lbin alpha ysum nat)

(define constr-type (caddr (alg-to-constr-types (py "ordl"))))
(define rel-alg-name-to-f-or-type-alist (list (list "ordl" (py "alpha"))))

(pp (constructor-type-to-product-type
     constr-type rel-alg-name-to-f-or-type-alist))
;; nat=>ordl ysum alpha

;; Tests for alg-or-arrow-types-to-uninst-corecop-types-and-tsubst

(for-each
 pp (car (alg-or-arrow-types-to-uninst-corecop-types-and-tsubst
	  (py "alpha=>nat"))))
;; alpha532=>(alpha532=>uysum(nat ysum alpha532))=>nat

(for-each
 pp (car (alg-or-arrow-types-to-uninst-corecop-types-and-tsubst (py "nat"))))
;; uysum nat ysumu=>nat

(for-each
 pp (car (alg-or-arrow-types-to-uninst-corecop-types-and-tsubst
	  (py "alpha=>ordl"))))
;; alpha178=>
;; (alpha178=>uysum((ordl ysum alpha178)ysum(nat=>ordl ysum alpha178)))=>ordl

(for-each
 pp (car (alg-or-arrow-types-to-uninst-corecop-types-and-tsubst (py "ordl"))))
;; uysum(ordl ysumu ysum(nat=>ordl ysumu))=>ordl

(define uninst-corecop-types-and-tsubst
  (alg-or-arrow-types-to-uninst-corecop-types-and-tsubst
   (py "nat=>ltlist alpha") (py "boole=>ltree alpha")))

(define uninst-corecop-types (car uninst-corecop-types-and-tsubst))
(define tsubst (cadr uninst-corecop-types-and-tsubst))
(define corecop-types (map (lambda (uninst-corecop-type)
			     (type-substitute uninst-corecop-type tsubst))
			   uninst-corecop-types))

(pp (car corecop-types))

;; nat=>
;; (nat=>uysum((ltree alpha ysum boole)@@(ltlist alpha ysum nat)))=>
;; (boole=>alpha ysum ltlist alpha ysum nat)=>ltlist alpha

(pp (cadr corecop-types))

;; boole=>
;; (nat=>uysum((ltree alpha ysum boole)@@(ltlist alpha ysum nat)))=>
;; (boole=>alpha ysum ltlist alpha ysum nat)=>ltree alpha

;; Tests for alg-or-arrow-types-to-uninst-corecop-types-and-tsubst

(for-each
 pp (car (alg-or-arrow-types-to-uninst-corecop-types-and-tsubst
	  (py "alpha=>nat"))))
;; alpha31=>(alpha31=>uysum(nat ysum alpha31))=>nat

(for-each
 pp (car (alg-or-arrow-types-to-uninst-corecop-types-and-tsubst (py "nat"))))
;; uysum nat ysumu=>nat

(for-each
 pp (car (alg-or-arrow-types-to-uninst-corecop-types-and-tsubst
	  (py "alpha=>ordl"))))
;; alpha178=>
;; (alpha178=>uysum((ordl ysum alpha178)ysum(nat=>ordl ysum alpha178)))=>ordl

(for-each
 pp (car (alg-or-arrow-types-to-uninst-corecop-types-and-tsubst (py "ordl"))))
;; uysum(ordl ysumu ysum(nat=>ordl ysumu))=>ordl

(define uninst-corecop-types-and-tsubst
  (alg-or-arrow-types-to-uninst-corecop-types-and-tsubst
   (py "nat=>ltlist alpha") (py "boole=>ltree alpha")))

(define uninst-corecop-types (car uninst-corecop-types-and-tsubst))
(define tsubst (cadr uninst-corecop-types-and-tsubst))
(define corecop-types (map (lambda (uninst-corecop-type)
			     (type-substitute uninst-corecop-type tsubst))
			   uninst-corecop-types))

(pp (car corecop-types))

;; nat=>
;; (nat=>uysum((ltree alpha ysum boole)@@(ltlist alpha ysum nat)))=>
;; (boole=>alpha ysum ltlist alpha ysum nat)=>ltlist alpha

(pp (cadr corecop-types))

;; boole=>
;; (nat=>uysum((ltree alpha ysum boole)@@(ltlist alpha ysum nat)))=>
;; (boole=>alpha ysum ltlist alpha ysum nat)=>ltree alpha

(define uninst-corecop-types-and-tsubst
  (alg-or-arrow-types-to-uninst-corecop-types-and-tsubst
   (py "boole=>ltree alpha") (py "nat=>ltlist alpha")))

(define uninst-corecop-types (car uninst-corecop-types-and-tsubst))
(define tsubst (cadr uninst-corecop-types-and-tsubst))
(define corecop-types (map (lambda (uninst-corecop-type)
			     (type-substitute uninst-corecop-type tsubst))
			   uninst-corecop-types))

(pp (car corecop-types))

;; boole=>
;; (nat=>uysum((ltree alpha ysum boole)@@(ltlist alpha ysum nat)))=>
;; (boole=>alpha ysum ltlist alpha ysum nat)=>ltree alpha

(pp (cadr corecop-types))

;; nat=>
;; (nat=>uysum((ltree alpha ysum boole)@@(ltlist alpha ysum nat)))=>
;; (boole=>alpha ysum ltlist alpha ysum nat)=>ltlist alpha

;; First argument type improper.

(define uninst-corecop-types-and-tsubst
  (alg-or-arrow-types-to-uninst-corecop-types-and-tsubst
   (py "ltlist alpha") (py "boole=>ltree alpha")))

(define uninst-corecop-types (car uninst-corecop-types-and-tsubst))
(define tsubst (cadr uninst-corecop-types-and-tsubst))
(define corecop-types (map (lambda (uninst-corecop-type)
			     (type-substitute uninst-corecop-type tsubst))
			   uninst-corecop-types))

(pp (car corecop-types))

;; uysum((ltree alpha ysum boole)@@ltlist alpha ysumu)=>
;; (boole=>alpha ysum ltlist alpha ysumu)=>ltlist alpha

(pp (cadr corecop-types))

;; boole=>
;; uysum((ltree alpha ysum boole)@@ltlist alpha ysumu)=>
;; (boole=>alpha ysum ltlist alpha ysumu)=>ltree alpha

;; Second argument type improper.

(define uninst-corecop-types-and-tsubst
  (alg-or-arrow-types-to-uninst-corecop-types-and-tsubst
   (py "nat=>ltlist alpha") (py "ltree alpha")))

(define uninst-corecop-types (car uninst-corecop-types-and-tsubst))
(define tsubst (cadr uninst-corecop-types-and-tsubst))
(define corecop-types (map (lambda (uninst-corecop-type)
			     (type-substitute uninst-corecop-type tsubst))
			   uninst-corecop-types))

(pp (car corecop-types))

;; nat=>
;; (nat=>uysum(ltree alpha ysumu@@(ltlist alpha ysum nat)))=>
;; alpha ysum ltlist alpha ysum nat=>ltlist alpha

(pp (cadr corecop-types))

;; (nat=>uysum(ltree alpha ysumu@@(ltlist alpha ysum nat)))=>
;; alpha ysum ltlist alpha ysum nat=>ltree alpha

;; Both argument types improper.

(define uninst-corecop-types-and-tsubst
  (alg-or-arrow-types-to-uninst-corecop-types-and-tsubst
   (py "ltlist alpha") (py "ltree alpha")))

(define uninst-corecop-types (car uninst-corecop-types-and-tsubst))
(define tsubst (cadr uninst-corecop-types-and-tsubst))
(define corecop-types (map (lambda (uninst-corecop-type)
			     (type-substitute uninst-corecop-type tsubst))
			   uninst-corecop-types))

(pp (car corecop-types))

;; uysum(ltree alpha ysumu@@ltlist alpha ysumu)=>
;; alpha ysum ltlist alpha ysumu=>ltlist alpha

(pp (cadr corecop-types))

;; uysum(ltree alpha ysumu@@ltlist alpha ysumu)=>
;; alpha ysum ltlist alpha ysumu=>ltree alpha

;; Tests of alg-or-arrow-types-to-uninst-corecop-types-and-tsubst
;; after adaption of corecursion to nested algebras.

(for-each
 pp (car (alg-or-arrow-types-to-uninst-corecop-types-and-tsubst
	  (py "alpha=>ntree"))))
;; alpha128=>(alpha128=>list(ntree ysum alpha128))=>ntree

(define uninst-corecop-types-and-tsubst
  (alg-or-arrow-types-to-uninst-corecop-types-and-tsubst
   (py "nat=>ltlist alpha") (py "boole=>ltree alpha") #f))

(define uninst-corecop-types (car uninst-corecop-types-and-tsubst))
(define tsubst (cadr uninst-corecop-types-and-tsubst))
(define corecop-types (map (lambda (uninst-corecop-type)
			     (type-substitute uninst-corecop-type tsubst))
			   uninst-corecop-types))

(pp (car corecop-types))

;; nat=>
;; (nat=>uysum((ltree alpha ysum boole)yprod(ltlist alpha ysum nat)))=>
;; (boole=>alpha ysum ltlist alpha ysum nat)=>ltlist alpha

;; Tests for alg-or-arrow-types-to-corec-const

(define term
  (make-term-in-const-form (alg-or-arrow-types-to-corec-const
			    (py "alpha=>nat"))))

(pp term)
;; (CoRec alpha=>nat)

(pp (term-to-type term))
;; alpha=>(alpha=>uysum(nat ysum nat))=>nat

(pp (nt term)) ;ok

(define term
  (make-term-in-const-form (alg-or-arrow-types-to-corec-const (py "nat"))))

(pp term)
;; (CoRec nat)

(pp (term-to-type term))
;; uysum nat ysumu=>nat

(pp (nt term)) ;ok

;; Tests for corec-const-to-corec-consts

(define corec-consts
  (alg-or-arrow-types-to-corec-consts (py "nat=>ltlist alpha")
				      (py "boole=>ltree alpha")))
(define corec-const (car corec-consts))
(define computed-corec-consts (corec-const-to-corec-consts corec-const))
(define computed-corec-const (car computed-corec-consts))

(pp (make-term-in-const-form corec-const))
;; (CoRec nat=>ltlist alpha boole=>ltree alpha)
(pp (make-term-in-const-form computed-corec-const))
;; (CoRec nat=>ltlist alpha boole=>ltree alpha)

;; First argument type improper.

(define corec-consts
  (alg-or-arrow-types-to-corec-consts (py "ltlist alpha")
				      (py "boole=>ltree alpha")))
(define corec-const (car corec-consts))
(define computed-corec-consts (corec-const-to-corec-consts corec-const))
(define computed-corec-const (car computed-corec-consts))

(pp (make-term-in-const-form corec-const))
;; (CoRec ltlist alpha boole=>ltree alpha)
(pp (make-term-in-const-form computed-corec-const))
;; (CoRec ltlist alpha boole=>ltree alpha)

;; Tests for corec-const-and-bound-to-bcorec-term

(define corec-const (alg-or-arrow-types-to-corec-const (py "alpha=>nat")))

(define bcorec-term (corec-const-and-bound-to-bcorec-term
		     corec-const (pt "1")))

(pp (rename-variables bcorec-term))


;; (Rec nat=>alpha=>(alpha=>uysum(nat ysum alpha))=>nat)1(CoRec alpha=>nat)
;; ([n,(alpha=>(alpha=>uysum(nat ysum alpha))=>nat),x,(alpha=>uysum(nat ysum alpha))_0]
;;   [if ((alpha=>uysum(nat ysum alpha))_0 x)
;;     0
;;     ([(nat ysum alpha)_1]
;;      Succ
;;      ((Map (nat ysum alpha) nat)(nat ysum alpha)_1
;;       ([(nat ysum alpha)_2]
;;         [if (nat ysum alpha)_2
;;           ([n0]n0)
;;           ([x0]
;;            (alpha=>(alpha=>uysum(nat ysum alpha))=>nat)x0
;;            (alpha=>uysum(nat ysum alpha))_0)])))])

(pp (nt bcorec-term))

;; [x0,(alpha=>uysum(nat ysum alpha))_1]
;;  [if ((alpha=>uysum(nat ysum alpha))_1 x0)
;;    0
;;    ([(nat ysum alpha)_2]
;;     Succ
;;     [if (nat ysum alpha)_2
;;       ([n3]n3)
;;       ([x3](CoRec alpha=>nat)x3(alpha=>uysum(nat ysum alpha))_1)])]

(define bcorec-term (corec-const-and-bound-to-bcorec-term
		     (alg-or-arrow-types-to-corec-const (py "alpha=>lbin nat"))
		     (pt "1")))

;; (pp (rename-variables bcorec-term))
(pp (rename-variables (nt bcorec-term)))

;; [x,(alpha=>nat ysum nat@@(lbin nat ysum alpha)@@(lbin nat ysum alpha))]
;;  [if ((alpha=>nat ysum nat@@(lbin nat ysum alpha)@@(lbin nat ysum alpha))x)
;;    (LbinNil nat)
;;    ([(nat@@(lbin nat ysum alpha)@@(lbin nat ysum alpha))_0]
;;     (LbinBranch nat)
;;     left(nat@@(lbin nat ysum alpha)@@(lbin nat ysum alpha))_0
;;     [if (left right(nat@@(lbin nat ysum alpha)@@(lbin nat ysum alpha))_0)
;;       ([(lbin nat)_1](lbin nat)_1)
;;       ([x0]
;;        (CoRec alpha=>lbin nat)x0
;;        (alpha=>nat ysum nat@@(lbin nat ysum alpha)@@(lbin nat ysum alpha)))]
;;     [if (right right(nat@@(lbin nat ysum alpha)@@(lbin nat ysum alpha))_0)
;;       ([(lbin nat)_1](lbin nat)_1)
;;       ([x0]
;;        (CoRec alpha=>lbin nat)x0
;;        (alpha=>nat ysum nat@@(lbin nat ysum alpha)@@(lbin nat ysum alpha)))])]

(define bcorec-term
  (corec-const-and-bound-to-bcorec-term
   (alg-or-arrow-types-to-corec-const (py "beta=>list alpha"))
   (pt "1")))

;; (pp (rename-variables bcorec-term))
(pp (rename-variables (nt bcorec-term)))

;; [beta,(beta=>uysum(alpha@@(list alpha ysum beta)))_0]
;;  [if ((beta=>uysum(alpha@@(list alpha ysum beta)))_0 beta)
;;    (Nil alpha)
;;    ([(alpha@@(list alpha ysum beta))_1]
;;     left(alpha@@(list alpha ysum beta))_1::
;;     [if (right(alpha@@(list alpha ysum beta))_1)
;;       ([xs]xs)
;;       ([beta_2]
;;        (CoRec beta=>list alpha)beta_2
;;        (beta=>uysum(alpha@@(list alpha ysum beta)))_0)])]

(define bcorec-term (corec-const-and-bound-to-bcorec-term
		     (alg-or-arrow-types-to-corec-const (py "alpha=>intv"))
		     (pt "1")))

;; (pp (rename-variables bcorec-term))
(pp (rename-variables (nt bcorec-term)))

;; [x,(alpha=>uysum((intv ysum alpha)ysum(intv ysum alpha)ysum intv ysum alpha))]
;;  [if ((alpha=>uysum((intv ysum alpha)ysum(intv ysum alpha)ysum intv ysum alpha))
;;        x)
;;    CInt
;;    ([((intv ysum alpha)ysum(intv ysum alpha)ysum intv ysum alpha)_0]
;;     [if ((intv ysum alpha)ysum(intv ysum alpha)ysum intv ysum alpha)_0
;;       ([(intv ysum alpha)_1]
;;        CIntN
;;        [if (intv ysum alpha)_1
;;          ([intv2]intv2)
;;          ([x0]
;;           (CoRec alpha=>intv)x0
;;           (alpha=>uysum((intv ysum alpha)ysum(intv ysum alpha)ysum intv ysum alpha)))])
;;       ([((intv ysum alpha)ysum intv ysum alpha)_1]
;;        [if ((intv ysum alpha)ysum intv ysum alpha)_1
;;          ([(intv ysum alpha)_2]
;;           CIntZ
;;           [if (intv ysum alpha)_2
;;             ([intv3]intv3)
;;             ([x0]
;;              (CoRec alpha=>intv)x0
;;              (alpha=>uysum((intv ysum alpha)ysum(intv ysum alpha)ysum intv ysum alpha)))])
;;          ([(intv ysum alpha)_2]
;;           CIntP
;;           [if (intv ysum alpha)_2
;;             ([intv3]intv3)
;;             ([x0]
;;              (CoRec alpha=>intv)x0
;;              (alpha=>uysum((intv ysum alpha)ysum(intv ysum alpha)ysum intv ysum alpha)))])])])]

(define bcorec-term (corec-const-and-bound-to-bcorec-term
		     (alg-or-arrow-types-to-corec-const (py "alpha=>ordl"))
		     (pt "1")))

;; (pp (rename-variables bcorec-term))
(pp (rename-variables (nt bcorec-term)))

;; [x,(alpha=>uysum((ordl ysum alpha)ysum(nat=>ordl ysum alpha)))]
;;  [if ((alpha=>uysum((ordl ysum alpha)ysum(nat=>ordl ysum alpha)))x)
;;    OrdZero
;;    ([((ordl ysum alpha)ysum(nat=>ordl ysum alpha))_0]
;;     [if ((ordl ysum alpha)ysum(nat=>ordl ysum alpha))_0
;;       ([(ordl ysum alpha)_1]
;;        OrdSucc
;;        [if (ordl ysum alpha)_1
;;          ([ordl2]ordl2)
;;          ([x0]
;;           (CoRec alpha=>ordl)x0
;;           (alpha=>uysum((ordl ysum alpha)ysum(nat=>ordl ysum alpha))))])
;;       ([(nat=>ordl ysum alpha)_1]
;;        OrdSup
;;        ([n]
;;          [if ((nat=>ordl ysum alpha)_1 n)
;;            ([ordl2]ordl2)
;;            ([x0]
;;             (CoRec alpha=>ordl)x0
;;             (alpha=>uysum((ordl ysum alpha)ysum(nat=>ordl ysum alpha))))]))])]

(define bcorec-term (corec-const-and-bound-to-bcorec-term
		     (alg-or-arrow-types-to-corec-const (py "alpha=>boole"))
		     (pt "1")))

(pp (rename-variables bcorec-term))

;; (Rec nat=>alpha=>(alpha=>boole)=>boole)1(CoRec alpha=>boole)
;; ([n,(alpha=>(alpha=>boole)=>boole),x,q][if (q x) True False])

(pp (rename-variables (nt bcorec-term)))
;; [x,q]q x

(define bcorec-term (corec-const-and-bound-to-bcorec-term
		     (alg-or-arrow-types-to-corec-const (py "alpha=>unit"))
		     (pt "1")))

(pp (rename-variables bcorec-term))

;; (Rec nat=>alpha=>(alpha=>unit)=>unit)1(CoRec alpha=>unit)
;; ([n,(alpha=>(alpha=>unit)=>unit),x,(alpha=>unit)_0]Dummy)

(pp (rename-variables (nt bcorec-term)))
;; [x,(alpha=>unit)]Dummy

;; Tests for corec-const-and-bound-to-bcorec-term with improper
;; argument type.

(define corec-const (alg-or-arrow-types-to-corec-const (py "nat")))

(define bcorec-term (corec-const-and-bound-to-bcorec-term
		     corec-const (pt "1")))

(pp (rename-variables bcorec-term))

;; (Rec nat=>uysum nat ysumu=>nat)1(CoRec nat)
;; ([n,(uysum nat ysumu=>nat),(uysum nat ysumu)_0]
;;   [if (uysum nat ysumu)_0
;;     0
;;     ([(nat ysumu)_1]
;;      Succ
;;      ((Map (nat ysumu) nat)(nat ysumu)_1
;;       ([(nat ysumu)_2]
;;         [if (nat ysumu)_2
;;           ([n0]n0)
;;           ((uysum nat ysumu=>nat)(uysum nat ysumu)_0)])))])

(pp (rename-variables (nt bcorec-term)))

;; [(uysum nat ysumu)]
;;  [if (uysum nat ysumu)
;;    0
;;    ([(nat ysumu)_0]
;;     Succ[if (nat ysumu)_0 ([n]n) ((CoRec nat)(uysum nat ysumu))])]

(define corec-const (alg-or-arrow-types-to-corec-const (py "intv")))

(define bcorec-term (corec-const-and-bound-to-bcorec-term
		     corec-const (pt "1")))

;; (pp (rename-variables bcorec-term))
(pp (rename-variables (nt bcorec-term)))

;; [(uysum(intv ysumu ysum intv ysumu ysum intv ysumu))]
;;  [if (uysum(intv ysumu ysum intv ysumu ysum intv ysumu))
;;    CInt
;;    ([(intv ysumu ysum intv ysumu ysum intv ysumu)_0]
;;     [if (intv ysumu ysum intv ysumu ysum intv ysumu)_0
;;       ([(intv ysumu)_1]
;;        CIntN
;;        [if (intv ysumu)_1
;;          ([intv2]intv2)
;;          ((CoRec intv)(uysum(intv ysumu ysum intv ysumu ysum intv ysumu)))])
;;       ([(intv ysumu ysum intv ysumu)_1]
;;        [if (intv ysumu ysum intv ysumu)_1
;;          ([(intv ysumu)_2]
;;           CIntZ
;;           [if (intv ysumu)_2
;;             ([intv3]intv3)
;;             ((CoRec intv)(uysum(intv ysumu ysum intv ysumu ysum intv ysumu)))])
;;          ([(intv ysumu)_2]
;;           CIntP
;;           [if (intv ysumu)_2
;;             ([intv3]intv3)
;;             ((CoRec intv)(uysum(intv ysumu ysum intv ysumu ysum intv ysumu)))])])])]

;; 2011-07-23.  Test for undelay-delayed-corec in a simultaneous case.
;; This essentially applies corec-const-and-bound-to-bcorec-term .  We
;; therefore need a corec-const.

(define corec-const
  (alg-or-arrow-types-to-corec-const (py "boole=>tlist") (py "nat=>tree")))

(pp (const-to-type corec-const))

;; boole=>
;; (boole=>uysum((tree ysum nat)@@(tlist ysum boole)))=>
;; (nat=>uysum(tlist ysum boole))=>tlist

;; Next we need step terms.

(define step0
  (pt "[boole]
 [if boole
   (Inr((InR nat tree)0@(InR boole tlist)False))
   (Inr((InR nat tree)1@(InR boole tlist)True))]"))

(pp (term-to-type step0))
;; boole=>uysum((tree ysum nat)@@(tlist ysum boole))

(define step1
  (pt "[n]
 [if n (Inr((InR boole tlist)False)) ([n1]Inr((InR boole tlist)True))]"))

(pp (term-to-type step1))
;; nat=>uysum(tlist ysum boole)

;; Now we apply corec-const to True and the step terms.

(define term
  (mk-term-in-app-form
   (make-term-in-const-form corec-const) (pt "True") step0 step1))

(pp term)

;; (CoRec boole=>tlist nat=>tree)True
;; ([boole]
;;   [if boole
;;     (Inr((InR nat tree)0@(InR boole tlist)False))
;;     (Inr((InR nat tree)1@(InR boole tlist)True))])
;; ([n][if n (Inr((InR boole tlist)False)) ([n1]Inr((InR boole tlist)True))])

;; Since normalization for CoRec is delayed, this term normalizes to
;; itself.  To unfold it a limited number of times, we use
;; undelay-delayed-corec .

(pp (nt (undelay-delayed-corec term 0)))

;; (CoRec boole=>tlist nat=>tree)True
;; ([p0]
;;   [if p0
;;     (Inr((InR nat tree)0@(InR boole tlist)False))
;;     (Inr((InR nat tree)1@(InR boole tlist)True))])
;; ([n0][if n0 (Inr((InR boole tlist)False)) ([n1]Inr((InR boole tlist)True))])

(pp (nt (undelay-delayed-corec term 1)))

;; Tcons
;; ((CoRec boole=>tlist nat=>tree)0
;;  ...
;;  ...)
;; ((CoRec boole=>tlist nat=>tree)False
;;  ...
;;  ...)

(pp (nt (undelay-delayed-corec term 2)))

;; Tcons
;; (Branch
;;  ((CoRec boole=>tlist nat=>tree)False
;;   ...
;;   ...))
;; (Tcons
;;  ((CoRec boole=>tlist nat=>tree)1
;;   ...
;;   ...)
;;  ((CoRec boole=>tlist nat=>tree)True
;;   ...
;;   ...))

(pp (nt (undelay-delayed-corec term 3)))

;; Tcons
;; (Branch
;;  (Tcons
;;   ((CoRec boole=>tlist nat=>tree)1
;;    ...
;;    ...)
;;   ((CoRec boole=>tlist nat=>tree)True
;;    ...
;;    ...)))
;; (Tcons
;;  (Branch
;;   ((CoRec boole=>tlist nat=>tree)True
;;    ...
;;    ...))
;;  (Tcons
;;   ((CoRec boole=>tlist nat=>tree)0
;;    ...
;;    ...)
;;   ((CoRec boole=>tlist nat=>tree)False
;;    ...
;;    ...)))

;; We can also reverse the order.

(define corec-const
  (alg-or-arrow-types-to-corec-const (py "nat=>tree") (py "boole=>tlist")))

(pp (const-to-type corec-const))

;; nat=>
;; (boole=>uysum((tree ysum nat)@@(tlist ysum boole)))=>
;; (nat=>uysum(tlist ysum boole))=>tree

;; Now we apply corec-const to 0 and the (same) step terms.

(define term
  (mk-term-in-app-form
   (make-term-in-const-form corec-const) (pt "0") step0 step1))

(pp term)

;; (CoRec boole=>tlist nat=>tree)0
;; ([boole]
;;   [if boole
;;     (Inr((InR nat tree)0 pair(InR boole tlist)False))
;;     (Inr((InR nat tree)1 pair(InR boole tlist)True))])
;; ([n][if n (Inr((InR boole tlist)False)) ([n1]Inr((InR boole tlist)True))])

;; Since normalization for CoRec is delayed, this term normalizes to
;; itself.  To unfold it a limited number of times, we use
;; undelay-delayed-corec .

(pp (nt (undelay-delayed-corec term 0)))

;; (CoRec nat=>tree boole=>tlist)0
;; ([p0]
;;   [if p0
;;     (Inr((InR nat tree)0@(InR boole tlist)False))
;;     (Inr((InR nat tree)1@(InR boole tlist)True))])
;; ([n0][if n0 (Inr((InR boole tlist)False)) ([n1]Inr((InR boole tlist)True))])

(pp (nt (undelay-delayed-corec term 1)))

;; Branch
;; ((CoRec boole=>tlist nat=>tree)False
;;  ...
;;  ...)

(pp (nt (undelay-delayed-corec term 2)))

;; Branch
;; (Tcons
;;  ((CoRec boole=>tlist nat=>tree)1
;;   ...
;;   ...)
;;  ((CoRec boole=>tlist nat=>tree)True
;;   ...
;;   ...))

(pp (nt (undelay-delayed-corec term 3)))

;; Branch
;; (Tcons
;;  (Branch
;;   ((CoRec boole=>tlist nat=>tree)True
;;    ...
;;    ([n0]
;;      [if n0 (Inr((InR boole tlist)False)) ([n1]Inr((InR boole tlist)True))])))
;;  (Tcons
;;   ((CoRec boole=>tlist nat=>tree)0
;;    ...
;;    ...)
;;   ((CoRec boole=>tlist nat=>tree)False
;;    ...
;;    ...)))

;; Tests for the types of simultaneous recursion operators

(pp (term-to-type (pt "(Rec tlist=>alpha1 tree=>alpha2)")))

;; tlist=>
;; alpha1=>
;; (tree=>alpha2=>tlist=>alpha1=>alpha1)=>
;; alpha2=>(tlist=>alpha1=>alpha2)=>alpha1

(pp (term-to-type (pt "(Rec tree=>alpha2 tlist=>alpha1)")))

;; tree=>
;; alpha1=>
;; (tree=>alpha2=>tlist=>alpha1=>alpha1)=>
;; alpha2=>(tlist=>alpha1=>alpha2)=>alpha2

;; Tests for the types of simplified simultaneous recursion operators.
;; (i)  omit all step types with irrelevant value type, and
;; (ii) simplify the remaining step types by omitting from the recursive
;;      argument types and also from their algebra-duplicates all those
;;      with irrelevant value type.

(pp (term-to-type (pt "(Rec tlist=>alpha1)")))
;; tlist=>alpha1=>(tlist=>alpha1=>alpha1)=>alpha1

(pp (term-to-type (pt "(Rec tree=>alpha2)")))
;; tree=>alpha2=>alpha2=>alpha2

;; Tests for GRec

(pp (pt "(GRec nat nat)"))
(pp (rename-variables (nt (pt "(GRec nat nat)"))))

;; [(nat=>nat),n,(nat=>(nat=>nat)=>nat)_0]
;;  (nat=>(nat=>nat)=>nat)_0 n
;;  ([n0]
;;    (GRecGuard nat nat)(nat=>nat)n0(nat=>(nat=>nat)=>nat)_0
;;    ((nat=>nat)n0<(nat=>nat)n))

(add-program-constant "Fix" (py "(alpha=>alpha)=>alpha") t-deg-zero 'const 1)

(pp (pt "(Fix nat)"))
(pp (term-to-type (pt "(Fix nat)")))

;; (nat=>nat)=>nat

(pp (nt (pt "(Fix nat)"))) ;no reduction, since we have no computation
			   ;rule

(remove-program-constant "Fix")
