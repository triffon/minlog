;; (load "~/git/minlog/init.scm")
(load "names.scm")

; 7. Formulas and comprehension terms
; ===================================
; (formula.scm and boole.scm)

;; ex and exd are treated differently by formula-to-undec-formula, in
;; case id-deco? is true.

(pp (formula-to-undec-formula (pf "ex boole T") #t)) ;ex boole T
(pp (formula-to-undec-formula (pf "exd boole T") #t)) ;exu boole T

(add-pvar-name "S" (make-arity (py "alpha") (py "alpha") (py "alpha")))

(define testformulas
  (list
   (pf "p^1=p^2")
   (pf "R x^1 x^2")
   (pf "Total x^1")
   (pf "x^1 eqd x^2")
   (pf "Pvar1 -> Pvar2")
   (pf "Pvar1 --> Pvar2")
   (pf "all x^1 R x^1 x^2")
   (pf "allnc x^1 R x^1 x^2")
   (pf "Pvar1 & Pvar2")
   (pf "ex x^1 R x^1 x^2")
   (pf "excl x^1 R x^1 x^2")
   (pf "excl x^1,x^2 S x^1 x^2 x^3")
   (pf "exca x^1 R x^1 x^2")
   (pf "exca x^1,x^2 S x^1 x^2 x^3")
   (pf "x^1 eqd x^2")
   (pf "exd x^1 R x^1 x^2")
   (pf "exl x^1 R x^1 x^2")
   (pf "exr x^1 R x^1 x^2")
   (pf "exu x^1 R x^1 x^2")
   (pf "exd x1 R x1 x^2")
   (pf "exl x1 R x1 x^2")
   (pf "exr x1 R x1 x^2")
   (pf "exu x1 R x1 x^2")
   (pf "Pvar1 ord Pvar2")
   (pf "Pvar1 orl Pvar2")
   (pf "Pvar1 orr Pvar2")
   (pf "Pvar1 oru Pvar2")
   (pf "Pvar1 andd Pvar2")
   (pf "Pvar1 andl Pvar2")
   (pf "Pvar1 andr Pvar2")
   (pf "Pvar1 andu Pvar2")
   (pf "(TrCl (cterm (x^1,x^2) Q x3 -> R x^1 x^2))x^1 x^3")
   ))

(for-each pp testformulas)

(for-each (lambda (fla)
	    (for-each pp (map make-term-in-var-form (formula-to-free fla))))
	  testformulas)

(for-each (lambda (fla) (for-each pp (formula-to-tvars fla))) testformulas)

;; Tests for totality-predicate?

(totality-predicate? (predicate-form-to-predicate (pf "Total alpha")))
;; ("Total" "TotalMR"), hence true

(totality-predicate? (predicate-form-to-predicate (pf "TotalBoole boole")))
;; #t

(totality-predicate? (predicate-form-to-predicate
		      (pf "(RTotalList (cterm (n^) Total n^))(Nil nat)")))
;; #t

(totality-predicate? (predicate-form-to-predicate
		      (pf "(RTotalList (cterm (n^) T))(Nil nat)")))
;; #f

;; To do: mr-totality-predicate?

;; Tests for unfold-totality

(add-var-name "ns" (py "list nat"))

(pp (unfold-totality (pf "Total x^")))
;; Total x^

(pp (unfold-totality (pf "Total n^")))
;; TotalNat n^

(pp (rename-variables (unfold-totality (pf "Total xs^"))))
;; (RTotalList (cterm (x^) Total x^))xs^

(pp (rename-variables (unfold-totality (pf "TotalList xs^"))))
;; (RTotalList (cterm (x^) Total x^))xs^

(pp (rename-variables (unfold-totality (pf "Total ns^"))))
;; (RTotalList (cterm (n^) TotalNat n^))ns^

(pp (rename-variables (unfold-totality (pf "TotalList ns^"))))
;; (RTotalList (cterm (n^) TotalNat n^))ns^

;; unfold-totality is needed when normalizing proofs with elim for
;; totality.

(pp (nbe-formula-to-type (pf "(RTotalList (cterm (x^) T)) xs^")))
;; nbeRTotalList alpha atomic

(pp (nbe-formula-to-type (pf "Total xs^"))) ;prop
;; should be (nbeTotalList alpha)

(pp (nbe-formula-to-type (pf "TotalList ns^")))
;; nbeTotalList nat

(pp (nbe-formula-to-type (pf "Total ns^"))) ;prop

(remove-var-name "ns")

;; Tests for formula-substitute

(define topsubst
  (list
   (list (py "alpha") (py "boole"))
   (list (pv "x^1") (pt "p^1"))
   (list (pv "x^2") (pt "p^2"))
   (list (pv "x^3") (pt "p^3"))
   (list (predicate-form-to-predicate (pf "R x^1 x^2"))
	 (make-cterm (pv "p^1") (pv "p^2") (pf "p^1=p^2")))
   (list (predicate-form-to-predicate (pf "S x^1 x^2 x^3"))
	 (make-cterm (pv "p^1") (pv "p^2") (pv "p^3")
		     (pf "p^1=p^2")))))

(pp-subst topsubst)
;;   alpha -> boole
;;   x^1 -> p^1
;;   x^2 -> p^2
;;   x^3 -> p^3
;;   R ->  (cterm (p^1,p^2) p^1=p^2)
;;   S ->  (cterm (p^1,p^2,p^3) p^1=p^2)

(for-each (lambda (fla)
	    (pp (rename-variables (formula-substitute fla topsubst))))
	  testformulas)

(remove-pvar-name "S")

;; Testing substitution in prime formulas built from idpredconsts (that
;; is, in the parameter cterms in those, and in the arguments)

(pp (rename-variables (formula-substitute
		       (pf "exd x^ x^ eqd x^")
		       (list (list (py "alpha") (py "boole"))))))
;; exd p^ p^ eqd p^

(pp (formula-substitute
     (pf "exd x^ Q x^")
     (list (list (predicate-form-to-predicate (pf "Q x^"))
		 (make-cterm (pv "x^") (pf "x^ eqd x^"))))))
;; exd x^ x^ eqd x^

(pp (formula-substitute
     (pf "exd x^ Q x^")
     (list (list (predicate-form-to-predicate (pf "Q x^"))
		 (make-cterm (pv "x") (pf "x eqd x"))))))
;; exd x^ x^ eqd x^

;; Notice that ExD has its clause with x^ .  It is only ExDT which has
;; its clause with x

;; In ets.scm
;; (add-ids (list (list "ExDT" (make-arity) "yprod"))
;; 	 '("all x(Q x -> ExDT)" "InitExDT"))

(pp (formula-substitute
     (pf "exd x Q x")
     (list (list (predicate-form-to-predicate (pf "Q x^"))
		 (make-cterm (pv "x") (pf "x eqd x"))))))
;; exd x x eqd x

(define testformula1
  (pf "all n allnc m(exca n1 n=n1 -> excl m1,m2(m1=m2 and F))"))

(formula-to-free testformula1)
(ex-free-formula? testformula1)
(pp (nbe-formula-to-type testformula1))
(length (formula-to-prime-subformulas testformula1))

(alpha-equal-formulas-to-renaming
 (pf "all p allnc unit(exca p1 p=p1 ->
                       excl unit1,unit2(unit1=unit2 and F))")
 (pf "all p allnc unit(exca p1 p=p1 ->
                       excl unit1,unit3(unit1=unit3 and F))"))

(var-to-string
 (var-and-vars-to-new-var
  (pv "n100") (list (pv "n") (pv "n2") (pv "n19") (pv "n1") (pv "m0"))))
;; "n0"

;; Tests for rename-variables

(pp (aconst-to-formula (all-formulas-to-ind-aconst (pf "all n n=n"))))

;; all n1987(
;;  0=0 -> all n1988(n1988=n1988 -> Succ n1988=Succ n1988) -> n1987=n1987)

(pp (rename-variables
     (aconst-to-formula (all-formulas-to-ind-aconst (pf "all n n=n")))))

;; all n(0=0 -> all n0(n0=n0 -> Succ n0=Succ n0) -> n=n)

(pp (rename-variables
     (aconst-to-formula
      (all-formula-and-number-to-gind-aconst (pf "all n n=n") 1))))

;; all (nat=>nat),n(
;;  all n0(all n1((nat=>nat)n1<(nat=>nat)n0 -> n1=n1) -> n0=n0) ->
;;  all boole0(boole0 -> n=n))

;; In boole.scm

;; Tests for mk-ysum-without-unit

(pp (mk-ysum-without-unit (py "unit")))
;; unit ;this is the only case where unit can appear in the value

(pp (mk-ysum-without-unit (py "alpha1") (py "alpha2")))
;; alpha1 ysum alpha2

(pp (mk-ysum-without-unit (py "unit") (py "alpha")))
;; uysum alpha

(pp (mk-ysum-without-unit (py "alpha") (py "unit")))
;; alpha ysumu

(pp (mk-ysum-without-unit (py "unit") (py "unit")))
;; boole

(pp (mk-ysum-without-unit (py "alpha1") (py "alpha2") (py "alpha3")))
;; alpha1 ysum alpha2 ysum alpha3

(pp (mk-ysum-without-unit (py "unit") (py "alpha1") (py "alpha2")))
;; uysum(alpha1 ysum alpha2)

(pp (mk-ysum-without-unit (py "alpha1") (py "unit") (py "alpha2")))
;; alpha1 ysum uysum alpha2

(pp (mk-ysum-without-unit (py "alpha1") (py "alpha2") (py "unit")))
;; alpha1 ysum alpha2 ysumu

(pp (mk-ysum-without-unit (py "unit") (py "unit") (py "alpha")))
;; uysum uysum alpha

(pp (mk-ysum-without-unit (py "unit") (py "alpha") (py "unit")))
;; uysum alpha ysumu

(pp (mk-ysum-without-unit (py "alpha") (py "unit") (py "unit")))
;; alpha ysum boole

;; Tests for ysum-without-unit-to-components

(for-each pp (ysum-without-unit-to-components (py "alpha")))
;; alpha

(for-each pp (ysum-without-unit-to-components (py "unit")))
;; unit

(for-each pp (ysum-without-unit-to-components (py "alpha1 ysum alpha2")))
;; alpha1
;; alpha2

(for-each pp (ysum-without-unit-to-components (py "uysum alpha")))
;; unit
;; alpha

(for-each pp (ysum-without-unit-to-components (py "alpha ysumu")))
;; alpha
;; unit

(for-each pp (ysum-without-unit-to-components (py "boole")))
;; unit
;; unit

(for-each pp (ysum-without-unit-to-components (py "alpha1 ysum alpha2 ysum alpha3")))
;; alpha1
;; alpha2
;; alpha3

(for-each pp (ysum-without-unit-to-components (py "uysum(alpha1 ysum alpha2)")))
;; unit
;; alpha1
;; alpha2

(for-each pp (ysum-without-unit-to-components (py "alpha1 ysum uysum alpha2")))
;; alpha1
;; unit
;; alpha2

(for-each pp (ysum-without-unit-to-components (py "(alpha1 ysum alpha2)ysumu")))
;; alpha1
;; alpha2
;; unit

(for-each pp (ysum-without-unit-to-components (py "uysum(uysum alpha)")))
;; unit
;; unit
;; alpha


(for-each pp (ysum-without-unit-to-components (py "uysum(alpha ysumu)")))
;; unit
;; alpha
;; unit

(for-each pp (ysum-without-unit-to-components (py "alpha ysum boole")))
;; alpha
;; unit
;; unit

(for-each pp (ysum-without-unit-to-components (py "uysum boole")))
;; unit
;; unit
;; unit

(for-each pp (ysum-without-unit-to-components (py "alpha ysum uysum boole")))
;; alpha
;; unit
;; unit
;; unit

;; All these are inverse to mk-ysum-without-unit:

(pp (apply mk-ysum-without-unit (ysum-without-unit-to-components (py "unit"))))
(pp (apply mk-ysum-without-unit (ysum-without-unit-to-components (py "boole"))))
(pp (apply mk-ysum-without-unit (ysum-without-unit-to-components (py "uysum alpha"))))
(pp (apply mk-ysum-without-unit (ysum-without-unit-to-components (py "alpha ysumu"))))
(pp (apply mk-ysum-without-unit (ysum-without-unit-to-components (py "alpha1 ysum alpha2"))))

;; Tests for make-injection

(pp (make-injection (py "alpha1 ysum alpha2") 0))
;; (InL alpha1 alpha2)

(pp (make-injection (py "alpha1 ysum alpha2") 1))
;; (InR alpha2 alpha1)

(pp (make-injection (py "alpha1 ysum alpha2 ysum alpha3") 0))
;; (InL alpha1 (alpha2 ysum alpha3))

(pp (rename-variables (make-injection (py "alpha1 ysum alpha2 ysum alpha3") 1)))
;; [alpha2](InR (alpha2 ysum alpha3) alpha1)((InL alpha2 alpha3)alpha2)

(pp (rename-variables (make-injection (py "alpha1 ysum alpha2 ysum alpha3") 2)))
;; [alpha3](InR (alpha2 ysum alpha3) alpha1)((InR alpha3 alpha2)alpha3)

(pp (make-injection (py "uysum alpha") 0))
;; (DummyL alpha)

(pp (make-injection (py "uysum alpha") 1))
;; (InrUysum alpha)

(pp (make-injection (py "alpha ysumu") 0))
;; (InlYsumu alpha)

(pp (make-injection (py "alpha ysumu") 1))
;; (DummyR alpha)

(pp (make-injection (py "uysum(alpha1 ysum alpha2)") 0))
;; (DummyL alpha1 ysum alpha2)

(pp (rename-variables (make-injection (py "uysum(alpha1 ysum alpha2)") 1)))
;; [alpha1]Inr((InL alpha1 alpha2)alpha1)

(pp (rename-variables (make-injection (py "uysum(alpha1 ysum alpha2)") 2)))
;; [alpha2]Inr((InR alpha2 alpha1)alpha2)

(pp (make-injection (py "alpha1 ysum alpha2 ysumu") 0))
;; (InL alpha1 (alpha2 ysumu))

(pp (rename-variables (make-injection (py "alpha1 ysum alpha2 ysumu") 1)))
;; [alpha2](InR (alpha2 ysumu) alpha1)Inl alpha2

(pp (make-injection (py "alpha1 ysum alpha2 ysumu") 2))
;; (InR (alpha2 ysumu) alpha1)(DummyR alpha2)

(pp (make-injection (py "uysum(alpha1 ysum alpha2 ysum alpha3)") 0))
;; (DummyL alpha1 ysum alpha2 ysum alpha3)

(pp (rename-variables
     (make-injection (py "uysum(alpha1 ysum alpha2 ysum alpha3)") 1)))
;; [alpha1]Inr((InL alpha1 (alpha2 ysum alpha3))alpha1)

(pp (rename-variables
     (make-injection (py "uysum(alpha1 ysum alpha2 ysum alpha3)") 2)))
;; [alpha2]
;;  Inr(([alpha2_0]
;;        (InR (alpha2 ysum alpha3) alpha1)((InL alpha2 alpha3)alpha2_0))
;;      alpha2)

(pp (nt (make-injection (py "uysum(alpha1 ysum alpha2 ysum alpha3)") 2)))
;; [alpha2_0]
;;  Inr((InR (alpha2 ysum alpha3) alpha1)((InL alpha2 alpha3)alpha2_0))

(pp (nt (make-injection (py "uysum(alpha1 ysum alpha2 ysum alpha3)") 3)))
;; [alpha3_0]
;;  Inr((InR (alpha2 ysum alpha3) alpha1)((InR alpha3 alpha2)alpha3_0))


