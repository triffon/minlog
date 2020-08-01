;; (load "~/git/minlog/init.scm")
(load "names.scm")

;; 6. Terms
;; ========
;; (term.scm and pp.scm)

(define testterms
  (list
   (pt "p^1")
   (pt "p1")
   (pt "x^1")
   (pt "x_1")
   (pt "nat=>boole 2")
   (pt "nat=>boole_ 2")
   (pt "nat=>boole^ 2")
   (pt "nat=>boole_2 2")
   (pt "nat=>boole^2 2")
   (pt "(nat=>alpha)2")
   (pt "(nat=>alpha)_ 2")
   (pt "(nat=>alpha)^ 2")
   (pt "(nat=>alpha)_2 2")
   (pt "(nat=>alpha)^2 2")
   (pt "(nat=>alpha2)_2 2")
   (pt "(nat=>alpha2)^2 2")
   (pt "p^1=p^2")
   (pt "NatPlus")
   (pt "(Rec nat=>alpha)")
   (pt "(Rec nat=>alpha)2")
   (pt "(Rec nat=>alpha)2 x")
   (pt "(Rec nat=>alpha)2 x(nat=>alpha=>alpha)")
   (pt "(Rec nat=>nat)n 0([n]Succ)")
   (pt "(Rec nat=>nat)2 0([n]Succ)")
   (pt "(GRecGuard nat alpha)")
   (pt "(GRecGuard nat boole)(nat=>nat)n([n,(nat=>boole)]False)")
   (pt "(GRecGuard nat boole)(nat=>nat)n([n,(nat=>boole)]False)True")))

;; Tests for term-to-scheme-expr

(map term-to-scheme-expr testterms)

;;  (lpar_nat=>boole_rpar 2) (lpar_nat=>boole_rpar^ 2)
;;  (lpar_nat=>boole_rpar_2 2) (lpar_nat=>boole_rpar^2 2)
;;  (lpar_nat=>alpha_rpar 2) (lpar_nat=>alpha_rpar 2)
;;  (lpar_nat=>alpha_rpar^ 2) (lpar_nat=>alpha_rpar_2 2)
;;  (lpar_nat=>alpha_rpar^2 2) (lpar_nat=>alpha2_rpar_2 2)
;;  (lpar_nat=>alpha2_rpar^2 2) (equal? p^1 p^2) NatPlus natRec
;;  (natRec 2) ((natRec 2) x)
;;  (((natRec 2) x) lpar_nat=>alpha=>alpha_rpar)
;;  (((natRec n) 0) (lambda (n) Succ))
;;  (((natRec 2) 0) (lambda (n) Succ)) natGrecGuard
;;  (((natGrecGuard lpar_nat=>nat_rpar) n)
;;    (lambda (n) (lambda (lpar_nat=>boole_rpar) #f)))
;;  ((((natGrecGuard lpar_nat=>nat_rpar) n)
;;     (lambda (n) (lambda (lpar_nat=>boole_rpar) #f)))
;;    #t))

;; 2012-10-27.  Tests for simplify-simrec-appterm

(add-var-name "a" "b" (py "ltree alpha"))
(add-var-name "as" "bs" (py "ltlist alpha"))
(add-var-name "u" (py "unit"))

(pp (term-to-type (pt "(Rec ltlist alpha=>nat ltree alpha=>unit)as 0")))

(define term
  (pt "(Rec ltlist alpha=>nat ltree alpha=>unit)as
0
([a,u,bs,n](Succ n))
([x]Dummy)
([as,n]Dummy)"))

(pp (simplify-simrec-appterm term))
;; (Rec ltlist alpha=>nat)as 0([bs,n]Succ n)

(define term
  (pt "(Rec ltree alpha=>unit ltlist alpha=>nat)a
0
([a,u,bs,n](Succ n))
([x]Dummy)
([as,n]Dummy)"))

(pp (simplify-simrec-appterm term))
;; (Rec ltree nat=>unit)a([x]Dummy)Dummy

;; Tests for unfold-simplified-simrec-appterm

(define term (pt "(Rec ltlist alpha=>nat)as 0([bs,n]Succ n)"))

(pp (rename-variables (unfold-simplified-simrec-appterm term)))

;; (Rec ltlist alpha=>nat ltree alpha=>ltree alpha)as 0([a,a0,bs,n]Succ n)
;; ([x](LLeaf alpha)(Inhab alpha))
;; ([as0,n](LLeaf alpha)(Inhab alpha))

(pp (nt (unfold-simplified-simrec-appterm term)))
;; (Rec ltlist boole=>nat)as 0([as2]Succ)

(remove-var-name "a" "b" "as" "bs" "u")

;; Tests for nt

;; Both nt and nbe-normalize-term-without-eta (i) need not terminate
;; (examples: Yf=f(Yf), corecursion) and (ii) for nullary pconsts may
;; only do a one-step conversion (example: for Om with computation
;; rule Om=Succ Om nt on Om returns the non-normal Succ Om).  (i) can
;; lead to non-termination of cdp, since formulas are compared after
;; normalizing them.  (ii) leads to correct proofs not accepted by cdp.
;; Example.

(add-program-constant "Omega" (py "nat"))
(add-computation-rule "Omega" "Succ Omega")

(pp (nt (pt "Omega")))
;; Succ Omega

(set-goal "Omega eqd Succ Omega")
(assert "all n^(n^ eqd Omega -> Succ n^ eqd Omega)")
 (assume "n^" "Hyp")
 (ng #t)
 (simp "Hyp")

;; (cdp)
;; equal formulas expected
;; Succ n^ eqd Succ Omega
;; Succ n^ eqd Omega

(remove-program-constant "Omega")

;; Tests for term-substitute

;; Simultaneously defined tree lists and trees with labels on leafs

(add-var-name "b" (py "beta"))
(add-var-name "f" (py "alpha=>alpha"))
(add-var-name "g" (py "beta=>beta"))

(pp (rename-variables (term-substitute
		       (pt "[x]f x")
		       (list (list (py "alpha") (py "beta"))
			     (list (pv "x") (pt "b"))
			     (list (pv "f") (pt "g"))))))
;; [b]g b

(remove-var-name "b" "f" "g")

;; A more complete test.

(for-each pp testterms)
(for-each (lambda (term) (pp (term-to-type term))) testterms)
(for-each (lambda (term) (pp (nt term))) testterms)

(define tosubst
  (make-substitution (list (py "alpha")
			   (pv "x")
			   (pv "x^1")
			   (pv "x_1")
			   (pv "(nat=>alpha)")
			   (pv "(nat=>alpha)_2")
			   (pv "(nat=>alpha)^2")
			   (pv "(nat=>alpha)^")
			   (pv "(nat=>alpha=>alpha)"))
		     (list (py "nat")
			   (pt "n")
			   (pt "n^1")
			   (pt "n_1")
			   (pt "(nat=>nat)")
			   (pt "(nat=>nat)_2")
			   (pt "(nat=>nat)^2")
			   (pt "(nat=>nat)^")
			   (pt "(nat=>nat=>nat)"))))

(for-each (lambda (term)
	    (if (admissible-substitution? tosubst term)
		(pp (term-substitute term tosubst))
		(begin (pp-subst tosubst)
		       (myerror "is not admissible for"
				term))))
	  testterms)

;; Tests for huet-match

(pp-subst (huet-match (pf "Q x^") (pf "Total x^")))
;;   Q ->  (cterm (x^1476) Total x^1476)

(pp-subst (huet-match (pf "(Pvar unit)unit^") (pf "Total x^")))
;;   (Pvar unit) ->  (cterm (unit^1479) Total x^)

(pp-subst (huet-match (pf "exr x^ (Pvar alpha)x^") (pf "exr n^ (Pvar nat)n^")))
;; alpha -> nat
;; (Pvar alpha) ->  (cterm (n^13622) (Pvar nat)n^13622)

;; Tests for huet-match with ignore-deco-flag set to #t

(add-pvar-name "P" (make-arity (py "boole")))

(define  pattern (pf "all p(P p -> P(negb p))"))
(define instance (pf "allnc p(P p --> P(negb p))"))

(huet-match pattern instance #t)
;; ()

(define  pattern (pf "all p(P p -> P(negb p)) -> all p(P True -> P p)"))
(define instance (pf "allnc p(P p --> P(negb p)) -> allnc p(P True --> P p)"))

(huet-match pattern instance #t)
;; ()

(add-var-name "f" (py "boole=>boole"))
(add-var-name "q" (py "boole"))

(define  pattern (pt "[p]f p andb f negb p"))
(define instance (pt "[p]f p andb f negb p"))

(huet-match pattern instance)
;; ()

(define pattern (pf "all p(P p -> P(negb p))"))
(define instance (pf "allnc p(exl q(p andb q) -> exl q(p andb q))"))
(huet-match pattern instance #t) ;#f

(define pattern (pf "all p(P p -> P(negb p))"))
(define instance (pf "allnc p(exl q(p andb q) -> exl q(p andb q))"))
(huet-match pattern instance #t) ;#f

(remove-var-name "q" "f")
(remove-pvar-name "P")

(pp-subst
 (huet-match
  (pf "all x^(Total x^ -> (Pvar alpha)x^)")
  (pf "all p^(Total p^ -> Total(boole=>boole=>boole^ p^))")))

;; alpha -> boole
;; (Pvar alpha) ->  (cterm (p^3265) Total((boole=>boole=>boole)^ p^3265))

(add-var-name "u" "c" (py "alpha=>(alpha=>beta)=>beta"))
(add-var-name "f" (py "alpha=>beta"))

(define pattern (pt "u x f"))
(define instance (pt "c x f"))

(pp-subst (huet-match pattern instance))
;;   u -> c

;; With cleaned-composed-subst rather than
;; cleaned-composed-subst-in-eta-nf in huet-match the result is
;;   u -> [x^114,f^113]c x^114([x^121]f^113 x^121)

(remove-var-name "u" "c" "f")

;; Florian Ranzi's examples:

(pp-subst
 (huet-match
  (pf "(Pvar boole)p12")
  (pf "p12=p12")))
;; (Pvar boole) ->  (cterm (p^3310) p^3310=p^3310)

(pp-subst
 (huet-match
  (pf "(Pvar boole)p^12")
  (pf "p^12 eqd p^12")))
;; (Pvar boole) ->  (cterm (p^3324) p^3324 eqd p^3324)

;; Tests for huet-match with products and projections

(add-var-name "f" (py "alpha=>alpha"))

(pp-subst (huet-match (pt "[x]f x") (pt "[x]x")))
;;   f -> [x^87]x^87

(add-var-name "xb" (py "alpha@@beta"))
(add-var-name "u" (py "alpha@@beta=>alpha"))

(pp-subst (huet-match (pt "u xb") (pt "left xb")))
;;   u -> [xb^101]left xb^101
(pp-subst (huet-match (pt "[xb]u xb") (pt "[xb]left xb")))
;;   u -> [xb^109]left xb^109

(remove-var-name "f" "xb" "u")
(add-var-name "u" (py "alpha=>beta=>alpha@@beta"))

(add-var-name "b" (py "beta"))

(pp-subst (huet-match (pt "u x b") (pt "x@b")))
;;   u -> [x^123,b^122]x^123@b^122
(pp-subst (huet-match (pt "[x,b]u x b") (pt "[x,b]x@b")))
;;   u -> [x^135,b^134]x^135@b^134

(remove-var-name "b" "u")

