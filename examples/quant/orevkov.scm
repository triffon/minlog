;; 2014-10-13.  orevkov.scm

;; (load "~/git/minlog/init.scm")

(add-var-name "x" "y" "z" "zero" (py "alpha"))
(add-var-name "S" (mk-arrow (py "alpha") (py "alpha")))
(add-predconst-name "R" (make-arity (py "alpha") (py "alpha") (py "alpha")))

(define hyp1-formula (pf "all y R y zero(S y)"))
(define hyp2-formula (pf "all y,x,z,z1(R y x z -> R z x z1 -> R y(S x)z1)"))

(define hyp1 (make-avar hyp1-formula 1 "hyp"))
(define hyp2 (make-avar hyp2-formula 2 "hyp"))

(define (a i)
  (if (zero? i)
      (pf "all y(all z(R y x z -> bot) -> bot)")
      (let* ((xterm (pt "x"))
	     (xvar (term-in-var-form-to-var xterm))
	     (yterm (pt "y"))
	     (yvar (term-in-var-form-to-var yterm))
	     (zterm (pt "z"))
	     (zvar (term-in-var-form-to-var zterm)))
	(mk-all
	 yvar
	 (mk-imp (formula-subst (a (- i 1)) xvar yterm)
		 (make-all
		  zvar (make-imp (formula-subst (a (- i 1)) xvar zterm)
				 (pf "R y x z -> bot")))
		 falsity-log)))))

(pp (a 0))
;; all y(all z(R y x z -> bot) -> bot)

(pp (rename-variables (a 1)))
;; all y(
;;  all y0(all z(R y0 y z -> bot) -> bot) -> 
;;  all z(all y0(all z0(R y0 z z0 -> bot) -> bot) -> R y x z -> bot) -> bot)

(pp (fold-formula (a 0)))
;; all y excl z R y x z

(pp (rename-variables (fold-formula (a 1))))
;; all y(all y0 excl z R y0 y z -> excl z(all y0 excl z0 R y0 z z0 ! R y x z))

(define (a0 i) (formula-subst (a i) (pv "x") (pt "zero")))

;; We directly construct proofs of theorems "D i": A_i 0 whose length
;; is bounded by a constant.  

;; (astepproof i) proves all x(A_i(x) -> A_i(S x))

(define (astepavar i) (make-avar (a i) -1 "d"))

(define (astepproof i)
  (let ((d (make-avar (a i) -1 "d"))
	(e3 (make-avar (pf "R y x z") 3 "e"))
	(e5 (make-avar (pf "R z x z1") 5 "e")))
    (if
     (zero? i)
     (let ((w (make-avar (make-all (pv "z") (pf "R y(S x)z -> bot")) -1 "w")))
       (mk-proof-in-intro-form
	(pv "x") d (pv "y") w
	(mk-proof-in-elim-form
	 (make-proof-in-avar-form d)
	 (pt "y")
	 (mk-proof-in-intro-form
	  (pv "z") e3
	  (mk-proof-in-elim-form
	   (make-proof-in-avar-form d)
	   (pt "z")
	   (mk-proof-in-intro-form
	    (pv "z1") e5
	    (mk-proof-in-elim-form
	     (make-proof-in-avar-form w)
	     (pt "z1")
	     (mk-proof-in-elim-form
	      (make-proof-in-avar-form hyp2)
	      (pt "y") (pt "x") (pt "z") (pt "z1")
	      (make-proof-in-avar-form e3)
	      (make-proof-in-avar-form e5)))))))))
					;else i positive
     (let
	 ((e1 (make-avar (formula-subst (a (- i 1)) (pv "x") (pt "y")) 1 "e"))
	  (e2 (make-avar (formula-subst (a (- i 1)) (pv "x") (pt "z")) 2 "e"))
	  (e4 (make-avar (formula-subst (a (- i 1)) (pv "x") (pt "z1")) 4 "e"))
	  (w (make-avar
	      (make-all
	       (pv "z1")
	       (make-imp (formula-subst (a (- i 1)) (pv "x") (pt "z1"))
			 (pf "R y(S x) z1 -> bot")))
	      -1 "w")))
       (mk-proof-in-intro-form
	(pv "x") d (pv "y") e1 w
       (mk-proof-in-elim-form
	(make-proof-in-avar-form d)
	(pt "y")
	(make-proof-in-avar-form e1)
	(mk-proof-in-intro-form
	 (pv "z") e2 e3
	 (mk-proof-in-elim-form
	  (make-proof-in-avar-form d)
	  (pt "z")
	  (make-proof-in-avar-form e2)
	  (mk-proof-in-intro-form
	   (pv "z1") e4 e5
	   (mk-proof-in-elim-form
	    (make-proof-in-avar-form w)
	    (pt "z1")
	    (make-proof-in-avar-form e4)
	    (mk-proof-in-elim-form
	     (make-proof-in-avar-form hyp2)
	     (pt "y") (pt "x") (pt "z") (pt "z1")
	     (make-proof-in-avar-form e3)
	     (make-proof-in-avar-form e5))))))))))))

;; (cdp (astepproof 0))
;; (cdp (astepproof 1))
;; (proof-to-expr-with-formulas (astepproof 0))
;; (proof-to-expr-with-formulas (astepproof 1))

;; (azeroproof i) proves A_i(0).

(define (azeroproof i)
  (if
   (zero? i)
   (let ((u (make-avar (pf "all z(R y zero z -> bot)") -1 "u")))
     (mk-proof-in-intro-form
      (pv "y") u
      (mk-proof-in-elim-form
       (make-proof-in-avar-form u) (pt "S y")
       (make-proof-in-all-elim-form
	(make-proof-in-avar-form hyp1) (pt "y")))))
   (let ((d (make-avar (a (- i 1)) -1 "d"))
	 (e (make-avar
	     (make-all (pv "z")
		       (make-imp (formula-subst (a (- i 1)) (pv "x") (pt "z"))
				 (pf "R x zero z -> bot")))
	     0 "e")))
     (mk-proof-in-intro-form
      (pv "x") d e
      (mk-proof-in-elim-form
       (make-proof-in-avar-form e) (pt "S x")
       (mk-proof-in-elim-form
	(astepproof (- i 1))
	(pt "x")
	(make-proof-in-avar-form d))
       (make-proof-in-all-elim-form
	(make-proof-in-avar-form hyp1) (pt "x")))))))

;; (cdp (azeroproof 2))
;; (proof-to-expr (azeroproof 2))
;; (proof-to-expr-with-formulas (azeroproof 2))

(classical-formula=? (a0 2) (proof-to-formula (azeroproof 2)))
;; #t

;; (aoneproof i) proves A_i(S 0): apply (astepproof i) to zero and
;; (azeroproof 0).

(define (aoneproof i)
  (mk-proof-in-elim-form (astepproof i) (pt "zero") (azeroproof i)))

;; (cdp (aoneproof 1))
;; (cdp (rename-bound-avars (aoneproof 1)))

;; (proof-to-expr (aoneproof 1))
;; (proof-to-expr (rename-bound-avars (aoneproof 1)))

;; (bproof i) proves falsity-log (written bot, hence bproof) from
;; u_i:A_{i-1}(z_i) (if i>0), v_i:R zero z_{i+1} z_i and w_i.  The
;; height of this tree will be linear in i.

(define (zvar i) (make-var (py "alpha") i t-deg-one "z"))
(define (zterm i) (make-term-in-var-form (zvar i)))
(define (uavar i) (make-avar
		   (formula-subst (a (- i 1)) (pv "x") (zterm i))
		   i "u"))
(define (r i)
  (make-predicate-formula
   (make-predconst
    (make-arity (py "alpha")  (py "alpha")  (py "alpha"))
    empty-subst -1 "R")
   (pt "zero") (zterm (+ i 1)) (zterm i)))

;; (pp (r 2))
;; R zero z3 z2

(define (vavar i) (make-avar (r i) i "v"))
(define (wformula i)
  (if
   (zero? i)
   (pf "all z0(R zero z1 z0 -> bot)")
   (make-all (zvar i) (make-imp (r i) (wformula (- i 1))))))

;; (pp (wformula 2))
;; "all z2(R zero z3 z2 -> all z1(R zero z2 z1 -> all z0(R zero z1 z0 -> bot)))"

(define (wavar i) (make-avar (wformula i) i "w"))

(define (bproof i)
  (if (zero? i)
      (mk-proof-in-elim-form
       (make-proof-in-avar-form (wavar 0))
       (zterm 0)
       (make-proof-in-avar-form (vavar 0)))
      (let* ((prev (bproof (- i 1)))
	     (subst-prev (proof-subst
			  prev
			  (wavar (- i 1))
			  (mk-proof-in-elim-form
			   (make-proof-in-avar-form (wavar i))
			   (zterm i)
			   (make-proof-in-avar-form (vavar i))))))
	(if (zero? (- i 1))
	    (mk-proof-in-elim-form
	     (make-proof-in-avar-form (uavar i))
	     (pt "zero")
	     (mk-proof-in-intro-form
	      (zvar (- i 1)) (vavar (- i 1))
	      subst-prev))
	    (mk-proof-in-elim-form
	     (make-proof-in-avar-form (uavar i))
	     (pt "zero")
	     (azeroproof (- i 2))
	     (mk-proof-in-intro-form
	      (zvar (- i 1)) (uavar (- i 1)) (vavar (- i 1))
	      subst-prev))))))

(map avar-to-string (proof-to-free-avars (bproof 0)))
;; ("w0" "v0")
(map avar-to-string (proof-to-free-avars (bproof 1)))
;; ("u1" "w1" "v1")
(map avar-to-string (proof-to-free-avars (bproof 2)))
;; ("u2" "hyp1" "w2" "v2")
(map avar-to-string (proof-to-free-avars (bproof 3)))
;; ("u3" "hyp2" "hyp1" "w3" "v3")

(map var-to-string (formula-to-free (avar-to-formula (uavar 2))))
;; ("z2")
(map var-to-string (formula-to-free (avar-to-formula (vavar 2))))
;; ("zero" "z3" "z2")
(map var-to-string (formula-to-free (avar-to-formula (wavar 2))))
;; ("zero" "z3")

;; In (bproof i) whose free avars are all of u_i:A_{i-1}(z_i) (if i>0),
;; v_i:R zero z_{i+1} z_i and w_i we want to substitute z_{i+1} by zero
;; and z_i by (S zero), for then v_i becomes provable by hyp1.  To have
;; an admissible substitution we need to substitute u_i:A_{i-1}(z_i) by
;; uone_i:A_{i-1}(S zero), v_i:R zero z_{i+1} z_i by (hyp1 zero) and
;; w_i by wzero_i, where the free variable z_{i+1} in w_i is replaced
;; by zero.

(define (uoneavar i)
  (if (zero? i) (myerror "uoneavar" "positive integer expected" i))
  (make-avar (formula-subst (a (- i 1)) (pv "x") (pt "S zero"))
	     i "uone"))

(define (wzeroavar i)
  (make-avar (formula-subst (wformula i) (zvar (+ i 1)) (pt "zero"))
	     i "wzero"))

(define (oasubst i)
  (if (zero? i)
      (list (list (zvar i) (pt "S zero"))
	    (list (zvar (+ i 1)) (pt "zero"))
	    (list (vavar i) (make-proof-in-all-elim-form
			     (make-proof-in-avar-form hyp1) (pt "zero")))
	    (list (wavar i) (make-proof-in-avar-form (wzeroavar i))))
      (list (list (zvar i) (pt "S zero"))
	    (list (zvar (+ i 1)) (pt "zero"))
	    (list (uavar i) (make-proof-in-avar-form (uoneavar i)))
	    (list (vavar i) (make-proof-in-all-elim-form
			     (make-proof-in-avar-form hyp1) (pt "zero")))
	    (list (wavar i) (make-proof-in-avar-form (wzeroavar i))))))

(admissible-substitution? (oasubst 2) (bproof 2))
;; #t

(define (bzerooneproof i) (proof-substitute (bproof i) (oasubst i)))

;; (cdp (bzerooneproof 2))
;; (proof-to-expr-with-formulas (bzerooneproof 3))

(map avar-to-string (proof-to-free-avars (bzerooneproof 3)))
;; ("uone3" "hyp2" "hyp1" "wzero3")

;; (cdp (bzerooneproof 0))

;; To get at the desired assumption variables (to be abstracted and
;; then applied to a proof of A_{i-1}(S zero)), and also for brevity,
;; instead of (azeroproof (- i 1)) we should use the theorem with name
;; "AZero".  But we need infinitely many theorems!  Alternative: only
;; take the newly created avars, whose name is different form "hyp".

(define (cproof i)
  (if
   (zero? i)
   (let* ((proof (bzerooneproof i))
	  (avars (list-transform-positive (proof-to-free-avars proof)
		   (lambda (avar) (not (string=? "hyp" (avar-to-name avar))))))
	  (wzero (car avars)))
     (make-proof-in-imp-intro-form wzero proof))
   (let* ((proof (bzerooneproof i))
	  (avars (list-transform-positive (proof-to-free-avars proof)
		   (lambda (avar) (not (string=? "hyp" (avar-to-name avar))))))
	  (uone (car avars))
	  (wzero (cadr avars))
	  (subst-proof (proof-subst proof uone (aoneproof (- i 1)))))
     (make-proof-in-imp-intro-form wzero subst-proof))))

;; (cdp (cproof 0))
;; (proof-to-expr (cproof 0))
;; (cdp (cproof 1))
;; (proof-to-expr (cproof 1))
;; (cdp (cproof 2))
;; (cdp (rename-bound-avars (cproof 2)))
;; (proof-to-expr (cproof 2))
;; (cdp (cproof 3))
;; (cdp (rename-bound-avars (cproof 3)))

;; Now we need cdproof

(define (c i)
  (if (zero? i)
      falsity-log
      (make-all (zvar (- i 1)) (make-imp (r (- i 1)) (c (- i 1))))))

(define (czero i) (formula-subst (c i) (zvar i) (pt "zero")))
(pp (czero 2))
;; all z1(R zero zero z1 -> all z0(R zero z1 z0 -> bot))

(define (dimp i)
  (if (zero? i)
      falsity-log
      (make-imp (r (- i 1)) (dimp (- i 1)))))

(pp (dimp 2))
;; R zero z2 z1 -> R zero z1 z0 -> bot

(define (dimpzero i) (formula-subst (dimp i) (zvar i) (pt "zero")))

(formula-to-string (dimpzero 2))
;; "R zero zero z1 -> R zero z1 z0 -> bot"

(define (zvars i)
  (if (zero? i) '()
      (cons (zvar (- i 1)) (zvars (- i 1)))))

(define (zterms i)
  (map make-term-in-var-form (zvars i)))

(define (dprem i)
  (apply mk-all (append (zvars i) (list (dimpzero i)))))

(pp (dprem 3))
;; all z2,z1,z0(R zero zero z2 -> R zero z2 z1 -> R zero z1 z0 -> bot)

(define (d i) (make-imp (dprem i) falsity-log))

(pp (d 3))
;; all z2,z1,z0(R zero zero z2 -> R zero z2 z1 -> R zero z1 z0 -> bot) -> bot

(pp (fold-formula (d 3)))
;; excl z2,z1,z0(R zero zero z2 ! R zero z2 z1 ! R zero z1 z0)

(define (cpremzeroavar i) (make-avar (czero i) i "c"))
(define (dpremavar i) (make-avar (dprem i) i "d"))
(define (czeroavar i) (make-avar (make-imp (czero i) falsity-log) i "c"))

;; (cdp (make-proof-in-avar-form (czeroavar 2)))
;; (cdp (make-proof-in-avar-form (dpremavar 2)))
(pp (proof-to-formula (make-proof-in-avar-form (dpremavar 2))))
;; all z1,z0(R zero zero z1 -> R zero z1 z0 -> bot)

(define (zvvars i)
  (if (zero? i) '()
      (cons (zvar (- i 1)) (cons (vavar (- i 1)) (zvvars (- i 1))))))

(define (vavars i)
  (if (zero? i) '()
      (cons (vavar (- i 1)) (vavars (- i 1)))))

(map formula-to-string (map avar-to-formula (vavars 3)))
;; ("R zero z3 z2" "R zero z2 z1" "R zero z1 z0")

(define (vprimeavar i) (make-avar (rprime i) i "v"))

(define (rprime i)
  (make-predicate-formula
   (make-predconst
    (make-arity (py "alpha")  (py "alpha")  (py "alpha"))
    empty-subst -1 "R")
   (pt "zero") (pt "zero") (zterm i)))

(define (cdproof i)
  (make-proof-in-imp-intro-form
   (dpremavar i)
   (make-proof-in-imp-elim-form
    (make-proof-in-avar-form (czeroavar i))
    (apply
     mk-proof-in-intro-form
     (append
      (list (zvar (- i 1)) (vprimeavar (- i 1)))
      (zvvars (- i 1))
      (list
       (apply mk-proof-in-elim-form
	      (append (list (make-proof-in-avar-form (dpremavar i)))
		      (zterms i)
		      (list (make-proof-in-avar-form (vprimeavar (- i 1))))
		      (map make-proof-in-avar-form (vavars (- i 1)))))))))))

;; (cdp (cdproof 3))
;; (proof-to-expr (cdproof 3))

;; (lambda (d3)
;;   (c3 (lambda (z2)
;;         (lambda (v2)
;;           (lambda (z1)
;;             (lambda (v1)
;;               (lambda (z0)
;;                 (lambda (v0) ((((((d3 z2) z1) z0) v2) v1) v0)))))))))

(define (dproof i)
  (if (zero? i)
      (cproof 0)
      (rename-bound-avars
       (proof-subst (cdproof (+ i 1))
		    (czeroavar (+ i 1))
		    (cproof i)))))

;; (cdp (dproof 2))
;; (proof-to-expr (dproof 2))

;; Now the A-translation

(define (ex-proof i) (atr-min-excl-proof-to-ex-proof (dproof i)))

;; (cdp (ex-proof 2))
(define eterm (proof-to-extracted-term (ex-proof 2)))
(pp (nt eterm))
;; S zero@S(S zero)@S(S(S(S zero)))

;; (cdp (ex-proof 3))
(define eterm (proof-to-extracted-term (ex-proof 3)))
(pp (nt eterm))
;; S zero@
;; S(S zero)@
;; S(S(S(S zero)))@S(S(S(S(S(S(S(S(S(S(S(S(S(S(S(S zero)))))))))))))))
