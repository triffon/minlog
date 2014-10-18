;; 2014-10-14.  nipkow.scm

;; Examples for pattern unification
;; Simple test examples (partially from Martin Kuebler)

;; (load "~/git/minlog/init.scm")

(add-var-name "x" "y" "z" (py "alpha"))
(add-var-name "f" "A" (py "alpha=>alpha"))
(add-var-name "g" "B" (py "alpha=>alpha=>alpha"))
(add-var-name "h" (py "alpha=>alpha=>alpha=>alpha"))

;; An example failing by rigid-rigid

  (pattern-unify
   (list (term-in-var-form-to-var (pt "A1"))
	 (term-in-var-form-to-var (pt "A2"))
	 (term-in-var-form-to-var (pt "B"))) ;sig-vars
   (list (term-in-var-form-to-var (pt "g"))) ;flex-vars
   '() ;forb-vars
   (list (pt "[x,y,z]B(g x y)(g x z)")
	 (pt "[x,y,z]B(A1 x)(A2 y)")))

;; An example using pointwise intersection in flex-flex

(define pair
  (pattern-unify
   (list (term-in-var-form-to-var (pt "A"))) ;sig-vars
   (list (term-in-var-form-to-var (pt "h"))) ;flex-vars
   '() ;forb-vars
   (list (pt "[y1,y2,y3,y4]h y1 y3 y4")
	 (pt "[y1,y2,y3,y4]h y2 y3 y4"))))

(display-substitution (car pair))
;; h	->	[y1,y3,y4]g13 y3 y4

(define pair
  (pattern-unify
   (list (term-in-var-form-to-var (pt "A"))) ;sig-vars
   (list (term-in-var-form-to-var (pt "h"))) ;flex-vars
   '() ;forb-vars
   (list (pt "[y1,y2,y3,y4]h y1 y2 y4")
	 (pt "[y1,y2,y3,y4]h y1 y3 y4"))))

(display-substitution (car pair))
;; h	->	[y1,y2,y4]g14 y1 y4

(define pair
  (pattern-unify
   (list (term-in-var-form-to-var (pt "A"))) ;sig-vars
   (list (term-in-var-form-to-var (pt "h"))) ;flex-vars
   '() ;forb-vars
   (list (pt "[y1,y2,y3,y4]h y1 y2 y4")
	 (pt "[y1,y2,y3,y4]h y2 y3 y4"))))

(display-substitution (car pair))
;; h	->	[y1,y2,y4]f15 y4

(define pair
  (pattern-unify
   (list (term-in-var-form-to-var (pt "A"))) ;sig-vars
   (list (term-in-var-form-to-var (pt "g"))) ;flex-vars
   '() ;forb-vars
   (list (pt "[x,y,z]A(g x y)")
	 (pt "[x,y,z]A(g y z)"))))

(display-substitution (car pair))
;; g	->	[x,y]x5

(apply display-prefix (cdr pair)) ;; -> under all A ex x5 all x,y,z

;; An example showing some effects of flex-flex

(define pair
  (pattern-unify
   (list (term-in-var-form-to-var (pt "B"))) ;sig-vars
   (list (term-in-var-form-to-var (pt "g1"))
	 (term-in-var-form-to-var (pt "g2"))
	 (term-in-var-form-to-var (pt "g3"))) ;flex-vars
   '() ;forb-vars
   (list (pt "[x,y,z]B(g2 x y)(g1 x z)")
	 (pt "[x,y,z]B(g3 x z)(g3 x y)"))))

(display-substitution (car pair))
;; g1	->	[x,z]f4 x
;; g2	->	[x,y]f4 x
;; g3	->	[x,z]f4 x

(apply display-prefix (cdr pair)) ;; -> under all B ex f4 all x,y,z

;; An example where unification fails because of the occurs check.

  (pattern-unify
   (list (term-in-var-form-to-var (pt "A"))
	 (term-in-var-form-to-var (pt "B"))) ;sig-vars
   (list (term-in-var-form-to-var (pt "g1"))
	 (term-in-var-form-to-var (pt "g2"))) ;flex-vars
   '() ;forb-vars
   (list (pt "[x,y,z]B(g1 x y)(g2 x z)")
	 (pt "[x,y,z]B(g2 x y)(A(g1 x z))")))

;; An example where pruning is not successful

  (pattern-unify
   (list (term-in-var-form-to-var (pt "A"))) ;sig-vars
   (list (term-in-var-form-to-var (pt "g"))) ;flex-vars
   '() ;forb-vars
   (list (pt "[x,y,z]g x y")
	 (pt "[x,y,z]A z")))

;; An example where pruning is successful

(define pair
  (pattern-unify
   (list (term-in-var-form-to-var (pt "A"))) ;sig-vars
   (list (term-in-var-form-to-var (pt "g1"))
	 (term-in-var-form-to-var (pt "g2"))) ;flex-vars
   '() ;forb-vars
   (list (pt "[x,y,z]g1 x y")
	 (pt "[x,y,z]A(g2 x z)"))))

(display-substitution (car pair))
;; g1	->	[x,y]A(f3 x)
;; g2	->	[x,z]f3 x

(apply display-prefix (cdr pair)) ;; -> under all A ex f3 all x,y,z

;; Dale Miller's example

(add-var-name "G" (py "(alpha=>alpha)=>alpha"))

(define pair
  (pattern-unify
   (list (term-in-var-form-to-var (pt "G"))) ;sig-vars
   (list (term-in-var-form-to-var (pt "h"))
	 (term-in-var-form-to-var (pt "f"))) ;flex-vars
   (list (term-in-var-form-to-var (pt "y"))) ;forb-vars
   (list (pt "G([x]G(h x y))")
	 (pt "G([z]f y)"))))

(display-substitution (car pair))
;; f	->	[y]G(g6 y)
;; h	->	[x]g6

(apply display-prefix (cdr pair)) ;; -> under all G ex g6 all y,x

;; Nipkow's example: critical pair of untyped lambda calculus

(add-var-name "App" (py "alpha=>alpha=>alpha"))
(add-var-name "Abs" (py "(alpha=>alpha)=>alpha"))

(define pair1
  (pattern-unify
   (list (term-in-var-form-to-var (pt "App"))
	 (term-in-var-form-to-var (pt "Abs"))) ;sig-vars
   (list (term-in-var-form-to-var (pt "f"))
	 (term-in-var-form-to-var (pt "g"))
	 (term-in-var-form-to-var (pt "z"))) ;flex-vars
   '() ;forb-vars
   (list (pt "[x]App z x")
	 (pt "[x]App(Abs([y]g x y))(f x)"))))

(display-substitution (car pair1))
;; f	->	[x]x
;; z	->	Abs([y]f0 y)
;; g	->	[x]f0

(apply display-prefix (cdr pair1))  ;-> under all App,Abs ex f0 all x

(remove-var-name "x" "y" "z" "f" "g" "h" "A" "B" "G" "App" "Abs")
