;; (load "~/minlog/init.scm")
(load "names.scm")

;; 3. Variables
;; ============
;; (var.scm)

(define testvars (list (pv "p")
		       (pv "p_")
		       (pv "p^")
		       (pv "p2")
		       (pv "p_2")
		       (pv "p^2")
		       (pv "boole")
		       (pv "boole_")
		       (pv "boole^")
		       (pv "boole_2")
		       (pv "boole2")
		       (pv "boole^2")
		       (pv "(boole)_2")
		       (pv "(nat=>boole)_2")
		       (pv "(nat=>boole)^2")
		       (pv "(nat=>alpha2)")
		       (pv "(nat=>alpha2)_2")
		       (pv "(nat=>alpha2)^2")))

(for-each (lambda (var) (pp (make-term-in-var-form var))) testvars)

;; Compare how applicative terms are written:

(for-each pp (list (pt "(nat=>boole) 2")
		   (pt "(nat=>boole)_ 2")
		   (pt "(nat=>boole)^ 2")
		   (pt "(nat=>boole)_2 2")
		   (pt "(nat=>boole)^2 2")
		   (pt "(nat=>alpha)2")
		   (pt "(nat=>alpha)_ 2")
		   (pt "(nat=>alpha)^ 2")
		   (pt "(nat=>alpha)_2 2")
		   (pt "(nat=>alpha)^2 2")
		   (pt "(nat=>alpha2)_2 2")
		   (pt "(nat=>alpha2)^2 2")))
