;; 2014-10-13.  lnf.scm

;; (load "~/git/minlog/init.scm")

;; Tests for proceed

(set-goal "T")
(proceed "Truth")

(set-goal "F -> F")
(proceed)

(add-predconst-name "A" "B" (make-arity))

(define mints (pf "((((A -> B) -> A) -> A) -> B) -> B"))
(set-goal mints)
(proceed)

(add-var-name "x" "y" "z" (py "alpha"))
(add-predconst-name "P" (make-arity))
(add-predconst-name "Qpredconst" (make-arity (py "alpha")))
(add-predconst-name "Rpredconst" (make-arity (py "alpha") (py "alpha")))

(add-token
 "Q"
 'predconst-name
 (string-and-arity-to-predconst-parse-function
  "Qpredconst" (make-arity (make-tvar -1 "alpha"))))

(add-token
 "R"
 'pred-infix
 (lambda (x y)
   ((string-and-arity-to-predconst-parse-function
     "Rpredconst" (make-arity (make-tvar -1 "alpha") (make-tvar -1 "alpha")))
    (- 1) x y)))

(add-predconst-display "Qpredconst" 'predconst-name "Q")
(add-predconst-display "Rpredconst" 'pred-infix "R")

(set-goal "all x(Q1 x -> Q2 x) -> all x Q1 x -> all x Q2 x")
(proceed)
;; (cdp (np (current-proof)))

(set-goal "all x(Q1 x & Q2 x) -> all x Q1 x & all x Q2 x")
(proceed)

(set-goal "all x Q1 x & all x Q2 x -> all x(Q1 x & Q2 x)")
(proceed)

(add-global-assumption "Sym" (pf "all x,y(x R y -> y R x)"))
(add-global-assumption "Trans" (pf "all x,y,z(x R y -> y R z -> x R z)"))

(set-goal "all x,y(x R y -> x R x)")
;; (proceed "Sym" "Trans") loops

(set-goal "(P -> all y Q y) -> all y(P -> Q y)")
(proceed)

(set-goal "(exca x Q x -> P) -> all x(Q x -> P)")
(proceed)

(set-goal "all y(F -> Q y) -> (P -> exca y Q y) -> exca y(P -> Q y)")
(proceed)
