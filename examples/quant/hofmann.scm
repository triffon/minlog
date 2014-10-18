;; 2014-10-13.  hofmann.scm

;; (load "~/git/minlog/init.scm")

;; Proof of f continuous -> f circ f continuous

(add-tvar-name "real" "open")
(add-var-name "x" "y" (py "real"))
(add-var-name "f" (py "real=>real"))
(add-var-name "U" "V" "W" (py "open"))
(add-predconst-name "ee" (make-arity (py "real") (py "open") (py "boole")))

(add-token
 "in"
 'pred-infix
 (lambda (x y)
   ((string-and-arity-to-predconst-parse-function
     "ee" (make-arity (py "real") (py "open")))
    (- 1) x y)))

(add-predconst-display "ee" 'pred-infix "in")

;; An explicit proof,  with all steps shown.
;; ContLemma
(set-goal "all f(
     all x,V(f x in V -> ex U(x in U & all y(y in U -> f y in V))) -> 
     all x,W(f(f x)in W -> ex U(x in U & all y(y in U -> f(f y)in W))))")
(assume "f" "fCont" "x" "W" "Hyp1")

(inst-with-to "fCont" (pt "f x") (pt "W") "Hyp2")
(inst-with-to "Hyp2" "Hyp1" "W-ExHyp")
(drop "Hyp2" "Hyp1")
(by-assume-with "W-ExHyp" "V" "VHyp")

(inst-with-to "fCont" (pt "x") (pt "V") "Hyp3")
(assert "ex U(x in U & all y(y in U -> f y in V))")
 (use "Hyp3")
 (use "VHyp")
 (assume "V-ExHyp")
;; ex U(x in U & all y(y in U -> f(f y)in W))
(by-assume-with "V-ExHyp" "U" "UHyp")
(ex-intro (pt "U"))
(split)
(use "UHyp")
(assume "y" "yHyp")
(use "VHyp")
(use "UHyp")
(use "yHyp")
;; Proof finished.
(save "ContLemma")

;; (check-and-display-proof (theorem-name-to-proof "ContLemma"))
;; (proof-to-expr-with-formulas (np (theorem-name-to-proof "ContLemma")))

;; This proof is constructive, hence has some computational content:
(add-var-name "M" (py "real=>open=>open")) ;M for modulus

(define eterm (proof-to-extracted-term (theorem-name-to-proof "ContLemma")))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [f,M,x,U]M x(M(f x)U)

;; One can also proof this for the classical existential quantifier excl.
(set-goal "all f(
      (all x,V(f x in V -> excl U(x in U ! all y(y in U -> f y in V)))) -> 
      all x,W(f(f x)in W -> excl U(x in U ! all y(y in U -> f(f y)in W))))")
(search)
;; Proof finished.
;; (cdp)
