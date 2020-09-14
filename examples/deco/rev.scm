;; 2014-10-18.  rev.scm.  Based on lectures/proofth/ss07/rev07.scm

;; (load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(libload "list.scm")
(set! COMMENT-FLAG #t)

;; 1.  Formalization of the weak existence proof
;; =============================================

(add-var-name "rev" (py "list nat=>list nat=>boole"))

;; We want x as the default variable of type nat, hence

(remove-var-name "n" "m" "l")
(add-var-name "x" "y" "n" (py "nat"))
(add-var-name "v" "w" (py "list nat"))

;; ExclRev
(set-goal "allnc rev all v(
      rev(Nil nat)(Nil nat) -> 
      all v,w,x(rev v w -> rev(v++x:)(x::w)) ->
      excl w rev v w)")
(assume "rev" "v" "InitRev" "GenRev" "u")
(assert "all v2,v1(v1++v2=v -> all w(rev v1 w -> bot))")
 (ind)
 ;; Base
 (ng)
 (assume "v1" "u0")
 (simp "u0")
 (use "u")
 ;; Step
 (assume "x" "v2" "IH" "v1" "u1" "w" "u2")
 (use-with "IH" (pt "v1++x:") "?" (pt "x::w") "?")
 (ng)
 (use "u1")
 (use "GenRev")
 (use "u2")
;; Assertion proved
(assume "Assertion")
(use "Assertion" (pt "v") (pt "(Nil nat)") (pt "(Nil nat)"))
(use "Truth")
(use "InitRev")
;; Proof finished.
(save "ExclRev")

(define proof (current-proof))
(define nproof (np proof))
;; (proof-to-expr-with-formulas nproof)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2.  Translation into an existence proof
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exproof (atr-excl-proof-to-ex-proof nproof))
;; (cdp exproof)
(define eterm (proof-to-extracted-term exproof))
(add-var-name "g" (py "list nat=>list nat=>list nat"))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [v]
;;  (Rec list nat=>list nat=>list nat=>list nat)v([v0,v1]v1)
;;  ([x,v0,g,v1,v2]g(v1++x:)(x::v2))
;;  (Nil nat)
;;  (Nil nat)

;; This amounts to:  f(v) = h(v,nil,nil) with
;;   h(nil,v0,v1) = v1,
;;   h(xv,v0,v1) = h(v,v0x,xv1)

;; Notice that the second argument of h is not needed.  However, its
;; presence makes the algorithm quadratic.  

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 3.  Optimal decoration
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define decproof (decorate exproof))
;; (cdp decproof)

(add-var-name "f" (py "list nat=>list nat"))
(define eterm (proof-to-extracted-term decproof))
(pp (rename-variables (nt eterm)))

;; [v](Rec list nat=>list nat=>list nat)v([v0]v0)([x,v0,f,v1]f(x::v1))(Nil nat)

;; This amounts to:  f(v) = g(v,nil) with
;;   g(nil,v0) = v0,
;;   g(xv,v0) = g(v,xv0)
;; and hence the usual linear algorithm, with an accumulator.

