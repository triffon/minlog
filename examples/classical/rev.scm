;; 2014-10-13.  rev.scm

;; Based on tutor.scm and to a lesser extent on
;; lectures/proofth/ss07/rev.scm, slides/varese08demo.scm

(load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(libload "list.scm")
(set! COMMENT-FLAG #t)

(add-var-name "x" "y" (py "alpha"))
(add-var-name "xs" "ys" (py "list alpha"))

(add-ids
 (list (list "RevI" (make-arity (py "list alpha") (py "list alpha"))))
 '("RevI(Nil alpha)(Nil alpha)" "InitRevI")
 '("all x,xs,ys(RevI xs ys -> RevI(xs++x:)(x::ys))" "GenRevI"))

;; RevIUnique
(set-goal "all xs,ys(RevI xs ys -> ys eqd Rev xs)")
(assume "xs" "ys" "Rxsys")
(elim "Rxsys")
(use "InitEqD")
(assume "x" "xs1" "ys1" "Rxsys1" "ys1=Rxs1")
(simp "ListRevAppd")
(ng #t)
(simp "ys1=Rxs1")
(use "InitEqD")
;; Proof finished.
(save "RevIUnique")

;; RevIRev
(set-goal "all ys RevI(Rev ys)ys")
(ind)
(use "InitRevI")
(assume "x" "xs")
(use "GenRevI")
;; Proof finished.
(save "RevIRev")

;; RevISym
(set-goal "all xs,ys(RevI xs ys -> RevI ys xs)")
(assume "xs" "ys" "Rxsys")
(assert "ys eqd Rev xs")
 (use "RevIUnique")
 (use "Rxsys")
(assume "EqHyp")
(simp "EqHyp")
(use "RevIRev")
;; Proof finished.
(save "RevISym")

(set-goal "all xs ex ys RevI xs ys")
(ind)
(ex-intro (pt "(Nil alpha)"))
(use "InitRevI")
;; Step
(assume "x" "xs" "ExHyp")
(by-assume "ExHyp" "ys" "ysProp")
(ex-intro (pt "ys++x:"))
(use "RevISym")
(use "GenRevI")
(use "RevISym")
(use "ysProp")
;; Proof finished.

(define constr-proof (current-proof))

(define eterm (proof-to-extracted-term constr-proof))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [xs](Rec list alpha=>list alpha)xs(Nil alpha)([x,xs0,xs1]xs1++x:)

;; (term-to-scheme-expr neterm)

(pp (nt (make-term-in-app-form neterm (pt "x0::x1::x2::x3:"))))
;; x3::x2::x1::x0:

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Program extraction from classical proofs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(set-goal "all xs excl ys RevI xs ys")
(assume "xs0" "Hyp")
(cut "all xs allnc xs1(xs1++xs eqd xs0 -> all ys(RevI xs1 ys -> bot))")
 (assume "Assertion")
 (use "Assertion" (pt "xs0") (pt "(Nil alpha)") (pt "(Nil alpha)"))
 (ng #t)
 (use "InitEqD")
 (use "InitRevI")
;; ?_4:all xs allnc xs1(xs1++xs eqd xs0 -> all ys(RevI xs1 ys -> bot))
(ind)
;; Base
(assume "xs")
(ng #t)
(assume "xs=xs0" "ys")
(simp "xs=xs0")
(use "Hyp")
;; Step
(assume "x" "xs" "IH" "xs2" "EqHyp" "ys" "RevHyp")
(use "IH" (pt "xs2++x:") (pt "x::ys"))
(ng #t)
(use "EqHyp")
(use "GenRevI")
(use "RevHyp")
;; Proof finished.

(define class-proof (np (current-proof)))

(add-var-name "g" (py "list alpha=>list alpha"))

(define eterm (atr-min-excl-proof-to-structured-extracted-term class-proof))
(define neterm (rename-variables (nt eterm)))

(pp neterm)

;; [xs]
;;  (Rec list alpha=>list alpha=>list alpha)xs([xs0]xs0)
;;  ([x,xs0,g,xs1]g(x::xs1))
;;  (Nil alpha)

(pp (nt (make-term-in-app-form neterm (pt "x0::x1::x2::x3:"))))
;; x3::x2::x1::x0:

;; This amounts to the usual linear algorithm (with an accumulator):
;; it employs cons rather than append in the step.
