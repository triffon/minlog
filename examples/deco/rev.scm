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

(remove-var-name "n" "m" "k")
(add-var-name "x" "y" "n" "m" "k" (py "nat"))
(add-var-name "v" "w" "u" (py "list nat"))

;; RevClass
(set-goal "all rev,v(
      rev(Nil nat)(Nil nat) -> 
      all v,w,x(rev v w -> rev(v++x:)(x::w)) ->
      excl w rev v w)")
(assume "rev" "v0" "InitRev" "GenRev" "Hyp")
(assert "all u all v(v++u=v0 -> all w(rev v w -> bot))")
 (ind)
 (assume "v")
 (ng)
 (assume "v=v0")
 (simp "v=v0")
 (use "Hyp")
 (assume "x" "u" "IH""v" "H1" "w" "H2")
 (use-with "IH" (pt "v++x:") "?" (pt "x::w") "?")
 (ng #t)
 (use "H1")
 (use "GenRev")
 (use "H2")
(assume "ISNR")
(use "ISNR" (pt "v0") (pt "(Nil nat)") (pt "(Nil nat)"))
(use "Truth")
(use "InitRev")
;; Proof finished.
(save "RevClass")

;; 2.  Translation into an existence proof
;; =======================================

(define min-excl-proof (theorem-name-to-proof "RevClass"))
(define ex-proof (atr-min-excl-proof-to-intuit-ex-proof min-excl-proof))
(define eterm (proof-to-extracted-term ex-proof))
(add-var-name "g" (py "list nat=>list nat=>list nat"))
(pp (rename-variables (nt eterm)))

;; [rev,v]
;;  (Rec list nat=>list nat=>list nat=>list nat)v([v0,v1]v1)
;;  ([x,v0,g,v1,v2]g(v1++x:)(x::v2))
;;  (Nil nat)
;;  (Nil nat)

;; This amounts to:  f(v) = h(v,nil,nil) with
;;   h(nil,v0,v1) = v1,
;;   h(xv,v0,v1) = h(v,v0x,xv1)

;; Notice that the second argument of h is not needed.  However, its
;; presence makes the algorithm quadratic.  

;; 3.  Optimal decoration
;; ======================

(define decproof (decorate ex-proof))
;; (cdp decproof)

(add-var-name "f" (py "list nat=>list nat"))
(define eterm (proof-to-extracted-term decproof))
(pp (rename-variables (nt eterm)))

;; [rev,v]
;;  (Rec list nat=>list nat=>list nat)v([v0]v0)([x,v0,f,v1]f(x::v1))(Nil nat)

;; This amounts to:  f(v) = g(v,nil) with
;;   g(nil,v0) = v0,
;;   g(xv,v0) = g(v,xv0)
;; and hence the usual linear algorithm, with an accumulator.

