;; $Id: quotrem.scm 2156 2008-01-25 13:25:12Z schimans $

;; (load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(set! COMMENT-FLAG #t)

(add-var-name "l" (py "nat"))

;; QR
(set-goal "all m,n ex k,l(n=(m+1)*k+l & l<m+1)")
(assume "m")
(ind)
;; Base
(ex-intro (pt "0"))
(ex-intro (pt "0"))
(split)
(use "Truth")
(use "Truth")
;; Step
(assume "n" "IH")
(by-assume "IH" "k" "kProp")
(by-assume "kProp" "l" "klProp")
(cases (pt "l<m"))

;; Case l<m
(assume "l<m")
(ex-intro (pt "k"))
(ex-intro (pt "l+1"))
(ng)
(split)
(use "klProp")
(use "l<m")

;; Case l<m -> F
(assume "l<m -> F")
(ex-intro (pt "k+1"))
(ex-intro (pt "0"))
(ng)
(split)
(assert "l=m")
 (use "NatLeAntiSym")
 (use "NatLtSuccToLe")
 (use "klProp")
 (use "NatNotLtToLe")
 (use "l<m -> F")
(assume "l=m")
(simphyp-with-to "klProp" "l=m" "klPropSimp")
(use "klPropSimp")
(use "Truth")
;; Proof finished.
(save "QR")

(define eterm (proof-to-extracted-term (theorem-name-to-proof "QR")))
(add-var-name "p" (py "nat@@nat"))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n,n0]
;;  (Rec nat=>nat@@nat)n0(0@0)
;;  ([n1,p][if (right p<n) (left p@Succ right p) (Succ left p@0)])

(pp (nt (mk-term-in-app-form neterm (pt "2") (pt "7"))))
(pp (nt (mk-term-in-app-form neterm (pt "5") (pt "7"))))
(pp (nt (mk-term-in-app-form neterm (pt "6") (pt "54"))))
(pp (nt (mk-term-in-app-form neterm (pt "6") (pt "754")))) 
;; 107@5

(define expr (term-to-expr neterm))

;; (lambda (n)
;;   (lambda (n0)
;;     (((natRec n0) (cons 0 0))
;;       (lambda (n1)
;;         (lambda (p)
;;           (if (< (cdr p) n)
;;               (cons (car p) (+ (cdr p) 1))
;;               (cons (+ (car p) 1) 0)))))))

(((ev expr) 6) 754) 
;; (107 . 5)

(((ev expr) 682) 387688)
;; (567 . 427)

;; (+ (* 567 683) 427)
;; 387688
