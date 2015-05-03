;; $Id: fib.scm 2156 2008-01-25 13:25:12Z schimans $

;; Extraction of the Fibonacci algorithm from a constructive proof

;; (load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(set! COMMENT-FLAG #t)

(add-var-name "l" (py "nat"))
(add-var-name "p" (py "nat@@nat"))

;; The graph of the Fibonacci function:

(add-ids
 (list (list "G" (make-arity (py "nat") (py "nat"))))
 '("G 0 0" "InitGZero")
 '("G 1 1" "InitGOne")
 '("all n,k,l(G n k -> G(n+1)l -> G(n+2)(k+l))" "GenG"))

(display-idpc "G")

;; G
;; 	InitGZero:	G 0 0
;; 	InitGOne:	G 1 1
;; 	GenG:	all n,k,l(G n k -> G(n+1)l -> G(n+2)(k+l))

;; Fibonacci
(set-goal "all n ex k G n k")
(assert "all n ex k,l(G n k & G(n+1)l)")
 (ind)
 (ex-intro (pt "0"))
 (ex-intro (pt "1"))
 (split)
 (use "InitGZero")
 (use "InitGOne")
 (assume "n" "IH")
 (by-assume "IH" "k" "IHk")
 (by-assume "IHk" "l" "IHl")
 (ex-intro (pt "l"))
 (ex-intro (pt "k+l"))
 (split)
 (use "IHl")
 (use "GenG")
 (use "IHl")
 (use "IHl")
(assume "all n ex k,l(G n k & G(n+1)l)" "n")
(inst-with-to "all n ex k,l(G n k & G(n+1)l)" (pt "n") "Exkl")
(drop "all n ex k,l(G n k & G(n+1)l)")
(by-assume "Exkl" "k" "Exl")
(by-assume "Exl" "l" "klProp")
(ex-intro (pt "k"))
(use "klProp")
;; Proof finished.
(save "Fibonacci")

(define eterm (proof-to-extracted-term (theorem-name-to-proof "Fibonacci")))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n]left((Rec nat=>nat@@nat)n(0@1)([n0,p]right p@left p+right p))

(pp (nt (make-term-in-app-form neterm (pt "0")))) ;"0"
(pp (nt (make-term-in-app-form neterm (pt "1")))) ;"1"
(pp (nt (make-term-in-app-form neterm (pt "2")))) ;"1"
(pp (nt (make-term-in-app-form neterm (pt "3")))) ;"2"
(pp (nt (make-term-in-app-form neterm (pt "4")))) ;"3"
(pp (nt (make-term-in-app-form neterm (pt "8")))) ;"21"
(pp (nt (make-term-in-app-form neterm (pt "10")))) ;"55"
(pp (nt (make-term-in-app-form neterm (pt "12")))) ;"144"

(term-to-expr neterm)

;; (lambda (n)
;;   (car (((natRec n) (cons 0 1))
;;          (lambda (n0)
;;            (lambda (p) (cons (cdr p) (+ (car p) (cdr p))))))))
		
;; (time ((ev (term-to-expr neterm)) 3000))
