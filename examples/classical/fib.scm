;; $Id: fib.scm 2156 2008-01-25 13:25:12Z schimans $

;; Extraction of the Fibonacci algorithm from a classical proof based
;; on [BBS02]

;; We need some arithmetic first.

;; (load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(set! COMMENT-FLAG #t)

(add-var-name "l" (py "nat"))
(add-var-name "f" (py "nat=>nat=>nat"))
(add-var-name "H" (py "(nat=>nat=>nat)=>nat"))

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
(set-goal "all n excl k G n k")
(cut "all n excl k,l(G n k ! G(n+1)l)")
(search)
(ind)
(search 1 '("InitGZero" 1) '("InitGOne" 1))
(search 1 '("GenG" 1))
;; Proof finished.
(save "Fibonacci")

(define proof (theorem-name-to-proof "Fibonacci"))
(define nproof (np proof))

(proof-to-expr-with-formulas nproof)

;; Ind: all n(
;;  excl k,l(G 0 k ! G(0+1)l) ->
;;  all n0(
;;   excl k,l(G n0 k ! G(n0+1)l) -> excl k,l(G(Succ n0)k ! G(Succ n0+1)l)) ->
;;  excl k,l(G n k ! G(n+1)l))
;; Intro: G 0 0
;; Intro: G 1 1
;; Intro: all n,k,l(G n k -> G(n+1)l -> G(n+2)(k+l))
;; u1474: all k(G n k --> bot)
;; u1475: all k,l(G 0 k --> G(0+1)l --> bot)
;; u1476: excl k,l(G n2075 k ! G(n2075+1)l)
;; u1477: all k,l(G(Succ n2075)k --> G(Succ n2075+1)l --> bot)
;; u1478: G n2075 k
;; u1479: G(n2075+1)l
;; u1480: G n k
;; u1481: G(n+1)l

;; (lambda (n)
;;   (lambda (u1474)
;;     ((((Ind n) (lambda (u1475) ((((u1475 0) 1) Intro) Intro)))
;;        (lambda (n2075)
;;          (lambda (u1476)
;;            (lambda (u1477)
;;              (u1476
;;                (lambda (k)
;;                  (lambda (l)
;;                    (lambda (u1478)
;;                      (lambda (u1479)
;;                        ((((u1477 l) (+ k l)) u1479)
;;                          (((((Intro n2075) k) l) u1478) u1479)))))))))))
;;       (lambda (k)
;;         (lambda (l)
;;           (lambda (u1480) (lambda (u1481) ((u1474 k) u1480))))))))

(define eterm (atr-min-excl-proof-to-structured-extracted-term nproof))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n]
;;  (Rec nat=>(nat=>nat=>nat)=>nat)n([f]f 0 1)
;;  ([n0,H,f]H([n1,n2]f n2(n1+n2)))
;;  ([n0,n1]n0)

(pp (nt (make-term-in-app-form neterm (pt "0")))) ;"0"
(pp (nt (make-term-in-app-form neterm (pt "1")))) ;"1"
(pp (nt (make-term-in-app-form neterm (pt "2")))) ;"1"
(pp (nt (make-term-in-app-form neterm (pt "3")))) ;"2"
(pp (nt (make-term-in-app-form neterm (pt "4")))) ;"3"
(pp (nt (make-term-in-app-form neterm (pt "8")))) ;"21"
(pp (nt (make-term-in-app-form neterm (pt "10")))) ;"55"
(pp (nt (make-term-in-app-form neterm (pt "12")))) ;"144"

(define expr (term-to-scheme-expr neterm))

;; (lambda (n)
;;   ((((natRec n) (lambda (f) ((f 0) 1)))
;;      (lambda (n0)
;;        (lambda (H)
;;          (lambda (f)
;;            (H (lambda (n1) (lambda (n2) ((f n2) (+ n1 n2)))))))))
;;     (lambda (n0) (lambda (n1) n0))))

;; (time ((ev expr) 3000))

;; For better readability we can split this expression in two definitions:

(define (fibo n)
  (fibo1 n (lambda (k l) k)))

(define (fibo1 n1 f)
  (if (= n1 0)
      (f 0 1)
      (fibo1 (- n1 1) (lambda (k l) (f l (+ k l))))))

;; (time (fibo 3000))
