;; 2014-10-12 root.scm

;; We prove the existence of integer square roots.

;; (load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(set! COMMENT-FLAG #t)

(add-var-name "f" "g" (py "nat=>nat"))

;; IntSqRt
(set-goal "all f,g,n(
 all n(n<f 0 -> bot) -> all n n<f(g n) ->
 excl m((n<f m -> bot) ! n<f(m+1)))")
(assume "f" "g" "n" "v1" "v2" "u")
(assert "all m(n<f m -> bot)")
 (ind)
 (use "v1")
 (use "u")
(assume "Assertion")
(use-with "Assertion" (pt "g n") "?")
(use "v2")
;; Proof finished.
(save "IntSqRt")

(define proof (theorem-name-to-proof "IntSqRt"))

;; For atr-min-excl-proof-to-structured-extracted-term it is not
;; necessary to first normalize the proof.  However, it is clearer to
;; work with normal proofs.

(define nproof (np proof))
(proof-to-expr-with-formulas nproof)

;; Ind: allnc n,f
;;  all n0(
;;   (n<f 0 -> bot) ->
;;   all n1((n<f n1 -> bot) -> n<f(Succ n1) -> bot) -> n<f n0 -> bot)
;; u1462: all n(n<f 0 -> bot)
;; u1463: all n n<f(g n)
;; u1464: all m((n<f m -> bot) -> n<f(m+1) -> bot)

;; (lambda (f)
;;   (lambda (g)
;;     (lambda (n)
;;       (lambda (u1462)
;;         (lambda (u1463)
;;           (lambda (u1464)
;;             ((((((Ind n) f) (g n)) (u1462 n)) u1464) (u1463 n))))))))

(define eterm (atr-min-excl-proof-to-structured-extracted-term nproof))

(define neterm (nt eterm))
(pp (rename-variables neterm))

;; [f,f0,n](Rec nat=>nat)(f0 n)0([n0,n1][if (n<f n0) n1 n0])

(define sqr (pt "[n]n*n"))

(pp (nt (mk-term-in-app-form neterm sqr (pt "Succ") (pt "3")))) ;"1"
(pp (nt (mk-term-in-app-form neterm sqr (pt "Succ") (pt "4")))) ;"2"
(pp (nt (mk-term-in-app-form neterm sqr (pt "Succ") (pt "8")))) ;"2"
(pp (nt (mk-term-in-app-form neterm sqr (pt "Succ") (pt "9")))) ;"3"
(pp (nt (mk-term-in-app-form neterm sqr (pt "Succ") (pt "15")))) ;"3"
(pp (nt (mk-term-in-app-form neterm sqr (pt "Succ") (pt "16")))) ;"4"

(define expr (term-to-scheme-expr neterm))

;; (lambda (f0)
;;   (lambda (f1)
;;     (lambda (n2)
;;       (((natRec (f1 n2)) 0)
;;         (lambda (n3) (lambda (n4) (if (< n2 (f0 n3)) n4 n3)))))))

(define (intsqrt m)
  ((((ev expr) (lambda (n) (* n n))) (lambda (n) (+ 1 n))) m))

(intsqrt 1712345)
;; 1308

;; (* 1308 1308) ;1710864
;; (* 1309 1309) ;1713481

;; (time (intsqrt 1712345))
;; 975 ms
;; Slow, because natRec counts down.
