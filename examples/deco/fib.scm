;; 2014-10-18.  fib.scm.  Based on leeds09demo.scm.  Fibonacci in
;; continuation passing style.

;; (load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(set! COMMENT-FLAG #t)

(add-pvar-name "Q" (make-arity (py "nat")))
(remove-var-name "k") ;k will be used for continuations.


;; 1. Double induction
;; ===================

;; Double induction ( "all n(Q n -> Q(Succ n) -> Q(Succ(Succ n))) ->
;; all n(Q 0 -> Q 1 -> Q n)") is proved in continuation passing style,
;; i.e., not directly, but using as an intermediate assertion
;; "all n,m((Q n -> Q(Succ n) -> Q(n+m)) -> Q 0 -> Q 1 -> Q(n+m))"

;; IndDoubleCont
(set-goal "all n(Q n -> Q(Succ n) -> Q(Succ(Succ n))) ->
           all n(Q 0 -> Q 1 -> Q n)")
(assume "Step")
(assert "all n,m((Q n -> Q(Succ n) -> Q(n+m)) -> Q 0 -> Q 1 -> Q(n+m))")
 (ind)

 ;; Base
 (auto)

 ;; Step
 (assume "n" "IHn" "m" "K" "Base0" "Base1")
 (assert "Q n -> Q(Succ n) -> Q(Succ n+m)")
  (assume "Q n" "Q(Succ n)")
  (use "K")
  (use "Q(Succ n)")
  (use "Step")
  (use "Q n")
  (use "Q(Succ n)")
 (assume "Hyp")
 (use-with "IHn" (pt "Succ m") "Hyp" "Base0" "Base1")

;; Now we have the continuation passing assertion available
(assume "Pass" "n" "Q 0")
(use-with "Pass" (pt "n") (pt "0") "?" "Q 0")
(assume "Q n" "Q(Succ n)")
(use "Q n")
;; Proof finished.
(save "IndDoubleCont")

(define pvar (predicate-form-to-predicate (pf "Q 0")))
(define tvar (PVAR-TO-TVAR pvar))

(add-var-name "x" tvar)
(add-var-name "k" (mk-arrow tvar tvar tvar))
(add-var-name
 "p" (mk-arrow (py "nat") (mk-arrow tvar tvar tvar) tvar tvar tvar))
(add-var-name "f" (mk-arrow (py "nat") tvar tvar tvar))

(define eterm (proof-to-extracted-term (theorem-name-to-proof "IndDoubleCont")))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [f,n]
;;  (Rec nat=>nat=>(alpha331=>alpha331=>alpha331)=>alpha331=>alpha331=>alpha331)
;;  n
;;  ([n0,k]k)
;;  ([n0,p,n1,k]p(Succ n1)([x,x0]k x0(f n0 x x0)))
;;  0
;;  ([x,x0]x)

;; (proof-to-expr-with-formulas (theorem-name-to-proof "IndDoubleCont"))

;; 2. Decoration
;; =============

(define proof (theorem-name-to-proof "IndDoubleCont"))
(define decproof (decorate proof))
;; (proof-to-expr-with-formulas decproof)
;; After decoration the formula proved by induction has "allnc m"
;; rather than "all m".

(remove-var-name "p")
(add-var-name "p" (mk-arrow (mk-arrow tvar tvar tvar) tvar tvar tvar))
(define eterm (proof-to-extracted-term decproof))
(pp (rename-variables (nt eterm)))

;; [f,n]
;;  (Rec nat=>(alpha331=>alpha331=>alpha331)=>alpha331=>alpha331=>alpha331)n
;;  ([k]k)
;;  ([n0,p,k]p([x,x0]k x0(f n0 x x0)))
;;  ([x,x0]x)

;; 3. Fibonacci numbers
;; ====================

;; An an example one can obtain a continuation based tail recursive
;; definition of the Fibonacci function, from a proof of its totality.

(add-pvar-name "G" (make-arity (py "nat") (py "nat"))) ;graph of Fibonacci
(add-var-name "v" "w" (py "nat")) ;values of Fibonacci

;; FibCont
(set-goal "G^ 0 0 --> G^ 1 1 -->
  all n,v,w(G^ n v --> G^(Succ n)w --> G^(Succ(Succ n))(v+w)) ->
  all n ex v G^ n v")
(assume "G^ 0 0" "G^ 1 1" "GenG" "n")
(use-with "IndDoubleCont"
	  (make-cterm (pv "n") (pf "ex v G^ n v")) "?" (pt "n") "?" "?")

;; Step
(assume "m" "IH1" "IH2")
(by-assume-with "IH1" "v" "G^ m v")
(by-assume-with "IH2" "w" "G^(Succ m)w")
(ex-intro (pt "v+w"))
(use "GenG")
(use "G^ m v")
(use "G^(Succ m)w")

;; Base
(ex-intro (pt "0"))
(use "G^ 0 0")
(ex-intro (pt "1"))
(use "G^ 1 1")
;; Proof finished.
(save "FibCont")

(define proof (theorem-name-to-proof "FibCont"))
(define expproof (expand-thm proof "IndDoubleCont"))
;; (proof-to-expr-with-formulas expproof)
(define eterm (proof-to-extracted-term expproof))

(remove-var-name "f" "p" "k")
(add-var-name "p" (py "nat=>(nat=>nat=>nat)=>nat=>nat=>nat"))
(add-var-name "k" (py "nat=>nat=>nat"))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n]
;;  (Rec nat=>nat=>(nat=>nat=>nat)=>nat=>nat=>nat)n([n0,k]k)
;;  ([n0,p,n1,k]p(Succ n1)([n2,n3]k n3(n2+n3)))
;;  0
;;  ([n0,n1]n0)
;;  0 
;;  1

;; The only unclean aspect of this term is the fact that the recursion
;; operator has value type nat=>(nat=>nat=>nat)=>nat=>nat=>nat rather
;; than (nat=>nat=>nat)=>nat=>nat=>nat, which would correspond to an
;; iteration.  We repair this by decoration.

(define decproof (decorate expproof))
;; (proof-to-expr-with-formulas decproof)

(remove-var-name "p")
(add-var-name "p" (py "(nat=>nat=>nat)=>nat=>nat=>nat"))

(define eterm (proof-to-extracted-term decproof))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [n]
;;  (Rec nat=>(nat=>nat=>nat)=>nat=>nat=>nat)n([k]k)
;;  ([n0,p,k]p([n1,n2]k n2(n1+n2)))
;;  ([n0,n1]n0)
;;  0 
;;  1

;; 4.  Running the extracted term
;; ==============================

;; (nt (mk-term-in-app-form neterm (pt "6")))
(pp (nt (mk-term-in-app-form neterm (pt "6"))))
;; 8

(term-to-scheme-expr neterm)

;; (lambda (n)
;;   ((((((natRec n) (lambda (k) k))
;;        (lambda (n0)
;;          (lambda (p)
;;            (lambda (k)
;;              (p (lambda (n1) (lambda (n2) ((k n2) (+ n1 n2)))))))))
;;       (lambda (n0) (lambda (n1) n0)))
;;      0)
;;     1))

;; (time ((ev (term-to-expr neterm)) 1000))

;; 3 ms elapsed cpu time
;;     3 ms elapsed real time
;;     668768 bytes allocated
;; 43466557686937456435688527675040625802564660517371780402481729089536555417949051890403879840079255169295922593080322634775209689623239873322471161642996440906533187938298969649928516003704476137795166849228875
