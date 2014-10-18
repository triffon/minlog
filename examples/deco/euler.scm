;; 2014-10-18.  euler.scm
;; Decorate a proof for Euler's phi-function (cf. decofullytest.scm)

;; (load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(set! COMMENT-FLAG #t)

(add-ids (list (list "C" (make-arity (py "nat")) "algC"))
	 '("all m^,k^(1<m^ -> 1<k^ -> C(m^ *k^))" "GenC"))

(add-global-assumption "Fact" "all n((C n -> F) orr C n)")
(add-global-assumption "PTest" "all n((C n -> F) oru C n)")
(add-program-constant "phi" (py "nat=>nat"))
(add-global-assumption "EulerPrime" "allnc n((C n -> F) -> phi n=n--1)")
(add-global-assumption "EulerComp" "allnc n(C n -> phi n<n--1)")

;; Euler
(set-goal "all n(phi n=n--1 ori phi n<n--1)")
(assume "n")
(inst-with-to "Fact" (pt "n") "FactInst")
(elim "FactInst")
(assume "C n -> F")
(intro 0)
(use "EulerPrime")
(use "C n -> F")
(assume "C n")
(intro 1)
(use "EulerComp")
(use "C n")
;; Proof finished.
(save "Euler")
;; ok, Euler has been added as a new theorem.
;; ok, program constant cEuler: nat=>boole
;; of t-degree 0 and arity 0 added

(define proof (theorem-name-to-proof "Euler"))
;; (cdp proof)
(proof-to-expr-with-formulas proof)

(define nproof (np proof))
(proof-to-expr-with-formulas nproof)

;; Elim: allnc n(
;;  (C n -> F) orr C n -> 
;;  ((C n -> F) -> phi n=n--1 oru phi n<n--1) -> 
;;  (C n -> phi n=n--1 oru phi n<n--1) -> phi n=n--1 oru phi n<n--1)
;; Fact: all n((C n -> F) orr C n)
;; Intro: allnc n(phi n=n--1 -> phi n=n--1 oru phi n<n--1)
;; EulerPrime: allnc n((C n -> F) -> phi n=n--1)
;; Intro: allnc n(phi n<n--1 -> phi n=n--1 oru phi n<n--1)
;; EulerComp: allnc n(C n -> phi n<n--1)
;; u1542: C n -> F
;; u1544: C n

;; (lambda (n)
;;   ((((Elim n) (Fact n))
;;      (lambda (u1542) ((Intro n) ((EulerPrime n) u1542))))
;;     (lambda (u1544) ((Intro n) ((EulerComp n) u1544)))))

(define eterm (proof-to-extracted-term nproof))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [n][if (cFact n) True ([algC]False)]

(define decnproof (fully-decorate nproof "Fact" "PTest"))
;; (cdp decnproof)
(proof-to-expr-with-formulas decnproof)
;; Elim: allnc n(
;;  (C n -> F) oru C n -> 
;;  ((C n -> F) -> phi n=n--1 oru phi n<n--1) -> 
;;  (C n --> phi n=n--1 oru phi n<n--1) -> phi n=n--1 oru phi n<n--1)
;; PTest: all n((C n -> F) oru C n)
;; Intro: allnc n(phi n=n--1 -> phi n=n--1 oru phi n<n--1)
;; EulerPrime: allnc n((C n -> F) -> phi n=n--1)
;; Intro: allnc n(phi n<n--1 -> phi n=n--1 oru phi n<n--1)
;; EulerComp: allnc n(C n -> phi n<n--1)
;; u1542: C n -> F
;; u1544: C n

;; (lambda (n)
;;   ((((Elim n) (PTest n))
;;      (lambda (u1542) ((Intro n) ((EulerPrime n) u1542))))
;;     (lambda (u1544) ((Intro n) ((EulerComp n) u1544)))))

(pp (nt (proof-to-extracted-term decnproof)))
;; cPTest
