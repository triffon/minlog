;; 2020-08-30.  wftest.scm

;; We prove the existence of a "least" element in a well-founded set.

;; (load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(set! COMMENT-FLAG #t)

(add-var-name "k" (py "nat"))
(add-var-name "f" (py "nat=>nat"))
(add-var-name "g" (py "nat=>nat=>nat"))

;; Hand construction of the proof, following 7.3.5 (in [SW12])
;; ===========================================================

(define baseproof
  (let ((v1 (make-avar (pf "all m(m<0 -> bot)") 1 "v"))
	(w2 (make-avar (pf "k<0") 2 "w"))
	(w3 (make-avar (pf "f m=k") 3 "w")))
    (mk-proof-in-intro-form
     (pv "k") w2 (pv "m") w3
     (mk-proof-in-elim-form
      (make-proof-in-avar-form v1)
      (pt "k")
      (make-proof-in-avar-form w2)))))

;; (proof-to-expr-with-formulas baseproof)

;; v1: all m(m<0 -> bot)
;; w2: k<0
;; w3: f m=k

;; (lambda (k)
;;   (lambda (w2) (lambda (m) (lambda (w3) ((v1 k) w2)))))

;; LOne
(set-goal (pf "all l,k,n(l<k -> k<n+1 -> l<n)"))
(assume "l" "k" "n" "w6" "w5")
(use "NatLtLeTrans" (pt "k"))
(use "w6")
(use "NatLtSuccToLe")
(use "w5")
;; Proof finished.
(save "LOne")

(define stepproof
  (let ((w1 (make-avar (pf "all k(all l(l<k -> all m(f m=l -> bot)) ->
                                  all m(f m=k -> bot))") 1 "w"))
	(w4 (make-avar (pf "all k(k<n -> all m(f m=k -> bot))") 4 "w"))
	(w5 (make-avar (pf "k<n+1") 5 "w"))
	(w6 (make-avar (pf "l<k") 6 "w")))
    (mk-proof-in-intro-form
     (pv "n") w4 (pv "k") w5
     (mk-proof-in-elim-form
      (make-proof-in-avar-form w1) (pt "k")
      (mk-proof-in-intro-form
       (pv "l") w6
       (mk-proof-in-elim-form
	(make-proof-in-avar-form w4) (pt "l")
	(mk-proof-in-elim-form
	 (make-proof-in-aconst-form (theorem-name-to-aconst "LOne"))
	 (pt "l") (pt "k") (pt "n")
	 (make-proof-in-avar-form w6)
	 (make-proof-in-avar-form w5))))))))

(proof-to-expr-with-formulas stepproof)

;; LOne: all l,k,n(l<k -> k<n+1 -> l<n)
;; w1: all k(all l(l<k -> all m(f m=l -> bot)) -> all m(f m=k -> bot))
;; w4: all k(k<n -> all m(f m=k -> bot))
;; w5: k<n+1
;; w6: l<k

;; (lambda (n)
;;   (lambda (w4)
;;     (lambda (k)
;;       (lambda (w5)
;;         ((w1 k)
;;           (lambda (l)
;;             (lambda (w6) ((w4 l) (((((LOne l) k) n) w6) w5)))))))))

;; IndB
(set-goal (pf "all f,n(all k(k<0 -> all m(f m=k -> bot)) ->
 all n(all k(k<n -> all m(f m=k -> bot)) ->
       all k(k<n+1 -> all m(f m=k -> bot))) ->
 all k(k<n -> all m(f m=k -> bot)))"))
(assume "f" "n" "Base" "Step")
(ind (pt "n"))
(use "Base")
(use "Step")
;; Proof finished.
(save "IndB")

(define cvindproof
  (let ((w1 (make-avar (pf "all k(all l(l<k -> all m(f m=l -> bot)) ->
                                  all m(f m=k -> bot))") 1 "w")))
    (mk-proof-in-intro-form
     w1 (pv "k")
     (mk-proof-in-elim-form
      (make-proof-in-aconst-form (theorem-name-to-aconst "IndB"))
      (pt "f") (pt "k+1") baseproof stepproof (pt "k")
      truth-proof))))

(proof-to-expr-with-formulas cvindproof)

;; IndB: all f,n(
;;  all k(k<0 -> all m(f m=k -> bot)) ->
;;  all n0(
;;   all k(k<n0 -> all m(f m=k -> bot)) -> all k(k<n0+1 -> all m(f m=k -> bot))) ->
;;  all k(k<n -> all m(f m=k -> bot)))
;; LOne: all l,k,n(l<k -> k<n+1 -> l<n)
;; EqDTrueToAtom: all boole^(boole^ eqd True -> boole^)
;; Intro: allnc boole^ boole^ eqd boole^
;; v1: all m(m<0 -> bot)
;; w1: all k(all l(l<k -> all m(f m=l -> bot)) -> all m(f m=k -> bot))
;; w2: k<0
;; w3: f m=k
;; w4: all k(k<n -> all m(f m=k -> bot))
;; w5: k<n+1
;; w6: l<k

;; (lambda (w1)
;;   (lambda (k)
;;     ((((((IndB f) (+ k 1))
;;          (lambda (k)
;;            (lambda (w2) (lambda (m) (lambda (w3) ((v1 k) w2))))))
;;         (lambda (n)
;;           (lambda (w4)
;;             (lambda (k)
;;               (lambda (w5)
;;                 ((w1 k)
;;                   (lambda (l)
;;                     (lambda (w6)
;;                       ((w4 l) (((((LOne l) k) n) w6) w5))))))))))
;;        k)
;;       ((EqDTrueToAtom #t) (Intro #t)))))

;; LTwo
(set-goal "all f,m,k(f(m+1)<f m -> f m=k -> f(m+1)<k)")
(assume "f" "m" "k" "w7" "w3")
(simp "<-" "w3")
(use "w7")
;; Proof finished.
(save "LTwo")

(define progproof
  (let ((u (make-avar (pf "all k((f(k+1)<f k -> bot) -> bot)") -1 "u"))
	(u1 (make-avar (pf "all l(l<k -> all m(f m=l -> bot))") 1 "u"))
	(w3 (make-avar (pf "f m=k") 3 "w"))
	(w7 (make-avar (pf "f(m+1)<f m") 7 "w")))
    (mk-proof-in-intro-form
     (pv "k") u1 (pv "m") w3
     (mk-proof-in-elim-form
      (make-proof-in-avar-form u) (pt "m")
      (mk-proof-in-intro-form
       w7 (mk-proof-in-elim-form
	   (make-proof-in-avar-form u1)
	   (pt "f(m+1)")
	   (mk-proof-in-elim-form
	    (make-proof-in-aconst-form (theorem-name-to-aconst "LTwo"))
	    (pt "f") (pt "m") (pt "k")
	    (make-proof-in-avar-form w7)
	    (make-proof-in-avar-form w3))
	   (pt "m+1")
	   truth-proof))))))

(proof-to-expr-with-formulas progproof)

;; LTwo: all f,m,k(f(m+1)<f m -> f m=k -> f(m+1)<k)
;; EqDTrueToAtom: all boole^(boole^ eqd True -> boole^)
;; Intro: allnc boole^ boole^ eqd boole^
;; u: all k((f(k+1)<f k -> bot) -> bot)
;; u1: all l(l<k -> all m(f m=l -> bot))
;; w3: f m=k
;; w7: f(m+1)<f m

;; (lambda (k)
;;   (lambda (u1)
;;     (lambda (m)
;;       (lambda (w3)
;;         ((u m)
;;           (lambda (w7)
;;             ((((u1 (f (+ m 1))) (((((LTwo f) m) k) w7) w3)) (+ m 1))
;;               ((EqDTrueToAtom #t) (Intro #t)))))))))

(define wftestproof
  (let ((v1 (make-avar (pf "all m(m<0 -> bot)") 1 "v"))
	(u (make-avar (pf "all k((f(k+1)<f k -> bot) -> bot)") -1 "u")))
    (mk-proof-in-intro-form
     (pv "f") v1 u
     (mk-proof-in-elim-form
      cvindproof progproof (pt "f 0") (pt "0")
      truth-proof))))

(proof-to-expr-with-formulas wftestproof)

;; IndB: all f,n(
;;  all k(k<0 -> all m(f m=k -> bot)) ->
;;  all n0(
;;   all k(k<n0 -> all m(f m=k -> bot)) -> all k(k<n0+1 -> all m(f m=k -> bot))) ->
;;  all k(k<n -> all m(f m=k -> bot)))
;; LOne: all l,k,n(l<k -> k<n+1 -> l<n)
;; EqDTrueToAtom: all boole^(boole^ eqd True -> boole^)
;; Intro: allnc boole^ boole^ eqd boole^
;; LTwo: all f,m,k(f(m+1)<f m -> f m=k -> f(m+1)<k)
;; v1: all m(m<0 -> bot)
;; u: all k((f(k+1)<f k -> bot) -> bot)
;; w1: all k(all l(l<k -> all m(f m=l -> bot)) -> all m(f m=k -> bot))
;; w2: k<0
;; w3: f m=k
;; w4: all k(k<n -> all m(f m=k -> bot))
;; w5: k<n+1
;; w6: l<k
;; u1: all l(l<k -> all m(f m=l -> bot))
;; w7: f(m+1)<f m

;; (lambda (f)
;;   (lambda (v1)
;;     (lambda (u)
;;       (((((lambda (w1)
;;             (lambda (k)
;;               ((((((IndB f) (+ k 1))
;;                    (lambda (k)
;;                      (lambda (w2) (lambda (m) (lambda (w3) ((v1 k) w2))))))
;;                   (lambda (n)
;;                     (lambda (w4)
;;                       (lambda (k)
;;                         (lambda (w5)
;;                           ((w1 k)
;;                             (lambda (l)
;;                               (lambda (w6)
;;                                 ((w4 l) (((((LOne l) k) n) w6) w5))))))))))
;;                  k)
;;                 ((EqDTrueToAtom #t) (Intro #t)))))
;;            (lambda (k)
;;              (lambda (u1)
;;                (lambda (m)
;;                  (lambda (w3)
;;                    ((u m)
;;                      (lambda (w7)
;;                        ((((u1 (f (+ m 1))) (((((LTwo f) m) k) w7) w3))
;;                           (+ m 1))
;;                          ((EqDTrueToAtom #t) (Intro #t))))))))))
;;           (f 0))
;;          0)
;;         ((EqDTrueToAtom #t) (Intro #t))))))
	
(define proof1
  (expand-theorems wftestproof
		   (lambda (string) (not (string=? "EqDCompat" string)))))
(define eterm (atr-min-excl-proof-to-structured-extracted-term (np proof1)))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [f]
;;  [if (f 1<f 0)
;;    ((Rec nat=>nat=>nat=>nat)(f 0)([n,n0]0)
;;    ([n,g,n0,n1][if (f(Succ n1)<f n1) (g(f(Succ n1))(Succ n1)) n1])
;;    (f 1)
;;    1)
;;    0]

;; Discussion: Rec defines a function h of type nat=>nat=>nat.  After
;; an initial check whether f 1<f 0, in the positive case a
;; recursively defined binary function is applied to f 0 and 1.  This
;; avoids applying h to 0 (and hence using dummy, where 0 =: dummy).
;; More readable description of the algorithm:

;; Point-of-increase f := [if (f 1<f 0) (h(f 0)1) 0] with

;; h 0 := [m]dummy
;; h(n+1) := [m] [if (f(m+1)<f m) (h n(m+1)) m]

;; Notice that n is not used in the definition of h.  Reason: induction
;; is used in the form of a minimum principle only.

(term-to-scheme-expr neterm)

;; (lambda (f)
;;   (if (< (f 1) (f 0))
;;       (((((natRec (f 0)) (lambda (n) (lambda (n0) 0)))
;;           (lambda (n)
;;             (lambda (g)
;;               (lambda (n0)
;;                 (lambda (n1)
;;                   (if (< (f (+ n1 1)) (f n1))
;;                       ((g (f (+ n1 1))) (+ n1 1))
;;                       n1))))))
;;          (f 1))
;;         1)
;;       0))

;; Tests

(define arg (pt "[n][if (n=0) 2 n]"))
(pp (nt (make-term-in-app-form neterm arg)))
;; 1

(define arg (pt "[n][if (n=0) 4 [if (n=1) 3 n]]"))
(pp (nt (make-term-in-app-form neterm arg)))
;; 2

;; (generate-tseq n) generates a list of 3^n infinite sequences
;; starting with all possible variations of n ternary digits and
;; continuing with 0.

(define (generate-tseq n)
  (if (= n 0)
      (list (lambda (n) 0))
      (foldr (lambda (f l)
	       (cons (lambda (n) (if (= n 0) 0 (f (- n 1))))
		     (cons (lambda (n) (if (= n 0) 1 (f (- n 1))))
			   (cons (lambda (n) (if (= n 0) 2 (f (- n 1))))
				 l))))
	     '()
	     (generate-tseq (- n 1)))))

;; (length (generate-tseq 3))
;; 27

;; (first f n) returns a list of (f 0),(f 1),...,(f n-1).

(define (first f n)
  (if (= n 0)
      '()
       (cons (f 0)
	     (first (lambda (n) (f (+ n 1))) (- n 1)))))

;; (for-each (lambda (x) (display (first x 6)) (newline)) (generate-tseq 3))

;; (0 0 0 0 0 0)
;; (1 0 0 0 0 0)
;; (2 0 0 0 0 0)
;; (0 1 0 0 0 0)
;; (1 1 0 0 0 0)
;; (2 1 0 0 0 0)
;; (0 2 0 0 0 0)
;; (1 2 0 0 0 0)
;; (2 2 0 0 0 0)
;; (0 0 1 0 0 0)
;; (1 0 1 0 0 0)
;; (2 0 1 0 0 0)
;; (0 1 1 0 0 0)
;; (1 1 1 0 0 0)
;; (2 1 1 0 0 0)
;; (0 2 1 0 0 0)
;; (1 2 1 0 0 0)
;; (2 2 1 0 0 0)
;; (0 0 2 0 0 0)
;; (1 0 2 0 0 0)
;; (2 0 2 0 0 0)
;; (0 1 2 0 0 0)
;; (1 1 2 0 0 0)
;; (2 1 2 0 0 0)
;; (0 2 2 0 0 0)
;; (1 2 2 0 0 0)
;; (2 2 2 0 0 0)

;; Test a Scheme program on a list of infinite ternary sequences.

(define (test-tseq program . l)
  (let ((len (if (null? l) 4 (car l))))
    (map (lambda (seq)
	   (display "Testing on: ")
	   (display (first seq (+ 3 len)))
	   (display tab)
	   (display "Result: ")
	   (display (program seq))
	   (newline))
	 (reverse (generate-tseq len))))
  *the-non-printing-object*)

(test-tseq (ev (term-to-expr neterm)) 3)

;; Testing on: (0 0 0 0 0 0)	Result: 0
;; Testing on: (1 0 0 0 0 0)	Result: 1
;; Testing on: (2 0 0 0 0 0)	Result: 1
;; Testing on: (0 1 0 0 0 0)	Result: 0
;; Testing on: (1 1 0 0 0 0)	Result: 0
;; Testing on: (2 1 0 0 0 0)	Result: 2
;; Testing on: (0 2 0 0 0 0)	Result: 0
;; Testing on: (1 2 0 0 0 0)	Result: 0
;; Testing on: (2 2 0 0 0 0)	Result: 0
;; Testing on: (0 0 1 0 0 0)	Result: 0
;; Testing on: (1 0 1 0 0 0)	Result: 1
;; Testing on: (2 0 1 0 0 0)	Result: 1
;; Testing on: (0 1 1 0 0 0)	Result: 0
;; Testing on: (1 1 1 0 0 0)	Result: 0
;; Testing on: (2 1 1 0 0 0)	Result: 1
;; Testing on: (0 2 1 0 0 0)	Result: 0
;; Testing on: (1 2 1 0 0 0)	Result: 0
;; Testing on: (2 2 1 0 0 0)	Result: 0
;; Testing on: (0 0 2 0 0 0)	Result: 0
;; Testing on: (1 0 2 0 0 0)	Result: 1
;; Testing on: (2 0 2 0 0 0)	Result: 1
;; Testing on: (0 1 2 0 0 0)	Result: 0
;; Testing on: (1 1 2 0 0 0)	Result: 0
;; Testing on: (2 1 2 0 0 0)	Result: 1
;; Testing on: (0 2 2 0 0 0)	Result: 0
;; Testing on: (1 2 2 0 0 0)	Result: 0
;; Testing on: (2 2 2 0 0 0)	Result: 0

;; Interactive construction of the proof
;; =====================================

;; We use the minimum principle, hence general induction, and weak
;; (i.e., classical) existential quantifiers.

;; WfTest
(set-goal "all f(all m(m<0 -> bot) -> excl k(f(k+1)<f k -> bot))")
(assume "f" 1)
(by-assume-minimal-wrt (pf "excl k T") "k" (pt "f") "k-Min" "k-Hyp")

(exc-intro (pt "0"))
(use "Truth")

(assume "u")
(use "u" (pt "k"))
(assume "Hyp")
(use "k-Min" (pt "k+1"))
(use "Hyp")
(use "Truth")
;; Proof finished.
(save "WfTest")

(define proof (theorem-name-to-proof "WfTest"))
(define nproof (np proof))

;; (proof-to-expr-with-aconsts nproof)

;; (lambda (f)
;;   (lambda (u1767)
;;     (((ExclElimNegOneCrNcCr f)
;;        (lambda (u1769)
;;          (((ExclIntroOneNc 0) Truth)
;;            (lambda (n3161)
;;              ((u1769 n3161)
;;                (lambda (n3114)
;;                  ((((GInd f) n3114) u1769) (< (f n3114) (f n3161)))))))))
;;       (lambda (n3159)
;;         (lambda (u1777)
;;           (lambda (u1778)
;;             (lambda (u1779)
;;               ((u1779 n3159)
;;                 (lambda (u1780)
;;                   (((u1777 (+ n3159 1)) u1780) Truth))))))))))

;; (cdp nproof)

(define nproof-without-exc (rm-exc nproof))

(map aconst-to-name (proof-to-aconsts nproof-without-exc))
;; ("Truth" "GInd")

(define eterm
  (atr-min-excl-proof-to-structured-extracted-term nproof-without-exc))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [f]
;;  [if (f 1<f 0)
;;    ((GRecGuard nat nat)f 1([n,f0][if (f(Succ n)<f n) (f0(Succ n)) n])
;;    (f 1<f 0))
;;    0]

(term-to-scheme-expr neterm)

;; (lambda (f)
;;   (if (< (f 1) (f 0))
;;       ((((natGrecGuard f) 1)
;;          (lambda (n)
;;            (lambda (f0) (if (< (f (+ n 1)) (f n)) (f0 (+ n 1)) n))))
;;         (< (f 1) (f 0)))
;;       0))

;; Tests

(define arg (pt "[n][if (n=0) 2 n]"))
(pp (nt (make-term-in-app-form neterm arg)))
;; 1

(define arg (pt "[n][if (n=0) 4 [if (n=1) 3 n]]"))
(pp (nt (make-term-in-app-form neterm arg)))
;; 2

(test-tseq (ev (term-to-scheme-expr neterm)) 3)

;; Testing on: (0 0 0 0 0 0)	Result: 0
;; Testing on: (1 0 0 0 0 0)	Result: 1
;; Testing on: (2 0 0 0 0 0)	Result: 1
;; Testing on: (0 1 0 0 0 0)	Result: 0
;; Testing on: (1 1 0 0 0 0)	Result: 0
;; Testing on: (2 1 0 0 0 0)	Result: 2
;; Testing on: (0 2 0 0 0 0)	Result: 0
;; Testing on: (1 2 0 0 0 0)	Result: 0
;; Testing on: (2 2 0 0 0 0)	Result: 0
;; Testing on: (0 0 1 0 0 0)	Result: 0
;; Testing on: (1 0 1 0 0 0)	Result: 1
;; Testing on: (2 0 1 0 0 0)	Result: 1
;; Testing on: (0 1 1 0 0 0)	Result: 0
;; Testing on: (1 1 1 0 0 0)	Result: 0
;; Testing on: (2 1 1 0 0 0)	Result: 1
;; Testing on: (0 2 1 0 0 0)	Result: 0
;; Testing on: (1 2 1 0 0 0)	Result: 0
;; Testing on: (2 2 1 0 0 0)	Result: 0
;; Testing on: (0 0 2 0 0 0)	Result: 0
;; Testing on: (1 0 2 0 0 0)	Result: 1
;; Testing on: (2 0 2 0 0 0)	Result: 1
;; Testing on: (0 1 2 0 0 0)	Result: 0
;; Testing on: (1 1 2 0 0 0)	Result: 0
;; Testing on: (2 1 2 0 0 0)	Result: 1
;; Testing on: (0 2 2 0 0 0)	Result: 0
;; Testing on: (1 2 2 0 0 0)	Result: 0
;; Testing on: (2 2 2 0 0 0)	Result: 0

