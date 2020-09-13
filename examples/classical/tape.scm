;; 2020-09-10.  tape.scm

;; Based on work of Diana Ratiu and Trifon Trifonov.

;; Problem:
;;  Given: An infinite tape containing 0s and 1s:
;;                 A: all n(f n=0 \/ f n=1)
;;  To show: There exist two cells with the same content:
;;                 G: excl n,m(n<m ! f n=f m)
;; Aditional information:
;;                 Inf0: all n excl k(n<=k ! f k=0)
;;                 Inf1: all n excl k(n<=k ! f k=1)
;; In our classical setting:
;;            A: all n((f n=0 -> bot) -> (f n=1 -> bot) -> bot)

;; (load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(set! COMMENT-FLAG #t)

(add-var-name "k" (py "nat"))

;; The infinite 0/1 tape
(add-var-name "f" (py "nat=>nat"))

;; We first show Lemma 1 (Stolzenberg's Principle, "InfZeroOrInfOne"):
;; The infinite boolean tape contains either infinitely many 0s or
;; infinitely many 1s.

;; Lemma(s) 2 ("InfZeroToG", "InfOneToG"): If either Inf0 or Inf1,
;; then G (the desired property of the tape).

;; and then the Corollary of Stolzenberg's Principle ("TapeTheorem"):
;; In an infinite tape containing 0s and 1s, there exist two cells with
;; the same content.

;; InfZeroOrInfOne
(set-goal "all f(
       all n((f n=0 -> bot) -> (f n=1 -> bot) -> bot) ->
       excl n all k(n<=k -> f k=0 -> bot) ->
       excl n all k(n<=k -> f k=1 -> bot) ->
       bot)")
(assume "f" "A" "NotInf0" "NotInf1")
(use "NotInf0")
(assume "m" "Hm")
(drop "NotInf0")
(use "NotInf1")
(assume "n" "Hn")
(drop "NotInf1")
(use "A" (pt "m max n"))
(use "Hm")
(use "NatMaxUB1")
(use "Hn")
(use "NatMaxUB2")
;; Proof finished.
(save "InfZeroOrInfOne")

;; The 2nd pair of Lemmas is "InfZeroToG": Inf0 -> G and "InfOneToG":
;; Inf1 -> G

;; InfZeroToG
(set-goal "all f(all n excl k(n<=k ! f k=0) -> excl n,m(n<m ! f n=f m))")
(assume "f" "Inf0" "NotG")
(use "Inf0" (pt "0"))
(assume "k" "Useless" "f k=0")
(drop "Useless")
(use "Inf0" (pt "Succ k"))
(assume "n" "Succ k<=n" "f n=0")
(use "NotG" (pt "k") (pt "n"))
(use "NatSuccLeToLt")
(use "Succ k<=n")
(use "NatEqTrans" (pt "0"))
(use "f k=0")
(use "NatEqSym")
(use "f n=0")
;; Proof finished.
(save "InfZeroToG")

;; InfOneToG
(set-goal "all f(all n excl k(n<=k ! f k=1) -> excl n,m(n<m ! f n=f m))")
(assume "f" "Inf1" "NotG")
(use "Inf1" (pt "0"))
(assume "k" "Useless" "f k=1")
(drop "Useless")
(use "Inf1" (pt "Succ k"))
(assume "n" "Succ k<=n" "f n=1")
(use "NotG" (pt "k") (pt "n"))
(use "NatSuccLeToLt")
(use "Succ k<=n")
(use "NatEqTrans" (pt "1"))
(use "f k=1")
(use "NatEqSym")
(use "f n=1")
;; Proof finished.
(save "InfOneToG")

;; Corollary of Stolzenberg's Principle: In an infinite tape containing
;; 0s and 1s, there exist two cells with the same content.

;; TapeTheorem
(set-goal "all f(
       all n((f n=0 -> bot) -> (f n=1 -> bot) -> bot) ->
       excl n,m(n<m ! f n=f m))")
(assume "f" "A" "H")
(use-with "InfZeroOrInfOne" (pt "f") "A" "?" "?")
(assume "H0")
(use-with "InfZeroToG" (pt "f") "H0" "H")
(assume "H1")
(use-with "InfOneToG" (pt "f") "H1" "H")
;; Proof finished.
(save "TapeTheorem")

(define tape-proof (theorem-name-to-proof "TapeTheorem"))
(proof-to-expr-with-formulas tape-proof)

;; Extraction
;; ==========

(atr-definite? (aconst-to-formula (theorem-name-to-aconst "InfZeroOrInfOne")))
(atr-definite? (aconst-to-formula (theorem-name-to-aconst "InfOneToG")))
(atr-definite? (aconst-to-formula (theorem-name-to-aconst "InfZeroToG")))

;; We expand the non-definite theorems "InfZeroOrInfOne", "InfOneToG",
;; "InfZeroToG".

(define expanded-tape-proof (np (atr-expand-theorems tape-proof)))
;; (proof-to-expr-with-formulas expanded-tape-proof)

;; We extract a term and normalize it.

(define eterm
  (atr-min-excl-proof-to-structured-extracted-term expanded-tape-proof))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [f]
;;  [if (f 0=1)
;;    [if (f 1=1)
;;     (0 pair 1)
;;     [if (f 1=0)
;;      [if (f 2=1)
;;       [if (f 3=1) (2 pair 3) [if (f 3=0) (1 pair 3) (0 pair 0)]]
;;       [if (f 2=0) (1 pair 2) (0 pair 0)]]
;;      (0 pair 0)]]
;;    [if (f 0=0)
;;     [if (f 1=1)
;;      [if (f 2=1) (1 pair 2) [if (f 2=0) (0 pair 2) (0 pair 0)]]
;;      [if (f 1=0) (0 pair 1) (0 pair 0)]]
;;     (0 pair 0)]]

;; This is the 2nd variant on p.54 of Diana Ratiu's thesis.

(define expr (term-to-scheme-expr neterm))

;; Tests
;; =====

;; The Scheme program for the extracted term

(define (program term)
  (lambda (seq)
    (let ((prog (ev (term-to-scheme-expr term))))
      (prog seq))))

;; ev is defined in init.scm as eval.  In other Scheme implementations
;; one may also try (define (ev x) (eval x (interaction-environment)))

;; We generate a list of 2^n infinite sequences starting with all
;; possible variations of n booleans and continuing with 0 and then
;; take its first "n" elements.

(define (generate-seq n)
  (if (= n 0)
      (list (lambda (n) 0))
      (foldr (lambda (x l)
	       (cons (lambda (n) (if (= n 0) 0 (x (- n 1))))
		     (cons (lambda (n) (if (= n 0) 1 (x (- n 1))))
			   l)))
	     '()
	     (generate-seq (- n 1)))))

;; fold right: (foldr bin-op initial-value list) folds a list with
;; bin-op starting from the end of the list

;; (first f n) returns the list of the first n elements of f.

(define (first f n)
  (if (= n 0)
      '()
      (cons (f 0)
	    (first (lambda (n) (f (+ n 1))) (- n 1)))))

;; Test a Scheme program on a list of infinite binary sequences

(define (test-bseq program . l)
  (let ((len (if (null? l) 4 (car l))))
    (map (lambda (seq)
	   (display "Testing on ")
	   (display (first seq len))
	   (display ": Result ")
	   (display (program seq))
	   (newline))
	 (generate-seq len)))
  *the-non-printing-object*)

(test-bseq (program neterm) 4)

;; Testing on (1 1 1 1): Result (0 . 1)
;; Testing on (0 1 1 1): Result (1 . 2)
;; Testing on (1 0 1 1): Result (2 . 3)
;; Testing on (0 0 1 1): Result (0 . 1)
;; Testing on (1 1 0 1): Result (0 . 1)
;; Testing on (0 1 0 1): Result (0 . 2)
;; Testing on (1 0 0 1): Result (1 . 2)
;; Testing on (0 0 0 1): Result (0 . 1)
;; Testing on (1 1 1 0): Result (0 . 1)
;; Testing on (0 1 1 0): Result (1 . 2)
;; Testing on (1 0 1 0): Result (1 . 3)
;; Testing on (0 0 1 0): Result (0 . 1)
;; Testing on (1 1 0 0): Result (0 . 1)
;; Testing on (0 1 0 0): Result (0 . 2)
;; Testing on (1 0 0 0): Result (1 . 2)
;; Testing on (0 0 0 0): Result (0 . 1)

;; Notice that there is asymmetry for (1 0 1 1) (with result: (2 . 3))
;; and (0 1 0 0) (with result (0 . 2)).  This is due to dealing with 0
;; first in the proofs.
