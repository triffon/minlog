; fph.scm.  2014-10-11.  Constructive proof.

(load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(libload "list.scm")
(set! COMMENT-FLAG #t)

(add-var-name "s" (py "nat=>nat"))
(add-var-name "i" "j" (py "nat"))
;; (add-var-name "l" (py "list nat"))
;; (add-var-name "ll" (py "list list nat"))

;; Largest pair
;; ============

;; The largest pair in s_0..s_{m+1} is the pair i@j with i#j such that
;; s_i<=s_j and s_k<=s_i for all k#i,j.

(add-var-name "ij" (py "nat@@nat"))

;; Rather than defining the largest pair by

;; (add-program-constant "Lp" (py "(nat=>nat)=>nat=>nat@@nat"))
;; (add-computation-rules
;;  "Lp s 0" "[if (s 0<=s 1) (0@1) (1@0)]"
;;  "Lp s(Succ m)" "([ij] [if (s(Succ(Succ m))<=s left ij)
;;                            ij
;;                            [if (s(Succ(Succ m))<=s right ij)
;;                                (Succ(Succ m)@right ij)
;;                                (right ij@Succ(Succ m))]])
;;                  (Lp s m)")

;; and then proving its properties we extract it from a proof.

;; LpProp
(set-goal "all s,m ex i,j(i<=Succ m & j<=Succ m & (i=j -> F) &
                          s i<=s j &
                          all k(k<=Succ m -> (k=j -> F) -> s k<=s i))")
(assume "s")
(ind)
;; Base
(cases (pt "s 0<=s 1"))
;; Case "s 0<=s 1"
(assume "s 0<=s 1")
(ex-intro (pt "0"))
(ex-intro (pt "1"))
(msplit)
(assume "k" "k<=1" "k#1")
(use "NatLeCases" (pt "1") (pt "k"))
(use "k<=1")
(assume "k<1")
(use "NatLtSuccCases" (pt "0") (pt "k"))
(use "k<1")
(ng)
(use "Efq")
(assume "k=0")
(simp "k=0")
(use "Truth")
(assume "k=1")
(use "Efq")
(use "k#1")
(use "k=1")
(use "s 0<=s 1")
(ng)
(assume "Absurd")
(use "Absurd")
(use "Truth")
(use "Truth")
(assume "s 0<=s 1 -> F")
;; Case "s 0<=s 1 -> F"
(ex-intro (pt "1"))
(ex-intro (pt "0"))
(msplit)
(assume "k" "k<=1" "k#0")
(use "NatLeCases" (pt "1") (pt "k"))
(use "k<=1")
(assume "k<1")
(use "NatLtSuccCases" (pt "0") (pt "k"))
(use "k<1")
(ng)
(use "Efq")
(assume "k=0")
(use "Efq")
(use "k#0")
(use "k=0")
(assume "k=1")
(simp "k=1")
(use "Truth")
(use "NatLtToLe")
(use "NatNotLeToLt")
(use "s 0<=s 1 -> F")
(assume "Absurd")
(use "Absurd")
(use "Truth")
(use "Truth")
;; Step
(assume "m" "IHm")
(by-assume "IHm" "i" "iProp")
(by-assume "iProp" "j" "ijProp")
(cases (pt "s(m+2)<=s i"))
;; Case "s(m+2)<=s i"
(assume "s(m+2)<=s i")
(ex-intro (pt "i"))
(ex-intro (pt "j"))
(msplit)
(assume "k" "k<=m+2" "k#j")
(use "NatLeCases" (pt "Succ(Succ m)") (pt "k"))
(use "k<=m+2")
(assume "k<m+2")
(use "ijProp")
(use "NatLtSuccToLe")
(use "k<m+2")
(use "k#j")
(assume "k=m+2")
(simp "k=m+2")
(use "s(m+2)<=s i")
(use "ijProp")
(use "ijProp")
(use "NatLeTrans" (pt "Succ m"))
(use "ijProp")
(use "Truth")
(use "NatLeTrans" (pt "Succ m"))
(use "ijProp")
(use "Truth")
;; Case "s(m+2)<=s i -> F"
(assume "s(m+2)<=s i -> F")
(assert "s i<s(m+2)")
 (use "NatNotLeToLt")
 (use "s(m+2)<=s i -> F")
(assume "s i<s(m+2")
(cases (pt "s(m+2)<=s j"))
;; Case "s(m+2)<=s j"
(assume "s(m+2)<=s j")
(ex-intro (pt "Succ(Succ m)"))
(ex-intro (pt "j"))
(msplit)
(assume "k" "k<=m+2" "k#j")
(use "NatLeCases" (pt "Succ(Succ m)") (pt "k"))
(use "k<=m+2")
(assume "k<m+2")
(use "NatLtToLe")
(use "NatLeLtTrans" (pt "s i"))
(use "ijProp")
(use "NatLtSuccToLe")
(use "k<m+2")
(use "k#j")
(use "s i<s(m+2")
(assume "k=m+2")
(simp "k=m+2")
(use "Truth")
(use "s(m+2)<=s j")
(assume "m+2=j")
(assert "Succ(Succ m)<=Succ m")
 (use "NatLeTrans" (pt "j"))
 (simp "m+2=j")
 (use "Truth")
 (use "ijProp")
(assume "Succ(Succ m)<=Succ m")
(use "Succ(Succ m)<=Succ m")
(use "NatLeTrans" (pt "Succ m"))
(use "ijProp")
(use "Truth")
(use "Truth")
;; Case "s(m+2)<=s j -> F"
(assume "s(m+2)<=s j -> F")
(assert "s j<s(m+2)")
 (use "NatNotLeToLt")
 (use "s(m+2)<=s j -> F")
(assume "s j<s(m+2)")
(ex-intro (pt "j"))
(ex-intro (pt "Succ(Succ m)"))
(msplit)
(assume "k" "k<=m+2" "k#m+2")
(cases (pt "k=j"))
(assume "k=j")
(simp "k=j")
(use "Truth")
(assume "k#j")
(use "NatLeTrans" (pt "s i"))
(use "ijProp")
(use "NatLeCases" (pt "Succ(Succ m)") (pt "k"))
(use "k<=m+2")
(use "NatLtSuccToLe")
(assume "k=m+2")
(use "Efq")
(use "k#m+2")
(use "k=m+2")
(use "k#j")
(use "ijProp")
(use "NatLtToLe")
(use "s j<s(m+2)")
(assume "j=m+2")
(simphyp-with-to "s j<s(m+2)" "j=m+2" "Absurd")
(use "Absurd")
(use "Truth")
(use "NatLeTrans" (pt "Succ m"))
(use "ijProp")
(use "Truth")
;; Proof finished.
(save "LpProp")

(define eterm (proof-to-extracted-term (theorem-name-to-proof "LpProp")))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [s,n]
;;  (Rec nat=>nat@@nat)n[if (s 0<=s 1) (0@1) (1@0)]
;;  ([n0,ij]
;;    [if (s(Succ(Succ n0))<=s left ij)
;;      ij
;;      [if (s(Succ(Succ n0))<=s right ij)
;;       (Succ(Succ n0)@right ij)
;;       (right ij@Succ(Succ n0))]])

(pp (term-to-type neterm))
;; (nat=>nat)=>nat=>nat@@na

(define lp-expr (term-to-scheme-expr neterm))
;; (lambda (s)
;;   (lambda (n)
;;     (((natRec n) (if (<= (s 0) (s 1)) (cons 0 1) (cons 1 0)))
;;       (lambda (n0)
;;         (lambda (ij)
;;           (if (<= (s (+ (+ n0 1) 1)) (s (car ij)))
;;               ij
;;               (if (<= (s (+ (+ n0 1) 1)) (s (cdr ij)))
;;                   (cons (+ (+ n0 1) 1) (cdr ij))
;;                   (cons (cdr ij) (+ (+ n0 1) 1)))))))))

;; (list-to-seq l) returns a sequence starting with the list l and
;; continuing with 0.

(define (list-to-seq l)
  (lambda (n)
    (if (< n (length l))
	(list-ref l n)
	0)))

;; (first f n) returns a list of (f 0),(f 1),...,(f n-1).

(define (first f n)
  (if (= n 0)
      '()
       (cons (f 0)
	     (first (lambda (n) (f (+ n 1))) (- n 1)))))

(first (list-to-seq '(2 7 4 1 8 5 3)) 10)
;; (2 7 4 1 8 5 3 0 0 0)

(((ev lp-expr) (list-to-seq '(2 7 4 1 8 5 3))) 3)
;; (1 . 4)

(((ev lp-expr) (list-to-seq '(2 7 4 1 8 5 3))) 2)
;; (2 . 1)

;; Finite pigeon hole principle
;; ============================

;; Given a sequence s of numbers such that s_0..s_{m+1} are <=m
;; (colors).  Then among s_0..s_{m+1} two must be equal.  The proof is
;; by induction on m.  Step m -> m+1.  Let i@j be Lp s(m+1) (i.e., the
;; largest pair in s_0..s_{m+2}).  If s_i=s_j we are done.  Assume
;; s_i<s_j.  Let s' be s with s_j omitted.  Apply the IH to s'.

;; Rather that defining FPH by

;; (add-program-constant "FPH" (py "(nat=>nat)=>nat=>nat@@nat"))
;; (add-computation-rules
;; "FPH s 0" "0@1"
;; "FPH s(Succ m)" "([ij][if (s left ij=s right ij)
;;                           ij
;;                           (FPH([n][if (n<right ij) (s n) (s(Succ n))])m)])
;;                  (Lp s(Succ m))")

;; and then proving its properties we extract it from a proof.

;; "FPH"
(set-goal "all m,s(all i(i<=Succ m -> s i<=m) ->
                   ex i,j(i<j & j<=Succ m & s i=s j))")
(ind)
;; Base
(assume "s" "H1")
(ex-intro (pt "0"))
(ex-intro (pt "1"))
(msplit)
(assert "s 0=0")
(use "NatLeAntiSym")
(use "H1")
(use "Truth")
(use "Truth")
(assume "s 0=0")
(assert "s 1=0")
(use "NatLeAntiSym")
(use "H1")
(use "Truth")
(use "Truth")
(assume "s 1=0")
(simp "s 1=0")
(use "s 0=0")
(use "Truth")
(use "Truth")
;; Step
(assume "m" "IH" "s" "H1")
;;   m6614  m  IH:all s(all i(i<=Succ m -> s i<=m) -> 
;;                 ex i,j(i<j & j<=Succ m & s i=s j))
;;   s  H1:all i(i<=Succ(Succ m) -> s i<=Succ m)
;; -----------------------------------------------------------------------------
;; ?_24:ex i,j(i<j & j<=Succ(Succ m) & s i=s j)

;; Pick a largest pair for s up to m+2

;; (cut "ex i,j(i<j & j<=Succ(Succ m) & s i=s j)")
;; (pp "LpProp")
(cut "ex i,j(
  i<=Succ(Succ m) & 
  j<=Succ(Succ m) & 
  (i=j -> F) & s i<=s j & all k(k<=Succ(Succ m) -> (k=j -> F) -> s k<=s i))")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "ExLP")
;; (inst-with-to "LpProp" (pt "s") (pt "Succ m") "ExLP")
(by-assume "ExLP" "i" "iProp")
(by-assume "iProp" "j" "ijProp")
(use "NatLeCases" (pt "s j") (pt "s i"))
(use "ijProp")
(assume "s i<s j")
(inst-with-to "IH" (pt "[n][if (n<j) (s n) (s(Succ n))]") "IHInst")
(drop "IH")
(ng "IHInst")
(assert "all i(i<=Succ m -> [if (i<j) (s i) (s(Succ i))]<=m)")
 (assume "n" "n<=m+1")
 (cases 'auto)
 (assume "n<j")
 (ng #t)
 (use "NatLtSuccToLe")
 (use "NatLeLtTrans" (pt "s i"))
 (use "ijProp")
 (use "NatLeTrans" (pt "Succ m"))
 (use "n<=m+1")
 (use "Truth")
 (assume "n=j")
 (simphyp-with-to "n<j" "n=j" "Absurd")
 (use "Absurd")
 (use "NatLtLeTrans" (pt "s j"))
 (use "s i<s j")
 (use "H1")
 (use "ijProp")
 (assume "n<j -> F")
 (ng #t)
 (use "NatLtSuccToLe")
 (use "NatLeLtTrans" (pt "s i"))
 (use "ijProp")
 (use "n<=m+1")
 (assume "n+1=j")
 (use "n<j -> F")
 (simp "<-" "n+1=j")
 (use "Truth")
 (use "NatLtLeTrans" (pt "s j"))
 (use "s i<s j")
 (use "H1")
 (use "ijProp")
(assume "sWithoutsjProp")
(cut "ex i,j0(
            i<j0 & 
            j0<=Succ m & 
            [if (i<j) (s i) (s(Succ i))]=[if (j0<j) (s j0) (s(Succ j0))])")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "ExPrevLP")
(by-assume "ExPrevLP" "i0" "i0Prop")
(by-assume "i0Prop" "j0" "j0Prop")
(cases (pt "j0<j"))
;; Case "j0<j"
(assume "j0<j")
(ex-intro (pt "i0"))
(ex-intro (pt "j0"))
(msplit)
(simphyp-with-to "j0Prop" "j0<j" "j0PropSimp")
(ng "j0PropSimp")
(assert "i0<j")
 (use "NatLtTrans" (pt "j0"))
 (use "j0Prop")
 (use "j0<j")
(assume "i0<j")
(simphyp-with-to "j0PropSimp" "i0<j" "j0PropSimpSimp")
(ng "j0PropSimpSimp")
(use "j0PropSimpSimp")
(use "NatLeTrans" (pt "Succ m"))
(use "j0Prop")
(use "Truth")
(use "j0Prop")
;; Case "j0<j -> F"
(assume "j0<j -> F")
(cases (pt "i0<j"))
;; Case "i0<j"
(assume "i0<j")
(ex-intro (pt "i0"))
(ex-intro (pt "Succ j0"))
(msplit)
(simphyp-with-to "j0Prop" "i0<j" "j0PropSimp")
(simphyp-with-to "j0PropSimp" "j0<j -> F" "j0PropSimpSimp")
(ng "j0PropSimpSimp")
(use "j0PropSimpSimp")
(use "j0Prop")
(use "NatLtTrans" (pt "j0"))
(use "j0Prop")
(use "Truth")
;; Case "i0<j -> F"
(assume "i0<j -> F")
(ex-intro (pt "Succ i0"))
(ex-intro (pt "Succ j0"))
(msplit)
(simphyp-with-to "j0Prop" "i0<j -> F" "j0PropSimp")
(simphyp-with-to "j0PropSimp" "j0<j -> F" "j0PropSimpSimp")
(ng "j0PropSimpSimp")
(use "j0PropSimpSimp")
(use "j0Prop")
(use "j0Prop")
;; ex i,j0(
;;       i<j0 & 
;;       j0<=Succ m & 
;;       [if (i<j) (s i) (s(Succ i))]=[if (j0<j) (s j0) (s(Succ j0))])
(use "IHInst")
(use "sWithoutsjProp")
;; Finally the trivial case "s i=s j"
(assume "s i=s j")
(cases (pt "i<j"))
;; Case "i<j"
(assume "i<j")
(ex-intro (pt "i"))
(ex-intro (pt "j"))
(msplit)
(use "s i=s j")
(use "ijProp")
(use "i<j")
;; Case "i<j -> F"
(assume "i<j -> F")
(ex-intro (pt "j"))
(ex-intro (pt "i"))
(msplit)
(use "NatEqSym")
(use "s i=s j")
(use "ijProp")
(use "NatNotLeToLt")
(assume "i<=j")
(use "NatLeCases" (pt "j") (pt "i"))
(use "i<=j")
(use "i<j -> F")
(use "ijProp")
;; ex i,j(
;;       i<=Succ(Succ m) & 
;;       j<=Succ(Succ m) & 
;;       (i=j -> F) & 
;;       s i<=s j & all k(k<=Succ(Succ m) -> (k=j -> F) -> s k<=s i))
(use "LpProp")
;; Proof finished.
;; (remove-theorem "FPH")
(save "FPH")

(define eterm (proof-to-extracted-term (theorem-name-to-proof "FPH")))
(add-var-name "H" (py "(nat=>nat)=>nat@@nat"))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [n]
;;  (Rec nat=>(nat=>nat)=>nat@@nat)n([s]0@1)
;;  ([n0,H,s]
;;    [let ij
;;      (cLpProp s(Succ n0))
;;      ((cNatLeCases nat@@nat)(s right ij)(s left ij)
;;      [let ij0
;;        (H([n1][if (n1<right ij) (s n1) (s(Succ n1))]))
;;        [if (right ij0<right ij)
;;         ij0
;;         ([if (left ij0<right ij)
;; 	     (left ij0)
;; 	     (Succ left ij0)]@Succ right ij0)]]
;;      [if (left ij<right ij) ij (right ij@left ij)])])

(animate "LpProp")
(animate "NatLeCases")
(define neterm (rename-variables (nt eterm)))

;; Test

(define fph-expr (term-to-scheme-expr neterm))

(((ev fph-expr) 3) (lambda (n) n))
;; (0 . 1)

;; (generate-seq n) generates a list of 2^n infinite sequences starting
;; with all possible variations of n digits and continuing with 0.

(define (generate-seq n)
  (if (= n 0)
      (list (lambda (n) 0))
      (foldr (lambda (f l)
	       (cons (lambda (n) (if (= n 0) 0 (f (- n 1))))
		     (cons (lambda (n) (if (= n 0) 1 (f (- n 1))))
			   l)))
	     '()
	     (generate-seq (- n 1)))))

;; (length (generate-seq 4))
;; 16

;; (first f n) returns a list of (f 0),(f 1),...,(f n-1).

(define (first f n)
  (if (= n 0)
      '()
       (cons (f 0)
	     (first (lambda (n) (f (+ n 1))) (- n 1)))))

;; (for-each (lambda (x) (display (first x 7)) (newline)) (generate-seq 4))
;; (0 0 0 0 0 0 0)
;; (1 0 0 0 0 0 0)
;; (0 1 0 0 0 0 0)
;; (1 1 0 0 0 0 0)
;; (0 0 1 0 0 0 0)
;; (1 0 1 0 0 0 0)
;; (0 1 1 0 0 0 0)
;; (1 1 1 0 0 0 0)
;; (0 0 0 1 0 0 0)
;; (1 0 0 1 0 0 0)
;; (0 1 0 1 0 0 0)
;; (1 1 0 1 0 0 0)
;; (0 0 1 1 0 0 0)
;; (1 0 1 1 0 0 0)
;; (0 1 1 1 0 0 0)
;; (1 1 1 1 0 0 0)

(for-each (lambda (f)
	    (display (((ev fph-expr) 3) f))
	    (display " indicates equal digits in ")
	    (display (first f 7))
	    (newline))
	  (generate-seq 4))

;; (0 . 1) indicates equal digits in (0 0 0 0 0 0 0)
;; (1 . 2) indicates equal digits in (1 0 0 0 0 0 0)
;; (0 . 2) indicates equal digits in (0 1 0 0 0 0 0)
;; (0 . 1) indicates equal digits in (1 1 0 0 0 0 0)
;; (0 . 1) indicates equal digits in (0 0 1 0 0 0 0)
;; (0 . 2) indicates equal digits in (1 0 1 0 0 0 0)
;; (1 . 2) indicates equal digits in (0 1 1 0 0 0 0)
;; (0 . 1) indicates equal digits in (1 1 1 0 0 0 0)
;; (0 . 1) indicates equal digits in (0 0 0 1 0 0 0)
;; (0 . 3) indicates equal digits in (1 0 0 1 0 0 0)
;; (1 . 3) indicates equal digits in (0 1 0 1 0 0 0)
;; (0 . 1) indicates equal digits in (1 1 0 1 0 0 0)
;; (2 . 3) indicates equal digits in (0 0 1 1 0 0 0)
;; (0 . 2) indicates equal digits in (1 0 1 1 0 0 0)
;; (1 . 2) indicates equal digits in (0 1 1 1 0 0 0)
;; (0 . 1) indicates equal digits in (1 1 1 1 0 0 0)

;; A corollary of LpProp (largest pair) and FPH useful for Dickson's lemma
;; =======================================================================

;; Every injective function s on 0...(m+1) has at one point j a value
;; s_j such that m<s_j.

;; Proof.  Let i@j be Lp s m (i.e., the largest pair in s_0..s_{m+1}).
;; If s_j<=m, all s_i are <=m.  Hence by FPH among s_0..s_{m+1} two
;; must be equal.  This contradicts injectivity.  Hence m<s_j.

;; "FPHCor"
(set-goal "all s,m(
 all i,j(i<j -> j<=Succ m -> s i=s j -> F) ->
 ex j(j<=Succ m & m<s j))")
(assume "s" "m" "Inj")
(inst-with-to "LpProp" (pt "s") (pt "m") "Lp")
(by-assume "Lp" "i" "iProp")
(by-assume "iProp" "j" "ijProp")
(ex-intro (pt "j"))
(split)
(use "ijProp")
(use "NatNotLeToLt")
(assume "s j<=m")
(assert "all k(k<=Succ m -> s k<=m)")
 (assume "k" "k<=S m")
 (cases (pt "k=j"))
 (assume "k=j")
 (simp "k=j")
 (use "s j<=m")
 (assume "k=j -> F")
 (use "NatLeTrans" (pt "s i"))
 (use "ijProp")
 (use "k<=S m")
 (use "k=j -> F")
 (use "NatLeTrans" (pt "s j"))
 (use "ijProp")
 (use "s j<=m")
(assume "FPHPrem")
(inst-with-to "FPH" (pt "m") (pt "s") "FPHPrem" "FPHConcl")
(by-assume "FPHConcl" "i1" "i1Prop")
(by-assume "i1Prop" "j1" "i1j1Prop")
(use "Inj" (pt "i1") (pt "j1"))
(use "i1j1Prop")
(use "i1j1Prop")
(use "i1j1Prop")
;; Proof finished.
(save "FPHCor")

(define eterm (proof-to-extracted-term (theorem-name-to-proof "FPHCor")))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [s,n]
;;  right((Rec nat=>nat@@nat)n[if (s 0<=s 1) (0@1) (1@0)]
;;        ([n0,ij]
;;          [if (s(Succ(Succ n0))<=s left ij)
;;            ij
;;            [if (s(Succ(Succ n0))<=s right ij)
;;             (Succ(Succ n0)@right ij)
;;             (right ij@Succ(Succ n0))]]))

;; The right component of the largest pair (see above)
