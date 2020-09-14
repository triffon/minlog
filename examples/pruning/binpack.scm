;; 2014-10-16.  binpack.scm
;; New attempt, using "Legal" as a program constant

;; (load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(libload "list.scm")
(set! COMMENT-FLAG #t)

(add-var-name "A" "X" "B" (py "list nat")) 
(add-var-name "i" "j" "a" "k" (py "nat"))
(add-var-name "p" (py "boole"))

;; X=i0::i1::...::i(p-1): is a list of blocks, B=j0::j1::...::j(q-1): a
;; list of bins, and A=k0::k1::...::k(p-1): an assignment giving the
;; indices of bins the blocks should go into.

;; Decr B k i decreases B__k by i.  It is defined via DecrAux,
;; searching for k.

(add-program-constant
 "DecrAux" (py "list nat=>nat=>nat=>nat=>list nat"))
(add-computation-rules
 "DecrAux(Nil nat)m a n" "(Nil nat)"
 "DecrAux(j::B)k i n" "[if (n=k) ((j--i)::B) (j::(DecrAux B k i(n+1)))]")

;; DecrAuxTotal
(set-totality-goal "DecrAux")
(use "AllTotalElim")
(ind)
;; Base
(strip)
(ng)
(use "TotalListNil")
;; Step
(assume "j" "A" "IH")
(use "AllTotalElim")
(assume "k")
(use "AllTotalElim")
(assume "i")
(use "AllTotalElim")
(assume "n")
(ng)
(use "BooleIfTotal")
(use "BooleTotalVar")
(use "ListTotalVar")
(use "TotalListCons")
(use "NatTotalVar")
(use "IH")
(use "NatTotalVar")
(use "NatTotalVar")
(use "NatTotalVar")
;; Proof finished.
(save-totality)

(add-program-constant "Decr" (py "list nat=>nat=>nat=>list nat"))
(add-computation-rules
 "Decr B k i" "DecrAux B k i 0")

;; DecrTotal
(set-totality-goal "Decr")
(use "AllTotalElim")
(assume "B")
(use "AllTotalElim")
(assume "k")
(use "AllTotalElim")
(assume "i")
(use "ListTotalVar")
;; Proof finished.
(save-totality)

;; (pp (nt (pt "Decr(j1::j2:)1 i")))
;; j1::(j2--i):

(add-program-constant "Legal" (py "list nat=>list nat=>list nat=>boole"))
(add-computation-rules
 "Legal(Nil nat)(Nil nat)B" "True"
 "Legal(Nil nat)(i::X)B" "False"
 "Legal(k::A)(Nil nat)B" "False"
 "Legal(k::A)(i::X)B" "k<Lh B andb i<=(k thof B)andb Legal A X(Decr B k i)")

;; LegalTotal
(set-totality-goal "Legal")
(use "AllTotalElim")
(ind)
;; Base
(use "AllTotalElim")
(cases)
(strip)
(ng)
(use "TotalBooleTrue")
(strip)
(ng)
(use "TotalBooleFalse")
;; Step
(assume "k" "A" "IH")
(use "AllTotalElim")
(cases)
(strip)
(ng)
(use "TotalBooleFalse")
(assume "i" "X")
(use "AllTotalElim")
(assume "B")
(ng)
(use "AndConstTotal")
(use "BooleTotalVar")
(use "AndConstTotal")
(use "BooleTotalVar")
(use "IH")
(use "ListTotalVar")
(use "ListTotalVar")
;; Proof finished.
(save-totality)

;; "LegalLength"
(set-goal "all A,X,B(Legal A X B -> Lh A=Lh X)")
(ind)
(cases)
(assume "B" "Useless")
(use "Truth")
(assume "k" "A" "B" "Absurd")
(use "Absurd")
(assume "k" "A" "IH")
(cases)
(assume "B" "Absurd")
(use "Absurd")
(assume "i" "X" "B" "H1")
(ng)
(use "IH" (pt "Decr B k i"))
(use "H1")
;; Proof finished.
(save "LegalLength")

;; "LegalZero"
(set-goal "all i,X,B,A(0<Lh A ->
                       (0 thof A)<Lh B ->
                       i<=((0 thof A)thof B) ->
                       Legal(Tail A)X(Decr B(0 thof A)i) ->
                       Legal A(i::X)B)")
(assume "i" "X" "B")
(cases)
(ng)
(use "Efq")
(assume "k" "A" "H1" "H2" "H3" "H4")
(ng)
(split)
(use "H2")
(split)
(use "H3")
(use "H4")
;; Proof finished.
(save "LegalZero")

;; "LegalOne"
(set-goal "all i,X,B,A(Legal A(i::X)B -> (0 thof A)<Lh B)")
(assume "i" "X" "B")
(cases)
(ng)
(use "Efq")
(assume "k" "A" "H1")
(ng)
(use "H1")
;; Proof finished.
(save "LegalOne")

;; "LegalTwo"
(set-goal "all i,X,B,A(Legal A(i::X)B -> i<=((0 thof A)thof B))")
(assume "i" "X" "B")
(cases)
(ng)
(use "Efq")
(assume "k" "A" "H1")
(ng)
(use "H1")
;; Proof finished.
(save "LegalTwo")

;; "LegalThree"
(set-goal "all i,X,B,A(Legal A(i::X)B -> Legal(Tail A)X(Decr B(0 thof A)i))")
(assume "i" "X" "B")
(cases)
(ng)
(use "Efq")
(assume "k" "A" "H1")
(ng)
(use "H1")
;; Proof finished.
(save "LegalThree")

;; "LemmaZero"
(set-goal "all i,X,B,n(
  (ex A(Legal A(i::X)B & n+1<=(0 thof A)) -> F) ->
  (ex A Legal A X(Decr B n i) -> F) ->
  ex A(Legal A(i::X)B & n<=(0 thof A)) -> F)")
(assume "i" "X" "B" "n" "Hyp1" "Hyp2" "Hyp3")
(by-assume-with "Hyp3" "A" "AProp")
(inst-with-to "AProp" 'left "Legal A(i::X)B")
(inst-with-to "AProp" 'right "n<=(0 thof A)")
(drop "AProp")
(use "NatLeCases" (pt "n") (pt "(0 thof A)"))
(use "n<=(0 thof A)")
(assume "n<(0 thof A)")
(drop "Hyp2")
(use "Hyp1")
(drop "Hyp1")
(ex-intro "A")
(split)
(use "Legal A(i::X)B")
(ng #t)
(use "NatLtToSuccLe")
(use "n<(0 thof A)")
(assume "n=(0 thof A)")
(drop "Hyp1")
(use "Hyp2")
(drop "Hyp2")
(ex-intro "Tail A")
(simp "n=(0 thof A)")
(use "LegalThree")
(use "Legal A(i::X)B")
;; Proof finished.
(save "LemmaZero")

;; "LemmaOne"
(set-goal "all i,X,B,n(
  (n thof B)<i ->
  (ex A(Legal A(i::X)B & n+1<=(0 thof A)) -> F) ->
  ex A(Legal A(i::X)B & n<=(0 thof A)) -> F)")
(assume "i" "X" "B" "n" "Hyp1" "Hyp2" "Hyp3")
(by-assume-with "Hyp3" "A" "AProp")
(inst-with-to "AProp" 'left "Legal A(i::X)B")
(inst-with-to "AProp" 'right "n<=(0 thof A)")
(drop "AProp")
(use "NatLeCases" (pt "n") (pt "(0 thof A)"))
(use "n<=(0 thof A)")
(assume "n<(0 thof A)")
(use "Hyp2")
(drop "Hyp2")
(ex-intro "A")
(split)
(use "Legal A(i::X)B")
(ng #t)
(use "NatLtToSuccLe")
(use "n<(0 thof A)")
(assume "n=(0 thof A)")
(drop "Hyp2" "n<=(0 thof A)")
(assert (pf "i<=((0 thof A)thof B)"))
 (use "LegalTwo" (pt "X"))
 (use "Legal A(i::X)B")
(assume "i<=((0 thof A)thof B)")
(cut (pf "(n thof B)<((0 thof A) thof B)"))
(simp "n=(0 thof A)")
(assume "Absurd")
(use "Absurd")
(use "NatLtLeTrans" (pt "i"))
(use "Hyp1")
(use "i<=((0 thof A)thof B)")
;; Proof finished.
(save "LemmaOne")

;; NatSuccPredCases
(set-goal "all nat((nat=0 -> Pvar) -> (nat=Succ(Pred nat) -> Pvar) -> Pvar)")
(cases)
(assume "H1" "H2")
(use "H1")
(use "Truth")
(assume "nat" "H1" "H2")
(use "H2")
(use "Truth")
;; Proof finished.
(save "NatSuccPredCases")

;; NatLtPredMinus
(set-goal "all nat1,nat2(0<nat1--nat2 -> Pred(nat1--nat2)<nat1)")
(ind)
(assume "nat2" "Absurd")
(use "Absurd")
(assume "nat1" "IH1")
(cases)
(assume "Trivial")
(use "Truth")
(ng)
(assume "nat2" "H1")
(use "NatLtTrans" (pt "nat1"))
(use "IH1")
(use "H1")
(use "Truth")
;; Proof finished.
(save "NatLtPredMinus")

;; BinPackIf
(set-goal "all X,B ex p((p -> ex A Legal A X B) &
                        ((p -> F) -> ex A Legal A X B -> F))")
(ind)
;; Base
(assume "B")
(ex-intro "True")
(split)
(assume "Useless")
(ex-intro "(Nil nat)")
(use "Truth")
(assume "Absurd" "Hyp")
(use "Absurd")
(use "Truth")
;; Step
(assume "i" "X" "DecX" "B")
;; Assert the bounded bin packing specification.
(assert "all n ex p(
  (p -> ex A(Legal A(i::X)B & Lh B--n<=(0 thof A))) & 
  ((p -> F) -> ex A(Legal A(i::X)B & Lh B--n<=(0 thof A)) -> F))")
 (ind)
 ;; Base
 (drop "DecX")
 (ex-intro "False")
 (split)
 (use "Efq")
 (assume "Useless" "ExHyp")
 (drop "Useless")
 (by-assume-with "ExHyp" "A" "AProp")
 (cut "(0 thof A)<(0 thof A)")
 (assume "Absurd")
 (use "Absurd")
 (use "NatLtLeTrans" (pt "Lh B"))
 (use "LegalOne" (pt "i") (pt "X"))
 (use "AProp")
 (use "AProp")
 ;; Step
 (assume "n" "IHn")
 (use "NatSuccPredCases" (pt "Lh B--n"))

 ;; Case 2.  "Lh B--n=0"
 (assume "Lh B--n=0")
 (assert "Pred(Lh B--n)=Lh B--n")
  (simp "Lh B--n=0")
  (use "Truth")
 (assume "Pred(Lh B--n)=Lh B--n")
 (ng)
 (simp "Pred(Lh B--n)=Lh B--n")
 (use "IHn")

 ;; Case 1.  "Lh B--n=Succ(Pred(Lh B--n))"
 (assume "Lh B--n=Succ(Pred(Lh B--n))")
 (use "If" (pt "i<=(Pred(Lh B--n)thof B)"))
;;  (cases (pt "i<=(Pred(Lh B--n)thof B)"))

 ;; Case 1.1.  "i<=(Pred(Lh B--n)thof B)"
 (assume "i<=(Pred(Lh B--n)thof B)")

 (inst-with-to "DecX" (pt "Decr B(Pred(Lh B--n))i") "IHDecr")
 (by-assume-with "IHDecr" "p" "pProp")
 (use "If" (pt "p"))
;;  (cases (pt "p"))

 ;; Cases 1.1.1 "ex A Legal A X(Decr B(Pred(Lh B--n))i)"
 (assume "pTrue")
 (inst-with-to "pProp" 'left "Hyp1")
 (drop "pProp")
 (inst-with-to "Hyp1" "pTrue" "ExHyp")
 (drop "Hyp1" "pTrue")
 (by-assume-with "ExHyp" "A" "Legal A X(Decr B(Pred(Lh B--n))i)")
 (ex-intro "True")
 (split)
 (assume "Useless")
 (drop "Useless")
 (ex-intro "Pred(Lh B--n)::A")
 (split)
 (use "LegalZero")
 (use "Truth")
 (ng #t)
 (use "NatLtPredMinus")
 (simp "Lh B--n=Succ(Pred(Lh B--n))")
 (use "Truth")
 (use "i<=(Pred(Lh B--n)thof B)")
 (use "Legal A X(Decr B(Pred(Lh B--n))i)")
 (use "Truth")
 (assume "Absurd")
 (use "Efq")
 (use "Absurd")
 (use "Truth")

 ;; Case 1.1.2 "ex A Legal A X(Decr B(Pred(Lh B--n))i) -> F"
 (assume "pFalse")
 (inst-with-to "pProp" 'right "Hyp1")
 (drop "pProp")
 (inst-with-to "Hyp1" "pFalse" "NegExHyp")
 (drop "Hyp1" "pFalse")

 ;; Now apply "IHn".
 (by-assume-with "IHn" "p1" "IHnKernel")
 (use "If" (pt "p1"))

 ;; Case 1.1.2.1.  "ex A(Legal A(i::X)B & Lh B--n<=(0 thof A)))"
 (assume "p1True")
 (inst-with-to "IHnKernel" 'left "Hyp2")
 (drop "IHnKernel")
 (inst-with-to "Hyp2" "p1True" "ExHyp")
 (ex-intro "True")
 (split)
 (assume "Useless")
 (drop "Useless")
 (by-assume-with "ExHyp" "A" "Legal A(i::X)B & Lh B--n<=(0 thof A)")
 (ex-intro "A")
 (split)
 (use "Legal A(i::X)B & Lh B--n<=(0 thof A)")
 (use "NatLeTrans" (pt "Lh B--n"))
 (use "Truth")
 (use "Legal A(i::X)B & Lh B--n<=(0 thof A)")
 (assume "Absurd")
 (use "Efq")
 (use "Absurd")
 (use "Truth")

 ;; Case 1.1.2.2.  "ex A(Legal A(i::X)B & Lh B--n<=(0 thof A))) -> F"
 (assume "p1False")
 (inst-with-to "IHnKernel" 'right "Hyp2")
 (drop "IHnKernel")
 (inst-with-to "Hyp2" "p1False" "NegExHyp1")
 (ex-intro "False")
 (split)
 (use "Efq")
 (assume "Useless")
 (drop "Useless")
 (use "LemmaZero")
 (ng #t)
 (simp "<-" "Lh B--n=Succ(Pred(Lh B--n))")
 (use "NegExHyp1")
 (drop "NegExHyp1")
 (use "NegExHyp")

 ;; Case 1.2. "i<=(Pred(Lh B--n)thof B) -> F"
 (assume "i<=(Pred(Lh B--n)thof B) -> F")
 (by-assume-with "IHn" "p1" "IHnKernel")
 (use "If" (pt "p1"))

 ;; Case 1.2.1.  "ex A(Legal A(i::X)B & Lh B--n<=(0 thof A)))"  (as 1.1.2.1)
 (assume "p1True")
 (inst-with-to "IHnKernel" 'left "Hyp2")
 (drop "IHnKernel")
 (inst-with-to "Hyp2" "p1True" "ExHyp")
 (ex-intro "True")
 (split)
 (assume "Useless")
 (drop "Useless")
 (by-assume-with "ExHyp" "A" "Legal A(i::X)B & Lh B--n<=(0 thof A)")
 (ex-intro "A")
 (split)
 (use "Legal A(i::X)B & Lh B--n<=(0 thof A)")
 (use "NatLeTrans" (pt "Lh B--n"))
 (use "Truth")
 (use "Legal A(i::X)B & Lh B--n<=(0 thof A)")
 (assume "Absurd")
 (use "Efq")
 (use "Absurd")
 (use "Truth")

 ;; Case 1.2.2.  "ex A(Legal A(i::X)B & Lh B--n<=(0 thof A))) -> F"
 (assume "p1False")
 (inst-with-to "IHnKernel" 'right "Hyp2")
 (drop "IHnKernel")
 (inst-with-to "Hyp2" "p1False" "NegExHyp1")
 (ex-intro "False")
 (split)
 (use "Efq")
 (assume "Useless")
 (drop "Useless")
 (use "LemmaOne")
 (use "NatNotLeToLt")
 (use "i<=(Pred(Lh B--n)thof B) -> F")
 (ng #t)
 (simp "<-" "Lh B--n=Succ(Pred(Lh B--n))")
 (use "NegExHyp1")

;; Now we have the assertion above available.
(assume "BPack")
(inst-with-to "BPack" (pt "Lh B") "Pack")
(drop "BPack" "DecX")
(by-assume-with "Pack" "p" "pProp")
(ex-intro "p")
(split)
(assume "pTrue")
(inst-with-to "pProp" 'left "Hyp1")
(inst-with-to "Hyp1" "pTrue" "ExHyp")
(by-assume-with "ExHyp" "A" "Legal A(i::X)B & 0<=(0 thof A)")
(ex-intro "A")
(use "Legal A(i::X)B & 0<=(0 thof A)")

(assume "pFalse")
(inst-with-to "pProp" 'right "Hyp1")
(inst-with-to "Hyp1" "pFalse" "NegExHyp")
(drop "pProp")
(assume "ex A Legal A(i::X)B")
(use "NegExHyp")
(drop "NegExHyp" "Hyp1" "pFalse")
(by-assume-with "ex A Legal A(i::X)B" "A" "Legal A(i::X)B")
(ex-intro "A")
(split)
(use "Legal A(i::X)B")
(use "Truth")
;; Proof finished.
(save "BinPackIf")

(define eterm (proof-to-extracted-term (theorem-name-to-proof "BinPackIf")))
(animate "NatSuccPredCases")
(animate "If")
(add-var-name "pA" (py "boole@@list nat"))
(add-var-name "f" (py "list nat=>boole@@list nat"))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [A]
;;  (Rec list nat=>list nat=>boole@@list nat)A([A0]True@(Nil nat))
;;  ([n,A0,f,A1]
;;    (Rec nat=>boole@@list nat)Lh A1(False@(Nil nat))
;;    ([n0,pA]
;;      [if (Lh A1--n0)
;;        pA
;;        ([n1]
;;         [if (n<=(Pred(Lh A1--n0)thof A1))
;;           [if (left(f(DecrAux A1(Pred(Lh A1--n0))n 0)))
;;            (True@Pred(Lh A1--n0)::right(f(DecrAux A1(Pred(Lh A1--n0))n 0)))
;;            [if (left pA) (True@right pA) (False@(Nil nat))]]
;;           [if (left pA) (True@right pA) (False@(Nil nat))]])]))

;; Experiment 1
;; ============

(define proof (theorem-name-to-proof "BinPackIf"))
(define ij1j2
  (expand-thm (mk-proof-in-elim-form proof (pt "i:") (pt "j1::j2:"))
	      "NatSuccPredCases"))

(animate "If")
;; (time (tag (nbe-normalize-proof-without-eta ij1j2)))
;; .8 s
(define n-ij1j2 (nbe-normalize-proof-without-eta ij1j2))
;; (proof-to-expr n-ij1j2)
;; 7 pages
;; (cdp n-ij1j2)

(define rem-n-ij1j2 (remove-predecided-if-theorems n-ij1j2))
;; (proof-to-expr rem-n-ij1j2)
;; 2 pages
;; (cdp rem-n-ij1j2)

;; (proof-in-normal-form? rem-n-ij1j2)
;; t
;; (length (proof-to-permutative-redexes rem-n-ij1j2))
;; 2

;; (time (tag (normalize-proof-pi rem-n-ij1j2)))
;; 220 ms
(define perm-rem-n-ij1j2 (normalize-proof-pi rem-n-ij1j2))

;; (proof-to-expr perm-rem-n-ij1j2)
;; 6 pages

;; (proof-in-normal-form? perm-rem-n-ij1j2)
;; #t
;; However, perm-rem-n-ij1j2 contains ExElim/ExIntro redexes.

;; (time (tag (nbe-normalize-proof-without-eta perm-rem-n-ij1j2)))
;; 318 ms

(define n-perm-rem-n-ij1j2
  (nbe-normalize-proof-without-eta perm-rem-n-ij1j2))

;; (proof-to-expr n-perm-rem-n-ij1j2)
;; 3 pages

;; (time (tag (remove-predecided-if-theorems n-perm-rem-n-ij1j2)))
;; 2 s

(define rem-n-perm-rem-n-ij1j2
  (remove-predecided-if-theorems n-perm-rem-n-ij1j2))

;; (proof-to-expr rem-n-perm-rem-n-ij1j2)
;; 1.5 pages

;; (cdp rem-n-perm-rem-n-ij1j2)
(pp (nt (proof-to-extracted-term rem-n-perm-rem-n-ij1j2)))

;; [if (i<=j1) (True@0:) [if (i<=j2) (True@1:) (False@(Nil nat))]]

;; Experiment 2
;; ============

(define i1i2jj
  (expand-thm (mk-proof-in-elim-form proof (pt "i1::i2:") (pt "j::j:"))
	      "NatSuccPredCases"))
;; (time (tag (nbe-normalize-proof-without-eta i1i2jj)))
;; 4 s
(define n-i1i2jj (nbe-normalize-proof-without-eta i1i2jj))
;; (proof-to-expr n-i1i2jj)
;; 55 pages

;; (time (tag (remove-predecided-if-theorems n-i1i2jj)))
;; 1.4 s
(define rem-n-i1i2jj (remove-predecided-if-theorems n-i1i2jj))
;; (proof-to-expr rem-n-i1i2jj)
;; 10 pages
;; (cdp rem-n-i1i2jj)

;; (proof-in-normal-form? rem-n-i1i2jj)
;; #f
;; (length (proof-to-permutative-redexes rem-n-i1i2jj))
;; 7

;; (time (tag (normalize-proof-pi rem-n-i1i2jj)))
;; 5 s
(define perm-rem-n-i1i2jj (normalize-proof-pi rem-n-i1i2jj))

;; (proof-to-expr perm-rem-n-i1i2jj)
;; many pages

;; However, perm-rem-n-i1i2jj contains ExElim/ExIntro redexes.

;; (time (tag (nbe-normalize-proof-without-eta perm-rem-n-i1i2jj)))
;; 8 s

(define n-perm-rem-n-i1i2jj
  (nbe-normalize-proof-without-eta perm-rem-n-i1i2jj))

;; (proof-to-expr n-perm-rem-n-i1i2jj)
;; Many pages

;; (time (tag (remove-predecided-if-theorems n-perm-rem-n-i1i2jj)))
;; 4 s

(define rem-n-perm-rem-n-i1i2jj
  (remove-predecided-if-theorems n-perm-rem-n-i1i2jj))

;; (proof-to-expr rem-n-perm-rem-n-i1i2jj)
;; 5.5 pages

;; (cdp rem-n-perm-rem-n-i1i2jj)
(pp (nt (proof-to-extracted-term rem-n-perm-rem-n-i1i2jj)))

;; [if (i1<=j)
;;   [if (i2<=j--i1) (True@0::0:) [if (i2<=j) (True@0::1:) (False@(Nil nat))]]
;;   (False@(Nil nat))]

;; Experiment 2 with assumption i2<=j
;; ==================================

(define s-i1i2jj
  (let ((avar (formula-to-new-avar (pf "i2<=j"))))
    (expand-thm
     (make-proof-in-imp-intro-form
      avar (mk-proof-in-elim-form proof (pt "i1::i2:") (pt "j::j:")))
     "NatSuccPredCases")))

;; (pp (proof-to-formula s-i1i2jj))

(define n-s-i1i2jj (nbe-normalize-proof-without-eta s-i1i2jj))
(define rem-n-s-i1i2jj (remove-predecided-if-theorems n-s-i1i2jj))
(define perm-rem-n-s-i1i2jj (normalize-proof-pi rem-n-s-i1i2jj))
(define n-perm-rem-n-s-i1i2jj
  (nbe-normalize-proof-without-eta perm-rem-n-s-i1i2jj))
(define rem-n-perm-rem-n-s-i1i2jj
  (remove-predecided-if-theorems n-perm-rem-n-s-i1i2jj))
(define simp-rem-n-perm-rem-n-s-i1i2jj
  (normalize-proof-simp n-perm-rem-n-s-i1i2jj))
(pp (nt (proof-to-extracted-term simp-rem-n-perm-rem-n-s-i1i2jj)))
;; [if (i1<=j) (True@0::1:) (False@(Nil nat))]

;; This is an extensionally different program: it never returns 0::0:
;; Program transformation cannot do this.
