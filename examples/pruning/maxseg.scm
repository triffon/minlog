;; 2014-10-16.  maxseg.scm.  Based on 

;; @Phdthesis{Goad80,
;; Author = "Christopher Alan Goad",
;; Title = "Computational uses of the manipulation 
;;          of formal proofs",
;; School = "Stanford University",
;; Note = "Department of Computer Science Report No. STAN--CS--80--819",
;; Month = "August",
;; Year = 1980}

;; @Article{Constable85,
;;   author = 	 "Joseph L. Bates and Robert L. Constable",
;;   title = 	 "Proofs as Programs",
;;   journal =	 "ACM Transactions on Programming Languages and Systems",
;;   year =	 "1985",
;;   volume =	 "7",
;;   number =	 "1",
;;   pages =	 "113--136",
;;   month =	 "January"}

;; We prove the existence of maximal segments, first generally, then
;; (by transforming the general proof) assuming monotonicity of seg.

;; MaxSeg: TransReflLinLeq -> ExMaxSeg
;; MaxSegMon: TransReflLinLeq -> SegMon -> ExMaxSeg

;; The general proof is by induction on the length n of the given
;; sequence, and needs to consider end segments as well.  It is
;; possible to split it by first assuming the step proposition for end
;; segments and then proving the latter separately.

;; MaxSegRel: TransReflLinLeq -> EndSegStep -> ExMaxSeg

;; In the general case, the proof of the step proposition for end
;; segments cannot make use of the step hypothesis, but has to use an
;; auxiliary induction instead.  This is on m (<=n), and considers end
;; segments seg l(n+1) with l<=m only (picking a maximal one from
;; these)

;; EndSegStep: TransReflLinLeq -> ExMaxEndSeg-n -> ExMaxEndSeg-n+1

;; In the special case, from monotonicity of seg and the step
;; hypothesis one obtains a maximal end segment by cases.  There is no
;; need for an auxiliary induction.

;; EndSegStepMon: TransReflLinLeq -> SegMon -> ExMaxEndSeg-n -> ExMaxEndSeg-n+1

;; A detailed description of the argument is in papers/akad96/maxseg:

;; @Article{Schwichtenberg97,
;;   author = 	 {Helmut Schwichtenberg},
;;   title = 	 {{Programmentwicklung durch Beweistransformation:
;;                   Das Maximalsegmentproblem}},
;;   journal = 	 {Sitzungsber.\ d.\ Bayer.\ Akad.\ d.\ Wiss., Math.-Nat.\ Kl.},
;;   year = 	 {1997},
;;   pages =	 {8*--12*}}

;; The code below is based on lectures/ws03/maxseg.scm.

;; (load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(set! COMMENT-FLAG #t)

(add-var-name "x" "y" "z" (py "alpha"))
(add-var-name "leq" (py "alpha=>alpha=>boole"))
(add-var-name "seg" (py "nat=>nat=>alpha"))
(add-var-name "i" "j" (py "nat"))

(add-token
 "<<="
 'rel-op
 (lambda (x y)
   (mk-term-in-app-form (pt "leq") x y)))

(add-display
 (py "boole")
 (lambda (x)
   (let ((op (term-in-app-form-to-final-op x))
	 (args (term-in-app-form-to-args x)))
     (if (equal? op (pt "leq"))
	 (let ((arg1 (car args))
	       (arg2 (cadr args)))
	   (list
	    'rel-op "<<="
	    (term-to-token-tree arg1)
	    (term-to-token-tree arg2)))
	 #f))))

;; (display-pconst "NatLe")

(add-pvar-name "R" (make-arity (py "nat") (py "nat")))

;; We prove the general proposition MaxSegRel, relative to an assumption
;; u expressing the step for end segments.

;; MaxSeqRel
(set-goal "all leq,seg(
 all x,y,z(x<<=y -> y<<=z -> x<<=z) -> 
 all x x<<=x -> 
 all x,y((x<<=y -> F) -> y<<=x) -> 
 all n(
  ex j(j<=n & all j1(j1<=n -> seg j1 n<<=seg j n)) -> 
  ex j(j<=n+1 & all j1(j1<=n+1 -> seg j1(n+1)<<=seg j(n+1)))) -> 
 all n 
  ex i,j,k(
   i<=k & 
   j<=n & 
   k<=n & 
   all i1,k1(i1<=k1 -> k1<=n -> seg i1 k1<<=seg i k) & 
   all j1(j1<=n -> seg j1 n<<=seg j n)))")
(assume "leq" "seg" "LeqTrans" "LeqRefl" "LeqLin" "u")
(ind)
;; Base
(ex-intro (pt "0"))
(ex-intro (pt "0"))
(ex-intro (pt "0"))
(msplit)
;; all j(j<=0 -> seg j 0<<=seg 0 0)
(assume "j")
(ng)
(assume "j=0")
(simp "j=0")
(use "LeqRefl")
;; all i,k(i<=k -> k<=0 -> seg i k<<=seg 0 0)
(assume "i" "k" "i<=k")
(ng)
(assume "k=0")
(simp "k=0")
(simphyp-with-to "i<=k" "k=0" "i<=0")
(ng "i<=0")
(simp "i<=0")
(use "LeqRefl")
(use "Truth")
(use "Truth")
(use "Truth")
;; Step
(assume "n" "IHn")
(by-assume-with "IHn" "i" "iProp")
(by-assume-with "iProp" "j" "jProp")
(by-assume-with "jProp" "k" "IH")
(cut "ex j(j<=n+1 & all j1(j1<=n+1 -> seg j1(n+1)<<=seg j(n+1)))")
(use "Id")
(assume "ExEndSegStep")
(by-assume-with "ExEndSegStep" "j1" "j1Prop")
;; Now we can define i1 and k1
(cases (pt "seg j1(n+1)<<=seg i k"))
;; Case seg j1(n+1)<<=seg i k
(assume "CaseHyp")
(ex-intro (pt "i"))
(ex-intro (pt "j1"))
(ex-intro (pt "k"))
(msplit)
;; all j(j<=Succ n -> seg j(Succ n)<<=seg j1(Succ n))
(use "j1Prop")
;; all i0,k0(i0<=k0 -> k0<=Succ n -> seg i0 k0<<=seg i k)
(assume "i1" "k1" "i1<=k1" "k1<=n+1")
(use "NatLeCases" (pt "Succ n") (pt "k1"))
(use "k1<=n+1")
(assume "k1<n+1")
(use "IH")
(use "i1<=k1")
(use "NatLtSuccToLe")
(use "k1<n+1")
(assume "k1=n+1")
(use "LeqTrans" (pt "seg j1(n+1)"))
(simp "k1=n+1")
(use "j1Prop")
(ng)
(simp "<-" "k1=n+1")
(use "i1<=k1")
(use "CaseHyp")
;; k<=Succ n"
(use "NatLeTrans" (pt "n"))
(use "IH")
(use "Truth")
;; j1<=Succ n
(use "j1Prop")
;; i<=k
(use "IH")
;; Case (seg j1(n+1)<<=seg i k -> F).  Then the maximal end segment is
;; the maximal segment.  Take i1=j1 and k1=n+1.
(assume "CaseHyp")
(ex-intro "j1")
(ex-intro "j1")
(ex-intro "n+1")
(msplit)
;; all j(j<=Succ n -> seg j(Succ n)<<=seg j1(Succ n))
(use "j1Prop")
;; all i,k(i<=k -> k<=Succ n -> seg i k<<=seg j1(n+1))
(assume "i1" "k1" "i1<=k1" "k1<=n+1")
(use "NatLeCases" (pt "Succ n") (pt "k1"))
(use "k1<=n+1")
(assume "k1<n+1")
(use "LeqTrans" (pt "seg i k"))
(use "IH")
(use "i1<=k1")
(use "NatLtSuccToLe")
(use "k1<n+1")
(use "LeqLin")
(use "CaseHyp")
(assume "k1=n+1")
(simp "k1=n+1")
(use "j1Prop")
(use "NatLeTrans" (pt "k1"))
(use "i1<=k1")
(use "k1<=n+1")
(use "Truth")
(use "j1Prop")
(use "j1Prop")
;; ex j(j<=n+1 & all j0(j0<=n+1 -> seg j0(n+1)<<=seg j(n+1)))
(use "u")
(ex-intro "j")
(split)
(use "IH")
(use "IH")
;; Proof finished.
(save "MaxSegRel")

(define eterm (proof-to-extracted-term (theorem-name-to-proof "MaxSegRel")))
(add-var-name "ijk" (py "nat@@nat@@nat"))
(add-var-name "step" (py "nat=>nat=>nat"))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [leq,seg,step,n]
;;  (Rec nat=>nat@@nat@@nat)n(0@0@0)
;;  ([n0,ijk]
;;    [let n1
;;      (step n0 left right ijk)
;;      ([if (seg n1(Succ n0)<<=seg left ijk right right ijk) (left ijk) n1]@
;;      n1@
;;      [if (seg n1(Succ n0)<<=seg left ijk right right ijk)
;;        (right right ijk)
;;        (Succ n0)])])

;; EndSeg
(set-goal "all leq,seg(
 all x,y,z(x<<=y -> y<<=z -> x<<=z) -> 
 all x x<<=x -> 
 all x,y((x<<=y -> F) -> y<<=x) -> 
 all n,m(m<=n ->
      ex j2(j2<=m & all j1(j1<=m -> seg j1 n<<=seg j2 n))))")
(assume "leq" "seg" "LeqTrans" "LeqRefl" "LeqLin" "n")
(ind)
;; Base
(assume "Useless")
(ex-intro (pt "0"))
(split)
(use "Truth")
(assume "j1")
(ng)
(assume "j1=0")
(simp "j1=0")
(use "LeqRefl")
;; Step
(assume "m" "IHm" "m+1<=n")
(assert "ex j(j<=m & all j0(j0<=m -> seg j0 n<<=seg j n))")
 (use "IHm")
 (use "NatLeTrans" (pt "Succ m"))
 (use "Truth")
 (use "m+1<=n")
(assume "ExHyp")
(by-assume-with "ExHyp" "j" "jProp")
(cases (pt "seg j n<<=seg(m+1)n"))
;; Case seg j n<<=seg(m+1)n
(assume "CaseHyp")
(ex-intro "Succ m")
(split)
(use "Truth")
(assume "j1" "j1<=m+1")
(use "NatLeCases" (pt "Succ m") (pt "j1"))
(use "j1<=m+1")
(assume "j1<m+1")
(use "LeqTrans" (pt "seg j n"))
(use "jProp")
(use "NatLtSuccToLe")
(use "j1<m+1")
(use "CaseHyp")
(assume "j1=m+1")
(simp "j1=m+1")
(use "LeqRefl")
;; Case seg j n<<=seg(m+1)n -> F
(assume "CaseHyp")
(ex-intro (pt "j"))
(split)
(use "NatLeTrans" (pt "m"))
(use "jProp")
(use "Truth")
(assume "j1" "j1<=m+1")
(use "NatLeCases" (pt "Succ m") (pt "j1"))
(use "j1<=m+1")
(assume "j1<m+1")
(use "jProp")
(use "NatLtSuccToLe")
(use "j1<m+1")
(assume "j1=m+1")
(simp "j1=m+1")
(use "LeqLin")
(use "CaseHyp")
;; Proof finished.
(save "EndSeg")

(define eterm (proof-to-extracted-term (theorem-name-to-proof "EndSeg")))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [leq,seg,n,n0]
;;  (Rec nat=>nat)n0 0([n1,n2][if (seg n2 n<<=seg(Succ n1)n) (Succ n1) n2])

;; We prove the general proposition MaxSeg, using the lemma EndSeg.

;; MaxSeg
(set-goal "all leq,seg(
 all x,y,z(x<<=y -> y<<=z -> x<<=z) -> 
 all x x<<=x -> 
 all x,y((x<<=y -> F) -> y<<=x) -> 
 all n 
  ex i,j,k(
   i<=k & 
   j<=n & 
   k<=n & 
   all i1,k1(i1<=k1 -> k1<=n -> seg i1 k1<<=seg i k) & 
   all j1(j1<=n -> seg j1 n<<=seg j n)))") 
(assume "leq" "seg" "LeqTrans" "LeqRefl" "LeqLin")
(use "MaxSegRel")
(use "LeqTrans")
(use "LeqRefl")
(use "LeqLin")
(assume "n" "Useless")
(use "EndSeg")
(use "LeqTrans")
(use "LeqRefl")
(use "LeqLin")
(use "Truth")
;; Proof finished.
(save "MaxSeg")
;; (remove-theorem "MaxSeg")

(define eterm (proof-to-extracted-term (theorem-name-to-proof "MaxSeg")))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [leq,seg]
;;  (cMaxSegRel alpha)leq seg([n,n0](cEndSeg alpha)leq seg(Succ n)(Succ n))

(animate "MaxSegRel")
(animate "EndSeg")
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [leq,seg,n]
;;  (Rec nat=>nat@@nat@@nat)n(0@0@0)
;;  ([n0,ijk]
;;    [let n1
;;      [if (seg
;;           ((Rec nat=>nat)n0 0
;;            ([n1,n2]
;;              [if (seg n2(Succ n0)<<=seg(Succ n1)(Succ n0)) (Succ n1) n2]))
;;           (Succ n0)<<=
;;           seg(Succ n0)(Succ n0))
;;       (Succ n0)
;;       ((Rec nat=>nat)n0 0
;;       ([n1,n2][if (seg n2(Succ n0)<<=seg(Succ n1)(Succ n0)) (Succ n1) n2]))]
;;      ([if (seg n1(Succ n0)<<=seg left ijk right right ijk) (left ijk) n1]@
;;      n1@
;;      [if (seg n1(Succ n0)<<=seg left ijk right right ijk)
;;        (right right ijk)
;;        (Succ n0)])])

;; This is a quadratic algorithm

(deanimate "MaxSegRel")
(deanimate "EndSeg")

;; We prove EndSegStepMon, assuming the monotonicity of seg.

;; EndSegStepMon
(set-goal "all leq,seg(
 all x,y,z(x<<=y -> y<<=z -> x<<=z) -> 
 all x x<<=x -> 
 all x,y((x<<=y -> F) -> y<<=x) -> 
 all i,j,k(seg i k<<=seg j k -> seg i(k+1)<<=seg j(k+1)) -> 
 all n(
  ex j(j<=n & all j1(j1<=n -> seg j1 n<<=seg j n)) -> 
  ex j(j<=n+1 & all j1(j1<=n+1 -> seg j1(n+1)<<=seg j(n+1)))))")
(assume "leq" "seg" "LeqTrans" "LeqRefl" "LeqLin" "SegMon" "n" "EndSeg-n")
(by-assume-with "EndSeg-n" "j" "EndSeg-j")
(inst-with-to "EndSeg-j" 'left "j<=n")
(inst-with-to "EndSeg-j" 'right "IHj")
(drop "EndSeg-j")
(cases (pt "seg j(n+1)<<=seg(n+1)(n+1)"))

;; Case seg j(n+1)<<=seg(n+1)(n+1)
(assume "CaseHyp")
(ex-intro (pt "n+1"))
(split)
(use "Truth")
(assume "j1" "j1<=n+1")
(use "NatLeCases" (pt "Succ n") (pt "j1"))
(use "j1<=n+1")
(assume "j1<=n")
(use "LeqTrans" (pt "seg j(n+1)"))
(use "SegMon")
(use "IHj")
(use "NatLtSuccToLe")
(use "j1<=n")
(use "CaseHyp")
(assume "j1=n+1")
(simp "j1=n+1")
(use "LeqRefl")

;; Case seg j(n+1)<<=seg(n+1)(n+1) -> F
(assume "CaseHyp")
(ex-intro (pt "j"))
(split)
(use "NatLeTrans" (pt "n"))
(use "j<=n")
(use "Truth")
(assume "j1" "j1<=n+1")
(use "NatLeCases" (pt "Succ n") (pt "j1"))
(use "j1<=n+1")
(assume "j1<=n")
(use "SegMon")
(use "IHj")
(use "NatLtSuccToLe")
(use "j1<=n")
(assume "j1=n+1")
(use "LeqLin")
(simp "j1=n+1")
(use "CaseHyp")
;; Proof finished.
(save "EndSegStepMon")

(define eterm (proof-to-extracted-term (theorem-name-to-proof "EndSegStepMon")))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [leq,seg,n,n0][if (seg n0(Succ n)<<=seg(Succ n)(Succ n)) (Succ n) n0]

;; MaxSegMon
(set-goal "all leq,seg(
 all x,y,z(x<<=y -> y<<=z -> x<<=z) -> 
 all x x<<=x -> 
 all x,y((x<<=y -> F) -> y<<=x) -> 
 all i,j,k(seg i k<<=seg j k -> seg i(k+1)<<=seg j(k+1)) -> 
 all n 
  ex i,j,k(
   i<=k & 
   j<=n & 
   k<=n & 
   all i1,k1(i1<=k1 -> k1<=n -> seg i1 k1<<=seg i k) & 
   all j1(j1<=n -> seg j1 n<<=seg j n)))") 
(assume "leq" "seg" "LeqTrans" "LeqRefl" "LeqLin" "SegMon")
(use "MaxSegRel")
(use "LeqTrans")
(use "LeqRefl")
(use "LeqLin")
(use "EndSegStepMon")
(use "LeqTrans")
(use "LeqRefl")
(use "LeqLin")
(use "SegMon")
;; Proof finished.
(save "MaxSegMon")

(define eterm (proof-to-extracted-term (theorem-name-to-proof "MaxSegMon")))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [leq,seg](cMaxSegRel alpha)leq seg((cEndSegStepMon alpha)leq seg)

(animate "MaxSegRel")
(animate "EndSegStepMon")

(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [leq,seg,n]
;;  (Rec nat=>nat@@nat@@nat)n(0@0@0)
;;  ([n0,ijk]
;;    [let n1
;;      [if (seg left right ijk(Succ n0)<<=seg(Succ n0)(Succ n0))
;;       (Succ n0)
;;       (left right ijk)]
;;      ([if (seg n1(Succ n0)<<=seg left ijk right right ijk) (left ijk) n1]@
;;      n1@
;;      [if (seg n1(Succ n0)<<=seg left ijk right right ijk)
;;        (right right ijk)
;;        (Succ n0)])])

;; This is a linear algorithm
