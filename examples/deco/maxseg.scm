;; 2014-10-16.  maxseg.scm.  Based on slides/chalmers11demo.scm.  

;; Maximal scoring segment
;; =======================

;; (load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(set! COMMENT-FLAG #t)

(add-var-name "x" "y" "z" (py "alpha"))
(add-var-name "le" (py "alpha=>alpha=>boole"))
(add-var-name "seg" (py "nat=>nat=>alpha"))
(add-var-name "i" "j" (py "nat"))

;; 1.  Maximal end segment
;; =======================

;; We prove the existence of a maximal end segment for n+1, by
;; induction on an auxiliary variable m.

;; L
(set-goal
 "all le,seg(
 all x,y,z(le x y -> le y z -> le x z) -> 
 all x le x x -> 
 all x,y((le x y -> F) -> le y x) -> 
 all n,m(
 m<=n+1 -> ex j2(j2<=n+1 & all j1(j1<=m -> le(seg j1(n+1))(seg j2(n+1))))))")
(assume "le" "seg" "leTrans" "leRefl" "leLin" "n")
(ind)

;; Base
(assume "0<=n+1")
(ex-intro "0")
(split)
(use "Truth")
(cases)
(assume "Useless")
(use "leRefl")
(assume "n1")
(ng)
(use "Efq")

;; Step
(assume "m" "IHm" "Succ m<=n+1")
(assert "ex j2(j2<=n+1 & all j1(j1<=m -> le(seg j1(n+1))(seg j2(n+1))))")
 (use "IHm")
 (use "NatLeTrans" (pt "Succ m"))
 (use "Truth")
 (use "Succ m<=n+1")
(assume "ExHyp")
(by-assume-with "ExHyp" "j2" "j2Hyp")
;; Have j2 with j2Hyp:j2<=n+1 & all j1(j1<=m -> le(seg j1(n+1))(seg j2(n+1)))
(cases (pt "le(seg j2(n+1))(seg(m+1)(n+1))"))
(assume "le(seg j2(n+1))(seg(m+1)(n+1))")

;; In case "le(seg j2(n+1))(seg(m+1)(n+1))" take the new j2 := m+1
(ex-intro "m+1")
(split)
(use "Succ m<=n+1")
(assume "j1" "j1<=Succ m")
(use "NatLeCases" (pt "Succ m") (pt "j1"))
(use "j1<=Succ m")

(assume "j1<Succ m")
(use "leTrans" (pt "seg j2(n+1)"))
(use "j2Hyp")
(use "NatLtSuccToLe")
(use "j1<Succ m")
(use "le(seg j2(n+1))(seg(m+1)(n+1))")

(assume "j1=Succ m")
(simp "j1=Succ m")
(use "leRefl")

(assume "le(seg j2(n+1))(seg(m+1)(n+1)) -> F")
;; In case "le(seg j2(n+1))(seg(m+1)(n+1)) -> F" take the old j2
(ex-intro "j2")
(split)
(use "j2Hyp")
(assume "j1" "j1<=Succ m")
(use "NatLeCases" (pt "Succ m") (pt "j1"))
(use "j1<=Succ m")

(assume "j1<Succ m")
(use "j2Hyp")
(use "NatLtSuccToLe")
(use "j1<Succ m")

(assume "j1=Succ m")
(simp "j1=Succ m")
(use "leLin")
(use "le(seg j2(n+1))(seg(m+1)(n+1)) -> F")
;; Proof finished.
(save "L")

;; (cdp "L")
(define eterm (proof-to-extracted-term (theorem-name-to-proof "L")))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [le,seg,n,n0]
;;  (Rec nat=>nat)n0 0
;;  ([n1,n2][if (le(seg n2(Succ n))(seg(Succ n1)(Succ n))) (Succ n1) n2])

;; 2.  Alternative proof of maximal end segment
;; ============================================

;; We give an alternative proof of the existence of a maximal end
;; segment for n+1, this time assuming monotonicity and the existence
;; of a maximal end segment for n.

;; LMon
(set-goal
 "all le,seg(
 all x,y,z(le x y -> le y z -> le x z) -> 
 all x le x x -> 
 all x,y((le x y -> F) -> le y x) -> 
 all i,j,k(le(seg i k)(seg j k) -> le(seg i(k+1))(seg j(k+1))) ->
 all n(
 ex j(j<=n & all j1(j1<=n -> le(seg j1 n)(seg j n))) ->
 allnc m(
 m<=n+1 -> ex j2(j2<=n+1 & all j1(j1<=m -> le(seg j1(n+1))(seg j2(n+1)))))))")
(assume "le" "seg" "leTrans" "leRefl" "leLin" "Mon" "n" "ESn" "m" "m<=n+1")
(by-assume-with "ESn" "j" "ih")
;; Distinguish cases on le(seg j(n+1))(seg(n+1)(n+1))
(cases (pt "le(seg j(n+1))(seg(n+1)(n+1))"))

;; In case "le(seg j(n+1))(seg(n+1)(n+1))" take the new j2 to be n+1
(assume "le(seg j(n+1))(seg(n+1)(n+1))")
(ex-intro "n+1")
(split)
(use "Truth")
(assume "j1" "j1<=m")
(use "NatLeCases" (pt "Succ n") (pt "j1"))
(use "NatLeTrans" (pt "m"))
(use "j1<=m")
(use "m<=n+1")
(assume "j1<n+1")
(use "leTrans" (pt "seg j(n+1)"))
(use "Mon")
(use "ih")
(use "NatLtSuccToLe")
(use "j1<n+1")
(use "le(seg j(n+1))(seg(n+1)(n+1))")
(assume "j1=n+1")
(simp "j1=n+1")
(use "leRefl")

;; In case "le(seg j(n+1))(seg(n+1)(n+1)) -> F" take the old j
(assume "le(seg j(n+1))(seg(n+1)(n+1)) -> F")
(ex-intro "j")
(split)
(use "NatLeTrans" (pt "n"))
(use "ih")
(use "Truth")
(assume "j1" "j1<=m")
(use "NatLeCases" (pt "Succ n") (pt "j1"))
(use "NatLeTrans" (pt "m"))
(use "j1<=m")
(use "m<=n+1")
(assume "j1<n+1")
(use "Mon")
(use "ih")
(use "NatLtSuccToLe")
(use "j1<n+1")
(assume "j1=n+1")
(simp "j1=n+1")
(use "leLin")
(use "le(seg j(n+1))(seg(n+1)(n+1)) -> F")
;; Proof finished.
(save "LMon")

;; (cdp "LMon")
(define eterm (proof-to-extracted-term (theorem-name-to-proof "LMon")))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [le,seg,n,n0][if (le(seg n0(Succ n))(seg(Succ n)(Succ n))) (Succ n) n0]

;; 3.  Maximal segment
;; ===================

;; We prove the existence of a maximal segment, using the auxiliary
;; lemma L proved by induction.  To get the induction through, we need
;; to prove simultaneously the existence of a maximal end segment.  

;; To prepare for later application of decorate w.r.t. "L" and "LMon":
;; where "L" is used we want to have "Mon" as well as "ESn" among the
;; available avars.  Hence we add the (for L) unnecessary hypothesis
;; "Mon".  To make "ESn" available we assert it at an appropriate
;; place.

;; MaxSegMon
(set-goal
 "all le,seg(
 all x,y,z(le x y -> le y z -> le x z) -> 
 all x le x x -> 
 all x,y((le x y -> F) -> le y x) -> 
 all i,j,k(le(seg i k)(seg j k) -> le(seg i(k+1))(seg j(k+1))) ->
 all n(
  ex i,j,k(
   i<=k & j<=n & k<=n & all i1,k1(i1<=k1 -> k1<=n -> le(seg i1 k1)(seg i k)) & 
   all j1(j1<=n -> le(seg j1 n)(seg j n)))))")
(assume "le" "seg" "leTrans" "leRefl" "leLin" "Mon")
(ind)

;; Base case
(ex-intro "0")
(ex-intro "0")
(ex-intro "0")
(msplit)
;; all j(j<=0 -> le(seg j 0)(seg 0 0))
(ng)
(assume "j1" "j1=0")
(simp "j1=0")
(use "leRefl")
;; all i,k(i<=k -> k<=0 -> le(seg i k)(seg 0 0))
(ng)
(assume "i1" "k1" "i1<=k1" "k1=0")
(simp "k1=0")
(simphyp-with-to "i1<=k1" "k1=0" "i1<=0")
(ng "i1<=0")
(simp "i1<=0")
(use "leRefl")
(use "Truth")
(use "Truth")
(use "Truth")

;; Step case
(assume "n" "IH")
(by-assume-with "IH" "i" "iHyp")
(by-assume-with "iHyp" "j" "jHyp")
(by-assume-with "jHyp" "k" "ih")
;; We now assert "ESn"
(assert "ex j(j<=n & all j1(j1<=n -> le(seg j1 n)(seg j n)))")
 (ex-intro "j")
 (split)
 (use "ih")
 (use "ih")
(assume "ESn")

;; We first prove the existence of a maximal end segment for n+1.
(assert "ex j2(j2<=n+1 & all j1(j1<=n+1 -> le(seg j1(n+1))(seg j2(n+1))))")
 (use "L")
 (use "leTrans")
 (use "leRefl")
 (use "leLin")
 (use "Truth")
;; We now have the asserted existence of a maximal end segment for n+1
(assume "ExMaxEndSeg")
(by-assume-with "ExMaxEndSeg" "j2" "j2MaxEndSeq")

;; Now compare the maximal segment for n with the maximal endsegment for n+1
(cases (pt "le(seg i k)(seg j2(n+1))"))

;; In case "le(seg i k)(seg j2(n+1))" take the new i,k to be j2,n+1
(assume "le(seg i k)(seg j2(n+1))")
(ex-intro "j2")
(ex-intro "j2")
(ex-intro "n+1")
(msplit)
(use "j2MaxEndSeq")
(assume "i1" "k1" "i1<=k1" "k1<=n+1")
(use "NatLeCases" (pt "Succ n") (pt "k1"))
(use "k1<=n+1")
(assume "k1<n+1")
(use "leTrans" (pt "seg i k"))
(use "ih")
(use "i1<=k1")
(use "NatLtSuccToLe")
(use "k1<n+1")
(use "le(seg i k)(seg j2(n+1))")
;; k1=Succ n -> le(seg i1 k1)(seg j2(n+1))
(assume "k1=n+1")
(simp "k1=n+1")
(use "j2MaxEndSeq")
(use "NatLeTrans" (pt "k1"))
(use "i1<=k1")
(use "k1<=n+1")
(use "Truth")
(use "j2MaxEndSeq")
(use "j2MaxEndSeq")

;; In case "le(seg i k)(seg j2(n+1)) -> F" take the old i,k
(assume "le(seg i k)(seg j2(n+1)) -> F")
(ex-intro "i")
(ex-intro "j2")
(ex-intro "k")
(msplit)
;; all j(j<=Succ n -> le(seg j(Succ n))(seg j2(Succ n)))
(use "j2MaxEndSeq")
;;all i0,k0(i0<=k0 -> k0<=Succ n -> le(seg i0 k0)(seg i k))
(assume "i1" "k1" "i1<=k1" "k1<=n+1")
(use "NatLeCases" (pt "Succ n") (pt "k1"))
(use "k1<=n+1")
(assume "k1<n+1")
(use "ih")
(use "i1<=k1")
(use "NatLtSuccToLe")
(use "k1<n+1")
(assume "k1=n+1")
(simp "k1=n+1")
(use "leTrans" (pt "seg j2(n+1)"))
(use "j2MaxEndSeq")
(use "NatLeTrans" (pt "k1"))
(use "i1<=k1")
(use "k1<=n+1")
(use "leLin")
(use "le(seg i k)(seg j2(n+1)) -> F")
(use "NatLeTrans" (pt "n"))
(use "ih")
(use "Truth")
(use "j2MaxEndSeq")
(use "ih")
;; Proof finished.
(save "MaxSegMon")

;; (cdp (theorem-name-to-proof "MaxSegMon"))
(define eterm (proof-to-extracted-term (theorem-name-to-proof "MaxSegMon")))
(add-var-name "ijk" (py "nat@@nat@@nat"))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [le,seg,n]
;;  (Rec nat=>nat@@nat@@nat)n(0@0@0)
;;  ([n0,ijk]
;;    [if (le(seg left ijk right right ijk)
;;          (seg((cL alpha)le seg n0(Succ n0))(Succ n0)))
;;      ((cL alpha)le seg n0(Succ n0))
;;      (left ijk)]@
;;    (cL alpha)le seg n0(Succ n0)@
;;    [if (le(seg left ijk right right ijk)
;;          (seg((cL alpha)le seg n0(Succ n0))(Succ n0)))
;;      (Succ n0)
;;      (right right ijk)])

;; Recall

(pp (rename-variables (nt
	 (proof-to-extracted-term (theorem-name-to-proof "L")))))

;; [le,seg,n,n0]
;;  (Rec nat=>nat)n0 0
;;  ([n1,n2][if (le(seg n2(Succ n))(seg(Succ n1)(Succ n))) (Succ n1) n2])

;; The two nested recursions give a quadratic algorithm.

;; 4. Extraction after decoration
;; ==============================

(define decproof (decorate (theorem-name-to-proof "MaxSegMon") "L" "LMon"))
;; (cdp decproof)

(pp (rename-variables (nt (proof-to-extracted-term decproof))))

;; [le,seg,n]
;;  (Rec nat=>nat@@nat@@nat)n(0@0@0)
;;  ([n0,ijk]
;;    [if (le(seg left ijk right right ijk)
;;          (seg((cLMon alpha)le seg n0 left right ijk)(Succ n0)))
;;      ((cLMon alpha)le seg n0 left right ijk)
;;      (left ijk)]@
;;    (cLMon alpha)le seg n0 left right ijk@
;;    [if (le(seg left ijk right right ijk)
;;          (seg((cLMon alpha)le seg n0 left right ijk)(Succ n0)))
;;      (Succ n0)
;;      (right right ijk)])

;; Recall

(pp (rename-variables
     (nt (proof-to-extracted-term (theorem-name-to-proof "LMon")))))

;; [le,seg,n,n0][if (le(seg n0(Succ n))(seg(Succ n)(Succ n))) (Succ n) n0]

;; Hence after decoration we have a linear algorithm.


