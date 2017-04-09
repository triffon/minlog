;; 2017-04-09.  sdJK.scm.  Auxiliary file for sdmult.scm and graymult.scm

;; (load "~/git/minlog/init.scm")

;; (set! COMMENT-FLAG #f)
;; (libload "nat.scm")
;; (libload "pos.scm")
;; (libload "int.scm")
;; (set! COMMENT-FLAG #t)

(if (not (assoc "nat" ALGEBRAS))
    (myerror "First execute (libload \"nat.scm\")"))

(if (not (assoc "pos" ALGEBRAS))
    (myerror "First execute (libload \"pos.scm\")"))

(if (not (assoc "int" ALGEBRAS))
    (myerror "First execute (libload \"int.scm\")"))

(display "loading sdJK.scm ...") (newline)

(add-var-name "d" "e" (py "int"))

;; Corresponding to
;; (display-alg "int")
;; int
;; 	IntPos:	pos=>int
;; 	IntZero:	int
;; 	IntNeg:	pos=>int
;; we add the algebra sd in the order positive (R), zero (M), negative (L)

(add-alg "sd" '("SdR" "sd") '("SdM" "sd") '("SdL" "sd"))
(add-var-name "s" (py "sd"))
(add-totality "sd")

;; SdTotalVar
(set-goal "all s TotalSd s")
(use "AllTotalIntro")
(assume "s^" "Ts")
(use "Ts")
;; Proof finished
(save "SdTotalVar")

;; SdEqToEqD
(set-goal "all s1,s2(s1=s2 -> s1 eqd s2)")
(cases)
(cases)
(assume "Useless")
(use "InitEqD")
(assume "Absurd")
(use "EfqEqD")
(use "Absurd")
(assume "Absurd")
(use "EfqEqD")
(use "Absurd")
(cases)
(assume "Absurd")
(use "EfqEqD")
(use "Absurd")
(assume "Useless")
(use "InitEqD")
(assume "Absurd")
(use "EfqEqD")
(use "Absurd")
(cases)
(assume "Absurd")
(use "EfqEqD")
(use "Absurd")
(assume "Absurd")
(use "EfqEqD")
(use "Absurd")
(assume "Useless")
(use "InitEqD")
;; Proof finished.
(save "SdEqToEqD")

(add-ids
 (list (list "Sd" (make-arity (py "int")) "sd"))
 '("Sd(IntP One)" "InitSdSdR")
 '("Sd IntZero" "InitSdSdM")
 '("Sd(IntN One)" "InitSdSdL"))

;; SdBound
(set-goal "all d(Sd d -> abs d<=1)")
(assume "d" "Sdd")
(elim "Sdd")
(use "Truth")
(use "Truth")
(use "Truth")
;; Proof finished.
(save "SdBound")

;; SdUMinus
(set-goal "allnc d(Sd d -> Sd(~d))")
(assume "d" "Sdd")
(elim "Sdd")
(use "InitSdSdL")
(use "InitSdSdM")
(use "InitSdSdR")
;; Proof finished.
(save "SdUMinus")

;; Corresponding to (display-alg "int") int IntPos: pos=>int IntZero:
;; int IntNeg: pos=>int we add the algebra sdtwo in the order positive
;; (RT, RR for 1, 2), zero (MT), negative (LT, LL for -1, -2))

(add-alg "sdtwo"
	 '("RT" "sdtwo")
	 '("RR" "sdtwo")
	 '("MT" "sdtwo")
	 '("LT" "sdtwo")
	 '("LL" "sdtwo"))
(add-var-name "t" (py "sdtwo"))
(add-totality "sdtwo")

;; SdtwoTotalVar
(set-goal "all t TotalSdtwo t")
(use "AllTotalIntro")
(assume "t^" "Tt")
(use "Tt")
;; Proof finished
(save "SdtwoTotalVar")

;; SdtwoEqToEqD
(set-goal "all t1,t2(t1=t2 -> t1 eqd t2)")
(cases)
(cases)
(assume "Useless")
(use "InitEqD")
(assume "Absurd")
(use "EfqEqD")
(use "Absurd")
(assume "Absurd")
(use "EfqEqD")
(use "Absurd")
(assume "Absurd")
(use "EfqEqD")
(use "Absurd")
(assume "Absurd")
(use "EfqEqD")
(use "Absurd")
(cases)
(assume "Absurd")
(use "EfqEqD")
(use "Absurd")
(assume "Useless")
(use "InitEqD")
(assume "Absurd")
(use "EfqEqD")
(use "Absurd")
(assume "Absurd")
(use "EfqEqD")
(use "Absurd")
(assume "Absurd")
(use "EfqEqD")
(use "Absurd")
(cases)
(assume "Absurd")
(use "EfqEqD")
(use "Absurd")
(assume "Absurd")
(use "EfqEqD")
(use "Absurd")
(assume "Useless")
(use "InitEqD")
(assume "Absurd")
(use "EfqEqD")
(use "Absurd")
(assume "Absurd")
(use "EfqEqD")
(use "Absurd")
(cases)
(assume "Absurd")
(use "EfqEqD")
(use "Absurd")
(assume "Absurd")
(use "EfqEqD")
(use "Absurd")
(assume "Absurd")
(use "EfqEqD")
(use "Absurd")
(assume "Useless")
(use "InitEqD")
(assume "Absurd")
(use "EfqEqD")
(use "Absurd")
(cases)
(assume "Absurd")
(use "EfqEqD")
(use "Absurd")
(assume "Absurd")
(use "EfqEqD")
(use "Absurd")
(assume "Absurd")
(use "EfqEqD")
(use "Absurd")
(assume "Absurd")
(use "EfqEqD")
(use "Absurd")
(assume "Useless")
(use "InitEqD")
;; Proof finished.
(save "SdtwoEqToEqD")

(add-ids
 (list (list "Sdtwo" (make-arity (py "int")) "sdtwo"))
 '("Sdtwo(IntP One)" "InitSdtwoRT")
 '("Sdtwo(IntP(SZero One))" "InitSdtwoRR")
 '("Sdtwo IntZero" "InitSdtwoMT")
 '("Sdtwo(IntN One)" "InitSdtwoLT")
 '("Sdtwo(IntN(SZero One))" "InitSdtwoLL"))

;; SdtwoBound
(set-goal "all i(Sdtwo i -> abs i<=2)")
(assume "i" "Sdtwoi")
(elim "Sdtwoi")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
;; Proof finished.
(save "SdtwoBound")

;; To handle digit calculations without abundant case distinctions we
;; define (i) embeddings into the integers and (ii) realizability
;; predicates SdMR and SdtwoMR.

(add-program-constant "SdToInt" (py "sd=>int"))

(add-computation-rules
 "SdToInt SdR" "IntP 1"
 "SdToInt SdM" "IntZero"
 "SdToInt SdL" "IntN 1")

(set-totality-goal "SdToInt")
(use "AllTotalElim")
(cases)
(use "IntTotalVar")
(use "IntTotalVar")
(use "IntTotalVar")
;; Prove finished.
(save-totality)

(add-program-constant "IntToSd" (py "int=>sd"))

(add-computation-rules
 "IntToSd(IntP p)" "SdR"
 "IntToSd IntZero" "SdM"
 "IntToSd(IntN p)" "SdL")

(set-totality-goal "IntToSd")
(use "AllTotalElim")
(cases)
(assume "p")
(use "SdTotalVar")
(use "SdTotalVar")
(assume "p")
(use "SdTotalVar")
;; Prove finished.
(save-totality)

;; SdToIntToSdId
(set-goal "all s IntToSd(SdToInt s)=s")
(cases)
(use "Truth")
(use "Truth")
(use "Truth")
;; Proof finished.
(save "SdToIntToSdId")

;; IntToSdToIntId
(set-goal "all d(abs d<=1 -> SdToInt(IntToSd d)=d)")
(cases)
(assume "p" "pBd")
(ng)
(simp "pBd")
(use "Truth")
(assume "Useless")
(use "Truth")
(assume "p" "pBd")
(ng)
(simp "pBd")
(use "Truth")
;; Proof finished.
(save "IntToSdToIntId")

(add-mr-ids "Sd")

(display-idpc "SdMR")
;; SdMR
;; 	InitSdSdRMR:	SdMR SdR 1
;; 	InitSdSdMMR:	SdMR SdM 0
;; 	InitSdSdLMR:	SdMR SdL(IntN 1)

;; SdMRId
(set-goal "all d,s(SdMR s d -> SdToInt s=d)")
(assume "d" "s" "SdMRsd")
(elim "SdMRsd")
(use "Truth")
(use "Truth")
(use "Truth")
;; Proof finished.
(save "SdMRId")

;; SdMRIntToSd
(set-goal "all d(abs d<=1 -> SdMR(IntToSd d)d)")
(cases)
(assume "p" "pBd")
(ng)
(simp "pBd")
(use "InitSdSdRMR")
(assume "Useless")
(use "InitSdSdMMR")
(assume "p" "pBd")
(ng)
(simp "pBd")
(use "InitSdSdLMR")
;; Proof finished.
(save "SdMRIntToSd")

;; SdMRIntro
(set-goal "allnc d(Sd d -> exl s SdMR s d)")
(assume "d" "Sdd")
(elim "Sdd")
(intro 0 (pt "SdR"))
(use "InitSdSdRMR")
(intro 0 (pt "SdM"))
(use "InitSdSdMMR")
(intro 0 (pt "SdL"))
(use "InitSdSdLMR")
;; Proof finished.
(save "SdMRIntro")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [s]s

(animate "SdMRIntro")

;; SdMRElim
(set-goal "allnc d all s(SdMR s d -> Sd d)")
(assume "d")
(cases)
;; 3-5
(assume "SdMRSdRd")
(inst-with-to "SdMRId" (pt "d") (pt "SdR") "SdMRSdRd" "SdMRIdInst")
(simp "<-" "SdMRIdInst")
(use "InitSdSdR")
;; 4
(assume "SdMRSdMd")
(inst-with-to "SdMRId" (pt "d") (pt "SdM") "SdMRSdMd" "SdMRIdInst")
(simp "<-" "SdMRIdInst")
(use "InitSdSdM")
;; 5
(assume "SdMRSdLd")
(inst-with-to "SdMRId" (pt "d") (pt "SdL") "SdMRSdLd" "SdMRIdInst")
(simp "<-" "SdMRIdInst")
(use "InitSdSdL")
;; Proof finished.
(save "SdMRElim")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [s]s

(animate "SdMRElim")

;; We do the same for Sdtwo.

(add-program-constant "SdtwoToInt" (py "sdtwo=>int"))

(add-computation-rules
 "SdtwoToInt RT" "IntP 1"
 "SdtwoToInt RR" "IntP 2"
 "SdtwoToInt MT" "IntZero"
 "SdtwoToInt LT" "IntN 1"
 "SdtwoToInt LL" "IntN 2")

(set-totality-goal "SdtwoToInt")
(use "AllTotalElim")
(cases)
(use "IntTotalVar")
(use "IntTotalVar")
(use "IntTotalVar")
(use "IntTotalVar")
(use "IntTotalVar")
;; Prove finished.
(save-totality)

(add-program-constant "PosToSdtwo" (py "pos=>sdtwo"))

(add-computation-rules
 "PosToSdtwo One" "RT"
 "PosToSdtwo(SZero p)" "RR"
 "PosToSdtwo(SOne p)" "RR")

(set-totality-goal "PosToSdtwo")
(use "AllTotalElim")
(cases)
(use "SdtwoTotalVar")
(assume "p")
(use "SdtwoTotalVar")
(assume "p")
(use "SdtwoTotalVar")
;; Proof finished.
(save-totality) 

(add-program-constant "SdtwoUMinus" (py "sdtwo=>sdtwo"))

(add-computation-rules
 "SdtwoUMinus RT" "LT"
 "SdtwoUMinus RR" "LL"
 "SdtwoUMinus MT" "MT"
 "SdtwoUMinus LT" "RT"
 "SdtwoUMinus LL" "RR")

(set-totality-goal "SdtwoUMinus")
(use "AllTotalElim")
(cases)
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
;; Proof finished.
(save-totality) 

(add-program-constant "IntToSdtwo" (py "int=>sdtwo"))

(add-computation-rules
 "IntToSdtwo(IntP p)" "PosToSdtwo p"
 "IntToSdtwo IntZero" "MT"
 "IntToSdtwo(IntN p)" "SdtwoUMinus(PosToSdtwo p)")

(set-totality-goal "IntToSdtwo")
(use "AllTotalElim")
(cases)
(assume "p")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(assume "p")
(use "SdtwoTotalVar")
;; Proof finished.
(save-totality) 

;; SdtwoToIntToSdtwoId
(set-goal "all t IntToSdtwo(SdtwoToInt t)=t")
(cases)
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
;; Proof finished.
(save "SdtwoToIntToSdtwoId")

;; IntToSdtwoToIntId
(set-goal "all i(abs i<=2 -> SdtwoToInt(IntToSdtwo i)=i)")
(cases)
(cases)
(assume "Useless")
(use "Truth")
(cases)
(assume "Useless")
(use "Truth")
(assume "p" "Absurd")
(use "EfqAtom")
(use "Absurd")
(assume "p" "Absurd")
(use "EfqAtom")
(use "Absurd")
(assume "p" "Absurd")
(use "EfqAtom")
(use "Absurd")
;; 3
(assume "Useless")
(use "Truth")
;; 4
(cases)
(assume "Useless")
(use "Truth")
(cases)
(assume "Useless")
(use "Truth")
(assume "p" "Absurd")
(use "EfqAtom")
(use "Absurd")
(assume "p" "Absurd")
(use "EfqAtom")
(use "Absurd")
(assume "p" "Absurd")
(use "EfqAtom")
(use "Absurd")
;; Proof finished.
(save "IntToSdtwoToIntId")

(add-mr-ids "Sdtwo")

(display-idpc "SdtwoMR")
;; SdtwoMR
;; 	InitSdtwoRTMR:	SdtwoMR RT 1
;; 	InitSdtwoRRMR:	SdtwoMR RR 2
;; 	InitSdtwoMTMR:	SdtwoMR MT 0
;; 	InitSdtwoLTMR:	SdtwoMR LT(IntN 1)
;; 	InitSdtwoLLMR:	SdtwoMR LL(IntN 2)

;; SdtwoMRId
(set-goal "all i,t(SdtwoMR t i -> SdtwoToInt t=i)")
(assume "i" "t" "SdtwoMRsdi")
(elim "SdtwoMRsdi")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
;; Proof finished.
(save "SdtwoMRId")

;; SdtwoMRIntro
(set-goal "allnc i(Sdtwo i -> exl t SdtwoMR t i)")
(assume "i" "Sdtwoi")
(elim "Sdtwoi")
;; 3-7
(intro 0 (pt "RT"))
(use "InitSdtwoRTMR")
;; 4
(intro 0 (pt "RR"))
(use "InitSdtwoRRMR")
;; 5
(intro 0 (pt "MT"))
(use "InitSdtwoMTMR")
;; 6
(intro 0 (pt "LT"))
(use "InitSdtwoLTMR")
;; 7
(intro 0 (pt "LL"))
(use "InitSdtwoLLMR")
;; Proof finished.
(save "SdtwoMRIntro")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [t]t

(animate "SdtwoMRIntro")

;; SdtwoMRElim
(set-goal "allnc i all t(SdtwoMR t i -> Sdtwo i)")
(assume "i")
(cases)
;; 3-7
(assume "SdtwoRTi")
(inst-with-to "SdtwoMRId" (pt "i") (pt "RT") "SdtwoRTi" "SdtwoMRIdInst")
(simp "<-" "SdtwoMRIdInst")
(use "InitSdtwoRT")
;; 4
(assume "SdtwoRRi")
(inst-with-to "SdtwoMRId" (pt "i") (pt "RR") "SdtwoRRi" "SdtwoMRIdInst")
(simp "<-" "SdtwoMRIdInst")
(use "InitSdtwoRR")
;; 5
(assume "SdtwoMTi")
(inst-with-to "SdtwoMRId" (pt "i") (pt "MT") "SdtwoMTi" "SdtwoMRIdInst")
(simp "<-" "SdtwoMRIdInst")
(use "InitSdtwoMT")
;; 6
(assume "SdtwoLTi")
(inst-with-to "SdtwoMRId" (pt "i") (pt "LT") "SdtwoLTi" "SdtwoMRIdInst")
(simp "<-" "SdtwoMRIdInst")
(use "InitSdtwoLT")
;; 7
(assume "SdtwoLLi")
(inst-with-to "SdtwoMRId" (pt "i") (pt "LL") "SdtwoLLi" "SdtwoMRIdInst")
(simp "<-" "SdtwoMRIdInst")
(use "InitSdtwoLL")
;; Proof finished.
(save "SdtwoMRElim")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [t]t

(animate "SdtwoMRElim")

;; SdtwoMRIntToSdtwo
(set-goal "all d(abs d<=2 -> SdtwoMR(IntToSdtwo d)d)")
(cases)
;; 2-4
(cases)
(assume "Useless")
(use "InitSdtwoRTMR")
(cases)
(assume "Useless")
(use "InitSdtwoRRMR")
(assume "p" "Absurd")
(use "Efq")
(use "Absurd")
(assume "p" "Absurd")
(use "Efq")
(use "Absurd")
(assume "p" "Absurd")
(use "Efq")
(use "Absurd")
;; 3
(assume "Useless")
(use "InitSdtwoMTMR")
;; 4
(cases)
(assume "Useless")
(use "InitSdtwoLTMR")
(cases)
(assume "Useless")
(use "InitSdtwoLLMR")
(assume "p" "Absurd")
(use "Efq")
(use "Absurd")
(assume "p" "Absurd")
(use "Efq")
(use "Absurd")
(assume "p" "Absurd")
(use "Efq")
(use "Absurd")
;; Proof finished.
(save "SdtwoMRIntToSdtwo")

;; IntPlusSdToSdtwo
(set-goal "allnc d,e(Sd d -> Sd e -> Sdtwo(d+e))")
(assume "d" "e" "Sdd" "Sde")
(assert "exl s1 SdMR s1 d")
(use "SdMRIntro")
(use "Sdd")
(assume "ExHyp1")
(by-assume "ExHyp1" "s1" "s1Prop")
(assert "exl s2 SdMR s2 e")
(use "SdMRIntro")
(use "Sde")
(assume "ExHyp2")
(by-assume "ExHyp2" "s2" "s2Prop")
(use "SdtwoMRElim" (pt "IntToSdtwo(SdToInt s1+SdToInt s2)"))
(simp (pf "SdToInt s1+SdToInt s2=d+e"))
(use "SdtwoMRIntToSdtwo")
;; ?_20:abs(d+e)<=2
(use "IntLeTrans" (pt "abs d+abs e"))
(use "IntLeAbsPlus")
(use "IntLeTrans" (pt "IntP 1+IntP 1"))
(use "IntLeMonPlus")
(use "SdBound")
(use "Sdd")
(use "SdBound")
(use "Sde")
(use "Truth")
;; ?_19:SdToInt s1+SdToInt s2=d+e
(inst-with-to "SdMRId" (pt "d") (pt "s1") "s1Prop" "SdMRIdInst1")
(inst-with-to "SdMRId" (pt "e") (pt "s2") "s2Prop" "SdMRIdInst2")
(simp "SdMRIdInst1")
(simp "SdMRIdInst2")
(use "Truth")
;; Proof finished.
(save "IntPlusSdToSdtwo")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [s,s0]IntToSdtwo(SdToInt s+SdToInt s0)

;; SdtwoToSdtwoToIntValue
(set-goal "allnc i(Sdtwo i -> exl t SdtwoToInt t=i)")
(assume "i" "Sdtwoi")
(inst-with-to "SdtwoMRIntro" (pt "i") "Sdtwoi" "SdtwoMRIntroInst")
(by-assume "SdtwoMRIntroInst" "t" "tProp")
(intro 0 (pt "t"))
(use "SdtwoMRId")
(use "tProp")
;; Proof finished.
(save "SdtwoToSdtwoToIntValue")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [t]t

(animate "SdtwoToSdtwoToIntValue")

;; Noe for JK

;; We define K: int=>int and J: int=>int and such that
;; (1) for abs k<=6 we have abs(K k)<=1
;; (2) abs(J k)<=2
;; (3) k=(K k)*4+(J k).

(add-program-constant "K" (py "int=>int"))
(add-computation-rules
 "K p" "lft(PosQR(PosS p)4)"
 "K 0" "0"
 "K(IntN p)" "~lft(PosQR(PosS p)4)")

(set-totality-goal "K")
(use "AllTotalElim")
(cases)
;; 3-5
(assume "p")
(ng)
(use "IntTotalVar")
;; 4
(use "IntTotalVar")
;; 5
(assume "p")
(ng)
(use "IntTotalVar")
;; Proof finished.
(save-totality)

(add-program-constant "J" (py "int=>int"))
(add-computation-rules
 "J p" "IntPred rht(PosQR(PosS p)4)"
 "J 0" "0"
 "J(IntN p)" "IntS~rht(PosQR(PosS p)4)")

(set-totality-goal "J")
(use "AllTotalElim")
(cases)
;; 3-5
(assume "p")
(ng)
(use "IntTotalVar")
;; 4
(use "IntTotalVar")
;; 5
(assume "p")
(ng)
(use "IntTotalVar")
;; Proof finished.
(save-totality)

;; KProp
(set-goal "all k(abs k<=6 -> abs(K k)<=1)")
(assert "all p(2<=lft(PosQR p 4) -> 2*IntP 4<=p)")
(assume "p" "2<=Qp4")
(assert "2*IntP 4<=lft(PosQR p 4)*4+rht(PosQR p 4)")
(use "IntLeTrans" (pt "lft(PosQR p 4)*4"))
(use "IntLeMonTimes")
(use "Truth")
(use "2<=Qp4")
(use "IntLeTrans" (pt "lft(PosQR p 4)*4+0"))
(use "Truth")
(use "IntLeMonPlus")
(use "Truth")
(use "PosQRCorrAux" (pt "p") (pt "4") (pt "lft(PosQR p 4)"))
(simp "PairConstrOneTwo")
(use "Truth")
(assume "Assertion")
(assert "p=lft(PosQR p 4)*4+rht(PosQR p 4)")
(use "PosQRCorrAux")
(simp "PairConstrOneTwo")
(use "Truth")
(assume "pProp")
(simp "pProp")
(simp "<-" "Assertion")
(use "Truth")
;; Assertion proved.
(assume "KPosAux1")
(assert "all p(IntP p<=7 -> lft(PosQR p 4)<=1)")
(assume "p" "p<=7")
(use "IntNotLtToLe")
(simp "<-" "IntLeIntS")
(assume "2<=Qp4")
(inst-with-to "KPosAux1" (pt "p") "2<=Qp4" "KPosAux1Inst")
(assert "IntP 8<=7")
 (use "IntLeTrans" (pt "IntP p"))
 (use "KPosAux1Inst")
 (use "p<=7")
(assume "Absurd")
(use "Absurd")
;; Assertion proved.
(assume "KPosAux2")
(assert "all p(p<=6 -> lft(PosQR(PosS p)4)<=1)")
(assume "p" "p<=6")
(use "KPosAux2")
(ng #t)
(simp (pf "7=PosS 6"))
(simp "PosLe9RewRule")
(use "p<=6")
(use "Truth")
;; Assertion proved.
(assume "KPosProp")
(assert "all p,q 0<=lft(PosQR p q)")
(ind)
;; 2-4
(cases)
;; 5-7
(use "Truth")
;; 6
(assume "p")
(use "Truth")
;; 7
(assume "p")
(use "Truth")
;; 3
(assume "p" "IH" "q")
(ng)
(inst-with-to "PairConstrOneTwo"
	      (py "int") (py "int") (pt "PosQR p q") "PairConstrOneTwoInst")
(simp "<-" "PairConstrOneTwoInst")
(drop "PairConstrOneTwoInst")
(ng)
(cases (pt "(2*rht(PosQR p q)<q)"))
(assume "Useless")
(ng)
(simp (pf "0=0*lft(PosQR p q)"))
(use "IntLeMonTimes")
(use "IH")
(use "Truth")
(use "Truth")
;; 18
(assume "Useless")
(ng)
(use "IntLeTrans" (pt "2*lft(PosQR p q)"))
(simp (pf "0=0*lft(PosQR p q)"))
(use "IntLeMonTimes")
(use "IH")
(use "Truth")
(use "Truth")
(use "Truth")
;; 4
(assume "p" "IH" "q")
(ng)
(inst-with-to "PairConstrOneTwo"
	      (py "int") (py "int") (pt "PosQR p q") "PairConstrOneTwoInst")
(simp "<-" "PairConstrOneTwoInst")
(drop "PairConstrOneTwoInst")
(ng)
(cases (pt "(2*rht(PosQR p q)+1<q)"))
(assume "Useless")
(ng)
(simp (pf "0=0*lft(PosQR p q)"))
(use "IntLeMonTimes")
(use "IH")
(use "Truth")
(use "Truth")
;; 41
(assume "Useless")
(ng)
(use "IntLeTrans" (pt "2*lft(PosQR p q)"))
(simp (pf "0=0*lft(PosQR p q)"))
(use "IntLeMonTimes")
(use "IH")
(use "Truth")
(use "Truth")
(use "Truth")
;; Assertion proved.
(assume "PosQRPairOneNNeg")
;; Now we are ready to prove KProp: all k(abs k<=6 -> abs(K k)<=1)")
(cases)
;; 11-13
(assume "p")
(ng)
(simp "IntAbsId")
(use "KPosProp")
(use "PosQRPairOneNNeg")
;; 12
(strip)
(use "Truth")
;; 13
(assume "p")
(ng)
(simp "IntAbsId")
(use "KPosProp")
(use "PosQRPairOneNNeg")
;; Proof finished.
(save "KProp")

;; JProp
(set-goal "all k abs(J k)<=2")
(cases)
;; 2-4
(assume "p")
(use "IntLeAbs")
;; 6,7
(ng)
(simp "<-" "IntLe6RewRule")
(ng)
(simp "<-" "IntLtIntS")
(use "PosQRCorr")
;; 7
(ng)
(use "IntLeTrans" (pt "IntS~0"))
(simp "IntLe6RewRule")
(simp "IntLe5RewRule")
(use "PosQRCorr")
(use "Truth")
;; 3
(use "Truth")
;; 4
(assume "p")
(ng)
(use "IntLeAbs")
;; 19,20
(use "IntLeTrans" (pt "IntS~0"))
(simp "IntLe6RewRule")
(simp "IntLe5RewRule")
(use "PosQRCorr")
(use "Truth")
;; 20
(simp (pf "2= ~(IntS~3)"))
(simp "IntLe5RewRule")
(simp "IntLe6RewRule")
(simp "IntLe5RewRule")
(simp "<-" "IntLtIntS")
(use "PosQRCorr")
(use "Truth")
;; Proof finished.
(save "JProp")

;; KJProp
(set-goal "all k k=K k*4+J k")
(cases)
;; 2-4
(ng)
(assume "p")
(simp "<-" "IntSInj")
(use "Truth")
(ng)
(simp (pf "all k,j IntS(k+j)=k+IntS j"))
(ng)
(use "PosQRCorr")
;; ?_11:all k,j IntS(k+j)=k+IntS j
(strip)
(use "Truth")
;; 3
(use "Truth")
;; 4
(ng)
(assume "p")
(simp "<-" "IntUMinusInj")
(ng)
(simp "<-" "PosQRCorr")
(use "Truth")
;; Proof finished.
(save "KJProp")

;; CoIAvcSatCoIClAux 
(set-goal "all x,y,d,e,i(Real x -> Real y ->
 (1#4)*((1#2)*(x+d)+(1#2)*(y+e)+i)===
 (1#2)*((1#4)*(x+y+J(d+e+i*2))+K(d+e+i*2)))")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "d" "e" "i" "Rx" "Ry")
(use "RealSeqEqToEq" (pt "Zero"))
;; 6-8
(use "RealTimesReal")
(use "RealRat")
(use "RealPlusReal")
(use "RealPlusReal")
(use "RealTimesReal")
(use "RealRat")
(use "RealPlusReal")
(use "Rx")
(use "RealRat")
(use "RealTimesReal")
(use "RealRat")
(use "RealPlusReal")
(use "Ry")
(use "RealRat")
(use "RealRat")
;; 9
(use "RealTimesReal")
(use "RealRat")
(use "RealPlusReal")
(use "RealTimesReal")
(use "RealRat")
(use "RealPlusReal")
(use "RealPlusReal")
(use "Rx")
(use "Ry")
(use "RealRat")
(use "RealRat")
;; 10
(assume "n" "Useless")
(ng)
;;   n
;; -----------------------------------------------------------------------------
;; ?_36:(1#4)*((1#2)*(as n+d)+(1#2)*(bs n+e)+i)==
;;      (1#2)*((1#4)*(as n+bs n+J(d+e+i*2))+K(d+e+i*2))
(simprat "RatTimesPlusDistr")
(simprat "RatTimesPlusDistr")
(simprat "RatTimesPlusDistr")
(simprat "RatTimesPlusDistr")
(simprat "RatTimesPlusDistr")
(simprat "RatTimesPlusDistr")
(simprat "RatTimesPlusDistr")
(simprat "RatTimesPlusDistr")
(simprat "RatTimesPlusDistr")
(simprat "RatTimesPlusDistr")
(simprat "RatTimesPlusDistr")
(ng)
;; ?_48:(1#8)*as n+(d#8)+(1#8)*bs n+(e#8)+(i#4)==
;;      (1#8)*as n+(1#8)*bs n+(J(d+e+i*2)#8)+(K(d+e+i*2)#2)
(assert "(1#8)*as n+(d#8)+(1#8)*bs n+(e#8)+(i#4)=
         (1#8)*as n+((d#8)+(1#8)*bs n+(e#8)+(i#4))")
 (ng)
 (use "Truth")
(assume "EqHyp1")
(simp "EqHyp1")
(drop "EqHyp1")
(assert "(1#8)*as n+(1#8)*bs n+(J(d+e+i*2)#8)+(K(d+e+i*2)#2)==
         (1#8)*as n+((1#8)*bs n+(J(d+e+i*2)#8)+(K(d+e+i*2)#2))")
 (ng)
 (use "Truth")
(assume "EqvHyp2")
(simprat "EqvHyp2")
(drop "EqvHyp2")
(use "RatPlusCompat")
(use "Truth")
(assert "(d#8)+(1#8)*bs n=(1#8)*bs n+(d#8)")
 (use "RatPlusComm")
(assume "EqHyp3")
(simp "EqHyp3")
(drop "EqHyp3")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
;; ?_72:(d#8)+((e#8)+(i#4))==(J(d+e+i*2)#8)+(K(d+e+i*2)#2)
(assert "(i#4)==(i*2#8)")
 (ng)
 (simp "<-" "IntTimesAssoc")
 (use "Truth")
(assume "EqvHyp4")
(simprat "EqvHyp4")
(drop "EqvHyp4")
(assert "(K(d+e+i*2)#2)==(K(d+e+i*2)*4#8)")
 (ng)
 (simp "<-" "IntTimesAssoc")
 (use "Truth")
(assume "EqvHyp5")
(simprat "EqvHyp5")
(drop "EqvHyp5")
;; ?_86:(d#8)+((e#8)+(i*2#8))==(J(d+e+i*2)#8)+(K(d+e+i*2)*4#8)
(simprat "<-" "RatEqvConstrPlus")
(simprat "<-" "RatEqvConstrPlus")
(simprat "<-" "RatEqvConstrPlus")
(assert "all k k=J k+K k*4")
 (assume "k")
 (simp "IntPlusComm")
 (use "KJProp")
(assume "JKProp")
(simp "<-" "JKProp")
(ng)
(use "Truth")
;; Proof finished.
(save "CoIAvcSatCoIClAux")

