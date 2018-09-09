;; 2018-09-08.  examples/analysis/digits.scm

;; Dependency of files

;; sdmult       sddiv <--   div  -->  graydiv     graymult
;;    ^           ^                      ^           ^
;;      \         |                      |         /
;;         \      |                      |      /
;;            \   |                      |   / 
;;  sdav <--   sdavaux <--  JK  -->  grayavaux --> grayav
;;                ^                      ^
;;                |                      |
;;                |                      |
;;                |                      |
;;             sdcode <--  digits --> graycode

;; (load "~/git/minlog/init.scm")

;; (set! COMMENT-FLAG #f)
;; (libload "nat.scm")
;; (libload "list.scm")
;; (libload "pos.scm")
;; (libload "int.scm")
;; (libload "rat.scm")
;; (remove-var-name "x" "y" "z")
;; (libload "rea.scm")
;; ;; (set! COMMENT-FLAG #t)

(display "loading digits.scm ...") (newline)

(remove-var-name "d") ;will be used as variable name for integers
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

;; SdtwoIntUMinus
(set-goal "allnc i(Sdtwo i -> Sdtwo(~i))")
(assume "i" "Sdtwoi")
(elim "Sdtwoi")
(use "InitSdtwoLT")
(use "InitSdtwoLL")
(use "InitSdtwoMT")
(use "InitSdtwoRT")
(use "InitSdtwoRR")
;; Proof finished.
(save "SdtwoIntUMinus")

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

;; IntTimesSdToSd
(set-goal "allnc d,e(Sd d -> Sd e -> Sd(d*e))")
(assume "d" "e")
(elim)
(elim)
(use "InitSdSdR")
(use "InitSdSdM")
(use "InitSdSdL")
(elim)
(use "InitSdSdM")
(use "InitSdSdM")
(use "InitSdSdM")
(elim)
(use "InitSdSdL")
(use "InitSdSdM")
(use "InitSdSdR")
;; Proof finished.
(save "IntTimesSdToSd")

(add-mr-ids "Sd")

(display-idpc "SdMR")
;; SdMR	non-computational
;; 	InitSdSdRMR:	SdMR 1 SdR
;; 	InitSdSdMMR:	SdMR 0 SdM
;; 	InitSdSdLMR:	SdMR(IntN 1)SdL

;; SdMRId
(set-goal "all d,s(SdMR d s -> SdToInt s=d)")
(assume "d" "s" "SdMRds")
(elim "SdMRds")
(use "Truth")
(use "Truth")
(use "Truth")
;; Proof finished.
(save "SdMRId")

;; SdMRIntToSd
(set-goal "all d(abs d<=1 -> SdMR d(IntToSd d))")
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
(set-goal "allnc d(Sd d -> exl s SdMR d s)")
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
(set-goal "allnc d all s(SdMR d s -> Sd d)")
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
;; SdtwoMR	non-computational
;; 	InitSdtwoRTMR:	SdtwoMR 1 RT
;; 	InitSdtwoRRMR:	SdtwoMR 2 RR
;; 	InitSdtwoMTMR:	SdtwoMR 0 MT
;; 	InitSdtwoLTMR:	SdtwoMR(IntN 1)LT
;; 	InitSdtwoLLMR:	SdtwoMR(IntN 2)LL

;; SdtwoMRId
(set-goal "all i,t(SdtwoMR i t -> SdtwoToInt t=i)")
(assume "i" "t" "SdtwoMRsit")
(elim "SdtwoMRsit")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
;; Proof finished.
(save "SdtwoMRId")

;; SdtwoMRIntro
(set-goal "allnc i(Sdtwo i -> exl t SdtwoMR i t)")
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
(set-goal "allnc i all t(SdtwoMR i t -> Sdtwo i)")
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
(set-goal "all d(abs d<=2 -> SdtwoMR d(IntToSdtwo d))")
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
(assert "exl s1 SdMR d s1")
(use "SdMRIntro")
(use "Sdd")
(assume "ExHyp1")
(by-assume "ExHyp1" "s1" "s1Prop")
(assert "exl s2 SdMR e s2")
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

;; For gray code we also need proper signed digits

(add-ids
 (list (list "Psd" (make-arity (py "int")) "boole"))
 '("Psd(IntP One)" "InitPsdTrue")
 '("Psd(IntN One)" "InitPsdFalse"))

;; PsdToAbsOne
(set-goal "all d(Psd d -> abs d=1)")
(assume "d" "Psdd")
(elim "Psdd")
(use "Truth")
(use "Truth")
;; Proof finished.
(save "PsdToAbsOne")

;; PsdToSd
(set-goal "allnc d(Psd d -> Sd d)")
(assume "d" "Psdd")
(elim "Psdd")
(use "InitSdSdR")
(use "InitSdSdL")
;; Proof finished.
(save "PsdToSd")

;; PsdToSdtwo
(set-goal "allnc d(Psd d -> Sdtwo d)")
(assume "d" "Psdd")
(elim "Psdd")
(use "InitSdtwoRT")
(use "InitSdtwoLT")
;; Proof finished.
(save "PsdToSdtwo")

;; PsdUMinus
(set-goal "allnc d(Psd d -> Psd(~d))")
(assume "d" "Psdd")
(elim "Psdd")
(use "InitPsdFalse")
(use "InitPsdTrue")
;; Proof finished.
(save "PsdUMinus")

;; To handle digit calculations without abundant case distinctions we
;; define (i) embeddings into the integers and (ii) the realizability
;; predicate PsdMR.

(add-program-constant "BooleToInt" (py "boole=>int"))

(add-computation-rules
 "BooleToInt True" "IntP 1"
 "BooleToInt False" "IntN 1")

(set-totality-goal "BooleToInt")
(use "AllTotalElim")
(cases)
(use "IntTotalVar")
(use "IntTotalVar")
;; Prove finished.
(save-totality)

(add-program-constant "IntToBoole" (py "int=>boole"))

(add-computation-rules
 "IntToBoole(IntP p)" "True"
 "IntToBoole IntZero" "True"
 "IntToBoole(IntN p)" "False")

(set-totality-goal "IntToBoole")
(use "AllTotalElim")
(cases)
(assume "p")
(use "BooleTotalVar")
(use "BooleTotalVar")
(assume "p")
(use "BooleTotalVar")
;; Prove finished.
(save-totality)

;; BooleToIntToBooleId
(set-goal "all boole IntToBoole(BooleToInt boole)=boole")
(cases)
(use "Truth")
(use "Truth")
;; Proof finished.
(save "BooleToIntToBooleId")

;; IntToBooleToIntId
(set-goal "all d(abs d=1 -> BooleToInt(IntToBoole d)=d)")
(cases)
(assume "p" "pProp")
(ng)
(simp "pProp")
(use "Truth")
(assume "Absurd")
(use "EfqAtom")
(use "Absurd")
(assume "p" "pProp")
(ng)
(simp "pProp")
(use "Truth")
;; Proof finished.
(save "IntToBooleToIntId")

(display-idpc "Psd")
;; Psd
;; 	InitPsdTrue:	Psd 1
;; 	InitPsdFalse:	Psd(IntN 1)

(add-mr-ids "Psd")

(display-idpc "PsdMR")
;; PsdMR	non-computational
;; 	InitPsdTrueMR:	PsdMR 1 True
;; 	InitPsdFalseMR:	PsdMR(IntN 1)False

;; PsdMRId
(set-goal "all d,boole(PsdMR d boole -> BooleToInt boole=d)")
(assume "d" "boole" "PsdMRHyp")
(elim "PsdMRHyp")
(use "Truth")
(use "Truth")
;; Proof finished.
(save "PsdMRId")

;; PsdMRIntro
(set-goal "allnc d(Psd d -> exl boole PsdMR d boole)")
(assume "d" "Psdd")
(elim "Psdd")
(intro 0 (pt "True"))
(use "InitPsdTrueMR")
(intro 0 (pt "False"))
(use "InitPsdFalseMR")
;; Proof finished.
(save "PsdMRIntro")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [boole]boole

(animate "PsdMRIntro")

;; PsdMRElim
(set-goal "allnc d all boole(PsdMR d boole -> Psd d)")
(assume "d")
(cases)
;; 3,4
(assume "PsdMRTrue")
(inst-with-to "PsdMRId" (pt "d") (pt "True") "PsdMRTrue" "PsdMRIdInst")
(simp "<-" "PsdMRIdInst")
(use "InitPsdTrue")
;; 4
(assume "PsdMRFalse")
(inst-with-to "PsdMRId" (pt "d") (pt "False") "PsdMRFalse" "PsdMRIdInst")
(simp "<-" "PsdMRIdInst")
(use "InitPsdFalse")
;; Proof finished.
(save "PsdMRElim")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [boole]boole

;; (animate "SdMRElim")

;; PsdToBooleToIntValue
(set-goal "allnc d(Psd d -> exl boole BooleToInt boole=d)")
(assume "d" "Psdd")
(inst-with-to "PsdMRIntro" (pt "d") "Psdd" "PsdMRIntroInst")
(by-assume "PsdMRIntroInst" "boole" "booleProp")
(intro 0 (pt "boole"))
(use "PsdMRId")
(use "booleProp")
;; Proof finished.
(save "PsdToBooleToIntValue")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [boole]boole
(animate "PsdToBooleToIntValue")

;; PsdMRIntToBoole
(set-goal "all d(abs d=1 -> PsdMR d(IntToBoole d))")
(cases)
(assume "p" "pProp")
(ng)
(simp "pProp")
(use "InitPsdTrueMR")
(assume "Absurd")
(use "Efq")
(use "Absurd")
(assume "p" "pProp")
(ng)
(simp "pProp")
(use "InitPsdFalseMR")
;; Proof finished.
(save "PsdMRIntToBoole")

;; IntTimesSdtwoPsdToSdtwo
(set-goal "allnc i,d(Sdtwo i -> Psd d -> Sdtwo(i*d))")
(assume "i" "d" "Sdtwoi")
(elim "Sdtwoi")
;; 3-7
(assume "Psdd")
(elim "Psdd")
;; 9,10
(ng)
(use "InitSdtwoRT")
;; 10
(ng)
(use "InitSdtwoLT")
;; 4
(assume "Psdd")
(elim "Psdd")
;; 14,15
(ng)
(use "InitSdtwoRR")
;; 15
(ng)
(use "InitSdtwoLL")
;; 5
(assume "Psdd")
(elim "Psdd")
;; 19,20
(ng)
(use "InitSdtwoMT")
;; 20
(ng)
(use "InitSdtwoMT")
;; 6
(assume "Psdd")
(elim "Psdd")
;; 24,25
(ng)
(use "InitSdtwoLT")
;; 25
(ng)
(use "InitSdtwoRT")
;; 7
(assume "Psdd")
(elim "Psdd")
;; 29,30
(ng)
(use "InitSdtwoLL")
;; 30
(ng)
(use "InitSdtwoRR")
;; Proof finished.
(save "IntTimesSdtwoPsdToSdtwo")

;; RealTimesPsdPsd
(set-goal "all d,x(Real x -> Psd d -> x*d*d===x)")
(assert "all d,x(Psd d -> x*d*d=+=x)")
(assume "d")
(cases)
(assume "as" "M" "Psdd")
(elim "Psdd")
;; 5,6
(use "RealEqSIntro")
(assume "n")
(ng)
(use "Truth")
;; 6
(use "RealEqSIntro")
(assume "n")
(ng)
(use "Truth")
;; Assertion proved.
(assume "RealTimesPsdPsdEqS" "d" "x" "Rx" "Psdd")
(use "RealEqSToEq")
(autoreal)
(use "RealTimesPsdPsdEqS")
(use "Psdd")
;; Proof finished.
(save "RealTimesPsdPsd")

;; IntPlusPsdToSdtwo
(set-goal "allnc d,e(Psd d -> Psd e -> Sdtwo(d+e))")
(assume "d" "e")
(elim)
(elim)
(use "InitSdtwoRR")
(use "InitSdtwoMT")
(elim)
(use "InitSdtwoMT")
(use "InitSdtwoLL")
;; Proof finished.
(save "IntPlusPsdToSdtwo")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [boole,boole0][if boole [if boole0 RR MT] [if boole0 MT LL]]

;; IntTimesPsdToPsd
(set-goal "allnc d,e(Psd d -> Psd e -> Psd(d*e))")
(assume "d" "e")
(elim)
(elim)
(use "InitPsdTrue")
(use "InitPsdFalse")
(elim)
(use "InitPsdFalse")
(use "InitPsdTrue")
;; Proof finished.
(save "IntTimesPsdToPsd")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [boole,boole0][if boole boole0 [if boole0 False True]]
;; Corresponds to IntTimes (under BooleToInt IntToBoole)

