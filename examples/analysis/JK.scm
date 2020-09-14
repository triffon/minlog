;; 2017-12-12.  examples/analysis/JK.scm

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

(display "loading JK.scm ...") (newline)

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

