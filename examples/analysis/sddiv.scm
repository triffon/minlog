;; 2020-08-14.  examples/analysis/sddiv.scm
;; Uses material form Franziskus Wiesnet's Master thesis

;; (load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(libload "list.scm")
(libload "pos.scm")
(libload "int.scm")
(libload "rat.scm")
(remove-var-name "x" "y" "z")
(libload "rea.scm")
;; (set! COMMENT-FLAG #t)

(load "~/git/minlog/examples/analysis/digits.scm")
(load "~/git/minlog/examples/analysis/sdcode.scm")
(load "~/git/minlog/examples/analysis/JK.scm")
(load "~/git/minlog/examples/analysis/sdavaux.scm")
(load "~/git/minlog/examples/analysis/div.scm")

;; CoIOne
(set-goal "CoI 1")
(assert "allnc x(exl x0(x0===1 andi x===x0) -> CoI x)")
 (assume "x2" "ExHyp2")
 (coind "ExHyp2")
 (drop "ExHyp2")
 (assume "x" "xProp")
 (by-assume "xProp" "x1" "x1Prop")
 (elim "x1Prop")
 (drop "x1Prop")
 (assume "x1=1" "x=x1")
 (intro 0 (pt "IntP 1"))
 (intro 0 (pt "x1"))
 (intro 0 (pt "x"))
 (split)
 (use "InitSdSdR")
 (split)
 (autoreal)
 (split)
 (simpreal "x1=1")
 (use "RatLeToRealLe")
 (use "Truth")
 (split)
 (intro 1)
 (intro 0 (pt "x1"))
 (split)
 (use "x1=1")
 (use "RealEqRefl")
 (autoreal)
 (split)
 (simpreal "x=x1")
 (simpreal "x1=1")
 (ng)
 (use "RatEqvToRealEq")
 (use "Truth")
 (use "RealEqRefl")
 (autoreal)
;; Assertion proved.
(assume "Assertion")
(use "Assertion")
(intro 0 (pt "RealPlus 1 0"))
(split)
(use "RatEqvToRealEq")
(use "Truth")
(use "RatEqvToRealEq")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "CoIOne")
;; ok, CoIOne has been added as a new theorem.
;; ok, program constant cCoIOne: ai
;; of t-degree 0 and arity 0 added

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)
;; (CoRec rea=>ai)1([x]SdR pair(InR rea ai)x)

(add-sound "CoIOne")
;; > ok, CoIOneSound has been added as a new theorem:

;; CoIMR 1 cCoIOne

;; with computation rule

;; cCoIOne eqd(CoRec rea=>ai)1([x]SdR pair(InR rea ai)x)

;; (cp "CoIOneSound")

(deanimate "CoIOne")

;; CoIIntNOne
(set-goal "CoI(IntN 1)")
(assert "allnc x(exl x0(x0===IntN 1 andi x===x0) -> CoI x)")
 (assume "x2" "ExHyp2")
 (coind "ExHyp2")
 (drop "ExHyp2")
 (assume "x" "xProp")
 (by-assume "xProp" "x1" "x1Prop")
 (elim "x1Prop")
 (drop "x1Prop")
 (assume "x1= ~1" "x=x1")
 (intro 0 (pt "IntN 1"))
 (intro 0 (pt "x1"))
 (intro 0 (pt "x"))
 (split)
 (use "InitSdSdL")
 (split)
 (autoreal)
 (split)
 (simpreal "x1= ~1")
 (ng #t)
 (use "RatLeToRealLe")
 (use "Truth")
 (split)
 (intro 1)
 (intro 0 (pt "x1"))
 (split)
 (use "x1= ~1")
 (use "RealEqRefl")
 (autoreal)
 (split)
 (simpreal "x=x1")
 (simpreal "x1= ~1")
 (ng #t)
 (use "RatEqvToRealEq")
 (use "Truth")
 (use "RealEqRefl")
 (autoreal)
;; Assertion proved.
(assume "Assertion")
(use "Assertion")
(intro 0 (pt "RealPlus ~1 0"))
(ng #t)
(split)
(use "RatEqvToRealEq")
(use "Truth")
(use "RatEqvToRealEq")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "CoIIntNOne")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)
;; (CoRec rea=>ai)IntN 1([x]SdL pair(InR rea ai)x)

(add-sound "CoIIntNOne")
;; ok, CoIIntNOneSound has been added as a new theorem:

;; CoIMR(IntN 1)cCoIIntNOne

;; with computation rule

;; cCoIIntNOne eqd(CoRec rea=>ai)IntN 1([x]SdL pair(InR rea ai)x)

;; (cp "CoIIntNOneSound")

(deanimate "CoIIntNOne")

;; CoINegToCoIPlusOne
(set-goal "allnc x(exr y(CoI y andi y<<=0 andi x===y+1) -> CoI x)")
(assume "x")
(coind)
(drop 1)
(assume "x0" "ExHyp")
(by-assume "ExHyp" "y" "yProp")
(elim "yProp")
(drop "yProp")
(assume "CoIy" "Conj")
(inst-with-to "CoIClosure" (pt "y") "CoIy"  "CoIClosureInst")
(by-assume "CoIClosureInst" "d" "dProp")
(by-assume "dProp" "x1" "dx1Prop")
(elim "dx1Prop")
(drop "dx1Prop")
(assume "Sdd" "Conj1")
(elim "Conj1")
(drop "Conj1")
(assume "CoIx1")
(assert "abs x1<<=1")
 (use "CoIToBd")
 (use "CoIx1")
(assume "x1Bd")
(elim "Sdd")
;; 30-32
;; Case d=1
(assume "yDef")
(intro 0 (pt "IntP 1"))
(intro 0 (pt "RealPlus 1 0"))
(intro 0 (pt "RealPlus 1 0"))
(ng #t)
(split)
(use "InitSdSdR")
(split)
(autoreal)
(split)
(use "RatLeToRealLe")
(use "Truth")
(split)
(intro 0)
(use "CoIOne")
(split)
(use "RatEqvToRealEq")
(use "Truth")
(assert "x1=== ~1")
(use "RealLeAntiSym")
;; 53,54
;; ?_53:x1<<= ~1
(use "RealLeTrans" (pt "x1+1+ ~1"))
(simpreal "<-" "RealPlusAssoc")
(ng #t)
(simpreal "RealPlusZero")
(use "RealLeRefl")
(autoreal)
(use "RealLeTrans" (pt "RealPlus 0 ~1"))
(use "RealLeMonPlus")
(use "RealLeTrans" (pt "2*((1#2)*(x1+1))"))
(simpreal "RealTimesAssoc")
(ng #t)
(simpreal "RealOneTimes")
(use "RealLeRefl")
(autoreal)
(use "RealLeTrans" (pt "RealTimes 2 0"))
(use "RealLeMonTimes")
(use "RealNNegPos")
(simpreal "<-" "yDef")
(use "Conj")
(use "RatLeToRealLe")
(use "Truth")
(use "RatLeToRealLe")
(use "Truth")
(use "RatLeToRealLe")
(use "Truth")
;; ?_54:~1<<=x1
(use "RealLeTrans" (pt "~abs x1"))
(use "RealLeTrans" (pt "~(RealPlus 0 1)"))
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeUMinus")
(use "x1Bd")
(use "RealLeTrans" (pt "~ ~x1"))
(use "RealLeUMinus")
(simpreal "<-" "RealAbsUMinus")
(use "RealLeAbsId")
(autoreal)
(simpreal "RealUMinusUMinus")
(use "RealLeRefl")
(autoreal)
;; Assertion proved.
(assume "x1=-1")
(simpreal "Conj")
(simpreal "yDef")
(simpreal "x1=-1")
(use "RatEqvToRealEq")
(use "Truth")
;; 31
;; Case d=0
(assume "yDef")
(intro 0 (pt "IntP 1"))
(intro 0 (pt "2*y+1"))
(intro 0 (pt "y+1"))
(split)
(use "InitSdSdR")
(split)
(autoreal)
(split)
(use "RealLeAbs")
;; 117,118
;; ?_117:2*y+1<<=1
(use "RealLeTrans" (pt "RealPlus 0 1"))
(use "RealLeMonPlus")
(use "RealLeTrans" (pt "RealTimes 2 0"))
(use "RealLeMonTimes")
(use "RealNNegPos")
(use "Conj")
(use "RatLeToRealLe")
(use "Truth")
(use "RatLeToRealLe")
(use "Truth")
(use "RatLeToRealLe")
(use "Truth")
;; ?_118:~(2*y+1)<<=1
(simpreal "RealUMinusPlus")
(use "RealLeTrans" (pt "RealPlus 1 0"))
(use "RealLeMonPlus")
(simpreal "yDef")
(simpreal "RealTimesAssoc")
(ng #t)
(simpreal "RealOneTimes")
(simpreal "RealPlusZero")
(use "RealLeTrans" (pt "abs x1"))
(simpreal "<-" "RealAbsUMinus")
(use "RealLeAbsId")
(autoreal)
(use "x1Bd")
(autoreal)
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeRefl")
(autoreal)
;; 116
(split)
(intro 1)
(intro 0 (pt "x1"))
(split)
(use "CoIx1")
(split)
(use "RealLeTrans" (pt "2*((1#2)*x1)"))
(simpreal "RealTimesAssoc")
(ng #t)
(simpreal "RealOneTimes")
(use "RealLeRefl")
(autoreal)
(use "RealLeTrans" (pt "RealTimes 2 0"))
(use "RealLeMonTimes")
(use "RealNNegPos")
(use "RealLeTrans" (pt "(1#2)*(x1+0)"))
(simpreal "RealPlusZero")
(use "RealLeRefl")
(autoreal)
(simpreal "<-" "yDef")
(use "Conj")
(use "RatLeToRealLe")
(use "Truth")
(simpreal "yDef")
(simpreal "RealTimesAssoc")
(ng #t)
(simpreal "RealOneTimes")
(simpreal "RealPlusZero")
(use "RealEqRefl")
(autoreal)
;; 155
(split)
(simpreal "<-" "RealPlusAssoc")
(ng #t)
(simpreal "RealTimesPlusDistr")
(simpreal "RealTimesAssoc")
(ng #t)
(simpreal "RealOneTimes")
(use "RealEqRefl")
(autoreal)
(use "Conj")
;; 32
;; Case d= ~1
(assume "yDef")
(intro 0 (pt "IntP 1"))
(intro 0 (pt "x1"))
(intro 0 (pt "x0"))
(split)
(use "InitSdSdR")
(split)
(autoreal)
(split)
(use "x1Bd")
(split)
(intro 0)
(use "CoIx1")
(split)
(simpreal "Conj")
(simpreal "yDef")
(simpreal "RealTimesPlusDistr")
(ng #t)
(simpreal "RealTimesPlusDistr")
(ng #t)
(simpreal "<-" "RealPlusAssoc")
(ng #t)
(use "RealEqRefl")
(autoreal)
(use "RealEqRefl")
(use "RealEqElim0" (pt "y+1"))
(use "Conj")
;; Proof finished.
;; (cdp)
(save "CoINegToCoIPlusOne")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [u](CoRec ai=>ai)u
;;  ([u0][case (cCoIClosure u0)
;;      (s pair u1 -> 
;;      [case s
;;        (SdR -> SdR pair InL cCoIOne)
;;        (SdM -> SdR pair InR u1)
;;        (SdL -> SdR pair InL u1)])])

(add-sound "CoINegToCoIPlusOne")
;; ok, CoINegToCoIPlusOneSound has been added as a new theorem:

;; allnc x,u^(
;;  (ExRTMR rea
;;    ai
;;    (cterm (y,u^0) 
;;    (AndLMR (cterm (u^1) CoIMR y u^1) (cterm () y<<=0 andnc x===y+1))u^0))
;;  u^ -> 
;;  CoIMR x(cCoINegToCoIPlusOne u^))

;; with computation rule

;; cCoINegToCoIPlusOne eqd
;; ([u]
;;   (CoRec ai=>ai)u
;;   ([u0]
;;     [if (cCoIClosure u0)
;;       ([s,u1]
;;        [if s
;;          (SdR pair(InL ai ai)cCoIOne)
;;          (SdR pair(InR ai ai)u1)
;;          (SdR pair(InL ai ai)u1)])]))

;; (cp "CoINegToCoIPlusOneSound")

(deanimate "CoINegToCoIPlusOne")

;; CoIPosToCoIMinusOne
(set-goal "allnc x(exr y(CoI y andi 0<<=y andi x===y+ ~1) -> CoI x)")
(assume "x")
(coind)
(drop 1)
(assume "x0" "ExHyp")
(by-assume "ExHyp" "y" "yProp")
(elim "yProp")
(drop "yProp")
(assume "CoIy" "Conj")
(inst-with-to "CoIClosure" (pt "y") "CoIy"  "CoIClosureInst")
(by-assume "CoIClosureInst" "d" "dProp")
(by-assume "dProp" "x1" "dx1Prop")
(elim "dx1Prop")
(drop "dx1Prop")
(assume "Sdd" "Conj1")
(elim "Conj1")
(drop "Conj1")
(assume "CoIx1")
(assert "abs x1<<=1")
 (use "CoIToBd")
 (use "CoIx1")
(assume "x1Bd")
(elim "Sdd")
;; 30-32
;; Case d=1
(assume "yDef")
(intro 0 (pt "IntN 1"))
(intro 0 (pt "x1"))
(intro 0 (pt "x0"))
(split)
(use "InitSdSdL")
(split)
(autoreal)
(split)
(use "x1Bd")
(split)
(intro 0)
(use "CoIx1")
(split)
(simpreal "Conj")
(simpreal "yDef")
(simpreal "RealTimesPlusDistr")
(ng #t)
(simpreal "RealTimesPlusDistr")
(ng #t)
(simpreal "<-" "RealPlusAssoc")
(ng #t)
(use "RealEqRefl")
(autoreal)
(use "RealEqRefl")
(use "RealEqElim0" (pt "y+ ~1"))
(use "Conj")
;; 30
;; Case d=0
(assume "yDef")
(intro 0 (pt "IntN 1"))
(intro 0 (pt "2*y+ ~1"))
(intro 0 (pt "y+ ~1"))
(split)
(use "InitSdSdL")
(split)
(autoreal)
(split)
(use "RealLeAbs")
;; 77,78
;; ?_77:2*y+ ~1<<=1
(use "RealLeTrans" (pt "(RealTimes 2 1)+ ~1"))
(use "RealLeMonPlus")
(use "RealLeMonTimes")
(use "RealNNegPos")
(use "RealLeTrans" (pt "abs y"))
(use "RealLeAbsId")
(autoreal)
(use "CoIToBd")
(use "CoIy")
(use "RatLeToRealLe")
(use "Truth")
(use "RatLeToRealLe")
(use "Truth")
(simpreal "RealUMinusPlus")
(ng #t)
(simpreal "<-" "RealTimesIdUMinus")
(use "RealLeTrans" (pt "(RealTimes 2 0)+1"))
(use "RealLeMonPlus")
(use "RealLeMonTimes")
(use "RealNNegPos")
(use "RealLeUMinusInv")
(simpreal "RealUMinusUMinus")
(use "Conj")
(autoreal)
(use "RatLeToRealLe")
(use "Truth")
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
;; 76
(split)
(intro 1)
(intro 0 (pt "x1"))
(split)
(use "CoIx1")
(split)
(use "RealLeTrans" (pt "2*y"))
(use "RealLeTrans" (pt "RealTimes 2 0"))
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeMonTimes")
(use "RealNNegPos")
(use "Conj")
(simpreal "yDef")
(simpreal "RealPlusZero")
(simpreal "RealTimesAssoc")
(ng #t)
(simpreal "RealOneTimes")
(use "RealLeRefl")
(autoreal)
(simpreal "yDef")
(simpreal "RealPlusZero")
(simpreal "RealTimesAssoc")
(ng #t)
(simpreal "RealOneTimes")
(use "RealEqRefl")
(autoreal)
;; 110
(split)
(simpreal "RealTimesPlusDistr")
(simpreal "RealTimesPlusDistr")
(ng #t)
(simpreal "RealTimesAssoc")
(ng #t)
(simpreal "<-" "RealPlusAssoc")
(ng #t)
(simpreal "RealOneTimes")
(use "RealEqRefl")
(autoreal)
(use "Conj")
;; 31
;; Case d= ~1
(assume "yDef")
(intro 0 (pt "IntN 1"))
(intro 0 (pt "RealPlus ~1 0 "))
(intro 0 (pt "RealPlus ~1 0 "))
(ng #t)
(split)
(use "InitSdSdL")
(split)
(autoreal)
(split)
(use "RatLeToRealLe")
(use "Truth")
(split)
(intro 0)
(use "CoIIntNOne")
(split)
(use "RatEqvToRealEq")
(use "Truth")
(use "RealLeAntiSym")
;; 188,189
;; ?_188:x0<<=IntN 1
(simpreal "Conj")
(use "RealLeTrans" (pt "RealPlus 0 ~1"))
(use "RealLeMonPlus")
(simpreal "yDef")
(use "RealLeTrans" (pt "(1#2)*(RealPlus 1 ~1)"))
(use "RealLeMonTimes")
(use "RealNNegPos")
(use "RealLeMonPlus")
(use "RealLeTrans" (pt "abs x1"))
(use "RealLeAbsId")
(autoreal)
(use "x1Bd")
(use "RatLeToRealLe")
(use "Truth")
(use "RatLeToRealLe")
(use "Truth")
(use "RatLeToRealLe")
(use "Truth")
(use "RatLeToRealLe")
(use "Truth")
(simpreal "Conj")
(use "RealLeTrans" (pt "RealPlus 0 ~1"))
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeMonPlus")
(use "Conj")
(use "RatLeToRealLe")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "CoIPosToCoIMinusOne")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [u](CoRec ai=>ai)u
;;  ([u0][case (cCoIClosure u0)
;;      (s pair u1 -> 
;;      [case s
;;        (SdR -> SdL pair InL u1)
;;        (SdM -> SdL pair InR u1)
;;        (SdL -> SdL pair InL cCoIIntNOne)])])

(add-sound "CoIPosToCoIMinusOne")
;; ok, CoIPosToCoIMinusOneSound has been added as a new theorem:

;; allnc x,u^(
;;  (ExRTMR rea
;;    ai
;;    (cterm (y,u^0) 
;;    (AndLMR (cterm (u^1) CoIMR y u^1) (cterm () 0<<=y andnc x===y+ ~1))u^0))
;;  u^ -> 
;;  CoIMR x(cCoIPosToCoIMinusOne u^))

;; with computation rule

;; cCoIPosToCoIMinusOne eqd
;; ([u]
;;   (CoRec ai=>ai)u
;;   ([u0]
;;     [if (cCoIClosure u0)
;;       ([s,u1]
;;        [if s
;;          (SdL pair(InL ai ai)u1)
;;          (SdL pair(InR ai ai)u1)
;;          (SdL pair(InL ai ai)cCoIIntNOne)])]))

;; (cp "CoIPosToCoIMinusOneSound")

(deanimate "CoIPosToCoIMinusOne")

;; CoIToCoIDouble
(set-goal "allnc x(CoI x -> abs x<<=(1#2) -> CoI(2*x))")
(assume "x" "CoIx" "LeHyp")
(inst-with-to "CoIClosure" (pt "x") "CoIx" "CoIClosureInst")
(by-assume "CoIClosureInst" "d" "dProp")
(by-assume "dProp" "x1" "dx1Prop")
(elim "dx1Prop")
(drop "dx1Prop")
(assume "Sdd" "Conj")
(elim "Conj")
(drop "Conj")
(assume "CoIx1")
(assert "abs x1<<=1")
 (use "CoIToBd")
 (use "CoIx1")
(assume "x1Bd")
(elim "Sdd")
;; 21-23
;; Case d=1
(assume "xDef")
(simpreal "xDef")
(simpreal "RealTimesAssoc")
(ng #t)
(simpreal "RealOneTimes")
(use "CoINegToCoIPlusOne")
(intro 0 (pt "x1"))
(split)
(use "CoIx1")
(split)
(use "RealLeTrans" (pt "2*((1#2)*(x1+1+ ~1))"))
(simpreal "RealTimesAssoc")
(simpreal "<-" "RealPlusAssoc")
(ng #t)
(simpreal "RealPlusZero")
(simpreal "RealOneTimes")
(use "RealLeRefl")
(autoreal)
(simpreal "RealTimesPlusDistr")
(simpreal "<-" "xDef")
(simpreal "RealTimesPlusDistr")
(ng #t)
(use "RealLeTrans" (pt "RealPlus 1 ~1"))
(use "RealLeMonPlus")
(use "RealLeTrans" (pt "RealTimes 2 abs x"))
(use "RealLeMonTimes")
(use "RealNNegPos")
(use "RealLeAbsId")
(autoreal)
(use "RealLeTrans" (pt "RealTimes 2(1#2)"))
(use "RealLeMonTimes")
(use "RealNNegPos")
(use "LeHyp")
(use "RatLeToRealLe")
(use "Truth")
(use "RatLeToRealLe")
(use "Truth")
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; 22
;; Case d=0
(assume "xDef")
(assert "2*x===x1")
 (simpreal "xDef")
 (simpreal "RealTimesAssoc")
 (ng #t)
 (simpreal "RealOneTimes")
 (simpreal "RealPlusZero")
 (use "RealEqRefl")
 (autoreal)
(assume "2x=x1")
(simpreal "2x=x1")
(use "CoIx1")
;; 23
;; Case d= ~1
(assume "xDef")
(simpreal "xDef")
(simpreal "RealTimesAssoc")
(ng #t)
(simpreal "RealOneTimes")
(use "CoIPosToCoIMinusOne")
(intro 0 (pt "x1"))
(split)
(use "CoIx1")
(split)
(use "RealLeTrans" (pt "2*((1#2)*(x1+IntN 1 + 1))"))
(simpreal "RealTimesPlusDistr")
(simpreal "<-" "xDef")
(ng #t)
(simpreal "RealTimesPlusDistr")
(use "RealLeTrans" (pt "RealPlus ~1 1"))
(use "RealLeRefl")
(autoreal)
(use "RealLeMonPlus")
(use "RealLeUMinusInv")
(ng #t)
(use "RealLeTrans" (pt "abs ~(2*x)"))
(use "RealLeAbsId")
(autoreal)
(simpreal "RealAbsUMinus")
(simpreal "RealAbsTimes")
(ng #t)
(use "RealLeTrans" (pt "RealTimes 2 (1#2)"))
(use "RealLeMonTimes")
(use "RealNNegPos")
(use "LeHyp")
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
(simpreal "RealTimesAssoc")
(simpreal "<-" "RealPlusAssoc")
(ng #t)
(simpreal "RealOneTimes")
(simpreal "RealPlusZero")
(use "RealLeRefl")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "CoIToCoIDouble")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [u][case (cCoIClosure u)
;;    (s pair u0 -> 
;;    [case s
;;      (SdR -> cCoICompat(cCoICompat(cCoICompat(cCoINegToCoIPlusOne u0))))
;;      (SdM -> cCoICompat u0)
;;      (SdL -> cCoICompat(cCoICompat(cCoICompat(cCoIPosToCoIMinusOne u0))))])]

(add-sound "CoIToCoIDouble")
;; ok, CoIToCoIDoubleSound has been added as a new theorem:

;; allnc x,u^(CoIMR x u^ -> abs x<<=(1#2) -> CoIMR(2*x)(cCoIToCoIDouble u^))

;; with computation rule

;; cCoIToCoIDouble eqd
;; ([u]
;;   [if (cCoIClosure u)
;;     ([s,u0]
;;      [if s
;;        (cCoICompat(cCoICompat(cCoICompat(cCoINegToCoIPlusOne u0))))
;;        (cCoICompat u0)
;;        (cCoICompat(cCoICompat(cCoICompat(cCoIPosToCoIMinusOne u0))))])])

;; (cp "CoIToCoIDoubleSound")

(deanimate "CoIToCoIDouble")

;; CoIToCoIQuad
(set-goal "allnc x(CoI x -> abs x<<=(1#4) -> CoI(4*x))")
(assume "x" "CoIx" "LeHyp")
(assert "4*x===2*(2*x)")
(simpreal "RealTimesAssoc")
(ng #t)
(use "RealEqRefl")
(autoreal)
;; Assertion proved
(assume "EqHyp")
(simpreal "EqHyp")
(use "CoIToCoIDouble")
(use "CoIToCoIDouble")
(use "CoIx")
(use "RealLeTrans" (pt "RealPlus 0(1#4)"))
(ng #t)
(use "LeHyp")
(ng #t)
(use "RatLeToRealLe")
(use "Truth")
(simpreal "RealAbsTimes")
(ng #t)
(use "RealLeTrans" (pt "RealTimes 2(1#4)"))
(use "RealLeMonTimes")
(use "RealNNegPos")
(use "LeHyp")
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
;; Proof finished.
;; (cdp)
(save "CoIToCoIQuad")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [u]cCoICompat(cCoIToCoIDouble(cCoIToCoIDouble u))

(add-sound "CoIToCoIQuad")
;; ok, CoIToCoIQuad has been added as a new theorem.
;; ok, program constant cCoIToCoIQuad: ai=>ai
;; of t-degree 0 and arity 0 added
;; > > > [u]cCoICompat(cCoIToCoIDouble(cCoIToCoIDouble u))
;; > ok, CoIToCoIQuadSound has been added as a new theorem:

;; allnc x,u^(CoIMR x u^ -> abs x<<=(1#4) -> CoIMR(4*x)(cCoIToCoIQuad u^))

;; with computation rule

;; cCoIToCoIQuad eqd([u]cCoICompat(cCoIToCoIDouble(cCoIToCoIDouble u)))

;; (cp "CoIToCoIQuadSound")

(deanimate "CoIToCoIQuad")

;; CoIDivSatCoIClAuxR
(set-goal "allnc x,y(CoI x -> CoI y -> (1#4)<<=y -> abs x<<=y -> 0<<=x -> 
 CoI(4*((1#2)*(x+ ~((1#2)*y)))))")
(assume "x" "y" "CoIx" "CoIy" "yLBd" "xBd" "0<<=x")
(use "CoIToCoIQuad")
(use "CoIAverage")
(use "CoIx")
(use "CoIUMinus")
(simpreal "RealUMinusUMinus")
(simpreal (pf "y===y+0"))
(use "CoIClosureInv")
(use "InitSdSdM")
(use "CoIy")
(simpreal "RealPlusZero")
(use "RealEqRefl")
(autoreal)
;; ?_4:abs((1#2)*(x+ ~((1#2)*y)))<<=(1#4)
(simpreal (pf "((1#2)*(x+ ~((1#2)*y)))===(1#4)*(4*((1#2)*(x+ ~((1#2)*y))))"))
(simpreal "RealAbsTimes")
(use "RealLeTrans" (pt "abs(1#4)*y"))
(use "RealLeMonTimes")
(use "RatNNegToRealNNeg")
(use "Truth")
(use "DivAuxBdR")
(use "0<<=x")
(use "RealLeTrans" (pt "abs x"))
(use "RealLeAbsId")
(autoreal)
(use "xBd")
(ng #t)
(use "RealLeTrans" (pt "RealTimes(1#4)1"))
(use "RealLeMonTimes")
(use "RealNNegPos")
(use "RealLeTrans" (pt "abs y"))
(use "RealLeAbsId")
(autoreal)
(use "CoIToBd")
(use "CoIy")
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
;; ?_18:(1#2)*(x+ ~((1#2)*y))===(1#4)*(4*((1#2)*(x+ ~((1#2)*y))))
(simpreal "RealTimesAssoc")
(ng #t)
(simpreal "RealOneTimes")
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "CoIDivSatCoIClAuxR")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [u,u0]
;;  cCoIToCoIQuad
;;  (cCoIAverage u(cCoIUMinus(cCoICompat(cCoICompat(cCoIClosureInv SdM u0)))))

(add-sound "CoIDivSatCoIClAuxR")
;; ok, CoIDivSatCoIClAuxRSound has been added as a new theorem:

;; allnc x,y,u^(
;;  CoIMR x u^ -> 
;;  allnc u^0(
;;   CoIMR y u^0 -> 
;;   (1#4)<<=y -> 
;;   abs x<<=y -> 
;;   0<<=x -> CoIMR(4*((1#2)*(x+ ~((1#2)*y))))(cCoIDivSatCoIClAuxR u^ u^0)))

;; with computation rule

;; cCoIDivSatCoIClAuxR eqd
;; ([u,u0]
;;   cCoIToCoIQuad
;;   (cCoIAverage u(cCoIUMinus(cCoICompat(cCoICompat(cCoIClosureInv SdM u0))))))

;; (cp "CoIDivSatCoIClAuxRSound")

(deanimate "CoIDivSatCoIClAuxR")

;; CoIDivSatCoIClAuxL
(set-goal "allnc x,y(CoI x -> CoI y -> (1#4)<<=y -> abs x<<=y -> x<<=0 -> 
 CoI(4*((1#2)*(x+(1#2)*y))))")
(assume "x" "y" "CoIx" "CoIy" "yLBd" "xBd" "x<<=0")
(use "CoIToCoIQuad")
(use "CoIAverage")
(use "CoIx")
(simpreal (pf "y===y+0"))
(use "CoIClosureInv")
(use "InitSdSdM")
(use "CoIy")
(simpreal "RealPlusZero")
(use "RealEqRefl")
(autoreal)
;; ?_4:abs((1#2)*(x+(1#2)*y))<<=(1#4)
(simpreal (pf "((1#2)*(x+(1#2)*y))===(1#4)*(4*((1#2)*(x+(1#2)*y)))"))
(simpreal "RealAbsTimes")
(use "RealLeTrans" (pt "abs(1#4)*y"))
(use "RealLeMonTimes")
(use "RatNNegToRealNNeg")
(use "Truth")
(use "DivAuxBdL")
(use "x<<=0")
(use "xBd")
;; ?_20:abs(1#4)*y<<=(1#4)
(ng #t)
(use "RealLeTrans" (pt "RealTimes(1#4) 1"))
(use "RealLeMonTimes")
(use "RealNNegPos")
(use "RealLeTrans" (pt "abs y"))
(use "RealLeAbsId")
(autoreal)
(use "CoIToBd")
(use "CoIy")
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
;; ?_15:(1#2)*(x+(1#2)*y)===(1#4)*(4*((1#2)*(x+(1#2)*y)))
(simpreal "RealTimesAssoc")
(ng #t)
(simpreal "RealOneTimes")
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "CoIDivSatCoIClAuxL")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [u,u0]cCoIToCoIQuad(cCoIAverage u(cCoICompat(cCoIClosureInv SdM u0)))

(add-sound "CoIDivSatCoIClAuxL")
;; ok, CoIDivSatCoIClAuxLSound has been added as a new theorem:

;; allnc x,y,u^(
;;  CoIMR x u^ -> 
;;  allnc u^0(
;;   CoIMR y u^0 -> 
;;   (1#4)<<=y -> 
;;   abs x<<=y -> 
;;   x<<=0 -> CoIMR(4*((1#2)*(x+(1#2)*y)))(cCoIDivSatCoIClAuxL u^ u^0)))

;; with computation rule

;; cCoIDivSatCoIClAuxL eqd
;; ([u,u0]cCoIToCoIQuad(cCoIAverage u(cCoICompat(cCoIClosureInv SdM u0))))

;; (cp "CoIDivSatCoIClAuxLSound")

(deanimate "CoIDivSatCoIClAuxL")

;; (set! COMMENT-FLAG #f)
;; CoIDivSatCoICl
(set-goal "allnc x,y(CoI x -> CoI y -> (1#4)<<=y -> abs x<<=y ->
 exr d0,x0(Sd d0 andi CoI x0 andi abs x0<<=y andi
 x*RealUDiv y 3===(1#2)*(x0*RealUDiv y 3+d0)))")
(assume "x" "y" "CoIx" "CoIy" "yLBd" "xBd")
;; Let d1,d2,d3 be the first three digits of x.
;; We first distinguish cases on the most significant digit d1
(inst-with-to "CoIClosure" (pt "x") "CoIx" "CoIClosureInst1")
(by-assume "CoIClosureInst1" "d1" "d1Prop")
(by-assume "d1Prop" "x1" "d1x1Prop")
(elim "d1x1Prop")
(assume "Sdd1")
(elim "Sdd1")
;; 13-15
;; Case d1=1
(assume "Conj11")
(elim "Conj11")
(assume "CoIx1")
(assert "abs x1<<=1")
 (use "CoIToBd")
 (use "CoIx1")
(assume "x1Bd" "Eq1")
(drop "d1x1Prop" "Conj11")
;; Next we show 0<<=x from x===(1#2)*(x1+1) using x1Bd
(assert "0<<=x")
 (simpreal "Eq1")
 (use "RealLeTrans" (pt "(1#2)*(RealUMinus 1+1)"))
 (ng)
 (use "RatLeToRealLe")
 (use "Truth")
 (use "RealLeMonTimes")
 (use "RatNNegToRealNNeg")
 (use "Truth")
 (use "RealLeMonPlus")
 (use "RealLeAbsInv")
 (autoreal)
 (use "x1Bd")
 (use "RatLeToRealLe")
 (use "Truth")
(assume "0<<=x")
;; Now we define d and x0
(intro 0 (pt "IntP 1"))
(intro 0 (pt "4*((1#2)*(x+ ~((1#2)*y)))"))
(split)
(use "InitSdSdR")
(split)
(use "CoIDivSatCoIClAuxR")
(use "CoIx")
(use "CoIy")
(use "yLBd")
(use "xBd")
(use "0<<=x")
;; ?_45:abs(4*((1#2)*(x+ ~((1#2)*y))))<<=y andnc 
;;      x*RealUDiv y 3===(1#2)*(4*((1#2)*(x+ ~((1#2)*y)))*RealUDiv y 3+1)
(split)
(use "DivAuxBdR")
(use "0<<=x")
(use "RealLeTrans" (pt "abs x"))
(use "RealLeAbsId")
(autoreal)
(use "xBd")
;; ?_52:x*RealUDiv y 3===(1#2)*(4*((1#2)*(x+ ~((1#2)*y)))*RealUDiv y 3+1)
(use "DivAuxEqR")
(autoreal)
(use "yLBd")
;; 14
;; Case d1=0.
(assume "Conj11")
(elim "Conj11")
(assume "CoIx1")
(assert "abs x1<<=1")
 (use "CoIToBd")
 (use "CoIx1")
(assume "x1Bd" "Eq1")
(drop "d1x1Prop" "Conj11")
(inst-with-to "CoIClosure" (pt "x1") "CoIx1" "CoIClosureInst2")
(by-assume "CoIClosureInst2" "d2" "d2Prop")
(by-assume "d2Prop" "x2" "d2x2Prop")
(elim "d2x2Prop")
(assume "Sdd2")
;; We now distinguish cases on d2
(elim "Sdd2")
;; 79-81
;; Case d1=0, d2=1
(assume "Conj21")
(elim "Conj21")
(assume "CoIx2")
(assert "abs x2<<=1")
 (use "CoIToBd")
 (use "CoIx2")
(assume "x2Bd" "Eq2")
(drop "d2x2Prop" "Conj21")
;; Next we show 0<<=x from x===(1#2)*(x1+0) and x1===(1#2)*(x2+1)
(assert "0<<=x")
 (simpreal "Eq1")
 (simpreal "Eq2")
 (use "RealLeTrans" (pt "(1#2)*((1#2)*(RealUMinus 1+1)+0)"))
 (ng)
 (use "RatLeToRealLe")
 (use "Truth")
 (use "RealLeMonTimes")
 (use "RatNNegToRealNNeg")
 (use "Truth")
 (use "RealLeMonPlus")
 (use "RealLeMonTimes")
 (use "RatNNegToRealNNeg")
 (use "Truth")
 (use "RealLeMonPlus")
 (use "RealLeAbsInv")
 (autoreal)
 (use "x2Bd")
 (use "RatLeToRealLe")
 (use "Truth")
 (use "RatLeToRealLe")
 (use "Truth")
(assume "0<<=x")
;; Now we define d and x0
(intro 0 (pt "IntP 1"))
(intro 0 (pt "4*((1#2)*(x+ ~((1#2)*y)))"))
(split)
(use "InitSdSdR")
(split)
(use "CoIDivSatCoIClAuxR")
(use "CoIx")
(use "CoIy")
(use "yLBd")
(use "xBd")
(use "0<<=x")
;; ?_118:abs(4*((1#2)*(x+ ~((1#2)*y))))<<=y andnc 
;;       x*RealUDiv y 3===(1#2)*(4*((1#2)*(x+ ~((1#2)*y)))*RealUDiv y 3+1)
(split)
(use "DivAuxBdR")
(use "0<<=x")
(use "RealLeTrans" (pt "abs x"))
(use "RealLeAbsId")
(autoreal)
(use "xBd")
;; ?_125:x*RealUDiv y 3===(1#2)*(4*((1#2)*(x+ ~((1#2)*y)))*RealUDiv y 3+1)
(use "DivAuxEqR")
(autoreal)
(use "yLBd")
;; 80
;; Case d1=0, d2=0
(assume "Conj21")
(elim "Conj21")
(assume "CoIx2")
(assert "abs x2<<=1")
 (use "CoIToBd")
 (use "CoIx2")
(assume "x2Bd" "Eq2")
(drop "d2x2Prop" "Conj21")
(inst-with-to "CoIClosure" (pt "x2") "CoIx2" "CoIClosureInst3")
(by-assume "CoIClosureInst3" "d3" "d3Prop")
(by-assume "d3Prop" "x3" "d3x3Prop")
(elim "d3x3Prop")
(assume "Sdd3")
;; We now distinguish cases on d3
(elim "Sdd3")
;; 152-254
;; Case d1=0, d2=0, d3=1
(assume "Conj31")
(elim "Conj31")
(assume "CoIx3")
(assert "abs x3<<=1")
 (use "CoIToBd")
 (use "CoIx3")
(assume "x3Bd" "Eq3")
(drop "d3x3Prop" "Conj31")
;; Next we show 0<<=x from x===(1#2)*(x1+0) x1===(1#2)*(x2+0) x2===(1#2)*(x3+1)
(assert "0<<=x")
 (simpreal "Eq1")
 (simpreal "Eq2")
 (simpreal "Eq3")
 (use "RealLeTrans" (pt "(1#2)*((1#2)*((1#2)*(RealUMinus 1+1)+0)+0)"))
 (ng)
 (use "RatLeToRealLe")
 (use "Truth")
 (use "RealLeMonTimes")
 (use "RatNNegToRealNNeg")
 (use "Truth")
 (use "RealLeMonPlus")
 (use "RealLeMonTimes")
 (use "RatNNegToRealNNeg")
 (use "Truth")
 (use "RealLeMonPlus")
 (use "RealLeMonTimes")
 (use "RatNNegToRealNNeg")
 (use "Truth")
 (use "RealLeMonPlus")
 (use "RealLeAbsInv")
 (autoreal)
 (use "x3Bd")
 (use "RatLeToRealLe")
 (use "Truth")
 (use "RatLeToRealLe")
 (use "Truth")
 (use "RatLeToRealLe")
 (use "Truth")
(assume "0<<=x")
;; Now we define d and x0
(intro 0 (pt "IntP 1"))
(intro 0 (pt "4*((1#2)*(x+ ~((1#2)*y)))"))
(split)
(use "InitSdSdR")
(split)
(use "CoIDivSatCoIClAuxR")
(use "CoIx")
(use "CoIy")
(use "yLBd")
(use "xBd")
(use "0<<=x")
;; ?_198:abs(4*((1#2)*(x+ ~((1#2)*y))))<<=y andnc 
;;       x*RealUDiv y 3===(1#2)*(4*((1#2)*(x+ ~((1#2)*y)))*RealUDiv y 3+1)
(split)
(use "DivAuxBdR")
(use "0<<=x")
(use "RealLeTrans" (pt "abs x"))
(use "RealLeAbsId")
(autoreal)
(use "xBd")
;; ?_205:x*RealUDiv y 3===(1#2)*(4*((1#2)*(x+ ~((1#2)*y)))*RealUDiv y 3+1)
(use "DivAuxEqR")
(autoreal)
(use "yLBd")
;; 153
;; Case d1=0, d2=0, d3=0
(assume "Conj31")
(elim "Conj31")
(assume "CoIx3")
 (assert "abs x3<<=1")
 (use "CoIToBd")
 (use "CoIx3")
(assume "x3Bd" "Eq3")
(drop "d3x3Prop" "Conj31")
;; We can now pick d=0 and x0 as 2*x
(intro 0 (pt "0"))
(intro 0 (pt "2*x"))
(split)
(use "InitSdSdM")
(split)
(use "CoIToCoIDouble")
(use "CoIx")
(simpreal "Eq1")
(simpreal "RealPlusZero")
(simpreal "RealAbsTimes")
(ng)
(use "RealLeTrans" (pt "RealTimes(1#2)1"))
(use "RealLeMonTimes")
(use"RatNNegToRealNNeg")
(use "Truth")
(use "x1Bd")
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
;; ?_227:abs(2*x)<<=y andnc x*RealUDiv y 3===(1#2)*(2*x*RealUDiv y 3+0)
(split)
(simpreal "RealAbsTimes")
(ng)
(simpreal "Eq1")
(simpreal "RealPlusZero")
(simpreal "RealAbsTimes")
(ng)
(simpreal "RealTimesAssoc")
(ng)
(simpreal "RealOneTimes")
(simpreal "Eq2")
(simpreal "RealPlusZero")
(simpreal "RealAbsTimes")
(ng)
(simpreal "Eq3")
(simpreal "RealPlusZero")
(simpreal "RealAbsTimes")
(ng)
(simpreal "RealTimesAssoc")
(ng)
(use "RealLeTrans" (pt "RealTimes(1#4)1"))
(use "RealLeMonTimes")
(use "RatNNegToRealNNeg")
(use "Truth")
(use "x3Bd")
(use "yLBd")
(autoreal)
;; ?_244:x*RealUDiv y 3===(1#2)*(2*x*RealUDiv y 3+0)
(assert "Real(RealUDiv y 3)")
 (use "RealUDivReal")
 (autoreal)
 (simp (pf "3=PosS 2"))
 (use "RealLeToPos")
 (use "RealLeTrans" (pt "y")) 
 (use "yLBd")
 (use "RealLeAbsId")
 (autoreal)
 (use "Truth")
(assume "R1/y")
(simpreal "RealPlusZero")
(simpreal "RealTimesAssoc")
(simpreal "RealTimesAssoc")
(ng)
(simpreal "RealOneTimes")
(use "RealEqRefl")
(autoreal)
;; 154
;; Case d1=0, d2=0, d3=IntN 1
(assume "Conj31")
(elim "Conj31")
(assume "CoIx3")
(assert "abs x3<<=1")
 (use "CoIToBd")
 (use "CoIx3")
(assume "x3Bd" "Eq3")
(drop "d3x3Prop" "Conj31")
;; Show x<<=0 from x===(1#2)*(x1+0) x1===(1#2)*(x2+0) x2===(1#2)*(x3+IntN 1)
(assert "x<<=0")
 (simpreal "Eq1")
 (simpreal "Eq2")
 (simpreal "Eq3")
 (simpreal "RealPlusZero")
 (simpreal "RealPlusZero")
 (use "RealLeTrans" (pt "(1#2)*((1#2)*((1#2)*(RealPlus 1 IntN 1)))"))
 (use "RealLeMonTimes")
 (use "RatNNegToRealNNeg")
 (use "Truth")
 (use "RealLeMonTimes")
 (use "RatNNegToRealNNeg")
 (use "Truth")
 (use "RealLeMonTimes")
 (use "RatNNegToRealNNeg")
 (use "Truth")
 (use "RealLeMonPlus")
 (use "RealLeTrans" (pt "abs x3"))
 (use "RealLeAbsId")
 (autoreal)
 (use "x3Bd")
 (use "RatLeToRealLe")
 (use "Truth")
 (use "RatLeToRealLe")
 (use "Truth")
 (autoreal)
(assume "x<<=0")
;; Now we define d and x0
(intro 0 (pt "IntN 1"))
(intro 0 (pt "4*((1#2)*(x+(1#2)*y))"))
(split)
(use "InitSdSdL")
(split)
(use "CoIDivSatCoIClAuxL")
(use "CoIx")
(use "CoIy")
(use "yLBd")
(use "xBd")
(use "x<<=0")
;; ?_353:abs(4*((1#2)*(x+(1#2)*y)))<<=y andnc 
;;       x*RealUDiv y 3===(1#2)*(4*((1#2)*(x+(1#2)*y))*RealUDiv y 3+IntN 1)
(split)
(use "DivAuxBdL")
(use "x<<=0")
(use "xBd")
(use "DivAuxEqL")
(autoreal)
(use "yLBd")
;; 81
;; Case d1=0, d2=IntN 1
(assume "Conj21")
(elim "Conj21")
(assume "CoIx2")
(assert "abs x2<<=1")
 (use "CoIToBd")
 (use "CoIx2")
(assume "x2Bd" "Eq2")
(drop "d2x2Prop" "Conj21")
;; Next we show x<<=0 from x===(1#2)*(x1+0) and x1===(1#2)*(x2+IntN 1)
(assert "x<<=0")
 (simpreal "Eq1")
 (simpreal "Eq2")
 (simpreal "RealPlusZero")
 (use "RealLeTrans" (pt "(1#2)*((1#2)*(RealPlus 1 IntN 1))"))
 (use "RealLeMonTimes")
 (use "RatNNegToRealNNeg")
 (use "Truth")
 (use "RealLeMonTimes")
 (use "RatNNegToRealNNeg")
 (use "Truth")
 (use "RealLeMonPlus")
 (use "RealLeTrans" (pt "abs x2"))
 (use "RealLeAbsId")
 (autoreal)
 (use "x2Bd")
 (use "RatLeToRealLe")
 (use "Truth")
 (use "RatLeToRealLe")
 (use "Truth")
 (autoreal)
(assume "x<<=0")
;; Now we define d and x0
(intro 0 (pt "IntN 1"))
(intro 0 (pt "4*((1#2)*(x+(1#2)*y))"))
(split)
(use "InitSdSdL")
(split)
(use "CoIDivSatCoIClAuxL")
(use "CoIx")
(use "CoIy")
(use "yLBd")
(use "xBd")
(use "x<<=0")
;; ?_401:abs(4*((1#2)*(x+(1#2)*y)))<<=y andnc 
;;       x*RealUDiv y 3===(1#2)*(4*((1#2)*(x+(1#2)*y))*RealUDiv y 3+IntN 1)
(split)
(use "DivAuxBdL")
(use "x<<=0")
(use "xBd")
(use "DivAuxEqL")
(autoreal)
(use "yLBd")
;; 15
;; Case d1=IntN 1
(assume "Conj11")
(elim "Conj11")
(assume "CoIx1")
 (assert "abs x1<<=1")
 (use "CoIToBd")
 (use "CoIx1")
(assume "x1Bd" "Eq1")
(drop "d1x1Prop" "Conj11")
;; Next we show x<<=0 from x===(1#2)*(x1+IntN 1) using x1Bd
(assert "x<<=0")
 (simpreal "Eq1")
 (use "RealLeTrans" (pt "(1#2)*(RealPlus 1 IntN 1)"))
 (use "RealLeMonTimes")
 (use "RatNNegToRealNNeg")
 (use "Truth")
 (use "RealLeMonPlus")
 (use "RealLeTrans" (pt "abs x1"))
 (use "RealLeAbsId")
 (autoreal)
 (use "x1Bd")
 (use "RatLeToRealLe")
 (use "Truth")
 (ng)
 (use "RatLeToRealLe")
 (use "Truth")
(assume "x<<=0")
(intro 0 (pt "IntN 1"))
(intro 0 (pt "4*((1#2)*(x+(1#2)*y))"))
(split)
(use "InitSdSdL")
(split)
(use "CoIDivSatCoIClAuxL")
(use "CoIx")
(use "CoIy")
(use "yLBd")
(use "xBd")
(use "x<<=0")
;; ?_444:abs(4*((1#2)*(x+(1#2)*y)))<<=y andnc 
;;       x*RealUDiv y 3===(1#2)*(4*((1#2)*(x+(1#2)*y))*RealUDiv y 3+IntN 1)
(split)
(use "DivAuxBdL")
(use "x<<=0")
(use "xBd")
;; ?_451:x*RealUDiv y 3===(1#2)*(4*((1#2)*(x+(1#2)*y))*RealUDiv y 3+IntN 1)
(use "DivAuxEqL")
(autoreal)
(use "yLBd")
;; Proof finished.
;; (cdp)
(save "CoIDivSatCoICl")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [u,u0]
;;  [case (cCoIClosure u)
;;    (s pair u1 -> 
;;    [case s
;;      (SdR -> SdR pair cCoIDivSatCoIClAuxR u u0)
;;      (SdM -> 
;;      [case (cCoIClosure u1)
;;        (s0 pair u2 -> 
;;        [case s0
;;          (SdR -> SdR pair cCoIDivSatCoIClAuxR u u0)
;;          (SdM -> 
;;          [case (cCoIClosure u2)
;;            (s1 pair u3 -> 
;;            [case s1
;;              (SdR -> SdR pair cCoIDivSatCoIClAuxR u u0)
;;              (SdM -> SdM pair cCoIToCoIDouble u)
;;              (SdL -> SdL pair cCoIDivSatCoIClAuxL u u0)])])
;;          (SdL -> SdL pair cCoIDivSatCoIClAuxL u u0)])])
;;      (SdL -> SdL pair cCoIDivSatCoIClAuxL u u0)])]

;; (set! COMMENT-FLAG #t)

(add-sound "CoIDivSatCoICl")
;; ok, CoIDivSatCoIClSound has been added as a new theorem:

;; allnc x,y,u^(
;;  CoIMR x u^ -> 
;;  allnc u^0(
;;   CoIMR y u^0 -> 
;;   (1#4)<<=y -> 
;;   abs x<<=y -> 
;;   (ExRTMR int
;;     sd yprod ai
;;     (cterm (d,su^) 
;;     (ExRTMR rea
;;       sd yprod ai
;;       (cterm (x0,su^0) 
;;       (AndDMR (cterm (s^) SdMR d s^)
;;         (cterm (u^1) 
;;         (AndLMR (cterm (u^2) CoIMR x0 u^2)
;;           (cterm () 
;;           abs x0<<=y andnc x*RealUDiv y 3===(1#2)*(x0*RealUDiv y 3+d)))
;;         u^1))
;;       su^0))
;;     su^))
;;   (cCoIDivSatCoICl u^ u^0)))

;; with computation rule

;; cCoIDivSatCoICl eqd
;; ([u,u0]
;;   [if (cCoIClosure u)
;;     ([s,u1]
;;      [if s
;;        (SdR pair cCoIDivSatCoIClAuxR u u0)
;;        [if (cCoIClosure u1)
;;         ([s0,u2]
;;          [if s0
;;            (SdR pair cCoIDivSatCoIClAuxR u u0)
;;            [if (cCoIClosure u2)
;;             ([s1,u3]
;;              [if s1
;;                (SdR pair cCoIDivSatCoIClAuxR u u0)
;;                (SdM pair cCoIToCoIDouble u)
;;                (SdL pair cCoIDivSatCoIClAuxL u u0)])]
;;            (SdL pair cCoIDivSatCoIClAuxL u u0)])]
;;        (SdL pair cCoIDivSatCoIClAuxL u u0)])])

;; (cp "CoIDivSatCoIClSound")

(deanimate "CoIDivSatCoICl")

;; CoIDivAux
(set-goal "allnc y(CoI y -> (1#4)<<=y -> allnc z(
 exr x(CoI x andi abs x<<=y andi z===x*RealUDiv y 3) -> CoI z))")
(assume "y" "CoIy" "yLBd" "x")
(assert "RealPos y 3")
 (simp (pf "3=PosS 2"))
 (use "RealLeToPos")
 (use "yLBd")
 (use "Truth")
(assume "0<y")
(assert "Real(RealUDiv y 3)")
 (use "RealUDivReal")
 (realproof)
 (simp (pf "3=PosS 2"))
 (use "RealLeToPos")
 (use "RealLeTrans" (pt "y")) 
 (use "yLBd")
 (use "RealLeAbsId")
 (autoreal)
 (use "Truth")
(assume "R1/y" "ExHyp")
(coind "ExHyp")
(drop "ExHyp")
(assume "x0" "x0Prop")
(by-assume "x0Prop" "x1" "x0x1Prop")
(elim "x0x1Prop")
(assume "CoIx1" "Conj1")
(elim "Conj1")
(assume "x1Bd" "x0Def")
(drop "x0x1Prop" "Conj1")
(inst-with-to "CoIDivSatCoICl"
	      (pt "x1") (pt "y") "CoIx1" "CoIy" "yLBd" "x1Bd"
	      "CoIDivInst")
(by-assume "CoIDivInst" "d" "dProp")
(by-assume "dProp" "x2" "dx2Prop")
(intro 0 (pt "d"))
(intro 0 (pt "x2*RealUDiv y 3"))
(intro 0 (pt "x0"))
(elim "dx2Prop")
(assume "Sdd")
(elim)
(assume "CoIx2" "x2Props")
(drop "dx2Prop")
(split)
(use "Sdd")
(split)
(autoreal)
(split)
;; ?_51:abs(x2*RealUDiv y 3)<<=1
(simpreal "RealAbsTimes")
(simpreal "<-" (pf "y*RealUDiv y 3===1"))
(simpreal "RealAbsUDiv")
(simpreal "RealNNegToUDivAbs")
(use "RealLeMonTimesL")
;; ?_64:RealNNeg(RealUDiv y 3) from RealPos y 3
(use "RealPosToNNegUDiv")
(autoreal)
(use "0<y")
(use "x2Props")
(use "RealPosAbs")
(use "0<y")
(use "RealPosToNNeg" (pt "3"))
(autoreal)
(use "0<y")
(use "0<y")
(autoreal)
(use "RealTimesUDiv")
(autoreal)
(use "0<y")
(use "R1/y")
(autoreal)
;; 52
(split)
(intro 1)
(intro 0 (pt "x2"))
(split)
(use "CoIx2")
(split)
(use "x2Props")
(use "RealEqRefl")
(autoreal)
(split)
(simpreal "x0Def")
(use "x2Props")
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "CoIDivAux")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [u,u0](CoRec ai=>ai)u0
;;  ([u1][case (cCoIDivSatCoICl u1 u) (s pair u2 -> s pair InR u2)])

(add-sound "CoIDivAux")
;; ok, CoIDivAuxSound has been added as a new theorem:

;; allnc y,u^(
;;  CoIMR y u^ -> 
;;  (1#4)<<=y -> 
;;  allnc z,u^0(
;;   (ExRTMR rea
;;     ai
;;     (cterm (x,u^1) 
;;     (AndLMR (cterm (u^2) CoIMR x u^2)
;;       (cterm () abs x<<=y andnc z===x*RealUDiv y 3))
;;     u^1))
;;   u^0 -> 
;;   CoIMR z(cCoIDivAux u^ u^0)))

;; with computation rule

;; cCoIDivAux eqd
;; ([u,u0]
;;   (CoRec ai=>ai)u0
;;   ([u1][if (cCoIDivSatCoICl u1 u) ([s,u2]s pair(InR ai ai)u2)]))

;; (cp "CoIDivAuxSound")

(deanimate "CoIDivAux")

;; CoIDiv
(set-goal "allnc x,y(CoI x -> CoI y -> (1#4)<<=y -> abs x<<=y ->
 CoI(x*(RealUDiv y 3)))")
(assume "x" "y" "CoIx" "CoIy" "(1#4)<<=y" "xBd")
(use "CoIDivAux" (pt "y"))
(use "CoIy")
(use "(1#4)<<=y")
(intro 0 (pt "x"))
(split)
(use "CoIx")
(split)
(use "xBd")
(assert "Real(RealUDiv y 3)")
 (use "RealUDivReal")
 (autoreal)
 (use "RealPosAbs")
 (simp (pf "3=PosS 2"))
 (use "RealLeToPos")
 (use "(1#4)<<=y")
 (use "Truth")
;; Assertion proved.
(assume "Ry/3")
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "CoIDiv")

(add-sound "CoIDiv")
;; ok, CoIDivSound has been added as a new theorem:

;; allnc x,y,u^(
;;  CoIMR x u^ -> 
;;  allnc u^0(
;;   CoIMR y u^0 -> 
;;   (1#4)<<=y -> abs x<<=y -> CoIMR(x*RealUDiv y 3)(cCoIDiv u^ u^0)))

;; with computation rule

;; cCoIDiv eqd([u,u0]cCoIDivAux u0 u)

;; (cp "CoIDivSound")

(deanimate "CoIDiv")

(define CoIDiv-eterm (proof-to-extracted-term (theorem-name-to-proof "CoIDiv")))
(animate "CoIDivAux")
(animate "CoIDivSatCoICl")
(define CoIDiv-neterm (rename-variables (nt CoIDiv-eterm)))
;; (ppc CoIDiv-neterm)

;; [u,u0](CoRec ai=>ai)u
;;  ([u1][case (cCoIClosure u1)
;;      (s pair u2 -> [case s
;;        (SdR -> SdR pair InR(cCoIDivSatCoIClAuxR u1 u0))
;;        (SdM -> [case (cCoIClosure u2)
;;          (s0 pair u3 -> [case s0
;;            (SdR -> SdR pair InR(cCoIDivSatCoIClAuxR u1 u0))
;;            (SdM -> [case (cCoIClosure u3)
;;              (s1 pair u4 -> [case s1
;;                (SdR -> SdR pair InR(cCoIDivSatCoIClAuxR u1 u0))
;;                (SdM -> SdM pair InR(cCoIToCoIDouble u1))
;;                (SdL -> SdL pair InR(cCoIDivSatCoIClAuxL u1 u0))])])
;;            (SdL -> SdL pair InR(cCoIDivSatCoIClAuxL u1 u0))])])
;;        (SdL -> SdL pair InR(cCoIDivSatCoIClAuxL u1 u0))])])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Haskell translation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; terms-to-haskell-program (written by Fredrik Nordvall-Forsberg)
;; generates a Haskell file (here sddivtest.hs).  To run it, in a
;; terminal type ghci sddivtest.hs.  In *Main> one can evaluate the
;; Haskell functions in sddivtest.hs .  Time mesurement by :set +s .
;; To quit type *Main> :q .

'(
(animate "RealToCoI")
(animate "RealToCoIAux")
(animate "ApproxSplitZeroMinusPtFive")
(animate "ApproxSplitZeroPtFive")
(animate "ApproxSplit")
(animate "CoIToCoIDouble")
(animate "CoIToCoIQuad")
(animate "CoIDivSatCoIClAuxL")
(animate "CoIDivSatCoIClAuxR")
(animate "CoIPosToCoIMinusOne")
(animate "CoIUMinus")
(animate "Rht")
(animate "SdUMinus")
(animate "Lft")
(animate "CoINegToCoIPlusOne")
(animate "CoIOne")
(animate "CoIClosure")
(animate "CoIIntNOne")
(animate "CoICompat")
(animate "CoIClosureInv")
(animate "CoIAverage")
(animate "CoIAvcToCoI")
(animate "CoIAvToAvc")
(animate "IntPlusSdToSdtwo")
(animate "CoIClauseInv")
(animate "CoIAvcSatCoICl")
(animate "CoIAvcSatCoIClAuxK")
(animate "CoIAvcSatCoIClAuxJ")

(terms-to-haskell-program
 "~/temp/sddivtest.hs"
 (list (list CoIDiv-eterm "coidiv")
       (list RealToCoI-eterm "realtocoi")
       (list RatToCoI-eterm "rattocoi")
       (list (pt "SdMs") "sdms")
       (list (pt "PtFive") "ptfive")
       (list (pt "MPtFive") "mptfive")
       (list (pt "OneSdR") "onesdr")
       (list (pt "OneSdL") "onesdl")
       (list (pt "SqrtTwoOverTwo") "stot")
       (list (pt "IrrStr") "irrstr")
       (list (pt "AiToReal") "aitoreal")
       (list (pt "TakeStr") "takestr")
       (list (pt "ListSdToRat") "listsdtorat")))
;; ok, output written to file ~/temp/sddivtest.hs

(deanimate "RealToCoI")
(deanimate "RealToCoIAux")
(deanimate "ApproxSplitZeroMinusPtFive")
(deanimate "ApproxSplitZeroPtFive")
(deanimate "ApproxSplit")
(deanimate "CoIToCoIDouble")
(deanimate "CoIToCoIQuad")
(deanimate "CoIDivSatCoIClAuxL")
(deanimate "CoIDivSatCoIClAuxR")
(deanimate "CoIPosToCoIMinusOne")
(deanimate "CoIUMinus")
(deanimate "Rht")
(deanimate "SdUMinus")
(deanimate "Lft")
(deanimate "CoINegToCoIPlusOne")
(deanimate "CoIOne")
(deanimate "CoIClosure")
(deanimate "CoIIntNOne")
(deanimate "CoICompat")
(deanimate "CoIClosureInv")
(deanimate "CoIAverage")
(deanimate "CoIAvcToCoI")
(deanimate "CoIAvToAvc")
(deanimate "IntPlusSdToSdtwo")
(deanimate "CoIClauseInv")
(deanimate "CoIAvcSatCoICl")
(deanimate "CoIAvcSatCoIClAuxK")
(deanimate "CoIAvcSatCoIClAuxJ")
)

;; In a terminal type
;; ghci sddivtest.hs

;; takestr 18 ((coidiv mptfive) ptfive)

;; SdL,SdL,SdL,SdL,SdL,SdL,SdL,SdL,SdL,SdL,SdL,SdL,SdL,SdL,SdL,SdL,SdL,SdL

;; takestr 18 (coidiv (realtocoi (aitoreal (irrstr (\ n -> (n + 1)) 0))) ptfive)

;; SdR,SdR,SdR,SdR,SdR,SdR,SdR,SdR,SdR,SdR,SdR,SdR,SdR,SdR,SdR,SdR,SdR,SdR

;; takestr 18 (coidiv (rattocoi (2 % 7)) ptfive)

;; SdR,SdM,SdR,SdL,SdM,SdR,SdL,SdM,SdR,SdL,SdM,SdR,SdL,SdM,SdR,SdL,SdM,SdR


;; takestr 19 (coidiv (rattocoi (1001 % 3001)) (rattocoi (10001 % 20001)))

;; SdR,SdR,SdL,SdR,SdL,SdR,SdL,SdR,SdL,SdR,SdM,SdR,SdL,SdL,SdR,SdL,SdR,SdR,SdL
;; (0.04 secs, 20,315,816 bytes)

;; Similarly we have
;; number of digits  runtime in seconds
;; 10                0.01
;; 25                0.05
;; 50                0.12
;; 75                0.23
;; 100               0.39
;; 250               2.11
;; 500               7,47
;; 750              17,36
;; 1000             38,48
