;; 2017-12-12.  examples/analysis/sdmult.scm

(load "~/git/minlog/init.scm")

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Multiplication for signed digit code
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; CoIZero
(set-goal "CoI 0")
(assert "allnc x(exl x1(x1===0 andi x===x1) -> CoI x)")
 (assume "x" "ExHyp")
 (coind "ExHyp")
 (by-assume "ExHyp" "x1" "x1Prop")
 (elim "x1Prop")
 (drop "x1Prop")
 (assume "x1=0" "x=x1")
 (assume "x2" "ExHypTwo")
 (by-assume "ExHypTwo" "x3" "x3Prop")
 (elim "x3Prop")
 (assume "x3=0" "x2=x3")
 (intro 0 (pt "0"))
 (intro 0 (pt "x1"))
 (intro 0 (pt "x2"))
 (split)
 (use "InitSdSdM")
 (split)
 (autoreal)
 (split)
 (simpreal "x1=0")
 (ng #t)
 (use "RealLeIntro")
 (use "RealRat")
 (use "RealRat")
 (use "RealNNegPos")
 (split)
 (intro 1)
 (intro 0 (pt "x1"))
 (split)
 (use "x1=0")
 (use "RealEqRefl")
 (autoreal)
 (split)
 (use "RealEqTrans" (pt "x3"))
 (use "x2=x3")
 (use "RealEqTrans" (pt "RealConstr([n](0#1))([p]Zero)"))
 (use "x3=0")
;;   {x}  x1  x1=0:x1===0
;;   x=x1:x===x1
;;   {x2}  x3  x3Prop:x3===0 andnc x2===x3
;;   x3=0:x3===0
;;   x2=x3:x2===x3
;; -----------------------------------------------------------------------------
;; ?_44:0===(1#2)*(x1+0)
(simpreal "x1=0")
(ng #t)
(use "RealEqRefl")
(use "RealRat")
(use "RealEqRefl")
(autoreal)
;; Assertion proved.
(assume "Assertion")
(use "Assertion")
(intro 0 (pt "RealConstr([n](0#1))([p]Zero)"))
(split)
(use "RealEqRefl")
(use "RealRat")
(use "RealEqRefl")
(use "RealRat")
;; Proof finished.
(save "CoIZero")
;; (cdp) ;ok

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; (CoRec rea=>str)0([x]SdM pair(InR rea str)0)

;; CoISdTimes
(set-goal "allnc d,x(Sd d -> CoI x -> CoI(d*x))")
(assume "d" "x" "Sdd")
(elim "Sdd")
;; 3-5
;; Case 1
(assume "CoIx")
(simpreal "RealOneTimes")
(use "CoIx")
(autoreal)
;; 4
;; Case 0
(assume "CoIx")
(simpreal "RealZeroTimes")
(use "CoIZero")
(autoreal)
;; 5
;; Case -1
(assume "CoIx")
(use "CoIUMinus")
(simpreal "RealIntNOneTimes")
(simpreal "RealUMinusUMinus")
(use "CoIx")
(autoreal)
;; Proof finished.
(save "CoISdTimes")
;; (cdp)

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [s,u]
;;  [if s
;;    (cCoICompat u)
;;    (cCoICompat cCoIZero)
;;    (cCoIUMinus(cCoICompat(cCoICompat u)))]

;; CoIMultcSatCoIClEq1
(set-goal "all x1,y,z0,d1,d0,i(Real x1 -> Real y -> Real z0 ->
 (1#4)*((1#2)*(x1+d1)*y+(1#2)*(z0+d0)+i)===
 (1#2)*((1#4)*(x1*y)+(1#4)*(z0+d1*y+i)+(1#4)*(RealPlus d0 i)))")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N")
(cases)
(assume "cs" "L" "d" "d0" "i" "Rx1" "Ry" "Rz0")
(use "RealEqSToEq")
(autoreal)
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?_13:(1#4)*((1#2)*(as n+d)*bs n+(1#2)*(cs n+d0)+i)==
;;      (1#2)*((1#4)*as n*bs n+(1#4)*(cs n+d*bs n+i)+(d0+i#4))
(use "RatEqvTrans" 
     (pt "(1#4)*((1#2)*((as n+d)*bs n)+(1#2)*(cs n+d0)+(1#2)*RatPlus i i)"))
(ng)
(simp (pf "2=IntPlus 1 1"))
(simp "IntTimes6RewRule") ;k*(j+i)=k*j+k*i
(use "Truth")
(use "Truth")
;; ?_15:(1#4)*((1#2)*((as n+d)*bs n)+(1#2)*(cs n+d0)+(1#2)*RatPlus i i)==
;;      (1#2)*((1#4)*as n*bs n+(1#4)*(cs n+d*bs n+i)+(d0+i#4))
;; Similarly replace (d0+i#4) by (1#4)*RatPlus d0 i.  Then cancel the factors
;; Finally use commutativity.
(use "RatEqvTrans"
     (pt "(1#2)*((1#4)*(as n*bs n)+(1#4)*(cs n+d*bs n+i)+(1#4)*RatPlus d0 i)"))
(simprat "<-" "RatTimesPlusDistr")
(simprat "<-" "RatTimesPlusDistr")
(simprat "<-" "RatTimesPlusDistr")
(simprat "<-" "RatTimesPlusDistr")
(simprat (pf "(cs n+d*bs n)==(d*bs n+cs n)"))
(simp "RatTimesAssoc")
(simp "RatTimesAssoc")
(simp (pf "(1#4)*(1#2)=(1#2)*(1#4)"))
(use "RatTimesCompat")
(use "Truth")
(simprat "RatTimesPlusDistrLeft")
(use "RatEqvTrans" (pt "as n*bs n+d*bs n+(cs n+i+RatPlus d0 i)"))
(use "RatEqvTrans" (pt "as n*bs n+d*bs n+(cs n+d0+RatPlus i i)"))
(use "Truth")
(use "RatPlusCompat")
(use "Truth")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
(simp "RatPlusAssoc")
(simp "RatPlusAssoc")
(use "RatPlusCompat")
(use "IntPlusComm")
(use "Truth")
(use "Truth")
(use "Truth")
(simp "RatPlusComm")
(use "Truth")
(ng #t)
(use "Truth")
;; Proof finished.
(save "CoIMultcSatCoIClEq1")

;; CoIMultcSatCoIClAvcDestr
(set-goal
 "allnc z0,d1,y,i(CoI z0 -> Sd d1 -> CoI y -> Sdtwo i -> exr z2,e,e0(
 CoI z2 andi Sd e andi Sd e0 andi (1#4)*(z0+d1*y+i)===(1#4)*(z2+e+2*e0)))")
(assume "z0" "d1" "y" "i" "CoIz0" "Sdd1" "CoIy" "Sdtwoi")
(assert "CoI((1#4)*(z0+d1*y+i))")
(use "CoIAvcToCoI")
(intro 0 (pt "i"))
(intro 0 (pt "z0"))
(intro 0 (pt "d1*y"))
(split)
(use "Sdtwoi")
(split)
(use "CoIz0")
(split)
(use "CoISdTimes")
(use "Sdd1")
(use "CoIy") 
(use "RealEqRefl")
(autoreal)
(assume "CoIv")
(cut "exr d,x(Sd d andi CoI x andi (1#4)*(z0+d1*y+i)===(1#2)*(x+d))")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "CoIClosureInstv")
(by-assume "CoIClosureInstv" "e0" "e0Prop")
(by-assume "e0Prop" "z1" "e0z1Prop")
(assert "CoI z1")
 (use "e0z1Prop")
(assume "CoIz1")
(inst-with-to "CoIClosure" (pt "z1") "CoIz1" "CoIClosureInstz1")
(by-assume "CoIClosureInstz1" "e" "eProp")
(by-assume "eProp" "z2" "ez2Prop")
(assert "CoI z2")
 (use "ez2Prop")
(assume "CoIz2")
(intro 0 (pt "z2"))
(intro 0 (pt "e"))
(intro 0 (pt "e0"))
(split)
(use "CoIz2")
(split)
(use "ez2Prop")
(split)
(use "e0z1Prop")
;; (1#4)*(z0+d1*y+i)===(1#4)*(z2+e+2*e0)
(simpreal (pf "(1#4)*(z0+d1*y+i)===(1#2)*(z1+e0)"))
(simpreal (pf "z1===(1#2)*(z2+e)"))
;; (1#2)*((1#2)*(z2+e)+e0)===(1#4)*(z2+e+2*e0)
(assert "all z2 (1#2)*((1#2)*(z2+e)+e0)=+=(1#4)*(z2+e+2*e0)")
(cases)
(assume "as" "M")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; (1#2)*((1#2)*(as n+e)+e0)==(1#4)*(as n+e+2*e0)
(simprat (pf "e0==(1#2)*(2*e0)"))
(simprat "<-" "RatTimesPlusDistr")
(ng #t)
(use "Truth")
(ng #t)
(use "IntTimesComm")
;; Assertion proved.
(assume "Assertion")
(use "RealEqSToEq")
(autoreal)
(use "Assertion")
(use "ez2Prop")
(use "e0z1Prop")
;; Now we need to prove CoIClosureInstv cut in above
(use "CoIClosure")
(use "CoIv")
;; Proof finished.
(save "CoIMultcSatCoIClAvcDestr")

;; cCoIMultcSatCoIClAvcDestr: str=>sd=>str=>sdtwo=>str yprod sd yprod sd

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [u,s,u0,t]
;;  [let su
;;    (cCoIClosure(cCoIAvcToCoI(t pair u pair cCoISdTimes s u0)))
;;    (crht(cCoIClosure crht su)pair clft(cCoIClosure crht su)pair clft su)]

;; CoIMultcSatCoIClEq2
(set-goal "all x1,y,z2,e,e0,d0,i(Real x1 -> Real y -> Real z2 ->
 (1#2)*((1#4)*(x1*y)+(1#4)*(z2+e+2*e0)+(1#4)*RealPlus d0 i)===
 (1#2)*((1#4)*(x1*y+z2+J(e+2*e0+d0+i))+K(e+2*e0+d0+i)))")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N")
(cases)
(assume "cs" "L" "e" "e0" "d0" "i" "Rx1" "Ry" "Rz2")
(use "RealEqSToEq")
(autoreal)
(use "RealEqSIntro")
(assume "n")
(ng #t)
(use "RatEqvTrans"
     (pt "(1#4)*as n*bs n+(1#4)*(cs n+e+2*e0)+(1#4)*RatPlus d0 i"))
(use "RatPlusCompat")
(use "Truth")
(use "Truth")
(use "RatEqvTrans" (pt "(1#4)*as n*bs n+(1#4)*(cs n+e+2*e0+d0+i)"))
(simp "<-" "RatTimesAssoc")
(simprat "<-" "RatTimesPlusDistr")
(simprat "<-" "RatTimesPlusDistr")
(simprat "<-" "RatTimesPlusDistr")
(use "RatTimesCompat")
(use "Truth")
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
(use "Truth")
(simprat (pf "K(e+2*e0+d0+i)==(1#4)*(K(e+2*e0+d0+i)*4)"))
(simprat "<-" "RatTimesPlusDistr")
(simp "<-" "RatTimesAssoc")
(simprat "<-" "RatTimesPlusDistr")
(use "RatTimesCompat")
(use "Truth")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
(use "RatPlusCompat")
(use "Truth")
(ng #t)
(simp (pf "J(e+2*e0+d0+i)+K(e+2*e0+d0+i)*4=K(e+2*e0+d0+i)*4+J(e+2*e0+d0+i)"))
(use "KJProp")
(use "IntPlusComm")
(ng #t)
(use "Truth")
;; Proof finished.
(save "CoIMultcSatCoIClEq2")

;; CoIMultcSatCoIClAuxJ
(set-goal "allnc e,e0,d0,i(Sd e -> Sd e0 -> Sd d0 -> Sdtwo i ->
 Sdtwo(J(e+2*e0+d0+i)))")
(assume "e" "e0" "d0" "i" "Sde" "Sde0" "Sdd0" "Sdtwoi")
(assert "exl s1 SdMR s1 e")
(use "SdMRIntro")
(use "Sde")
(assume "ExHyp1")
(by-assume "ExHyp1" "s1" "s1Prop")
(assert "exl s2 SdMR s2 e0")
(use "SdMRIntro")
(use "Sde0")
(assume "ExHyp2")
(by-assume "ExHyp2" "s2" "s2Prop")
(assert "exl s1 SdMR s1 d0")
(use "SdMRIntro")
(use "Sdd0")
(assume "ExHyp3")
(by-assume "ExHyp3" "s3" "s3Prop")
(assert "exl t SdtwoMR t i")
(use "SdtwoMRIntro")
(use "Sdtwoi")
(assume "ExHyp4")
(by-assume "ExHyp4" "t" "tProp")
(use "SdtwoMRElim"
     (pt "IntToSdtwo(J(SdToInt s1+2*SdToInt s2+SdToInt s3+SdtwoToInt t))"))
(simp (pf "J(SdToInt s1+2*SdToInt s2+SdToInt s3+SdtwoToInt t)=J(e+2*e0+d0+i)"))
(use "SdtwoMRIntToSdtwo")
;; ?_34:abs(J(e+2*e0+d0+i))<=2
(use "JProp")
(simp (pf "SdToInt s1+2*SdToInt s2+SdToInt s3+SdtwoToInt t=e+2*e0+d0+i"))
(use "Truth")
;; ?_36:SdToInt s1+2*SdToInt s2+SdToInt s3+SdtwoToInt t=e+2*e0+d0+i
(inst-with-to "SdMRId" (pt "e") (pt "s1") "s1Prop" "SdMRIdInst1")
(inst-with-to "SdMRId" (pt "e0") (pt "s2") "s2Prop" "SdMRIdInst2")
(inst-with-to "SdMRId" (pt "d0") (pt "s3") "s3Prop" "SdMRIdInst3")
(inst-with-to "SdtwoMRId" (pt "i") (pt "t") "tProp" "SdtwoMRIdInst")
(simp "SdMRIdInst1")
(simp "SdMRIdInst2")
(simp "SdMRIdInst3")
(simp "SdtwoMRIdInst")
(use "Truth")
;; Proof finished.
(save "CoIMultcSatCoIClAuxJ")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [s,s0,s1,t]
;;  IntToSdtwo(J(SdToInt s+2*SdToInt s0+SdToInt s1+SdtwoToInt t))

;; CoIMultcSatCoIClAuxK
(set-goal "allnc e,e0,d0,i(Sd e -> Sd e0 -> Sd d0 -> Sdtwo i ->
 Sd(K(e+2*e0+d0+i)))")
(assume "e" "e0" "d0" "i" "Sde" "Sde0" "Sdd0" "Sdtwoi")
(assert "exl s1 SdMR s1 e")
(use "SdMRIntro")
(use "Sde")
(assume "ExHyp1")
(by-assume "ExHyp1" "s1" "s1Prop")
(assert "exl s2 SdMR s2 e0")
(use "SdMRIntro")
(use "Sde0")
(assume "ExHyp2")
(by-assume "ExHyp2" "s2" "s2Prop")
(assert "exl s1 SdMR s1 d0")
(use "SdMRIntro")
(use "Sdd0")
(assume "ExHyp3")
(by-assume "ExHyp3" "s3" "s3Prop")
(assert "exl t SdtwoMR t i")
(use "SdtwoMRIntro")
(use "Sdtwoi")
(assume "ExHyp4")
(by-assume "ExHyp4" "t" "tProp")
(use "SdMRElim"
     (pt "IntToSd(K(SdToInt s1+2*SdToInt s2+SdToInt s3+SdtwoToInt t))"))
(simp (pf "K(SdToInt s1+2*SdToInt s2+SdToInt s3+SdtwoToInt t)=K(e+2*e0+d0+i)"))
(use "SdMRIntToSd")
;; ?_34:abs(K(e+2*e0+d0+i))<=1
(use "KProp")
;; ?_35:abs(e+2*e0+d0+i)<=6
(use "IntLeTrans" (pt "IntP 4+IntP 2"))
(use "IntLeTrans" (pt "abs(e+2*e0+d0)+abs i"))
(use "IntLeAbsPlus")
(use "IntLeMonPlus")
(use "IntLeTrans" (pt "IntP 3+IntP 1"))
(use "IntLeTrans" (pt "abs(e+2*e0)+abs d0"))
(use "IntLeAbsPlus")
(use "IntLeMonPlus")
(use "IntLeTrans" (pt "IntP 1+IntP 2"))
(use "IntLeTrans" (pt "abs e+abs(2*e0)"))
(use "IntLeAbsPlus")
(use "IntLeMonPlus")
(use "SdBound")
(use "Sde")
(ng)
(simp "IntTimesComm")
(use "IntLeTrans" (pt "IntP 1*2"))
(use "IntLeMonTimes")
(use "Truth")
(use "SdBound")
(use "Sde0")
(use "Truth")
(use "Truth")
(use "SdBound")
(use "Sdd0")
(use "Truth")
(use "SdtwoBound")
(use "Sdtwoi")
(use "Truth")
(simp (pf "SdToInt s1+2*SdToInt s2+SdToInt s3+SdtwoToInt t=e+2*e0+d0+i"))
(use "Truth")
;; ?_65:SdToInt s1+2*SdToInt s2+SdToInt s3+SdtwoToInt t=e+2*e0+d0+i
(inst-with-to "SdMRId" (pt "e") (pt "s1") "s1Prop" "SdMRIdInst1")
(inst-with-to "SdMRId" (pt "e0") (pt "s2") "s2Prop" "SdMRIdInst2")
(inst-with-to "SdMRId" (pt "d0") (pt "s3") "s3Prop" "SdMRIdInst3")
(inst-with-to "SdtwoMRId" (pt "i") (pt "t") "tProp" "SdtwoMRIdInst")
(simp "SdMRIdInst1")
(simp "SdMRIdInst2")
(simp "SdMRIdInst3")
(simp "SdtwoMRIdInst")
(use "Truth")
;; Proof finished.
(save "CoIMultcSatCoIClAuxK")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [s,s0,s1,t]IntToSd(K(SdToInt s+2*SdToInt s0+SdToInt s1+SdtwoToInt t))

;; CoIMultToMultc
(set-goal "allnc x,y(CoI x -> CoI y ->
 exr i,x1,y1,z1(CoI y1 andi Sdtwo i andi CoI x1 andi CoI z1 andi
 x*y===(1#4)*(x1*y1+z1+i)))")
(assume "x" "y" "CoIx" "CoIy")
(inst-with-to "CoIClosure" (pt "x") "CoIx" "CoIClosureInstx")
(by-assume "CoIClosureInstx" "d1" "d1Prop")
(by-assume "d1Prop" "x1" "d1x1Prop")
(inst-with-to "CoIClosure" (pt "y") "CoIy" "CoIClosureInsty")
(by-assume "CoIClosureInsty" "e1" "e1Prop")
(by-assume "e1Prop" "y1" "e1y1Prop")
(assert "CoI((1#2)*(e1*x1+d1*y1))")
(use "CoIAverage")
(use "CoISdTimes")
(use "e1y1Prop")
(use "d1x1Prop")
(use "CoISdTimes")
(use "d1x1Prop")
(use "e1y1Prop")
(assume "CoIAvxy")
(cut "exr d,x(Sd d andi CoI x andi (1#2)*(e1*x1+d1*y1)===(1#2)*(x+d))")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "CoIClosureInstxy")
(by-assume "CoIClosureInstxy" "d" "dProp")
(by-assume "dProp" "z1" "dz1Prop")
(intro 0 (pt "d+d1*e1"))
(intro 0 (pt "x1"))
(intro 0 (pt "y1"))
(intro 0 (pt "z1"))
(assert "CoI x1")
(use "d1x1Prop")
(assume "CoIx1")
(assert "CoI y1")
(use "e1y1Prop")
(assume "CoIy1")
(assert "CoI z1")
(use "dz1Prop")
(assume "CoIz1")
(split)
(use "CoIy1")
(split)
(use "IntPlusSdToSdtwo")
(use "dz1Prop")
(use "IntTimesSdToSd")
(use "d1x1Prop")
(use "e1y1Prop")
(split)
(use "CoIx1")
(split)
(use "CoIz1")
(assert "Real((1#4)*(x1*y1+z1+(d+d1*e1)))")
(autoreal)
(assume "R")
(simpreal "d1x1Prop")
(simpreal (pf "y===(y1+e1)*(1#2)"))
(simpreal "RealTimesAssoc")
(simpreal "RealTimesComm")
(simpreal "RealTimesAssoc")
(simpreal "RealTimesAssoc")
(ng)
(simpreal "<-" "RealTimesAssoc")
(use "RealTimesCompat")
(use "RealEqRefl")
(use "RealRat")
(simpreal "RealTimesPlusDistr")
(simpreal "RealTimesPlusDistrLeft")
(simpreal "<-" "RealPlusAssoc")
(use "RealEqSym")
(simpreal "<-" "RealPlusAssoc")
(use "RealPlusCompat")
(use "RealEqRefl")
(autoreal)
(use "RealEqSym")
(simpreal "RealTimesPlusDistrLeft")
(simpreal "RealPlusAssoc")
(simpreal (pf "d1*y1+x1*e1===z1+d"))
(simpreal "<-" "RealPlusAssoc")
(use "RealEqRefl")
(autoreal)
(simpreal (pf "d1*y1+x1*e1===(1#2)*(e1*x1+d1*y1)*2"))
(simpreal (pf "z1+d===(1#2)*(z1+d)*2"))
(use "RealTimesCompat")
(use "dz1Prop")
(use "RealEqRefl")
(use "RealRat")
(simpreal "RealTimesComm")
(simpreal "RealTimesAssoc")
(ng)
(use "RealEqSym")
(use "RealOneTimes")
(autoreal)
(use "RealEqSym")
(simpreal "RealTimesComm")
(simpreal "RealTimesAssoc")
(simpreal "RealPlusComm")
(ng)
(simpreal (pf "x1*e1===e1*x1"))
(use "RealOneTimes")
(autoreal)
(use "RealTimesComm")
(autoreal)
;;
(simpreal "RealTimesComm")
(use "e1y1Prop")
(use "RealRat")
(autoreal)
;; Now we prove the formula cut in above
(use "CoIClosure")
(use "CoIAvxy")
;; Proof finished.
(save "CoIMultToMultc")
;; (cdp)

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [u,u0]
;;  [let su
;;    (cCoIClosure
;;    (cCoIAverage(cCoISdTimes clft(cCoIClosure u0)crht(cCoIClosure u))
;;     (cCoISdTimes clft(cCoIClosure u)crht(cCoIClosure u0))))
;;    (crht(cCoIClosure u0)pair 
;;    cIntPlusSdToSdtwo clft su
;;    (cIntTimesSdToSd clft(cCoIClosure u)clft(cCoIClosure u0))pair 
;;    crht(cCoIClosure u)pair crht su)]

;; In CoIMultcSatCoICl y is viewed as a parameter.  It is
;; formulated as the step in a corecursion where from a triple one
;; gets a signed digit d and another triple.

;; CoIMultcSatCoICl
(set-goal "allnc y,i,x,z(CoI y -> Sdtwo i andi CoI x andi CoI z ->
 exr d,j,x1,z1(Sd d andi Sdtwo j andi CoI x1 andi CoI z1 andi
 (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x1*y+z1+j)+d)))")
(assume "y" "i" "x" "z" "CoIy" "Conj")
(cut "exr d1,x1(Sd d1 andi CoI x1 andi x===(1#2)*(x1+d1))")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "ExHypx")
(by-assume "ExHypx" "d1" "d1Prop")
(by-assume "d1Prop" "x1" "d1x1Prop")
(cut "exr d0,z0(Sd d0 andi CoI z0 andi z===(1#2)*(z0+d0))")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "ExHypz")
(by-assume "ExHypz" "d0" "d0Prop")
(by-assume "d0Prop" "z0" "d0z0Prop")
(cut "exr z2,e,e0(CoI z2 andd 
  Sd e andd Sd e0 andl (1#4)*(z0+d1*y+i)===(1#4)*(z2+e+2*e0))")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "AvcUnfolding") ;was ThreeInst
(by-assume "AvcUnfolding" "z2" "z2Prop")
(by-assume "z2Prop" "e" "z2eProp")
(by-assume "z2eProp" "e0" "z2ee0Prop")
(intro 0 (pt "K(e+2*e0+d0+i)"))
(intro 0 (pt "J(e+2*e0+d0+i)"))
(intro 0 (pt "x1"))
(intro 0 (pt "z2"))
;;   {y}  {i}  {x}  {z}  CoIy:
;;     CoI y
;;   Conj:Sdtwo i andd CoI x andd CoI z
;;   {d1}  {x1}  d1x1Prop:Sd d1 andd CoI x1 andl x===(1#2)*(x1+d1)
;;   {d0}  {z0}  d0z0Prop:Sd d0 andd CoI z0 andl z===(1#2)*(z0+d0)
;;   {z2}  {e}  {e0}  z2ee0Prop:
;;     CoI z2 andd Sd e andd Sd e0 andl (1#4)*(z0+d1*y+i)===(1#4)*(z2+e+2*e0)
;; -----------------------------------------------------------------------------
;; ?_39:Sd(K(e+2*e0+d0+i)) andd 
;;      Sdtwo(J(e+2*e0+d0+i)) andd 
;;      CoI x1 andd 
;;      CoI z2 andl 
;;      (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x1*y+z2+J(e+2*e0+d0+i))+K(e+2*e0+d0+i))
(split)
(use "CoIMultcSatCoIClAuxK")
(use "z2ee0Prop")
(use "z2ee0Prop")
(use "d0z0Prop")
(use "Conj")
(split)
(use "CoIMultcSatCoIClAuxJ")
(use "z2ee0Prop")
(use "z2ee0Prop")
(use "d0z0Prop")
(use "Conj")
(split)
(use "d1x1Prop")
(split)
(use "z2ee0Prop")
;; ?_55:(1#4)*(x*y+z+i)===(1#2)*((1#4)*(x1*y+z2+J(e+2*e0+d0+i))+K(e+2*e0+d0+i))
;; Since realproof cannot look into conjunctions we provide
(assert "CoI x")
(use "Conj")
(assume "CoIx")
(assert "CoI z")
(use "Conj")
(assume "CoIz")
(assert "CoI x1")
(use "d1x1Prop")
(assume "CoIx1")
(assert "CoI z0")
(use "d0z0Prop")
(assume "CoIz0")
(assert "CoI z2")
(use "z2ee0Prop")
(assume "CoIz2")
(use "RealEqTrans" (pt "(1#4)*((1#2)*(x1+d1)*y+(1#2)*(z0+d0)+i)"))
;; ?_71:(1#4)*(x*y+z+i)===(1#4)*((1#2)*(x1+d1)*y+(1#2)*(z0+d0)+i)
(simpreal "d1x1Prop")
(simpreal "d0z0Prop")
(use "RealEqRefl")
(autoreal)
(use "RealEqTrans"
     (pt "(1#2)*((1#4)*(x1*y)+(1#4)*(z2+e+2*e0)+(1#4)*RealPlus d0 i)"))
;; ?_76:(1#4)*((1#2)*(x1+d1)*y+(1#2)*(z0+d0)+i)===
;;      (1#2)*((1#4)*(x*y)+(1#4)*(z2+e+2*e0)+(1#4)*RealPlus d i)
(simpreal "<-" "z2ee0Prop")
(simpreal "CoIMultcSatCoIClEq1")
(use "RealEqRefl")
(autoreal)
;; ?_77:(1#2)*((1#4)*(x1*y)+(1#4)*(z2+e+2*e0)+(1#4)*RealPlus d0 i)===
;;      (1#2)*((1#4)*(x1*y+z2+J(e+2*e0+d0+i))+K(e+2*e0+d0+i))
(use "CoIMultcSatCoIClEq2")
(autoreal)
;; Now we need to prove the formulas cut in above
;; ?_24:exr z,e,e0(
;;       CoI z andd Sd e andd Sd e0 andl (1#4)*(z0+d1*y+i)===(1#4)*(z+e+2*e0))
(use "CoIMultcSatCoIClAvcDestr")
(use "d0z0Prop")
(use "d1x1Prop")
(use "CoIy")
(use "Conj")
;; ?_14:exr d,z0(Sd d andd CoI z0 andl z===(1#2)*(z0+d))
(use "CoIClosure")
(use "Conj")
;; ?_4:exr d,x0(Sd d andd CoI x0 andl x===(1#2)*(x0+d))
(use "CoIClosure")
(use "Conj")
;; Proof finished.
(save "CoIMultcSatCoICl")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [u,tuv]
;;  [let su
;;    (cCoIClosure clft crht tuv)
;;    [let su0
;;     (cCoIClosure crht crht tuv)
;;     [let (str yprod sd yprod sd)
;;      (cCoIMultcSatCoIClAvcDestr crht su0 clft su u clft tuv)
;;      (cCoIMultcSatCoIClAuxK clft crht(str yprod sd yprod sd)
;;      crht crht(str yprod sd yprod sd)
;;      clft su0 
;;      clft tuv pair 
;;      cCoIMultcSatCoIClAuxJ clft crht(str yprod sd yprod sd)
;;      crht crht(str yprod sd yprod sd)
;;      clft su0 
;;      clft tuv pair 
;;      crht su pair clft(str yprod sd yprod sd))]]]

(animate "CoIMultcSatCoIClAvcDestr")
(animate "CoIMultcSatCoIClAuxJ")
(animate "CoIMultcSatCoIClAuxK")

(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [u,tuv]
;;  [let su
;;    (cCoIClosure clft crht tuv)
;;    [let su0
;;     (cCoIClosure crht crht tuv)
;;     [let (str yprod sd yprod sd)
;;      [let su1
;;       (cCoIClosure
;;       (cCoIAvcToCoI(clft tuv pair crht su0 pair cCoISdTimes clft su u)))
;;       (crht(cCoIClosure crht su1)pair clft(cCoIClosure crht su1)pair clft su1)]
;;      (IntToSd
;;      (K
;;       (SdToInt clft crht(str yprod sd yprod sd)+
;;        2*SdToInt crht crht(str yprod sd yprod sd)+
;;        SdToInt clft su0+
;;        SdtwoToInt clft tuv))pair 
;;      IntToSdtwo
;;      (J
;;       (SdToInt clft crht(str yprod sd yprod sd)+
;;        2*SdToInt crht crht(str yprod sd yprod sd)+
;;        SdToInt clft su0+
;;        SdtwoToInt clft tuv))pair 
;;      crht su pair clft(str yprod sd yprod sd))]]]

(deanimate "CoIMultcSatCoIClAvcDestr")
(deanimate "CoIMultcSatCoIClAuxJ")
(deanimate "CoIMultcSatCoIClAuxK")

;; Putting things together

;; CoIMultcToCoI
(set-goal "allnc z(
 exr i,x0,y0,z0(CoI y0 andi Sdtwo i andi CoI x0 andi CoI z0 andi
 z===(1#4)*(x0*y0+z0+i)) -> CoI z)")
(assume "z" "Qz")
(coind "Qz")
(assume "x" "Qx")
(by-assume "Qx" "i" "iProp")
(by-assume "iProp" "x1" "ix1Prop")
(by-assume "ix1Prop" "y1" "ix1y1Prop")
(by-assume "ix1y1Prop" "z1" "ix1y1z1Prop")
(cut "exr d,j,x0,z0(
 Sd d andi Sdtwo j andi CoI x0 andi CoI z0 andi
 (1#4)*(x1*y1+z1+i)===(1#2)*((1#4)*(x0*y1+z0+j)+d))")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "CoIMultcSatCoIClInst")
(by-assume "CoIMultcSatCoIClInst" "d" "dProp")
(by-assume "dProp" "j" "djProp")
(by-assume "djProp" "x2" "djx2Prop")
(by-assume "djx2Prop" "z2" "djx2z2Prop")
(assert "CoI x2")
(use "djx2z2Prop")
(assume "CoIx2")
(assert "CoI y1")
(use "ix1y1z1Prop")
(assume "CoIy1")
(assert "CoI z2")
(use "djx2z2Prop")
(assume "CoIz2")
(intro 0 (pt "d"))
(intro 0 (pt "(1#4)*(x2*y1+z2+j)"))
(intro 0 (pt "x"))
(split)
(use "djx2z2Prop")
(split)
;; ?_47:Real((1#4)*(x2*y1+z2+j))
(autoreal)
(split)
;; ?_49:abs((1#4)*(x2*y1+z2+j))<<=1
(inst-with-to "CoIToBd" (pt "x2") "CoIx2" "x2Bd")
(inst-with-to "CoIToBd" (pt "y1") "CoIy1" "y1Bd")
(inst-with-to "CoIToBd" (pt "z2") "CoIz2" "z2Bd")
(simpreal "RealAbsTimes")
(use "RealLeTrans" (pt "RealAbs(1#4)*(((RealTimes 1 1)+1)+2)"))
(use "RealLeMonTimes")
(use "RealNNegPos")
(use "RealLeTrans" (pt "abs(x2*y1+z2)+RealAbs j"))
(use "RealLeAbsPlus")
(autoreal)
(use "RealLeMonPlus")
(use "RealLeTrans" (pt "abs(x2*y1)+abs z2"))
(use "RealLeAbsPlus")
(autoreal)
(use "RealLeMonPlus")
(simpreal "RealAbsTimes")
(use "RealLeMonTimesTwo")
(use "RealNNegAbs")
(autoreal)
(use "RealNNegAbs")
(autoreal)
(use "x2Bd")
(use "y1Bd")
(autoreal)
(use "z2Bd")
(use "SdtwoBoundReal")
(use "djx2z2Prop")
(ng #t)
(use "RealLeRefl")
(use "RealRat")
(autoreal)
(split)
(intro 1)
(intro 0 (pt "j"))
(intro 0 (pt "x2"))
(intro 0 (pt "y1"))
(intro 0 (pt "z2"))
(split)
(use "ix1y1z1Prop")
(split)
(use "djx2z2Prop")
(split)
(use "djx2z2Prop")
(split)
(use "djx2z2Prop")
(use "RealEqRefl")
;; ?_103:Real((1#4)*(x2*y1+z2+j))
(autoreal)
(split)
(use "RealEqTrans" (pt "(1#4)*(x1*y1+z1+i)"))
(use "ix1y1z1Prop")
(use "djx2z2Prop")
(use "RealEqRefl")
(use "RealEqElim0" (pt "(1#4)*(x1*y1+z1+i)"))
(use "ix1y1z1Prop")
;; Now we prove the formula cut in above
(use "CoIMultcSatCoICl")
(use "ix1y1z1Prop")
(split)
(use "ix1y1z1Prop")
(split)
(use "ix1y1z1Prop")
(use "ix1y1z1Prop")
;; Proof finished.
(save "CoIMultcToCoI")

;; cCoIMultcToCoI: str yprod sdtwo yprod str yprod str=>str

(define eterm (proof-to-extracted-term))
(add-var-name "utvw" (py "str yprod sdtwo yprod str yprod str"))
(add-var-name "stuv" (py "sd yprod sdtwo yprod str yprod str"))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [utvw]
;;  (CoRec str yprod sdtwo yprod str yprod str=>str)utvw
;;  ([utvw0]
;;    [let stuv
;;      (cCoIMultcSatCoICl clft utvw0 crht utvw0)
;;      (clft stuv pair InR(clft utvw0 pair crht stuv))])

;; CoIMult
(set-goal "allnc x,y(CoI x -> CoI y -> CoI(x*y))")
(assume "x" "y" "CoIx" "CoIy")
(cut "exr i,x0,y0,z(CoI y0 andi Sdtwo i andi CoI x0 andi CoI z andi
 x*y===(1#4)*(x0*y0+z+i))")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "CoIMultToMultcInst")
(by-assume "CoIMultToMultcInst" "i" "iProp")
(by-assume "iProp" "x1" "ix1Prop")
(by-assume "ix1Prop" "y1" "ix1y1Prop")
(by-assume "ix1y1Prop" "z" "ix1y1zProp")
(use "CoIMultcToCoI")
(intro 0 (pt "i"))
(intro 0 (pt "x1"))
(intro 0 (pt "y1"))
(intro 0 (pt "z"))
(split)
(use "ix1y1zProp")
(split)
(use "ix1y1zProp")
(split)
(use "ix1y1zProp")
(split)
(use "ix1y1zProp")
(use "ix1y1zProp")
;; Now we prove the formula cut in above
(use "CoIMultToMultc")
(use "CoIx")
(use "CoIy")
;; Proof finished.
(save "CoIMult")

(define eterm (proof-to-extracted-term))
(animate "CoIMultcToCoI")
(define neterm-CoIMult (rename-variables (nt eterm)))
(ppc neterm-CoIMult)

;; [u,u0][let utvw (cCoIMultToMultc u u0)
;;    ((CoRec str yprod sdtwo yprod str yprod str=>str)utvw
;;    ([utvw0][let stuv (cCoIMultcSatCoICl clft utvw0 crht utvw0)
;;        (clft stuv pair InR(clft utvw0 pair crht stuv))]))]

(deanimate "CoIMultcToCoI")
