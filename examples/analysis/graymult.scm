;; 2017-12-12.  examples/analysis/graymult.scm.

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
(load "~/git/minlog/examples/analysis/graycode.scm")
(load "~/git/minlog/examples/analysis/JK.scm")
(load "~/git/minlog/examples/analysis/grayavaux.scm")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Multiplication for Gray code
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; CoGZero
(set-goal "CoG 0")
(assert "allnc x(exl x1(Real x1 andi x1===0 andi x===x1) -> CoG x)")
(assume "x" "CoG-ExHyp")
(coind "CoG-ExHyp" (pf "exl x1(Real x1 andi x1===0 andi x===x1) -> CoH x"))
(assume "y" "CoH-ExHyp")
(intro 1)
(by-assume "CoG-ExHyp" "x1" "x1Prop")
(by-assume "CoH-ExHyp" "y1" "y1Prop")
(intro 0 (pt "x1"))
(intro 0 (pt "y1"))
(split)
(use "x1Prop")
(split)
(simpreal "x1Prop")
(use "RatLeToRealLe")
(use "Truth")
(split)
(intro 1)
(intro 0 (pt "x1"))
(split)
(use "x1Prop")
(split)
(use "x1Prop")
(use "RealEqRefl")
(use "x1Prop")
(split)
(assert "Real x1")
(use "x1Prop")
(assume "Rx1")
(assert "Real y1")
(use "y1Prop")
(assume "Ry1")
(simpreal "y1Prop")
(simpreal "x1Prop")
(simpreal "RealTimesZero")
(use "RatEqvToRealEq")
(use "Truth")
(autoreal)
(use "y1Prop")
;; 6
(assume "y" "CoH-ExHyp")
(intro 1)
(by-assume "CoG-ExHyp" "x1" "x1Prop")
(by-assume "CoH-ExHyp" "y1" "y1Prop")
(intro 0 (pt "x1"))
(intro 0 (pt "y1"))
(split)
(use "x1Prop")
(split)
(simpreal "x1Prop")
(use "RatLeToRealLe")
(use "Truth")
(split)
(intro 1)
(intro 0 (pt "x1"))
(split)
(use "x1Prop")
(split)
(use "x1Prop")
(use "RealEqRefl")
(use "x1Prop")
(split)
(assert "Real x1")
(use "x1Prop")
(assume "Rx1")
(assert "Real y1")
(use "y1Prop")
(assume "Ry1")
(simpreal "y1Prop")
(simpreal "x1Prop")
(simpreal "RealTimesZero")
(use "RatEqvToRealEq")
(use "Truth")
(autoreal)
(use "y1Prop")
;; Assertion proved.
(assume "Assertion")
(use "Assertion")
(intro 0 (pt "RealConstr([n](0#1))([p]Zero)"))
(split)
(autoreal)
(split)
(use "RatEqvToRealEq")
(use "Truth")
(use "RatEqvToRealEq")
(use "Truth")
;; Proof finished.
(save "CoGZero")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; (CoRec rea=>ag rea=>ah)0([x]InR(InR 0))([x]InR(InR 0))

;; CoGMultToMultc
(set-goal "allnc x,y(CoG x -> CoG y ->
 exr i,x1,y1,z1(Sdtwo i andi CoG x1 andi CoG y1 andi CoG z1 andi
 x*y===(1#4)*(x1*y1+z1+i)))")
(assume "x" "y" "CoGx" "CoGy")
(inst-with-to "CoGClosure" (pt "x") "CoGx" "xCases")
(elim "xCases")
;; 5,6
(drop "xCases")

;; Case LRx
(assume "ExHypx")
(by-assume "ExHypx" "d1" "d1Prop")
(by-assume "d1Prop" "x1" "d1x1Prop")
(assert "CoG x1")
(use "d1x1Prop")
(assume "CoGx1")

;; We distinguish cases on CoG y
(inst-with-to "CoGClosure" (pt "y") "CoGy" "yCases")
(elim "yCases")
;; 20,21
(drop "yCases")

;; Subcase LRx, LRy
(assume "ExHypy")
(by-assume "ExHypy" "e1" "e1Prop")
(by-assume "e1Prop" "y1" "e1y1Prop")
(assert "CoG y1")
(use "e1y1Prop")
(assume "CoGy1")

(assert "CoG((1#2)*(x1* ~(d1*e1)+ y1* ~(d1*e1)))")
(use "CoGAverage")
(use "CoGPsdTimes")
(use "CoGx1")
(use "PsdUMinus")
(use "IntTimesPsdToPsd")
(use "d1x1Prop")
(use "e1y1Prop")
(use "CoGPsdTimes")
(use "CoGy1")
(use "PsdUMinus")
(use "IntTimesPsdToPsd")
(use "d1x1Prop")
(use "e1y1Prop")
(assume "CoGAvxy")

;;   {x}  {y}  CoGx:CoG x
;;   CoGy:CoG y
;;   {d1}  {x1}  d1x1Prop:Psd d1 andd CoG x1 andl x===(1#2)*(x1+IntN 1)* ~d1
;;   CoGx1:CoG x1
;;   {e1}  {y1}  e1y1Prop:Psd e1 andd CoG y1 andl y===(1#2)*(y1+IntN 1)* ~e1
;;   CoGy1:CoG y1
;;   CoGAvxy:CoG((1#2)*(x1* ~(d1*e1)+y1* ~(d1*e1)))
;; -----------------------------------------------------------------------------
;; ?_47:exr i,x0,y0,z(
;;       Sdtwo i andd 
;;       CoG x0 andd CoG y0 andd CoG z andl x*y===(1#4)*(x0*y0+z+i))

(inst-with-to "CoGClosure"
	      (pt "(1#2)*(x1* ~(d1*e1)+y1* ~(d1*e1))") "CoGAvxy" "zCases")
(elim "zCases")
;; 50,51
(drop "zCases")

;; Case LRz
(assume "ExHypz")
(by-assume "ExHypz" "d0" "d0Prop")
(by-assume "d0Prop" "z1" "d0z1Prop")
(assert "CoG z1")
(use "d0z1Prop")
(assume "CoGz1")
(intro 0 (pt "d0+d1*e1"))
(intro 0 (pt "x1*d1"))
(intro 0 (pt "y1*e1"))
(intro 0 (pt "z1* ~d0"))
(split)
(use "IntPlusPsdToSdtwo")
(use "d0z1Prop")
(use "IntTimesPsdToPsd")
(use "d1x1Prop")
(use "e1y1Prop")
(split)
(use "CoGPsdTimes")
(use "CoGx1")
(use "d1x1Prop")
(split)
(use "CoGPsdTimes")
(use "CoGy1")
(use "e1y1Prop")
(split)
(use "CoGPsdTimes")
(use "CoGz1")
(use "PsdUMinus")
(use "d0z1Prop")
(assert "Real((1#4)*(x1*d1*(y1*e1)+z1* ~d0+(d0+d1*e1)))")
(realproof)
(assume "R")
(simpreal "d1x1Prop")
(simpreal "e1y1Prop")
;; ?_90:(1#2)*(x1+IntN 1)* ~d1*((1#2)*(y1+IntN 1)* ~e1)===
;;      (1#4)*(x1*d1*(y1*e1)+z1* ~d0+(d0+d1*e1))
;; RealEqTrans for simpreal with (1#2)*z1
(use "RealEqTrans"
     (pt "(1#4)*(x1*d1*(y1*e1)+2*((1#2)*(z1+IntN 1)* ~d0)+d1*e1)"))
(simpreal "<-" "d0z1Prop")
;; ?_93:(1#2)*(x1+IntN 1)* ~d1*((1#2)*(y1+IntN 1)* ~e1)===
;;      (1#4)*(x1*d1*(y1*e1)+2*((1#2)*(x1* ~(d1*e1)+y1* ~(d1*e1)))+d1*e1)
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealEqSIntro")
(assume "n")
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y1"))
(assume "bs" "N" "y1Def")
(ng #t)
(simprat (pf "(1#2)*(as n+IntN 1)* ~d1*(1#2)==
              (1#2)*((1#2)*(as n+IntN 1)* ~d1)"))
(ng #t)
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimesAssoc")
(simp "RatEqv6RewRule")
;; ?_110:(as n+IntN 1)*(d1*((bs n+IntN 1)*e1))==
;;       as n*d1*bs n*e1+ ~(as n*(d1*e1))+ ~(bs n*(d1*e1))+d1*e1
(simprat "RatTimesPlusDistrLeft")
(simprat "RatTimesPlusDistrLeft")
(simprat "RatTimesPlusDistr")
(simprat "RatTimesPlusDistr")
(simprat "RatTimesPlusDistr")
(ng #t)
(use "RatPlusCompat")
(use "RatPlusCompat")
(simp "RatEqv4RewRule")
(simp "<-" "RatTimes3RewRule")
;; ?_122:as n*(d1*IntN 1*e1)==as n* ~(d1*e1)
(simp "IntTimesIntNR")
(use "Truth")
;; ?_120:IntN 1*d1*bs n*e1== ~(bs n*(d1*e1))
(simp "IntTimesIntNL")
(ng #t)
(simp (pf "d1*bs n=bs n*d1"))
(simp (pf "(d1*e1#1)=RatTimes d1 e1"))
(use "RatEqvSym")
(simp "RatTimesAssoc")
(use "Truth")
(use "Truth")
(use "RatTimesComm")
;; ?_118:IntN 1*d1*IntN 1*e1==d1*e1
(simp "IntTimesIntNL")
(ng #t)
(simp "<-" "IntTimesAssoc")
(simp "IntTimesIntNL")
(use "Truth")
;; ?_105:(1#2)*(as n+IntN 1)* ~d1*(1#2)==(1#2)*((1#2)*(as n+IntN 1)* ~d1)
(simp (pf "(1#2)*((1#2)*(as n+IntN 1)* ~d1)=((1#2)*(as n+IntN 1)* ~d1)*(1#2)"))
(use "Truth")
(use "RatTimesComm")
;; ?_92:(1#4)*(x1*d1*(y1*e1)+2*((1#2)*(z1* ~d0+d0))+d1*e1)===
;;      (1#4)*(x1*d1*(y1*e1)+z1* ~d0+(d0+d1*e1))
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y1"))
(assume "bs" "N" "y1Def")
(cases (pt "z1"))
(assume "as1" "M1" "z1Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
(simprat "RatTimesPlusDistrLeft")
(ng #t)
(simp "IntTimesIntNL")
(ng #t)
(simp (pf "d0+d1*e1=RatPlus d0(d1*e1)"))
(simp "<-" "RatPlusAssoc")
(use "Truth")
(use "Truth")
;; ?_51:exr x0(CoH x0 andl (1#2)*(x1* ~(d1*e1)+y1* ~(d1*e1))===(1#2)*x0) -> 
;;      exr i,x0,y0,z(
;;       Sdtwo i andd 
;;       CoG x0 andd CoG y0 andd CoG z andl x*y===(1#4)*(x0*y0+z+i))
(drop "zCases")
(assume "ExHypz1")
(by-assume "ExHypz1" "z1" "z1Prop")
(assert "CoH z1")
(use "z1Prop")
(assume "CoHz1")
;;   {z1}  z1Prop:CoH z1 andl (1#2)*(x1* ~(d1*e1)+y1* ~(d1*e1))===(1#2)*z1
;;   CoHz1:CoH z1
;; -----------------------------------------------------------------------------
;; ?_164:exr i,x0,y0,z(
;;        Sdtwo i andd 
;;        CoG x0 andd CoG y0 andd CoG z andl x*y===(1#4)*(x0*y0+z+i))

(intro 0 (pt "d1*e1"))
(intro 0 (pt "x1*d1"))
(intro 0 (pt "y1*e1"))
(intro 0 (pt "z1"))
(split)
(use "PsdToSdtwo")
(use "IntTimesPsdToPsd")
(use "d1x1Prop")
(use "e1y1Prop")
(split)
(use "CoGPsdTimes")
(use "CoGx1")
(use "d1x1Prop")
(split)
(use "CoGPsdTimes")
(use "CoGy1")
(use "e1y1Prop")
(split)
(use "CoHToCoG")
(use "CoHz1")
;; ?_183:x*y===(1#4)*(x1*d1*(y1*e1)+z1+d1*e1)
(simpreal "d1x1Prop")
(simpreal "e1y1Prop")
;; ?_186:(1#2)*(x1+IntN 1)* ~d1*((1#2)*(y1+IntN 1)* ~e1)===
;;       (1#4)*(x1*d1*(y1*e1)+z1+d1*e1)
;; RealEqTrans for simpreal with (1#2)*z1
(use "RealEqTrans" (pt "(1#4)*(x1*d1*(y1*e1)+2*((1#2)*z1)+d1*e1)"))
(simpreal "<-" "z1Prop")
;; ?_189:(1#2)*(x1+IntN 1)* ~d1*((1#2)*(y1+IntN 1)* ~e1)===
;;       (1#4)*(x1*d1*(y1*e1)+2*((1#2)*(x1* ~(d1*e1)+y1* ~(d1*e1)))+d1*e1)
;; Same goal as 93 above
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealEqSIntro")
(assume "n")
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y1"))
(assume "bs" "N" "y1Def")
(ng #t)
(simprat (pf "(1#2)*(as n+IntN 1)* ~d1*(1#2)==
              (1#2)*((1#2)*(as n+IntN 1)* ~d1)"))
(ng #t)
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimesAssoc")
(simp "RatEqv6RewRule")
;; ?_206:(as n+IntN 1)*(d1*((bs n+IntN 1)*e1))==
;;       as n*d1*bs n*e1+ ~(as n*(d1*e1))+ ~(bs n*(d1*e1))+d1*e1
(simprat "RatTimesPlusDistrLeft")
(simprat "RatTimesPlusDistrLeft")
(simprat "RatTimesPlusDistr")
(simprat "RatTimesPlusDistr")
(simprat "RatTimesPlusDistr")
(ng #t)
(use "RatPlusCompat")
(use "RatPlusCompat")
(simp "RatEqv4RewRule")
(simp "<-" "RatTimes3RewRule")
;; ?_218:as n*(d1*IntN 1*e1)==as n* ~(d1*e1)
(simp "IntTimesIntNR")
(use "Truth")
;; ?_216:IntN 1*d1*bs n*e1== ~(bs n*(d1*e1))
(simp "IntTimesIntNL")
(ng #t)
(simp (pf "d1*bs n=bs n*d1"))
(simp (pf "(d1*e1#1)=RatTimes d1 e1"))
(use "RatEqvSym")
(simp "RatTimesAssoc")
(use "Truth")
(use "Truth")
(use "RatTimesComm")
;; ?_214:IntN 1*d1*IntN 1*e1==d1*e1
(simp "IntTimesIntNL")
(ng #t)
(simp "<-" "IntTimesAssoc")
(simp "IntTimesIntNL")
(use "Truth")
;; ?_201:(1#2)*(as n+IntN 1)* ~d1*(1#2)==(1#2)*((1#2)*(as n+IntN 1)* ~d1)
(simp (pf "(1#2)*((1#2)*(as n+IntN 1)* ~d1)=((1#2)*(as n+IntN 1)* ~d1)*(1#2)"))
(use "Truth")
(use "RatTimesComm")
;; 188:(1#4)*(x1*d1*(y1*e1)+2*((1#2)*z1)+d1*e1)===(1#4)*(x1*d1*(y1*e1)+z1+d1*e1)
(simpreal (pf "2*((1#2)*z1)===z1"))
(use "RealEqRefl")
(realproof)
;; ?_235:2*((1#2)*z1)===z1
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealEqSIntro")
(assume "n")
(cases (pt "z1"))
(assume "as" "M" "z1Def")
(ng #t)
(use "Truth")
;; ?_21:exr x0(CoH x0 andl y===(1#2)*x0) -> 
;;      exr i,x0,y0,z(
;;       Sdtwo i andd 
;;       CoG x0 andd CoG y0 andd CoG z andl x*y===(1#4)*(x0*y0+z+i))
(drop "yCases")

;; Subcase LRx, Uy
(assume "ExHypy")
(by-assume "ExHypy" "y1" "y1Prop")
(assert "CoH y1")
(use "y1Prop")
(assume "CoHy1")
(intro 0 (pt "0"))
(intro 0 (pt "x1* ~d1"))
(intro 0 (pt "y1"))
(intro 0 (pt "y1*d1"))
(split)
(use "InitSdtwoMT")
(split)
(use "CoGPsdTimes")
(use "CoGx1")
(use "PsdUMinus")
(use "d1x1Prop")
(split)
(use "CoHToCoG")
(use "CoHy1")
(split)
(use "CoGPsdTimes")
(use "CoHToCoG")
(use "CoHy1")
(use "d1x1Prop")
;; ?_268:x*y===(1#4)*(x1* ~d1*y1+y1*d1+0)
(simpreal "d1x1Prop")
(simpreal "y1Prop")
;; ?_273:(1#2)*(x1+IntN 1)* ~d1*((1#2)*y1)===(1#4)*(x1* ~d1*y1+y1*d1+0)
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealEqSIntro")
(assume "n")
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y1"))
(assume "bs" "N" "y1Def")
(ng #t)
;; ?_283:~((1#2)*(as n+IntN 1)*d1*(1#2)*bs n)==(1#4)*(~(as n*d1*bs n)+bs n*d1)
(simp (pf "(1#2)*(as n+IntN 1)*d1*(1#2)=(1#2)*((1#2)*(as n+IntN 1)*d1)"))
(ng #t)
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimes3RewRule")
(simp "RatEqv6RewRule")
(simprat "RatTimesPlusDistrLeft")
(ng #t)
(simp "IntTimesIntNL")
(ng #t)
(simp "RatTimesComm")
(use "Truth")
;; ?_285:(1#2)*(as n+IntN 1)*d1*(1#2)=(1#2)*((1#2)*(as n+IntN 1)*d1)
(simp "RatTimesComm")
(use "Truth")
;; ?_6:exr x0(CoH x0 andl x===(1#2)*x0) -> 
;;     exr i,x0,y0,z(
;;      Sdtwo i andd CoG x0 andd CoG y0 andd CoG z andl x*y===(1#4)*(x0*y0+z+i))
(drop "xCases")

;; Case Ux
(assume "ExHypx")
(by-assume "ExHypx" "x1" "x1Prop")
(assert "CoH x1")
(use "x1Prop")
(assume "CoHx1")

;; We distinguish cases on CoG y
(inst-with-to "CoGClosure" (pt "y") "CoGy" "yCases")
(elim "yCases")
;; 307,308
(drop "yCases")

;; Subcase Ux, LRy
(assume "ExHypy")
(by-assume "ExHypy" "e1" "e1Prop")
(by-assume "e1Prop" "y1" "e1y1Prop")
(assert "CoG y1")
(use "e1y1Prop")
(assume "CoGy1")
(intro 0 (pt "0"))
(intro 0 (pt "x1"))
(intro 0 (pt "y1* ~e1"))
(intro 0 (pt "x1*e1"))
(split)
(use "InitSdtwoMT")
(split)
(use "CoHToCoG")
(use "CoHx1")
(split)
(use "CoGPsdTimes")
(use "CoGy1")
(use "PsdUMinus")
(use "e1y1Prop")
(split)
(use "CoGPsdTimes")
(use "CoHToCoG")
(use "CoHx1")
(use "e1y1Prop")
;; ?_335:x*y===(1#4)*(x1*(y1* ~e1)+x1*e1+0)
(simpreal "x1Prop")
(simpreal "e1y1Prop")
;; ?_340:(1#2)*x1*((1#2)*(y1+IntN 1)* ~e1)===(1#4)*(x1*(y1* ~e1)+x1*e1+0)
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealEqSIntro")
(assume "n")
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y1"))
(assume "bs" "N" "y1Def")
(ng #t)
;; ?_350:~((1#2)*as n*(1#2)*(bs n+IntN 1)*e1)==(1#4)*(~(as n*bs n*e1)+as n*e1)
;;         (1#2)*as n*(1#2)*(bs n+IntN 1)* ~e1==(1#4)*(as n*bs n* ~e1+as n*e1)
(simp (pf "(1#2)*as n*(1#2)=(1#2)*((1#2)*as n)"))
(ng #t)
(simp "<-" "RatTimes3RewRule")
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimesAssoc")
(use "RatTimesCompat")
(use "Truth")
(simprat "RatTimesPlusDistrLeft")
(simprat "RatTimesPlusDistr")
(simp "RatTimesIntNL")
(use "Truth")
;; ?_352:(1#2)*as n*(1#2)=(1#2)*((1#2)*as n)
(simp "RatTimesComm")
(use "Truth")
;; ?_308:exr x0(CoH x0 andl y===(1#2)*x0) -> 
;;       exr i,x0,y0,z(
;;        Sdtwo i andd 
;;        CoG x0 andd CoG y0 andd CoG z andl x*y===(1#4)*(x0*y0+z+i))
(drop "yCases")

;; Subcase Ux, Uy
(assume "ExHypy")
(by-assume "ExHypy" "y1" "y1Prop")
(assert "CoH y1")
(use "y1Prop")
(assume "CoHy1")
(intro 0 (pt "0"))
(intro 0 (pt "x1"))
(intro 0 (pt "y1"))
(intro 0 (pt "RealConstr([n](0#1))([p]Zero)"))
(split)
(use "InitSdtwoMT")
(split)
(use "CoHToCoG")
(use "CoHx1")
(split)
(use "CoHToCoG")
(use "CoHy1")
(split)
(use "CoGZero")
;; ?_384:x*y===(1#4)*(x1*y1+0+0)
(simpreal "x1Prop")
(simpreal "y1Prop")
;; ?_486:(1#2)*x1*((1#2)*y1)===(1#4)*(x1*y1+0+0)
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealEqSIntro")
(assume "n")
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y1"))
(assume "bs" "N" "y1Def")
(ng #t)
;; ?_396:(1#2)*as n*(1#2)*bs n==(1#4)*as n*bs n
(simp (pf "(1#2)*as n*(1#2)=(1#2)*((1#2)*as n)"))
(use "Truth")
(use "RatTimesComm")
;; Proof finished.
(save "CoGMultToMultc")

;; cCoGMultToMultc: ag=>ag=>sdtwo yprod ag yprod ag yprod ag

(define eterm (proof-to-extracted-term))
(animate "CoGClosure")
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [ag,ag0][case (DesYprod ag)
;;    (InL bg -> [case (DesYprod ag0)
;;      (InL bg0 -> [case (DesYprod(cCoGAverage
;;        (cCoGPsdTimes crht bg
;;         (cPsdUMinus(cIntTimesPsdToPsd clft bg clft bg0)))
;;        (cCoGPsdTimes crht bg0
;;         (cPsdUMinus(cIntTimesPsdToPsd clft bg clft bg0)))))
;;        (InL bg1 -> 
;;        cIntPlusPsdToSdtwo 
;;          clft bg1(cIntTimesPsdToPsd clft bg clft bg0)pair 
;;        cCoGPsdTimes crht bg clft bg pair 
;;        cCoGPsdTimes crht bg0 clft bg0 pair 
;;        cCoGPsdTimes crht bg1(cPsdUMinus clft bg1))
;;        (InR ah -> 
;;        cPsdToSdtwo(cIntTimesPsdToPsd clft bg clft bg0)pair 
;;        cCoGPsdTimes crht bg clft bg pair 
;;        cCoGPsdTimes crht bg0 clft bg0 pair
;;        cCoHToCoG ah)])
;;      (InR ah -> MT pair 
;;                 cCoGPsdTimes crht bg(cPsdUMinus clft bg)pair 
;;                 cCoHToCoG ah pair
;;                 cCoGPsdTimes(cCoHToCoG ah)clft bg)])
;;    (InR ah -> [case (DesYprod ag0)
;;      (InL bg -> MT pair 
;;                 cCoHToCoG ah pair 
;;                 cCoGPsdTimes crht bg(cPsdUMinus clft bg)pair 
;;                 cCoGPsdTimes(cCoHToCoG ah)clft bg)
;;      (InR ah0 -> MT pair
;;                  cCoHToCoG ah pair
;;                  cCoHToCoG ah0 pair
;;                  cCoGZero)])]

(deanimate "CoGClosure")

;; We need auxiliary lemmas

;;       JKLrzLrvLr
;;       JKLrzLrvU
;;     JKLrzLrv
;;       JKLrzUvFin
;;       JKLrzUvD
;;     JKLrzUv
;;   JKLrz

;;       JKUzLrvLr
;;       JKUzLrvU
;;     JKUzLrv
;;       JKUzUvFin
;;       JKUzUvD
;;     JKUzUv
;;   JKUz

;; JKLrzLrvLr
(set-goal "allnc i,d0,y(Sdtwo i -> Psd d0 -> CoG y --> allnc e0,z2(
 Psd e0 -> CoG z2 --> y===(1#2)*(z2+IntN 1)* ~e0 -> allnc e,z3(
 Psd e -> CoG z3 -> z2===(1#2)*(z3+IntN 1)* ~e ->
 exr j,d,z(Sdtwo j andi Sd d andi CoG z andi y+(d0+i#4)===(1#4)*(z+j)+d))))")
(assume "i" "d0" "y" "Sdtwoi" "Psdd0" "CoGy"
	"e0" "z2" "Psde0" "CoGz2" "e0z2Prop"
        "e" "z3" "Psde" "CoGz3" "ez3Prop")

(assert "exnc j j=J(e* ~e0+2*e0+d0+i)")
(intro 0 (pt "J(e* ~e0+2*e0+d0+i)"))
(use "Truth")
(assume "ExHypj")
(by-assume "ExHypj" "j" "jDef")

(assert "exnc k k=K(e* ~e0+2*e0+d0+i)")
(intro 0 (pt "K(e* ~e0+2*e0+d0+i)"))
(use "Truth")
(assume "ExHypk")
(by-assume "ExHypk" "k" "kDef")

(intro 0 (pt "j"))
(intro 0 (pt "k"))
(intro 0 (pt "z3*e*e0"))

(assert "exl boole BooleToInt boole=e")
(use "PsdToBooleToIntValue")
(use "Psde")
(assume "ExHype")
(by-assume "ExHype" "boole" "booleProp")

(assert "exl boole BooleToInt boole=e0")
(use "PsdToBooleToIntValue")
(use "Psde0")
(assume "ExHype0")
(by-assume "ExHype0" "boole1" "boole1Prop")

(assert "exl boole BooleToInt boole=d0")
(use "PsdToBooleToIntValue")
(use "Psdd0")
(assume "ExHypd0")
(by-assume "ExHypd0" "boole0" "boole0Prop")

(assert "exl t SdtwoToInt t=i")
(use "SdtwoToSdtwoToIntValue")
(use "Sdtwoi")
(assume "ExHypi")
(by-assume "ExHypi" "t" "tProp")

(split)
(simp "jDef")
;; ?_50:Sdtwo(J(e* ~e0+2*e0+d0+i))
;; Replace the (nc) vars by cr vars

(simp "<-" "booleProp")
(simp "<-" "boole1Prop")
(simp "<-" "boole0Prop")
(simp "<-" "tProp")
(use "SdtwoMRElim"
 (pt "IntToSdtwo(J(BooleToInt boole* ~(BooleToInt boole1)+
                   2*BooleToInt boole1+BooleToInt boole0+SdtwoToInt t))"))
(simp (pf "J(BooleToInt boole* ~(BooleToInt boole1)+
             2*BooleToInt boole1+BooleToInt boole0+
             SdtwoToInt t)=J(e* ~e0+2*e0+d0+i)"))
(use "SdtwoMRIntToSdtwo")
;; ?_58:abs(J(e* ~e0+2*e0+d0+i))<=2
(use "JProp")
(simp "booleProp")
(simp "boole1Prop")
(simp "boole0Prop")
(simp "tProp")
(use "Truth")

(split)
(simp "kDef")
;; ?_65:Sd(K(e* ~e0+2*e0+d0+i))
(simp "<-" "booleProp")
(simp "<-" "boole1Prop")
(simp "<-" "boole0Prop")
(simp "<-" "tProp")
(use "SdMRElim"
 (pt "IntToSd(K(BooleToInt boole* ~(BooleToInt boole1)+
                   2*BooleToInt boole1+BooleToInt boole0+
                   SdtwoToInt t))"))
(simp (pf "K(BooleToInt boole* ~(BooleToInt boole1) +
             2*BooleToInt boole1+BooleToInt boole0+
             SdtwoToInt t)=K(e* ~e0+2*e0+d0+i)"))
(use "SdMRIntToSd")
(use "KProp")
;; ?_74:abs(e* ~e0+2*e0+d0+i)<=6
(use "IntLeTrans" (pt "IntP 4+IntP 2"))
(use "IntLeTrans" (pt "abs(e* ~e0+2*e0+d0)+abs i"))
(use "IntLeAbsPlus")
(use "IntLeMonPlus")
(use "IntLeTrans" (pt "IntP 3+IntP 1"))
(use "IntLeTrans" (pt "abs(e* ~e0+2*e0)+abs d0"))
(use "IntLeAbsPlus")
(use "IntLeMonPlus")
(use "IntLeTrans" (pt "IntP 1+IntP 2"))
(use "IntLeTrans" (pt "abs(e* ~e0)+abs(2*e0)"))
(use "IntLeAbsPlus")
(use "IntLeMonPlus")
(simp "PsdToAbsOne")
(use "Truth")
(use "IntTimesPsdToPsd")
(use "Psde")
(use "PsdUMinus")
(use "Psde0")
(ng #t)
(simp (pf "abs e0=1"))
(use "Truth")
(use "PsdToAbsOne")
(use "Psde0")
(use "Truth")
(simp (pf "abs d0=1"))
(use "Truth")
(use "PsdToAbsOne")
(use "Psdd0")
(use "Truth")
(use "SdtwoBound")
(use "Sdtwoi")
(use "Truth")
(simp "boole1Prop")
(simp "booleProp")
(simp "boole0Prop")
(simp "tProp")
(use "Truth")
(split)
(use "CoGPsdTimes")
(use "CoGPsdTimes")
(use "CoGz3")
(use "Psde")
(use "Psde0")

;; ?_111:y+(d0+i#4)===(1#4)*(z3*e*e0+j)+k
(simpreal "e0z2Prop")
(simpreal "ez3Prop")
;; ?_117:(1#2)*((1#2)*(z3+IntN 1)* ~e+IntN 1)* ~e0+(d0+i#4)===
;;       (1#4)*(z3*e*e0+j)+k
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z3"))
(assume "cs" "L" "z3Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?_129:~((1#2)*(~((1#2)*(cs n+IntN 1)*e)+IntN 1)*e0)+(d0+i#4)==
;;       (1#4)*(cs n*e*e0+j)+k
(use "RatEqvTrans"
     (pt "(1#2)*(((1#2)*((cs n+IntN 1)* ~e)+IntN 1)* ~e0)+(1#4)*RatPlus d0 i"))
(use "Truth")
(simprat "RatTimesPlusDistrLeft")
(simprat "RatTimesPlusDistrLeft")
(simp "RatTimesIntNL")
(simp "RatTimesIntNL")
(simp (pf "~(RatTimes 1~e)=(e#1)"))
(simp (pf "~(RatTimes 1~e0)=(e0#1)"))
;; ?_138:(1#2)*((1#2)*(cs n* ~e+e)* ~e0+e0)+(1#4)*RatPlus d0 i==
;;       (1#4)*(cs n*e*e0+j)+k
(use "RatEqvTrans"
     (pt "(1#2)*((1#2)*((cs n* ~e+e)* ~e0)+e0)+(1#4)*RatPlus d0 i"))
(use "Truth")
(simprat "RatTimesPlusDistrLeft")
(simprat
 (pf "(1#2)*(cs n* ~e* ~e0+RatTimes e~e0)+e0==
      (1#2)*(cs n* ~e* ~e0+RatTimes e~e0)+(1#2)*(2*e0)"))
(simprat "<-" "RatTimesPlusDistr")
(simp "RatTimesAssoc")
(simp (pf "(1#2)*(1#2)=(1#4)"))
(simprat "<-" "RatTimesPlusDistr")
(simprat (pf "k==(1#4)*(k*4)"))
(simprat "<-" "RatTimesPlusDistr")
(use "RatTimesCompat")
(use "Truth")
;; ?_154:cs n* ~e* ~e0+RatTimes e~e0+2*e0+RatPlus d0 i==cs n*e*e0+j+k*4
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimesAssoc")
(simp (pf "RatTimes~e~e0=RatTimes e e0"))
(simprat (pf "cs n*RatTimes e e0+RatTimes e~e0+2*e0+RatPlus d0 i==
              cs n*RatTimes e e0+(RatTimes e~e0+2*e0+RatPlus d0 i)"))
(simp (pf "cs n*RatTimes e e0+j+k*4=cs n*RatTimes e e0+(j+k*4)"))
(use "RatPlusCompat")
(use "Truth")
;; ?_164:RatTimes e~e0+2*e0+RatPlus d0 i==j+k*4
(simp "jDef")
(simp "kDef")
(simp (pf "J(e* ~e0+2*e0+d0+i)+K(e* ~e0+2*e0+d0+i)*4=
           K(e* ~e0+2*e0+d0+i)*4+J(e* ~e0+2*e0+d0+i)"))
(simp "<-" "KJProp")
;; ?_169:RatTimes e~e0+2*e0+RatPlus d0 i==e* ~e0+2*e0+d0+i
(use "Truth")
(use "IntPlusComm")
;; ?_162:cs n*RatTimes e e0+j+k*4=cs n*RatTimes e e0+(j+k*4)
(simp "<-" "RatPlusAssoc")
(use "Truth")
;; ?_160:cs n*RatTimes e e0+RatTimes e~e0+2*e0+RatPlus d0 i==
;;       cs n*RatTimes e e0+(RatTimes e~e0+2*e0+RatPlus d0 i)
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
;; ?_144:(1#2)*(cs n* ~e* ~e0+RatTimes e~e0)+e0==
;;       (1#2)*(cs n* ~e* ~e0+RatTimes e~e0)+(1#2)*(2*e0)
(use "RatPlusCompat")
(use "Truth")
(use "IntTimesComm")
;; ?_139:~ ~e0=e0
(use "Truth")
(use "Truth")
;; Proof finished.
(save "JKLrzLrvLr")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [t,boole,boole0,boole1,ag]
;;  IntToSdtwo(J(~(BooleToInt boole1*BooleToInt boole0)+
;;             2*BooleToInt boole0+
;;             BooleToInt boole+
;;             SdtwoToInt t))pair 
;;  IntToSd(K(~(BooleToInt boole1*BooleToInt boole0)+
;;           2*BooleToInt boole0+
;;           BooleToInt boole+
;;           SdtwoToInt t))pair 
;;           cCoGPsdTimes(cCoGPsdTimes ag boole1)boole0

;; JKLrzLrvU
(set-goal "allnc i,d0,y(Sdtwo i -> Psd d0 -> CoG y --> allnc e0,z2(
 Psd e0 -> CoG z2 --> y===(1#2)*(z2+IntN 1)* ~e0 -> allnc z3(
 CoH z3 -> z2===(1#2)*z3 ->
 exr j,d,z(Sdtwo j andi Sd d andi CoG z andi y+(d0+i#4)===(1#4)*(z+j)+d))))")
(assume "i" "d0" "y" "Sdtwoi" "Psdd0" "CoGy"
	"e0" "z2" "Psde0" "CoGz2" "e0z2Prop"
        "z3" "CoHz3" "z3Prop")

(assert "exnc j j=J(2*e0+d0+i)")
(intro 0 (pt "J(2*e0+d0+i)"))
(use "Truth")
(assume "ExHypj")
(by-assume "ExHypj" "j" "jDef")

(assert "exnc k k=K(2*e0+d0+i)")
(intro 0 (pt "K(2*e0+d0+i)"))
(use "Truth")
(assume "ExHypk")
(by-assume "ExHypk" "k" "kDef")

(intro 0 (pt "j"))
(intro 0 (pt "k"))
(intro 0 (pt "z3* ~e0"))

(assert "exl boole BooleToInt boole=e0")
(use "PsdToBooleToIntValue")
(use "Psde0")
(assume "ExHype0")
(by-assume "ExHype0" "boole1" "boole1Prop")

(assert "exl boole BooleToInt boole=d0")
(use "PsdToBooleToIntValue")
(use "Psdd0")
(assume "ExHypd0")
(by-assume "ExHypd0" "boole0" "boole0Prop")

(assert "exl t SdtwoToInt t=i")
(use "SdtwoToSdtwoToIntValue")
(use "Sdtwoi")
(assume "ExHypi")
(by-assume "ExHypi" "t" "tProp")

(split)
(simp "jDef")
;; ?_43:Sdtwo(J(2*e0+d0+i))
;; Replace the vars by cr vars
(simp "<-" "boole1Prop")
(simp "<-" "boole0Prop")
(simp "<-" "tProp")
(use "SdtwoMRElim"
 (pt "IntToSdtwo(J(2*BooleToInt boole1+BooleToInt boole0+SdtwoToInt t))"))
(simp (pf "J(2*BooleToInt boole1+BooleToInt boole0+
             SdtwoToInt t)=J(2*e0+d0+i)"))
(use "SdtwoMRIntToSdtwo")
;; ?_50:abs(J(2*e0+d0+i))<=2
(use "JProp")
(simp "boole1Prop")
(simp "boole0Prop")
(simp "tProp")
(use "Truth")

(split)
(simp "kDef")
;; ?_56:Sd(K(2*e0+d0+i))
(simp "<-" "boole1Prop")
(simp "<-" "boole0Prop")
(simp "<-" "tProp")
(use "SdMRElim"
 (pt "IntToSd(K(2*BooleToInt boole1+BooleToInt boole0+SdtwoToInt t))"))
(simp (pf "K(2*BooleToInt boole1+BooleToInt boole0+
             SdtwoToInt t)=K(2*e0+d0+i)"))
(use "SdMRIntToSd")
(use "KProp")
;; ?_64:abs(2*e0+d0+i)<=6
(use "IntLeTrans" (pt "IntP 3+IntP 2"))
(use "IntLeTrans" (pt "abs(2*e0+d0)+abs i"))
(use "IntLeAbsPlus")
(use "IntLeMonPlus")
(use "IntLeTrans" (pt "IntP 2+IntP 1"))
(use "IntLeTrans" (pt "abs(2*e0)+abs d0"))
(use "IntLeAbsPlus")
(use "IntLeMonPlus")
(ng #t)
(simp (pf "abs e0=1"))
(use "Truth")
(use "PsdToAbsOne")
(use "Psde0")
(simp (pf "abs d0=1"))
(use "Truth")
(use "PsdToAbsOne")
(use "Psdd0")
(use "Truth")
(use "SdtwoBound")
(use "Sdtwoi")
(use "Truth")
(simp "boole1Prop")
(simp "boole0Prop")
(simp "tProp")
(use "Truth")

(split)
(use "CoGPsdTimes")
(use "CoHToCoG")
(use "CoHz3")
(use "PsdUMinus")
(use "Psde0")

;; ?_89:y+(d0+i#4)===(1#4)*(z3* ~e0+j)+k
(simpreal "e0z2Prop")
(simpreal "z3Prop")
;; ?_95:(1#2)*((1#2)*z3+IntN 1)* ~e0+(d0+i#4)===(1#4)*(z3* ~e0+j)+k
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z3"))
(assume "cs" "L" "z3Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?_107:~((1#2)*((1#2)*cs n+IntN 1)*e0)+(d0+i#4)==(1#4)*(~(cs n*e0)+j)+k
(use "RatEqvTrans"
 (pt "(1#2)*(((1#2)*cs n+IntN 1)* ~e0)+(1#4)*RatPlus d0 i"))
(use "Truth")
(simprat "RatTimesPlusDistrLeft")
(simp "RatTimesIntNL")
(simp (pf "~(RatTimes 1~e0)=(e0#1)"))
;; ?_112:(1#2)*((1#2)*cs n* ~e0+e0)+(1#4)*RatPlus d0 i==(1#4)*(cs n* ~e0+j)+k
(simp (pf "(1#2)*cs n* ~e0=(1#2)*(cs n* ~e0)"))
(simprat (pf "(1#2)*((1#2)*(cs n* ~e0)+e0)==
              (1#2)*((1#2)*(cs n* ~e0)+(1#2)*(2*e0))"))
(simprat "<-" "RatTimesPlusDistr")
(simp "RatTimesAssoc")
(simp (pf "(1#2)*(1#2)=(1#4)"))
(simprat "<-" "RatTimesPlusDistr")
(simprat (pf "k==(1#4)*(k*4)"))
(simprat "<-" "RatTimesPlusDistr")
(use "RatTimesCompat")
(use "Truth")
;; ?_127:cs n* ~e0+2*e0+RatPlus d0 i==cs n* ~e0+j+k*4
(simp (pf "cs n* ~e0+2*e0+RatPlus d0 i=cs n* ~e0+(2*e0+RatPlus d0 i)"))
(simp (pf "cs n* ~e0+j+k*4=cs n* ~e0+(j+k*4)"))
(use "RatPlusCompat")
(use "Truth")
;; ?_133:2*e0+RatPlus d0 i==j+k*4
(simp "jDef")
(simp "kDef")
(simp (pf "J(2*e0+d0+i)+K(2*e0+d0+i)*4=K(2*e0+d0+i)*4+J(2*e0+d0+i)"))
(simp "<-" "KJProp")
;; ?_138:2*e0+RatPlus d0 i==2*e0+d0+i
(use "Truth")
(use "IntPlusComm")
;; ?_131:cs n* ~e0+j+k*4=acs n* ~e0+(j+k*4)
(simp "<-" "RatPlusAssoc")
(use "Truth")
;; ?_129:cs n* ~e0+2*e0+RatPlus d0 i=cs n* ~e0+(2*e0+RatPlus d0 i)
(simp "<-" "RatPlusAssoc")
(use "Truth")
(use "Truth")
(use "Truth")
;; ?_117:(1#2)*((1#2)*(cs n* ~e0)+e0)==(1#2)*((1#2)*(cs n* ~e0)+(1#2)*(2*e0))
(use "RatTimesCompat")
(use "Truth")
;; ?_142:(1#2)*(cs n* ~e0)+e0==(1#2)*(cs n* ~e0)+(1#2)*(2*e0)
(use "RatPlusCompat")
(use "Truth")
(use "IntTimesComm")
;; ?_115:(1#2)*cs n* ~e0=(1#2)*(cs n* ~e0)
(use "Truth")
(use "Truth")
;; Proof finished.
(save "JKLrzLrvU")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [t,boole,boole0,ah]
;;  IntToSdtwo(J(2*BooleToInt boole0+
;;             BooleToInt boole+
;;             SdtwoToInt t))pair 
;;  IntToSd(K(2*BooleToInt boole0+
;;          BooleToInt boole+
;;          SdtwoToInt t))pair 
;;  cCoGPsdTimes(cCoHToCoG ah)(cPsdUMinus boole0)

;; JKLrzLrv
(set-goal "allnc i,d0,y(Sdtwo i -> Psd d0 -> CoG y --> allnc e0,z2(
 Psd e0 -> CoG z2 -> y===(1#2)*(z2+IntN 1)* ~e0 ->
 exr j,d,z(Sdtwo j andi Sd d andi CoG z andi y+(d0+i#4)===(1#4)*(z+j)+d)))")
(assume "i" "d0" "y" "Sdtwoi" "Psdd0" "CoGy"
	"e0" "z2" "Psde0" "CoGz2" "e0z2Prop")
(inst-with-to "CoGClosure" (pt "z2") "CoGz2" "z2Cases")
(elim "z2Cases")
;; 5,6
(drop "z2Cases")

;; Subcase Lrz2
(assume "ExHypz2")
(by-assume "ExHypz2" "e" "eProp")
(by-assume "eProp" "z3" "ez3Prop")

(use-with "JKLrzLrvLr"
 (pt "i") (pt "d0") (pt "y") "Sdtwoi" "Psdd0" "CoGy"
 (pt "e0") (pt "z2") "Psde0" "CoGz2" "e0z2Prop"
 (pt "e") (pt "z3") "?" "?" "?")
(use "ez3Prop")
(use "ez3Prop")
(use "ez3Prop")

;; ?_6:exr x(CoH x andl z2===(1#2)*x) -> 
;;     exr j,d,z(Sdtwo j andd Sd d andd CoG z andl y+(d0+i#4)===(1#4)*(z+j)+d)

(drop "z2Cases")

;; Subcase Uz2
(assume "ExHypz2")
(by-assume "ExHypz2" "z3" "z3Prop")

(use-with "JKLrzLrvU"
 (pt "i") (pt "d0") (pt "y") "Sdtwoi" "Psdd0" "CoGy"
 (pt "e0") (pt "z2") "Psde0" "CoGz2" "e0z2Prop"
 (pt "z3") "?" "?")
(use "z3Prop")
(use "z3Prop")
;; Proof finished.
(save "JKLrzLrv")
;; (cdp)

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [t,boole,boole0,ag]
;;  [case (cCoGClosure ag)
;;    (InL bg -> cJKLrzLrvLr t boole boole0 clft bg crht bg)
;;    (InR ah -> cJKLrzLrvU t boole boole0 ah)]

(animate "CoGClosure")
(animate "JKLrzLrvLr")
(animate "JKLrzLrvU")

(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [t,boole,boole0,ag]
;;  [case (DesYprod ag)
;;    (InL bg -> 
;;    IntToSdtwo
;;    (J(~(BooleToInt clft bg*BooleToInt boole0)+2*BooleToInt boole0+
;;      BooleToInt boole+
;;      SdtwoToInt t))pair 
;;    IntToSd
;;    (K(~(BooleToInt clft bg*BooleToInt boole0)+2*BooleToInt boole0+
;;      BooleToInt boole+
;;      SdtwoToInt t))pair 
;;    cCoGPsdTimes(cCoGPsdTimes crht bg clft bg)boole0)
;;    (InR ah -> 
;;    IntToSdtwo(J(2*BooleToInt boole0+BooleToInt boole+SdtwoToInt t))pair 
;;    IntToSd(K(2*BooleToInt boole0+BooleToInt boole+SdtwoToInt t))pair 
;;    cCoGPsdTimes(cCoHToCoG ah)(cPsdUMinus boole0))]

(deanimate "CoGClosure")
(deanimate "JKLrzLrvLr")
(deanimate "JKLrzLrvU")

;; JKLrzUvFin
(set-goal "allnc i,d0,y(Sdtwo i -> Psd d0 -> CoG y --> allnc z2(
 CoH z2 --> y===(1#2)*z2 -> allnc e,z3(
 Psd e -> CoG z3 -> z2===(1#2)*(z3+1)*e ->
 exr j,d,z(Sdtwo j andi Sd d andi CoG z andi y+(d0+i#4)===(1#4)*(z+j)+d))))")
(assume "i" "d0" "y" "Sdtwoi" "Psdd0" "CoGy"
	"z2" "CoHz2" "z2Prop"
        "e" "z3" "Psde" "CoGz3" "ez3Prop")

(assert "exnc j j=J(e+d0+i)")
(intro 0 (pt "J(e+d0+i)"))
(use "Truth")
(assume "ExHypj")
(by-assume "ExHypj" "j" "jDef")

(assert "exnc k k=K(e+d0+i)")
(intro 0 (pt "K(e+d0+i)"))
(use "Truth")
(assume "ExHypk")
(by-assume "ExHypk" "k" "kDef")

(intro 0 (pt "j"))
(intro 0 (pt "k"))
(intro 0 (pt "z3*e"))

(assert "exl boole BooleToInt boole=e")
(use "PsdToBooleToIntValue")
(use "Psde")
(assume "ExHype")
(by-assume "ExHype" "boole" "booleProp")

(assert "exl boole BooleToInt boole=d0")
(use "PsdToBooleToIntValue")
(use "Psdd0")
(assume "ExHypd0")
(by-assume "ExHypd0" "boole0" "boole0Prop")

(assert "exl t SdtwoToInt t=i")
(use "SdtwoToSdtwoToIntValue")
(use "Sdtwoi")
(assume "ExHypi")
(by-assume "ExHypi" "t" "tProp")

(split)
(simp "jDef")
;; Replace the vars by cr vars
(simp "<-" "booleProp")
(simp "<-" "boole0Prop")
(simp "<-" "tProp")
(use "SdtwoMRElim"
 (pt "IntToSdtwo(J(BooleToInt boole+BooleToInt boole0+SdtwoToInt t))"))
(simp (pf "J(BooleToInt boole+BooleToInt boole0+SdtwoToInt t)=
           J(e+d0+i)"))
(use "SdtwoMRIntToSdtwo")
;; ?_50:abs(J(e+d0+i))<=2
(use "JProp")
(simp "booleProp")
(simp "boole0Prop")
(simp "tProp")
(use "Truth")

(split)
(simp "kDef")
;; ?_56:Sd(K(e+d0+i))
(simp "<-" "booleProp")
(simp "<-" "boole0Prop")
(simp "<-" "tProp")
(use "SdMRElim"
 (pt "IntToSd(K(BooleToInt boole+BooleToInt boole0+SdtwoToInt t))"))
(simp (pf "K(BooleToInt boole+BooleToInt boole0+
             SdtwoToInt t)=K(e+d0+i)"))
(use "SdMRIntToSd")
(use "KProp")
;; ?_64:abs(e+d0+i)<=6
(use "IntLeTrans" (pt "IntP 2+IntP 2"))
(use "IntLeTrans" (pt "abs(e+d0)+abs i"))
(use "IntLeAbsPlus")
(use "IntLeMonPlus")
(use "IntLeTrans" (pt "IntP 1+IntP 1"))
(use "IntLeTrans" (pt "abs e+abs d0"))
(use "IntLeAbsPlus")
(use "IntLeMonPlus")
(simp (pf "abs e=1"))
(use "Truth")
(use "PsdToAbsOne")
(use "Psde")
(simp (pf "abs d0=1"))
(use "Truth")
(use "PsdToAbsOne")
(use "Psdd0")
(use "Truth")
(use "SdtwoBound")
(use "Sdtwoi")
(use "Truth")
(simp "booleProp")
(simp "boole0Prop")
(simp "tProp")
(use "Truth")

(split)
(use "CoGPsdTimes")
(use "CoGz3")
(use "Psde")

;; ?_88:y+(d0+i#4)===(1#4)*(z3*e+j)+k
(simpreal "z2Prop")
(simpreal "ez3Prop")
;; ?_92:(1#2)*((1#2)*(z3+1)*e)+(d0+i#4)===(1#4)*(z3*e+j)+k
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z3"))
(assume "cs" "L" "z3Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?_104:(1#4)*(cs n+1)*e+(d0+i#4)==(1#4)*(cs n*e+j)+k
(use "RatEqvTrans" (pt "(1#4)*(cs n+1)*e+(1#4)*RatPlus d0 i"))
(use "Truth")
;; ?_106:(1#4)*(cs n+1)*e+(1#4)*RatPlus d0 i==(1#4)*(cs n*e+j)+k
(simp (pf "(1#4)*(cs n+1)*e=(1#4)*((cs n+1)*e)"))
(simprat "RatTimesPlusDistrLeft")
(simprat (pf "k==(1#4)*(k*4)"))
(simprat "<-" "RatTimesPlusDistr")
(simprat "<-" "RatTimesPlusDistr")
(use "RatTimesCompat")
(use "Truth")
;; ?_115:cs n*e+RatTimes 1 e+RatPlus d0 i==cs n*e+j+k*4
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
;; ?_119:RatTimes 1 e+RatPlus d0 i==RatPlus j(k*4)
(simp "jDef")
(simp "kDef")
(simp (pf "RatPlus(J(e+d0+i))(K(e+d0+i)*4)=K(e+d0+i)*4+J(e+d0+i)"))
(simp "<-" "KJProp")
;; ?_124:RatTimes 1 e+RatPlus d0 i==e+d0+i
(use "Truth")
(use "IntPlusComm")
(use "Truth")
(use "Truth")
;; Proof finished.
(save "JKLrzUvFin")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [t,boole,boole0,ag]
;;  IntToSdtwo(J(BooleToInt boole0+BooleToInt boole+SdtwoToInt t))pair 
;;  IntToSd(K(BooleToInt boole0+BooleToInt boole+SdtwoToInt t))pair 
;;  cCoGPsdTimes ag boole0

;; JKLrzUvD
(set-goal "allnc i,d0,y(Sdtwo i -> Psd d0 -> CoG y --> allnc z2(
 CoH z2 --> y===(1#2)*z2 -> allnc z3(
 CoH z3 -> z2===(1#2)*z3 ->
 exr j,d,z(Sdtwo j andi Sd d andi CoG z andi y+(d0+i#4)===(1#4)*(z+j)+d))))")
(assume "i" "d0" "y" "Sdtwoi" "Psdd0" "CoGy"
	"z2" "CoHz2" "z2Prop"
        "z3" "CoHz3" "z3Prop")

(assert "exnc j j=J(d0+i)")
(intro 0 (pt "J(d0+i)"))
(use "Truth")
(assume "ExHypj")
(by-assume "ExHypj" "j" "jDef")

(assert "exnc k k=K(d0+i)")
(intro 0 (pt "K(d0+i)"))
(use "Truth")
(assume "ExHypk")
(by-assume "ExHypk" "k" "kDef")

(intro 0 (pt "j"))
(intro 0 (pt "k"))
(intro 0 (pt "z3"))

(assert "exl boole BooleToInt boole=d0")
(use "PsdToBooleToIntValue")
(use "Psdd0")
(assume "ExHypd0")
(by-assume "ExHypd0" "boole0" "boole0Prop")

(assert "exl t SdtwoToInt t=i")
(use "SdtwoToSdtwoToIntValue")
(use "Sdtwoi")
(assume "ExHypi")
(by-assume "ExHypi" "t" "tProp")

(split)
(simp "jDef")
;; ?_36:Sdtwo(J(d0+i))
;; Replace vars by cr vars
(simp "<-" "boole0Prop")
(simp "<-" "tProp")
(use "SdtwoMRElim"
 (pt "IntToSdtwo(J(BooleToInt boole0+SdtwoToInt t))"))
(simp (pf "J(BooleToInt boole0+SdtwoToInt t)=J(d0+i)"))
(use "SdtwoMRIntToSdtwo")
;; ?_42:abs(J(d0+i))<=2
(use "JProp")
(simp "boole0Prop")
(simp "tProp")
(use "Truth")

(split)
(simp "kDef")
;; ?_47:Sd(K(d0+i))
(simp "<-" "boole0Prop")
(simp "<-" "tProp")
(use "SdMRElim" (pt "IntToSd(K(BooleToInt boole0+SdtwoToInt t))"))
(simp (pf "K(BooleToInt boole0+SdtwoToInt t)=K(d0+i)"))
(use "SdMRIntToSd")
(use "KProp")
;; ?_54:abs(d0+i)<=6
(use "IntLeTrans" (pt "IntP 1+IntP 2"))
(use "IntLeTrans" (pt "abs d0+abs i"))
(use "IntLeAbsPlus")
(use "IntLeMonPlus")
(simp (pf "abs d0=1"))
(use "Truth")
(use "PsdToAbsOne")
(use "Psdd0")
(use "SdtwoBound")
(use "Sdtwoi")
(use "Truth")
(simp "boole0Prop")
(simp "tProp")
(use "Truth")

(split)
(use "CoHToCoG")
(use "CoHz3")

;; ?_68:y+(d0+i#4)===(1#4)*(z3+j)+k
(simpreal "z2Prop")
(simpreal "z3Prop")
;; ?_71:(1#2)*((1#2)*z3)+(d0+i#4)===(1#4)*(z3+j)+k
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "z3"))
(assume "cs" "L" "z3Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?_79:(1#4)*cs n+(d0+i#4)==(1#4)*(cs n+j)+k
(use "RatEqvTrans" (pt "(1#4)*cs n+(1#4)*RatPlus d0 i"))
(use "Truth")
(simprat "<-" "RatTimesPlusDistr")
(simprat (pf "k==(1#4)*(k*4)"))
(simprat "<-" "RatTimesPlusDistr")
(use "RatTimesCompat")
(use "Truth")
;; ?_87:cs n+RatPlus d0 i==cs n+j+k*4
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
(ng #t)
;; ?_91:d0+i=j+k*4
(simp "jDef")
(simp "kDef")
(simp (pf "J(d0+i)+K(d0+i)*4=K(d0+i)*4+J(d0+i)"))
(use "KJProp")
(use "IntPlusComm")
(use "Truth")
;; Proof finished.
(save "JKLrzUvD")
;; (cdp)

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [t,boole,ah]
;;  IntToSdtwo(J(BooleToInt boole+SdtwoToInt t))pair 
;;  IntToSd(K(BooleToInt boole+SdtwoToInt t))pair cCoHToCoG ah

;; JKLrzUv
(set-goal "allnc i,d0,y(Sdtwo i -> Psd d0 -> CoG y --> allnc z2(
 CoH z2 -> y===(1#2)*z2 ->
 exr j,d,z(Sdtwo j andi Sd d andi CoG z andi y+(d0+i#4)===(1#4)*(z+j)+d)))")
(assume "i" "d0" "y" "Sdtwoi" "Psdd0" "CoGy"
	"z2" "CoHz2" "z2Prop")
(inst-with-to "CoHClosure" (pt "z2") "CoHz2" "z2Cases")
(elim "z2Cases")
;; 5,6
(drop "z2Cases")

;; Subcase Lrz2
(assume "ExHypz2")
(by-assume "ExHypz2" "e" "eProp")
(by-assume "eProp" "z3" "ez3Prop")

(use-with "JKLrzUvFin"
 (pt "i") (pt "d0") (pt "y") "Sdtwoi" "Psdd0" "CoGy"
 (pt "z2") "CoHz2" "z2Prop"
 (pt "e") (pt "z3") "?" "?" "?")
(use "ez3Prop")
(use "ez3Prop")
(use "ez3Prop")

;; ?_6:exr x(CoH x andl z2===(1#2)*x) -> 
;;     exr j,d,z(Sdtwo j andd Sd d andd CoG z andl y+(d0+i#4)===(1#4)*(z+j)+d)

(drop "z2Cases")

;; Subcase Uz2
(assume "ExHypz2")
(by-assume "ExHypz2" "z3" "z3Prop")

(use-with "JKLrzUvD"
 (pt "i") (pt "d0") (pt "y") "Sdtwoi" "Psdd0" "CoGy"
 (pt "z2") "CoHz2" "z2Prop"
 (pt "z3") "?" "?")
(use "z3Prop")
(use "z3Prop")
;; Proof finished.
(save "JKLrzUv")
;; (cdp)

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [t,boole,ah]
;;  [case (cCoHClosure ah)
;;    (InL bg -> cJKLrzUvFin t boole clft bg crht bg)
;;    (InR ah -> cJKLrzUvD t boole ah)]

(animate "CoHClosure")
(animate "JKLrzUvFin")
(animate "JKLrzUvD")

(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [t,boole,ah]
;;  [case (DesYprod ah)
;;    (InL bg -> 
;;    IntToSdtwo(J(BooleToInt clft bg+BooleToInt boole+SdtwoToInt t))pair 
;;    IntToSd(K(BooleToInt clft bg+BooleToInt boole+SdtwoToInt t))pair 
;;    cCoGPsdTimes crht bg clft bg)
;;    (InR ah0 -> 
;;    IntToSdtwo(J(BooleToInt boole+SdtwoToInt t))pair 
;;    IntToSd(K(BooleToInt boole+SdtwoToInt t))pair cCoHToCoG ah0)]

(deanimate "CoHClosure")
(deanimate "JKLrzUvFin")
(deanimate "JKLrzUvD")

;; JKLrz
(set-goal "allnc i,d0,y(Sdtwo i -> Psd d0 -> CoG y ->
 exr j,d,z(Sdtwo j andi Sd d andi CoG z andi y+(d0+i#4)===(1#4)*(z+j)+d))")
(assume "i" "d0" "y" "Sdtwoi" "Psdd0" "CoGy")
(inst-with-to "CoGClosure" (pt "y") "CoGy" "vCases")
(elim "vCases")
;; 5,6
(drop "vCases")

;; Case Lrv
(assume "ExHyp")
(by-assume "ExHyp" "e0" "e0Prop")
(by-assume "e0Prop" "z2" "e0z2Prop")

;; (pp "JKLrzLrv")
(use-with "JKLrzLrv"
 (pt "i") (pt "d0") (pt "y") "Sdtwoi" "Psdd0" "CoGy"
 (pt "e0") (pt "z2") "?" "?" "?")
(use "e0z2Prop")
(use "e0z2Prop")
(use "e0z2Prop")

;; ?_6:exr x(CoH x andl y===(1#2)*x) -> 
;;     exr j,d,z(Sdtwo j andd Sd d andd CoG z andl y+(d0+i#4)===(1#4)*(z+j)+d)

(drop "vCases")

;; Case Uv
(assume "ExHyp")
(by-assume "ExHyp" "z2" "z2Prop")

;; (pp "JKLrzUv")
(use "JKLrzUv" (pt "z2"))
(use "Sdtwoi")
(use "Psdd0")
(use "CoGy")
(use "z2Prop")
(use "z2Prop")
;; Proof finished.
(save "JKLrz")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [t,boole,ag]
;;  [case (cCoGClosure ag)
;;    (InL bg -> cJKLrzLrv t boole clft bg crht bg)
;;    (InR ah -> cJKLrzUv t boole ah)]

(animate "CoGClosure")
(animate "CoHClosure")
(animate "JKLrzLrvLr")
(animate "JKLrzLrvU")
(animate "JKLrzLrv")
(animate "JKLrzUvFin")
(animate "JKLrzUvD")
(animate "JKLrzUv")

(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [t,boole,ag]
;;  [case (DesYprod ag)
;;    (InL bg -> 
;;    [case (DesYprod crht bg)
;;      (InL bg0 -> 
;;      IntToSdtwo
;;      (J
;;       (~(BooleToInt clft bg0*BooleToInt clft bg)+2*BooleToInt clft bg+
;;        BooleToInt boole+
;;        SdtwoToInt t))pair 
;;      IntToSd
;;      (K
;;       (~(BooleToInt clft bg0*BooleToInt clft bg)+2*BooleToInt clft bg+
;;        BooleToInt boole+
;;        SdtwoToInt t))pair 
;;      cCoGPsdTimes(cCoGPsdTimes crht bg0 clft bg0)clft bg)
;;      (InR ah -> 
;;      IntToSdtwo(J(2*BooleToInt clft bg+BooleToInt boole+SdtwoToInt t))pair 
;;      IntToSd(K(2*BooleToInt clft bg+BooleToInt boole+SdtwoToInt t))pair 
;;      cCoGPsdTimes(cCoHToCoG ah)(cPsdUMinus clft bg))])
;;    (InR ah -> 
;;    [case (DesYprod ah)
;;      (InL bg -> 
;;      IntToSdtwo(J(BooleToInt clft bg+BooleToInt boole+SdtwoToInt t))pair 
;;      IntToSd(K(BooleToInt clft bg+BooleToInt boole+SdtwoToInt t))pair 
;;      cCoGPsdTimes crht bg clft bg)
;;      (InR ah0 -> 
;;      IntToSdtwo(J(BooleToInt boole+SdtwoToInt t))pair 
;;      IntToSd(K(BooleToInt boole+SdtwoToInt t))pair cCoHToCoG ah0)])]

(deanimate "CoGClosure")
(deanimate "CoHClosure")
(deanimate "JKLrzLrvLr")
(deanimate "JKLrzLrvU")
(deanimate "JKLrzLrv")
(deanimate "JKLrzUvFin")
(deanimate "JKLrzUvD")
(deanimate "JKLrzUv")

;; JKUzLrvLr
(set-goal "allnc i,y(Sdtwo i -> CoG y --> allnc e0,z2(
 Psd e0 -> CoG z2 --> y===(1#2)*(z2+IntN 1)* ~e0 -> allnc e,z3(
 Psd e -> CoG z3 -> z2===(1#2)*(z3+IntN 1)* ~e ->
 exr j,d,z(Sdtwo j andi Sd d andi CoG z andi y+(i#4)===(1#4)*(z+j)+d))))")
(assume "i" "y" "Sdtwoi" "CoGy"
	"e0" "z2" "Psde0" "CoGz2" "e0z2Prop"
        "e" "z3" "Psde" "CoGz3" "ez3Prop")

(assert "exnc j j=J(e* ~e0+2*e0+i)")
(intro 0 (pt "J(e* ~e0+2*e0+i)"))
(use "Truth")
(assume "ExHypj")
(by-assume "ExHypj" "j" "jDef")

(assert "exnc k k=K(e* ~e0+2*e0+i)")
(intro 0 (pt "K(e* ~e0+2*e0+i)"))
(use "Truth")
(assume "ExHypk")
(by-assume "ExHypk" "k" "kDef")

(intro 0 (pt "j"))
(intro 0 (pt "k"))
(intro 0 (pt "z3*e*e0"))

(assert "exl boole BooleToInt boole=e")
(use "PsdToBooleToIntValue")
(use "Psde")
(assume "ExHype")
(by-assume "ExHype" "boole" "booleProp")

(assert "exl boole BooleToInt boole=e0")
(use "PsdToBooleToIntValue")
(use "Psde0")
(assume "ExHype0")
(by-assume "ExHype0" "boole1" "boole1Prop")

(assert "exl t SdtwoToInt t=i")
(use "SdtwoToSdtwoToIntValue")
(use "Sdtwoi")
(assume "ExHypi")
(by-assume "ExHypi" "t" "tProp")

(split)
(simp "jDef")
;; ?_43:Sdtwo(J(e* ~e0+2*e0+i))
;; Replace the (nc) vars by cr vars

(simp "<-" "booleProp")
(simp "<-" "boole1Prop")
(simp "<-" "tProp")
(use "SdtwoMRElim"
 (pt "IntToSdtwo(J(BooleToInt boole* ~(BooleToInt boole1)+
                   2*BooleToInt boole1+SdtwoToInt t))"))
(simp (pf "J(BooleToInt boole* ~(BooleToInt boole1)+
             2*BooleToInt boole1+SdtwoToInt t)=J(e* ~e0+2*e0+i)"))
(use "SdtwoMRIntToSdtwo")
;; ?_50:abs(J(e* ~e0+2*e0+i))<=2
(use "JProp")
(simp "booleProp")
(simp "boole1Prop")
(simp "tProp")
(use "Truth")

(split)
(simp "kDef")
;; ?_56:Sd(K(e* ~e0+2*e0+i))
(simp "<-" "booleProp")
(simp "<-" "boole1Prop")
(simp "<-" "tProp")
(use "SdMRElim"
 (pt "IntToSd(K(BooleToInt boole* ~(BooleToInt boole1)+
                   2*BooleToInt boole1+SdtwoToInt t))"))
(simp (pf "K(BooleToInt boole* ~(BooleToInt boole1) +
             2*BooleToInt boole1+SdtwoToInt t)=K(e* ~e0+2*e0+i)"))
(use "SdMRIntToSd")
(use "KProp")
;; ?_64:abs(e* ~e0+2*e0+i)<=6
(use "IntLeTrans" (pt "IntP 3+IntP 2"))
(use "IntLeTrans" (pt "abs(e* ~e0+2*e0)+abs i"))
(use "IntLeAbsPlus")
(use "IntLeMonPlus")
(use "IntLeTrans" (pt "IntP 1+IntP 2"))
(use "IntLeTrans" (pt "abs(e* ~e0)+abs(2*e0)"))
(use "IntLeAbsPlus")
(use "IntLeMonPlus")
(simp "PsdToAbsOne")
(use "Truth")
(use "IntTimesPsdToPsd")
(use "Psde")
(use "PsdUMinus")
(use "Psde0")
(ng #t)
(simp (pf "abs e0=1"))
(use "Truth")
(use "PsdToAbsOne")
(use "Psde0")
(use "Truth")
(use "SdtwoBound")
(use "Sdtwoi")
(use "Truth")
(simp "boole1Prop")
(simp "booleProp")
(simp "tProp")
(use "Truth")

(split)
(use "CoGPsdTimes")
(use "CoGPsdTimes")
(use "CoGz3")
(use "Psde")
(use "Psde0")

;; ?_91:y+(i#4)===(1#4)*(z3*e*e0+j)+k
(simpreal "e0z2Prop")
(simpreal "ez3Prop")

;; ?_97:(1#2)*((1#2)*(z3+IntN 1)* ~e+IntN 1)* ~e0+(i#4)===(1#4)*(z3*e*e0+j)+k
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z3"))
(assume "cs" "L" "z3Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?_109:(1#2)*((1#2)*(cs n+IntN 1)* ~e+IntN 1)* ~e0+(i#4)==
;;       (1#4)*(cs n*e*e0+j)+k
(use "RatEqvTrans"
 (pt "(1#2)*(((1#2)*((cs n+IntN 1)* ~e)+IntN 1)* ~e0)+(i#4)"))
(use "Truth")
(simprat "RatTimesPlusDistrLeft")
(simprat "RatTimesPlusDistrLeft")
(simp "RatTimesIntNL")
(simp "RatTimesIntNL")
(simp (pf "~(RatTimes 1~e)=(e#1)"))
(simp (pf "~(RatTimes 1~e0)=(e0#1)"))
;; ?_118:(1#2)*((1#2)*(cs n* ~e+e)* ~e0+e0)+(i#4)==(1#4)*(cs n*e*e0+j)+k
(use "RatEqvTrans" (pt "(1#2)*((1#2)*((cs n* ~e+e)* ~e0)+e0)+(i#4)"))
(use "Truth")
(simprat "RatTimesPlusDistrLeft")
(simprat
 (pf "(1#2)*(cs n* ~e* ~e0+RatTimes e~e0)+e0==
      (1#2)*(cs n* ~e* ~e0+RatTimes e~e0)+(1#2)*(2*e0)"))
(simprat "<-" "RatTimesPlusDistr")
(simp "RatTimesAssoc")
(simp (pf "(1#2)*(1#2)=(1#4)"))
(simp (pf "(i#4)=(1#4)*i"))
(simprat "<-" "RatTimesPlusDistr")
(simprat (pf "k==(1#4)*(k*4)"))
(simprat "<-" "RatTimesPlusDistr")
(use "RatTimesCompat")
(use "Truth")
;; ?_136:cs n* ~e* ~e0+RatTimes e~e0+2*e0+i==cs n*e*e0+j+k*4
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimesAssoc")
(simp (pf "RatTimes~e~e0=RatTimes e e0"))
(simprat (pf "cs n*RatTimes e e0+RatTimes e~e0+2*e0+i==
              cs n*RatTimes e e0+(RatTimes e~e0+2*e0+i)"))
(simp (pf "cs n*RatTimes e e0+j+k*4=cs n*RatTimes e e0+(j+k*4)"))
(use "RatPlusCompat")
(use "Truth")
;; ?_146:RatTimes e~e0+2*e0+i==j+k*4
(simp "jDef")
(simp "kDef")
(simp (pf "J(e* ~e0+2*e0+i)+K(e* ~e0+2*e0+i)*4=
           K(e* ~e0+2*e0+i)*4+J(e* ~e0+2*e0+i)"))
(simp "<-" "KJProp")
;; ?_151:RatTimes e~e0+2*e0+i==e* ~e0+2*e0+i
(use "Truth")
(use "IntPlusComm")
;; ?_144:cs n*RatTimes e e0+j+k*4=cs n*RatTimes e e0+(j+k*4)
(simp "<-" "RatPlusAssoc")
(use "Truth")
;; ?_142:cs n*RatTimes e e0+RatTimes e~e0+2*e0+i==
;;       cs n*RatTimes e e0+(RatTimes e~e0+2*e0+i)
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
;; ?_124:(1#2)*(cs n* ~e* ~e0+RatTimes e~e0)+e0==
;;       (1#2)*(cs n* ~e* ~e0+RatTimes e~e0)+(1#2)*(2*e0)
(use "RatPlusCompat")
(use "Truth")
(use "IntTimesComm")
;; ?_119:~ ~e0=e0
(use "Truth")
(use "Truth")
;; Proof finished.
(save "JKUzLrvLr")
;; (cdp)

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [t,boole,boole0,ag]
;;  IntToSdtwo(J(~(BooleToInt boole0*BooleToInt boole)+
;;               2*BooleToInt boole+SdtwoToInt t))pair 
;;  IntToSd(K(~(BooleToInt boole0*BooleToInt boole)+
;;            2*BooleToInt boole+SdtwoToInt t))pair 
;;  cCoGPsdTimes(cCoGPsdTimes ag boole0)boole

;; JKUzLrvU
(set-goal "allnc i,y(Sdtwo i -> CoG y --> allnc e0,z2(
 Psd e0 -> CoG z2 --> y===(1#2)*(z2+IntN 1)* ~e0 -> allnc z3(
 CoH z3 -> z2===(1#2)*z3 ->
 exr j,d,z(Sdtwo j andi Sd d andi CoG z andi y+(i#4)===(1#4)*(z+j)+d))))")
(assume "i" "y" "Sdtwoi" "CoGy"
	"e0" "z2" "Psde0" "CoGz2" "e0z2Prop"
        "z3" "CoHz3" "z3Prop")

(assert "exnc j j=J(2*e0+i)")
(intro 0 (pt "J(2*e0+i)"))
(use "Truth")
(assume "ExHypj")
(by-assume "ExHypj" "j" "jDef")

(assert "exnc k k=K(2*e0+i)")
(intro 0 (pt "K(2*e0+i)"))
(use "Truth")
(assume "ExHypk")
(by-assume "ExHypk" "k" "kDef")

(intro 0 (pt "j"))
(intro 0 (pt "k"))
(intro 0 (pt "z3* ~e0"))

(assert "exl boole BooleToInt boole=e0")
(use "PsdToBooleToIntValue")
(use "Psde0")
(assume "ExHype0")
(by-assume "ExHype0" "boole1" "boole1Prop")

(assert "exl t SdtwoToInt t=i")
(use "SdtwoToSdtwoToIntValue")
(use "Sdtwoi")
(assume "ExHypi")
(by-assume "ExHypi" "t" "tProp")

(split)
(simp "jDef")
;; ?_36:Sdtwo(J(2*e0+i))
;; Replace the vars by cr vars
(simp "<-" "boole1Prop")
(simp "<-" "tProp")
(use "SdtwoMRElim" (pt "IntToSdtwo(J(2*BooleToInt boole1+SdtwoToInt t))"))
(simp (pf "J(2*BooleToInt boole1+SdtwoToInt t)=J(2*e0+i)"))
(use "SdtwoMRIntToSdtwo")
;; ?_42:abs(J(2*e0+i))<=2
(use "JProp")
(simp "boole1Prop")
(simp "tProp")
(use "Truth")

(split)
(simp "kDef")
;; ?_47:Sd(K(2*e0+i))
(simp "<-" "boole1Prop")
(simp "<-" "tProp")
(use "SdMRElim" (pt "IntToSd(K(2*BooleToInt boole1+SdtwoToInt t))"))
(simp (pf "K(2*BooleToInt boole1+SdtwoToInt t)=K(2*e0+i)"))
(use "SdMRIntToSd")
(use "KProp")
;; ?_54:abs(2*e0+i)<=6
(use "IntLeTrans" (pt "IntP 2+IntP 2"))
(use "IntLeTrans" (pt "abs(2*e0)+abs i"))
(use "IntLeAbsPlus")
(use "IntLeMonPlus")
(ng #t)
(simp (pf "abs e0=1"))
(use "Truth")
(use "PsdToAbsOne")
(use "Psde0")
(use "SdtwoBound")
(use "Sdtwoi")
(use "Truth")
(simp "boole1Prop")
(simp "tProp")
(use "Truth")

(split)
(use "CoGPsdTimes")
(use "CoHToCoG")
(use "CoHz3")
(use "PsdUMinus")
(use "Psde0")

;; ?_69:y+(i#4)===(1#4)*(z3* ~e0+j)+k
(simpreal "e0z2Prop")
(simpreal "z3Prop")
;; ?_75:(1#2)*((1#2)*z3+IntN 1)* ~e0+(i#4)===(1#4)*(z3* ~e0+j)+k
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z3"))
(assume "cs" "L" "z3Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?_87:(1#2)*((1#2)*cs n+IntN 1)* ~e0+(i#4)==(1#4)*(cs n* ~e0+j)+k
(use "RatEqvTrans" (pt "(1#2)*(((1#2)*cs n+IntN 1)* ~e0)+(1#4)*i"))
(use "Truth")
(simprat "RatTimesPlusDistrLeft")
(simp "RatTimesIntNL")
(simp (pf "~(RatTimes 1~e0)=(e0#1)"))
;; ?_92:(1#2)*((1#2)*cs n* ~e0+e0)+(1#4)*i==(1#4)*(cs n* ~e0+j)+k
(simp (pf "(1#2)*cs n* ~e0=(1#2)*(cs n* ~e0)"))
(simprat (pf "(1#2)*((1#2)*(cs n* ~e0)+e0)==
              (1#2)*((1#2)*(cs n* ~e0)+(1#2)*(2*e0))"))
(simprat "<-" "RatTimesPlusDistr")
(simp "RatTimesAssoc")
(simp (pf "(1#2)*(1#2)=(1#4)"))
(simprat "<-" "RatTimesPlusDistr")
(simprat (pf "k==(1#4)*(k*4)"))
(simprat "<-" "RatTimesPlusDistr")
(use "RatTimesCompat")
(use "Truth")
;; ?_107:cs n* ~e0+2*e0+i==cs n* ~e0+j+k*4
(simprat (pf "cs n* ~e0+2*e0+i==cs n* ~e0+(2*e0+i)"))
(simprat (pf "cs n* ~e0+j+k*4==cs n* ~e0+RatPlus j(k*4)"))
(use "RatPlusCompat")
(use "Truth")
;; ?_113:2*e0+i==RatPlus j(k*4)
(simp "jDef")
(simp "kDef")
(simp "IntPlusComm")
(simp (pf "J(i+2*e0)+K(i+2*e0)*4=K(i+2*e0)*4+J(i+2*e0)"))
(simp "<-" "KJProp")
(use "Truth")
(use "IntPlusComm")
(simp "RatPlusAssoc")
(use "Truth")
(simp "<-" "RatPlusAssoc")
(use "Truth")
(use "Truth")
(use "Truth")
;; ?_97:(1#2)*((1#2)*(cs n* ~e0)+e0)==(1#2)*((1#2)*(cs n* ~e0)+(1#2)*(2*e0))
(use "RatTimesCompat")
(use "Truth")
;; ?_121:(1#2)*(cs n* ~e0)+e0==(1#2)*(cs n* ~e0)+(1#2)*(2*e0)
(use "RatPlusCompat")
(use "Truth")
(use "IntTimesComm")
;; ?_95:(1#2)*cs n* ~e0=(1#2)*(cs n* ~e0)
(use "Truth")
(use "Truth")
;; Proof finished.
(save "JKUzLrvU")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [t,boole,ah]
;;  IntToSdtwo(J(2*BooleToInt boole+
;;               SdtwoToInt t))pair 
;;  IntToSd(K(2*BooleToInt boole+
;;            SdtwoToInt t))pair 
;;  cCoGPsdTimes(cCoHToCoG ah)(cPsdUMinus boole)

;; JKUzLrv
(set-goal "allnc i,y(Sdtwo i -> CoG y --> allnc e0,z2(
 Psd e0 -> CoG z2 -> y===(1#2)*(z2+IntN 1)* ~e0 ->
 exr j,d,z(Sdtwo j andi Sd d andi CoG z andi y+(i#4)===(1#4)*(z+j)+d)))")
(assume "i" "y" "Sdtwoi" "CoGy"
	"e0" "z2" "Psde0" "CoGz2" "e0z2Prop")
(inst-with-to "CoGClosure" (pt "z2") "CoGz2" "z2Cases")
(elim "z2Cases")
;; 5,6
(drop "z2Cases")

;; Subcase Lrz2
(assume "ExHypz2")
(by-assume "ExHypz2" "e" "eProp")
(by-assume "eProp" "z3" "ez3Prop")

(use-with "JKUzLrvLr"
 (pt "i") (pt "y") "Sdtwoi" "CoGy"
 (pt "e0") (pt "z2") "Psde0" "CoGz2" "e0z2Prop"
 (pt "e") (pt "z3") "?" "?" "?")
(use "ez3Prop")
(use "ez3Prop")
(use "ez3Prop")

;; ?_6:exr x(CoH x andl z2===(1#2)*x) -> 
;;     exr j,d,z(Sdtwo j andd Sd d andd CoG z andl y+(i#4)===(1#4)*(z+j)+d)

(drop "z2Cases")

;; Subcase Uz2
(assume "ExHypz2")
(by-assume "ExHypz2" "z3" "z3Prop")

(use-with "JKUzLrvU"
 (pt "i") (pt "y") "Sdtwoi" "CoGy"
 (pt "e0") (pt "z2") "Psde0" "CoGz2" "e0z2Prop"
 (pt "z3") "?" "?")
(use "z3Prop")
(use "z3Prop")
;; Proof finished.
(save "JKUzLrv")
;; (cdp)

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [t,boole,ag]
;;  [case (cCoGClosure ag)
;;    (InL bg -> cJKUzLrvLr t boole clft bg crht bg)
;;    (InR ah -> cJKUzLrvU t boole ah)]

(animate "CoGClosure")
(animate "JKUzLrvLr")
(animate "JKUzLrvU")

(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [t,boole,ag][case (DesYprod ag)
;;    (InL bg -> 
;;    IntToSdtwo
;;    (J(~(BooleToInt clft bg*BooleToInt boole)+
;;       2*BooleToInt boole+SdtwoToInt t))pair 
;;    IntToSd
;;    (K(~(BooleToInt clft bg*BooleToInt boole)+
;;       2*BooleToInt boole+SdtwoToInt t))pair 
;;    cCoGPsdTimes(cCoGPsdTimes crht bg clft bg)boole)
;;    (InR ah -> 
;;    IntToSdtwo(J(2*BooleToInt boole+SdtwoToInt t))pair 
;;    IntToSd(K(2*BooleToInt boole+SdtwoToInt t))pair 
;;    cCoGPsdTimes(cCoHToCoG ah)(cPsdUMinus boole))]

(deanimate "CoGClosure")
(deanimate "JKUzLrvLr")
(deanimate "JKUzLrvU")

;; JKUzUvFin
(set-goal "allnc i,y(Sdtwo i -> CoG y --> allnc z2(
 CoH z2 --> y===(1#2)*z2 -> allnc e,z3(
 Psd e -> CoG z3 -> z2===(1#2)*(z3+1)*e ->
 exr j,d,z(Sdtwo j andi Sd d andi CoG z andi y+(i#4)===(1#4)*(z+j)+d))))")
(assume "i" "y" "Sdtwoi" "CoGy"
	"z2" "CoHz2" "z2Prop"
        "e" "z3" "Psde" "CoGz3" "ez3Prop")

(assert "exnc j j=J(e+i)")
(intro 0 (pt "J(e+i)"))
(use "Truth")
(assume "ExHypj")
(by-assume "ExHypj" "j" "jDef")

(assert "exnc k k=K(e+i)")
(intro 0 (pt "K(e+i)"))
(use "Truth")
(assume "ExHypk")
(by-assume "ExHypk" "k" "kDef")

(intro 0 (pt "j"))
(intro 0 (pt "k"))
(intro 0 (pt "z3*e"))

(assert "exl boole BooleToInt boole=e")
(use "PsdToBooleToIntValue")
(use "Psde")
(assume "ExHype")
(by-assume "ExHype" "boole" "booleProp")

(assert "exl t SdtwoToInt t=i")
(use "SdtwoToSdtwoToIntValue")
(use "Sdtwoi")
(assume "ExHypi")
(by-assume "ExHypi" "t" "tProp")

(split)
(simp "jDef")
;; Replace the vars by cr vars
(simp "<-" "booleProp")
(simp "<-" "tProp")
(use "SdtwoMRElim" (pt "IntToSdtwo(J(BooleToInt boole+SdtwoToInt t))"))
(simp (pf "J(BooleToInt boole+SdtwoToInt t)=J(e+i)"))
(use "SdtwoMRIntToSdtwo")
;; ?_42:abs(J(e+i))<=2
(use "JProp")
(simp "booleProp")
(simp "tProp")
(use "Truth")

(split)
(simp "kDef")
;; ?_47:Sd(K(e+i))
(simp "<-" "booleProp")
(simp "<-" "tProp")
(use "SdMRElim" (pt "IntToSd(K(BooleToInt boole+SdtwoToInt t))"))
(simp (pf "K(BooleToInt boole+SdtwoToInt t)=K(e+i)"))
(use "SdMRIntToSd")
(use "KProp")
;; ?_54:abs(e+i)<=6
(use "IntLeTrans" (pt "IntP 1+IntP 2"))
(use "IntLeTrans" (pt "abs e+abs i"))
(use "IntLeAbsPlus")
(use "IntLeMonPlus")
(simp (pf "abs e=1"))
(use "Truth")
(use "PsdToAbsOne")
(use "Psde")
(use "SdtwoBound")
(use "Sdtwoi")
(use "Truth")
(simp "booleProp")
(simp "tProp")
(use "Truth")

(split)
(use "CoGPsdTimes")
(use "CoGz3")
(use "Psde")

;; ?_68:y+(i#4)===(1#4)*(z3*e+j)+k
(simpreal "z2Prop")
(simpreal "ez3Prop")
;; ?_72:(1#2)*((1#2)*(z3+1)*e)+(i#4)===(1#4)*(z3*e+j)+k
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z3"))
(assume "cs" "L" "z3Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?_84:(1#4)*(cs n+1)*e+(i#4)==(1#4)*(cs n*e+j)+k
(use "RatEqvTrans" (pt "(1#4)*(cs n+1)*e+(1#4)*i"))
(use "Truth")
;; ?_106:(1#4)*(cs n+1)*e+(1#4)*i==(1#4)*(cs n*e+j)+k
(simp (pf "(1#4)*(cs n+1)*e=(1#4)*((cs n+1)*e)"))
(simprat "RatTimesPlusDistrLeft")
(simprat (pf "k==(1#4)*(k*4)"))
(simprat "<-" "RatTimesPlusDistr")
(simprat "<-" "RatTimesPlusDistr")
(use "RatTimesCompat")
(use "Truth")
;; ?_95:cs n*e+RatTimes 1 e+i==cs n*e+j+k*4
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
;; ?_99:RatTimes 1 e+i==RatPlus j(k*4)
(simp "jDef")
(simp "kDef")
(simp (pf "RatPlus(J(e+i))(K(e+i)*4)=K(e+i)*4+J(e+i)"))
(simp "<-" "KJProp")
;; ?_104:RatTimes 1 e+i==e+i
(use "Truth")
(use "IntPlusComm")
(use "Truth")
(use "Truth")
;; Proof finished.
(save "JKUzUvFin")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [t,boole,ag]
;;  IntToSdtwo(J(BooleToInt boole+
;;               SdtwoToInt t))pair 
;;  IntToSd(K(BooleToInt boole+
;;            SdtwoToInt t))pair
;;  cCoGPsdTimes ag boole

;; JKUzUvD
(set-goal "allnc i,y(Sdtwo i -> CoG y --> allnc z2(
 CoH z2 --> y===(1#2)*z2 -> allnc z3(
 CoH z3 -> z2===(1#2)*z3 ->
 exr j,d,z(Sdtwo j andi Sd d andi CoG z andi y+(i#4)===(1#4)*(z+j)+d))))")
(assume "i" "y" "Sdtwoi" "CoGy"
	"z2" "CoHz2" "z2Prop"
        "z3" "CoHz3" "z3Prop")

(assert "exnc j j=J(i)")
(intro 0 (pt "J(i)"))
(use "Truth")
(assume "ExHypj")
(by-assume "ExHypj" "j" "jDef")

(assert "exnc k k=K(i)")
(intro 0 (pt "K(i)"))
(use "Truth")
(assume "ExHypk")
(by-assume "ExHypk" "k" "kDef")

(intro 0 (pt "j"))
(intro 0 (pt "k"))
(intro 0 (pt "z3"))

(assert "exl t SdtwoToInt t=i")
(use "SdtwoToSdtwoToIntValue")
(use "Sdtwoi")
(assume "ExHypi")
(by-assume "ExHypi" "t" "tProp")

(split)
(simp "jDef")
;; ?_29:Sdtwo(J i)
;; Replace vars by cr vars
(simp "<-" "tProp")
(use "SdtwoMRElim" (pt "IntToSdtwo(J(SdtwoToInt t))"))
(simp (pf "J(SdtwoToInt t)=J i"))
(use "SdtwoMRIntToSdtwo")
;; ?_34:abs(J i)<=2
(use "JProp")
(simp "tProp")
(use "Truth")

(split)
(simp "kDef")
;; ?_38:Sd(K i)
(simp "<-" "tProp")
(use "SdMRElim" (pt "IntToSd(K(SdtwoToInt t))"))
(simp (pf "K(SdtwoToInt t)=K i"))
(use "SdMRIntToSd")
(use "KProp")
;; ?_44:abs i<=6
(use "IntLeTrans" (pt "IntP 2"))
(use "SdtwoBound")
(use "Sdtwoi")
(use "Truth")
(simp "tProp")
(use "Truth")

(split)
(use "CoHToCoG")
(use "CoHz3")

;; ?_50:y+(i#4)===(1#4)*(z3+j)+k
(simpreal "z2Prop")
(simpreal "z3Prop")
;; ?_53:(1#2)*((1#2)*z3)+(i#4)===(1#4)*(z3+j)+k
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "z3"))
(assume "cs" "L" "z3Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?_61:(1#4)*cs n+(i#4)==(1#4)*(cs n+j)+k
(use "RatEqvTrans" (pt "(1#4)*cs n+(1#4)*i"))
(use "Truth")
(simprat "<-" "RatTimesPlusDistr")
(simprat (pf "k==(1#4)*(k*4)"))
(simprat "<-" "RatTimesPlusDistr")
(use "RatTimesCompat")
(use "Truth")
;; ?_69:cs n+i==cs n+j+k*4
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
(ng #t)
;; ?_73:i=j+k*4
(simp "jDef")
(simp "kDef")
(simp (pf "J i+K i*4=K i*4+J i"))
(use "KJProp")
(use "IntPlusComm")
(use "Truth")
;; Proof finished.
(save "JKUzUvD")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [t,ah]
;;  IntToSdtwo(J(SdtwoToInt t))pair 
;;  IntToSd(K(SdtwoToInt t))pair
;;  cCoHToCoG ah

;; JKUzUv
(set-goal "allnc i,y(Sdtwo i -> CoG y --> allnc z2(
 CoH z2 -> y===(1#2)*z2 ->
 exr j,d,z(Sdtwo j andi Sd d andi CoG z andi y+(i#4)===(1#4)*(z+j)+d)))")
(assume "i" "y" "Sdtwoi" "CoGy"
	"z2" "CoHz2" "z2Prop")
(inst-with-to "CoHClosure" (pt "z2") "CoHz2" "z2Cases")
(elim "z2Cases")
;; 5,6
(drop "z2Cases")

;; Subcase Lrz2
(assume "ExHypz2")
(by-assume "ExHypz2" "e" "eProp")
(by-assume "eProp" "z3" "ez3Prop")

(use-with "JKUzUvFin"
 (pt "i") (pt "y") "Sdtwoi" "CoGy"
 (pt "z2") "CoHz2" "z2Prop"
 (pt "e") (pt "z3") "?" "?" "?")
(use "ez3Prop")
(use "ez3Prop")
(use "ez3Prop")

;; ?_6:exr x(CoH x andl z2===(1#2)*x) -> 
;;     exr j,d,z(Sdtwo j andd Sd d andd CoG z andl y+(i#4)===(1#4)*(z+j)+d)

(drop "z2Cases")

;; Subcase Uz2
(assume "ExHypz2")
(by-assume "ExHypz2" "z3" "z3Prop")

(use-with "JKUzUvD"
 (pt "i") (pt "y") "Sdtwoi" "CoGy"
 (pt "z2") "CoHz2" "z2Prop"
 (pt "z3") "?" "?")
(use "z3Prop")
(use "z3Prop")
;; Proof finished.
(save "JKUzUv")
;; (cdp)

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [t,ah]
;;  [case (cCoHClosure ah)
;;    (InL bg -> cJKUzUvFin t clft bg crht bg)
;;    (InR ah -> cJKUzUvD t ah)]

(animate "CoHClosure")
(animate "JKUzUvFin")
(animate "JKUzUvD")

(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [t,ah][case (DesYprod ah)
;;    (InL bg -> IntToSdtwo(J(BooleToInt clft bg+
;;                            SdtwoToInt t))pair 
;;    IntToSd(K(BooleToInt clft bg+
;;              SdtwoToInt t))pair 
;;    cCoGPsdTimes crht bg clft bg)
;;    (InR ah0 -> IntToSdtwo(J(SdtwoToInt t))pair 
;;                IntToSd(K(SdtwoToInt t))pair
;;                cCoHToCoG ah0)]

(deanimate "CoHClosure")
(deanimate "JKUzUvFin")
(deanimate "JKUzUvD")

;; JKUz
(set-goal "allnc i,y(Sdtwo i -> CoG y ->
 exr j,d,z(Sdtwo j andi Sd d andi CoG z andi y+(i#4)===(1#4)*(z+j)+d))")
(assume "i" "y" "Sdtwoi" "CoGy")
(inst-with-to "CoGClosure" (pt "y") "CoGy" "vCases")
(elim "vCases")
;; 5,6
(drop "vCases")

;; Case Lrv
(assume "ExHyp")
(by-assume "ExHyp" "e0" "e0Prop")
(by-assume "e0Prop" "z2" "e0z2Prop")

(use-with "JKUzLrv"
 (pt "i") (pt "y") "Sdtwoi" "CoGy"
 (pt "e0") (pt "z2") "?" "?" "?")
(use "e0z2Prop")
(use "e0z2Prop")
(use "e0z2Prop")

;; ?_6:exr x(CoH x andl y===(1#2)*x) -> 
;;     exr j,d,z(Sdtwo j andd Sd d andd CoG z andl y+(i#4)===(1#4)*(z+j)+d)

(drop "vCases")

;; Case Uv
(assume "ExHyp")
(by-assume "ExHyp" "z2" "z2Prop")

;; (pp "JKUzUv")
(use "JKUzUv" (pt "z2"))
(use "Sdtwoi")
(use "CoGy")
(use "z2Prop")
(use "z2Prop")
;; Proof finished.
(save "JKUz")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [t,ag][case (cCoGClosure ag)
;;    (InL bg -> cJKUzLrv t clft bg crht bg)
;;    (InR ah -> cJKUzUv t ah)]

(animate "CoGClosure")
(animate "CoHClosure")
(animate "JKUzLrvLr")
(animate "JKUzLrvU")
(animate "JKUzLrv")
(animate "JKUzUvFin")
(animate "JKUzUvD")
(animate "JKUzUv")

(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [t,ag][case (DesYprod ag)
;;  (InL bg -> [case (DesYprod crht bg)
;;   (InL bg0 -> IntToSdtwo(J(~(BooleToInt clft bg0*
;;                              BooleToInt clft bg)+
;;                            2*BooleToInt clft bg+
;;                            SdtwoToInt t))pair 
;;               IntToSd(K(~(BooleToInt clft bg0*
;;                           BooleToInt clft bg)+
;;                         2*BooleToInt clft bg+
;;                         SdtwoToInt t))pair 
;;               cCoGPsdTimes
;;                (cCoGPsdTimes crht bg0 clft bg0)clft bg)
;;   (InR ah -> IntToSdtwo(J(2*BooleToInt clft bg+
;;                           SdtwoToInt t))pair 
;;              IntToSd(K(2*BooleToInt clft bg+
;;                        SdtwoToInt t))pair 
;;              cCoGPsdTimes(cCoHToCoG ah)
;;                          (cPsdUMinus clft bg))])
;;  (InR ah -> [case (DesYprod ah)
;;   (InL bg -> IntToSdtwo(J(BooleToInt clft bg+
;;                           SdtwoToInt t))pair 
;;              IntToSd(K(BooleToInt clft bg+
;;                        SdtwoToInt t))pair 
;;              cCoGPsdTimes crht bg clft bg)
;;   (InR ah0 -> IntToSdtwo(J(SdtwoToInt t))pair 
;;               IntToSd(K(SdtwoToInt t))pair
;;               cCoHToCoG ah0)])]

(deanimate "CoGClosure")
(deanimate "CoHClosure")
(deanimate "JKUzLrvLr")
(deanimate "JKUzLrvU")
(deanimate "JKUzLrv")
(deanimate "JKUzUvFin")
(deanimate "JKUzUvD")
(deanimate "JKUzUv")

;; We show CoGMultcSatCoICl, using JKLrz and JKUz.  This is split into
;; CoGMultcSatCoIClLrxLrz using JKLrz
;; CoGMultcSatCoIClLrxUz  using JKUz
;; CoGMultcSatCoIClUxLrz  using JKLrz
;; CoGMultcSatCoIClUxUz   using JKUz

;; CoGMultcSatCoIClLrxLrz
(set-goal "allnc y,i,x,z(CoG y -> Sdtwo i -> CoG x --> CoG z --> allnc d1,x1(
 Psd d1 -> CoG x1 -> x===(1#2)*(x1+IntN 1)* ~d1 -> allnc d0,z1(
 Psd d0 -> CoG z1 -> z===(1#2)*(z1+IntN 1)* ~d0 ->
 exr d,j,x0,z0(Sd d andi Sdtwo j andi CoG x0 andi CoG z0 andi 
 (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x0*y+z0+j)+d)))))")
(assume "y" "i" "x" "z" "CoGy" "Sdtwoi" "CoGx" "CoGz"
	"d1" "x1" "Psdd1" "CoGx1" "d1x1Prop"
	"d0" "z1" "Psdd0" "CoGz1" "d0z1Prop")

;; Substitute x===(1#2)*(x1+IntN 1)* ~d1 and z===(1#2)*(z1+IntN 1)* ~d0
(assert "(1#4)*(x*y+z+i)===
(1#4)*(((1#2)*(x1+IntN 1)* ~d1)*y+((1#2)*(z1+IntN 1)* ~d0)+i)")
(simpreal "d1x1Prop")
(simpreal "d0z1Prop")
(use "RealEqRefl")
(realproof)
(assume "Eq1")
;; Prepare for application of CoGAvcToCoG and JKLrz
(assert "(1#4)*(((1#2)*(x1+IntN 1)* ~d1)*y+((1#2)*(z1+IntN 1)* ~d0)+i)===
         (1#2)*((1#4)*(x1* ~d1*y)+((1#4)*(y*d1+z1* ~d0+i)+(d0+i#4)))")
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z1"))
(assume "cs" "L" "z1Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?_22:(1#4)*(~((1#2)*(as n+IntN 1)*d1*bs n)+ ~((1#2)*(cs n+IntN 1)*d0)+i)==
;;      (1#2)*(~((1#4)*as n*d1*bs n)+(1#4)*(bs n*d1+ ~(cs n*d0)+i)+(d0+i#4))
;; Replace first i by (1#2)*RatPlus i i, and prepare for taking (1#2) out
(use "RatEqvTrans" 
 (pt "(1#4)*(~((1#2)*(as n+IntN 1)*d1*bs n)+ ~(1#2)*((cs n+IntN 1)*d0)+
      (1#2)*RatPlus i i)"))
(ng #t)
(simp (pf "IntP 2=IntPlus 1 1"))
(simp "IntTimes6RewRule") ;k*(j+i)=k*j+k*i
(use "Truth")
(use "Truth")
;; Similarly replace (d0+i#4) by (1#4)*RatPlus d0 i.
(use "RatEqvTrans" 


  (pt "(1#2)*(~((1#4)*as n*d1*bs n)+(1#4)*(bs n*d1+ ~(cs n*d0)+i)+
       (1#4)*RatPlus d0 i)"))
;; ?_29:(1#4)*
;;      (~((1#2)*(as n+IntN 1)*d1*bs n)+ ~(1#2)*((cs n+IntN 1)*d0)+
;;       (1#2)*RatPlus i i)==
;;      (1#2)*
;;      (~((1#4)*as n*d1*bs n)+(1#4)*(bs n*d1+ ~(cs n*d0)+i)+(1#4)*RatPlus d0 i)
(simp "<-" "RatTimes3RewRule")
(simp "<-" "RatTimes3RewRule")
(simp "<-" "RatTimes3RewRule")
(simp (pf "~(1#2)*((cs n+IntN 1)*d0)= (1#2)* ~((cs n+IntN 1)*d0)"))
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimesAssoc")
(simprat "<-" "RatTimesPlusDistr")
(simprat "<-" "RatTimesPlusDistr")
(simprat "<-" "RatTimesPlusDistr")
(simprat "<-" "RatTimesPlusDistr")
(simp "RatTimesAssoc")
(simp "RatTimesAssoc")
(simp "RatTimesAssoc")
(simp (pf "(1#4)*(1#2)=(1#2)*(1#4)"))
(use "RatTimesCompat")
(use "Truth")
;; ?_50:(as n+IntN 1)*d1* ~(bs n)+ ~((cs n+IntN 1)*d0)+RatPlus i i==
;;      as n*(d1* ~(bs n))+(bs n*d1+cs n* ~d0+i)+RatPlus d0 i
(simprat "RatTimesPlusDistrLeft")
(simprat "RatTimesPlusDistrLeft")
(simprat "RatTimesPlusDistrLeft")
;; ?_53:as n*d1* ~(bs n)+RatTimes IntN 1 d1* ~(bs n)+ 
;;      ~(cs n*d0+RatTimes IntN 1 d0)+
;;      RatPlus i i==
;;      as n*(d1* ~(bs n))+(bs n*d1+cs n* ~d0+i)+RatPlus d0 i
(assert "all k RatTimes IntN 1 k= ~k")
 (assume "k")
 (ng #t)
 (simp "IntTimesIntNL")
 (use "Truth")
(assume "Assertion")
(simp "Assertion")
(simp "Assertion")
;; ?_61:as n*d1* ~(bs n)+ ~d1* ~(bs n)+ ~(cs n*d0+ ~d0)+RatPlus i i==
;;      as n*(d1* ~(bs n))+(bs n*d1+cs n* ~d0+i)+RatPlus d0 i
;; ?_52:as n* ~d1*bs n+d1*bs n+(cs n* ~d0+d0)+RatPlus i i==
;;      as n* ~d1*bs n+(bs n*d1+cs n* ~d0+i)+RatPlus d0 i
(simp "<-" (pf "d1*bs n=bs n*d1"))
(use "RatEqvTrans" (pt "as n* ~d1*bs n+bs n*d1+(cs n* ~d0+i+RatPlus d0 i)"))
(use "RatEqvTrans" (pt "as n* ~d1*bs n+bs n*d1+(cs n* ~d0+d0+RatPlus i i)"))
(ng #t)
(simp "RatTimesComm")
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
;; ?_65:as n* ~d1*bs n+bs n*d1+(cs n* ~d0+i+RatPlus d0 i)==
;;      as n*(d1* ~(bs n))+(d1*bs n+cs n* ~d0+i)+RatPlus d0 i
(ng #t)
(simp "RatTimesComm")
(use "Truth")
(use "RatTimesComm")
(use "Truth")
;; ?_35:~(1#2)*((cs n+IntN 1)*d0)=(1#2)* ~((cs n+IntN 1)*d0)
(use "Truth")
;; ?_30:(1#2)*
;;      (~((1#4)*as n*d1*bs n)+(1#4)*(bs n*d1+ ~(cs n*d0)+i)+(1#4)*RatPlus d0 i)==
;;      (1#2)*(~((1#4)*as n*d1*bs n)+(1#4)*(bs n*d1+ ~(cs n*d0)+i)+(d0+i#4))
(use "Truth")
;; ?_9:(1#4)*((1#2)*(x1+IntN 1)* ~d1*y+(1#2)*(z1+IntN 1)* ~d0+i)===
;;     (1#2)*((1#4)*(x1* ~d1*y)+((1#4)*(y*d1+z1* ~d0+i)+(d0+i#4))) -> 
;;     exr d,j,x0,z0(
;;      Sd d andd 
;;      Sdtwo j andd 
;;      CoG x0 andd CoG z0 andl (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x0*y+z0+j)+d))
(assume "Eq2")
;;   Eq1:(1#4)*(x*y+z+i)===
;;       (1#4)*((1#2)*(x1+IntN 1)* ~d1*y+(1#2)*(z1+IntN 1)* ~d0+i)
;;   Eq2:(1#4)*((1#2)*(x1+IntN 1)* ~d1*y+(1#2)*(z1+IntN 1)* ~d0+i)===
;;       (1#2)*((1#4)*(x1* ~d1*y)+((1#4)*(y*d1+z1* ~d0+i)+(d0+i#4)))
;; -----------------------------------------------------------------------------
;; ?_82:exr d,j,x0,z0(
;;       Sd d andd 
;;       Sdtwo j andd 
;;       CoG x0 andd CoG z0 andl (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x0*y+z0+j)+d))

;; Now we aim for using JKLrz
(cut "exr j,d,z(Sdtwo j andi Sd d andi CoG z andi
                (1#4)*(y*d1+z1* ~d0+i)+(d0+i#4)===(1#4)*(z+j)+d)")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "ExHyp")
(by-assume "ExHyp" "j" "jProp")
(by-assume "jProp" "d" "jdProp")
(by-assume "jdProp" "z0" "jdz0Prop")

(intro 0 (pt "d"))
(intro 0 (pt "j"))
(intro 0 (pt "x1* ~d1"))
(intro 0 (pt "z0"))

(split)
(use "jdz0Prop")
(split)
(use "jdz0Prop")
(split)
(use "CoGPsdTimes")
(use "CoGx1")
(use "PsdUMinus")
(use "Psdd1")
(split)
(use "jdz0Prop")

;; ?_110:(1#4)*(x*y+z+i)===(1#2)*((1#4)*(x1* ~d1*y+z0+j)+d)
(use "RealEqTrans" 
     (pt "(1#4)*((1#2)*(x1+IntN 1)* ~d1*y+(1#2)*(z1+IntN 1)* ~d0+i)"))
(use "Eq1")
(use "RealEqTrans" 
     (pt "(1#2)*((1#4)*(x1* ~d1*y)+((1#4)*(y*d1+z1* ~d0+i)+(d0+i#4)))"))
(use "Eq2")
(drop "Eq1" "Eq2")
(assert "CoG z0")
(use "jdz0Prop")
(assume "CoGz0")

(assert "Real((1#2)*((1#4)*(x1* ~d1*y+z0+j)+d))")
(realproof)
(assume "R")
(simpreal "jdz0Prop")
;; ?_122:(1#2)*((1#4)*(x1* ~d1*y)+((1#4)*(z0+j)+d))===
;;       (1#2)*((1#4)*(x1* ~d1*y+z0+j)+d)
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z0"))
(assume "cs" "L" "z0Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?_134:~((1#4)*as n*d1*bs n)+(1#4)*(cs n+j)==(1#4)*(~(as n*d1*bs n)+cs n+j)
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimes3RewRule")
(simprat "<-" "RatTimesPlusDistr")
(use "RatTimesCompat")
(use "Truth")
(use "Truth")

;; Now we prove the formula cut in above
(use "JKLrz")
(use "Sdtwoi")
(use "Psdd0")
(use "CoGAvcToCoG")

(intro 0 (pt "i"))
(intro 0 (pt "y*d1"))
(intro 0 (pt "z1* ~d0"))
(split)
(use "Sdtwoi")
(split)
(use "CoGPsdTimes")
(use "CoGy")
(use "Psdd1")
(split)
(use "CoGPsdTimes")
(use "CoGz1")
(use "PsdUMinus")
(use "Psdd0")
(use "RealEqRefl")
(realproof)
;; Proof finished.
(save "CoGMultcSatCoIClLrxLrz")

;; cCoGMultcSatCoIClLrxLrz:
;; ag=>sdtwo=>boole=>ag=>boole=>ag=>sd yprod sdtwo yprod ag yprod ag

(define eterm (proof-to-extracted-term))
(add-var-name "tsg" (py "sdtwo yprod sd yprod ag"))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [ag,t,boole,ag0,boole0,ag1]
;;  [let tsg
;;    (cJKLrz t boole0
;;    (cCoGAvcToCoG
;;     (t pair cCoGPsdTimes ag boole pair cCoGPsdTimes ag1(cPsdUMinus boole0))))
;;    (clft crht tsg pair 
;;    clft tsg pair cCoGPsdTimes ag0(cPsdUMinus boole)pair crht crht tsg)]

;; CoGMultcSatCoIClLrxUz
(set-goal "allnc y,i,x,z(CoG y -> Sdtwo i -> CoG x --> CoG z --> allnc d1,x1(
 Psd d1 -> CoG x1 -> x===(1#2)*(x1+IntN 1)* ~d1 -> allnc z1(
 CoH z1 -> z===(1#2)*z1 ->
 exr d,j,x0,z0(Sd d andi Sdtwo j andi CoG x0 andi CoG z0 andi 
 (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x0*y+z0+j)+d)))))")
(assume "y" "i" "x" "z" "CoGy" "Sdtwoi" "CoGx" "CoGz"
	"d1" "x1" "Psdd1" "CoGx1" "d1x1Prop"
	"z1" "CoHz1" "z1Prop")
;; Substitute x===(1#2)*(x1+IntN 1)* ~d1 and z===(1#2)*(z1+IntN 1)* ~d0
(assert "(1#4)*(x*y+z+i)===(1#4)*(((1#2)*(x1+IntN 1)* ~d1)*y+((1#2)*z1)+i)")
(simpreal "d1x1Prop")
(simpreal "z1Prop")
(use "RealEqRefl")
(realproof)
(assume "Eq1")
;; Prepare for application of CoGAvcToCoG and JKLrz
(assert "(1#4)*(((1#2)*(x1+IntN 1)* ~d1)*y+((1#2)*z1)+i)===
(1#2)*((1#4)*(x1* ~d1*y)+((1#4)*(y*d1+z1+i)+(i#4)))")
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z1"))
(assume "cs" "L" "z1Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?_22:(1#4)*(~((1#2)*(as n+IntN 1)*d1*bs n)+(1#2)*cs n+i)==
;;      (1#2)*(~((1#4)*as n*d1*bs n)+(1#4)*(bs n*d1+cs n+i)+(i#4))
;; Replace first i by (1#2)*RatPlus i i, and prepare for taking (1#2) out

(use "RatEqvTrans" 
 (pt "(1#4)*(~(1#2)*((as n+IntN 1)*d1*bs n)+(1#2)*cs n+(1#2)*RatPlus i i)"))
(ng #t)
(simp (pf "2=IntPlus 1 1"))
(simp "IntTimes6RewRule") ;k*(j+i)=k*j+k*i
(use "Truth")
(use "Truth")
;; Similarly replace (i#4) by (1#4)*i.
(use "RatEqvTrans" 
  (pt "(1#2)*(~(1#4)*(as n*d1*bs n)+(1#4)*(bs n*d1+cs n+i)+(1#4)*i)"))
;; ?_29:(1#4)*(~(1#2)*((as n+IntN 1)*d1*bs n)+(1#2)*cs n+(1#2)*RatPlus i i)==
;;      (1#2)*(~(1#4)*(as n*d1*bs n)+(1#4)*(bs n*d1+cs n+i)+(1#4)*i)
;; Cancel rational factors
(simp (pf "~(1#2)*((as n+IntN 1)*d1*bs n)=(1#2)* ~((as n+IntN 1)*d1*bs n)"))
(simp (pf "~(1#4)*(as n*d1*bs n)=(1#4)* ~(as n*d1*bs n)"))
(simprat "<-" "RatTimesPlusDistr")
(simprat "<-" "RatTimesPlusDistr")
(simprat "<-" "RatTimesPlusDistr")
(simprat "<-" "RatTimesPlusDistr")
(simp "RatTimesAssoc")
(simp "RatTimesAssoc")
(simp (pf "(1#4)*(1#2)=(1#2)*(1#4)"))
(use "RatTimesCompat")
(use "Truth")
;; ?_44:~((as n+IntN 1)*d1*bs n)+cs n+RatPlus i i== 
;;      ~(as n*d1*bs n)+(bs n*d1+cs n+i)+i
(simprat "RatTimesPlusDistrLeft")
(simprat "RatTimesPlusDistrLeft")
;; ?_46:~(as n*d1*bs n+RatTimes IntN 1 d1*bs n)+cs n+RatPlus i i== 
;;      ~(as n*d1*bs n)+(bs n*d1+cs n+i)+i
(assert "all k (IntN 1#1)*k= ~k")
 (assume "k")
 (ng #t)
 (simp "IntTimesIntNL")
 (use "Truth")
(assume "Assertion")
(simp "Assertion")
;; ?_53:~(as n*d1*bs n+ ~d1*bs n)+cs n+RatPlus i i== 
;;      ~(as n*d1*bs n)+(bs n*d1+cs n+i)+i
(simp "RatUMinus2RewRule")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(ng #t)
(simp "RatTimesComm")
(use "Truth")
(use "Truth")
;; ?_34:~(1#2)*((as n+IntN 1)*d1*bs n)=(1#2)* ~((as n+IntN 1)*d1*bs n)
(use "Truth")
;; ?_32:(1#2)*(~(1#4)*(as n*d1*bs n)+(1#4)*(bs n*d1+cs n+i)+(1#4)*i)==
;;      (1#2)*(~((1#4)*as n*d1*bs n)+(1#4)*(bs n*d1+cs n+i)+(i#4))
(use "Truth")
;; ?_30:(1#2)*(~(1#4)*(as n*d1*bs n)+(1#4)*(bs n*d1+cs n+i)+(1#4)*i)==
;;      (1#2)*(~((1#4)*as n*d1*bs n)+(1#4)*(bs n*d1+cs n+i)+(i#4))
(use "Truth")
(assume "Eq2")

;;   Eq1:(1#4)*(x*y+z+i)===(1#4)*((1#2)*(x1+IntN 1)* ~d1*y+(1#2)*z1+i)
;;   Eq2:(1#4)*((1#2)*(x1+IntN 1)* ~d1*y+(1#2)*z1+i)===
;;       (1#2)*((1#4)*(x1* ~d1*y)+((1#4)*(y*d1+z1+i)+(i#4)))
;; -----------------------------------------------------------------------------
;; ?_64:exr d,j,x0,z0(
;;       Sd d andd 
;;       Sdtwo j andd 
;;       CoG x0 andd CoG z0 andl (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x0*y+z0+j)+d))
;; Now we aim for using JKUz
(cut "exr j,d,z(Sdtwo j andd Sd d andd CoG z andl
                (1#4)*(y*d1+z1+i)+(i#4)===(1#4)*(z+j)+d)")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "ExHyp")
(by-assume "ExHyp" "j" "jProp")
(by-assume "jProp" "d" "jdProp")
(by-assume "jdProp" "z0" "jdz0Prop")

(intro 0 (pt "d"))
(intro 0 (pt "j"))
(intro 0 (pt "x1* ~d1"))
(intro 0 (pt "z0"))

(split)
(use "jdz0Prop")
(split)
(use "jdz0Prop")
(split)
(use "CoGPsdTimes")
(use "CoGx1")
(use "PsdUMinus")
(use "Psdd1")
(split)
(use "jdz0Prop")

;; ?_92:(1#4)*(x*y+z+i)===(1#2)*((1#4)*(x1* ~d1*y+z0+j)+d)
(use "RealEqTrans" (pt "(1#4)*((1#2)*(x1+IntN 1)* ~d1*y+(1#2)*z1+i)"))
(use "Eq1")
(use "RealEqTrans" (pt "(1#2)*((1#4)*(x1* ~d1*y)+((1#4)*(y*d1+z1+i)+(i#4)))"))
(use "Eq2")
(drop "Eq1" "Eq2")
(assert "CoG z0")
(use "jdz0Prop")
(assume "CoGz0")
(simpreal "jdz0Prop")

;; ?_101:(1#2)*((1#4)*(x1* ~d1*y)+((1#4)*(z0+j)+d))===
;;       (1#2)*((1#4)*(x1* ~d1*y+z0+j)+d)
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z0"))
(assume "cs" "L" "z0Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?_113:~((1#4)*as n*d1*bs n)+(1#4)*(cs n+j)==(1#4)*(~(as n*d1*bs n)+cs n+j)
(simp (pf "(1#4)*as n*d1*bs n=(1#4)*(as n*d1*bs n)"))
(simp (pf "~((1#4)*(as n*d1*bs n))=(1#4)* ~(as n*d1*bs n)"))
(simprat "<-" "RatTimesPlusDistr")
(use "RatTimesCompat")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
;; Now we prove the formula cut in above
(use "JKUz")
(use "Sdtwoi")
(use "CoGAvcToCoG")
(intro 0 (pt "i"))
(intro 0 (pt "y*d1"))
(intro 0 (pt "z1"))
(split)
(use "Sdtwoi")
(split)
(use "CoGPsdTimes")
(use "CoGy")
(use "Psdd1")
(split)
(use "CoHToCoG")
(use "CoHz1")
(use "RealEqRefl")
(realproof)
;; Proof finished.
(save "CoGMultcSatCoIClLrxUz")

;; cCoGMultcSatCoIClLrxUz:
;; ag=>sdtwo=>boole=>ag=>ah=>sd yprod sdtwo yprod ag yprod ag

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [ag,t,boole,ag0,ah]
;;  [let tsg
;;    (cJKUz t(cCoGAvcToCoG(t pair cCoGPsdTimes ag boole pair cCoHToCoG ah)))
;;    (clft crht tsg pair 
;;    clft tsg pair cCoGPsdTimes ag0(cPsdUMinus boole)pair crht crht tsg)]

;; CoGMultcSatCoIClUxLrz
(set-goal "allnc y,i,x,z(CoG y -> Sdtwo i -> CoG x --> CoG z --> allnc x1(
 CoH x1 -> x===(1#2)*x1 -> allnc d0,z1(
 Psd d0 -> CoG z1 -> z===(1#2)*(z1+IntN 1)* ~d0 ->
 exr d,j,x0,z0(Sd d andi Sdtwo j andi CoG x0 andi CoG z0 andi 
 (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x0*y+z0+j)+d)))))")
(assume "y" "i" "x" "z" "CoGy" "Sdtwoi" "CoGx" "CoGz"
	"x1" "CoHx1" "x1Prop"
	"d0" "z1" "Psdd0" "CoGz1" "d0z1Prop")

;; Substitute x===(1#2)*x1 and z===(1#2)*(z1+IntN 1)* ~d0
(assert "(1#4)*(x*y+z+i)===
(1#4)*((1#2)*x1*y+((1#2)*(z1+IntN 1)* ~d0)+i)")
(simpreal "x1Prop")
(simpreal "d0z1Prop")
(use "RealEqRefl")
(realproof)
(assume "Eq1")
;; Prepare for application of CoGAvcToCoG and JKLrz
(assert "(1#4)*((1#2)*x1*y+(1#2)*(z1+IntN 1)* ~d0+i)===
         (1#2)*((1#4)*(x1*y)+((1#4)*(0+z1* ~d0+i)+(d0+i#4)))")
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z1"))
(assume "cs" "L" "z1Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?_22:(1#4)*((1#2)*as n*bs n+(1#2)*(cs n+IntN 1)* ~d0+i)==
;;      (1#2)*((1#4)*as n*bs n+(1#4)*(cs n* ~d0+i)+(d0+i#4))
;; Replace first i by (1#2)*RatPlus i i, and prepare for taking (1#2) out

(use "RatEqvTrans" 
 (pt "(1#4)*((1#2)*(as n*bs n)+(1#2)*((cs n+IntN 1)* ~d0)+(1#2)*RatPlus i i)"))
(ng #t)
(simp (pf "2=IntPlus 1 1"))
(simp "IntTimes6RewRule") ;k*(j+i)=k*j+k*i
(use "Truth")
(use "Truth")
;; Similarly replace (d0+i#4) by (1#4)*RatPlus d0 i.
(use "RatEqvTrans" 
  (pt "(1#2)*((1#4)*(as n*bs n)+(1#4)*(cs n* ~d0+i)+(1#4)*RatPlus d0 i)"))
;; Cancel rational factors
(simprat "<-" "RatTimesPlusDistr")
(simprat "<-" "RatTimesPlusDistr")
(simprat "<-" "RatTimesPlusDistr")
(simprat "<-" "RatTimesPlusDistr")
(simp "RatTimesAssoc")
(simp "RatTimesAssoc")
(simp (pf "(1#4)*(1#2)=(1#2)*(1#4)"))
(use "RatTimesCompat")
(use "Truth")
;; ?_40:as n*bs n+(cs n+IntN 1)* ~d0+RatPlus i i==
;;      as n*bs n+(cs n* ~d0+i)+RatPlus d0 i
(simprat "RatTimesPlusDistrLeft")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
(use "RatPlusCompat")
(use "Truth")
(ng #t)
(simp "IntTimesIntNL")
(ng #t)
(simp (pf "d0+i=i+d0"))
(use "Truth")
(use "IntPlusComm")
(use "RatTimesComm")
(use "Truth")
(assume "Eq2")
;;   Eq1:(1#4)*(x*y+z+i)===(1#4)*((1#2)*x1*y+(1#2)*(z1+IntN 1)* ~d0+i)
;;   Eq2:(1#4)*((1#2)*x1*y+(1#2)*(z1+IntN 1)* ~d0+i)===
;;       (1#2)*((1#4)*(x1*y)+((1#4)*(0+z1* ~d0+i)+(d0+i#4)))
;; -----------------------------------------------------------------------------
;; ?_55:exr d,j,x0,y0,z0(
;;       Sd d andd 
;;       Sdtwo j andd 
;;       CoG x0 andd CoG z0 andl (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x0*y0+z0+j)+d))
;; Now we aim for using JKLrz
(cut "exr j,d,z(Sdtwo j andi Sd d andi CoG z andi
                (1#4)*(0+z1* ~d0+i)+(d0+i#4)===(1#4)*(z+j)+d)")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "ExHyp")
(by-assume "ExHyp" "j" "jProp")
(by-assume "jProp" "d" "jdProp")
(by-assume "jdProp" "z0" "jdz0Prop")

(intro 0 (pt "d"))
(intro 0 (pt "j"))
(intro 0 (pt "x1"))
(intro 0 (pt "z0"))

(split)
(use "jdz0Prop")
(split)
(use "jdz0Prop")
(split)
(use "CoHToCoG")
(use "CoHx1")
(split)
(use "jdz0Prop")

;; ?_81:(1#4)*(x*y+z+i)===(1#2)*((1#4)*(x1*y+z0+j)+d)
(use "RealEqTrans" (pt "(1#4)*((1#2)*x1*y+(1#2)*(z1+IntN 1)* ~d0+i)"))
(use "Eq1")
(use "RealEqTrans"
     (pt "(1#2)*((1#4)*(x1*y)+((1#4)*(0+z1* ~d0+i)+(d0+i#4)))"))
(use "Eq2")
(drop "Eq1" "Eq2")
(assert "CoG z0")
(use "jdz0Prop")
(assume "CoGz0")

(assert "Real((1#2)*((1#4)*(x1*y+z0+j)+d))")
(realproof)
(assume "R")
(simpreal "jdz0Prop")
;; ?_93:(1#2)*((1#4)*(x1*y)+((1#4)*(z0+j)+d))===(1#2)*((1#4)*(x1*y+z0+j)+d)
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z0"))
(assume "cs" "L" "z1Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?_105:(1#4)*as n*bs n+(1#4)*(cs n+j)==(1#4)*(as n*bs n+cs n+j)

(simp "<-" "RatTimesAssoc")
(simprat "<-" "RatTimesPlusDistr")
(use "RatTimesCompat")
(use "Truth")
;; ?_109:as n*bs n+(cs n+j)==as n*bs n+cs n+j
(use "Truth")
;; Now we prove the formula cut in above
(use "JKLrz")
(use "Sdtwoi")
(use "Psdd0")
(use "CoGAvcToCoG")
(intro 0 (pt "i"))
(intro 0 (pt "RealConstr([n](0#1))([p]Zero)"))
(intro 0 (pt "z1* ~d0"))
(split)
(use "Sdtwoi")
(split)
(use "CoGZero")
(split)
(use "CoGPsdTimes")
(use "CoGz1")
(use "PsdUMinus")
(use "Psdd0")
(use "RealEqRefl")
(realproof)
;; Proof finished.
(save "CoGMultcSatCoIClUxLrz")

;; cCoGMultcSatCoIClUxLrz:
;; ag=>sdtwo=>ah=>boole=>ag=>sd yprod sdtwo yprod ag yprod ag

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [ag,t,ah,boole,ag0]
;;  [let tsg
;;    (cJKLrz t boole
;;    (cCoGAvcToCoG(t pair cCoGZero pair cCoGPsdTimes ag0(cPsdUMinus boole))))
;;    (clft crht tsg pair clft tsg pair cCoHToCoG ah pair crht crht tsg)]

;; CoGMultcSatCoIClUxUz
(set-goal "allnc y,i,x,z(CoG y -> Sdtwo i -> CoG x --> CoG z --> allnc x1(
 CoH x1 -> x===(1#2)*x1 -> allnc z1(
 CoH z1 -> z===(1#2)*z1 ->
 exr d,j,x0,z0(Sd d andi Sdtwo j andi CoG x0 andi CoG z0 andi 
 (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x0*y+z0+j)+d)))))")
(assume "y" "i" "x" "z" "CoGy" "Sdtwoi" "CoGx" "CoGz"
	"x1" "CoHx1" "x1Prop"
	"z1" "CoHz1" "z1Prop")

;; Substitute x===(1#2)*x1 and z===(1#2)*z1
(assert "(1#4)*(x*y+z+i)===(1#4)*((1#2)*x1*y+(1#2)*z1+i)")
(simpreal "x1Prop")
(simpreal "z1Prop")
(use "RealEqRefl")
(realproof)
(assume "Eq1")
;; Prepare for application of CoGAvcToCoG and JKLrz
(assert "(1#4)*((1#2)*x1*y+(1#2)*z1+i)===
         (1#2)*((1#4)*(x1*y)+((1#4)*(0+z1+i)+(i#4)))")
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z1"))
(assume "cs" "L" "z1Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?_22:(1#4)*((1#2)*as n*bs n+(1#2)*cs n+i)==
;;      (1#2)*((1#4)*as n*bs n+(1#4)*(cs n+i)+(i#4))
;; Replace first i by (1#2)*RatPlus i i, and prepare for taking (1#2) out

(use "RatEqvTrans" 
 (pt "(1#4)*((1#2)*(as n*bs n)+(1#2)*cs n+(1#2)*RatPlus i i)"))
(ng #t)
(simp (pf "2=IntPlus 1 1"))
(simp "IntTimes6RewRule") ;k*(j+i)=k*j+k*i
(use "Truth")
(use "Truth")
;; Similarly replace (i#4) by (1#4)*i.
(use "RatEqvTrans" (pt "(1#2)*((1#4)*(as n*bs n)+(1#4)*(cs n+i)+(1#4)*i)"))
;; Cancel rational factors
(simprat "<-" "RatTimesPlusDistr")
(simprat "<-" "RatTimesPlusDistr")
(simprat "<-" "RatTimesPlusDistr")
(simprat "<-" "RatTimesPlusDistr")
(simp "RatTimesAssoc")
(simp "RatTimesAssoc")
(simp (pf "(1#4)*(1#2)=(1#2)*(1#4)"))
(use "RatTimesCompat")
(use "Truth")
;; ?_40:as n*bs n+cs n+RatPlus i i==as n*bs n+(cs n+i)+i
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(use "Truth")
(use "Truth")
(use "Truth")
(assume "Eq2")
;;   Eq1:(1#4)*(x*y+z+i)===(1#4)*((1#2)*x1*y+(1#2)*z1+i)
;;   Eq2:(1#4)*((1#2)*x1*y+(1#2)*z1+i)===
;;       (1#2)*((1#4)*(x1*y)+((1#4)*(0+z1+i)+(i#4)))
;; -----------------------------------------------------------------------------
;; ?_44:exr d,j,x0,z0(
;;       Sd d andd 
;;       Sdtwo j andd 
;;       CoG x0 andd CoG z0 andl (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x0*y+z0+j)+d))
;; Now we aim for using JKUz
(cut "exr j,d,z(Sdtwo j andi Sd d andi CoG z andi
                (1#4)*(0+z1+i)+(i#4)===(1#4)*(z+j)+d)")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "ExHyp")
(by-assume "ExHyp" "j" "jProp")
(by-assume "jProp" "d" "jdProp")
(by-assume "jdProp" "z0" "jdz0Prop")

(intro 0 (pt "d"))
(intro 0 (pt "j"))
(intro 0 (pt "x1"))
(intro 0 (pt "z0"))

(split)
(use "jdz0Prop")
(split)
(use "jdz0Prop")
(split)
(use "CoHToCoG")
(use "CoHx1")
(split)
(use "jdz0Prop")

;; ?_70:(1#4)*(x*y+z+i)===(1#2)*((1#4)*(x1*y+z0+j)+d)
(use "RealEqTrans" (pt "(1#4)*((1#2)*x1*y+(1#2)*z1+i)"))
(use "Eq1")
(use "RealEqTrans" (pt "(1#2)*((1#4)*(x1*y)+((1#4)*(0+z1+i)+(i#4)))"))
(use "Eq2")
(drop "Eq1" "Eq2")
(assert "CoG z0")
(use "jdz0Prop")
(assume "CoGz0")

(simpreal "jdz0Prop")
;; ?_79:(1#2)*((1#4)*(x1*y)+((1#4)*(z0+j)+d))===(1#2)*((1#4)*(x1*y+z0+j)+d)
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z0"))
(assume "cs" "L" "z1Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?_91:(1#4)*as n*bs n+(1#4)*(cs n+j)==(1#4)*(as n*bs n+cs n+j)
(simp "<-" "RatTimesAssoc")
(simprat "<-" "RatTimesPlusDistr")
(use "RatTimesCompat")
(use "Truth")
(use "Truth")
;; Now we prove the formula cut in above
(use "JKUz")
(use "Sdtwoi")
(use "CoGAvcToCoG")
(intro 0 (pt "i"))
(intro 0 (pt "RealConstr([n](0#1))([p]Zero)"))
(intro 0 (pt "z1"))
(split)
(use "Sdtwoi")
(split)
(use "CoGZero")
(split)
(use "CoHToCoG")
(use "CoHz1")
(use "RealEqRefl")
(realproof)
;; Proof finished.
(save "CoGMultcSatCoIClUxUz")

;; cCoGMultcSatCoIClUxUz:
;; ag=>sdtwo=>ah=>ah=>sd yprod sdtwo yprod ag yprod ag

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [ag,t,ah,ah0]
;;  [let tsg
;;    (cJKUz t(cCoGAvcToCoG(t pair cCoGZero pair cCoHToCoG ah0)))
;;    (clft crht tsg pair clft tsg pair cCoHToCoG ah pair crht crht tsg)]

;; CoGMultcSatCoICl
(set-goal "allnc y,i,x,z(CoG y -> Sdtwo i -> CoG x -> CoG z -> 
 exr d,j,x0,z0(Sd d andi Sdtwo j andi CoG x0 andi CoG z0 andi 
 (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x0*y+z0+j)+d)))")
(assume "y" "i" "x" "z" "CoGy" "Sdtwoi" "CoGx" "CoGz")

(inst-with-to "CoGClosure" (pt "x") "CoGx" "xCases")
(elim "xCases")
;; 5,6
(drop "xCases")

;; Case LRx
(assume "ExHypx")
(by-assume "ExHypx" "d1" "d1Prop")
(by-assume "d1Prop" "x1" "d1x1Prop")
(assert "CoG x1")
(use "d1x1Prop")
(assume "CoGx1")

;; We distinguish cases on CoG z
(inst-with-to "CoGClosure" (pt "z") "CoGz" "zCases")
(elim "zCases")
;; 20,21
(drop "zCases")

;; Subcase LRx, LRz
(assume "ExHypz")
(by-assume "ExHypz" "d0" "d0Prop")
(by-assume "d0Prop" "z1" "d0z1Prop")

(use "CoGMultcSatCoIClLrxLrz" (pt "d1") (pt "x1") (pt "d0") (pt "z1"))
(use "CoGy")
(use "Sdtwoi")
(use "CoGx")
(use "CoGz")
(use "d1x1Prop")
(use "d1x1Prop")
(use "d1x1Prop")
(use "d0z1Prop")
(use "d0z1Prop")
(use "d0z1Prop")

;; ?_21:exr x0(CoH x0 andl z===(1#2)*x0) -> 
;;      exr d,j,x0,z0(
;;       Sd d andd 
;;       Sdtwo j andd 
;;       CoG x0 andd CoG z0 andl (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x0*y+z0+j)+d))

(drop "zCases")

;; Subcase LRx, Uz
(assume "ExHypz")
(by-assume "ExHypz" "z1" "z1Prop")

(use "CoGMultcSatCoIClLrxUz" (pt "d1") (pt "x1") (pt "z1"))
(use "CoGy")
(use "Sdtwoi")
(use "CoGx")
(use "CoGz")
(use "d1x1Prop")
(use "d1x1Prop")
(use "d1x1Prop")
(use "z1Prop")
(use "z1Prop")

;; ?_6:exr x0(CoH x0 andl x===(1#2)*x0) -> 
;;     exr d,j,x0,z0(
;;      Sd d andd 
;;      Sdtwo j andd 
;;      CoG x0 andd CoG z0 andl (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x0*y+z0+j)+d))

(drop "xCases")

;; Case Ux
(assume "ExHypx")
(by-assume "ExHypx" "x1" "x1Prop")

;; We distinguish cases on CoG z
(inst-with-to "CoGClosure" (pt "z") "CoGz" "zCases")
(elim "zCases")
;; 61,62
(drop "zCases")

;; Subcase Ux, LRz
(assume "ExHypz")
(by-assume "ExHypz" "d0" "d0Prop")
(by-assume "d0Prop" "z1" "d0z1Prop")

(use "CoGMultcSatCoIClUxLrz" (pt "x1") (pt "d0") (pt "z1"))
(use "CoGy")
(use "Sdtwoi")
(use "CoGx")
(use "CoGz")
(use "x1Prop")
(use "x1Prop")
(use "d0z1Prop")
(use "d0z1Prop")
(use "d0z1Prop")

;; ?_62:exr x0(CoH x0 andl z===(1#2)*x0) -> 
;;      exr d,j,x0,z0(
;;       Sd d andd 
;;       Sdtwo j andd 
;;       CoG x0 andd CoG z0 andl (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x0*y+z0+j)+d))

(drop "zCases")

;; Subcase Ux, Uz
(assume "ExHypz")
(by-assume "ExHypz" "z1" "z1Prop")

(use "CoGMultcSatCoIClUxUz" (pt "x1") (pt "z1"))
(use "CoGy")
(use "Sdtwoi")
(use "CoGx")
(use "CoGz")
(use "x1Prop")
(use "x1Prop")
(use "z1Prop")
(use "z1Prop")
;; Proof finished.
(save "CoGMultcSatCoICl")

;; cCoGMultcSatCoICl:
;; ag=>sdtwo=>ag=>ag=>sd yprod sdtwo yprod ag yprod ag

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [ag,t,ag0,ag1]
;;  [case (cCoGClosure ag0)
;;    (InL bg -> 
;;    [case (cCoGClosure ag1)
;;      (InL bg0 -> 
;;      cCoGMultcSatCoIClLrxLrz ag t clft bg crht bg clft bg0 crht bg0)
;;      (InR ah -> cCoGMultcSatCoIClLrxUz ag t clft bg crht bg ah)])
;;    (InR ah -> 
;;    [case (cCoGClosure ag1)
;;      (InL bg -> cCoGMultcSatCoIClUxLrz ag t ah clft bg crht bg)
;;      (InR ah0 -> cCoGMultcSatCoIClUxUz ag t ah ah0)])]

(animate "CoGClosure")
(animate "CoGMultcSatCoIClLrxLrz")
(animate "CoGMultcSatCoIClLrxUz")
(animate "CoGMultcSatCoIClUxLrz")
(animate "CoGMultcSatCoIClUxUz")

(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [ag,t,ag0,ag1][case (DesYprod ag0)
;;    (InL bg -> [case (DesYprod ag1)
;;      (InL bg0 -> 
;;      [let tsg (cJKLrz t clft bg0
;;        (cCoGAvcToCoG (t pair cCoGPsdTimes ag clft bg pair 
;;                       cCoGPsdTimes crht bg0(cPsdUMinus clft bg0))))
;;        (clft crht tsg pair 
;;        clft tsg pair 
;;        cCoGPsdTimes crht bg(cPsdUMinus clft bg)pair crht crht tsg)])
;;      (InR ah -> [let tsg
;;        (cJKUz t (cCoGAvcToCoG(t pair cCoGPsdTimes ag clft bg pair
;;                               cCoHToCoG ah)))
;;        (clft crht tsg pair 
;;         clft tsg pair 
;;         cCoGPsdTimes crht bg(cPsdUMinus clft bg)pair
;;         crht crht tsg)])])
;;    (InR ah -> [case (DesYprod ag1)
;;      (InL bg -> [let tsg (cJKLrz t clft bg
;;        (cCoGAvcToCoG (t pair cCoGZero pair
;;                       cCoGPsdTimes crht bg(cPsdUMinus clft bg))))
;;        (clft crht tsg pair clft tsg pair
;;         cCoHToCoG ah pair crht crht tsg)])
;;      (InR ah0 -> [let tsg
;;        (cJKUz t(cCoGAvcToCoG(t pair cCoGZero pair cCoHToCoG ah0)))
;;        (clft crht tsg pair clft tsg pair
;;         cCoHToCoG ah pair crht crht tsg)])])]

(deanimate "CoGClosure")
(deanimate "CoGMultcSatCoIClLrxLrz")
(deanimate "CoGMultcSatCoIClLrxUz")
(deanimate "CoGMultcSatCoIClUxLrz")
(deanimate "CoGMultcSatCoIClUxUz")

;; Putting things together.  First a lemma for estimates.

;; CoGMultcToCoGAux
(set-goal "all x,y,z,i(Real x -> Real y -> Real z -> Sdtwo i ->
 abs x<<=1 -> abs y<<=1 -> abs z<<=1 -> abs((1#4)*(x*y+z+i))<<=1)")
(assume "x" "y" "z" "i" "Rx" "Ry" "Rz" "Sdtwoi" "xBd" "yBd" "zBd")
(simpreal "RealAbsTimes")
(use "RealLeTrans" (pt "RealTimes(1#4)4"))
(use "RealLeMonTimesTwo")
(use "RatNNegToRealNNeg")
(use "Truth")
(use "RealNNegAbs")
(autoreal)
(use "RatLeToRealLe")
(use "Truth")
;; ?_11:abs(x*y+z+i)<<=4
(use "RealLeTrans" (pt "(RealTimes 1 1)+1+2"))
(use "RealLeTrans" (pt "abs(x*y)+(abs z)+RealAbs i"))
(use "RealLeTrans" (pt "abs(x*y+z)+RealAbs i"))
(use "RealLeAbsPlus")
(autoreal)
(use "RealLeMonPlus")
(use "RealLeAbsPlus")
(autoreal)
(use "RatLeToRealLe")
(use "Truth")
(use "RealLeMonPlus")
(use "RealLeMonPlus")
(simpreal "RealAbsTimes")
(use "RealLeMonTimesTwo")
(use "RealNNegAbs")
(autoreal)
(use "RealNNegAbs")
(autoreal)
(use "xBd")
(use "yBd")
(autoreal)
(use "zBd")
(use "RatLeToRealLe")
(use "RatLeTrans" (pt "2#1"))
(use "SdtwoBound")
(use "Sdtwoi")
(use "Truth")
(use "RatLeToRealLe")
(use "Truth")
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
;; Proof finished.
(save "CoGMultcToCoGAux")

(set! COMMENT-FLAG #f)
;; CoGMultcToCoG
(set-goal "allnc z0(
 exr i,x,y,z(Sdtwo i andi CoG x andi CoG y andi CoG z andi
             z0===(1#4)*(x*y+z+i)) -> CoG z0)")
(assume "z0" "Qz0")
(coind "Qz0" (pf "exr i,x,y,z
          (Sdtwo i andi CoG x andi CoG y andi CoG z andi
           z0===(1#4)*(x*y+z+i)) -> CoH z0"))
;; 3,4
(assume "z2" "Qz2")
(by-assume "Qz2" "i" "iProp")
(by-assume "iProp" "x" "ixProp")
(by-assume "ixProp" "y" "ixyProp")
(by-assume "ixyProp" "z" "ixyzProp")
(assert "CoG y")
(use "ixyzProp")
(assume "CoGy")
;; let introduction
(cut "exr d,j,x0,z0(
 Sd d andi Sdtwo j andi CoG x0 andi CoG z0 andi
 (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x0*y+z0+j)+d))")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "ExCoGAvcSatCoICl")
(by-assume "ExCoGAvcSatCoICl" "d1" "d1Prop")
(by-assume "d1Prop" "i1" "d1i1Prop")
(by-assume "d1i1Prop" "x1" "d1i1x1Prop")
(by-assume "d1i1x1Prop" "z1" "d1i1x1z1Prop")
(assert "Sd d1")
(use "d1i1x1z1Prop")
(assume "Sdd1")
(assert "Sdtwo i1")
(use "d1i1x1z1Prop")
(assume "Sdtwoi1")
(assert "CoG x1")
(use "d1i1x1z1Prop")
(assume "CoGx1")
(assert "CoG z1")
(use "d1i1x1z1Prop")
(assume "CoGz1")
(assert "(1#4)*(x*y+z+i)===(1#2)*((1#4)*(x1*y+z1+i1)+d1)")
(use "d1i1x1z1Prop")
(assume "Eq")
(drop "d1i1x1z1Prop")
(assert "d1=0 orr Psd d1")
 (use-with "SdDisj" (pt "d1") "?")
 (use "Sdd1")
(assume "Disj")
(elim "Disj")
;; 57,58
(drop "Disj")
(assume "d1=0") ;case small
(intro 1)
(intro 0 (pt "(1#4)*(x1*y+z1+i1)"))
(intro 0 (pt "z2"))
(split)
(realproof)
(split)
;; ?_66:abs((1#4)*(x1*y+z1+i1))<<=1
(use "CoGMultcToCoGAux")
(autoreal)
(use "Sdtwoi1")
(use "CoGToBd")
(use "CoGx1")
(use "CoGToBd")
(use "CoGy")
(use "CoGToBd")
(use "CoGz1")
(split)
(intro 1)
(intro 0 (pt "i1"))
(intro 0 (pt "x1"))
(intro 0 (pt "y"))
(intro 0 (pt "z1"))
(split)
(use "Sdtwoi1")
(split)
(use "CoGx1")
(split)
(use "CoGy")
(split)
(use "CoGz1")
(use "RealEqRefl")
(autoreal)
(split)
(simpreal "ixyzProp")
(simpreal "Eq")
;;   d1=0:d1=0
;; -----------------------------------------------------------------------------
;; ?_97:(1#2)*((1#4)*(x1*y+z1+i1)+d1)===(1#2)*((1#4)*(x1*y+z1+i1))
(simp "d1=0")
(simpreal "RealPlusZero")
(use "RealEqRefl")
(autoreal)
(simpreal "ixyzProp")
(use "RealEqRefl")
(autoreal)
;; 58
(drop "Disj")
(assume "Psdd1")
(intro 0)
(intro 0 (pt "d1"))
(intro 0 (pt "(1#4)*(x1*y* ~d1+z1* ~d1+RealTimes i1~d1)"))
(intro 0 (pt "z2"))
(split)
(use "Psdd1")
(split)
(autoreal)
(split)
;; ?_114:abs((1#4)*(x1*y* ~d1+z1* ~d1+RealTimes i1~d1))<<=1
(use "CoGMultcToCoGAux")
(autoreal)
(simp (pf "~(i1*d1)= ~i1*d1"))
(use "IntTimesSdtwoPsdToSdtwo")
;; ?_125:Sdtwo(~i1)
(use "SdtwoIntUMinus")
(use "Sdtwoi1")
(use "Psdd1")
(use "Truth")
(simpreal "RealAbsTimes")
(use "RealLeTrans" (pt "RealTimes 1 1"))
(use "RealLeMonTimesTwo")
(use "RealNNegAbs")
(autoreal)
(use "RealNNegAbs")
(autoreal)
(use "CoGToBd")
(use "CoGx1")
(use "CoGToBd")
(use "CoGy")
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
(use "RatLeToRealLe")
;; ?_142:RatLe abs d1 1
(ng #t)
(simp "PsdToAbsOne")
(use "Truth")
(use "Psdd1")
(simpreal "RealAbsTimes")
(use "RealLeTrans" (pt "RealTimes 1 1"))
(use "RealLeMonTimesTwo")
(use "RealNNegAbs")
(autoreal)
(use "RealNNegAbs")
(autoreal)
(use "CoGToBd")
(use "CoGz1")
;; ?_154:abs~d1<<=1
(use "RatLeToRealLe")
;; ?_158:RatLe abs d1 1
(ng #t)
(simp "PsdToAbsOne")
(use "Truth")
(use "Psdd1")
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
;; 115
(split)
(intro 1)
(intro 0 (pt "i1* ~d1"))
(intro 0 (pt "x1"))
(intro 0 (pt "y* ~d1"))
(intro 0 (pt "z1* ~d1"))
(split)
(use "IntTimesSdtwoPsdToSdtwo")
(use "Sdtwoi1")
(use "PsdUMinus")
(use "Psdd1")
(split)
(use "CoGx1")
(split)
(use "CoGPsdTimes")
(use "CoGy")
(use "PsdUMinus")
(use "Psdd1")
(split)
(use "CoGPsdTimes")
(use "CoGz1")
(use "PsdUMinus")
(use "Psdd1")
;; ?_183:(1#4)*(x1*y* ~d1+z1* ~d1+RealTimes i1~d1)===
;;       (1#4)*(x1*(y* ~d1)+z1* ~d1+i1* ~d1)
(use "RealEqSToEq")
(autoreal)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z1"))
(assume "cs" "L" "z1Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
(use "Truth")
;;?_164:z2===(1#2)*((1#4)*(x1*y* ~d1+z1* ~d1+RealTimes i1~d1)+IntN 1)* ~d1 andnc
;;       z2===z2
(split)
(simpreal "ixyzProp")
(simpreal "Eq")
;; ?_202:(1#2)*((1#4)*(x1*y+z1+i1)+d1)===
;;       (1#2)*((1#4)*(x1*y* ~d1+z1* ~d1+RealTimes i1~d1)+IntN 1)* ~d1
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z1"))
(assume "cs" "L" "z1Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?_214:(1#2)*((1#4)*(as n*bs n+cs n+i1)+d1)== 
;;       ~((1#2)*((1#4)*(~(as n*bs n*d1)+ ~(cs n*d1)+ ~(i1*d1))+IntN 1)*d1)
(simp "<-" "RatTimes3RewRule")
(simp "<-" "RatTimesAssoc")
(use "RatTimesCompat")
(use "Truth")
;; ?_218:(1#4)*(as n*bs n+cs n+i1)+d1==
;;       ((1#4)*(~(as n*bs n*d1)+ ~(cs n*d1)+ ~(i1*d1))+IntN 1)* ~d1
(simp "<-" "RatTimesAssoc")
(simprat "RatTimesPlusDistrLeft")
(simp "RatTimesIntNL")
(use "RatPlusCompat")
;; ?_222:(1#4)*(as n*bs n+cs n+i1)==
;;       (1#4)*(~(as n*(bs n*d1))+ ~(cs n*d1)+ ~(i1*d1))* ~d1
(simp "<-" "RatTimesAssoc")
(use "RatTimesCompat")
(use "Truth")
(simprat "RatTimesPlusDistrLeft")
(simprat "RatTimesPlusDistrLeft")
(ng #t)
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimesAssoc")
(ng #t)
(simp "<-" "RatTimesAssoc")
(simp "<-" "IntTimesAssoc")
(assert "allnc d(Psd d -> d*d=1)")
 (assume "d" "Psdd")
 (elim "Psdd")
 (use "Truth")
 (use "Truth")
(assume "PsdSquareOne")
(simp "PsdSquareOne")
(use "Truth")
(use "Psdd1")
(use "Truth")
;; ?_200:z2===z2
(use "RealEqRefl")
(use "RealEqElim0" (pt "(1#4)*(x*y+z+i)"))
(use "ixyzProp")

;; ?_22:exr j,d,x0,y0,z0(
;;       Sdtwo j andd 
;;       Sd d andd 
;;       CoG x0 andd 
;;       CoG y0 andd CoG z0 andl (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x0*y0+z0+j)+d))

;; Now we prove the formula cut in above, using CoGMultcSatCoICl
(use "CoGMultcSatCoICl")
(use "CoGy")
(use "ixyzProp")
(use "ixyzProp")
(use "ixyzProp")
;; 4
(assume "z2" "Qz2")
(by-assume "Qz2" "i" "iProp")
(by-assume "iProp" "x" "ixProp")
(by-assume "ixProp" "y" "ixyProp")
(by-assume "ixyProp" "z" "ixyzProp")
(assert "CoG y")
(use "ixyzProp")
(assume "CoGy")
;; let introduction
(cut "exr d,j,x0,z0(
 Sd d andi Sdtwo j andi CoG x0 andi CoG z0 andi
 (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x0*y+z0+j)+d))")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "ExCoGAvcSatCoICl")
(by-assume "ExCoGAvcSatCoICl" "d1" "d1Prop")
(by-assume "d1Prop" "i1" "d1i1Prop")
(by-assume "d1i1Prop" "x1" "d1i1x1Prop")
(by-assume "d1i1x1Prop" "z1" "d1i1x1z1Prop")
(assert "Sd d1")
 (use "d1i1x1z1Prop")
(assume "Sdd1")
(assert "Sdtwo i1")
 (use "d1i1x1z1Prop")
(assume "Sdtwoi1")
(assert "CoG x1")
 (use "d1i1x1z1Prop")
(assume "CoGx1")
(assert "CoG z1")
 (use "d1i1x1z1Prop")
(assume "CoGz1")
(assert "(1#4)*(x*y+z+i)===(1#2)*((1#4)*(x1*y+z1+i1)+d1)")
 (use "d1i1x1z1Prop")
(assume "Eq")
(drop "d1i1x1z1Prop")
(assert "d1=0 orr Psd d1")
 (use-with "SdDisj" (pt "d1") "?")
 (use "Sdd1")
(assume "Disj")
(elim "Disj")
;; 302,303
(drop "Disj")
(assume "d1=0") ;case small
(intro 1)
(intro 0 (pt "(1#4)*(x1*y+z1+i1)"))
(intro 0 (pt "z2"))
(split)
(autoreal)
(split)
;; ?_311:abs((1#4)*(x1*y+z1+i1))<<=1
(use "CoGMultcToCoGAux")
(autoreal)
(use "Sdtwoi1")
(use "CoGToBd")
(use "CoGx1")
(use "CoGToBd")
(use "CoGy")
(use "CoGToBd")
(use "CoGz1")
(split)
(intro 1)
(intro 0 (pt "i1"))
(intro 0 (pt "x1"))
(intro 0 (pt "y"))
(intro 0 (pt "z1"))
(split)
(use "Sdtwoi1")
(split)
(use "CoGx1")
(split)
(use "CoGy")
(split)
(use "CoGz1")
(use "RealEqRefl")
(autoreal)
(split)
(simpreal "ixyzProp")
(simpreal "Eq")
;;   d1=0:d1=0
;; -----------------------------------------------------------------------------
;; ?_342:(1#2)*((1#4)*(x1*y+z1+i1)+d1)===(1#2)*((1#4)*(x1*y+z1+i1))
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z1"))
(assume "cs" "L" "z1Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
(simp "d1=0")
(use "Truth")
;; ?_340:z2===z2
(use "RealEqRefl")
(use "RealEqElim0" (pt "(1#4)*(x*y+z+i)"))
(use "ixyzProp")
;; 303
(drop "Disj")
(assume "Psdd1")
(intro 0)
(intro 0 (pt "d1"))
(intro 0 (pt "(1#4)*(x1*y* d1+z1* d1+RealTimes i1 d1)"))
(intro 0 (pt "z2"))
(split)
(use "Psdd1")
(split)
(autoreal)
(split)
;; ?_368:abs((1#4)*(x1*y*d1+z1*d1+RealTimes i1 d1))<<=1
(use "CoGMultcToCoGAux")
(autoreal)
(use "IntTimesSdtwoPsdToSdtwo")
(use "Sdtwoi1")
(use "Psdd1")
(simpreal "RealAbsTimes")
(use "RealLeTrans" (pt "RealTimes 1 1"))
(use "RealLeMonTimesTwo")
(use "RealNNegAbs")
(autoreal)
(use "RealNNegAbs")
(autoreal)
(use "CoGToBd")
(use "CoGx1")
(use "CoGToBd")
(use "CoGy")
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
(use "RatLeToRealLe")
;; ?_393:RatLe abs d1 1
(ng #t)
(simp "PsdToAbsOne")
(use "Truth")
(use "Psdd1")
(simpreal "RealAbsTimes")
(use "RealLeTrans" (pt "RealTimes 1 1"))
(use "RealLeMonTimesTwo")
(use "RealNNegAbs")
(autoreal)
(use "RealNNegAbs")
(autoreal)
(use "CoGToBd")
(use "CoGz1")
;; ?_405:abs d1<<=1
(use "RatLeToRealLe")
;; ?_409:RatLe abs d1 1
(ng #t)
(simp "PsdToAbsOne")
(use "Truth")
(use "Psdd1")
(use "RatLeToRealLe")
(use "Truth")
(autoreal)
;; 369
(split)
(intro 1)
(intro 0 (pt "i1*d1"))
(intro 0 (pt "x1"))
(intro 0 (pt "y*d1"))
(intro 0 (pt "z1*d1"))
(split)
(use "IntTimesSdtwoPsdToSdtwo")
(use "Sdtwoi1")
(use "Psdd1")
(split)
(use "CoGx1")
(split)
(use "CoGPsdTimes")
(use "CoGy")
(use "Psdd1")
(split)
(use "CoGPsdTimes")
(use "CoGz1")
(use "Psdd1")
;; ?_432:(1#4)*(x1*y*d1+z1*d1+RealTimes i1 d1)===(1#4)*(x1*(y*d1)+z1*d1+i1*d1)
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z1"))
(assume "cs" "L" "z1Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
(use "Truth")
;; ?_3415:z2===(1#2)*((1#4)*(x1*y*d1+z1*d1+RealTimes i1 d1)+1)*d1 andnc z2===z2
(split)
(simpreal "ixyzProp")
(simpreal "Eq")
;; ?_450:(1#2)*((1#4)*(x1*y+z1+i1)+d1)===
;;       (1#2)*((1#4)*(x1*y*d1+z1*d1+RealTimes i1 d1)+1)*d1
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y"))
(assume "bs" "N" "yDef")
(cases (pt "z1"))
(assume "cs" "L" "z1Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?_352:(1#2)*((1#4)*(as n*bs n+cs n+i1)+d1)==
;;       (1#2)*((1#4)*(as n*bs n*d1+cs n*d1+i1*d1)+1)*d1
(simp "<-" "RatTimesAssoc")
(use "RatTimesCompat")
(use "Truth")
;; ?_465:(1#4)*(as n*bs n+cs n+i1)+d1==((1#4)*(as n*bs n*d1+cs n*d1+i1*d1)+1)*d1
(simp "<-" "RatTimesAssoc")
(simprat "RatTimesPlusDistrLeft")
(use "RatPlusCompat")
;; ?_468:(1#4)*(as n*bs n+cs n+i1)==(1#4)*(as n*(bs n*d1)+cs n*d1+i1*d1)*d1
(simp "<-" "RatTimesAssoc")
(simprat "RatTimesPlusDistrLeft")
(simprat "RatTimesPlusDistrLeft")
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimesAssoc")
(ng #t)
(simp "<-" "RatTimesAssoc")
(simp "<-" "IntTimesAssoc")
(assert "allnc d(Psd d -> d*d=1)")
 (assume "d" "Psdd")
 (elim "Psdd")
 (use "Truth")
 (use "Truth")
(assume "PsdSquareOne")
(simp "PsdSquareOne")
(use "Truth")
(use "Psdd1")
(use "Truth")
;; ?_448:z2===z2
(use "RealEqRefl")
(use "RealEqElim0" (pt "(1#4)*(x*y+z+i)"))
(use "ixyzProp")

;; ?_267:exr d,j,x0,z0(
;;        Sd d andd 
;;        Sdtwo j andd 
;;        CoG x0 andd CoG z0 andl (1#4)*(x*y+z+i)===(1#2)*((1#4)*(x0*y+z0+j)+d))

;; Now we prove the formula cut in above, using CoGMultcSatCoICl
(use "CoGMultcSatCoICl")
(use "CoGy")
(use "ixyzProp")
(use "ixyzProp")
(use "ixyzProp")
;; Proof finished.
(save "CoGMultcToCoG")

;; cCoGMultcToCoG: sdtwo yprod ag yprod ag yprod ag=>ag

(define eterm (proof-to-extracted-term))
(add-var-name "tggg" (py "sdtwo yprod ag yprod ag yprod ag"))
(add-var-name "stgg" (py "sd yprod sdtwo yprod ag yprod ag"))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [tggg](CoRec sdtwo yprod ag yprod ag yprod ag=>ag
;;              sdtwo yprod ag yprod ag yprod ag=>ah)tggg
;;  ([tggg0][let stgg (cCoGMultcSatCoICl
;;                      clft crht crht tggg0 clft tggg0
;;                      clft crht tggg0 crht crht crht tggg0)
;;      [case (cSdDisj clft stgg)
;;       (DummyL -> InR(InR(clft crht stgg pair 
;;                          clft crht crht stgg pair
;;                          clft crht crht tggg0 pair
;;                          crht crht crht stgg)))
;;       (Inr boole -> InL(boole pair 
;;        InR(cIntTimesSdtwoPsdToSdtwo
;;             clft crht stgg(cPsdUMinus boole)pair 
;;             clft crht crht stgg pair 
;;             cCoGPsdTimes clft crht crht tggg0
;;                          (cPsdUMinus boole)pair 
;;             cCoGPsdTimes crht crht crht stgg
;;                          (cPsdUMinus boole))))]])
;;  ([tggg0][let stgg (cCoGMultcSatCoICl
;;                      clft crht crht tggg0 clft tggg0
;;                      clft crht tggg0 crht crht crht tggg0)
;;      [case (cSdDisj clft stgg)
;;       (DummyL -> InR(InR(clft crht stgg pair 
;;                          clft crht crht stgg pair 
;;                          clft crht crht tggg0 pair
;;                          crht crht crht stgg)))
;;       (Inr boole -> InL(boole pair 
;;        InR(cIntTimesSdtwoPsdToSdtwo
;;             clft crht stgg boole pair 
;;             clft crht crht stgg pair 
;;             cCoGPsdTimes clft crht crht tggg0 boole pair 
;;             cCoGPsdTimes crht crht crht stgg boole)))]])

;; CoGMult
(set-goal "allnc x,y(CoG x -> CoG y -> CoG(x*y))")
(assume "x" "y" "CoGx" "CoGy")
(use "CoGMultcToCoG")
(use "CoGMultToMultc")
(use "CoGx")
(use "CoGy")
;; Proof finished.
(save "CoGMult")

(define eterm (proof-to-extracted-term))
(define neterm-CoGMult (rename-variables (nt eterm)))
(ppc neterm-CoGMult)

;; [ag,ag0]cCoGMultcToCoG(cCoGMultToMultc ag ag0)
