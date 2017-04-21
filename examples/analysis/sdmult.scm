;; 2017-04-21.  sdmult.scm

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

(remove-var-name "d") ;will be used as variable name for integers
(load "~/git/minlog/examples/analysis/sdJK.scm") ;adds d,e:int

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Inductive predicate I
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(add-algs "str" '("C" "sd=>str=>str"))
(add-var-name "u" "v" "w" (py "str"))
(add-totality "str")

(add-ids
 (list (list "I" (make-arity (py "rea")) "str"))
 '("allnc d,x,y(Sd d -> Real x -> abs x<<=1 -> I x -> y===(1#2)*(x+d) -> I y)"
   "GenI"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; General properties of I
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; By the least-fixed-point (or elimination) axiom I is a fixed point.
;; Hence the inverse implication holds as well.

;; Recall (1) and-junctors are rightassociative, and (2) andi (and
;; used interactively) determines decorations automatically).  Example:
;; (pp (pf "Pvar1 andi Pvar^2 andi Pvar3 andi Pvar^4"))
;; Pvar1 andd Pvar^2 andr Pvar3 andl Pvar^4

;; IClauseInv
(set-goal
 "allnc x(I x -> exr d,x0(
 Sd d andi Real x0 andi abs x0<<=1 andi I x0 andi x===(1#2)*(x0+d)))")
(assume "x" "Ix")
(elim "Ix")
(assume "d" "x1" "y1" "Sdd" "Rx1" "x1Bd" "Ix1" "ExHyp" "EqHyp")
(intro 0 (pt "d"))
(intro 0 (pt "x1"))
(split)
(use "Sdd")
(split)
(use "Rx1")
(split)
(use "x1Bd")
(split)
(use "Ix1")
(use "EqHyp")
;; Proof finished.
(save "IClauseInv")
;; (cdp)

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [u][if u (PairConstr sd str)]
(ppc neterm)
;; [u][case u (C s u -> s pair u)]

;; We now add the companion predicate CoI for I, meant to be the
;; greatest-fixed-point of the I clauses.

(add-co "I" (list "RealEq"))
(pp "CoIClause")
;; allnc x(
;;  CoI x -> 
;;  exr d,x0,y(
;;   Sd d andd 
;;   Real x0 andr abs x0<<=1 andr CoI x0 andl y===(1#2)*(x0+d) andnc x===y))

;; We provide a simplified variant of CoIClause.

;; CoIClosure
(set-goal "allnc x(CoI x -> exr d,x1(
 Sd d andi abs x1<<=1 andi CoI x1 andi x===(1#2)*(x1+d)))")
(assume "x" "CoIx")
(inst-with-to "CoIClause" (pt "x") "CoIx" "CoIClauseInst")
(by-assume "CoIClauseInst" "d" "dProp")
(by-assume "dProp" "x1" "dx1Prop")
(by-assume "dx1Prop" "y" "dx1yProp")
(intro 0 (pt "d"))
(intro 0 (pt "x1"))
(split)
(use "dx1yProp")
(split)
(use "dx1yProp")
(split)
(use "dx1yProp")
(use "RealEqTrans" (pt "y"))
(use "dx1yProp")
(use "dx1yProp")
;; Proof finished.
(save "CoIClosure")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; (Destr str)

;; By the greatest-fixed-point (or coinduction) axiom CoI is a fixed
;; point.  Hence the inverse implication holds as well.

;; CoIClauseInv
(set-goal
 "allnc x(exr d,x0,y(Sd d andi Real x0 andi abs x0<<=1 andi CoI x0 andi
  y===(1#2)*(x0+d) andi x===y) -> CoI x)")
(assume "x" "ExHyp")
(coind "ExHyp")
(assume "x1" "x1Prop")
(by-assume "x1Prop" "d" "dProp")
(by-assume "dProp" "x2" "dx2Prop")
(by-assume "dx2Prop" "y" "dx2yProp")
(intro 0 (pt "d"))
(intro 0 (pt "x2"))
(intro 0 (pt "y"))
(split)
(use "dx2yProp")
(split)
(use "dx2yProp")
(split)
(use "dx2yProp")
(split)
(intro 0)
(use "dx2yProp")
(split)
(use "dx2yProp")
(use "dx2yProp")
;; Proof finished.
(save "CoIClauseInv")

(define eterm (proof-to-extracted-term))
(add-var-name "su" (py "sd yprod str"))
(define neterm (rename-variables (nt eterm)))
(define nneterm (rename-variables (nt (undelay-delayed-corec neterm 1))))
(pp nneterm)

;; [su]C clft su crht su

;; We show that CoI satisfies the clause of I

;; GenCoI 
(set-goal "allnc d,x,y(Sd d -> Real x -> abs x<<=1 -> CoI x ->
  y===(1#2)*(x+d) -> CoI y)")
(assume "d" "x" "y" "Sdd" "Rx" "xBd" "CoIx" "EqHyp")
(use "CoIClauseInv")
(intro 0 (pt "d"))
(intro 0 (pt "x"))
(intro 0 (pt "y"))
(split)
(use "Sdd")
(split)
(use "Rx")
(split)
(use "xBd")
(split)
(use "CoIx")
(split)
(use "EqHyp")
(use "RealEqRefl")
(use "RealEqElim0" (pt "(1#2)*(x+d)"))
(use "EqHyp")
;; Proof finished.
(save "GenCoI")

(define eterm (proof-to-extracted-term))
(animate "CoIClauseInv")
(define neterm (rename-variables (nt eterm)))
(define nneterm (rename-variables (nt (undelay-delayed-corec neterm 1))))
(pp nneterm)

;; [s,u]C clft(s pair u)crht(s pair u)

(animate "Lft")
(animate "Rht")
(define neterm (rename-variables (nt eterm)))
(define nneterm (nt (undelay-delayed-corec neterm 1)))
(pp nneterm)
;; C
(deanimate "Lft")
(deanimate "Rht")

;; An immediate consequence is that the least-fixed-point is contained
;; in the greatest-fixed-point.

;; IToCoI
(set-goal "allnc x(I x -> CoI x)")
(assume "x" "Ix")
(elim "Ix")
(assume "d" "x1" "y" "Sdd" "Rx1" "x1Bd" "Ix1" "CoIx1" "EqHyp")
(use "GenCoI" (pt "d") (pt "x1"))
(use "Sdd")
(use "Rx1")
(use "x1Bd")
(use "CoIx1")
(use "EqHyp")
;; Proof finished.
(save "IToCoI")

(define eterm (proof-to-extracted-term))
(animate "GenCoI")
(define neterm (rename-variables (nt eterm)))
(define nneterm (rename-variables (nt (undelay-delayed-corec neterm 1))))
(pp nneterm)

;; [u](Rec str=>str)u([s,u0,u1]C clft(s pair u1)crht(s pair u1))

(animate "Lft")
(animate "Rht")
(define neterm (rename-variables (nt eterm)))
(define nneterm (rename-variables (nt (undelay-delayed-corec neterm 1))))
(pp nneterm)
;; [u](Rec str=>str)u([s,u0]C s)
(deanimate "Lft")
(deanimate "Rht")

;; This is extensionally equal to the identity on str.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Specific properties of I
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; IToReal
(set-goal "all x(I x -> Real x)")
(assume "x" "Ix")
(inst-with-to "IClauseInv" (pt "x") "Ix" "IClauseInvInst")
(by-assume "IClauseInvInst" "d" "dProp")
(by-assume "dProp" "x0" "dx0Prop") 
(use "RealEqElim0" (pt "(1#2)*(x0+d)"))
(use "dx0Prop")
;; Proof finished.
(save "IToReal")

;; RealICompat
(set-goal "allnc x,y(x===y -> I x -> I y)")
(assume "x" "y" "x===y" "Ix")
(elim "Ix")
(assume
 "d" "x1" "y1" "Useless1" "Useless2" "Useless3" "Useless4" "Iy" "Useless5")
(use "Iy")
;; Proof finished.
(save "RealICompat")

(define eterm (proof-to-extracted-term))
(pp (rename-variables eterm))

;; [u](Rec str=>str)u([s,u0,u1]u1)

;; This is the identity on str

;; CoIToReal
(set-goal "all x(CoI x -> Real x)")
(assume "x" "CoIx")
(inst-with-to "CoIClause" (pt "x") "CoIx" "CoIClauseInst")
(by-assume "CoIClauseInst" "d" "dProp")
(by-assume "dProp" "x1" "dx1Prop")
(by-assume "dx1Prop" "y" "dx1yProp")
(use "RealEqElim0" (pt "y"))
(use "dx1yProp")
;; Proof finished.
(save "CoIToReal")

;; SdBoundReal
(set-goal "all d(Sd d -> RealAbs d<<=1)")
(assume "d" "Sdd")
(use "RealLeIntro")
(realproof)
(use "RealRat")
(use "RealNNegIntro")
(realproof)
(assume "p")
(ng)
;; ?_9:0<=2**p+ ~(abs d*2**p)+1
(use "IntLeTrans" (pt "2**p+ ~(2**p)+1"))
(use "Truth")
(use "IntLeMonPlus")
(use "IntLeMonPlus")
(use "Truth")
(simp "IntLe5RewRule")
(use "IntLeTrans" (pt "IntP 1*2**p"))
(use "IntLeMonTimes")
(use "Truth")
(use "SdBound")
(use "Sdd")
(use "Truth")
(use "Truth")
;; Proof finished.
(save "SdBoundReal")

;; CoIToBd
(set-goal "all x(CoI x -> abs x<<=1)")
(assume "x" "CoIx")
(inst-with-to "CoIClause" (pt "x") "CoIx" "CoIClauseInst")
(by-assume "CoIClauseInst" "d" "dProp")
(by-assume "dProp" "x1" "dx1Prop")
(by-assume "dx1Prop" "y" "dx1yProp")
(simpreal "dx1yProp")
(simpreal "dx1yProp")
(assert "Real x1")
(use "dx1yProp")
(assume "Rx1")
(use "RealLeAbs")
;; 19,20
(simpreal (pf "RealConstr([n](1#1))([p]Zero)===RealTimes(1#2)(RealPlus 1 1)"))
(use "RealLeMonTimes")
(use "RealNNegPos")
(use "RealLeMonPlus")
(use "RealLeTrans" (pt "abs x1"))
(use "RealLeAbsId")
(use "Rx1")
(use "dx1yProp")
(use "RealLeTrans" (pt "RealAbs d"))
(use "RealLeAbsId")
(use "RealRat")
(use "SdBoundReal")
(use "dx1yProp")
;; ?_22:1===(1#2)*RealPlus 1 1
(use "RealEqRefl")
(use "RealRat")
;; ?_20:~((1#2)*(x1+d))<<=1
(simpreal "<-" (pf "~(RealUMinus 1)===1"))
(use "RealLeUMinus")
(simpreal
 (pf "RealUMinus 1===RealTimes(1#2)(RealPlus(RealUMinus 1)(RealUMinus 1))"))
(use "RealLeMonTimes")
(use "RealNNegPos")
(use "RealLeMonPlus")
(simpreal "<-" (pf "~ ~x1===x1"))
(use "RealLeUMinus")
(use "RealLeTrans" (pt "abs x1"))
(simpreal "<-" "RealAbsUMinus")
(use "RealLeAbsId")
(realproof)
(use "Rx1")
(use "dx1yProp")
(use "RealUMinusUMinus")
(use "Rx1")
(simpreal "<-" (pf "~(RealUMinus d)===d"))
(use "RealLeUMinus")
(use "RealLeTrans" (pt "RealAbs d"))
(simpreal "<-" "RealAbsUMinus")
(use "RealLeAbsId")
(use "RealRat")
(use "RealRat")
(use "SdBoundReal")
(use "dx1yProp")
(use "RealUMinusUMinus")
(use "RealRat")
(use "RealEqRefl")
(use "RealRat")
(use "RealUMinusUMinus")
(use "RealRat")
;; Proof finished.
(save "CoIToBd")

;; CoICompat
(set-goal "allnc x,y(x===y -> CoI x -> CoI y)")
(assume "x" "y" "x===y" "CoIx")
(inst-with-to "CoIClause" (pt "x") "CoIx" "CoIClauseInst")
(by-assume "CoIClauseInst" "d" "dProp")
(by-assume "dProp" "x1" "dx1Prop")
(by-assume "dx1Prop" "y1" "dx1y1Prop")
(use "CoIClauseInv")
(intro 0 (pt "d"))
(intro 0 (pt "x1"))
(intro 0 (pt "y1"))
(split)
(use "dx1y1Prop")
(split)
(use "dx1y1Prop")
(split)
(use "dx1y1Prop")
(split)
(use "dx1y1Prop")
(split)
(use "dx1y1Prop")
(use "RealEqSym")
(use "RealEqTrans" (pt "x"))
(use "RealEqSym")
(use "dx1y1Prop")
(use "x===y")
;; Proof finished.
(save "CoICompat")

(define eterm (proof-to-extracted-term))
(deanimate "CoIClause")
(define neterm (rename-variables (nt eterm)))
(define nneterm (rename-variables (nt (undelay-delayed-corec neterm 1))))
(pp (rename-variables nneterm))

;; [u]C clft(cCoIClause u)crht(cCoIClause u)

;; This is the identity on str

;; CoIUMinus
(set-goal "allnc x(CoI(~x) -> CoI x)")
(assume "x" "CoI-x")
(coind "CoI-x")
(assume "x1" "CoI-x1")
(assert "Real x1")
(use "RealUMinusRealInv")
(use "CoIToReal")
(use "CoI-x1")
(assume "Rx1")
(inst-with-to "CoIClosure" (pt "~x1") "CoI-x1" "CoIClosureInst")
(by-assume "CoIClosureInst" "d" "dProp")
(by-assume "dProp" "x2" "dx2Prop")
;; Since realproof cannot look into conjunctions we provide
(assert "CoI x2")
(use "dx2Prop")
(assume "CoIx2")
(intro 0 (pt "~d"))
(intro 0 (pt "~x2"))
(intro 0 (pt "x1"))
(split)
(use "SdUMinus")
(use "dx2Prop")
(split)
(realproof)
(split)
(simpreal "RealAbsUMinus")
(use "dx2Prop")
(realproof)
(split)
(intro 1)
(simpreal "RealUMinusUMinus")
(use "CoIx2")
(realproof)
(split)
;; 38,39
(simpreal "<-" "RealUMinusPlusRat")
(simpreal "RealTimesIdUMinus")
(use "RealUMinusInj")
(simpreal "RealUMinusUMinus")
(use "dx2Prop")
(realproof)
(realproof)
(use "RealRat")
(realproof)
(use "RealEqRefl")
(realproof)
;; Proof finished.
(save "CoIUMinus")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [u]
;;  (CoRec str=>str)u
;;  ([u0]
;;    cSdUMinus clft(cCoIClosure u0)pair InR(cCoICompat crht(cCoIClosure u0)))

;; CoIClosureInv
(set-goal "allnc d,x(Sd d -> CoI x -> CoI((1#2)*(x+d)))")
(assume "d" "x" "Sdd" "CoIx")
(use "CoIClauseInv")
(intro 0 (pt "d"))
(intro 0 (pt "x"))
(intro 0 (pt "(1#2)*(x+d)"))
(split)
(use "Sdd")
(split)
(realproof)
(split)
(use "CoIToBd")
(use "CoIx")
(split)
(use "CoIx")
(split)
(use "RealEqRefl")
(realproof)
(use "RealEqRefl")
(realproof)
;; Proof finished.
(save "CoIClosureInv")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [s,u](CoRec sd yprod str=>str)(s pair u)([su]clft su pair InL crht su)

;; CoIAvToAvc
(set-goal "allnc x,y(CoI x -> CoI y -> 
 exr i,x1,y1(Sdtwo i andi CoI x1 andi CoI y1 andi
 (1#2)*(x+y)===(1#4)*(x1+y1+i)))")
(assume "x" "y" "CoIx" "CoIy")
(inst-with-to "CoIClosure" (pt "x") "CoIx" "CoIClosureInstx")
(by-assume "CoIClosureInstx" "d" "dProp")
(by-assume "dProp" "x1" "dx1Prop")
(assert "CoI x1")
(use "dx1Prop")
(assume "CoIx1")
(inst-with-to "CoIClosure" (pt "y") "CoIy" "CoIClosureInsty")
(by-assume "CoIClosureInsty" "e" "eProp")
(by-assume "eProp" "y1" "ey1Prop")
(assert "CoI y1")
(use "ey1Prop")
(assume "CoIy1")
(intro 0 (pt "d+e"))
(intro 0 (pt "x1"))
(intro 0 (pt "y1"))
(split)
(use "IntPlusSdToSdtwo")
(use "dx1Prop")
(use "ey1Prop")
(split)
(use "CoIx1")
(split)
(use "CoIy1")
;; ?_35:(1#2)*(x+y)===(1#4)*(x1+y1+(d+e))
(assert "Real((1#4)*(x1+y1+(d+e)))")
(realproof)
(assume "R")
(simpreal "dx1Prop")
(simpreal "ey1Prop")
;; ?_40:(1#2)*((1#2)*(x1+d)+(1#2)*(y1+e))===(1#4)*(x1+y1+(d+e))
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y1"))
(assume "bs" "N" "y1Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?_50:(1#2)*((1#2)*(as n+d)+(1#2)*(bs n+e))==(1#4)*(as n+bs n+(d+e))
(simprat "<-" "RatTimesPlusDistr")
;; ?_51:(1#2)*((1#2)*(as n+d+(bs n+e)))==(1#4)*(as n+bs n+(d+e))
(ng #t)
;; ?_52:(1#4)*(as n+d+bs n+e)==(1#4)*(as n+bs n+(d+e))
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
;; ?_57:d+(bs n+e)==bs n+(d+e)
(ng #t)
(simp (pf "d+bs n=bs n+d"))
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
(use "Truth")
(use "RatPlusComm")
;; Proof finished.
(save "CoIAvToAvc")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [u,u0]
;;  cIntPlusSdToSdtwo clft(cCoIClosure u)clft(cCoIClosure u0)pair 
;;  crht(cCoIClosure u)pair crht(cCoIClosure u0)

;; For CoIAvcSatCoICl we need J,K.

;; CoIAvcSatCoIClAuxJ
(set-goal "allnc d,e,i(Sd d -> Sd e -> Sdtwo i -> Sdtwo(J(d+e+i*2)))")
(assume "d" "e" "i" "Sdd" "Sde" "Sdtwoi")
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
(assert "exl t SdtwoMR t i")
(use "SdtwoMRIntro")
(use "Sdtwoi")
(assume "ExHyp3")
(by-assume "ExHyp3" "t" "tProp")
(use "SdtwoMRElim"
     (pt "IntToSdtwo(J(SdToInt s1+SdToInt s2+SdtwoToInt t*2))"))
(simp (pf "J(SdToInt s1+SdToInt s2+SdtwoToInt t*2)=J(d+e+i*2)"))
(use "SdtwoMRIntToSdtwo")
;; ?_27:abs(J(d+e+i*2))<=2
(use "JProp")
(simp (pf "SdToInt s1+SdToInt s2+SdtwoToInt t*2=d+e+i*2"))
(use "Truth")
;; ?_29:SdToInt s1+SdToInt s2+SdtwoToInt t*2=d+e+i*2
(inst-with-to "SdMRId" (pt "d") (pt "s1") "s1Prop" "SdMRIdInst1")
(inst-with-to "SdMRId" (pt "e") (pt "s2") "s2Prop" "SdMRIdInst2")
(inst-with-to "SdtwoMRId" (pt "i") (pt "t") "tProp" "SdtwoMRIdInst")
(simp "SdMRIdInst1")
(simp "SdMRIdInst2")
(simp "SdtwoMRIdInst")
(use "Truth")
;; Proof finished.
(save "CoIAvcSatCoIClAuxJ")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [s,s0,t]IntToSdtwo(J(SdToInt s+SdToInt s0+SdtwoToInt t*2))

;; CoIAvcSatCoIClAuxK
(set-goal "allnc d,e,i(Sd d -> Sd e -> Sdtwo i -> Sd(K(d+e+i*2)))")
(assume "d" "e" "i" "Sdd" "Sde" "Sdtwoi")
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
(assert "exl t SdtwoMR t i")
(use "SdtwoMRIntro")
(use "Sdtwoi")
(assume "ExHyp3")
(by-assume "ExHyp3" "t" "tProp")
(use "SdMRElim" (pt "IntToSd(K(SdToInt s1+SdToInt s2+SdtwoToInt t*2))"))
(simp (pf "K(SdToInt s1+SdToInt s2+SdtwoToInt t*2)=K(d+e+i*2)"))
(use "SdMRIntToSd")
;; ?_27:abs(K(d+e+i*2))<=1
(use "KProp")
;; ?_28:abs(d+e+i*2)<=6
(use "IntLeTrans" (pt "IntP 2+IntP 4"))
(use "IntLeTrans" (pt "abs(d+e)+abs(i*2)"))
(use "IntLeAbsPlus")
(use "IntLeMonPlus")
(use "IntLeTrans" (pt "IntP 1+IntP 1"))
(use "IntLeTrans" (pt "abs d+abs e"))
(use "IntLeAbsPlus")
(use "IntLeMonPlus")
(use "SdBound")
(use "Sdd")
(use "SdBound")
(use "Sde")
(use "Truth")
(ng #t)
(use "IntLeTrans" (pt "IntP 2*IntP 2"))
(use "IntLeMonTimes")
(use "Truth")
(use "SdtwoBound")
(use "Sdtwoi")
(use "Truth")
(use "Truth")
(simp (pf "SdToInt s1+SdToInt s2+SdtwoToInt t*2=d+e+i*2"))
(use "Truth")
;; ?_50:SdToInt s1+SdToInt s2+SdtwoToInt t*2=d+e+i*2
(inst-with-to "SdMRId" (pt "d") (pt "s1") "s1Prop" "SdMRIdInst1")
(inst-with-to "SdMRId" (pt "e") (pt "s2") "s2Prop" "SdMRIdInst2")
(inst-with-to "SdtwoMRId" (pt "i") (pt "t") "tProp" "SdtwoMRIdInst")
(simp "SdMRIdInst1")
(simp "SdMRIdInst2")
(simp "SdtwoMRIdInst")
(use "Truth")
;; Proof finished.
(save "CoIAvcSatCoIClAuxK")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [s,s0,t]IntToSd(K(SdToInt s+SdToInt s0+SdtwoToInt t*2))

;; CoIAvcSatCoIClAux 
;; (set-goal "all x,y,d,e,i(Real x -> Real y ->
;;  (1#4)*((1#2)*(x+d)+(1#2)*(y+e)+i)===
;;  (1#2)*((1#4)*(x+y+J(d+e+i*2))+K(d+e+i*2)))")
;; already proved in JK.scm

;; CoIAvcSatCoICl
(set-goal "allnc i,x,y(Sdtwo i -> CoI x -> CoI y ->
 exr j,d,x1,y1(Sdtwo j andi Sd d andi CoI x1 andi CoI y1 andi
 (1#4)*(x+y+i)===(1#2)*((1#4)*(x1+y1+j)+d)))")
(assume "i" "x" "y" "Sdtwoi" "CoIx" "CoIy")
(inst-with-to "CoIClosure" (pt "x") "CoIx" "CoIClosureInst1")
(by-assume "CoIClosureInst1" "d" "dProp")
(by-assume "dProp" "x1" "dx1Prop")
(assert "CoI x1")
(use "dx1Prop")
(assume "CoIx1")
(inst-with-to "CoIClosure" (pt "y") "CoIy" "CoIClosureInst2")
(by-assume "CoIClosureInst2" "e" "eProp")
(by-assume "eProp" "y1" "ey1Prop")
(assert "CoI y1")
(use "ey1Prop")
(assume "CoIy1")
(intro 0 (pt "J(d+e+i*2)"))
(intro 0 (pt "K(d+e+i*2)"))
(intro 0 (pt "x1"))
(intro 0 (pt "y1"))
(split)
(use "CoIAvcSatCoIClAuxJ")
(use "dx1Prop")
(use "ey1Prop")
(use "Sdtwoi")
(split)
(use "CoIAvcSatCoIClAuxK")
(use "dx1Prop")
(use "ey1Prop")
(use "Sdtwoi")
(split)
(use "CoIx1")
(split)
(use "CoIy1")
;; ?_42:(1#4)*(x+y+i)===(1#2)*((1#4)*(x1+y1+J(d+e+i*2))+K(d+e+i*2))
(simpreal "dx1Prop")
(simpreal "ey1Prop")
;; ?_44:(1#4)*((1#2)*(x1+d)+(1#2)*(y1+e)+i)===
;;      (1#2)*((1#4)*(x1+y1+J(d+e+i*2))+K(d+e+i*2))
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y1"))
(assume "bs" "N" "y1Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
;; ?_54:(1#4)*((1#2)*(as n+d)+(1#2)*(bs n+e)+i)==
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
;; ?_66:(1#8)*as n+(d#8)+(1#8)*bs n+(e#8)+(i#4)==
;;      (1#8)*as n+(1#8)*bs n+(J(d+e+i*2)#8)+(K(d+e+i*2)#2)
(use "RatEqvTrans" (pt "(1#8)*as n+((d#8)+(1#8)*bs n+(e#8)+(i#4))"))
(use "Truth")
(use "RatEqvTrans" (pt "(1#8)*as n+((1#8)*bs n+(J(d+e+i*2)#8)+(K(d+e+i*2)#2))"))
(use "RatPlusCompat")
(use "Truth")
(simp (pf "(d#8)+(1#8)*bs n=(1#8)*bs n+(d#8)"))
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
;; ?_79:(d#8)+((e#8)+(i#4))==(J(d+e+i*2)#8)+(K(d+e+i*2)#2)
(simprat (pf "(i#4)==(i*2#8)"))
(simprat (pf "(K(d+e+i*2)#2)==(K(d+e+i*2)*4#8)"))
;; ?_82:(d#8)+((e#8)+(i*2#8))==(J(d+e+i*2)#8)+(K(d+e+i*2)*4#8)
(simprat "<-" "RatEqvConstrPlus")
(simprat "<-" "RatEqvConstrPlus")
(simprat "<-" "RatEqvConstrPlus")
(simp (pf "J(d+e+i*2)+K(d+e+i*2)*4=K(d+e+i*2)*4+J(d+e+i*2)"))
(simp "KJProp")
(use "Truth")
(use "IntPlusComm")
;; ?_83:(K(d+e+i*2)#2)==(K(d+e+i*2)*4#8)
(ng #t)
(simp "<-" "IntTimesAssoc")
(use "Truth")
;; ?_81:(i#4)==(i*2#8)
(ng #t)
(simp "<-" "IntTimesAssoc")
(use "Truth")
;; ?_74:(d#8)+(1#8)*bs n=(1#8)*bs n+(d#8)
(use "RatPlusComm")
(use "Truth")
;; Proof finished.
(save "CoIAvcSatCoICl")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [t,u,u0]
;;  cCoIAvcSatCoIClAuxJ clft(cCoIClosure u)clft(cCoIClosure u0)t pair 
;;  cCoIAvcSatCoIClAuxK clft(cCoIClosure u)clft(cCoIClosure u0)t pair 
;;  crht(cCoIClosure u)pair crht(cCoIClosure u0)

;; This term can be read as follows.  Given t, u, u0, destruct the
;; latter two.  Both are composed, i.e., of the form s1u1 and s2u2.
;; Take their components s1,u1 and s2,u2.  Then we obtain the quadruple
;; J(s1,s2,t) pair K(s1,s2,t) pair u1 pair u2.

;; SdtwoBoundReal
(set-goal "all k(Sdtwo k -> RealAbs k<<=2)")
(assume "i" "Sdtwoi")
(use "RealLeIntro")
(use "RealRat")
(use "RealRat")
(use "RealNNegIntro")
(use "RealRat")
(assume "p")
(ng)
;; ?_9:0<=SZero(2**p)+ ~(abs i*2**p)+1
;; ?_9:0<=2**p+ ~(abs d*2**p)+1
(use "IntLeTrans" (pt "2*2**p+ ~(2*2**p)+1"))
(use "Truth")
(use "IntLeMonPlus")
(use "IntLeMonPlus")
(use "Truth")
(simp "IntLe5RewRule")
(use "IntLeTrans" (pt "IntP 2*2**p"))
(use "IntLeMonTimes")
(use "Truth")
(use "SdtwoBound")
(use "Sdtwoi")
(use "Truth")
(use "Truth")
;; Proof finished.
(save "SdtwoBoundReal")

;; Putting things together

;; CoIAvcToCoI
(set-goal "allnc z(exr i,x,y(Sdtwo i andi CoI x andi CoI y andi
 z===(1#4)*(x+y+i)) -> CoI z)")
(assume "z" "Qz")
(coind "Qz")
(assume "x" "Qx")
(by-assume "Qx" "i" "iProp")
(by-assume "iProp" "x1" "x1iProp")
(by-assume "x1iProp" "y1" "y1x1iProp")
(cut "exr j,d,x0,y0(
 Sdtwo j andi Sd d andi CoI x0 andi CoI y0 andi
 (1#4)*(x1+y1+i)===(1#2)*((1#4)*(x0+y0+j)+d))")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "CoIAvcSatCoIClInst")
(by-assume "CoIAvcSatCoIClInst" "j" "jProp")
(by-assume "jProp" "d" "jdProp")
(by-assume  "jdProp" "x2" "jdx2Prop")
(by-assume "jdx2Prop" "y2" "jdx2y2Prop")
(assert "CoI x2")
(use "jdx2y2Prop")
(assume "CoIx2")
(assert "CoI y2")
(use "jdx2y2Prop")
(assume "CoIy2")
(intro 0 (pt "d"))
(intro 0 (pt "(1#4)*(x2+y2+j)"))
(intro 0 (pt "x"))
(split)
(use "jdx2y2Prop")
(split)
(realproof)
(split)
(inst-with-to "CoIToBd" (pt "x2") "CoIx2" "x2Bd")
(inst-with-to "CoIToBd" (pt "y2") "CoIy2" "y2Bd")
(simpreal "RealAbsTimes")
(use "RealLeTrans" (pt "RealAbs(1#4)*((RealPlus 1 1)+2)"))
(use "RealLeMonTimes")
(use "RealNNegPos")
(use "RealLeTrans" (pt "abs(x2+y2)+RealAbs j"))
(use "RealLeAbsPlus")
(realproof)
(use "RealRat")
(use "RealLeMonPlus")
(use "RealLeTrans" (pt "abs x2+abs y2"))
(use "RealLeAbsPlus")
(realproof)
(realproof)
(use "RealLeMonPlus")
(use "x2Bd")
(use "y2Bd")
(use "SdtwoBoundReal")
(use "jdx2y2Prop")
(ng #t)
(use "RealLeRefl")
(use "RealRat")
(realproof)
(use "RealRat")
(split)
(intro 1)
(intro 0 (pt "j"))
(intro 0 (pt "x2"))
(intro 0 (pt "y2"))
(split)
(use "jdx2y2Prop")
(split)
(use "CoIx2")
(split)
(use "CoIy2")
(use "RealEqRefl")
(realproof)
(split)
(simpreal "y1x1iProp")
(use "jdx2y2Prop")
(use "RealEqRefl")
(use "RealEqElim0" (pt "(1#4)*(x1+y1+i)"))
(use "y1x1iProp")
;; Now we prove the formula cut in above
(use "CoIAvcSatCoICl")
(use "y1x1iProp")
(use "y1x1iProp")
(use "y1x1iProp")
;; Proof finished.
(save "CoIAvcToCoI")

(define eterm (proof-to-extracted-term))
(add-var-name "tuv" (py "sdtwo yprod str yprod str"))
(add-var-name "tsuv" (py "sdtwo yprod sd yprod str yprod str"))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [tuv]
;;  (CoRec sdtwo yprod str yprod str=>str)tuv
;;  ([tuv0]
;;    [let tsuv
;;      (cCoIAvcSatCoICl clft tuv0 clft crht tuv0 crht crht tuv0)
;;      (clft crht tsuv pair InR(clft tsuv pair crht crht tsuv))])

;; CoIAverage
(set-goal "allnc x,y(CoI x -> CoI y -> CoI((1#2)*(x+y)))")
(assume "x" "y" "CoIx" "CoIy")
(cut "exr i,x0,y0(Sdtwo i andd 
                  CoI x0 andd CoI y0 andl (1#2)*(x+y)===(1#4)*(x0+y0+i))")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "CoIAvToAvcInst")
(by-assume "CoIAvToAvcInst" "i" "iProp")
(by-assume "iProp" "x1" "ix1Prop")
(by-assume "ix1Prop" "y1" "ix1y1Prop")
(use "CoIAvcToCoI")
(intro 0 (pt "i"))
(intro 0 (pt "x1"))
(intro 0 (pt "y1"))
(split)
(use "ix1y1Prop")
(split)
(use "ix1y1Prop")
(split)
(use "ix1y1Prop")
(use "ix1y1Prop")
;; Now prove the formula cut in above
(use-with "CoIAvToAvc" (pt "x") (pt "y") "CoIx" "CoIy")
;; Proof finished.
(save "CoIAverage")

(define eterm (proof-to-extracted-term))
(define neterm-CoIAverage (rename-variables (nt eterm)))
(pp neterm-CoIAverage)

;; [u,u0](cId sdtwo yprod str yprod str=>str)cCoIAvcToCoI(cCoIAvToAvc u u0)

(animate "CoIAvcToCoI")
(animate "CoIAvToAvc")
(animate "CoIAvcSatCoICl")
(animate "CoIAvcSatCoIClAuxJ")
(animate "CoIAvcSatCoIClAuxK")
(animate "IntPlusSdToSdtwo")

(define neterm-CoIAverage (rename-variables (nt eterm)))
(ppc neterm-CoIAverage)

;; [u,u0]
;;  [let tuv
;;    (IntToSdtwo(SdToInt clft(cCoIClosure u)+SdToInt clft(cCoIClosure u0))pair 
;;    crht(cCoIClosure u)pair crht(cCoIClosure u0))
;;    ((CoRec sdtwo yprod str yprod str=>str)tuv
;;    ([tuv0]
;;      [let tsuv
;;        (IntToSdtwo
;;        (J
;;         (SdToInt clft(cCoIClosure clft crht tuv0)+
;;          SdToInt clft(cCoIClosure crht crht tuv0)+
;;          SdtwoToInt clft tuv0*2))pair 
;;        IntToSd
;;        (K
;;         (SdToInt clft(cCoIClosure clft crht tuv0)+
;;          SdToInt clft(cCoIClosure crht crht tuv0)+
;;          SdtwoToInt clft tuv0*2))pair 
;;        crht(cCoIClosure clft crht tuv0)pair crht(cCoIClosure crht crht tuv0))
;;        (clft crht tsuv pair InR(clft tsuv pair crht crht tsuv))]))]

(deanimate "CoIAvcToCoI")
(deanimate "CoIAvToAvc")
(deanimate "CoIAvcSatCoICl")
(deanimate "CoIAvcSatCoIClAuxJ")
(deanimate "CoIAvcSatCoIClAuxK")
(deanimate "IntPlusSdToSdtwo")

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
 (realproof)
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
 (realproof)
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
(realproof)
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

;; CoISdTimes
(set-goal "allnc d,x(Sd d -> CoI x -> CoI(d*x))")
(assume "d" "x" "Sdd")
(elim "Sdd")
;; 3-5
;; Case 1
(assume "CoIx")
(simpreal "RealOneTimes")
(use "CoIx")
(realproof)
;; 4
;; Case 0
(assume "CoIx")
(simpreal "RealZeroTimes")
(use "CoIZero")
(realproof)
;; 5
;; Case -1
(assume "CoIx")
(use "CoIUMinus")
(simpreal "RealIntNOneTimes")
(simpreal "RealUMinusUMinus")
(use "CoIx")
(realproof)
(realproof)
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
(realproof)
(realproof)
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
(realproof)
(assume "CoIv")
(cut "exr d,x(Sd d andi abs x<<=1 andi CoI x andi
 (1#4)*(z0+d1*y+i)===(1#2)*(x+d))")
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
(realproof)
(realproof)
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
(realproof)
(realproof)
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
(cut "exr d,x(
 Sd d andi abs x<<=1 andi CoI x andi (1#2)*(e1*x1+d1*y1)===(1#2)*(x+d))")
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
(realproof)
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
(realproof)
(use "RealEqSym")
(simpreal "RealTimesPlusDistrLeft")
(simpreal "RealPlusAssoc")
(simpreal (pf "d1*y1+x1*e1===z1+d"))
(simpreal "<-" "RealPlusAssoc")
(use "RealEqRefl")
(realproof)
(use "RealRat")
(use "RealRat")
(realproof)
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
(realproof)
(realproof)
(use "RealRat")
(use "RealRat")
(use "RealRat")
(realproof)
(use "RealEqSym")
(simpreal "RealTimesComm")
(simpreal "RealTimesAssoc")
(simpreal "RealPlusComm")
(ng)
(simpreal (pf "x1*e1===e1*x1"))
(use "RealOneTimes")
(realproof)
(use "RealTimesComm")
(realproof)
(use "RealRat")
(realproof)
(realproof)
(realproof)
(use "RealRat")
(use "RealRat")
(use "RealRat")
(realproof)
(use "RealRat")
(realproof)
(realproof)
(use "RealRat")
(use "RealRat")
(realproof)
(realproof)
(realproof)
(realproof)
(realproof)
(realproof)
(realproof)
(realproof)
(use "RealRat")
(realproof)
(use "RealRat")
(realproof)
(realproof)
(realproof)
(realproof)
(use "RealRat")
(realproof)
(use "RealRat")
(use "RealRat")
(realproof)
(realproof)
(use "RealRat")
(use "RealRat")
(realproof)
(use "RealRat")
(realproof)
(realproof)
;;
(simpreal "RealTimesComm")
(use "e1y1Prop")
(use "RealRat")
(realproof)
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
(cut "exr d1,x1(Sd d1 andi abs x1<<=1 andi CoI x1 andi x===(1#2)*(x1+d1))")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "ExHypx")
(by-assume "ExHypx" "d1" "d1Prop")
(by-assume "d1Prop" "x1" "d1x1Prop")
(cut "exr d0,z0(Sd d0 andi abs z0<<=1 andi CoI z0 andi z===(1#2)*(z0+d0))")
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
;;   {d1}  {x1}  d1x1Prop:Sd d1 andd abs x1<<=1 andr CoI x1 andl x===(1#2)*(x1+d1)
;;   {d0}  {z0}  d0z0Prop:Sd d0 andd abs z0<<=1 andr CoI z0 andl z===(1#2)*(z0+d0)
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
(realproof)
(use "RealEqTrans"
     (pt "(1#2)*((1#4)*(x1*y)+(1#4)*(z2+e+2*e0)+(1#4)*RealPlus d0 i)"))
;; ?_76:(1#4)*((1#2)*(x1+d1)*y+(1#2)*(z0+d0)+i)===
;;      (1#2)*((1#4)*(x*y)+(1#4)*(z2+e+2*e0)+(1#4)*RealPlus d i)
(simpreal "<-" "z2ee0Prop")
(simpreal "CoIMultcSatCoIClEq1")
(use "RealEqRefl")
(realproof)
(realproof)
(realproof)
(realproof)
;; ?_77:(1#2)*((1#4)*(x1*y)+(1#4)*(z2+e+2*e0)+(1#4)*RealPlus d0 i)===
;;      (1#2)*((1#4)*(x1*y+z2+J(e+2*e0+d0+i))+K(e+2*e0+d0+i))
(use "CoIMultcSatCoIClEq2")
(realproof)
(realproof)
(realproof)
;; Now we need to prove the formulas cut in above
;; ?_24:exr z,e,e0(
;;       CoI z andd Sd e andd Sd e0 andl (1#4)*(z0+d1*y+i)===(1#4)*(z+e+2*e0))
(use "CoIMultcSatCoIClAvcDestr")
(use "d0z0Prop")
(use "d1x1Prop")
(use "CoIy")
(use "Conj")
;; ?_14:exr d,z0(Sd d andd abs z0<<=1 andr CoI z0 andl z===(1#2)*(z0+d))
(use "CoIClosure")
(use "Conj")
;; ?_4:exr d,x0(Sd d andd abs x0<<=1 andr CoI x0 andl x===(1#2)*(x0+d))
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
(realproof)
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
(realproof)
(use "RealRat")
(use "RealLeMonPlus")
(use "RealLeTrans" (pt "abs(x2*y1)+abs z2"))
(use "RealLeAbsPlus")
(realproof)
(realproof)
(use "RealLeMonPlus")
(simpreal "RealAbsTimes")
(use "RealLeMonTimesTwo")
(use "RealNNegAbs")
(realproof)
(use "RealNNegAbs")
(realproof)
(use "x2Bd")
(use "y1Bd")
(realproof)
(realproof)
(use "z2Bd")
(use "SdtwoBoundReal")
(use "djx2z2Prop")
(ng #t)
(use "RealLeRefl")
(use "RealRat")
(realproof)
(use "RealRat")
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
(realproof)
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

