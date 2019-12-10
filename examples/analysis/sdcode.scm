;; 2019-11-27

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

;; (load "~/git/minlog/examples/analysis/digits.scm")

;; (set! COMMENT-FLAG #t)

(display "loading sdcode.scm ...") (newline)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Inductive predicate I
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; str renamed into ai (algebra for I), similar to ag and ah for gray
;; code.  Reason: str is a parametrized algebra treated in lib/str.scm

(add-algs "ai" '("C" "sd=>ai=>ai"))
(add-var-name "u" "v" "w" (py "ai"))
(add-totality "ai")

(add-ids
 (list (list "I" (make-arity (py "rea")) "ai"))
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
;; (cdp)
(save "IClauseInv")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [u][if u (PairConstr sd ai)]
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
;; (cdp)
(save "CoIClauseInv")

(define eterm (proof-to-extracted-term))
(add-var-name "su" (py "sd yprod ai"))
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
;; (cdp)
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
;; (cdp)
(save "IToCoI")

(define eterm (proof-to-extracted-term))
(animate "GenCoI")
(define neterm (rename-variables (nt eterm)))
(define nneterm (rename-variables (nt (undelay-delayed-corec neterm 1))))
(pp nneterm)
;; [u](Rec ai=>ai)u([s,u0,u1]C clft(s pair u1)crht(s pair u1))

(animate "Lft")
(animate "Rht")
(define neterm (rename-variables (nt eterm)))
(define nneterm (rename-variables (nt (undelay-delayed-corec neterm 1))))
(pp nneterm)
;; [u](Rec ai=>ai)u([s,u0]C s)
(deanimate "Lft")
(deanimate "Rht")

;; This is extensionally equal to the identity on ai.

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
;; (cdp)
(save "IToReal")

;; RealICompat
(set-goal "allnc x,y(x===y -> I x -> I y)")
(assume "x" "y" "x===y" "Ix")
(elim "Ix")
(assume
 "d" "x1" "y1" "Useless1" "Useless2" "Useless3" "Useless4" "Iy" "Useless5")
(use "Iy")
;; Proof finished.
;; (cdp)
(save "RealICompat")

(define eterm (proof-to-extracted-term))
(pp (rename-variables eterm))

;; [u](Rec ai=>ai)u([s,u0,u1]u1)

;; This is the identity on ai

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
;; (cdp)
(save "CoIToReal")

;; SdBoundReal
(set-goal "all d(Sd d -> RealAbs d<<=1)")
(assume "d" "Sdd")
(use "RealLeIntro")
(autoreal)
(use "RealNNegIntro")
(autoreal)
(assume "p")
(ng)
;; ?^9:0<=2**p+ ~(abs d*2**p)+1
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
;; (cdp)
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
;; ?^22:1===(1#2)*RealPlus 1 1
(use "RealEqRefl")
(use "RealRat")
;; ?^20:~((1#2)*(x1+d))<<=1
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
(autoreal)
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
;; (cdp)
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
;; (cdp)
(save "CoICompat")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(define nneterm (rename-variables (nt (undelay-delayed-corec neterm 1))))
(pp nneterm)
;; [u]C clft DesYprod u crht DesYprod u
;; This is the identity on ai

;; We provide a simplified variant of CoIClause.

;; CoIClosure
(set-goal "allnc x(CoI x -> exr d,x1(Sd d andi CoI x1 andi x===(1#2)*(x1+d)))")
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
(use "RealEqTrans" (pt "y"))
(use "dx1yProp")
(use "dx1yProp")
;; Proof finished.
;; (cdp)
(save "CoIClosure")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; (Destr ai)

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
(autoreal)
(split)
(simpreal "RealAbsUMinus")
(use "CoIToBd")
(use "CoIx2")
(autoreal)
(split)
(intro 1)
(simpreal "RealUMinusUMinus")
(use "CoIx2")
(autoreal)
(split)
;; 39,40
(simpreal "<-" "RealUMinusPlusRat")
(simpreal "RealTimesIdUMinus")
(use "RealUMinusInj")
(simpreal "RealUMinusUMinus")
(use "dx2Prop")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "CoIUMinus")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [u](CoRec ai=>ai)u
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
(autoreal)
(split)
(use "CoIToBd")
(use "CoIx")
(split)
(use "CoIx")
(split)
(use "RealEqRefl")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "CoIClosureInv")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [s,u](CoRec sd yprod ai=>ai)(s pair u)([su]clft su pair InL crht su)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Another specific property of I
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; For use in the Haskell translation we prove a further specific
;; property of CoI.  We prove RealToCoI, based on archive/koepp/CsToStr.scm
;; in an optimized form (avoiding real multiplication)

;; TwoTimesPlusIntReal
(set-goal "all as,M,i(Real(RealConstr as M) ->
	    Real(RealConstr([n]2*(as n)+i)([p](M(PosS p)))))")
(assume "as" "M" "i" "Rx")
(inst-with-to "RealConstrToCauchy" (pt "as") (pt "M") "Rx" "CauchyInst")
(inst-with-to "RealConstrToMon" (pt "as") (pt "M") "Rx" "MonInst")
(intro 0)
(intro 0)
(assume "p" "n" "m" "Bd1" "Bd2")
(ng) 
(simprat (pf "2*as n +i + ~(2*as m)+ ~i==2*(as n + ~(as m))"))
(simp "RatAbsTimes")
(ng #t)
(simp "RatTimesComm")
(simprat (pf "(1#2**p)==(1#2**PosS p)*2"))
(use "RatLeMonTimes")
(ng #t)
(use "Truth")
(use "CauchyElim" (pt "M"))
(use "CauchyInst")
(use "Bd1")
(use "Bd2")
(simprat "<-" "RatPlusHalfExpPosS")
(simprat (pf "(1#2**PosS p)+(1#2**PosS p)==(1#2**PosS p)*1+(1#2**PosS p)*1"))
(simprat "<-" "RatTimesPlusDistr")
(ng #t)
(use "Truth")
(ng #t)
(use "Truth")
(simp "<-" "RatPlusAssoc")
(simp-with "RatPlusComm" (pt "~(2*as m)") (pt "~i#1"))
(simp "<-" "RatPlusAssoc")
(ng #t)
(simp (pf "~(2* as m)=2* ~(as m)"))
(simprat "RatTimesPlusDistr")
(ng #t)
(use "Truth")
(ng #t)
(use "Truth")
(ng #t)
(intro 0)
(assume "p" "q" "p<=q")
(ng #t)
(use "MonElim" (pt "as"))
(use "MonInst")
(ng #t)
(use "p<=q")
;; Proof finished.
;; (cdp)
(save "TwoTimesPlusIntReal")

;; TwoTimesPlusEq
(set-goal "all as,M,i(Real(RealConstr as M) -> 
  RealConstr([n]2*(as n)+i)([p](M(PosS p)))===2*(RealConstr as M) +i)")
(assume "as" "M" "i" "Rx")
(use "RealEqSToEq")
(use "TwoTimesPlusIntReal")
(use "Rx")
(autoreal)
(use "RealEqSIntro")
(assume "n")
(use "Truth")
;; Proof finished.
;; (cdp)
(save "TwoTimesPlusEq")

;; ;; TwoTimesPlusEq
;; (set-goal "all as,M,i(Real(RealConstr as M) -> 
;;   RealConstr([n]2*(as n)+i)([p](M(PosS p)))===2*(RealConstr as M) +i)")
;; (assume "as" "M" "i" "Rx")
;; (ng #t)
;; (use "RealEqSToEq")
;; (use "TwoTimesPlusIntReal")
;; (use "Rx")
;; (autoreal)
;; (assert "Real(2*RealConstr as M +i)")
;; (autoreal)
;; (ng #t)
;; (use "Id")
;; (ng #t)
;; (intro 0)
;; (assume "n")
;; (ng #t)
;; (use "Truth")
;; ;; Proof finished.
;; ;; (cdp)
;; (save "TwoTimesPlusEq")

;; ApproxSplitZeroPtFive
(set-goal "all x(Real x ->  x<<=(1#2) ori 0<<=x)")
(assume "x" "Rx")
(use "ApproxSplit" (pt "1"))
(autoreal)
(ng #t)
(use "Truth")
;; Proof finished.
;; (cdp)
(save "ApproxSplitZeroPtFive")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
(animate "ApproxSplit")
(define neterm (rename-variables (nt eterm)))
(ppc neterm)
;; [x][case x (RealConstr as M -> as(M 3)<=(1#4))]
(deanimate "ApproxSplit")

;; ApproxSplitZeroMinusPtFive
(set-goal "all x(Real x ->  x<<=0 oru (IntN 1#2)<<=x)")
(assume "x" "Rx")
(use "ApproxSplit" (pt "1"))
(autoreal)
(ng #t)
(use "Truth")
;; Proof finished.
;; (cdp)
(save "ApproxSplitZeroMinusPtFive")

(define eterm (proof-to-extracted-term))
(animate "ApproxSplit")
(define neterm (rename-variables (nt eterm)))
(ppc neterm)
;; [x][case x (RealConstr as M -> as(M 3)<=(IntN 1#4))]
(deanimate "ApproxSplit")

;; RealToCoIAux
(set-goal "all x(Real x -> abs x<<=1 ->
 exd s exl y(Real y andnc abs y<<=1 andnc x===(1#2)*(y+(SdToInt s))))")
(assume "x")
(cases (pt "x"))
(assume "as" "M" "xDef" "Rx" "abs x<=1")
(assert "x<<=0 oru ~(1#2)<<=x")
  (use "ApproxSplitZeroMinusPtFive")
  (simp "xDef")
  (autoreal)
(assume "Disj")
(elim "Disj")
;; 10,11
(assume "x<=0")
(intro 0 (pt "SdL"))
(intro 0 (pt "RealConstr([n](2*as n+1))([p](M(PosS p)))"))
(split)
(use "TwoTimesPlusIntReal")
(use "Rx")
(split)
;; ?^18:abs(RealConstr([n]2*as n+1)([p]M(PosS p)))<<=1
(use "RealLeAbs")
(simpreal "TwoTimesPlusEq")
(use "RealLeTrans"
     (pt "2*(RealConstr([n]0)([p]Zero))+(RealConstr([n]1)([p]Zero))"))
(use "RealLeMonPlus")
(use "RealLeMonTimes")
(intro 0)
(use "RealRat")
(assume "p")
(ng #t)
(use "Truth")
(simp "<-" "xDef")
(use "x<=0")
(use "RealLeRefl")
(use "RealRat")
(ng #t)
(use "RealLeRefl")
(use "RealRat")
(use "Rx")
(simpreal "TwoTimesPlusEq")
(simpreal "RealUMinusPlus")
(use "RealLeTrans"
     (pt "(RealConstr([n]2)([p]Zero))+ ~(RealConstr([n]1)([p]Zero))"))
(use "RealLeMonPlus")
(simpreal "RealTimesComm")
(simpreal "<-" "RealTimesUMinusId")
(simpreal-with "<-" "RealOneTimes" (pt "RealConstr([n]2)([p]Zero)") "?")
(simpreal "RealTimesAssoc")
(use "RealLeMonTimesL")
(intro 0)
(use "RealRat")
(assume "p")
(ng #t)
(use "Truth")
(simpreal "RealTimesOne")
(use "RealLeTrans" (pt "abs x"))
(simpreal "<-" "RealAbsUMinus")
(simp "<-" "xDef")
(use "RealLeAbsId")
(realproof)
(simp "xDef")
(use "Rx")
(simp "xDef")
(use "abs x<=1")
(autoreal)
(use "RealLeRefl")
(use "RealRat")
(ng #t)
(use "RealLeRefl")
(use "RealRat")
(use "RealRat")
(realproof)
(realproof)
;; ?^19:
;; RealConstr as M===(1#2)*(RealConstr([n]2*as n+1)([p]M(PosS p))+SdToInt SdL)
(simpreal "TwoTimesPlusEq")
(simp "<-" "xDef")
(ng #t)
(simpreal "<-" "RealPlusAssoc")
(ng #t)
(simpreal "RealPlusZero")
(simpreal "RealTimesAssoc")
(ng #t)
(simpreal "RealOneTimes")
(use "RealEqRefl")
(autoreal)
(assume "(~1#2)<<=x")
(assert "x<<=(1#2) oru 0<<=x")
 (use "ApproxSplitZeroPtFive")
 (simp "xDef")
 (autoreal)
(assume "Disj2")
(elim "Disj2")
(assume "x<<=0.5")
(intro 0 (pt "SdM"))
(intro 0 (pt "RealConstr([n]2*as n+0)([p]M(PosS p))"))
(split)
(use "TwoTimesPlusIntReal")
(realproof)
(split)
;; ?^111:abs(RealConstr([n]2*as n+0)([p]M(PosS p)))<<=1
(simpreal "TwoTimesPlusEq")
(simpreal "RealPlusZero")
(simpreal "RealAbsTimes")
(simp "<-" "xDef")
(ng #t)
(simpreal (pf "RealConstr([n]1)([p]Zero)===2*RealConstr([n](1#2))([p]Zero)"))
(use "RealLeMonTimes")
(intro 0)
(use "RealRat")
(assume "p")
(ng #t)
(use "Truth")
(use "RealLeAbs")
(use "x<<=0.5")
(simpreal
 (pf "RealConstr([n](1#2))([p]Zero)=== ~ ~(RealConstr([n](1#2))([p]Zero))"))
(use "RealLeUMinus")
(use "(~1#2)<<=x")
(ng #t)
(use "RealEqRefl")
(use "RealRat")
(ng #t)
(use "RealEqRefl")
(use "RealRat")
(use "Rx")
(use "RealRat")
(autoreal)
;; ?^112:RealConstr as M===
;; (1#2)*(RealConstr([n]2*as n+0)([p]M(PosS p))+SdToInt SdM)
(simpreal "TwoTimesPlusEq")
(simp "<-" "xDef")
(ng #t)
(simpreal "RealPlusZero")
(simpreal "RealPlusZero")
(simpreal "RealTimesAssoc")
(ng #t)
(simpreal "RealOneTimes")
(use "RealEqRefl")
(autoreal)
(assume "0<=x")
(intro 0 (pt "SdR"))
(intro 0 (pt "RealConstr([n](2*as n)+ ~1)([p]M(PosS p))"))
(split)
(use "TwoTimesPlusIntReal")
(realproof)
(split)
;; ?^161:abs(RealConstr([n]2*as n+ ~1)([p]M(PosS p)))<<=1
(simpreal "TwoTimesPlusEq")
(use "RealLeAbs")
(simpreal (pf "RealConstr([n]1)([p]Zero)===
               (RealConstr([n]2)([p]Zero))*1+ ~(RealConstr([n]1)([p]Zero))"))
(use "RealLeMonPlus")
(use "RealLeMonTimes")
(intro 0)
(use "RealRat")
(assume "p")
(ng #t)
(use "Truth")
(use "RealLeTrans" (pt "abs x"))
(simp "xDef")
(use "RealLeAbsId")
(use "Rx")
(simp "xDef")
(use "abs x<=1")
(use "RealLeRefl")
(use "RealRat")
(ng #t)
(use "RealEqRefl")
(use "RealRat")
(simp "<-" "xDef")
(simpreal "RealUMinusPlus")
(ng #t)
(simpreal (pf "RealConstr([n]1)([p]Zero)===
               (RealConstr([n]0)([p]Zero))*2+ (RealConstr([n]1)([p]Zero))"))
(use "RealLeMonPlus")
(simpreal "RealTimesComm")
(simpreal "<-" "RealTimesUMinusId")
(use "RealLeMonTimesL")
(intro 0)
(use "RealRat")
(assume "p")
(ng #t)
(use "Truth")
(simpreal (pf "RealConstr([n]0)([p]Zero)=== ~ ~(RealConstr([n]0)([p]Zero))"))
(use "RealLeUMinus")
(ng #t)
(use "0<=x")
(ng #t)
(use "RealEqRefl")
(autoreal)
(ng #t)
(use "RealLeRefl")
(use "RealRat")
(ng #t)
(use "RealEqRefl")
(use "RealRat")
(use "RealRat")
(realproof)
(use "Rx")
;; ?^162:RealConstr as M===
;;       (1#2)*(RealConstr([n]2*as n+ ~1)([p]M(PosS p))+SdToInt SdR)
(simpreal "TwoTimesPlusEq")
(simp "<-" "xDef")
(ng #t)
(simpreal "<-" "RealPlusAssoc")
(ng #t)
(simpreal "RealPlusZero")
(simpreal "RealTimesAssoc")
(ng #t)
(simpreal "RealOneTimes")
(simp "xDef")
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "RealToCoIAux")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [x]
;;  [if x
;;    ([as,M]
;;     [if (cApproxSplitZeroMinusPtFive x)
;;       (SdL pair RealConstr([n]2*as n+1)([p]M(PosS p)))
;;       [if (cApproxSplitZeroPtFive x)
;;        (SdM pair RealConstr([n]2*as n)([p]M(PosS p)))
;;        (SdR pair RealConstr([n]2*as n+IntN 1)([p]M(PosS p)))]])]

;; Was before optimization (with RealTimes in 2*x and its modulus
;; involving the Archimedian property RealBd)

;; [x]
;;  [if (cApproxSplit(IntN 1#2)0 x 1)
;;    (SdL pair 2*x+1)
;;    [if (cApproxSplit 0(1#2)x 1) (SdM pair 2*x) (SdR pair 2*x+IntN 1)]]

;; SdMRSdToInt
(set-goal "allnc s(SdMR(SdToInt s)s)")
(ind)
(ng #t)
(use "InitSdSdRMR")
(ng #t)
(use "InitSdSdMMR")
(ng #t)
(use "InitSdSdLMR")
;; Proof finished.
;; (cdp)
(save "SdMRSdToInt")

;; RealToCoI
(set-goal "all x(Real x -> abs x<<=1 -> CoI x)")
(assume "x" "Rx" "xBd")
(assert "exd sd exl y(Real y andnc abs y<<=1 andnc x===(1#2)*(y+SdToInt sd))")
 (use "RealToCoIAux" (pt "x"))
 (use "Rx")
 (use "xBd")
(assume "Hyp")
(coind "Hyp")
(pp (formula-to-et-type (proof-to-formula (current-goal))))
;; sd yprod rea=>sd yprod(ai ysum sd yprod rea)
(assume "y" "ExHyp")
(by-assume "ExHyp" "s" "sProp")
(by-assume "sProp" "y0" "sy0Prop")
(assert "exd sd exl y(Real y andnc abs y<<=1 andnc y0===(1#2)*(y+SdToInt sd))")
 (use "RealToCoIAux")
 (use "sy0Prop")
 (use "sy0Prop")
(assume "y0ExHyp")
(by-assume "y0ExHyp" "s1" "s1Prop")
(by-assume "s1Prop" "y1" "s1y1Prop")
(intro 0 (pt "SdToInt s"))
(intro 0 (pt "y0"))
(intro 0 (pt "y"))
(split)
(use "SdMRElim" (pt "s"))
(use "SdMRSdToInt")
(split)
(use "sy0Prop")
(split)
(use "sy0Prop")
(split)
(intro 1)
(intro 0 (pt "s1"))
(intro 0 (pt "y1"))
(split)
(use "s1y1Prop")
(split)
(use "s1y1Prop")
(use "s1y1Prop")
(split)
(use "sy0Prop")
(simpreal "sy0Prop")
(use "RealEqRefl")
(assert "Real y0")
 (use "sy0Prop")
(assume "Ry0")
(realproof)
;; Proof finished.
;; (cdp)
(save "RealToCoI")

(define RealToCoI-eterm (proof-to-extracted-term))
(add-var-name "sx" (py "sd yprod rea"))
(define RealToCoI-neterm (rename-variables (nt RealToCoI-eterm)))
(ppc RealToCoI-neterm)

;; [x]
;;  (CoRec sd yprod rea=>ai)(cRealToCoIAux x)
;;  ([sx]
;;    [case sx
;;      (s pair x0 -> 
;;      [case (cRealToCoIAux x0) (s0 pair x1 -> s pair InR(s0 pair x1))])])

;; RatToReal
(set-goal "all a(abs a<=1 -> exl x(Real x andi abs x<<=1 andi x===a))")
(assume "a" "aBd")
(intro 0 (pt "RealConstr([n]a)([p]Zero)"))
(split)
(use "RealRat")
(split)
(use "RatLeToRealLe")
(use "aBd")
(use "RealEqRefl")
(use "RealRat")
;; Proof finished.
;; (cdp)
(save "RatToReal")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [a]a
;; ppn means pretty print with names.
(ppn neterm)
;; (lambda a ((lambda n a) RealConstr (lambda p Zero)))

;; RatToCoI
(set-goal "all a(abs a<=1 -> CoI a)")
(assume "a" "aBd")
(use "RealToCoI")
(use "RealRat")
(use "RatLeToRealLe")
(use "aBd")
;; Proof finished.
;; (cdp)
(save "RatToCoI")

(define RatToCoI-eterm (proof-to-extracted-term))
(define RatToCoI-neterm (rename-variables (nt RatToCoI-eterm)))
(pp RatToCoI-neterm)
;; [a]cRealToCoI a
(animate "RatToReal")
(animate "RealToCoI")
(animate "RealToCoIAux")
(animate "ApproxSplitZeroPtFive")
(animate "ApproxSplitZeroMinusPtFive")
(animate "ApproxSplit")
(define RatToCoI-neterm (rename-variables (nt RatToCoI-eterm)))
(ppc RatToCoI-neterm)

;; [a]
;;  (CoRec sd yprod rea=>ai)
;;  [case (a<=(IntN 1#4))
;;    (True -> SdL pair 2*a+1)
;;    (False -> 
;;    [case (a<=(1#4)) (True -> SdM pair 2*a) (False -> SdR pair 2*a+IntN 1)])]
;;  ([sx]
;;    [case sx
;;      (s pair x -> 
;;      [case x
;;        (RealConstr as M -> 
;;        [case x
;;          (RealConstr as0 M0 -> 
;;          [case (as0(M0 3)<=(IntN 1#4))
;;            (True -> 
;;            [case (SdL pair RealConstr([n]2*as n+1)([p]M(PosS p)))
;;              (s0 pair x0 -> s pair InR(s0 pair x0))])
;;            (False -> 
;;            [case x
;;              (RealConstr as1 M1 -> 
;;              [case (as1(M1 3)<=(1#4))
;;                (True -> 
;;                [case (SdM pair RealConstr([n]2*as n)([p]M(PosS p)))
;;                  (s0 pair x0 -> s pair InR(s0 pair x0))])
;;                (False -> 
;;                [case (SdR pair RealConstr([n]2*as n+IntN 1)([p]M(PosS p)))
;;                  (s0 pair x0 -> s pair InR(s0 pair x0))])])])])])])])

(deanimate "GenCoI")
(deanimate "CoIClauseInv")
(deanimate "RatToReal")
(deanimate "RealToCoI")
(deanimate "RealToCoIAux")
(deanimate "ApproxSplitZeroPtFive")
(deanimate "ApproxSplitZeroMinusPtFive")
(deanimate "ApproxSplit")

;; To check which program constants are animated evaluate
;; (display-animation)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Haskell translation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; terms-to-haskell-program (written by Fredrik Nordvall-Forsberg)
;; generates a Haskell file (here sdtest.hs).  To run it, in a
;; terminal type ghci sdtest.hs.  Then in *Main> one can evaluate
;; the Haskell functions in sdtest.hs.  To quit type *Main> :q.

;; To prepare for the Haskell translation we define program constants,
;; which will be translated into Haskell programs.

(add-program-constant "SdMs" (py "ai"))
(add-computation-rules "SdMs" "C SdM SdMs")

(add-program-constant "PtFive" (py "ai"))
(add-computation-rules "PtFive" "C SdR SdMs")

(add-program-constant "MPtFive" (py "ai"))
(add-computation-rules "MPtFive" "C SdL SdMs")

;; OneSdR n defines 1#2**Succ n

(add-program-constant "OneSdR" (py "nat=>ai"))
(add-computation-rules
 "OneSdR Zero" "C SdR SdMs"
 "OneSdR(Succ n)" "C SdM(OneSdR n)")

;; OneSdL n defines IntN 1#2**(Succ n)

(add-program-constant "OneSdL" (py "nat=>ai"))
(add-computation-rules
 "OneSdL Zero" "C SdL SdMs"
 "OneSdL(Succ n)" "C SdM(OneSdL n)")

(add-program-constant "HeronAux" (py "rat=>rat"))
(add-computation-rules "HeronAux a" "a+(2/a)")

(add-program-constant "Heron" (py "nat=>rat"))
(add-computation-rules
 "Heron Zero" "1#1"
 "Heron(Succ n)" "(1#2)*HeronAux(Heron n)")

(add-program-constant "SqrtTwoOverTwo" (py "rea"))
(add-computation-rules
 "SqrtTwoOverTwo" "RealConstr([n](Heron n/2))([p]PosS p)")

(add-program-constant "AiAppd" (py "list sd=>ai=>ai"))
(add-computation-rules
 "AiAppd(Nil sd)u" "u"
 "AiAppd(s::(list sd))u" "C s(AiAppd(list sd)u)")

(add-program-constant "Zeros" (py "nat=>list sd"))
(add-computation-rules
 "Zeros Zero" "(Nil sd)"
 "Zeros(Succ n)" "SdM::Zeros n")

;; (pp (nt (pt "Zeros 3")))
;; SdM::SdM::SdM:

(add-program-constant "OneZeros" (py "nat=>list sd"))
(add-computation-rules
 "OneZeros n" "SdR::Zeros(Succ n)")

;; (pp (nt (pt "OneZeros 3")))
;; SdR::SdM::SdM::SdM::SdM:

(add-program-constant "IrrStr" (py "(nat=>nat)=>nat=>ai"))
(add-computation-rules
 "IrrStr(nat=>nat)n" "AiAppd(OneZeros n)(IrrStr(nat=>nat)(Succ n))")

(add-program-constant "AiProj" (py "nat=>ai=>sd"))
(add-computation-rules
 "AiProj Zero(C s ai)" "s"
 "AiProj(Succ n)(C s ai)" "AiProj n ai")

(add-program-constant "AiToCs" (py "ai=>nat=>rat"))
(add-computation-rules
 "AiToCs ai Zero" "0#1"
 "AiToCs ai(Succ n)" "(AiToCs ai n)+(1#2**n*2)*SdToInt(AiProj n ai)")

(add-program-constant "AiToReal" (py "ai=>rea"))
(add-computation-rules
 "AiToReal ai" "RealConstr(AiToCs ai)([p]p)")

(add-program-constant "AiHead" (py "ai=>sd"))
(add-computation-rules "AiHead(C s u)" "s")

(add-program-constant "AiTail" (py "ai=>ai"))
(add-computation-rules "AiTail(C s u)" "u")

(add-program-constant "TakeStr" (py "nat=>ai=>list sd"))
(add-computation-rules
 "TakeStr Zero u" "(Nil sd)"
 "TakeStr(Succ n) u" "AiHead u :: (TakeStr n(AiTail u))")

(add-program-constant "ListSdToRat" (py "list sd=>rat"))
(add-computation-rules
 "ListSdToRat(Nil sd)" "0#1"
 "ListSdToRat(s::list sd)" "(1#2)*(ListSdToRat(list sd)+SdToInt s)")

;; terms-to-haskell-program requires that all auxiliary program
;; constants cThm have computation rules.  This means that all
;; c.r. theorems must be animated.

'(
(animate "RealToCoI")
(animate "RealToCoIAux")
(animate "ApproxSplitZeroMinusPtFive")
(animate "ApproxSplitZeroPtFive")
(animate "ApproxSplit")

(terms-to-haskell-program
 "~/temp/sdtest.hs"
 (list (list RealToCoI-eterm "realtocoi")
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

(deanimate "RealToCoI")
(deanimate "RealToCoIAux")
(deanimate "ApproxSplitZeroMinusPtFive")
(deanimate "ApproxSplitZeroPtFive")
(deanimate "ApproxSplit")
)

;; ghci sdtest.hs
;; takestr 18 (rattocoi (4 % 7)) 
;; [SdR,SdM,SdR,SdL,SdM,SdR,SdL,SdM,SdR,SdL,SdM,SdR,SdL,SdM,SdR,SdL,SdM,SdR]

;; listsdtorat (takestr 18 (rattocoi (4 % 7)))
;; 149797 % 262144

;; (exact->inexact 149797/262144)
;; 0.5714302062988281

;; (/ 4 7.0)
;; 0.5714285714285714

;; takestr 18 (onesdr 16)
;; [SdM,SdM,SdM,SdM,SdM,SdM,SdM,SdM,SdM,SdM,SdM,SdM,SdM,SdM,SdM,SdM,SdR,SdM]

;; takestr 10 (realtocoi stot)
;; [SdR,SdR,SdM,SdL,SdR,SdL,SdR,SdL,SdM,SdM]

;; listsdtorat (takestr 10 (realtocoi stot))
;; 181 % 256

;; (exact->inexact 181/256)
;; 0.70703125

;; (* (sqrt 2) 0.5)
;; 0.7071067811865476

;; takestr 40 (irrstr (\ n -> (n + 1)) 0)

;; SdR,SdM,
;; SdR,SdM,SdM,
;; SdR,SdM,SdM,SdM,
;; SdR,SdM,SdM,SdM,SdM,
;; SdR,SdM,SdM,SdM,SdM,SdM,
;; SdR,SdM,SdM,SdM,SdM,SdM,SdM,
;; SdR,SdM,SdM,SdM,SdM,SdM,SdM,SdM,
;; SdR,SdM,SdM,SdM,SdM...

;; takestr 40 (irrstr (\ n -> (n + 1)) 1)

;; SdR,SdM,SdM,
;; SdR,SdM,SdM,SdM,
;; SdR,SdM,SdM,SdM,SdM,
;; SdR,SdM,SdM,SdM,SdM,SdM,
;; SdR,SdM,SdM,SdM,SdM,SdM,SdM,
;; SdR,SdM,SdM,SdM,SdM,SdM,SdM,SdM,
;; SdR,SdM,SdM,SdM,SdM,SdM,SdM...
