;; 2017-12-12.  examples/analysis/sdcode.scm

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

(display "loading sdcode.scm ...") (newline)

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
(autoreal)
(use "RealNNegIntro")
(autoreal)
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
(save "CoIClosure")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; cCoIClause

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
(save "CoIUMinus")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [u](CoRec str=>str)u
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
(save "CoIClosureInv")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [s,u](CoRec sd yprod str=>str)(s pair u)([su]clft su pair InL crht su)

