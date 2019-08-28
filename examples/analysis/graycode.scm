;; 2019-08-26.  examples/analysis/graycode.scm

;; (load "~/git/minlog/init.scm")

;; (set! COMMENT-FLAG #f)
;; (libload "nat.scm")
;; (libload "list.scm")
;; (libload "str.scm")
;; (libload "pos.scm")
;; (libload "int.scm")
;; (libload "rat.scm")
;; (remove-var-name "x" "y" "z")
;; (libload "rea.scm")
;; ;; (set! COMMENT-FLAG #t)

;; (load "~/git/minlog/examples/analysis/digits.scm")
;; (load "~/git/minlog/examples/analysis/sdcode.scm")

(display "loading graycode.scm ...") (newline)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Inductive predicates G and H
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(add-algs (list "ag" "ah")
	  '("boole=>ag=>ag" "LR") ;for left/right
	  '("ah=>ag" "U") ;for undefined
	  '("boole=>ag=>ah" "Fin") ;for finally
	  '("ah=>ah" "D")) ;for delay

;; (display-alg "ag" "ah")
;; ag
;; 	LR:	boole=>ag=>ag
;; 	U:	ah=>ag
;; ah
;; 	Fin:	boole=>ag=>ah
;; 	D:	ah=>ah

(add-ids
  (list (list "G" (make-arity (py "rea")) "ag")
       (list "H" (make-arity (py "rea")) "ah"))
 '("allnc d,x,y(Psd d -> Real x -> abs x<<=1 -> G x ->
                y===(1#2)*(x+IntN 1)* ~d -> G y)" "GenLR")
 '("allnc x,y(Real x -> abs x<<=1 -> H x -> y===(1#2)*x -> G y)" "GenU")
 '("allnc d,x,y(Psd d -> Real x -> abs x<<=1 -> G x ->
                y===(1#2)*(x+1)*d -> H y)" "GenFin")
 '("allnc x,y(Real x -> abs x<<=1 -> H x -> y===(1#2)*x -> H y)" "GenD"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; General properties of G
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; We add the companion predicate CoG for G, meant to be the
;; greatest-fixed-point of the G clauses.

(add-co "G" (list "RealEq") (list "RealEq"))
;; (pp "CoGClause")

;; allnc x(
;;  CoG x -> 
;;  exr d,x0,y(
;;   Psd d andd 
;;   Real x0 andr 
;;   abs x0<<=1 andr CoG x0 andl y===(1#2)*(x0+IntN 1)* ~d andnc x===y) ord 
;;  exr x0,y(Real x0 andr abs x0<<=1 andr CoH x0 andl y===(1#2)*x0 andnc x===y))

;; (pp "CoHClause")

;; allnc x(
;;  CoH x -> 
;;  exr d,x0,y(
;;   Psd d andd Real x0 andr CoG x0 andl y===(1#2)*(x0+1)*d andnc x===y) ord 
;;  exr x0,y(Real x0 andr CoH x0 andl y===(1#2)*x0 andnc x===y))

;; By the greatest-fixed-point (or coinduction) axiom CoG is a fixed
;; point.  Hence the inverse implication holds as well.

;; CoGClauseInv
(set-goal "allnc x(
 exr d,x0,y(Psd d andd Real x0 andi abs x0<<=1 
            andr CoG x0 andl y===(1#2)*(x0+IntN 1)* ~d andnc x===y) ord 
 exr x0,y(Real x0 andi abs x0<<=1 andr CoH x0 andl
          y===(1#2)*x0 andnc x===y) -> CoG x)")
(assume "x" "Disj")
(coind
 "Disj"
 (pf "exr d,x0,y(
  Psd d andd Real x0 andi abs x0<<=1 andr CoG x0 andl
  y===(1#2)*(x0+1)*d andnc x===y) ord 
  exr x0,y(Real x0 andi abs x0<<=1 andr CoH x0 andl
           y===(1#2)*x0 andnc x===y) -> CoH x"))
;; 3,4
(drop "Disj")
(assume "x1" "x1Prop")
(elim "x1Prop")
;; 7,8
(drop "x1Prop")
;; LR initial case
(assume "ExHypLR")
(by-assume "ExHypLR" "d" "dProp")
(by-assume "dProp" "x2" "dx2Prop")
(by-assume "dx2Prop" "y2" "dx2y2Prop")
(intro 0)
(intro 0 (pt "d"))
(intro 0 (pt "x2"))
(intro 0 (pt "y2"))
(split)
(use "dx2y2Prop")
(split)
(use "dx2y2Prop")
(split)
(use "dx2y2Prop")
(split)
(intro 0)
(use "dx2y2Prop")
(use "dx2y2Prop")
;; 8
(drop "x1Prop")
;; generating case
(assume "ExHypU")
(by-assume "ExHypU" "x2" "x2Prop")
(by-assume "x2Prop" "y2" "x2y2Prop")
(intro 1)
(intro 0 (pt "x2"))
(intro 0 (pt "y2"))
(split)
(use "x2y2Prop")
(split)
(use "x2y2Prop")
(split)
(intro 0)
(use "x2y2Prop")
(use "x2y2Prop")
;; 4
(drop "Disj")
(assume "x1" "x1Prop")
(elim "x1Prop")
;; 49,50
(drop "x1Prop")
;; LR
(assume "ExHypLR")
(by-assume "ExHypLR" "d" "dProp")
(by-assume "dProp" "x2" "x2dProp")
(by-assume "x2dProp" "y2" "x2dy2Prop")
(intro 0)
(intro 0 (pt "d"))
(intro 0 (pt "x2"))
(intro 0 (pt "y2"))
(split)
(use "x2dy2Prop")
(split)
(use "x2dy2Prop")
(split)
(use "x2dy2Prop")
(split)
(intro 0)
(use "x2dy2Prop")
(use "x2dy2Prop")
;; 50
(drop "x1Prop")
;; SdM
(assume "ExHypD")
(by-assume "ExHypD" "x2" "x2Prop")
(by-assume "x2Prop" "y2" "x2y2Prop")
(intro 1)
(intro 0 (pt "x2"))
(intro 0 (pt "y2"))
(split)
(use "x2y2Prop")
(split)
(use "x2y2Prop")
(split)
(intro 0)
(use "x2y2Prop")
(use "x2y2Prop")
;; Proof finished.
;; (cdp)
(save "CoGClauseInv")

(define eterm (proof-to-extracted-term))
(add-var-name "bgh" (py "boole yprod ag ysum ah"))
(add-var-name "bg" (py "boole yprod ag"))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [bgh]
;;  (CoRec boole yprod ag ysum ah=>ag boole yprod ag ysum ah=>ah)bgh
;;  ([bgh0]
;;    [case bgh0
;;      (InL bg -> InL(clft bg pair InL crht bg))
;;      (InR ah -> InR(InL ah))])
;;  ([bgh0]
;;    [case bgh0
;;      (InL bg -> InL(clft bg pair InL crht bg))
;;      (InR ah -> InR(InL ah))])

;; CoHClauseInv
(set-goal "allnc x(
 exr d,x0,y(
  Psd d andd Real x0 andi abs x0<<=1 andr CoG x0 andl
  y===(1#2)*(x0+1)*d andnc x===y) ord 
 exr x0,y(Real x0 andi abs x0<<=1 andr CoH x0 andl
 y===(1#2)*x0 andnc x===y) ->  CoH x)")
(assume "x" "Disj")
(coind
 "Disj"
 (pf "exr d,x0,y(Psd d andd Real x0 andi abs x0<<=1 andr
  CoG x0 andl y===(1#2)*(x0+IntN 1)* ~d andnc x===y) ord 
 exr x0,y(Real x0 andi abs x0<<=1 andr CoH x0 andl
 y===(1#2)*x0 andnc x===y) -> CoG x"))
;; 3,4
(drop "Disj")
(assume "x1" "x1Prop")
(elim "x1Prop")
;; 7,8
(drop "x1Prop")
;; LR initial case
(assume "ExHypLR")
(by-assume "ExHypLR" "d" "dProp")
(by-assume "dProp" "x2" "dx2Prop")
(by-assume "dx2Prop" "y2" "dx2y2Prop")
(intro 0)
(intro 0 (pt "d"))
(intro 0 (pt "x2"))
(intro 0 (pt "y2"))
(split)
(use "dx2y2Prop")
(split)
(use "dx2y2Prop")
(split)
(use "dx2y2Prop")
(split)
(intro 0)
(use "dx2y2Prop")
(use "dx2y2Prop")
;; 8
(drop "x1Prop")
;; generating case
(assume "ExHypU")
(by-assume "ExHypU" "x2" "x2Prop")
(by-assume "x2Prop" "y2" "x2y2Prop")
(intro 1)
(intro 0 (pt "x2"))
(intro 0 (pt "y2"))
(split)
(use "x2y2Prop")
(split)
(use "x2y2Prop")
(split)
(intro 0)
(use "x2y2Prop")
(use "x2y2Prop")
;; 4
(drop "Disj")
(assume "x1" "x1Prop")
(elim "x1Prop")
;; 53,54
(drop "x1Prop")
;; LR
(assume "ExHypLR")
(by-assume "ExHypLR" "d" "dProp")
(by-assume "dProp" "x2" "x2dProp")
(by-assume "x2dProp" "y2" "x2dy2Prop")
(intro 0)
(intro 0 (pt "d"))
(intro 0 (pt "x2"))
(intro 0 (pt "y2"))
(split)
(use "x2dy2Prop")
(split)
(use "x2dy2Prop")
(split)
(use "x2dy2Prop")
(split)
(intro 0)
(use "x2dy2Prop")
(use "x2dy2Prop")
;; 54
(drop "x1Prop")
;; Mid
(assume "ExHypD")
(by-assume "ExHypD" "x2" "x2Prop")
(by-assume "x2Prop" "y2" "x2y2Prop")
(intro 1)
(intro 0 (pt "x2"))
(intro 0 (pt "y2"))
(split)
(use "x2y2Prop")
(split)
(use "x2y2Prop")
(split)
(intro 0)
(use "x2y2Prop")
(use "x2y2Prop")
;; Proof finished.
;; (cdp)
(save "CoHClauseInv")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [bgh]
;;  (CoRec boole yprod ag ysum ah=>ah boole yprod ag ysum ah=>ag)bgh
;;  ([bgh0]
;;    [case bgh0
;;      (InL bg -> InL(clft bg pair InL crht bg))
;;      (InR ah -> InR(InL ah))])
;;  ([bgh0]
;;    [case bgh0
;;      (InL bg -> InL(clft bg pair InL crht bg))
;;      (InR ah -> InR(InL ah))])

;; CoGCompat
(set-goal "allnc x,y(x===y -> CoG x -> CoG y)")
(assume "x" "y" "x===y" "CoGx")
(inst-with-to "CoGClause" (pt "x") "CoGx" "CoGClauseInst")
(elim "CoGClauseInst")
(drop "CoGClauseInst")
;; LR case
(assume "ExHyp")
(by-assume "ExHyp" "d" "dProp")
(by-assume "dProp" "x1" "dx1Prop")
(by-assume "dx1Prop" "y1" "dx1y1Prop")
(use "CoGClauseInv")
(intro 0)
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
(use "RealEqTrans" (pt "x"))
(use "RealEqSym")
(use "x===y")
(use "dx1y1Prop")
(drop "CoGClauseInst")
;; U case
(assume "ExHyp")
(use "CoGClauseInv")
(intro 1)
(by-assume "ExHyp" "x1" "x1Prop")
(by-assume "x1Prop" "y1" "x1y1Prop")
(intro 0 (pt "x1"))
(intro 0 (pt "y1"))
(split)
(use "x1y1Prop")
(split)
(use "x1y1Prop")
(split)
(use "x1y1Prop")
(split)
(use "x1y1Prop")
(use "RealEqTrans" (pt "x"))
(use "RealEqSym")
(use "x===y")
(use "x1y1Prop")
;; Proof finished.
;; (cdp)
(save "CoGCompat")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [ag][case (DesYprod ag)
;;    (InL bg -> cCoGClauseInv(InL bg))
;;    (InR ah -> cCoGClauseInv(InR ah))]

(animate "CoGClauseInv")

(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [ag]
;;  [case (DesYprod ag)
;;    (InL bg -> 
;;    (CoRec boole yprod ag ysum ah=>ag boole yprod ag ysum ah=>ah)(InL bg)
;;    ([bgh]
;;      [case bgh
;;        (InL bg0 -> InL(clft bg0 pair InL crht bg0))
;;        (InR ah -> InR(InL ah))])
;;    ([bgh]
;;      [case bgh
;;        (InL bg0 -> InL(clft bg0 pair InL crht bg0))
;;        (InR ah -> InR(InL ah))]))
;;    (InR ah -> 
;;    (CoRec boole yprod ag ysum ah=>ag boole yprod ag ysum ah=>ah)(InR ah)
;;    ([bgh]
;;      [case bgh
;;        (InL bg -> InL(clft bg pair InL crht bg))
;;        (InR ah0 -> InR(InL ah0))])
;;    ([bgh]
;;      [case bgh
;;        (InL bg -> InL(clft bg pair InL crht bg))
;;        (InR ah0 -> InR(InL ah0))]))]

(define nneterm (rename-variables (nt (undelay-delayed-corec neterm 1))))
;; (pp (rename-variables nneterm))

;; [ag][if (DesYprod ag) ([bg]LR clft bg crht bg) U]

;; (ppc (rename-variables nneterm))

;; [ag][case (DesYprod ag) (InL bg -> LR clft bg crht bg) (InR ah -> U ah)]

;; This is the identity on CoG

(deanimate "CoGClauseInv")

;; CoHCompat
(set-goal "allnc x,y(x===y -> CoH x -> CoH y)")
(assume "x" "y" "x=y" "CoHx")
(inst-with-to "CoHClause" (pt "x") "CoHx" "CoHClauseInst")
(elim "CoHClauseInst")
(drop "CoHClauseInst")
;; LR case
(assume "ExHyp")
(by-assume "ExHyp" "d" "dProp")
(by-assume "dProp" "x1" "dx1Prop")
(by-assume "dx1Prop" "y1" "dx1y1Prop")
(use "CoHClauseInv")
(intro 0)
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
(use "RealEqTrans" (pt "x"))
(use "RealEqSym")
(use "x=y")
(use "dx1y1Prop")
(drop "CoHClauseInst")
;; U case
(assume "ExHyp")
(use "CoHClauseInv")
(intro 1)
(by-assume "ExHyp" "x1" "x1Prop")
(by-assume "x1Prop" "y1" "x1y1Prop")
(intro 0 (pt "x1"))
(intro 0 (pt "y1"))
(split)
(use "x1y1Prop")
(split)
(use "x1y1Prop")
(split)
(use "x1y1Prop")
(split)
(use "x1y1Prop")
(use "RealEqTrans" (pt "x"))
(use "RealEqSym")
(use "x=y")
(use "x1y1Prop")
;; Proof finished.
;; (cdp)
(save "CoHCompat")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [ah]
;;  [case (DesYprod ah)
;;    (InL bg -> cCoHClauseInv(InL bg))
;;    (InR ah0 -> cCoHClauseInv(InR ah0))]

(animate "CoHClauseInv")

(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [ah]
;;  [case (DesYprod ah)
;;    (InL bg -> 
;;    (CoRec boole yprod ag ysum ah=>ah boole yprod ag ysum ah=>ag)(InL bg)
;;    ([bgh]
;;      [case bgh
;;        (InL bg0 -> InL(clft bg0 pair InL crht bg0))
;;        (InR ah0 -> InR(InL ah0))])
;;    ([bgh]
;;      [case bgh
;;        (InL bg0 -> InL(clft bg0 pair InL crht bg0))
;;        (InR ah0 -> InR(InL ah0))]))
;;    (InR ah0 -> 
;;    (CoRec boole yprod ag ysum ah=>ah boole yprod ag ysum ah=>ag)(InR ah0)
;;    ([bgh]
;;      [case bgh
;;        (InL bg -> InL(clft bg pair InL crht bg))
;;        (InR ah1 -> InR(InL ah1))])
;;    ([bgh]
;;      [case bgh
;;        (InL bg -> InL(clft bg pair InL crht bg))
;;        (InR ah1 -> InR(InL ah1))]))]

(define nneterm (rename-variables (nt (undelay-delayed-corec neterm 1))))
;; (pp (rename-variables nneterm))

;; [ah][if (DesYprod ah) ([bg]Fin clft bg crht bg) D]

;; (ppc (rename-variables nneterm))

;; [ah][case (DesYprod ah) (InL bg -> Fin clft bg crht bg) (InR ah -> D ah)]

;; This is the identity on CoH

(deanimate "CoHClauseInv")

;; CoGToReal
(set-goal "all x(CoG x -> Real x)")
(assume "x" "CoGx")
(inst-with-to "CoGClause" (pt "x") "CoGx" "CoGClauseInst")
(elim "CoGClauseInst")
(drop "CoGClauseInst")
;; LR case
(assume "ExHyp")
(by-assume "ExHyp" "d" "dProp")
(by-assume "dProp" "x1" "dx1Prop")
(by-assume "dx1Prop" "y" "dx1yProp")
(use "RealEqElim0" (pt "y"))
(use "dx1yProp")
;; U case
(drop "CoGClauseInst")
(assume "ExHyp")
(by-assume "ExHyp" "x1" "x1Prop")
(by-assume "x1Prop" "y" "x1yProp")
(use "RealEqElim0" (pt "y"))
(use "x1yProp")
;; Proof finished.
;; (cdp)
(save "CoGToReal")

;; CoHToReal
(set-goal "all x(CoH x -> Real x)")
(assume "x" "CoHx")
(inst-with-to "CoHClause" (pt "x") "CoHx" "CoHClauseInst")
(elim "CoHClauseInst")
(drop "CoHClauseInst")
;; LR case
(assume "ExHyp")
(by-assume "ExHyp" "d" "dProp")
(by-assume "dProp" "x1" "dx1Prop")
(by-assume "dx1Prop" "y" "dx1yProp")
(use "RealEqElim0" (pt "y"))
(use "dx1yProp")
;; U case
(drop "CoHClauseInst")
(assume "ExHyp")
(by-assume "ExHyp" "x1" "x1Prop")
(by-assume "x1Prop" "y" "x1yProp")
(use "RealEqElim0" (pt "y"))
(use "x1yProp")
;; Proof finished.
;; (cdp)
(save "CoHToReal")

;; CoGToBd
(set-goal "all x(CoG x -> abs x<<=1)")
(assume "x" "CoGx")
(inst-with-to "CoGClause" (pt "x") "CoGx" "CoGClauseInst")
(elim "CoGClauseInst")
;; 5,6
(drop "CoGClauseInst")
;; LR case
(assume "ExHyp")
(by-assume "ExHyp" "d" "dProp")
(by-assume "dProp" "x1" "dx1Prop")
(by-assume "dx1Prop" "y" "dx1yProp")
(simpreal "dx1yProp")
(simpreal "dx1yProp")
(assert "Real x1")
(use "dx1yProp")
(assume "Rx1")
(simpreal "RealAbsTimes")
(simpreal "RealAbsTimes")
(simpreal (pf "RealConstr([n](1#1))([p]Zero)===
               abs(RealConstr([n](1#2))([p]Zero))*
               abs(RealConstr([n](1#1))([p]Zero)+1)*
               abs(RealConstr([n]~d)([p]Zero))"))
(use "RealLeMonTimesTwo")
(simpreal "<-" "RealAbsTimes")
(use "RealNNegAbs")
(autoreal)
(use "RealNNegAbs")
(use "RealRat")
(use "RealLeMonTimesTwo")
(use "RealNNegAbs")
(use "RealRat")
(use "RealNNegAbs")
(autoreal)
(use "RealLeRefl")
(use "RealRat")
;; ?^43:abs(x1+IntN 1)<<=abs(RealPlus 1 1) from abs x1<<=1
(use "RealLeTrans" (pt "abs x1+abs(RealConstr([n](IntN 1#1))([p]Zero))"))
(use "RealLeAbsPlus")
(use "Rx1")
(use "RealRat")
(use "RealLeTrans" (pt "RealConstr([n](1#1))([p]Zero)+1"))
(use "RealLeMonPlus")
(use "dx1yProp")
(ng #t)
(use "RealLeRefl")
(use "RealRat")
(use "RealLeAbsId")
(autoreal)
(use "RealLeRefl")
(autoreal)
;; ?^30:1===abs(1#2)*abs(RealPlus 1 1)*abs~d
(ng #t)
(use "RealSeqEqToEq" (pt "Zero"))
(use "RealRat")
(autoreal)
(assume "n" "Useless")
(ng #t)
(simp "PsdToAbsOne")
(use "Truth")
(use "dx1yProp")
(autoreal)
;; ?^6:exr x0,y(
;;      Real x0 andr abs x0<<=1 andr CoH x0 andl y===(1#2)*x0 andnc x===y) -> 
;;     abs x<<=1
(drop "CoGClauseInst")
;; U case
(assume "ExHyp")
(by-assume "ExHyp" "x1" "x1Prop")
(by-assume "x1Prop" "y" "x1yProp")
(simpreal "x1yProp")
(simpreal "x1yProp")
(assert "Real x1")
(use "x1yProp")
(assume "Rx1")
(simpreal "RealAbsTimes")
(simpreal (pf "RealConstr([n](1#1))([p]Zero)===
               abs(RealConstr([n](1#2))([p]Zero))*
               abs(RealConstr([n](1#1))([p]Zero)+1)"))
(use "RealLeMonTimesTwo")
(use "RealNNegAbs")
(use "RealRat")
(use "RealNNegAbs")
(use "Rx1")
(use "RealLeRefl")
(autoreal)
(use "RealLeTrans" (pt "RealConstr([n](1#1))([p]Zero)"))
(use "x1yProp")
(ng #t)
(use "RatLeToRealLe")
(use "Truth")
(ng #t)
(use "RealEqRefl")
(use "RealRat")
(use "Rx1")
(use "RealRat")
;; Proof finished.
;; (cdp)
(save "CoGToBd")

;; (ppn "RealLeAbsPlus")
;; (ppn (goal-to-formula (current-goal)))

;; CoHToBd
(set-goal "all x(CoH x -> abs x<<=1)")
(assume "x" "CoHx")
(inst-with-to "CoHClause" (pt "x") "CoHx" "CoHClauseInst")
(elim "CoHClauseInst")
;; 5,6
(drop "CoHClauseInst")
;; LR case
(assume "ExHyp")
(by-assume "ExHyp" "d" "dProp")
(by-assume "dProp" "x1" "dx1Prop")
(by-assume "dx1Prop" "y" "dx1yProp")
(simpreal "dx1yProp")
(simpreal "dx1yProp")
(assert "Real x1")
 (use "dx1yProp")
(assume "Rx1")
(simpreal "RealAbsTimes")
(simpreal "RealAbsTimes")
(use "RealLeTrans" (pt "abs(RealConstr([n](1#2))([p]Zero))*
                        abs(RealConstr([n](1#1))([p]Zero)+1)*
                        abs(RealConstr([n](d#1))([p]Zero))"))
(use "RealLeMonTimesL")
(use "RealNNegAbs")
(use "RealRat")
(use "RealLeMonTimes")
(use "RealNNegAbs")
(use "RealRat")
;; ?^35:abs(x1+1)<<=abs(RealPlus 1 1) from abs x1<<=1
(use "RealLeTrans" (pt "abs x1+abs(RealConstr([n](1#1))([p]Zero))"))
(use "RealLeAbsPlus")
(use "Rx1")
(use "RealRat")
(use "RealLeTrans" (pt "RealConstr([n](1#1))([p]Zero)+1"))
(use "RealLeMonPlus")
(use "dx1yProp")
(ng #t)
(use "RealLeRefl")
(use "RealRat")
(use "RealLeAbsId")
(autoreal)
(ng #t)
(simp "PsdToAbsOne")
(use "RealLeRefl")
(use "RealRat")
(use "dx1yProp")
(autoreal)
;; ?^6:exr x0,y(
;;      Real x0 andr abs x0<<=1 andr CoH x0 andl y===(1#2)*x0 andnc x===y) -> 
;;     abs x<<=1
(drop "CoHClauseInst")
;; U case
(assume "ExHyp")
(by-assume "ExHyp" "x1" "x1Prop")
(by-assume "x1Prop" "y" "x1yProp")
(simpreal "x1yProp")
(simpreal "x1yProp")
(assert "Real x1")
 (use "x1yProp")
(assume "Rx1")
(simpreal "RealAbsTimes")
(simpreal (pf "RealConstr([n](1#1))([p]Zero)===
               abs(RealConstr([n](1#2))([p]Zero))*
               abs(RealConstr([n](1#1))([p]Zero)+1)"))
(use "RealLeMonTimesTwo")
(use "RealNNegAbs")
(use "RealRat")
(use "RealNNegAbs")
(use "Rx1")
(use "RealLeRefl")
(autoreal)
(use "RealLeTrans" (pt "RealConstr([n](1#1))([p]Zero)"))
(use "x1yProp")
(ng #t)
(use "RatLeToRealLe")
(use "Truth")
(ng #t)
(use "RealEqRefl")
(use "RealRat")
(use "Rx1")
(use "RealRat")
;; Proof finished.
;; (cdp)
(save "CoHToBd")

;; We provide a simplified variant of CoGClause.

;; CoGClosure
(set-goal "allnc x(CoG x ->
 exr d,x1(Psd d andd CoG x1 andl x===(1#2)*(x1+IntN 1)* ~d) ord 
 exr x1(CoH x1 andl x===(1#2)*x1))")
(assume "x" "CoGx")
(inst-with-to "CoGClause" (pt "x") "CoGx" "CoGClauseInst")
(elim "CoGClauseInst")
(drop "CoGClauseInst")
;; LRCase
(assume "ExHyp")
(intro 0)
(by-assume "ExHyp" "d" "dProp")
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
;; U Case
(drop "CoGClauseInst")
(assume "ExHyp")
(intro 1)
(by-assume "ExHyp" "x1" "x1Prop")
(by-assume "x1Prop" "y" "x1yProp")
(intro 0 (pt "x1"))
(split)
(use "x1yProp")
(use "RealEqTrans" (pt "y"))
(use "x1yProp")
(use "x1yProp")
;; Proof finished.
;; (cdp)
(save "CoGClosure")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [ag][case (DesYprod ag) (InL bg -> InL bg) (InR ah -> InR ah)]

;; (pp neterm)

;; [ag][if (DesYprod ag) (InL (boole yprod ag) ah) (InR ah (boole yprod ag))]

;; (pp (term-to-type (pt "(InL (boole yprod ag) ah)")))
;; boole yprod ag=>boole yprod ag ysum ah
;; (pp (term-to-type (pt "(InR ah (boole yprod ag))")))
;; ah=>boole yprod ag ysum ah

;; CoHClosure
(set-goal "allnc x(CoH x ->
 exr d,x1(Psd d andd CoG x1 andl x===(1#2)*(x1+1)*d) ord 
 exr x1(CoH x1 andl x===(1#2)*x1))")
(assume "x" "CoHx")
(inst-with-to "CoHClause" (pt "x") "CoHx" "CoHClauseInst")
(elim "CoHClauseInst")
(drop "CoHClauseInst")
;; LRCase
(assume "ExHyp")
(intro 0)
(by-assume "ExHyp" "d" "dProp")
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
;; U Case
(drop "CoHClauseInst")
(assume "ExHyp")
(intro 1)
(by-assume "ExHyp" "x1" "x1Prop")
(by-assume "x1Prop" "y" "x1yProp")
(intro 0 (pt "x1"))
(split)
(use "x1yProp")
(use "RealEqTrans" (pt "y"))
(use "x1yProp")
(use "x1yProp")
;; Proof finished.
;; (cdp)
(save "CoHClosure")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [ah][case (DesYprod ah) (InL bg -> InL bg) (InR ah -> InR ah)]

;; (pp neterm)

;; [ah][if (DesYprod ah) (InL (boole yprod ag) ah) (InR ah (boole yprod ag))]

;; (pp (term-to-type (pt "(InL (boole yprod ag) ah)")))
;; boole yprod ag=>boole yprod ag ysum ah
;; (pp (term-to-type (pt "(InR ah (boole yprod ag))")))
;; ah=>boole yprod ag ysum ah

;; CoGLr
(set-goal "allnc d,x(Psd d -> CoG x -> CoG((1#2)*(x+IntN 1)* ~d))")
(assume "d" "x" "Psdd" "CoGx")
(use "CoGClauseInv")
(intro 0)
(intro 0 (pt "d"))
(intro 0 (pt "x"))
(intro 0 (pt "(1#2)*(x+IntN 1)* ~d"))
(split)
(use "Psdd")
(split)
(autoreal)
(split)
(use "CoGToBd")
(use "CoGx")
(split)
(use "CoGx")
(split)
(use "RealEqRefl")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "CoGLr")

(define eterm (proof-to-extracted-term))
(animate "CoGClauseInv")
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [boole,ag](CoRec boole yprod ag ysum ah=>ag boole yprod ag ysum ah=>ah)
;;  (InL(boole pair ag))
;;  ([bgh][case bgh
;;      (InL bg -> InL(clft bg pair InL crht bg))
;;      (InR ah -> InR(InL ah))])
;;  ([bgh][case bgh
;;      (InL bg -> InL(clft bg pair InL crht bg))
;;      (InR ah -> InR(InL ah))])

(deanimate "CoGClauseInv")

;; CoGU
(set-goal "allnc x(CoH x -> CoG((1#2)*x))")
(assume "x" "CoHx")
(use "CoGClauseInv")
(intro 1)
(intro 0 (pt "x"))
(intro 0 (pt "(1#2)*x"))
(split)
(autoreal)
(split)
(use "CoHToBd")
(use "CoHx")
(split)
(use "CoHx")
(split)
(use "RealEqRefl")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "CoGU")

(define eterm (proof-to-extracted-term))
(animate "CoGClauseInv")
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [ah](CoRec boole yprod ag ysum ah=>ag boole yprod ag ysum ah=>ah)(InR ah)
;;  ([bgh][case bgh
;;      (InL bg -> InL(clft bg pair InL crht bg))
;;      (InR ah0 -> InR(InL ah0))])
;;  ([bgh][case bgh
;;      (InL bg -> InL(clft bg pair InL crht bg))
;;      (InR ah0 -> InR(InL ah0))])

(deanimate "CoGClauseInv")

;; CoHLr
(set-goal "allnc d,x(Psd d -> CoG x -> CoH((1#2)*(x+1)*d))")
(assume "d" "x" "Psdd" "CoGx")
(use "CoHClauseInv")
(intro 0)
(intro 0 (pt "d"))
(intro 0 (pt "x"))
(intro 0 (pt "(1#2)*(x+1)*d"))
(split)
(use "Psdd")
(split)
(autoreal)
(split)
(use "CoGToBd")
(use "CoGx")
(split)
(use "CoGx")
(split)
(use "RealEqRefl")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "CoHLr")

(define eterm (proof-to-extracted-term))
(animate "CoHClauseInv")
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [boole,ag](CoRec boole yprod ag ysum ah=>ah boole yprod ag ysum ah=>ag)
;;  (InL(boole pair ag))
;;  ([bgh][case bgh
;;      (InL bg -> InL(clft bg pair InL crht bg))
;;      (InR ah -> InR(InL ah))])
;;  ([bgh][case bgh
;;      (InL bg -> InL(clft bg pair InL crht bg))
;;      (InR ah -> InR(InL ah))])

(deanimate "CoHClauseInv")

;; CoHU
(set-goal "allnc x(CoH x -> CoH((1#2)*x))")
(assume "x" "CoHx")
(use "CoHClauseInv")
(intro 1)
(intro 0 (pt "x"))
(intro 0 (pt "(1#2)*x"))
(split)
(autoreal)
(split)
(use "CoHToBd")
(use "CoHx")
(split)
(use "CoHx")
(split)
(use "RealEqRefl")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "CoHU")

(define eterm (proof-to-extracted-term))
(animate "CoHClauseInv")
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [ah](CoRec boole yprod ag ysum ah=>ah boole yprod ag ysum ah=>ag)(InR ah)
;;  ([bgh][case bgh
;;      (InL bg -> InL(clft bg pair InL crht bg))
;;      (InR ah0 -> InR(InL ah0))])
;;  ([bgh][case bgh
;;      (InL bg -> InL(clft bg pair InL crht bg))
;;      (InR ah0 -> InR(InL ah0))])

(deanimate "CoHClauseInv")

;; For CoGUMinus we use the fact that our coinductive definitions are
;; in strengthened form.

;; CoGUMinus
(set-goal "allnc x(CoG(~x) -> CoG x)")
(assume "x" "CoG-x")
(coind "CoG-x" (pf "CoH(~x) -> CoH x"))
(assume "x1" "CoG-x1")
(inst-with-to "CoGClosure" (pt "~x1") "CoG-x1" "Disj")
(elim "Disj")
(drop "Disj")
;; LR generating case
(assume "ExHyp")
(by-assume "ExHyp" "d" "dProp")
(by-assume "dProp" "x2" "dx2Prop")
(elim "dx2Prop")
(drop "dx2Prop")
(assume "Psdd" "Conj")
(elim "Conj")
(drop "Conj")
(assume "CoGx2" "EqHyp")
(intro 0)
(intro 0 (pt "~d"))
(intro 0 (pt "x2"))
(intro 0 (pt "x1"))
(split)
(use "PsdUMinus")
(use "Psdd")
(split)
(autoreal)
(split)
(use "CoGToBd")
(use "CoGx2")
(split)
(intro 0)
(use "CoGx2")
(split)
;; ?^39:x1===(1#2)*(x2+IntN 1)* ~ ~d
(use "RealEqTrans" (pt "~ ~x1"))
(use "RealEqSym")
(use "RealUMinusUMinus")
(use "RealUMinusRealInv")
(autoreal)
(use "RealEqTrans" (pt "~((1#2)*(x2+IntN 1)* ~d)"))
(use "RealUMinusCompat")
(use "EqHyp")
(use "RealEqSym")
(use "RealTimesIdRatUMinus")
(autoreal)
(use "RealEqRefl")
(use "RealUMinusRealInv")
(autoreal)
;; 9
;; U case
(drop "Disj")
(assume "ExHyp")
(by-assume "ExHyp" "x2" "x2Prop")
(elim "x2Prop")
(drop "x2Prop")
(assume "CoHx2" "EqHyp")
(intro 1)
(intro 0 (pt "~x2"))
(intro 0 (pt "x1"))
(split)
(autoreal)
(split)
(simpreal "RealAbsUMinus")
(use "CoHToBd")
(use "CoHx2")
(autoreal)
(split)
(intro 1)
;; ?_73:CoH(~ ~x2)
(use "CoHCompat" (pt "x2"))
(use "RealEqSym")
(use "RealUMinusUMinus")
(autoreal)
(use "CoHx2")
(split)
;; ?^78:x1===(1#2)* ~x2
(use "RealEqTrans" (pt "~ ~x1"))
(use "RealEqSym")
(use "RealUMinusUMinus")
(use "RealUMinusRealInv")
(autoreal)
(simpreal "EqHyp")
(use "RealEqSym")
(use "RealTimesIdUMinus")
(use "RealRat")
(autoreal)
(use "RealEqRefl")
(use "RealUMinusRealInv")
(autoreal)
;; 4
(assume "x1" "CoH-x1")
(inst-with-to "CoHClosure" (pt "~x1") "CoH-x1" "Disj")
(elim "Disj")
;; 94,95
(drop "Disj")
;; LR case
(assume "ExHyp")
(by-assume "ExHyp" "d" "dProp")
(by-assume "dProp" "x2" "dx2Prop")
(elim "dx2Prop")
(drop "dx2Prop")
(assume "Psdd" "Conj")
(elim "Conj")
(drop "Conj")
(assume "CoGx2" "EqHyp")
(intro 0)
(intro 0 (pt "~d"))
(intro 0 (pt "x2"))
(intro 0 (pt "x1"))
(split)
(use "PsdUMinus")
(use "Psdd")
(split)
(autoreal)
(split)
(use "CoGToBd")
(use "CoGx2")
(split)
(intro 0)
(use "CoGx2")
(split)
;; ?^125:x1===(1#2)*(x2+1)* ~d
(use "RealEqTrans" (pt "~ ~x1"))
(use "RealEqSym")
(use "RealUMinusUMinus")
(use "RealUMinusRealInv")
(autoreal)
(simpreal "EqHyp")
(use "RealEqSym")
(use "RealTimesIdRatUMinus")
(autoreal)
(use "RealEqRefl")
(use "RealUMinusRealInv")
(autoreal)
;; U case
(drop "Disj")
(assume "ExHyp")
(by-assume "ExHyp" "x2" "x2Prop")
(elim "x2Prop")
(drop "x2Prop")
(assume "CoHx2" "EqHyp")
(intro 1)
(intro 0 (pt "~x2"))
(intro 0 (pt "x1"))
(split)
(use "RealUMinusReal")
(autoreal)
(split)
(simpreal "RealAbsUMinus")
(use "CoHToBd")
(use "CoHx2")
(autoreal)
(split)
(intro 1)
(use "CoHCompat" (pt "x2"))
(use "RealEqSym")
(use "RealUMinusUMinus")
(autoreal)
(use "CoHx2")
(split)
(use "RealEqTrans" (pt "~ ~x1"))
(use "RealEqSym")
(use "RealUMinusUMinus")
(use "RealUMinusRealInv")
(autoreal)
(use "RealEqTrans" (pt "~((1#2)*x2)"))
(use "RealUMinusCompat")
(use "EqHyp")
(use "RealEqSym")
(use "RealTimesIdUMinus")
(use "RealRat")
(autoreal)
(use "RealEqRefl")
(use "RealUMinusRealInv")
(autoreal)
;; Proof finished.
;; (cdp)
(save "CoGUMinus")

(define eterm (proof-to-extracted-term))
(animate "CoGClosure")
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [ag](CoRec ag=>ag ah=>ah)ag
;;  ([ag0][case (DesYprod ag0)
;;      (InL bg -> [case bg (boole pair ag1 ->
;;                  InL(cPsdUMinus boole pair InL ag1))])
;;      (InR ah -> InR(InR(cCoHCompat ah)))])
;;  ([ah][case (cCoHClosure ah)
;;      (InL bg -> [case bg (boole pair ag0 ->
;;                  InL(cPsdUMinus boole pair InL ag0))])
;;      (InR ah0 -> InR(InR(cCoHCompat ah0)))])

(deanimate "CoGClosure")

;; CoGPsdTimes
(set-goal "allnc x,d(CoG x -> Psd d -> CoG(x*d))")
(assume "x" "d" "CoGx" "Psdd")
(elim "Psdd")
;; 3,4
(simpreal "RealTimesOne")
(use "CoGx")
(autoreal)
;; 4
(assert "x* IntUMinus 1=== ~x")
 (simpreal "RealTimesIdRatUMinus")
 (simpreal "RealTimesOne")
 (use "RealEqRefl")
 (autoreal)
(assume "Assertion")
(simpreal "Assertion")
(use "CoGUMinus")
(simpreal "RealUMinusUMinus")
(use "CoGx")
(autoreal)
;; Proof finished.
;; (cdp)
(save "CoGPsdTimes")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [ag,boole][if boole (cCoGCompat ag) (cCoGCompat(cCoGUMinus(cCoGCompat ag)))]

;; CoHToCoGAux
(set-goal "all d,x(Real x -> (~x+IntN 1)* ~d===(x+1)*d)")
(assert "all d,x (~x+IntN 1)* ~d=+=(x+1)*d")
(assume "d")
(cases)
(assume "as" "M")
(use "RealEqSIntro")
(assume "n")
(ng)
;; ?^9:~((~(as n)+IntN 1)*d)==(as n+1)*d
(simprat "RatTimesPlusDistrLeft")
(simprat "RatTimesPlusDistrLeft")
(ng)
(simp "IntTimesIntNL")
(use "Truth")
;; Assertion proved.
(assume "CoHToCoGAuxEqS" "d" "x" "Rx")
(use "RealEqSToEq")
(autoreal)
(use "CoHToCoGAuxEqS")
;; Proof finished.
;; (cdp)
(save "CoHToCoGAux")

;; CoHToCoG
(set-goal "allnc x(CoH x -> CoG x)")
(assume "x" "CoHx")
(coind "CoHx" (pf "CoG x -> CoH x"))
;; 3,4
(assume "x1" "CoHx1")
(inst-with-to "CoHClosure" (pt "x1") "CoHx1" "CoHClosureInst")
(elim "CoHClosureInst")
;; 8,9
(drop "CoHClosureInst")
;; left case
(assume "ExHyp")
(by-assume "ExHyp" "d" "dProp")
(by-assume "dProp" "x2" "dx2Prop")
(assert "CoG x2")
 (use "dx2Prop")
(assume "CoGx2")
(intro 0)
(intro 0 (pt "d"))
(intro 0 (pt "~x2"))
(intro 0 (pt "x1"))
(split)
(use "dx2Prop")
(split)
(autoreal)
(split)
(simpreal "RealAbsUMinus")
(use "CoGToBd")
(use "CoGx2")
(autoreal)
(split)
(intro 0)
(use "CoGUMinus")
;; ?_37:CoG(~ ~x2)
(simpreal "RealUMinusUMinus")
(use "CoGx2")
(autoreal)
(split)
;; ?^40:x1===(1#2)*(~x2+IntN 1)* ~d
(simpreal "<-" "RealTimesAssoc")
(simpreal "CoHToCoGAux")
(simpreal "RealTimesAssoc")
(use "dx2Prop")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; 9
(drop "CoHClosureInst")
;; middle case
(assume "ExHyp")
(intro 1)
(by-assume "ExHyp" "x2" "x2Prop")
(elim "x2Prop")
(drop "x2Prop")
(assume "CoHx2" "x1Def")
(intro 0 (pt "x2"))
(intro 0 (pt "x1"))
(split)
(autoreal)
(split)
(use "CoHToBd")
(use "CoHx2")
(split)
(intro 0)
(use "CoHx2")
(split)
(use "x1Def")
(use "RealEqRefl")
(autoreal)
;; 4
(assume "x1" "CoGx1")
(inst-with-to "CoGClosure" (pt "x1") "CoGx1" "CoGClosureInst")
(elim "CoGClosureInst")
;; 78,79
(drop "CoGClosureInst")
;; left case
(assume "ExHyp")
(by-assume "ExHyp" "d" "dProp")
(by-assume "dProp" "x2" "dx2Prop")
(assert "CoG x2")
 (use "dx2Prop")
(assume "CoGx2")
(intro 0)
(intro 0 (pt "d"))
(intro 0 (pt "~x2"))
(intro 0 (pt "x1"))
(split)
(use "dx2Prop")
(split)
(autoreal)
(split)
(simpreal "RealAbsUMinus")
(use "CoGToBd")
(use "CoGx2")
(autoreal)
(split)
(intro 0)
(use "CoGUMinus")
;; ?_107:CoG(~ ~x2)
(simpreal "RealUMinusUMinus")
(use "CoGx2")
(autoreal)
(split)
;; ?^110:x1===(1#2)*(~x2+1)*d
(simpreal "dx2Prop")
(simpreal "<-" "RealTimesAssoc")
(simpreal "<-" "RealTimesAssoc")
(simpreal "RealTimesPlusIntNOneDistrLeft")
(simpreal "RealTimesPlusOneDistrLeft")
(simpreal "RealTimesIdRatUMinus")
(simpreal "RealTimesUMinusId")
(use "RealEqRefl")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; 79
(drop "CoGClosureInst")
;; middle case
(assume "ExHyp")
(intro 1)
(by-assume "ExHyp" "x2" "x2Prop")
(elim "x2Prop")
(drop "x2Prop")
(assume "CoHx2" "x1Def")
(intro 0 (pt "x2"))
(intro 0 (pt "x1"))
(split)
(autoreal)
(split)
(use "CoHToBd")
(use "CoHx2")
(split)
(intro 0)
(use "CoHx2")
(split)
(use "x1Def")
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "CoHToCoG")

(define eterm (proof-to-extracted-term))
(animate "CoGClosure")
(animate "CoHClosure")
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [ah](CoRec ah=>ag ag=>ah)ah
;;  ([ah0][case (DesYprod ah0)
;;      (InL bg -> InL(clft bg pair InL(cCoGUMinus(cCoGCompat crht bg))))
;;      (InR ah1 -> InR(InL ah1))])
;;  ([ag][case (DesYprod ag)
;;      (InL bg -> InL(clft bg pair InL(cCoGUMinus(cCoGCompat crht bg))))
;;      (InR ah0 -> InR(InL ah0))])

(deanimate "CoGClosure")
(deanimate "CoHClosure")

;; CoGToCoH
(set-goal "allnc x(CoG x -> CoH x)")
(assume "x" "CoGx")
(coind "CoGx" (pf "CoH x -> CoG x"))
;; 3,4
(assume "x1" "CoHx1")
(inst-with-to "CoHClosure" (pt "x1") "CoHx1" "CoHClosureInst")
(elim "CoHClosureInst")
;; 8,9
(drop "CoHClosureInst")
;; left case
(assume "ExHyp")
(by-assume "ExHyp" "d" "dProp")
(by-assume "dProp" "x2" "dx2Prop")
(assert "CoG x2")
 (use "dx2Prop")
(assume "CoGx2")
(intro 0)
(intro 0 (pt "d"))
(intro 0 (pt "~x2"))
(intro 0 (pt "x1"))
(split)
(use "dx2Prop")
(split)
(autoreal)
(split)
(simpreal "RealAbsUMinus")
(use "CoGToBd")
(use "CoGx2")
(autoreal)
(split)
(intro 0)
(use "CoGUMinus")
;; ?_37:CoG(~ ~x2)
(simpreal "RealUMinusUMinus")
(use "CoGx2")
(autoreal)
(split)
;; ?^40:x1===(1#2)*(~x2+IntN 1)* ~d
(simpreal "<-" "RealTimesAssoc")
(simpreal "CoHToCoGAux")
(simpreal "RealTimesAssoc")
(use "dx2Prop")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; 9
(drop "CoHClosureInst")
;; middle case
(assume "ExHyp")
(intro 1)
(by-assume "ExHyp" "x2" "x2Prop")
(elim "x2Prop")
(drop "x2Prop")
(assume "CoHx2" "x1Def")
(intro 0 (pt "x2"))
(intro 0 (pt "x1"))
(split)
(autoreal)
(split)
(use "CoHToBd")
(use "CoHx2")
(split)
(intro 0)
(use "CoHx2")
(split)
(use "x1Def")
(use "RealEqRefl")
(autoreal)
;; 4
(assume "x1" "CoGx1")
(inst-with-to "CoGClosure" (pt "x1") "CoGx1" "CoGClosureInst")
(elim "CoGClosureInst")
;; 78,79
(drop "CoGClosureInst")
;; left case
(assume "ExHyp")
(by-assume "ExHyp" "d" "dProp")
(by-assume "dProp" "x2" "dx2Prop")
(assert "CoG x2")
 (use "dx2Prop")
(assume "CoGx2")
(intro 0)
(intro 0 (pt "d"))
(intro 0 (pt "~x2"))
(intro 0 (pt "x1"))
(split)
(use "dx2Prop")
(split)
(autoreal)
(split)
(simpreal "RealAbsUMinus")
(use "CoGToBd")
(use "CoGx2")
(autoreal)
(split)
(intro 0)
(use "CoGUMinus")
;; ?_107:CoG(~ ~x2)
(simpreal "RealUMinusUMinus")
(use "CoGx2")
(autoreal)
(split)
;; ?^110:x1===(1#2)*(~x2+1)*d
(simpreal "dx2Prop")
(simpreal "<-" "RealTimesAssoc")
(simpreal "<-" "RealTimesAssoc")
(simpreal "RealTimesPlusIntNOneDistrLeft")
(simpreal "RealTimesPlusOneDistrLeft")
(simpreal "RealTimesIdRatUMinus")
(simpreal "RealTimesUMinusId")
(use "RealEqRefl")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; 79
(drop "CoGClosureInst")
;; middle case
(assume "ExHyp")
(intro 1)
(by-assume "ExHyp" "x2" "x2Prop")
(elim "x2Prop")
(drop "x2Prop")
(assume "CoHx2" "x1Def")
(intro 0 (pt "x2"))
(intro 0 (pt "x1"))
(split)
(autoreal)
(split)
(use "CoHToBd")
(use "CoHx2")
(split)
(intro 0)
(use "CoHx2")
(split)
(use "x1Def")
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "CoGToCoH")

(define eterm (proof-to-extracted-term))
(animate "CoGClosure")
(animate "CoHClosure")
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [ag](CoRec ag=>ah ah=>ag)ag
;;  ([ah][case (DesYprod ah)
;;      (InL bg -> InL(clft bg pair InL(cCoGUMinus(cCoGCompat crht bg))))
;;      (InR ah0 -> InR(InL ah0))])
;;  ([ag0][case (DesYprod ag0)
;;      (InL bg -> InL(clft bg pair InL(cCoGUMinus(cCoGCompat crht bg))))
;;      (InR ah -> InR(InL ah))])

(deanimate "CoGClosure")
(deanimate "CoHClosure")

;; Here ends the original file examples/analysis/graycode.scm
;; Additions for use in the Haskell translation.

;; CoGClosureInv
(set-goal "allnc x(
 exr d,x0(Psd d andd CoG x0 andl x===(1#2)*(x0+IntN 1)* ~d) ord 
 exr x0(CoH x0 andl x===(1#2)*x0) -> CoG x)")
(assume "x" "Disj")
(use "CoGClauseInv")
(elim "Disj")
;; 4,5
(drop "Disj")
(assume "ExHyp")
(by-assume "ExHyp" "d" "dProp")
(by-assume "dProp" "x1" "dx1Prop")
(intro 0)
(intro 0 (pt "d"))
(intro 0 (pt "x1"))
(intro 0 (pt "x"))
(split)
(use "dx1Prop")
(split)
(use "CoGToReal")
(use "dx1Prop")
(split)
(use "CoGToBd")
(use "dx1Prop")
(split)
(use "dx1Prop")
(split)
(use "dx1Prop")
(use "RealEqRefl")
(assert "x===(1#2)*(x1+IntN 1)* ~d")
(use "dx1Prop")
(assume "EqHyp")
(realproof)
;; 5
(drop "Disj")
(assume "ExHyp")
(by-assume "ExHyp" "x1" "x1Prop")
(intro 1)
(intro 0 (pt "x1"))
(intro 0 (pt "x"))
(split)
(use "CoHToReal")
(use "x1Prop")
(split)
(use "CoHToBd")
(use "x1Prop")
(split)
(use "x1Prop")
(split)
(use "x1Prop")
(use "RealEqRefl")
(assert "x===(1#2)*x1")
(use "x1Prop")
(assume "EqHyp")
(realproof)
;; Proof finished.
;; (cdp)
(save "CoGClosureInv")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)
;; [bgh]
;; cCoGClauseInv[if bgh (InL (boole yprod ag) ah) (InR ah (boole yprod ag))]
;; (ppc neterm)
;; [bgh]cCoGClauseInv[case bgh (InL bg -> InL bg) (InR ah -> InR ah)]
(animate "CoGClauseInv")
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [bgh]
;;  (CoRec boole yprod ag ysum ah=>ag boole yprod ag ysum ah=>ah)
;;  [case bgh (InL bg -> InL bg) (InR ah -> InR ah)]
;;  ([bgh0]
;;    [case bgh0
;;      (InL bg -> InL(clft bg pair InL crht bg))
;;      (InR ah -> InR(InL ah))])
;;  ([bgh0]
;;    [case bgh0
;;      (InL bg -> InL(clft bg pair InL crht bg))
;;      (InR ah -> InR(InL ah))])

(deanimate "CoGClauseInv")

;; ;; RealToCoIAux is renamed into RealToSdPairReal and is to be moved
;; ;; into examples/analysis/digits.scm, together with its auxiliaries
;; ;; ApproxSplitZeroMinusPtFive ApproxSplitZeroPtFive
;; ;; TwoTimesPlusIntReal TwoTimesPlusEq and also SdMRSdToInt

;; 2019-08-05.  New attempt for RealToCoG: use RealToCoI with a new
;; CoIToCoG.

;; SdToPsd
(set-goal "allnc d(Sd d -> Psd d orl d=0)")
(assume "d" "Sdd")
(elim "Sdd")
(intro 0)
(use "InitPsdTrue")
(intro 1)
(use "Truth")
(intro 0)
(use "InitPsdFalse")
;; Proof finished.
;; (cdp)
(save "SdToPsd")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)
;; [s][case s (SdR -> Inl True) (SdM -> DummyR) (SdL -> Inl False)]`

;; PsdToDisj
(set-goal "allnc d(Psd d -> d=1 oru d=IntN 1)")
(assume "d" "Psdd")
(elim "Psdd")
(intro 0)
(use "Truth")
(intro 1)
(use "Truth")
;; Proof finished.
;; (cdp)
(save "PsdToDisj")

;; (set! COMMENT-FLAG #f)
;; CoIToCoG
(set-goal "allnc x(Real x -> abs x<<=1 -> CoI x -> CoG x)")
(assume "x" "Rx" "xBd" "CoIx")
(coind "CoIx" (pf "CoI x -> CoH x"))
;; 3,4
(assume "x1" "CoIx1")
(inst-with-to "CoIClause" (pt "x1") "CoIx1" "CoIClauseInst")
(by-assume "CoIClauseInst" "d" "dProp")
(by-assume "dProp" "x2" "dx2Prop")
(by-assume "dx2Prop" "y2" "dx2y2Prop")
(assert "Real x2")
 (use "dx2y2Prop")
(assume "Rx2")
(assert "Psd d orl d=0")
 (use "SdToPsd")
 (use "dx2y2Prop")
(assume "Disj")
(elim "Disj")
;; 24,25
(drop "Disj")
(assume "Psdd")
(intro 0)
(inst-with-to "PsdToDisj" (pt "d") "Psdd" "dDisj")
(elim "dDisj")
;; 31,32
(drop "dDisj")
(assume "d=1")
(intro 0 (pt "IntP 1"))
;; (intro 0 (pt "IntN 1"))
(intro 0 (pt "~x2"))
(intro 0 (pt "x1"))
(split)
(use "InitPsdTrue")
(split)
(realproof)
(split)
(simpreal "RealAbsUMinus")
(use "dx2y2Prop")
(use "Rx2")
(split)
(intro 1)
(use "CoIUMinus")
(simpreal "RealUMinusUMinus")
(use "dx2y2Prop")
(use "Rx2")
(split)
(simpreal "dx2y2Prop")
(simpreal "dx2y2Prop")
(simpreal "<-" "RealTimesAssoc")
(simpreal "CoHToCoGAux")
(simpreal "RealTimesOne")
(simp "d=1")
(use "RealEqRefl")
(autoreal)
(use "RealEqRefl")
(realproof)
;; 32
(drop "dDisj")
(assume "d=IntN 1")
(intro 0 (pt "IntN 1"))
(intro 0 (pt "x2"))
(intro 0 (pt "x1"))
(split)
(use "InitPsdFalse")
(split)
(realproof)
(split)
(use "dx2y2Prop")
(split)
(intro 1)
(use "dx2y2Prop")
(split)
(simpreal "dx2y2Prop")
(simpreal "dx2y2Prop")
(simpreal "<-" "RealTimesAssoc")
(ng #t)
(simpreal "RealTimesOne")
(simp "d=IntN 1")
(use "RealEqRefl")
(autoreal)
(use "RealEqRefl")
(realproof)
;; 25
(drop "Disj")
(assume "d=0")
(intro 1)
(intro 0 (pt "2*x1"))
(intro 0 (pt "x1"))
;; To avoid many cCoICompat's in the extracted term (arising from a
;; later proof of CoI(2*x1)) we first prove 2*x1===x2 (idea of
;; F. Wiesnet).
(assert "2*x1===x2")
 (simpreal "dx2y2Prop")
 (simpreal "dx2y2Prop")
 (simpreal "RealTimesAssoc")
 (ng #t)
 (simpreal "RealOneTimes")
 (simp "d=0")
 (simpreal "RealPlusZero")
 (use "RealEqRefl")
 (autoreal)
;; Assertion proved.
(assume "2x1=x2")
(split)
(assert "Real x1")
 (use "CoIToReal")
 (use "CoIx1")
(assume "Rx1")
(realproof)
(split)
(simpreal "2x1=x2")
(use "dx2y2Prop")
(split)
(intro 1)
(simpreal "2x1=x2")
(use "dx2y2Prop")
(split)
(simpreal "RealTimesAssoc")
(ng #t)
(simpreal "RealOneTimes")
(use "RealEqRefl")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; 4
(assume "x1" "CoIx1")
(inst-with-to "CoIClause" (pt "x1") "CoIx1" "CoIClauseInst")
(by-assume "CoIClauseInst" "d" "dProp")
(by-assume "dProp" "x2" "dx2Prop")
(by-assume "dx2Prop" "y2" "dx2y2Prop")
(assert "Real x2")
 (use "dx2y2Prop")
(assume "Rx2")
(assert "Psd d orl d=0")
 (use "SdToPsd")
 (use "dx2y2Prop")
(assume "Disj")
(elim "Disj")
;; 165,166
(drop "Disj")
(assume "Psdd")
(intro 0)
(inst-with-to "PsdToDisj" (pt "d") "Psdd" "dDisj")
(elim "dDisj")
;; 172,173
(drop "dDisj")
(assume "d=1")
(intro 0 (pt "IntP 1"))
;; (intro 0 (pt "IntN 1"))
(intro 0 (pt "x2"))
(intro 0 (pt "x1"))
(split)
(use "InitPsdTrue")
(split)
(realproof)
(split)
(use "dx2y2Prop")
(split)
(intro 1)
(use "dx2y2Prop")
(split)
(simpreal "dx2y2Prop")
(simpreal "dx2y2Prop")
(simpreal "<-" "RealTimesAssoc")
(simpreal "RealTimesOne")
(simp "d=1")
(use "RealEqRefl")
(autoreal)
(use "RealEqRefl")
(realproof)
;; 173
(drop "dDisj")
(assume "d=IntN 1")
(intro 0 (pt "IntN 1"))
(intro 0 (pt "~x2"))
(intro 0 (pt "x1"))
(split)
(use "InitPsdFalse")
(split)
(realproof)
(split)
(simpreal "RealAbsUMinus")
(use "dx2y2Prop")
(use "dx2y2Prop")
(split)
(intro 1)
(use "CoIUMinus")
(simpreal "RealUMinusUMinus")
(use "dx2y2Prop")
(use "Rx2")
(split)
(simpreal "dx2y2Prop")
(simpreal "dx2y2Prop")
(simpreal "<-" "RealTimesAssoc")
(simpreal "RealTimesPlusDistrLeft")
(ng #t)
(simpreal "RealTimesUMinusId")
(simpreal "RealTimesIntNOne")
(simpreal "RealUMinusUMinus")
(simp "d=IntN 1")
(use "RealEqRefl")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; 166
(assume "d=0")
(intro 1)
(intro 0 (pt "2*x1"))
(intro 0 (pt "x1"))
(assert "2*x1===x2")
 (simpreal "dx2y2Prop")
 (simpreal "dx2y2Prop")
 (simpreal "RealTimesAssoc")
 (ng #t)
 (simpreal "RealOneTimes")
 (simp "d=0")
 (simpreal "RealPlusZero")
 (use "RealEqRefl")
 (autoreal)
;; Assertion proved.
(assume "2x1=x2")
(split)
(assert "Real x1")
 (use "CoIToReal")
 (use "CoIx1")
(assume "Rx1")
(realproof)
(split)
(simpreal "2x1=x2")
(use "dx2y2Prop")
(split)
(intro 1)
(simpreal "2x1=x2")
(use "dx2y2Prop")
(split)
(simpreal "RealTimesAssoc")
(ng #t)
(simpreal "RealOneTimes")
(use "RealEqRefl")
(autoreal)
(use "RealEqRefl")
(autoreal)
;; Proof finished.
;; (cdp)
(save "CoIToCoG")
;; (set! COMMENT-FLAG #t)

(define CoIToCoG-eterm (proof-to-extracted-term))
(define CoIToCoG-neterm (rename-variables (nt CoIToCoG-eterm)))
;; (ppc CoIToCoG-neterm)

;; [u]
;;  (CoRec ai=>ag ai=>ah)u
;;  ([u0]
;;    [case (cSdToPsd clft DesYprod u0)
;;      (Inl boole -> 
;;      InL
;;      [case (cPsdToDisj boole)
;;        (True -> True pair InR(cCoIUMinus(cCoICompat crht DesYprod u0)))
;;        (False -> False pair InR crht DesYprod u0)])
;;      (DummyR -> InR(InR(cCoICompat crht DesYprod u0)))])
;;  ([u0]
;;    [case (cSdToPsd clft DesYprod u0)
;;      (Inl boole -> 
;;      InL
;;      [case (cPsdToDisj boole)
;;        (True -> True pair InR crht DesYprod u0)
;;        (False -> False pair InR(cCoIUMinus(cCoICompat crht DesYprod u0)))])
;;      (DummyR -> InR(InR(cCoICompat crht DesYprod u0)))])

;; 2019-08-13.  We now prepare for the Haskell translation including a
;; reasonable display of what is returned.

;; Similar to what was done in digits we add a finite algebra gd for
;; Gray digits

(add-algs
 "gd"
 '("GR" "gd") '("GL" "gd") '("GU" "gd") '("HR" "gd") '("HL" "gd") '("HD" "gd"))
(add-totality "gd")

;; GdTotalVar
(set-goal "all gd TotalGd gd")
(use "AllTotalIntro")
(assume "gd^" "Tgd")
(use "Tgd")
;; Proof finished
(save "GdTotalVar")

;; GdEqToEqD
(set-goal "all gd1,gd2(gd1=gd2 -> gd1 eqd gd2)")
(cases)
;; 2-7
(cases)
(assume "Useless")
(use "InitEqD")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
;; 3
(cases)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Useless")
(use "InitEqD")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
;; 4
(cases)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Useless")
(use "InitEqD")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
;; 5
(cases)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Useless")
(use "InitEqD")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
;; 6
(cases)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Useless")
(use "InitEqD")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
;; 7
(cases)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "Useless")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "GdEqToEqD")

;; (pp (pt "str gd"))

;; 2019-08-14.  
;; Conversion from ag/ah into str gd

(add-program-constant "GToStrGd" (py "ag=>str gd"))
(add-program-constant "HToStrGd" (py "ah=>str gd"))
(add-computation-rules
 "GToStrGd(LR True ag)" "GR:~:GToStrGd ag"
 "GToStrGd(LR False ag)" "GL:~:GToStrGd ag"
 "GToStrGd(U ah)" "GU:~:HToStrGd ah")

(add-computation-rules
 "HToStrGd(Fin True ag)" "HR:~:GToStrGd ag"
 "HToStrGd(Fin False ag)" "HL:~:GToStrGd ag"
 "HToStrGd(D ah)" "HD:~:HToStrGd ah")

(add-program-constant "TakeG" (py "nat=>ag=>list gd"))
(add-computation-rules
 "TakeG n ag" "n init(GToStrGd ag)") 

;; Conversion from list gd into rat
(add-program-constant "ListGdToRat" (py "list gd=>rat"))
(add-computation-rules
 "ListGdToRat(Nil gd)" "0#1"
 "ListGdToRat(GR::list gd)" "(1#2)*(~(ListGdToRat(list gd))+1)"
 "ListGdToRat(GL::list gd)" "(1#2)*(ListGdToRat(list gd)+IntN 1)"
 "ListGdToRat(GU::list gd)" "(1#2)*ListGdToRat(list gd)"
 "ListGdToRat(HR::list gd)" "(1#2)*(ListGdToRat(list gd)+1)"
 "ListGdToRat(HL::list gd)" "(1#2)*(~(ListGdToRat(list gd))+IntN 1)"
 "ListGdToRat(HD::list gd)" "(1#2)*ListGdToRat(list gd)")

'(
(animate "RealToCoI")
(animate "RealToCoIAux")
(animate "ApproxSplitZeroPtFive")
(animate "ApproxSplitZeroMinusPtFive")
(animate "ApproxSplit")
(animate "SdToPsd")
(animate "Lft")
(animate "Rht")
(animate "PsdToDisj")
(animate "CoIUMinus")
(animate "CoICompat")
(animate "CoIClosure")
(animate "CoIClauseInv")
(animate "SdUMinus")

(terms-to-haskell-program
 "~/temp/graytest.hs"
 (list (list CoIToCoG-eterm "coitocog")
       (list RealToCoI-eterm "realtocoi")
       (list RatToCoI-eterm "rattocoi")
       (list (pt "SdMs") "sdms")
       (list (pt "PtFive") "ptfive")
       (list (pt "MPtFive") "mptfive")
       ;; (list (pt "OneSdR") "onesdr")
       ;; (list (pt "OneSdL") "onesdl")
       ;; (list (pt "SqrtTwoOverTwo") "stot")
       ;; (list (pt "IrrStr") "irrstr")
       (list (pt "TakeStr") "takestr")
       (list (pt "ListSdToRat") "listsdtorat")
       (list (pt "GToStrGd") "gtostrgd")
       (list (pt "HToStrGd") "htostrgd")
       (list (pt "TakeG") "takeg")
       (list (pt "ListGdToRat") "listgdtorat")
       ))

(deanimate "RealToCoI")
(deanimate "RealToCoIAux")
(deanimate "ApproxSplitZeroMinusPtFive")
(deanimate "ApproxSplitZeroPtFive")
(deanimate "ApproxSplit")
(deanimate "SdToPsd")
(deanimate "Lft")
(deanimate "Rht")
(deanimate "PsdToDisj")
(deanimate "CoIUMinus")
(deanimate "CoICompat")
(deanimate "CoIClosure")
(deanimate "CoIClauseInv")
(deanimate "SdUMinus")
)

;; ghci graytest.hs

;; 2019-08-14

;; takestr 18 (rattocoi (1 % 3))
;; [SdR,SdL,SdR,SdL,SdR,SdL,SdR,SdL,SdR,SdL,SdR,SdL,SdR,SdL,SdR,SdL,SdR,SdL]

;; takeg 18 (coitocog (rattocoi (1 % 3)))
;; [GR,GR,GR,GR,GR,GR,GR,GR,GR,GR,GR,GR,GR,GR,GR,GR,GR,GR]

;; CoIToCoG is probably wrongly translated.  Postponed.

