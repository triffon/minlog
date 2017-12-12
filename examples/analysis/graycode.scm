;; 2017-12-12.  examples/analysis/graycode.scm

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
;;   Psd d andd Real x0 andr CoG x0 andl y===(1#2)*(x0+IntN 1)* ~d andnc x===y) ord 
;;  exr x0,y(Real x0 andr CoH x0 andl y===(1#2)*x0 andnc x===y))

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
(save "CoGClauseInv")

(define eterm (proof-to-extracted-term))
(add-var-name "bgh" (py "boole yprod ag ysum ah"))
(add-var-name "bg" (py "boole yprod ag"))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

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
  CoG x0 andl y===(1#2)*(x0+IntN 1)* ~d
                                           andnc x===y) ord 
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
(save "CoHClauseInv")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

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
(save "CoGCompat")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [ag][case (DesYprod ag)
;;    (InL bg -> cCoGClauseInv(InL bg))
;;    (InR ah -> cCoGClauseInv(InR ah))]

(animate "CoGClauseInv")

(define neterm (rename-variables (nt eterm)))
(ppc neterm)

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
(save "CoHCompat")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [ah]
;;  [case (DesYprod ah)
;;    (InL bg -> cCoHClauseInv(InL(clft bg pair crht bg)))
;;    (InR ah0 -> cCoHClauseInv(InR ah0))]

(animate "CoHClauseInv")

(define neterm (rename-variables (nt eterm)))
(ppc neterm)

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
(pp (rename-variables nneterm))

;; [ah][if (DesYprod ah) ([bg]Fin clft bg crht bg) D]

(ppc (rename-variables nneterm))

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
;; ?_43:abs(x1+IntN 1)<<=abs(RealPlus 1 1) from abs x1<<=1
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
;; ?_30:1===abs(1#2)*abs(RealPlus 1 1)*abs~d
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
;; ?_6:exr x0,y(
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
;; ?_35:abs(x1+1)<<=abs(RealPlus 1 1) from abs x1<<=1
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
;; ?_6:exr x0,y(
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
(save "CoGClosure")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [ag][case (DesYprod ag) (InL bg -> InL bg) (InR ah -> InR ah)]

(pp neterm)

;; [ag][if (DesYprod ag) (InL (boole yprod ag) ah) (InR ah (boole yprod ag))]

(pp (term-to-type (pt "(InL (boole yprod ag) ah)")))
;; boole yprod ag=>boole yprod ag ysum ah
(pp (term-to-type (pt "(InR ah (boole yprod ag))")))
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
(save "CoHClosure")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [ah][case (DesYprod ah) (InL bg -> InL bg) (InR ah -> InR ah)]

(pp neterm)

;; [ah][if (DesYprod ah) (InL (boole yprod ag) ah) (InR ah (boole yprod ag))]

(pp (term-to-type (pt "(InL (boole yprod ag) ah)")))
;; boole yprod ag=>boole yprod ag ysum ah
(pp (term-to-type (pt "(InR ah (boole yprod ag))")))
;; ah=>boole yprod ag ysum ah

;; CoGClosureInvG
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
(save "CoGClosureInvG")

(define eterm (proof-to-extracted-term))
(animate "CoGClauseInv")
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [boole,ag](CoRec boole yprod ag ysum ah=>ag boole yprod ag ysum ah=>ah)
;;  (InL(boole pair ag))
;;  ([bgh][case bgh
;;      (InL bg -> InL(clft bg pair InL crht bg))
;;      (InR ah -> InR(InL ah))])
;;  ([bgh][case bgh
;;      (InL bg -> InL(clft bg pair InL crht bg))
;;      (InR ah -> InR(InL ah))])

;; CoGClosureInvH
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
(save "CoGClosureInvH")

(define eterm (proof-to-extracted-term))
(animate "CoGClauseInv")
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [ah](CoRec boole yprod ag ysum ah=>ag boole yprod ag ysum ah=>ah)(InR ah)
;;  ([bgh][case bgh
;;      (InL bg -> InL(clft bg pair InL crht bg))
;;      (InR ah0 -> InR(InL ah0))])
;;  ([bgh][case bgh
;;      (InL bg -> InL(clft bg pair InL crht bg))
;;      (InR ah0 -> InR(InL ah0))])

(deanimate "CoGClauseInv")

;; CoHClosureInvG
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
(save "CoHClosureInvG")

(define eterm (proof-to-extracted-term))
(animate "CoHClauseInv")
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [boole,ag](CoRec boole yprod ag ysum ah=>ah boole yprod ag ysum ah=>ag)
;;  (InL(boole pair ag))
;;  ([bgh][case bgh
;;      (InL bg -> InL(clft bg pair InL crht bg))
;;      (InR ah -> InR(InL ah))])
;;  ([bgh][case bgh
;;      (InL bg -> InL(clft bg pair InL crht bg))
;;      (InR ah -> InR(InL ah))])

;; CoHClosureInvH
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
(save "CoHClosureInvH")

(define eterm (proof-to-extracted-term))
(animate "CoHClauseInv")
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

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
;; ?_39:x1===(1#2)*(x2+IntN 1)* ~ ~d
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
;; ?_78:x1===(1#2)* ~x2
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
;; ?_125:x1===(1#2)*(x2+1)* ~d
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
(save "CoGUMinus")

(define eterm (proof-to-extracted-term))
(animate "CoGClosure")
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

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
(use "CoGCompat" (pt "x"))
(use "RealEqSym")
(use "RealTimesOne")
(use "CoGToReal")
(use "CoGx")
(use "CoGx")
;; 4
(assert "x* IntUMinus 1=== ~(x*1)")
(use "RealTimesIdRatUMinus")
(use "CoGToReal")
(use "CoGx")
(ng)
(assume "x*IntN 1=== ~(x*1)")
(use "CoGCompat" (pt "~(x*1)"))
(use "RealEqSym")
(use "x*IntN 1=== ~(x*1)")
(use "CoGUMinus")
(use "CoGCompat" (pt "x*1"))
(use "RealEqSym")
(use "RealUMinusUMinus")
(use "RealTimesReal")
(use "CoGToReal")
(use "CoGx")
(use "RealRat")
(use "CoGCompat" (pt "x"))
;;   {x}  {d}  CoGx:CoG x
;;   2:Psd d
;;   x*IntN 1=== ~(x*1):x*IntN 1=== ~(x*1)
;; -----------------------------------------------------------------------------
;; ?_27:x===x*1
(use "RealEqSym")
(use "RealTimesOne")
(use "CoGToReal")
(use "CoGx")
(use "CoGx")
;; Proof finished.
(save "CoGPsdTimes")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [ag,boole]
;; [if boole (cCoGCompat ag)
;;           (cCoGCompat(cCoGUMinus(cCoGCompat(cCoGCompat ag))))]

;; CoHToCoGAux
(set-goal "all d,x(Real x -> (~x+IntN 1)* ~d===(x+1)*d)")
(assert "all d,x (~x+IntN 1)* ~d=+=(x+1)*d")
(assume "d")
(cases)
(assume "as" "M")
(use "RealEqSIntro")
(assume "n")
(ng)
;; ?_9:~((~(as n)+IntN 1)*d)==(as n+1)*d
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
;; ?_40:x1===(1#2)*(~x2+IntN 1)* ~d
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
;; ?_110:x1===(1#2)*(~x2+1)*d
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
(save "CoHToCoG")

(define eterm (proof-to-extracted-term))
(animate "CoGClosure")
(animate "CoHClosure")
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

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
;; ?_40:x1===(1#2)*(~x2+IntN 1)* ~d
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
;; ?_110:x1===(1#2)*(~x2+1)*d
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
(save "CoGToCoH")

(define eterm (proof-to-extracted-term))
(animate "CoGClosure")
(animate "CoHClosure")
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [ag](CoRec ag=>ah ah=>ag)ag
;;  ([ah][case (DesYprod ah)
;;      (InL bg -> InL(clft bg pair InL(cCoGUMinus(cCoGCompat crht bg))))
;;      (InR ah0 -> InR(InL ah0))])
;;  ([ag0][case (DesYprod ag0)
;;      (InL bg -> InL(clft bg pair InL(cCoGUMinus(cCoGCompat crht bg))))
;;      (InR ah -> InR(InL ah))])

(deanimate "CoGClosure")
(deanimate "CoHClosure")
