;; 2017-04-21.  graymult.scm

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
;; Gray code
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
;; PsdMR
;; 	InitPsdTrueMR:	PsdMR True 1
;; 	InitPsdFalseMR:	PsdMR False(IntN 1)

;; PsdMRId
(set-goal "all d,boole(PsdMR boole d -> BooleToInt boole=d)")
(assume "d" "boole" "PsdMRHyp")
(elim "PsdMRHyp")
(use "Truth")
(use "Truth")
;; Proof finished.
(save "PsdMRId")

;; PsdMRIntro
(set-goal "allnc d(Psd d -> exl boole PsdMR boole d)")
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
(set-goal "allnc d all boole(PsdMR boole d -> Psd d)")
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
(set-goal "all d(abs d=1 -> PsdMR(IntToBoole d)d)")
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
 '("allnc d,x,y(Psd d -> Real x -> G x -> y===(1#2)*(x+IntN 1)* ~d -> G y)"
  "GenLR")
 '("allnc x,y(Real x -> H x -> y===(1#2)*x -> G y)" "GenU")
 '("allnc d,x,y(Psd d -> Real x -> G x -> y===(1#2)*(x+1)*d -> H y)" "GenFin")
 '("allnc x,y(Real x -> H x -> y===(1#2)*x -> H y)" "GenD"))

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
 exr d,x0,y(Psd d andd Real x0 andr CoG x0 andl y===(1#2)*(x0+IntN 1)* ~d
                                           andnc x===y) ord 
 exr x0,y(Real x0 andr CoH x0 andl y===(1#2)*x0 andnc x===y) -> CoG x)")
(assume "x" "Disj")
(coind
 "Disj"
 (pf "exr d,x0,y(
  Psd d andd Real x0 andr CoG x0 andl y===(1#2)*(x0+1)*d andnc x===y) ord 
  exr x0,y(Real x0 andr CoH x0 andl y===(1#2)*x0 andnc x===y) -> CoH x"))
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
  Psd d andd Real x0 andr CoG x0 andl y===(1#2)*(x0+1)*d andnc x===y) ord 
 exr x0,y(Real x0 andr CoH x0 andl y===(1#2)*x0 andnc x===y) ->  CoH x)")
(assume "x" "Disj")
(coind
 "Disj"
 (pf "exr d,x0,y(Psd d andd Real x0 andr CoG x0 andl y===(1#2)*(x0+IntN 1)* ~d
                                           andnc x===y) ord 
 exr x0,y(Real x0 andr CoH x0 andl y===(1#2)*x0 andnc x===y) -> CoG x"))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Average for Gray code
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
(realproof)
(split)
(intro 0)
(use "CoGx2")
(split)
;;   {x}  CoG-x:CoG(~x)
;;   {x1}  CoG-x1:CoG(~x1)
;;   {d}  {x2}  dx2Prop:Psd d andd CoG x2 andl ~x1===(1#2)*(x2+IntN 1)* ~d
;; -----------------------------------------------------------------------------
;; ?_36:x1===(1#2)*(x2+IntN 1)* ~ ~d
(use "RealEqTrans" (pt "~ ~x1"))
(use "RealEqSym")
(use "RealUMinusUMinus")
(use "RealUMinusRealInv")
(realproof)
(use "RealEqTrans" (pt "~((1#2)*(x2+IntN 1)* ~d)"))
(use "RealUMinusCompat")
(use "EqHyp")
(use "RealEqSym")
(use "RealTimesIdRatUMinus")
(realproof)
(use "RealEqRefl")
(use "RealUMinusRealInv")
(realproof)
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
(realproof)
(split)
(intro 1)
;; ?_65:CoH(~ ~x2)
(use "CoHCompat" (pt "x2"))
(use "RealEqSym")
(use "RealUMinusUMinus")
(realproof)
(use "CoHx2")
(split)
;;   {x}  CoG-x:CoG(~x)
;;   {x1}  CoG-x1:CoG(~x1)
;;   {x2}  x2Prop:CoH x2 andl ~x1===(1#2)*x2
;; -----------------------------------------------------------------------------
;; ?_70:x1===(1#2)* ~x2
(use "RealEqTrans" (pt "~ ~x1"))
(use "RealEqSym")
(use "RealUMinusUMinus")
(use "RealUMinusRealInv")
(realproof)
(simpreal "EqHyp")
(use "RealEqSym")
(use "RealTimesIdUMinus")
(use "RealRat")
(realproof)
(use "RealEqRefl")
(use "RealUMinusRealInv")
(realproof)
;; 4
(assume "x1" "CoH-x1")
(inst-with-to "CoHClosure" (pt "~x1") "CoH-x1" "Disj")
(elim "Disj")
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
(realproof)
(split)
(intro 0)
(use "CoGx2")
(split)
;;   {x}  CoG-x:CoG(~x)
;;   {x1}  CoH-x1:CoH(~x1)
;;   {d}  {x2}  Psdd:Psd d
;;   CoGx2:CoG x2
;;   EqHyp:~x1===(1#2)*(x2+1)*d
;; -----------------------------------------------------------------------------
;; ?_114:x1===(1#2)*(x2+1)* ~d
(use "RealEqTrans" (pt "~ ~x1"))
(use "RealEqSym")
(use "RealUMinusUMinus")
(use "RealUMinusRealInv")
(realproof)
(simpreal "EqHyp")
(use "RealEqSym")
(use "RealTimesIdRatUMinus")
(realproof)
(use "RealEqRefl")
(use "RealUMinusRealInv")
(realproof)
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
(use "CoHToReal")
(use "x2Prop")
(split)
(intro 1)
(use "CoHCompat" (pt "x2"))
(use "RealEqSym")
(use "RealUMinusUMinus")
(use "CoHToReal")
(use "x2Prop")
(use "x2Prop")
(split)
(use "RealEqTrans" (pt "~ ~x1"))
(use "RealEqSym")
(use "RealUMinusUMinus")
(use "RealUMinusRealInv")
(use "CoHToReal")
(use "CoH-x1")
(use "RealEqTrans" (pt "~((1#2)*x2)"))
(use "RealUMinusCompat")
(use "x2Prop")
(use "RealEqSym")
(use "RealTimesIdUMinus")
(use "RealRat")
(use "CoHToReal")
(use "x2Prop")
(use "RealEqRefl")
(use "RealUMinusRealInv")
(use "CoHToReal")
(use "CoH-x1")
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
;; [if boole (cCoGCompat ag) (cCoGCompat(cCoGUMinus(cCoGCompat(cCoGCompat ag))))]

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
(realproof)
(realproof)
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
(intro 0)
(intro 0 (pt "d"))
(intro 0 (pt "~x2"))
(intro 0 (pt "x1"))
(split)
(use "dx2Prop")
(split)
(use "RealUMinusReal")
(use "CoGToReal")
(use "dx2Prop")
(split)
(intro 0)
(use "CoGUMinus")
;; ?_31:CoG(~ ~x2)
(use "CoGCompat" (pt "x2"))
(use "RealEqSym")
(use "RealUMinusUMinus")
(use "CoGToReal")
(use "dx2Prop")
(use "dx2Prop")
(split)
;;   {x}  CoHx:CoH x
;;   {x1}  CoHx1:CoH x1
;;   {d}  {x2}  dx2Prop:Psd d andd CoG x2 andl x1===(1#2)*(x2+1)*d
;; -----------------------------------------------------------------------------
;; ?_37:x1===(1#2)*(~x2+IntN 1)* ~d
;; Before being able to apply CoHToCoGAux we need some compatibilities
(use "RealEqTrans" (pt "(1#2)*(x2+1)*d"))
(use "dx2Prop")
(use "RealEqTrans" (pt "(1#2)*((x2+1)*d)"))
(use "RealEqSym")
(use "RealTimesAssoc")
(use "RealRat")
(use "RealPlusReal")
(use "CoGToReal")
(use "dx2Prop")
(use "RealRat")
(use "RealRat")
(use "RealEqTrans" (pt "(1#2)*((~x2+IntN 1)* ~d)"))
(use "RealTimesCompat")
(use "RealEqRefl")
(use "RealRat")
(use "RealEqSym")
(use "CoHToCoGAux")
(use "CoGToReal")
(use "dx2Prop")
(use "RealTimesAssoc")
(use "RealRat")
(use "RealPlusReal")
(use "RealUMinusReal")
(use "CoGToReal")
(use "dx2Prop")
(use "RealRat")
(use "RealRat")
(use "RealEqRefl")
(use "CoHToReal")
(use "CoHx1")
;; 9
(drop "CoHClosureInst")
;; middle case
(assume "ExHyp")
(intro 1)
(by-assume "ExHyp" "x2" "x2Prop")
(intro 0 (pt "x2"))
(intro 0 (pt "x1"))
(split)
(use "CoHToReal")
(use "x2Prop")
(split)
(intro 0)
(use "x2Prop")
(split)
(use "x2Prop")
(use "RealEqRefl")
(use "CoHToReal")
(use "CoHx1")
;; 4
(assume "x1" "CoGx1")
(inst-with-to "CoGClosure" (pt "x1") "CoGx1" "CoGClosureInst")
(elim "CoGClosureInst")
;; 88,89
(drop "CoGClosureInst")
;; left case
(assume "ExHyp")
(by-assume "ExHyp" "d" "dProp")
(by-assume "dProp" "x2" "dx2Prop")
(intro 0)
(intro 0 (pt "d"))
(intro 0 (pt "~x2"))
(intro 0 (pt "x1"))
(split)
(use "dx2Prop")
(split)
(use "RealUMinusReal")
(use "CoGToReal")
(use "dx2Prop")
(split)
(intro 0)
(use "CoGUMinus")
;; ?_111:CoG(~ ~x2)
(use "CoGCompat" (pt "x2"))
(use "RealEqSym")
(use "RealUMinusUMinus")
(use "CoGToReal")
(use "dx2Prop")
(use "dx2Prop")
(split)
;; Need (~x2+1)*d===(x2+IntN 1)* ~d
(use "RealEqTrans" (pt "(1#2)*(x2+IntN 1)* ~d"))
(use "dx2Prop")
(use "RealEqTrans" (pt "(1#2)*((x2+IntN 1)* ~d)"))
(use "RealEqSym")
(use "RealTimesAssoc")
(use "RealRat")
(use "RealPlusReal")
(use "CoGToReal")
(use "dx2Prop")
(use "RealRat")
(use "RealRat")
(use "RealEqTrans" (pt "(1#2)*((~x2+1)*d)"))
(use "RealTimesCompat")
(use "RealEqRefl")
(use "RealRat")
;; ?_133:(x2+IntN 1)* ~d===(~x2+1)*d
(use "RealEqTrans" (pt "(~ ~x2+IntN 1)* ~d"))
(use "RealTimesCompat")
(use "RealPlusCompat")
(use "RealEqSym")
(use "RealUMinusUMinus")
(use "CoGToReal")
(use "dx2Prop")
(use "RealEqRefl")
(use "RealRat")
(use "RealEqRefl")
(use "RealRat")
(use "CoHToCoGAux")
(use "RealUMinusReal")
(use "CoGToReal")
(use "dx2Prop")
(use "RealTimesAssoc")
(use "RealRat")
(use "RealPlusReal")
(use "RealUMinusReal")
(use "CoGToReal")
(use "dx2Prop")
(use "RealRat")
(use "RealRat")
(use "RealEqRefl")
(use "CoGToReal")
(use "CoGx1")
;; 89
(drop "CoGClosureInst")
;; right case
(assume "ExHyp")
(by-assume "ExHyp" "x2" "x2Prop")
(intro 1)
(intro 0 (pt "x2"))
(intro 0 (pt "x1"))
(split)
(use "CoHToReal")
(use "x2Prop")
(split)
(intro 0)
(use "x2Prop")
(split)
(use "x2Prop")
(use "RealEqRefl")
(use "CoGToReal")
(use "CoGx1")
;; Proof finished.
(save "CoHToCoG")

(define eterm (proof-to-extracted-term))
(animate "CoGClosure")
(animate "CoHClosure")
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [ah](CoRec ah=>ag ag=>ah)ah
;;  ([ah0][case (DesYprod ah0)
;;      (InL bg -> InL(clft bg pair
;;                     InL(cCoGUMinus(cCoGCompat crht bg))))
;;      (InR ah1 -> InR(InL ah1))])
;;  ([ag][case (DesYprod ag)
;;      (InL bg -> InL(clft bg pair
;;                     InL(cCoGUMinus(cCoGCompat crht bg))))
;;      (InR ah0 -> InR(InL ah0))])

(deanimate "CoGClosure")
(deanimate "CoHClosure")

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

;; CoGAvAvcAux
(set-goal "all x,y,d,e(Real x -> Real y ->
 (1#2)*((1#2)*(x+IntN 1)* ~d+(1#2)*(y+IntN 1)* ~e)===
 (1#4)*(x* ~d+y* ~e+(d+e)))")
(assert "all x,y,d,e
 (1#2)*((1#2)*(x+IntN 1)* ~d+(1#2)*(y+IntN 1)* ~e)=+=
 (1#4)*(x* ~d+y* ~e+(d+e))")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "d" "e")
(use "RealEqSIntro")
(assume "n")
(ng)
;; ?_10:(1#2)*((1#2)*(as n+IntN 1)* ~d+(1#2)*(bs n+IntN 1)* ~e)==
;;      (1#4)*(as n* ~d+bs n* ~e+(d+e))
(use "RatEqvTrans"
     (pt "(1#2)*((1#2)*((as n+IntN 1)* ~d)+(1#2)*((bs n+IntN 1)* ~e))"))
(use "RatTimesCompat")
(use "Truth")
(use "RatPlusCompat")
(use "Truth")
(use "Truth")
;; ?_12:(1#2)*((1#2)*((as n+IntN 1)* ~d)+(1#2)*((bs n+IntN 1)* ~e))==
;;      (1#4)*(as n* ~d+bs n* ~e+(d+e))
(simprat "<-" "RatTimesPlusDistr")
(simp "RatTimesAssoc")
(ng)
;; ~((as n+IntN 1)*d)+ ~((bs n+IntN 1)*e)== ~(as n*d)+ ~(bs n*e)+(d+e)
(simprat "RatTimesPlusDistrLeft")
(simprat "RatTimesPlusDistrLeft")
(ng)
(simp "IntTimesIntNL")
(simp "IntTimesIntNL")
(ng)
(simp (pf "d+e=RatPlus d e"))
(simp "<-" "RatPlus2RewRule")
(simp "<-" "RatPlus2RewRule")
(simp "<-" "RatPlus2RewRule")
(simp "RatEqv4RewRule")
(simp "RatPlusAssoc")
(simp "RatPlusAssoc")
(simp "RatEqv3RewRule")
(simprat "RatEqvSym")
(use "Truth")
(simp "RatPlusComm")
(use "Truth")
(use "Truth")
;; Assertion proved.
(assume "CoGAvAvcAuxEqS" "x" "y" "d" "e" "Rx" "Ry")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "CoGAvAvcAuxEqS")
;; Proof finished.
(save "CoGAvAvcAux")

;; CoGAvAvcPsdMid
(set-goal "all x,y,d(Real x -> Real y -> 
 (1#2)*((1#2)*(x+IntN 1)* ~d+(1#2)*y)===(1#4)*(x* ~d+y+d))")
(assert "all x,y,d
 (1#2)*((1#2)*(x+IntN 1)* ~d+(1#2)*y)=+=(1#4)*(x* ~d+y+d)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "d")
(use "RealEqSIntro")
(assume "n")
(ng)
;; ?_10:(1#2)*((1#2)*(as n+IntN 1)* ~d+(1#2)*bs n)==(1#4)*(as n* ~d+bs n+d)
(use "RatEqvTrans" (pt "(1#2)*((1#2)*((as n+IntN 1)* ~d)+(1#2)*bs n)"))
(use "RatTimesCompat")
(use "Truth")
(use "RatPlusCompat")
(use "Truth")
(use "Truth")
;; ?_12:(1#2)*((1#2)*((as n+IntN 1)* ~d)+(1#2)*bs n)==(1#4)*(as n* ~d+bs n+d)
(simprat "<-" "RatTimesPlusDistr")
(simp "RatTimesAssoc")
(ng)
;; ?_19:~((as n+IntN 1)*d)+bs n== ~(as n*d)+bs n+d
(simprat "RatTimesPlusDistrLeft")
(ng)
(simp "IntTimesIntNL")
(ng)
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp (pf "d+bs n=bs n+d"))
(use "Truth")
(use "RatPlusComm")
;; Assertion proved.
(assume "CoGAvAvcPsdMidEqS" "x" "y" "d" "Rx" "Ry")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "CoGAvAvcPsdMidEqS")
;; Proof finished.
(save "CoGAvAvcPsdMid")

;; CoGAvAvcMidPsd
(set-goal "all x,y,e(Real x -> Real y ->
 (1#2)*((1#2)*x+(1#2)*(y+IntN 1)* ~e)===(1#4)*(x+y* ~e+e))")
(assert "all x,y,e
 (1#2)*((1#2)*x+(1#2)*(y+IntN 1)* ~e)=+=(1#4)*(x+y* ~e+e)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "e")
(use "RealEqSIntro")
(assume "n")
(ng)
;; ?_10:(1#2)*((1#2)*as n+(1#2)*(bs n+IntN 1)* ~e)==(1#4)*(as n+bs n* ~e+e)
(use "RatEqvTrans" (pt "(1#2)*((1#2)*as n+(1#2)*((bs n+IntN 1)* ~e))"))
(use "Truth")
(simprat "<-" "RatTimesPlusDistr")
(ng)
(simp "<-" "RatPlusAssoc")
(simp "RatEqv4RewRule")
(simprat "RatTimesPlusDistrLeft")
(ng)
(simp "IntTimesIntNL")
(use "Truth")
;; Assertion proved
(assume "CoGAvAvcMidPsdEqS" "x" "y" "e" "Rx" "Ry")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "CoGAvAvcMidPsdEqS")
;; Proof finished.
(save "CoGAvAvcMidPsd")

;; CoGAvAvcMidMid
(set-goal "all x,y(Real x -> Real y ->
 (1#2)*((1#2)*x+(1#2)*y)===(1#4)*(x+y+0))")
(assert "all x,y (1#2)*((1#2)*x+(1#2)*y)=+=(1#4)*(x+y+0)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N")
(use "RealEqSIntro")
(assume "n")
(ng)
;; ?_10:(1#2)*((1#2)*as n+(1#2)*bs n)==(1#4)*(as n+bs n)
(simprat "<-" "RatTimesPlusDistr")
(use "Truth")
;; Assertion proved.
(assume "CoGAvAvcMidMidEqS" "x" "y" "Rx" "Ry")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "CoGAvAvcMidMidEqS")
;; Proof finished.
(save "CoGAvAvcMidMid")

;; CoGAvToAvc
(set-goal "allnc x,y(CoG x -> CoG y -> 
 exr i,x1,y1(Sdtwo i andi CoG x1 andi CoG y1 andi
 (1#2)*(x+y)===(1#4)*(x1+y1+i)))")
(assume "x" "y" "CoGx" "CoGy")
(inst-with-to "CoGClosure" (pt "x") "CoGx" "xCases")
(elim "xCases")
(drop "xCases")

;; Case LRx
(assume "ExHypx")
(by-assume "ExHypx" "d" "dProp")
(by-assume "dProp" "x1" "dx1Prop")

;; We distinguish cases on CoG y
(inst-with-to "CoGClosure" (pt "y") "CoGy" "yCases")
(elim "yCases")
(drop "yCases")

;; Subcase LRx, LRy
(assume "ExHypy")
(by-assume "ExHypy" "e" "eProp")
(by-assume "eProp" "y1" "ey1Prop")
(intro 0 (pt "d+e"))
(intro 0 (pt "x1* ~d"))
(intro 0 (pt "y1* ~e"))
(split)
(use "IntPlusPsdToSdtwo")
(use "dx1Prop")
(use "ey1Prop")
(split)
(use "CoGPsdTimes")
(use "dx1Prop")
(use "PsdUMinus")
(use "dx1Prop")
(split)
(use "CoGPsdTimes")
(use "ey1Prop")
(use "PsdUMinus")
(use "ey1Prop")
;;   {x}  {y}  CoGx:CoG x
;;   CoGy:CoG y
;;   {d}  {x1}  dx1Prop:Psd d andd CoG x1 andl x===(1#2)*(x1+IntN 1)* ~d
;;   {e}  {y1}  ey1Prop:Psd e andd CoG y1 andl y===(1#2)*(y1+IntN 1)* ~e
;; -----------------------------------------------------------------------------
;; ?_40:(1#2)*(x+y)===(1#4)*(x1* ~d+y1* ~e+(d+e))
;; Before being able to use CoGAvAvcAux we need compatibilities.
(use "RealEqTrans" (pt "(1#2)*((1#2)*(x1+IntN 1)* ~d+(1#2)*(y1+IntN 1)* ~e)"))
(use "RealTimesCompat")
(use "RealEqRefl")
(use "RealRat")
(use "RealPlusCompat")
(use "dx1Prop")
(use "ey1Prop")
(use "CoGAvAvcAux")
(use "CoGToReal")
(use "dx1Prop")
(use "CoGToReal")
(use "ey1Prop")
;; 18
(drop "yCases")

;; Case LRx,Midy
(assume "ExHypy")
(by-assume "ExHypy" "y1" "y1Prop")
(intro 0 (pt "d"))
(intro 0 (pt "x1* ~d"))
(intro 0 (pt "y1"))
(split)
(use "PsdToSdtwo")
(use "dx1Prop")
(split)
(use "CoGPsdTimes")
(use "dx1Prop")
(use "PsdUMinus")
(use "dx1Prop")
(split)
(use "CoHToCoG")
(use "y1Prop")
;;   {x}  {y}  CoGx:CoG x
;;   CoGy:CoG y
;;   {d}  {x1}  dx1Prop:Psd d andd CoG x1 andl x===(1#2)*(x1+IntN 1)* ~d
;;   {y1}  y1Prop:CoH y1 andl y===(1#2)*y1
;; -----------------------------------------------------------------------------
;; ?_72:(1#2)*(x+y)===(1#4)*(x1* ~d+y1+d)
(use "RealEqTrans" (pt "(1#2)*((1#2)*(x1+IntN 1)* ~d+y)")) 
(use "RealTimesCompat")
(use "RealEqRefl")
(use "RealRat")
(use "RealPlusCompat")
(use "dx1Prop")
(use "RealEqRefl")
(use "CoGToReal")
(use "CoGy")
(use "RealEqTrans" (pt "(1#2)*((1#2)*(x1+IntN 1)* ~d+(1#2)*y1)"))
(use "RealTimesCompat")
(use "RealEqRefl")
(use "RealRat")
(use "RealPlusCompat")
(use "RealEqRefl")
(use "RealTimesReal")
(use "RealTimesReal")
(use "RealRat")
(use "RealPlusReal")
(use "CoGToReal")
(use "dx1Prop")
(use "RealRat")
(use "RealRat")
(use "y1Prop")
;;   {x}  {y}  CoGx:CoG x
;;   CoGy:CoG y
;;   {d}  {x1}  dx1Prop:Psd d andd CoG x1 andl x===(1#2)*(x1+IntN 1)* ~d
;;   {y1}  y1Prop:CoH y1 andl y===(1#2)*y1
;; -----------------------------------------------------------------------------
;; ?_84:(1#2)*((1#2)*(x1+IntN 1)* ~d+(1#2)*y1)===(1#4)*(x1* ~d+y1+d)
(use "CoGAvAvcPsdMid")
(use "CoGToReal")
(use "dx1Prop")
(use "CoHToReal")
(use "y1Prop")
;; 6 Case Midx
(assume "ExHypx")
(by-assume "ExHypx" "x1" "x1Prop")

;; We distinguish cases on CoG y
(inst-with-to "CoGClosure" (pt "y") "CoGy" "yCases")
(elim "yCases")
(drop "yCases")

;; Subcase Midx, LRy
(assume "ExHypy")
(by-assume "ExHypy" "e" "eProp")
(by-assume "eProp" "y1" "ey1Prop")
(intro 0 (pt "e"))
(intro 0 (pt "x1"))
(intro 0 (pt "y1* ~e"))
(split)
(use "PsdToSdtwo")
(use "ey1Prop")
(split)
(use "CoHToCoG")
(use "x1Prop")
(split)
(use "CoGPsdTimes")
(use "ey1Prop")
(use "PsdUMinus")
(use "ey1Prop")
;;   {x}  {y}  CoGx:CoG x
;;   CoGy:CoG y
;;   {x1}  x1Prop:CoH x1 andl x===(1#2)*x1
;;   {e}  {y1}  ey1Prop:Psd e andd CoG y1 andl y===(1#2)*(y1+IntN 1)* ~e
;; -----------------------------------------------------------------------------
;; ?_128:(1#2)*(x+y)===(1#4)*(x1+y1* ~e+e)
(use "RealEqTrans" (pt "(1#2)*((1#2)*x1+y)"))
(use "RealTimesCompat")
(use "RealEqRefl")
(use "RealRat")
(use "RealPlusCompat")
(use "x1Prop")
(use "RealEqRefl")
(use "CoGToReal")
(use "CoGy")
(use "RealEqTrans" (pt "(1#2)*((1#2)*x1+(1#2)*(y1+IntN 1)* ~e)"))
(use "RealTimesCompat")
(use "RealEqRefl")
(use "RealRat")
(use "RealPlusCompat")
(use "RealEqRefl")
(use "RealTimesReal")
(use "RealRat")
(use "CoHToReal")
(use "x1Prop")
(use "ey1Prop")
;;   {x}  {y}  CoGx:CoG x
;;   CoGy:CoG y
;;   {x1}  x1Prop:CoH x1 andl x===(1#2)*x1
;;   {e}  {y1}  ey1Prop:Psd e andd CoG y1 andl y===(1#2)*(y1+IntN 1)* ~e
;; -----------------------------------------------------------------------------
;; ?_142:(1#2)*((1#2)*x1+(1#2)*(y1+IntN 1)* ~e)===(1#4)*(x1+y1* ~e+e)
(use  "CoGAvAvcMidPsd")
(use "CoHToReal")
(use "x1Prop")
(use "CoGToReal")
(use "ey1Prop")

;; Subcase Midx, Midy
(assume "ExHypy")
(drop "yCases")
(by-assume "ExHypy" "y1" "y1Prop")
(intro 0 (pt "0"))
(intro 0 (pt "x1"))
(intro 0 (pt "y1"))
(split)
(use "InitSdtwoMT")
(split)
(use "CoHToCoG")
(use "x1Prop")
(split)
(use "CoHToCoG")
(use "y1Prop")
;;   {x}  {y}  CoGx:CoG x
;;   CoGy:CoG y
;;   {x1}  x1Prop:CoH x1 andl x===(1#2)*x1
;;   {y1}  y1Prop:CoH y1 andl y===(1#2)*y1
;; -----------------------------------------------------------------------------
;; ?_170:(1#2)*(x+y)===(1#4)*(x1+y1+0)
(use "RealEqTrans" (pt "(1#2)*((1#2)*x1+y)"))
(use "RealTimesCompat")
(use "RealEqRefl")
(use "RealRat")
(use "RealPlusCompat")
(use "x1Prop")
(use "RealEqRefl")
(use "CoGToReal")
(use "CoGy")
(use "RealEqTrans" (pt "(1#2)*((1#2)*x1+(1#2)*y1)"))
(use "RealTimesCompat")
(use "RealEqRefl")
(use "RealRat")
(use "RealPlusCompat")
(use "RealEqRefl")
(use "RealTimesReal")
(use "RealRat")
(use "CoHToReal")
(use "x1Prop")
(use "y1Prop")
(use "CoGAvAvcMidMid")
(use "CoHToReal")
(use "x1Prop")
(use "CoHToReal")
(use "y1Prop")
;; Proof finished.
(save "CoGAvToAvc")

(define eterm (proof-to-extracted-term))
(animate "CoGClosure")
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [ag,ag0][case (DesYprod ag)
;;    (InL bg -> [case (DesYprod ag0)
;;      (InL bg0 -> 
;;      cIntPlusPsdToSdtwo clft bg clft bg0 pair 
;;      cCoGPsdTimes crht bg(cPsdUMinus clft bg)pair 
;;      cCoGPsdTimes crht bg0(cPsdUMinus clft bg0))
;;      (InR ah -> 
;;      cPsdToSdtwo clft bg pair 
;;      cCoGPsdTimes crht bg(cPsdUMinus clft bg)pair cCoHToCoG ah)])
;;    (InR ah -> [case (DesYprod ag0)
;;      (InL bg -> 
;;      cPsdToSdtwo clft bg pair 
;;      cCoHToCoG ah pair cCoGPsdTimes crht bg(cPsdUMinus clft bg))
;;      (InR ah0 -> MT pair cCoHToCoG ah pair cCoHToCoG ah0)])]

(deanimate "CoGClosure")

;; RealTimesPlusIntNOneDistrLeft
(set-goal "all d,x(Real x -> (x+IntN 1)* ~d===(x* ~d+d))")
(assert "all d,x (x+IntN 1)* ~d=+=(x* ~d+d)")
(assume "d")
(cases)
(assume "as" "M")
(use "RealEqSIntro")
(assume "n")
(ng)
(simprat "RatTimesPlusDistrLeft")
(ng)
(simp "IntTimesIntNL")
(use "Truth")
;; Assertion proved.
(assume "RealTimesPlusIntNOneDistrLeftEqS" "d" "x" "Rx")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealTimesPlusIntNOneDistrLeftEqS")
;; Proof finished.
(save "RealTimesPlusIntNOneDistrLeft")

;; RealTimesPlusOneDistrLeft
(set-goal "all d,x(Real x -> (x+1)*d===x*d+d)")
(assert "all d,x (x+1)*d=+=x*d+d")
(assume "d")
(cases)
(assume "as" "M")
(use "RealEqSIntro")
(assume "n")
(ng)
(simprat "RatTimesPlusDistrLeft")
(use "RatPlusCompat")
(use "Truth")
(ng)
(use "Truth")
;; Assertion proved.
(assume  "RealTimesPlusOneDistrLeftEqS" "d" "x" "Rx")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealTimesPlusOneDistrLeftEqS")
;; Proof finished.
(save "RealTimesPlusOneDistrLeft")

;; CoGAvUMinus
(set-goal "all d,x(Real x -> (1#2)*(x+IntN 1)* ~d===(1#2)*(x* ~d+d))")
(assume "d" "x" "Rx")
(use "RealEqTrans" (pt "(1#2)*((x+IntN 1)* ~d)"))
(use "RealEqSym")
(use "RealTimesAssoc")
(use "RealRat")
(use "RealPlusReal")
(use "Rx")
(use "RealRat")
(use "RealRat")
(use "RealTimesCompat")
(use "RealEqRefl")
(use "RealRat")
(use "RealTimesPlusIntNOneDistrLeft")
(use "Rx")
;; Proof finished.
(save "CoGAvUMinus")

;; We now need JK.scm

;; SdDisj
(set-goal "allnc d(Sd d -> d=0 orr Psd d)")
(assume "d" "Sdd")
(elim "Sdd")
;; 3-5
(intro 1)
(use "InitPsdTrue")
;; 4
(intro 0)
(use "Truth")
;; 5
(intro 1)
(use "InitPsdFalse")
;; Proof finished.
(save "SdDisj")

;; To avoid case lengthy distinctions and achieve some clarity in the
;; usage of J,K we could employ IntToBoole, BooleToInt, PsdMR and
;; invariance axioms.  However, in the present simple case the latter
;; are easily provable.

;; CoGAvcSatCoIClAuxJ
(set-goal "allnc d,e,i(Psd d -> Psd e -> Sdtwo i -> Sdtwo(J(d+e+i*2)))")
(assume "d" "e" "i" "Psdd" "Psde" "Sdtwoi")
(assert "exl boole1 PsdMR boole1 d")
(use "PsdMRIntro")
(use "Psdd")
(assume "ExHyp1")
(by-assume "ExHyp1" "boole1" "boole1Prop")
(assert "exl boole2 PsdMR boole2 e")
(use "PsdMRIntro")
(use "Psde")
(assume "ExHyp2")
(by-assume "ExHyp2" "boole2" "boole2Prop")
(assert "exl t SdtwoMR t i")
(use "SdtwoMRIntro")
(use "Sdtwoi")
(assume "ExHyp3")
(by-assume "ExHyp3" "t" "tProp")
(use "SdtwoMRElim"
 (pt "IntToSdtwo(J(BooleToInt boole1+BooleToInt boole2+SdtwoToInt t*2))"))
(simp (pf "J(BooleToInt boole1+BooleToInt boole2+SdtwoToInt t*2)=J(d+e+i*2)"))
(use "SdtwoMRIntToSdtwo")
;; ?_27:abs(J(d+e+i*2))<=2
(use "JProp")
(simp (pf "BooleToInt boole1+BooleToInt boole2+SdtwoToInt t*2=d+e+i*2"))
(use "Truth")
;; ?_29:BooleToInt boole1+BooleToInt boole2+SdtwoToInt t*2=d+e+i*2
(inst-with-to "PsdMRId" (pt "d") (pt "boole1") "boole1Prop" "PsdMRIdInst1")
(inst-with-to "PsdMRId" (pt "e") (pt "boole2") "boole2Prop" "PsdMRIdInst2")
(inst-with-to "SdtwoMRId" (pt "i") (pt "t") "tProp" "SdtwoMRIdInst")
(simp "PsdMRIdInst1")
(simp "PsdMRIdInst2")
(simp "SdtwoMRIdInst")
(use "Truth")
;; Proof finished.
(save "CoGAvcSatCoIClAuxJ")

;; CoGAvcSatCoIClAuxK
(set-goal "allnc d,e,i(Psd d -> Psd e -> Sdtwo i -> Sd(K(d+e+i*2)))")
(assume "d" "e" "i" "Psdd" "Psde" "Sdtwoi")
(assert "exl boole1 PsdMR boole1 d")
(use "PsdMRIntro")
(use "Psdd")
(assume "ExHyp1")
(by-assume "ExHyp1" "boole1" "boole1Prop")
(assert "exl boole2 PsdMR boole2 e")
(use "PsdMRIntro")
(use "Psde")
(assume "ExHyp2")
(by-assume "ExHyp2" "boole2" "boole2Prop")
(assert "exl t SdtwoMR t i")
(use "SdtwoMRIntro")
(use "Sdtwoi")
(assume "ExHyp3")
(by-assume "ExHyp3" "t" "tProp")
(use "SdMRElim"
     (pt "IntToSd(K(BooleToInt boole1+BooleToInt boole2+SdtwoToInt t*2))"))
(simp (pf "K(BooleToInt boole1+BooleToInt boole2+SdtwoToInt t*2)=K(d+e+i*2)"))
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
(simp "PsdToAbsOne")
(use "Truth")
(use "Psdd")
(simp "PsdToAbsOne")
(use "Truth")
(use "Psde")
(use "Truth")
(ng #t)
(use "IntLeTrans" (pt "IntP 2*IntP 2"))
(use "IntLeMonTimes")
(use "Truth")
(use "SdtwoBound")
(use "Sdtwoi")
(use "Truth")
(use "Truth")
(simp (pf "BooleToInt boole1+BooleToInt boole2+SdtwoToInt t*2=d+e+i*2"))
(use "Truth")
;; ?_52:BooleToInt boole1+BooleToInt boole2+SdtwoToInt t*2=d+e+i*2
(inst-with-to "PsdMRId" (pt "d") (pt "boole1") "boole1Prop" "PsdMRIdInst1")
(inst-with-to "PsdMRId" (pt "e") (pt "boole2") "boole2Prop" "PsdMRIdInst2")
(inst-with-to "SdtwoMRId" (pt "i") (pt "t") "tProp" "SdtwoMRIdInst")
(simp "PsdMRIdInst1")
(simp "PsdMRIdInst2")
(simp "SdtwoMRIdInst")
(use "Truth")
;; Proof finished.
(save "CoGAvcSatCoIClAuxK")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [boole,boole0,t]
;;  IntToSd(K(BooleToInt boole+BooleToInt boole0+SdtwoToInt t*2))

;; SdtwoPsdToSdtwoJ
(set-goal "allnc i,d(Sdtwo i -> Psd d -> Sdtwo(J(d+i*2)))")
(assume "i" "d" "Sdtwoi")
(elim "Sdtwoi")
;; 3-7
(assume "Psdd")
(elim "Psdd")
;; 9,10
(ng)
(use "InitSdtwoLT")
;; 10
(ng)
(use "InitSdtwoRT")
;; 4
(assume "Psdd")
(elim "Psdd")
;; 14,15
(ng)
(use "InitSdtwoRT")
;; 15
(ng)
(use "InitSdtwoLT")
;; 5
(assume "Psdd")
(elim "Psdd")
;; 19,20
(ng)
(use "InitSdtwoRT")
; 20
(ng)
(use "InitSdtwoLT")
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
(use "InitSdtwoRT")
;; 30
(ng)
(use "InitSdtwoLT")
;; Proof finished.
(save "SdtwoPsdToSdtwoJ")

;; SdtwoToSdtwoJ
(set-goal "allnc i(Sdtwo i -> Sdtwo(J(i*2)))")
(assume "i" "Sdtwoi")
(elim "Sdtwoi")
;; 3-7
(ng)
(use "InitSdtwoRR")
;; 4
(ng)
(use "InitSdtwoMT")
;; 5
(ng)
(use "InitSdtwoMT")
;; 6
(ng)
(use "InitSdtwoLL")
;; 7
(ng)
(use "InitSdtwoMT")
;; Proof finished.
(save "SdtwoToSdtwoJ")

;; SdtwoPsdToSdK
(set-goal "allnc i,d(Sdtwo i -> Psd d -> Sd(K(d+i*2)))")
(assume "i" "d" "Sdtwoi")
(elim "Sdtwoi")
;; 3-7
(assume "Psdd")
(elim "Psdd")
;; 9,10
(ng)
(use "InitSdSdR")
;; 10
(ng)
(use "InitSdSdM")
;; 4
(assume "Psdd")
(elim "Psdd")
;; 14,15
(ng)
(use "InitSdSdR")
;; 15
(ng)
(use "InitSdSdR")
;; 5
(assume "Psdd")
(elim "Psdd")
;; 19,20
(ng)
(use "InitSdSdM")
; 20
(ng)
(use "InitSdSdM")
;; 6
(assume "Psdd")
(elim "Psdd")
;; 24,25
(ng)
(use "InitSdSdM")
;; 25
(ng)
(use "InitSdSdL")
;; 7
(assume "Psdd")
(elim "Psdd")
;; 29,30
(ng)
(use "InitSdSdL")
;; 30
(ng)
(use "InitSdSdL")
;; Proof finished.
(save "SdtwoPsdToSdK")

;; SdtwoToSdK
(set-goal "allnc i(Sdtwo i -> Sd(K(i*2)))")
(assume "i" "Sdtwoi")
(elim "Sdtwoi")
;; 3-7
(ng)
(use "InitSdSdM")
;; 4
(ng)
(use "InitSdSdR")
;; 5
(ng)
(use "InitSdSdM")
;; 6
(ng)
(use "InitSdSdM")
;; 7
(ng)
(use "InitSdSdL")
;; Proof finished.
(save "SdtwoToSdK")

;; CoGAvcSatCoICl
(set-goal "allnc i,x,y(Sdtwo i -> CoG x -> CoG y -> 
 exr j,d,x0,y0(Sdtwo j andi Sd d andi CoG x0 andi CoG y0 andi
 (1#4)*(x+y+i)===(1#2)*((1#4)*(x0+y0+j)+d)))")
(assume "i" "x" "y" "Sdtwoi" "CoGx" "CoGy")
(inst-with-to "CoGClosure" (pt "x") "CoGx" "CoGClosureInstx")
(elim "CoGClosureInstx")
;; 5,6
(drop "CoGClosureInstx")
(assume "CoGClosureInstxLeft")
(by-assume "CoGClosureInstxLeft" "d" "dProp")
(by-assume "dProp" "x1" "dx1Prop")
(inst-with-to "CoGClosure" (pt "y") "CoGy" "CoGClosureInsty")
(elim "CoGClosureInsty")
;; 17,18
(drop "CoGClosureInsty")
(assume "CoGClosureInstyLeft")
(by-assume "CoGClosureInstyLeft" "e" "eProp")
(by-assume "eProp" "y1" "ey1Prop")
(intro 0 (pt "J(d+e+i*2)"))
(intro 0 (pt "K(d+e+i*2)"))
(intro 0 (pt "x1* ~d"))
(intro 0 (pt "y1* ~e"))
(split)
;;   {i}  {x}  {y}  Sdtwoi:Sdtwo i
;;   CoGx:CoG x
;;   CoGy:CoG y
;;   {d}  {x1}  dx1Prop:Psd d andd CoG x1 andl x===(1#2)*(x1+IntN 1)* ~d
;;   {e}  {y1}  ey1Prop:Psd e andd CoG y1 andl y===(1#2)*(y1+IntN 1)* ~e
;; -----------------------------------------------------------------------------
;; ?_31:Sdtwo(J(d+e+i*2))
(use "CoGAvcSatCoIClAuxJ")
(use "dx1Prop")
(use "ey1Prop")
(use "Sdtwoi")
(split)
 ;same for K
(use "CoGAvcSatCoIClAuxK")
(use "dx1Prop")
(use "ey1Prop")
(use "Sdtwoi")
(split)
(use "CoGPsdTimes")
(use "dx1Prop")
(use "PsdUMinus")
(use "dx1Prop")
(split)
(use "CoGPsdTimes")
(use "ey1Prop")
(use "PsdUMinus")
(use "ey1Prop")
;;   {i}  {x}  {y}  Sdtwoi:Sdtwo i
;;   CoGx:CoG x
;;   CoGy:CoG y
;;   {d}  {x1}  dx1Prop:Psd d andd CoG x1 andl x===(1#2)*(x1+IntN 1)* ~d
;;   {e}  {y1}  ey1Prop:Psd e andd CoG y1 andl y===(1#2)*(y1+IntN 1)* ~e
;; -----------------------------------------------------------------------------
;; ?_47:(1#4)*(x+y+i)===(1#2)*((1#4)*(x1* ~d+y1* ~e+J(d+e+i*2))+K(d+e+i*2))
(use "RealEqTrans" (pt "(1#4)*((1#2)*(x1* ~d+d)+(1#2)*(y1* ~e+e)+i)"))
(use "RealTimesCompat")
(use "RealEqRefl")
(use "RealRat")
(use "RealPlusCompat")
(use "RealPlusCompat")
(use "RealEqTrans" (pt "(1#2)*(x1+IntN 1)* ~d"))
(use "dx1Prop")
(use "CoGAvUMinus")
(use "CoGToReal")
(use "dx1Prop")
(use "RealEqTrans" (pt "(1#2)*(y1+IntN 1)* ~e"))
(use "ey1Prop")
(use "CoGAvUMinus")
(use "CoGToReal")
(use "ey1Prop")
(use "RealEqRefl")
(use "RealRat")
;;   {i}  {x}  {y}  Sdtwoi:Sdtwo i
;;   CoGx:CoG x
;;   CoGy:CoG y
;;   {d}  {x1}  dx1Prop:Psd d andd CoG x1 andl x===(1#2)*(x1+IntN 1)* ~d
;;   {e}  {y1}  ey1Prop:Psd e andd CoG y1 andl y===(1#2)*(y1+IntN 1)* ~e
;; -----------------------------------------------------------------------------
;; ?_52:(1#4)*((1#2)*(x1* ~d+d)+(1#2)*(y1* ~e+e)+i)===
;;      (1#2)*((1#4)*(x1* ~d+y1* ~e+J(d+e+i*2))+K(d+e+i*2))
(use "CoIAvcSatCoIClAux")
(use "RealTimesReal")
(use "CoGToReal")
(use "dx1Prop")
(use "RealRat")
(use "RealTimesReal")
(use "CoGToReal")
(use "ey1Prop")
(use "RealRat")
;; 18
(drop "CoGClosureInsty")
(assume "CoGClosureInstyRight")
(by-assume "CoGClosureInstyRight" "y1" "y1Prop")
(intro 0 (pt "J(d+i*2)"))
(intro 0 (pt "K(d+i*2)"))
(intro 0 (pt "x1* ~d"))
(intro 0 (pt "y1"))
(split)
;; ?_86:Sdtwo(J(d+i*2))
(use "SdtwoPsdToSdtwoJ")
(use "Sdtwoi")
(use "dx1Prop")
(split)
;; ?_90:Sd(K(d+i*2))
(use "SdtwoPsdToSdK")
(use "Sdtwoi")
(use "dx1Prop")
(split)
(use "CoGPsdTimes")
(use "dx1Prop")
(use "PsdUMinus")
(use "dx1Prop")
(split)
(use "CoHToCoG")
(use "y1Prop")
;;   {i}  {x}  {y}  Sdtwoi:Sdtwo i
;;   CoGx:CoG x
;;   CoGy:CoG y
;;   {d}  {x1}  dx1Prop:Psd d andd CoG x1 andl x===(1#2)*(x1+IntN 1)* ~d
;;   {y1}  y1Prop:CoH y1 andl y===(1#2)*y1
;; -----------------------------------------------------------------------------
;; ?_100:(1#4)*(x+y+i)===(1#2)*((1#4)*(x1* ~d+y1+J(d+i*2))+K(d+i*2))

;; We had CoIAvcSatCoIClAux
;; "all x,y,d,e,i(Real x -> Real y ->
;;  (1#4)*((1#2)*(x+d)+(1#2)*(y+e)+i)===
;;  (1#2)*((1#4)*(x+y+J(d+e+i*2))+K(d+e+i*2)))"
;; Strategy for uses of CoIAvcSatCoIClAux : using RealEqTrans bring
;; the goal in in the form required by CoIAvcSatCoIClAux .  Then use
;; CoGAvUMinus and RealPlusZero to prove the rest.
(use "RealEqTrans" (pt "(1#4)*((1#2)*(x1* ~d+d)+(1#2)*(y1+0)+i)"))
(use "RealTimesCompat")
(use "RealEqRefl")
(use "RealRat")
(use "RealPlusCompat")
(use "RealPlusCompat")
(use "RealEqTrans" (pt "(1#2)*(x1+IntN 1)* ~d"))
(use "dx1Prop")
(use "CoGAvUMinus")
(use "CoGToReal")
(use "dx1Prop")
(use "RealEqTrans" (pt "(1#2)*y1"))
(use "y1Prop")
(use "RealTimesCompat")
(use "RealEqRefl")
(use "RealRat")
(use "RealEqSym")
(use "RealPlusZero")
(use "CoHToReal")
(use "y1Prop")
(use "RealEqRefl")
(use "RealRat")
;;   {i}  {x}  {y}  Sdtwoi:Sdtwo i
;;   CoGx:CoG x
;;   CoGy:CoG y
;;   {d}  {x1}  dx1Prop:Psd d andd CoG x1 andl x===(1#2)*(x1+IntN 1)* ~d
;;   {y1}  y1Prop:CoH y1 andl y===(1#2)*y1
;; -----------------------------------------------------------------------------
;; ?_103:(1#4)*((1#2)*(x1* ~d+d)+(1#2)*(y1+0)+i)===
;;       (1#2)*((1#4)*(x1* ~d+y1+J(d+i*2))+K(d+i*2))
(use-with "CoIAvcSatCoIClAux" (pt "x1* ~d") (pt "y1") (pt "d")
	  (pt "0") (pt "i") "?" "?")
(use "RealTimesReal")
(use "CoGToReal")
(use "dx1Prop")
(use "RealRat")
(use "CoHToReal")
(use "y1Prop")
;; 6
(drop "CoGClosureInstx")
(assume "CoGClosureInstxRight")
(by-assume "CoGClosureInstxRight" "x1" "x1Prop")
(inst-with-to "CoGClosure" (pt "y") "CoGy" "CoGClosureInsty")
(elim "CoGClosureInsty")
;; 137,138
(drop "CoGClosureInsty")
(assume "CoGClosureInstyLeft")
(by-assume "CoGClosureInstyLeft" "e" "eProp")
(by-assume "eProp" "y1" "ey1Prop")
(intro 0 (pt "J(e+i*2)"))
(intro 0 (pt "K(e+i*2)"))
(intro 0 (pt "x1"))
(intro 0 (pt "y1* ~e"))
(split)
;; ?_151:Sdtwo(J(e+i*2))
(use "SdtwoPsdToSdtwoJ")
(use "Sdtwoi")
(use "ey1Prop")
(split)
;; ?_155:Sd(K(e+i*2))
(use "SdtwoPsdToSdK")
(use "Sdtwoi")
(use "ey1Prop")
(split)
(use "CoHToCoG")
(use "x1Prop")
(split)
(use "CoGPsdTimes")
(use "ey1Prop")
(use "PsdUMinus")
(use "ey1Prop")
;;   {i}  {x}  {y}  Sdtwoi:Sdtwo i
;;   CoGx:CoG x
;;   CoGy:CoG y
;;   {x1}  x1Prop:CoH x1 andl x===(1#2)*x1
;;   {e}  {y1}  ey1Prop:Psd e andd CoG y1 andl y===(1#2)*(y1+IntN 1)* ~e
;; -----------------------------------------------------------------------------
;; ?_163:(1#4)*(x+y+i)===(1#2)*((1#4)*(x1+y1* ~e+J(e+i*2))+K(e+i*2))
(use "RealEqTrans" (pt "(1#4)*((1#2)*(x1+0)+(1#2)*(y1* ~e+e)+i)"))
(use "RealTimesCompat")
(use "RealEqRefl")
(use "RealRat")
(use "RealPlusCompat")
(use "RealPlusCompat")
(use "RealEqTrans" (pt "(1#2)*x1"))
(use "x1Prop")
(use "RealTimesCompat")
(use "RealEqRefl")
(use "RealRat")
(use "RealEqSym")
(use "RealPlusZero")
(use "CoHToReal")
(use "x1Prop")
(use "RealEqTrans" (pt "(1#2)*(y1+IntN 1)* ~e"))
(use "ey1Prop")
(use "CoGAvUMinus")
(use "CoGToReal")
(use "ey1Prop")
(use "RealEqRefl")
(use "RealRat")
;;   {i}  {x}  {y}  Sdtwoi:Sdtwo i
;;   CoGx:CoG x
;;   CoGy:CoG y
;;   {x1}  x1Prop:CoH x1 andl x===(1#2)*x1
;;   {e}  {y1}  ey1Prop:Psd e andd CoG y1 andl y===(1#2)*(y1+IntN 1)* ~e
;; -----------------------------------------------------------------------------
;; ?_168:(1#4)*((1#2)*(x1+0)+(1#2)*(y1* ~e+e)+i)===
;;       (1#2)*((1#4)*(x1+y1* ~e+J(e+i*2))+K(e+i*2))

(use-with "CoIAvcSatCoIClAux" (pt "x1") (pt "y1* ~e") (pt "0")
	  (pt "e") (pt "i") "?" "?")
(use "CoHToReal")
(use "x1Prop")
(use "RealTimesReal")
(use "CoGToReal")
(use "ey1Prop")
(use "RealRat")
;; 138
(drop "CoGClosureInsty")
(assume  "CoGClosureInstyRight")
(by-assume  "CoGClosureInstyRight" "y1" "y1Prop")
(intro 0 (pt "J(i*2)"))
(intro 0 (pt "K(i*2)"))
(intro 0 (pt "x1"))
(intro 0 (pt "y1"))
(split)
;; ?_204:Sdtwo(J(i*2))
(use "SdtwoToSdtwoJ")
(use "Sdtwoi")
(split)
;; ?_207:Sd(K(i*2))
(use "SdtwoToSdK")
(use "Sdtwoi")
(split)
(use "CoHToCoG")
(use "x1Prop")
(split)
(use "CoHToCoG")
(use "y1Prop")
;;   {i}  {x}  {y}  Sdtwoi:Sdtwo i
;;   CoGx:CoG x
;;   CoGy:CoG y
;;   {x1}  x1Prop:CoH x1 andl x===(1#2)*x1
;;   {y1}  y1Prop:CoH y1 andl y===(1#2)*y1
;; -----------------------------------------------------------------------------
;; ?_214:(1#4)*(x+y+i)===(1#2)*((1#4)*(x1+y1+J(i*2))+K(i*2))
(use "RealEqTrans" (pt "(1#4)*((1#2)*(x1+0)+(1#2)*(y1+0)+i)"))
(use "RealTimesCompat")
(use "RealEqRefl")
(use "RealRat")
(use "RealPlusCompat")
(use "RealPlusCompat")
(use "RealEqTrans" (pt "(1#2)*x1"))
(use "x1Prop")
(use "RealTimesCompat")
(use "RealEqRefl")
(use "RealRat")
(use "RealEqSym")
(use "RealPlusZero")
(use "CoHToReal")
(use "x1Prop")
(use "RealEqTrans" (pt "(1#2)*y1"))
(use "y1Prop")
(use "RealTimesCompat")
(use "RealEqRefl")
(use "RealRat")
(use "RealEqSym")
(use "RealPlusZero")
(use "CoHToReal")
(use "y1Prop")
(use "RealEqRefl")
(use "RealRat")
;;   {i}  {x}  {y}  Sdtwoi:Sdtwo i
;;   CoGx:CoG x
;;   CoGy:CoG y
;;   {x1}  x1Prop:CoH x1 andl x===(1#2)*x1
;;   {y1}  y1Prop:CoH y1 andl y===(1#2)*y1
;; -----------------------------------------------------------------------------
;; 217:(1#4)*((1#2)*(x1+0)+(1#2)*(y1+0)+i)===(1#2)*((1#4)*(x1+y1+J(i*2))+K(i*2))

(use-with "CoIAvcSatCoIClAux"  (pt "x1") (pt "y1") (pt "0") (pt "0") (pt "i")
	  "?" "?")
(use "CoHToReal")
(use "x1Prop")
(use "CoHToReal")
(use "y1Prop")
;; Proof finished.
(save "CoGAvcSatCoICl")

(define eterm (proof-to-extracted-term))
(animate "CoGClosure")
(animate "CoGAvcSatCoIClAuxJ")
(animate "CoGAvcSatCoIClAuxK")
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [t,ag,ag0][case (DesYprod ag)
;;    (InL bg -> [case (DesYprod ag0)
;;      (InL bg0 -> IntToSdtwo(J(BooleToInt clft bg+
;;                               BooleToInt clft bg0+
;;                               SdtwoToInt t*2))pair 
;;                  IntToSd(K(BooleToInt clft bg+
;;                            BooleToInt clft bg0+
;;                            SdtwoToInt t*2))pair 
;;      cCoGPsdTimes crht bg(cPsdUMinus clft bg)pair 
;;      cCoGPsdTimes crht bg0(cPsdUMinus clft bg0))
;;      (InR ah -> cSdtwoPsdToSdtwoJ t clft bg pair 
;;                 cSdtwoPsdToSdK t clft bg pair 
;;                 cCoGPsdTimes crht bg(cPsdUMinus clft bg)pair
;;                 cCoHToCoG ah)])
;;    (InR ah -> [case (DesYprod ag0)
;;      (InL bg -> cSdtwoPsdToSdtwoJ t clft bg pair 
;;                 cSdtwoPsdToSdK t clft bg pair 
;;                 cCoHToCoG ah pair
;;                 cCoGPsdTimes crht bg(cPsdUMinus clft bg))
;;      (InR ah0 -> cSdtwoToSdtwoJ t pair 
;;                  cSdtwoToSdK t pair
;;                  cCoHToCoG ah pair
;;                  cCoHToCoG ah0)])]

(deanimate "CoGClosure")
(deanimate "CoGAvcSatCoIClAuxJ")
(deanimate "CoGAvcSatCoIClAuxK")

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
(realproof)
(realproof)
(use "RealTimesPsdPsdEqS")
(use "Psdd")
;; Proof finished.
(save "RealTimesPsdPsd")

;; Putting things together

;; CoGAvcToCoG
(set-goal "allnc z(
 exr i,x,y(Sdtwo i andi CoG x andi CoG y andi z===(1#4)*(x+y+i)) -> CoG z)")
(assume "z" "Qz")
(coind "Qz" (pf "exr i,x,y
          (Sdtwo i andi CoG x andi CoG y andi z===(1#4)*(x+y+i)) -> CoH z"))
;; 3,4
(assume "z1" "Qz1")
(by-assume "Qz1" "i" "iProp")
(by-assume "iProp" "x" "ixProp")
(by-assume "ixProp" "y" "ixyProp")
;; let introduction
(cut "exr j,d,x0,y0(Sdtwo j andi Sd d andi CoG x0 andi CoG y0 andi
 (1#4)*(x+y+i)===(1#2)*((1#4)*(x0+y0+j)+d))")
;; 15,16
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "ExCoGAvcSatCoICl")
(by-assume "ExCoGAvcSatCoICl" "i1" "i1Prop")
(by-assume "i1Prop" "d1" "i1d1Prop")
(by-assume "i1d1Prop" "x1" "i1d1x1Prop")
(by-assume "i1d1x1Prop" "y1" "i1d1x1y1Prop")
(assert "Sdtwo i1")
(use "i1d1x1y1Prop")
(assume "Sdtwoi1")
(assert "CoG x1")
(use "i1d1x1y1Prop")
(assume "CoGx1")
(assert "CoG y1")
(use "i1d1x1y1Prop")
(assume "CoGy1")
(assert "(1#4)*(x+y+i)===(1#2)*((1#4)*(x1+y1+i1)+d1)")
(use "i1d1x1y1Prop")
(assume "Eq")
(drop "i1d1x1y1Prop")
(assert "d1=0 orr Psd d1")
 (use-with "SdDisj" (pt "d1") "?")
 (use "i1d1x1y1Prop")
(assume "Disj")
(elim "Disj")
;; 47,48
(drop "Disj")
(assume "d1=0") ;case small
(intro 1)
(intro 0 (pt "(1#4)*(x1+y1+i1)"))
(intro 0 (pt "z1"))
(split)
(realproof)
(split)
(intro 1)
(intro 0 (pt "i1"))
(intro 0 (pt "x1"))
(intro 0 (pt "y1"))
(split)
(use "Sdtwoi1")
(split)
(use "CoGx1")
(split)
(use "CoGy1")
(use "RealEqRefl")
(realproof)
(split)
(simpreal "ixyProp")
(simpreal "Eq")
;; ?_73:(1#2)*((1#4)*(x1+y1+i1)+d1)===(1#2)*((1#4)*(x1+y1+i1))
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y1"))
(assume "bs" "N" "y1Def")
(cases (pt "z1"))
(assume "cs" "L" "z1Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
(simp "d1=0")
(use "Truth")
;; ?_71:z1===z1
(use "RealEqRefl")
(use "RealEqElim0" (pt "(1#4)*(x+y+i)"))
(use "ixyProp")
;; 49
(drop "Disj")
(assume "Psdd1")
(intro 0)
(intro 0 (pt "d1"))
(intro 0 (pt "(1#4)*(x1* ~d1+y1* ~d1+RealTimes i1~d1)"))
(intro 0 (pt "z1"))
(split)
(use "Psdd1")
(split)
(realproof)
(split)
(intro 1)
(intro 0 (pt "i1* ~d1"))
(intro 0 (pt "x1* ~d1"))
(intro 0 (pt "y1* ~d1"))
(split)
(use "IntTimesSdtwoPsdToSdtwo")
(use "Sdtwoi1")
(use "PsdUMinus")
(use "Psdd1")
(split)
(use "CoGPsdTimes")
(use "CoGx1")
(use "PsdUMinus")
(use "Psdd1")
(split)
(use "CoGPsdTimes")
(use "CoGy1")
(use "PsdUMinus")
(use "Psdd1")
;; ?_116:(1#4)*(x1* ~d1+y1* ~d1+RealTimes i1~d1)===
;;       (1#4)*(x1* ~d1+y1* ~d1+i1* ~d1)
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y1"))
(assume "bs" "N" "y1Def")
(cases (pt "z1"))
(assume "cs" "L" "z1Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
(use "Truth")
;; ?_100:z1===(1#2)*((1#4)*(x1* ~d1+y1* ~d1+RealTimes i1~d1)+IntN 1)* ~d1 andnc 
;;       z1===z1
(split)
(simpreal "ixyProp")
(simpreal "Eq")
;; ?_135:(1#2)*((1#4)*(x1+y1+i1)+d1)===
;;       (1#2)*((1#4)*(x1* ~d1+y1* ~d1+RealTimes i1~d1)+IntN 1)* ~d1
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
;; ?_145:(1#2)*((1#4)*(as n+bs n+i1)+d1)== 
;;       ~((1#2)*((1#4)*(~(as n*d1)+ ~(bs n*d1)+ ~(i1*d1))+IntN 1)*d1)
(simp (pf "~(i1*d1)=RatUMinus(RatTimes i1 d1)"))
(simp (pf "(IntN 1#1)= ~(1#1)"))
(simp "<-" "RatUMinus2RewRule")
(simp "<-" "RatUMinus2RewRule")
(simp "RatTimes3RewRule")
(simp "<-" "RatUMinus2RewRule")
(simp "RatTimes3RewRule")
(simp "RatTimes4RewRule")
(simp "RatUMinus1RewRule")
;; ?_156:(1#2)*((1#4)*(as n+bs n+i1)+d1)==
;;       (1#2)*((1#4)*(as n*d1+bs n*d1+RatTimes i1 d1)+1)*d1
(simp "<-" "RatTimesAssoc")
(simp "RatEqv6RewRule")
(simprat "RatTimesPlusDistrLeft")
(simp "<-" "RatTimesAssoc")
(simprat "RatTimesPlusDistrLeft")
(simprat "RatTimesPlusDistrLeft")
(ng)
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimesAssoc")
(simp "<-" "IntTimesAssoc")
(simp (pf "RatTimes d1 d1=d1*d1"))
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
(use "Truth")
(use "Truth")
;; ?_133:z1===z1
(use "RealEqRefl")
(use "RealEqElim0" (pt "(1#4)*(x+y+i)"))
(use "ixyProp")

;; ?_16:exr j,d,x0,y0(
;;       Sdtwo j andd 
;;       Sd d andd 
;;       CoG x0 andd CoG y0 andl (1#4)*(x+y+i)===(1#2)*((1#4)*(x0+y0+j)+d))

;; Now we prove the formula cut in above, using CoGAvcSatCoICl
(use "CoGAvcSatCoICl")
(use "ixyProp")
(use "ixyProp")
(use "ixyProp")
;; 4
(assume "z1" "Qz1")
(by-assume "Qz1" "i" "iProp")
(by-assume "iProp" "x" "ixProp")
(by-assume "ixProp" "y" "ixyProp")
;; let introduction
(cut "exr j,d,x0,y0(Sdtwo j andi Sd d andi CoG x0 andi CoG y0 andi
 (1#4)*(x+y+i)===(1#2)*((1#4)*(x0+y0+j)+d))")
;; 192,193
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "ExCoGAvcSatCoICl")
(by-assume "ExCoGAvcSatCoICl" "i1" "i1Prop")
(by-assume "i1Prop" "d1" "i1d1Prop")
(by-assume "i1d1Prop" "x1" "i1d1x1Prop")
(by-assume "i1d1x1Prop" "y1" "i1d1x1y1Prop")
(assert "Sdtwo i1")
(use "i1d1x1y1Prop")
(assume "Sdtwoi1")
(assert "CoG x1")
(use "i1d1x1y1Prop")
(assume "CoGx1")
(assert "CoG y1")
(use "i1d1x1y1Prop")
(assume "CoGy1")
(assert "(1#4)*(x+y+i)===(1#2)*((1#4)*(x1+y1+i1)+d1)")
(use "i1d1x1y1Prop")
(assume "Eq")
(drop "i1d1x1y1Prop")
(assert "d1=0 orr Psd d1")
 (use-with "SdDisj" (pt "d1") "?")
 (use "i1d1x1y1Prop")
(assume "Disj")
(elim "Disj")
;; 225,226
(drop "Disj")
(assume "d1=0") ;case small
(intro 1)
(intro 0 (pt "(1#4)*(x1+y1+i1)"))
(intro 0 (pt "z1"))
(split)
(realproof)
(split)
(intro 1)
(intro 0 (pt "i1"))
(intro 0 (pt "x1"))
(intro 0 (pt "y1"))
(split)
(use "Sdtwoi1")
(split)
(use "CoGx1")
(split)
(use "CoGy1")
(use "RealEqRefl")
(realproof)
(split)
(simpreal "ixyProp")
(simpreal "Eq")
;; ?_250:(1#2)*((1#4)*(x1+y1+i1)+d1)===(1#2)*((1#4)*(x1+y1+i1))
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y1"))
(assume "bs" "N" "y1Def")
(cases (pt "z1"))
(assume "cs" "L" "z1Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
(simp "d1=0")
(use "Truth")
;; ?_248:z1===z1
(use "RealEqRefl")
(use "RealEqElim0" (pt "(1#4)*(x+y+i)"))
(use "ixyProp")
;; 226
(drop "Disj")
(assume "Psdd1")
(intro 0)
(intro 0 (pt "d1"))
(intro 0 (pt "(1#4)*(x1*d1+y1*d1+RealTimes i1 d1)"))
(intro 0 (pt "z1"))
(split)
(use "Psdd1")
(split)
(realproof)
(split)
(intro 1)
(intro 0 (pt "i1*d1"))
(intro 0 (pt "x1*d1"))
(intro 0 (pt "y1*d1"))
(split)
(use "IntTimesSdtwoPsdToSdtwo")
(use "Sdtwoi1")
(use "Psdd1")
(split)
(use "CoGPsdTimes")
(use "CoGx1")
(use "Psdd1")
(split)
(use "CoGPsdTimes")
(use "CoGy1")
(use "Psdd1")
;; ?_291:(1#4)*(x1*d1+y1*d1+RealTimes i1 d1)===(1#4)*(x1*d1+y1*d1+i1*d1)
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x1"))
(assume "as" "M" "x1Def")
(cases (pt "y1"))
(assume "bs" "N" "y1Def")
(cases (pt "z1"))
(assume "cs" "L" "z1Def")
(use "RealEqSIntro")
(assume "n")
(ng #t)
(use "Truth")
;; ?_277:z1===(1#2)*((1#4)*(x1*d1+y1*d1+RealTimes i1 d1)+1)*d1 andnc z1===z1
(split)
(simpreal "ixyProp")
(simpreal "Eq")
;; ?_309:(1#2)*((1#4)*(x1+y1+i1)+d1)===
;;       (1#2)*((1#4)*(x1*d1+y1*d1+RealTimes i1 d1)+1)*d1
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
;; ?_319:(1#2)*((1#4)*(as n+bs n+i1)+d1)==
;;       (1#2)*((1#4)*(as n*d1+bs n*d1+i1*d1)+1)*d1
(simp "<-" "RatTimesAssoc")
(simp "RatEqv6RewRule")
;; ?_321:(1#4)*(as n+bs n+i1)+d1==((1#4)*(as n*d1+bs n*d1+i1*d1)+1)*d1
(simprat "RatTimesPlusDistrLeft")
(simp (pf "RatTimes 1 d1=(d1#1)"))
(simp "RatEqv3RewRule")
;; ?_325:(1#4)*(as n+bs n+i1)==(1#4)*(as n*d1+bs n*d1+i1*d1)*d1
(simp "<-" "RatTimesAssoc")
(simprat "RatTimesPlusDistrLeft")
(simprat "RatTimesPlusDistrLeft")
(simp "<-" "RatTimesAssoc")
(simp "<-" "RatTimesAssoc")
(ng #t)
;; ?_331:as n+bs n+i1==as n*(d1*d1)+bs n*(d1*d1)+i1*d1*d1
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
;; ?_307:z1===z1
(use "RealEqRefl")
(use "RealEqElim0" (pt "(1#4)*(x+y+i)"))
(use "ixyProp")

;; ?_193:exr j,d,x0,y0(
;;        Sdtwo j andd 
;;        Sd d andd 
;;        CoG x0 andd CoG y0 andl (1#4)*(x+y+i)===(1#2)*((1#4)*(x0+y0+j)+d))

;; Now we prove the formula cut in above, using CoGAvcSatCoICl
(use "CoGAvcSatCoICl")
(use "ixyProp")
(use "ixyProp")
(use "ixyProp")
;; Proof finished.
(save "CoGAvcToCoG")

;; cCoGAvcToCoG: sdtwo yprod ag yprod ag=>ag

(define eterm (proof-to-extracted-term))
(add-var-name "gg" (py "ag yprod ag"))
(add-var-name "tgg" (py "sdtwo yprod ag yprod ag"))
(add-var-name "sgg" (py "sd yprod ag yprod ag"))
(add-var-name "tsgg" (py "sdtwo yprod sd yprod ag yprod ag"))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [tgg](CoRec sdtwo yprod ag yprod ag=>ag 
;;             sdtwo yprod ag yprod ag=>ah)tgg
;;  ([tgg0][let tsgg
;;      (cCoGAvcSatCoICl clft tgg0 clft crht tgg0 crht crht tgg0)
;;      [case (cSdDisj clft crht tsgg)
;;       (DummyL -> InR(InR(clft tsgg pair crht crht tsgg)))
;;       (Inr boole -> InL(boole pair InR
;;        (cIntTimesSdtwoPsdToSdtwo clft tsgg(cPsdUMinus boole)pair 
;;         cCoGPsdTimes clft crht crht tsgg(cPsdUMinus boole)pair 
;;         cCoGPsdTimes crht crht crht tsgg(cPsdUMinus boole))))]])
;;  ([tgg0][let tsgg
;;      (cCoGAvcSatCoICl clft tgg0 clft crht tgg0 crht crht tgg0)
;;      [case (cSdDisj clft crht tsgg)
;;       (DummyL -> InR(InR(clft tsgg pair crht crht tsgg)))
;;       (Inr boole -> 
;;       InL(boole pair InR
;;        (cIntTimesSdtwoPsdToSdtwo clft tsgg boole pair 
;;         cCoGPsdTimes clft crht crht tsgg boole pair 
;;         cCoGPsdTimes crht crht crht tsgg boole)))]])

;; CoGAverage
(set-goal "allnc x,y(CoG x -> CoG y -> CoG((1#2)*(x+y)))")
(assume "x" "y" "CoGx" "CoGy")
(use "CoGAvcToCoG")
(use "CoGAvToAvc")
(use "CoGx")
(use "CoGy")
;; Proof finished.
(save "CoGAverage")

(define eterm (proof-to-extracted-term))
(define neterm-CoGAverage (rename-variables (nt eterm)))
(pp neterm-CoGAverage)

;; [ag,ag0]cCoGAvcToCoG(cCoGAvToAvc ag ag0)

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
(use "RealEqSToEq")
(use "RealRat")
(realproof)
(use "RealEqSIntro")
(assume "n")
(ng)
(use "Truth")
(use "y1Prop")
;; 4
(assume "y" "CoH-ExHyp")
(intro 1)
(by-assume "CoG-ExHyp" "x1" "x1Prop")
(by-assume "CoH-ExHyp" "y1" "y1Prop")
(intro 0 (pt "x1"))
(intro 0 (pt "y1"))
(split)
(use "x1Prop")
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
(use "RealEqSToEq")
(use "RealRat")
(realproof)
(use "RealEqSIntro")
(assume "n")
(ng)
(use "Truth")
(use "y1Prop")
;; Assertion proved.
(assume "Assertion")
(use "Assertion")
(intro 0 (pt "RealConstr([n](0#1))([p]Zero)"))
(split)
(use "RealRat")
(split)
(use "RealEqRefl")
(use "RealRat")
(use "RealEqRefl")
(use "RealRat")
;; Proof finished.
(save "CoGZero")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; (CoRec rea=>ag rea=>ah)0([x]InR(InR 0))([x]InR(InR 0))

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

;; Putting things together

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
(realproof)
(split)
(simpreal "ixyzProp")
(simpreal "Eq")
;;   d1=0:d1=0
;; -----------------------------------------------------------------------------
;; ?_85:(1#2)*((1#4)*(x1*y+z1+i1)+d1)===(1#2)*((1#4)*(x1*y+z1+i1))
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
;; ?_83:z2===z2
(use "RealEqRefl")
(use "RealEqElim0" (pt "(1#4)*(x*y+z+i)"))
(use "ixyzProp")
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
(realproof)
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
;; ?_131:(1#4)*(x1*y* ~d1+z1* ~d1+RealTimes i1~d1)===
;;       (1#4)*(x1*(y* ~d1)+z1* ~d1+i1* ~d1)
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
;;?_112:z2===(1#2)*((1#4)*(x1*y* ~d1+z1* ~d1+RealTimes i1~d1)+IntN 1)* ~d1 andnc 
;;       z2===z2
(split)
(simpreal "ixyzProp")
(simpreal "Eq")
;; ?_150:(1#2)*((1#4)*(x1*y+z1+i1)+d1)===
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
;; ?_162:(1#2)*((1#4)*(as n*bs n+cs n+i1)+d1)== 
;;       ~((1#2)*((1#4)*(~(as n*bs n*d1)+ ~(cs n*d1)+ ~(i1*d1))+IntN 1)*d1)
(simp "<-" "RatTimes3RewRule")
(display-pconst "RatTimes")
(simp "<-" "RatTimesAssoc")
(use "RatTimesCompat")
(use "Truth")
;; ?_166:(1#4)*(as n*bs n+cs n+i1)+d1==
;;       ((1#4)*(~(as n*bs n*d1)+ ~(cs n*d1)+ ~(i1*d1))+IntN 1)* ~d1
(simp "<-" "RatTimesAssoc")
(simprat "RatTimesPlusDistrLeft")
(simp "RatTimesIntNL")
(use "RatPlusCompat")
;; ?_170:(1#4)*(as n*bs n+cs n+i1)==
;;       (1#4)*(~(as n*(bs n*d1))+ ~(cs n*d1)+ ~(i1*d1))* ~d1

;; ?_169:(1#4)*(as n*bs n+cs n+i1)==
;;       (1#4)*(as n*(bs n* ~d1)+cs n* ~d1+ ~(i1*d1))* ~d1
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
;; ?_148:z2===z2
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
;; 250,251
(drop "Disj")
(assume "d1=0") ;case small
(intro 1)
(intro 0 (pt "(1#4)*(x1*y+z1+i1)"))
(intro 0 (pt "z2"))
(split)
(realproof)
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
(realproof)
(split)
(simpreal "ixyzProp")
(simpreal "Eq")
;;   d1=0:d1=0
;; -----------------------------------------------------------------------------
;; ?_276:(1#2)*((1#4)*(x1*y+z1+i1)+d1)===(1#2)*((1#4)*(x1*y+z1+i1))
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
;; ?_276:z2===z2
(use "RealEqRefl")
(use "RealEqElim0" (pt "(1#4)*(x*y+z+i)"))
(use "ixyzProp")
;; 251
(drop "Disj")
(assume "Psdd1")
(intro 0)
(intro 0 (pt "d1"))
(intro 0 (pt "(1#4)*(x1*y* d1+z1* d1+RealTimes i1 d1)"))
(intro 0 (pt "z2"))
(split)
(use "Psdd1")
(split)
(realproof)
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
;; ?_322:(1#4)*(x1*y*d1+z1*d1+RealTimes i1 d1)===(1#4)*(x1*(y*d1)+z1*d1+i1*d1)
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
;; ?_305:z2===(1#2)*((1#4)*(x1*y*d1+z1*d1+RealTimes i1 d1)+1)*d1 andnc z2===z2
(split)
(simpreal "ixyzProp")
(simpreal "Eq")
;; ?_340:(1#2)*((1#4)*(x1*y+z1+i1)+d1)===
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
;; ?_355:(1#4)*(as n*bs n+cs n+i1)+d1==((1#4)*(as n*bs n*d1+cs n*d1+i1*d1)+1)*d1
(simp "<-" "RatTimesAssoc")
(simprat "RatTimesPlusDistrLeft")
(use "RatPlusCompat")
;; ?_358:(1#4)*(as n*bs n+cs n+i1)==(1#4)*(as n*(bs n*d1)+cs n*d1+i1*d1)*d1
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
;; ?_338:z2===z2
(use "RealEqRefl")
(use "RealEqElim0" (pt "(1#4)*(x*y+z+i)"))
(use "ixyzProp")

;; ?_215:exr d,j,x0,z0(
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
