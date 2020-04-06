;; 2020-04-06.  examples/analysis/sdcode.scm

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

;; This adds the c.r. predicate TotalAi of type ai with clause
;; TotalAiC:	allnc s^(TotalSd s^ -> allnc u^(TotalAi u^ -> TotalAi(C s^ u^)))

(add-totalnc "ai")
(add-co "TotalAi")
(add-co "TotalAiNc")

(add-mr-ids "TotalAi")
(add-co "TotalAiMR")

;; We add pointwise equality EqPAi and EqPAiNc (c.r. and n.c. versions)
;; for ai, and also their companion predicates CoEqPAi and CoEqPAiNc

(add-eqp "ai")
(add-eqpnc "ai")
(add-co "EqPAi")
(add-co "EqPAiNc")

(add-mr-ids "EqPAi")
(add-co "EqPAiMR")

;; Later in the soundness proof when InvarAll is used we will need
;; CoEqPAiNcSym
;; CoEqPAiNcTrans
;; CoEqPAiNcReflLeft

;; EqPSdNcSym
(set-goal "allnc s^1,s^2(EqPSdNc s^1 s^2 -> EqPSdNc s^2 s^1)")
(assume "s^1" "s^2" "EqPSdNcs1s2")
(elim "EqPSdNcs1s2")
(use "EqPSdNcSdR")
(use "EqPSdNcSdM")
(use "EqPSdNcSdL")
;; Proof finished.
;; (cdp)
(save "EqPSdNcSym")

;; CoEqPAiNcSym
(set-goal "allnc u^1,u^2(CoEqPAiNc u^1 u^2 -> CoEqPAiNc u^2 u^1)")
(assume "u^1" "u^2" "u1~u2")
(coind "u1~u2")
(assume "u^3" "u^4" "u4~u3")
(inst-with-to
 (make-proof-in-aconst-form
  (coidpredconst-to-closure-aconst
   (predicate-form-to-predicate (pf "CoEqPAiNc u^2 u^1"))))
 (pt "u^4") (pt "u^3") "u4~u3" "Inst")
(elim "Inst")
;; 7
(drop "Inst")
(assume "s^1" "ExHyp")
(by-assume "ExHyp" "s^2" "Conj")
(elim "Conj")
(drop "Conj")
(assume "EqPs1s2" "ExHyp1")
(by-assume "ExHyp1" "u^5" "u5Prop")
(by-assume "u5Prop" "u^6" "Conj1")
(elim "Conj1")
(drop "Conj1")
(assume "CoEqPu5u6" "Conj2")
(elim "Conj2")
(drop "Conj2")
(assume "u4Def" "u3Def")
(intro 0 (pt "s^2"))
(intro 0 (pt "s^1"))
(split)
(use "EqPSdNcSym")
(use "EqPs1s2")
;; (use "EqPs1s2")
(intro 0 (pt "u^6"))
(intro 0 (pt "u^5"))
(split)
(intro 1)
(use "CoEqPu5u6")
(split)
(use "u3Def")
(use "u4Def")
;; Proof finished.
;; (cdp)
(save "CoEqPAiNcSym")

;; TotalSdNcToRefl
(set-goal "allnc s^(TotalSdNc s^ -> EqPSdNc s^ s^)")
(assume "s^" "Ts")
(elim "Ts")
(use "EqPSdNcSdR")
(use "EqPSdNcSdM")
(use "EqPSdNcSdL")
;; Proof finished.
;; (cdp)
(save "TotalSdNcToRefl")

;; CoEqPAiNcRefl
(set-goal "allnc u^(CoTotalAiNc u^ -> CoEqPAiNc u^ u^)")
(assert
 "allnc u^1,u^2(CoTotalAiNc u^1 andi u^1 eqd u^2 -> CoEqPAiNc u^1 u^2)")
(assume "u^1" "u^2" "u1~u2")
(coind "u1~u2")
(assume "u^3" "u^4" "Conj")
(elim "Conj")
(drop "Conj")
(assume "CoTu3" "u3=u4")
(simp "<-" "u3=u4")
(drop "u3=u4")
(inst-with-to "CoTotalAiNcClause" (pt "u^3") "CoTu3" "Inst")
(elim "Inst")
;; 14
(drop "Inst")
(assume "s^1" "Conj1")
(elim "Conj1")
(drop "Conj1")
(assume "Ts1" "ExHyp")
(by-assume "ExHyp" "u^5" "Conj2")
(elim "Conj2")
(drop "Conj2")
(assume "CoTu5" "u3Def")
(intro 0 (pt "s^1"))
(intro 0 (pt "s^1"))
(split)
(use "TotalSdNcToRefl")
(use "Ts1")
(intro 0 (pt "u^5"))
(intro 0 (pt "u^5"))
(split)
(intro 1)
(split)
(use "CoTu5")
(use "InitEqD")
(split)
(use "u3Def")
(use "u3Def")
;; 2
(assume "AllHyp" "u^" "CoTu")
(use "AllHyp")
(split)
(use "CoTu")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "CoEqPAiNcRefl")

;; EqPSdNcToTotalNcRight
(set-goal "allnc s^1,s^2(EqPSdNc s^1 s^2 -> TotalSdNc s^2)")
(assume "s^1" "s^2" "s1~s2")
(elim "s1~s2")
(use "TotalSdNcSdR")
(use "TotalSdNcSdM")
(use "TotalSdNcSdL")
;; Proof finished.
;; (cdp)
(save "EqPSdNcToTotalNcRight")

;; CoEqPAiNcToCoTotalNcRight
(set-goal "allnc u^1,u^2(CoEqPAiNc u^1 u^2 -> CoTotalAiNc u^2)")
(assume "u^1" "u^2" "u1~u2")
(use (imp-formulas-to-coind-proof
      (pf "exr u^3 CoEqPAiNc u^3 u^2 -> CoTotalAiNc u^2")))
;; 3,4
(assume "u^4" "ExHyp3")
(by-assume "ExHyp3" "u^3" "u3~u4")
(inst-with-to "CoEqPAiNcClause" (pt "u^3") (pt "u^4") "u3~u4" "Inst")
(elim "Inst")
;; 11
(drop "Inst")
(assume "s^1" "ExHyp1")
(by-assume "ExHyp1" "s^2" "Conj")
(elim "Conj")
(drop "Conj")
(assume "EqPs1s2" "ExHyp2")
(by-assume "ExHyp2" "u^5" "u5Prop")
(by-assume "u5Prop" "u^6" "Conj1")
(elim "Conj1")
(drop "Conj1")
(assume "CoEqPu5u6" "Conj3")
(elim "Conj3")
(drop "Conj3")
(assume "u3Def" "u4Def")
(intro 0 (pt "s^2"))
(split)
(use "EqPSdNcToTotalNcRight" (pt "s^1"))
(use "EqPs1s2")
(intro 0 (pt "u^6"))
(split)
(intro 1)
(intro 0 (pt "u^5"))
(use "CoEqPu5u6")
(use "u4Def")
;; 4
(intro 0 (pt "u^1"))
(use "u1~u2")
;; Proof finished.
;; (cdp)
(save "CoEqPAiNcToCoTotalNcRight")

;; CoEqPAiNcToEqD
(set-goal "allnc u^1,u^2(CoEqPAiNc u^1 u^2 -> u^1 eqd u^2)")
(use (make-proof-in-aconst-form (finalg-to-bisim-aconst (py "ai"))))
;; Proof finished.
;; (cdp)
(save "CoEqPAiNcToEqD")

;; CoEqPAiNcTrans
(set-goal "allnc u^1,u^2,u^3(CoEqPAiNc u^1 u^2 -> CoEqPAiNc u^2 u^3 ->
                             CoEqPAiNc u^1 u^3)")
(assume "u^1" "u^2" "u^3" "CoEqPu1u2" "CoEqPu2u3")
(simp (pf "u^1 eqd u^2"))
(simp (pf "u^2 eqd u^3"))
(use "CoEqPAiNcRefl")
(use "CoEqPAiNcToCoTotalNcRight" (pt "u^2"))
(use "CoEqPu2u3")
(use "CoEqPAiNcToEqD")
(use "CoEqPu2u3")
(use "CoEqPAiNcToEqD")
(use "CoEqPu1u2")
;; Proof finished.
;; (cdp)
(save "CoEqPAiNcTrans")

;; CoEqPAiNcReflLeft
(set-goal "allnc u^1,u^2(CoEqPAiNc u^1 u^2 -> CoEqPAiNc u^1 u^1)")
(assume "u^1" "u^2" "CoEqPu1u2")
(use "CoEqPAiNcTrans" (pt "u^2"))
(use "CoEqPu1u2")
(use "CoEqPAiNcSym")
(use "CoEqPu1u2")
;; Proof finished.
;; (cdp)
(save "CoEqPAiNcReflLeft")

(add-ids
 (list (list "I" (make-arity (py "rea")) "ai"))
 '("allnc d,x,y(Sd d -> Real x -> abs x<<=1 -> I x -> y===(1#2)*(x+d) -> I y)"
   "GenI"))

(add-mr-ids "I")
(add-co "IMR")

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
;; (pp neterm)
;; [u][if u (PairConstr sd ai)]
;; (ppc neterm)
;; [u][case u (C s u -> s pair u)]

;; We now add the companion predicate CoI for I, meant to be the
;; greatest-fixed-point of the I clauses.  We also provide GfpCoIMR,
;; needed for soundness proofs when coinduction for CoI was used.

(add-co "I" (list "RealEq"))
;; (pp "CoIClause")
;; allnc x(
;;  CoI x -> 
;;  exr d,x0,y(
;;   Sd d andd 
;;   Real x0 andr abs x0<<=1 andr CoI x0 andl y===(1#2)*(x0+d) andnc x===y))

;; Preparations for AiCoRecExt and GfpCoIMR

;; (pp (term-to-type (pt "(CoRec gamma=>ai)")))
;; gamma=>(gamma=>sd yprod(ai ysum gamma))=>ai

(add-var-name "f" (py "gamma=>sd yprod(ai ysum gamma)"))
(remove-var-name "w")
(add-var-name "w" (py "gamma"))

;; AiCoRec0L
(set-goal "allnc f^,w^,s^,u^1(
 f^ w^ eqd(s^ pair(InL ai gamma)u^1) -> (CoRec gamma=>ai)w^ f^ eqd C s^ u^1)")
(assume "f^" "w^" "s^" "u^1" "EqHyp")
(simp-with (make-proof-in-aconst-form
	    (alg-or-arrow-types-to-corec-aconst (py "gamma=>ai"))))
(ng)
(simp-with "EqHyp")
(ng)
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "AiCoRec0L")

;; AiCoRec0R
(set-goal "allnc f^,w^,s^,w^1(
     f^ w^ eqd(s^ pair(InR gamma ai)w^1) -> 
     (CoRec gamma=>ai)w^ f^ eqd
     C s^((CoRec gamma=>ai)w^1 f^))")
(assume "f^" "w^" "s^" "w^1" "EqHyp")
(assert "allnc u^2(
 C s^((CoRec gamma=>ai)w^1 f^)eqd u^2 -> (CoRec gamma=>ai)w^ f^ eqd u^2)")
 (assume "u^2" "EqHyp2")
 (simp-with (make-proof-in-aconst-form
 	    (alg-or-arrow-types-to-corec-aconst (py "gamma=>ai"))))
 (ng)
 (simp "EqHyp")
 (ng)
 (use "EqHyp2")
(assume "Assertion")
(use "Assertion")
(use "InitEqD")
;; Proof finished.
;; (cdp)
(save "AiCoRec0R")

;; AiCoRecExt
(set-goal "allnc f^1,f^2(
      allnc w^1,w^2(EqP w^1 w^2 ->
      exr s^1,s^2(
       EqPSd s^1 s^2 andi
       (exr u^1,u^2(
         f^1 w^1 eqd(s^1 pair(InL ai gamma)u^1) andi 
         f^2 w^2 eqd(s^2 pair(InL ai gamma)u^2) andi CoEqPAi u^1 u^2) ord
        exr w^3,w^4(
         f^1 w^1 eqd(s^1 pair(InR gamma ai)w^3) andi 
         f^2 w^2 eqd(s^2 pair(InR gamma ai)w^4) andi EqP w^3 w^4)))) -> 
     allnc u^1,u^2( 
      exr w^1,w^2( u^1 eqd(CoRec gamma=>ai)w^1 f^1 andi
                    u^2 eqd(CoRec gamma=>ai)w^2 f^2 andi EqP w^1 w^2) ->
     CoEqPAi u^1 u^2))")
(assume "f^1" "f^2" "EqPf1f2" "u^1" "u^2")
(use (imp-formulas-to-coind-proof
   (pf "exr w^1,w^2( u^1 eqd(CoRec gamma=>ai)w^1 f^1 andi
                     u^2 eqd(CoRec gamma=>ai)w^2 f^2 andi EqP w^1 w^2) ->
        CoEqPAi u^1 u^2")))
(assume "u^3" "u^4" "ExHyp")
(by-assume "ExHyp" "w^1" "w1Prop")
(by-assume "w1Prop" "w^2" "w1w2Prop")
(assert "EqP w^1 w^2")
(use "w1w2Prop")
(assume "EqPw1w2")
(inst-with-to "EqPf1f2" (pt "w^1") (pt "w^2")  "EqPw1w2" "EqPf1f2Inst")
(drop "EqPf1f2")
(by-assume "EqPf1f2Inst" "s^1" "s1Prop")
(by-assume "s1Prop" "s^2" "s1s2Prop")
(intro 0 (pt "s^1"))
(intro 0 (pt "s^2"))
(split)
(use "s1s2Prop")
(inst-with-to "s1s2Prop" 'right "Disj")
(drop "s1s2Prop")
(elim "Disj")
;; 30,31
(drop "Disj")
(assume "ExHypL")
(by-assume "ExHypL" "u^5" "u5Prop")
(by-assume "u5Prop" "u^6" "u5u6Prop")
(simp "w1w2Prop")
(simp "w1w2Prop")
(intro 0 (pt "u^5"))
(intro 0 (pt "u^6"))
(split)
(intro 0)
(use "u5u6Prop")
(split)
(use "AiCoRec0L")
(use "u5u6Prop")
(use "AiCoRec0L")
(use "u5u6Prop")
;; 31
(drop "Disj")
(assume "ExHypR")
(by-assume "ExHypR" "w^3" "w3Prop")
(by-assume "w3Prop" "w^4" "w3w4Prop")
(simp "w1w2Prop")
(simp "w1w2Prop")
(intro 0 (pt "(CoRec gamma=>ai)w^3 f^1"))
(intro 0 (pt "(CoRec gamma=>ai)w^4 f^2"))
(split)
(intro 1)
(intro 0 (pt "w^3"))
(intro 0 (pt "w^4"))
(split)
(use "InitEqD")
(split)
(use "InitEqD")
(use "w3w4Prop")
(split)
(use "AiCoRec0R")
(use "w3w4Prop")
(use "AiCoRec0R")
(use "w3w4Prop")
;; Proof finished.
;; (cdp) ;ok
(save "AiCoRecExt")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)
;; [f,w](CoRec gamma=>ai)w f

(add-pvar-name "X" (make-arity (py "rea")))
(set! PVAR-TO-TVAR-ALIST
      (cons (list (predicate-form-to-predicate (pf "X rea")) (py "gamma"))
	     PVAR-TO-TVAR-ALIST))
(add-pvar-name "XMR" (make-arity (py "rea") (py "gamma")))
(set! PVAR-TO-MR-PVAR-ALIST
      (cons (list (predicate-form-to-predicate (pf "X rea"))
		  (predicate-form-to-predicate (pf "XMR^ rea gamma")))
	    PVAR-TO-MR-PVAR-ALIST))

(add-var-name "uw" (py "ai ysum gamma"))
(add-var-name "suw" (py "sd yprod(ai ysum gamma)"))

;; GfpCoIMR
(set-goal (rename-variables
	   (real-and-formula-to-mr-formula
	    (pt "(CoRec gamma=>ai)")
	    (aconst-to-formula
	     (imp-formulas-to-gfp-aconst (pf "X x -> CoI x"))))))
(assume "x" "w^" "XMRxw" "f^" "Step")
(use-with
 (make-proof-in-aconst-form
  (imp-formulas-to-gfp-aconst (pf "(Pvar rea ai)^ x u^ -> CoIMR x u^")))
 (make-cterm
  (pv "x1") (pv "u^")
  (pf "exnc w^1(XMR^ x1 w^1 andnc u^ eqd((CoRec gamma=>ai)w^1 f^))"))
 (pt "x") (pt "((CoRec gamma=>ai)w^ f^)") (pt "f^")
 "?" "?")
;; 3,4
(drop "Step")
(intro 0 (pt "w^"))
(split)
(use "XMRxw")
(use "InitEqD")
;; 4
(drop "XMRxw")
(assume "x1" "u^1" "ExHyp")
(by-assume "ExHyp" "w^1" "x1w1Prop")
(elim "x1w1Prop")
(drop "x1w1Prop")
(assume "XMRx1w1" "u1Def")
(inst-with-to "Step" (pt "x1") (pt "w^1") "XMRx1w1" "StepInst")
(drop "Step")
(assert "exnc d(ExRTMR rea
               sd yprod(ai ysum gamma)
               (cterm (x,suw^0) 
               (ExRTMR rea
                 sd yprod(ai ysum gamma)
                 (cterm (y,suw^1) 
                 (AndDMR (cterm (s^) SdMR d s^)
                   (cterm (uw^) 
                   (AndRMR (cterm () Real x)
                     (cterm (uw^0) 
                     (AndRMR (cterm () abs x<<=1)
                       (cterm (uw^1) 
                       (AndLMR (cterm (uw^2) 
                                 (OrDMR (cterm (u^) CoIMR x u^)
                                   (cterm (w^) XMR^ x w^))
                                 uw^2)
                         (cterm () y===(1#2)*(x+d) andnc x1===y))
                       uw^1))
                     uw^0))
                   uw^))
                 suw^1))
               suw^0))
             (f^ w^1)")
(elim "StepInst")
(drop "StepInst")
(assume "d" "suw^" "ExRTMRsuw")
(intro 0 (pt "d"))
(use "ExRTMRsuw")
;; Assertion proved
(drop "StepInst")
(assume "ExNcHyp")
(by-assume "ExNcHyp" "d" "dProp")
(assert "exnc x(ExRTMR rea
                 sd yprod(ai ysum gamma)
                 (cterm (y,suw^0) 
                 (AndDMR (cterm (s^) SdMR d s^)
                   (cterm (uw^) 
                   (AndRMR (cterm () Real x)
                     (cterm (uw^0) 
                     (AndRMR (cterm () abs x<<=1)
                       (cterm (uw^1) 
                       (AndLMR (cterm (uw^2) 
                                 (OrDMR (cterm (u^) CoIMR x u^)
                                   (cterm (w^) XMR^ x w^))
                                 uw^2)
                         (cterm () y===(1#2)*(x+d) andnc x1===y))
                       uw^1))
                     uw^0))
                   uw^))
                 suw^0))
                 (f^ w^1)")
(elim "dProp")
(drop "dProp")
(assume "x2" "suw^" "ExRTMR1suw")
(intro 0 (pt "x2"))
(use "ExRTMR1suw")
;; Assertion proved.
(drop "dProp")
(assume "ExNcHyp1")
(by-assume "ExNcHyp1" "x2" "x2Prop")
(assert "exnc y(AndDMR (cterm (s^) SdMR d s^)
                        (cterm (uw^) 
                        (AndRMR (cterm () Real x2)
                          (cterm (uw^0) 
                          (AndRMR (cterm () abs x2<<=1)
                            (cterm (uw^1) 
                            (AndLMR (cterm (uw^2) 
                                      (OrDMR (cterm (u^) CoIMR x2 u^)
                                        (cterm (w^) XMR^ x2 w^))
                                      uw^2)
                              (cterm () y===(1#2)*(x2+d) andnc x1===y))
                            uw^1))
                          uw^0))
                        uw^))
                       (f^ w^1)")
(elim "x2Prop")
(drop "x2Prop")
(assume "y" "suw^" "AndDMRsuw")
(intro 0 (pt "y"))
(use "AndDMRsuw")
;; Assertion proved.
(drop "x2Prop")
(assume "ExNcHyp2")
(by-assume "ExNcHyp2" "y" "yProp")
(assert "(f^ w^1)eqd clft(f^ w^1)pair crht(f^ w^1) andnc
 SdMR d(clft(f^ w^1)) andnc
 (AndRMR (cterm () Real x2)
                            (cterm (uw^0) 
                            (AndRMR (cterm () abs x2<<=1)
                              (cterm (uw^1) 
                              (AndLMR (cterm (uw^2) 
                                        (OrDMR (cterm (u^) CoIMR x2 u^)
                                          (cterm (w^) XMR^ x2 w^))
                                        uw^2)
                                (cterm () y===(1#2)*(x2+d) andnc x1===y))
                              uw^1))
                            uw^0))
                           (crht(f^ w^1))")
(elim "yProp")
(drop "yProp")
(assume "s^" "SdMRds" "uw^""AndRMRuw")
(ng #t)
(split)
(simp "STotalToPairClftCrhtEq")
(use "InitEqD")
(intro 0)
(split)
;; Need animation of Lft here
(animate "Lft")
(ng #t)
(use "SdMRds")
(animate "Rht")
(ng #t)
(use "AndRMRuw")
;; Assertion proved.
(drop "yProp")
(assume "Conj")
(inst-with-to "Conj" 'left "fw1Pair")
(inst-with-to "Conj" 'right 'left "SdMRclftfw1")
(inst-with-to "Conj" 'right 'right "AndRMRuw")
(drop "Conj")
(assert "Real x2 andnc (AndRMR (cterm () abs x2<<=1)
               (cterm (uw^0) 
               (AndLMR (cterm (uw^1) 
                         (OrDMR (cterm (u^) CoIMR x2 u^)
                           (cterm (w^) XMR^ x2 w^))
                         uw^1)
                 (cterm () y===(1#2)*(x2+d) andnc x1===y))
               uw^0))(crht(f^ w^1))")
(elim "AndRMRuw")
(drop "AndRMRuw")
(assume "Rx2" "uw^" "AndRMR1uw")
(split)
(use "Rx2")
(use "AndRMR1uw")
;; Assertion proved.
(drop "AndRMRuw")
(assume "Conj1")
(inst-with-to "Conj1" 'left "Rx2")
(inst-with-to "Conj1" 'right "AndRMRcrhtfw1")
(drop "Conj1")
(assert "abs x2<<=1 andnc (AndLMR (cterm (uw^0) 
                           (OrDMR (cterm (u^) CoIMR x2 u^)
                             (cterm (w^) XMR^ x2 w^))
                           uw^0)
                   (cterm () y===(1#2)*(x2+d) andnc x1===y))(crht(f^ w^1))")
(elim "AndRMRcrhtfw1")
(drop "AndRMRcrhtfw1")
(assume "x2Bd" "uw^" "AndLMRuw")
(split)
(use "x2Bd")
(use "AndLMRuw")
;; Assertion proved.
(drop "AndRMRcrhtfw1")
(assume "Conj2")
(inst-with-to "Conj2" 'left "x2Bd")
(inst-with-to "Conj2" 'right "AndLMRcrhtfw1")
(drop "Conj2")
(assert "(OrDMR (cterm (u^) CoIMR x2 u^)
                           (cterm (w^) XMR^ x2 w^))(crht(f^ w^1))
 andnc
 y===(1#2)*(x2+d) andnc x1===y")
(elim "AndLMRcrhtfw1")
(drop "AndLMRcrhtfw1")
(assume "uw^" "OrDMRuw" "Conj3")
(split)
(use "OrDMRuw")
(use "Conj3")
;; Assertion proved.
(drop "AndLMRcrhtfw1")
(assume "Conj4")
(inst-with-to "Conj4" 'left "OrDMRcrhtfw1")
(inst-with-to "Conj4" 'right "Conj5")
(elim "Conj5")
(drop "Conj5")
(assume "yDef" "x1=y")
(drop "Conj4")
(assert "exnc u^(CoIMR x2 u^ andnc crht(f^ w^1)eqd(InL ai gamma)u^)ornc
         exnc w^(XMR^ x2 w^ andnc crht(f^ w^1)eqd(InR gamma ai)w^)")
(elim "OrDMRcrhtfw1")
(drop "OrDMRcrhtfw1")
(assume "u^2" "CoIMRx2u2")
(intro 0)
(intro 0 (pt "u^2"))
(split)
(use "CoIMRx2u2")
(use "InitEqD")
;; Assertion proved.
(drop "OrDMRcrhtfw1")
(assume "w^2" "XMRx2w2")
(intro 1)
(intro 0 (pt "w^2"))
(split)
(use "XMRx2w2")
(use "InitEqD")
;; 121
(drop "OrDMRcrhtfw1")
(assume "Disj")
(elim "Disj")
;; 139,140
(drop "Disj")
(assume "ExHyp1")
(by-assume "ExHyp1" "u^2" "u2Prop")
;; (pp "AiCoRec0L")
;; allnc f^,w^,s^,u^(
;;  f^ w^ eqd(s^ pair(InL ai gamma)u^) -> (CoRec gamma=>ai)w^ f^ eqd C s^ u^)
(intro 0 (pt "d"))
(intro 0 (pt "x2"))
(intro 0 (pt "x1"))
(intro 0 (pt "clft(f^ w^1)"))
(split)
(use "SdMRclftfw1")
(split)
(use "Rx2")
(split)
(use "x2Bd")
(intro 0 (pt "u^2"))
(split)
(intro 0)
(use "u2Prop")
(split)
(use "RealEqTrans" (pt "y"))
(use "x1=y")
(use "yDef")
(split)
(use "InitEqD")
;; (use "RealEqRefl")
;; (realproof)
(simp "u1Def")
(use "AiCoRec0L")
(simp "<-" "u2Prop")
(use "fw1Pair")
;; 140
(drop "Disj")
(assume "ExHyp1")
(by-assume "ExHyp1" "w^2" "w2Prop")
;; (pp "AiCoRec0R")
;; allnc f^,w^,s^,w^0(
;;  f^ w^ eqd(s^ pair(InR gamma ai)w^0) -> 
;;  (CoRec gamma=>ai)w^ f^ eqd C s^((CoRec gamma=>ai)w^0 f^))
(intro 0 (pt "d"))
(intro 0 (pt "x2"))
(intro 0 (pt "x1"))
(intro 0 (pt "clft(f^ w^1)"))
(split)
(use "SdMRclftfw1")
(split)
(use "Rx2")
(split)
(use "x2Bd")
(intro 0 (pt "(CoRec gamma=>ai)w^2 f^"))
(split)
(intro 1)
(intro 0 (pt "w^2"))
(split)
(use "w2Prop")
(use "InitEqD")
(split)
(simpreal "x1=y")
(use "yDef")
(split)
;; (use "RealEqRefl")
;; (realproof)
(use "InitEqD")
(simp "u1Def")
(use "AiCoRec0R")
(simp "<-" "w2Prop")
(use "fw1Pair")
;; Proof finished.
;; (cp)
(save "GfpCoIMR")

(deanimate "Lft")
(deanimate "Rht")

;; Similarly we prove ClauseCoIMR

;; ClauseCoIMR
(set-goal (rename-variables
	   (real-and-formula-to-mr-formula
	    (pt "(Destr ai)")
	    (aconst-to-formula
	     (theorem-name-to-aconst "CoIClause")))))
(assume "x" "u^" "CoIMRxu")
(inst-with-to "CoIMRClause" (pt "x") (pt "u^") "CoIMRxu" "CoIMRClauseInst")
(by-assume "CoIMRClauseInst" "d" "dProp")
(by-assume "dProp" "x1" "dx1Prop")
(by-assume "dx1Prop" "y" "dx1yProp")
(by-assume "dx1yProp" "s^" "dx1ysProp")
(elim "dx1ysProp")
(drop "dx1ysProp")
(assume "SdMRds" "Conj1")
(elim "Conj1")
(drop "Conj1")
(assume "Rx1" "Conj2")
(elim "Conj2")
(drop "Conj2")
(assume "x1Bd" "ExHyp")
(by-assume "ExHyp" "u^1" "u1Prop")
(elim "u1Prop")
(drop "u1Prop")
(assume "CoIMRx1u1" "Conj3")
(elim "Conj3")
(drop "Conj3")
(assume "yDef" "Conj4")
(elim "Conj4")
(drop "Conj4")
(assume "x=y" "uDef")
(intro 0 (pt "d"))
(intro 0 (pt "x1"))
(intro 0 (pt "y"))
(simp "uDef")
(ng #t)
(intro 0)
(use "SdMRds")
(intro 0)
(use "Rx1")
(intro 0)
(use "x1Bd")
(intro 0)
(use "CoIMRx1u1")
(split)
(use "yDef")
(simp "x=y")
(use "RealEqRefl")
(realproof)
;; Proof finished.
;; (cdp)
(save "ClauseCoIMR")

(add-sound "CoIClause")
;; ok, CoIClauseSound has been added as a new theorem:

;; allnc x,u^(
;;  CoIMR x u^ -> 
;;  (ExRTMR int
;;    sd yprod ai
;;    (cterm (d,(sd yprod ai)^) 
;;    (ExRTMR rea
;;      sd yprod ai
;;      (cterm (x0,(sd yprod ai)^0) 
;;      (ExRTMR rea
;;        sd yprod ai
;;        (cterm (y,(sd yprod ai)^1) 
;;        (AndDMR (cterm (s^) SdMR d s^)
;;          (cterm (u^0) 
;;          (AndRMR (cterm () Real x0)
;;            (cterm (u^1) 
;;            (AndRMR (cterm () abs x0<<=1)
;;              (cterm (u^2) 
;;              (AndLMR (cterm (u^3) CoIMR x0 u^3)
;;                (cterm () y===(1#2)*(x0+d) andnc x===y))
;;              u^2))
;;            u^1))
;;          u^0))
;;        (sd yprod ai)^1))
;;      (sd yprod ai)^0))
;;    (sd yprod ai)^))
;;  (cCoIClause u^))

;; with computation rule

;; cCoIClause eqd(Destr ai)

;; (cdp "CoIClauseSound")

;; Here we do not deanimate CoIClause, since we do not want to use
;; cCoIClause as an abbreviation.

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
;; (pp nneterm)
;; [su]C clft su crht su

(add-sound "CoIClauseInv")
;; ok, CoIClauseInvSound has been added as a new theorem:

;; allnc x,su^(
;;  (ExRTMR int
;;    sd yprod ai
;;    (cterm (d,su^0) 
;;    (ExRTMR rea
;;      sd yprod ai
;;      (cterm (x0,su^1) 
;;      (ExRTMR rea
;;        sd yprod ai
;;        (cterm (y,su^2) 
;;        (AndDMR (cterm (s^) SdMR d s^)
;;          (cterm (u^) 
;;          (AndRMR (cterm () Real x0)
;;            (cterm (u^0) 
;;            (AndRMR (cterm () abs x0<<=1)
;;              (cterm (u^1) 
;;              (AndLMR (cterm (u^2) CoIMR x0 u^2)
;;                (cterm () y===(1#2)*(x0+d) andnc x===y))
;;              u^1))
;;            u^0))
;;          u^))
;;        su^2))
;;      su^1))
;;    su^0))
;;  su^ -> 
;;  CoIMR x(cCoIClauseInv su^))

;; with computation rule

;; cCoIClauseInv eqd
;; ([su]
;;   (CoRec sd yprod ai=>ai)su
;;   ([su0]clft su0 pair(InL ai (sd yprod ai))crht su0))

;; (cdp "CoIClauseInvSound") ;takes a while
;; (cp "CoIClauseInvSound") ;should be used instead
;; ok, proof is correct.

(deanimate "CoIClauseInv")

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
;; (pp nneterm)
;; [s,u]C clft(s pair u)crht(s pair u)

(add-sound "GenCoI")
;; ok, GenCoISound has been added as a new theorem:

;; allnc d,x,y,s^(
;;  SdMR d s^ -> 
;;  Real x -> 
;;  abs x<<=1 -> 
;;  allnc u^(CoIMR x u^ -> y===(1#2)*(x+d) -> CoIMR y(cGenCoI s^ u^)))

;; with computation rule

;; cGenCoI eqd
;; ([s,u]
;;   (CoRec sd yprod ai=>ai)(s pair u)
;;   ([su]clft su pair(InL ai (sd yprod ai))crht su))

;; (cdp "GenCoISound")

(deanimate "GenCoI")

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
;; (pp nneterm)
;; [u](Rec ai=>ai)u([s,u0,u1]C clft(s pair u1)crht(s pair u1))
(deanimate "GenCoI")

;; This is extensionally equal to the identity on ai.

(add-sound "IToCoI")
;; ok, IToCoISound has been added as a new theorem:

;; allnc x,u^(IMR x u^ -> CoIMR x(cIToCoI u^))

;; with computation rule

;; cIToCoI eqd([u](Rec ai=>ai)u([s,u0]cGenCoI s))

;; (cdp "IToCoISound")

(deanimate "IToCoI")

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
;; (pp (rename-variables eterm))

;; [u](Rec ai=>ai)u([s,u0,u1]u1)

;; This is the identity on ai

(add-sound "RealICompat")
;; ok, RealICompatSound has been added as a new theorem:

;; allnc x,y(x===y -> allnc u^(IMR x u^ -> IMR y(cRealICompat u^)))

;; with computation rule

;; cRealICompat eqd([u](Rec ai=>ai)u([s,u0,u1]u1))

;; (cdp "RealICompatSound")

(deanimate "RealICompat")

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
;; (pp nneterm)
;; [u]C clft DesYprod u crht DesYprod u
;; This is the identity on ai

(animate "Lft")
(animate "Rht")
(define neterm (rename-variables (nt eterm)))
(define nneterm (rename-variables (nt (undelay-delayed-corec neterm 1))))
;; (pp nneterm)
;; [u]C[if (DesYprod u) ([s,u0]s)][if (DesYprod u) ([s,u0]u0)]

(add-sound "CoICompat")
;; ok, CoICompatSound has been added as a new theorem:

;; allnc x,y(x===y -> allnc u^(CoIMR x u^ -> CoIMR y(cCoICompat u^)))

;; with computation rule

;; cCoICompat eqd
;; ([u]
;;   (CoRec sd yprod ai=>ai)
;;   ([if (DesYprod u) ([s,u0]s)]pair[if (DesYprod u) ([s,u0]u0)])
;;   ([su][if su ([s,u0]s)]pair(InL ai (sd yprod ai))[if su ([s,u0]u0)]))

;; (cdp "CoICompatSound") ;takes a while
;; (cp "CoICompatSound")

(deanimate "CoICompat")
(deanimate "Lft")
(deanimate "Rht")

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
;; (pp neterm)
;; (Destr ai)

;; Need animation of Lft Rht for (add-sound "CoIClosure")
(animate "Lft")
(animate "Rht")

;; (remove-theorem "CoIClosureSound")
;; (remove-computation-rules-for (pt "cCoIClosure"))

(add-sound "CoIClosure")
;; ok, CoIClosureSound has been added as a new theorem:

;; allnc x,u^(
;;  CoIMR x u^ -> 
;;  (ExRTMR int
;;    sd yprod ai
;;    (cterm (d,su^) 
;;    (ExRTMR rea
;;      sd yprod ai
;;      (cterm (x0,su^0) 
;;      (AndDMR (cterm (s^) SdMR d s^)
;;        (cterm (u^0) 
;;        (AndLMR (cterm (u^1) CoIMR x0 u^1) (cterm () x===(1#2)*(x0+d)))u^0))
;;      su^0))
;;    su^))
;;  (cCoIClosure u^))

;; with computation rule

;; cCoIClosure eqd
;; ([u][if (DesYprod u) ([s,u0]s)]pair[if (DesYprod u) ([s,u0]u0)])

;; (cp "CoIClosureSound")

(deanimate "CoIClosure")
(deanimate "Lft")
(deanimate "Rht")

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
;; (ppc neterm)

;; [u](CoRec ai=>ai)u
;;  ([u0]
;;    cSdUMinus clft(cCoIClosure u0)pair InR(cCoICompat crht(cCoIClosure u0)))

(add-sound "CoIUMinus")
;; ok, CoIUMinusSound has been added as a new theorem:

;; allnc x,u^(CoIMR(~x)u^ -> CoIMR x(cCoIUMinus u^))

;; with computation rule

;; cCoIUMinus eqd
;; ([u]
;;   (CoRec ai=>ai)u
;;   ([u0]
;;     cSdUMinus clft(cCoIClosure u0)pair
;;     (InR ai ai)(cCoICompat crht(cCoIClosure u0))))

;; (cp "CoIUMinusSound")

(deanimate "CoIUMinus")

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
;; (ppc neterm)
;; [s,u]cCoIClauseInv(s pair u)

(add-sound "CoIClosureInv")
;; ok, CoIClosureInvSound has been added as a new theorem:

;; allnc d,x,s^(
;;  SdMR d s^ -> 
;;  allnc u^(CoIMR x u^ -> CoIMR((1#2)*(x+d))(cCoIClosureInv s^ u^)))

;; with computation rule

;; cCoIClosureInv eqd
;; ([s,u]
;;   (CoRec sd yprod ai=>ai)(s pair u)
;;   ([su]clft su pair(InL ai (sd yprod ai))crht su))

;; (cp "CoIClosureInvSound")

(deanimate "CoIClosureInv")

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

;; (remove-theorem "ApproxSplitSound")
(add-sound "ApproxSplit")
;; ok, ApproxSplitSound has been added as a new theorem:

;; allnc x,y,z,p(
;;  Real x -> 
;;  Real y -> 
;;  Real z -> 
;;  RealLt x y p -> 
;;  (OrUMR (cterm () z<<=y) (cterm () x<<=z))(cApproxSplit x y z p))

;; with computation rule

;; cApproxSplit eqd
;; ([x,x0,x1,p]
;;   [if x
;;     ([as,M]
;;      [if x0
;;        ([as0,M0]
;;         [if x1
;;           ([as1,M1]
;;            as1(M1(PosS(PosS p))max M0(PosS(PosS p))max M(PosS(PosS p)))<=
;;            (as(M0(PosS(PosS p))max M(PosS(PosS p)))+
;;             as0(M0(PosS(PosS p))max M(PosS(PosS p))))*
;;            (1#2))])])])

;; (cp "ApproxSplitSound")

(deanimate "ApproxSplit")

;; Normalizing the (huge) soundness proof for ApproxSplit generates an error
;; npterm-and-var-genavar-alist-and-formula-to-proof
;; classical equal formulas expected

;; (a+ ~b)*(1#4)== ~((~a+b)*(1#4))  and  T

;; The rational equation on the left is in normal form.  Trace postponed.

;; term-to-external-expr
;; unknown if (alg)
;; [if x197810 ((nat=>rat)=>(pos=>nat)=>rea=>pos=>boole)_197809]

;; This indicates that the algebra rea should be added in
;; term-to-external-expr .  Postponed.

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
;; (pp neterm)
(animate "ApproxSplit")
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)
;; [x][case x (RealConstr as M -> as(M 3)<=(1#4))]
(deanimate "ApproxSplit")

;; (remove-theorem "ApproxSplitZeroPtFiveSound")
(add-sound "ApproxSplitZeroPtFive")
;; ok, ApproxSplitZeroPtFiveSound has been added as a new theorem:

;; allnc x(
;;  Real x -> 
;;  (OrUMR (cterm () x<<=(1#2)) (cterm () 0<<=x))(cApproxSplitZeroPtFive x))

;; with computation rule

;; cApproxSplitZeroPtFive eqd([x]cApproxSplit 0(1#2)x 1)

;; (cp "ApproxSplitZeroPtFiveSound")

;; (deanimate "ApproxSplitZeroPtFive")
;; Leave it animated since the rhs is simple

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
;; (ppc neterm)
;; [x][case x (RealConstr as M -> as(M 3)<=(IntN 1#4))]
(deanimate "ApproxSplit")

(add-sound "ApproxSplitZeroMinusPtFive")
;; ok, ApproxSplitZeroMinusPtFiveSound has been added as a new theorem:

;; allnc x(
;;  Real x -> 
;;  (OrUMR (cterm () x<<=0) (cterm () (IntN 1#2)<<=x))
;;  (cApproxSplitZeroMinusPtFive x))

;; with computation rule

;; cApproxSplitZeroMinusPtFive eqd([x]cApproxSplit(IntN 1#2)0 x 1)

;; (cp "ApproxSplitZeroMinusPtFiveSound")

;; (deanimate "ApproxSplitZeroMinusPtFive")
;; Leave it animated since the rhs is simple

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
;; (pp neterm)

;; [x]
;;  [if x
;;    ([as,M]
;;     [if (cApproxSplitZeroMinusPtFive x)
;;       (SdL pair RealConstr([n]2*as n+1)([p]M(PosS p)))
;;       [if (cApproxSplitZeroPtFive x)
;;        (SdM pair RealConstr([n]2*as n)([p]M(PosS p)))
;;        (SdR pair RealConstr([n]2*as n+IntN 1)([p]M(PosS p)))]])]

(add-sound "RealToCoIAux")
;; ok, RealToCoIAuxSound has been added as a new theorem:

;; allnc x(
;;  Real x -> 
;;  abs x<<=1 -> 
;;  (ExDTMR (cterm (s,x^0) 
;;            (ExLTMR (cterm (y) 
;;                      Real y andnc abs y<<=1 andnc x===(1#2)*(y+SdToInt s)))
;;            x^0))
;;  (cRealToCoIAux x))

;; with computation rule

;; cRealToCoIAux eqd
;; ([x]
;;   [if x
;;     ([as,M]
;;      [if (cApproxSplit(IntN 1#2)0 x 1)
;;        (SdL pair RealConstr([n]2*as n+1)([p]M(PosS p)))
;;        [if (cApproxSplit 0(1#2)x 1)
;;         (SdM pair RealConstr([n]2*as n)([p]M(PosS p)))
;;         (SdR pair RealConstr([n]2*as n+IntN 1)([p]M(PosS p)))]])])

;; (cp "RealToCoIAuxSound")

(deanimate "RealToCoIAux")

;; SdInjSdToInt
(set-goal "allnc s(SdInj(SdToInt s)s)")
(ind)
(ng #t)
(use "InitSdSdRInj")
(ng #t)
(use "InitSdSdMInj")
(ng #t)
(use "InitSdSdLInj")
;; Proof finished.
;; (cdp)
(save "SdInjSdToInt")

;; RealToCoI
(set-goal "all x(Real x -> abs x<<=1 -> CoI x)")
(assume "x" "Rx" "xBd")
(assert "exd sd exl y(Real y andnc abs y<<=1 andnc x===(1#2)*(y+SdToInt sd))")
 (use "RealToCoIAux" (pt "x"))
 (use "Rx")
 (use "xBd")
(assume "Hyp")
(coind "Hyp")
;; (pp (formula-to-et-type (proof-to-formula (current-goal))))
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
(use "SdInjElim" (pt "s"))
(use "SdInjSdToInt")
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
;; (ppc RealToCoI-neterm)

;; [x]
;;  (CoRec sd yprod rea=>ai)(cRealToCoIAux x)
;;  ([sx]
;;    [case sx
;;      (s pair x0 -> 
;;      [case (cRealToCoIAux x0) (s0 pair x1 -> s pair InR(s0 pair x1))])])

(add-sound "RealToCoI")
;; ok, RealToCoISound has been added as a new theorem:

;; allnc x(Real x -> abs x<<=1 -> CoIMR x(cRealToCoI x))

;; with computation rule

;; cRealToCoI eqd
;; ([x]
;;   (CoRec sd yprod rea=>ai)(cRealToCoIAux x)
;;   ([sx]
;;     [if sx
;;       ([s,x0]
;;        [if (cRealToCoIAux x0)
;;          ([s0,x1]s pair(InR (sd yprod rea) ai)(s0 pair x1))])]))

;; (cp "RealToCoISound")

(deanimate "RealToCoI")

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
;; (pp neterm)
;; [a]a
;; ppn means pretty print with names.
;; (ppn neterm)
;; (lambda a ((lambda n a) RealConstr (lambda p Zero)))

(add-sound "RatToReal")
;; ok, RatToRealSound has been added as a new theorem:

;; allnc a(
;;  abs a<=1 -> 
;;  (ExLTMR (cterm (x) Real x andnc abs x<<=1 andnc x===a))(cRatToReal a))

;; with computation rule

;; cRatToReal eqd([a]a)

;; (cp "RatToRealSound")

;; (deanimate "RatToReal")
;; Leave it animated because it gives an identity.

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
;; (pp RatToCoI-neterm)
;; [a]cRealToCoI a

(animate "RealToCoI")
(animate "RealToCoIAux")
(animate "ApproxSplitZeroPtFive")
(animate "ApproxSplitZeroMinusPtFive")
(animate "ApproxSplit")
(define RatToCoI-neterm (rename-variables (nt RatToCoI-eterm)))
;; (ppc RatToCoI-neterm)

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
;;            s pair InR(SdL pair RealConstr([n]2*as n+1)([p]M(PosS p))))
;;            (False -> 
;;            [case x
;;              (RealConstr as1 M1 -> 
;;              [case (as1(M1 3)<=(1#4))
;;                (True -> 
;;                s pair InR(SdM pair RealConstr([n]2*as n)([p]M(PosS p))))
;;                (False -> 
;;                s pair 
;;                InR(SdR pair
;; 		       RealConstr([n]2*as n+IntN 1)([p]M(PosS p))))])])])])])])

(deanimate "RealToCoI")
(deanimate "RealToCoIAux")
(deanimate "ApproxSplitZeroPtFive")
(deanimate "ApproxSplitZeroMinusPtFive")
(deanimate "ApproxSplit")

;; To check which program constants are animated evaluate
;; (display-animation)

(add-sound "RatToCoI")
;; ok, RatToCoISound has been added as a new theorem:

;; allnc a(abs a<=1 -> CoIMR a(cRatToCoI a))

;; with computation rule

;; cRatToCoI eqd([a]cRealToCoI a)

;; (cdp "RatToCoISound")

;; (deanimate "RatToCoI")
;; Leave it animated since the rhs in simple.

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


