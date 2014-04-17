;; 2013-09-15.  examplesaanalysisaverge.scm.  Abstract reals (type r)
;; instantiated to concrete ones (type rea) satisfying Real x.
;; Program constant (P r) replaced by RealPlus.  Rewrite rules derived
;; from theorems.  Closed term (using CoRec) provided for 1/2 sqrt{2}.
;; Haskell translation done.

;; (load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(libload "numbers.scm")
(libload "simpreal.scm")
(libload "real.scm")
;; (set! COMMENT-FLAG #t)

(remove-var-name "i" "j") ;will be used as variable name for sdtwo.

;; No: keep M for the modulus.  This will be used later when construct
;; a cototal interval from a real x.  Use Lft Mid Rht instead of M L R

;; (remove-var-name "M") ;will be used as constructor for sd
;; (remove-token "M")
(remove-var-name "d") ;will be used for signed digits

;; Next we define the algebra of signed digits, similar to boole.

(add-alg "sd" '("Lft" "sd") '("Mid" "sd") '("Rht" "sd"))
(add-totality "sd")

(add-alg "sdtwo"
	 '("LL" "sdtwo")
	 '("LT" "sdtwo")
	 '("MT" "sdtwo")
	 '("RT" "sdtwo")
	 '("RR" "sdtwo"))
(add-totality "sdtwo")

(add-var-name "d" "e" (py "sd"))
(add-var-name "i" "j" (py "sdtwo"))

;; We need a conversion of sd into int

(add-program-constant "SDToInt" (py "sd=>int"))

(add-computation-rules
 "SDToInt Lft" "IntN 1"
 "SDToInt Mid" "0"
 "SDToInt Rht" "1")

;; "SDToIntTotal"
(set-goal (term-to-totality-formula (pt "SDToInt")))
(assume "d^" "Td")
(elim "Td")
(ng #t)
(use "TotalIntIntNeg")
(use "TotalPosOne")
(ng #t)
(use "TotalIntIntZero")
(ng #t)
(use "TotalIntIntPos")
(use "TotalPosOne")
;; Proof finished.
(save "SDToIntTotal")

(add-program-constant "SDTwoToInt" (py "sdtwo=>int"))

(add-computation-rules
 "SDTwoToInt LL" "IntN 2"
 "SDTwoToInt LT" "IntN 1"
 "SDTwoToInt MT" "0"
 "SDTwoToInt RT" "1"
 "SDTwoToInt RR" "2")

;; "SDTwoToIntTotal"
(set-goal (rename-variables (term-to-totality-formula (pt "SDTwoToInt"))))
(assume "i^" "Ti")
(elim "Ti")
(ng #t)
(use "TotalIntIntNeg")
(use "TotalPosSZero")
(use "TotalPosOne")
(ng #t)
(use "TotalIntIntNeg")
(use "TotalPosOne")
(ng #t)
(use "TotalIntIntZero")
(ng #t)
(use "TotalIntIntPos")
(use "TotalPosOne")
(ng #t)
(use "TotalIntIntPos")
(use "TotalPosSZero")
(use "TotalPosOne")
;; Proof finished.
(save "SDTwoToIntTotal")

(add-alg "iv" '("II" "iv") '("C" "sd=>iv=>iv"))
(add-var-name "v" "w" (py "iv"))

(add-totality "iv")

(pp (rename-variables (proof-to-formula (theorem-name-to-proof "TotalIvC"))))
;; allnc d^,v^(TotalSd d^ -> TotalIv v^ -> TotalIv(C d^ v^))

;; We inductively define a set I of reals, by the clauses
;; InitI: I 0
;; GenI: I x -> I(x+d)/2 (d a signed digit).

(add-ids
 (list (list "I" (make-arity (py "rea")) "iv"))
 '("I 0" "InitI")
 '("allnc x^(TotalRea x^ --> all d(I x^ -> I((x^ +SDToInt d)/2)))" "GenI"))

;; Remark.  By AllncTotalIntro and -Elim one might want to write

;; (add-ids
;;  (list (list "I" (make-arity (py "rea")) "iv"))
;;  '("I 0" "InitI")
;;  '("allnc x all d(I x -> I((x+SDToInt d)/2))" "GenI"))

;; However, the CoIClause then is
;; allnc x^(
;;  CoI x^ -> x^ eqd 0 orr exr x0 ex d(CoI x0 andl x^ eqd(x0+SDToInt d)/2))
;; and hence not what we want.  Therefore in add-ids we should not use
;; the abbreviations provided by AllncTotalIntro and -Elim

(add-co "I")

(pp (rename-variables (aconst-to-formula
		       (theorem-name-to-aconst "CoIClause"))))
;; allnc x^(
;;  CoI x^ -> 
;;  x^ eqd 0 orr 
;;  exr x^0(TotalRea x^0 andr ex d(CoI x^0 andl x^ eqd(x^0+SDToInt d)/2)))

;; We define JOne:sd=>sd=>sdtwo with 

(add-program-constant "JOne" (py "sd=>sd=>sdtwo"))

(add-computation-rules
 "JOne Lft Lft" "LL"
 "JOne Lft Mid" "LT"
 "JOne Lft Rht" "MT"
 "JOne Mid Lft" "LT"
 "JOne Mid Mid" "MT"
 "JOne Mid Rht" "RT"
 "JOne Rht Lft" "MT"
 "JOne Rht Mid" "RT"
 "JOne Rht Rht" "RR")

;; "JOneTotal"
(set-goal (rename-variables (term-to-totality-formula (pt "JOne"))))
(assume "d^1" "Td1" "d^2" "Td2")
(elim "Td1")

(elim "Td2")
(ng #t)
(use "TotalSdtwoLL")
(ng #t)
(use "TotalSdtwoLT")
(ng #t)
(use "TotalSdtwoMT")

(elim "Td2")
(ng #t)
(use "TotalSdtwoLT")
(ng #t)
(use "TotalSdtwoMT")
(ng #t)
(use "TotalSdtwoRT")

(elim "Td2")
(ng #t)
(use "TotalSdtwoMT")
(ng #t)
(use "TotalSdtwoRT")
(ng #t)
(use "TotalSdtwoRR")
;; Proof finished.
(save "JOneTotal")

;; "JOneProp"
(set-goal "all d,e(SDToInt d+SDToInt e=SDTwoToInt(JOne d e))")
(cases)
(cases)
(use "Truth")
(use "Truth")
(use "Truth")
(cases)
(use "Truth")
(use "Truth")
(use "Truth")
(cases)
(use "Truth")
(use "Truth")
(use "Truth")
;; Proof finished.
(save "JOneProp")

;; "XSubY"
(set-goal "allnc x,y(
      CoI x -> 
      CoI y -> 
      exr x^0,y^0 ex i(TotalRea x^0 andr TotalRea y^0 andr
       x +y eqd (x^0+y^0+SDTwoToInt i)/2 & CoI x^0 & CoI y^0))")
(use "AllncTotalIntro")
(assume "x^" "Tx")
(use "AllncTotalIntro")
(assume "y^" "Ty" "CoIx" "CoIy")
;; We first distinguish cases on CoI x
(inst-with-to "CoIClause" (pt "x^") "CoIx" "xCases")
(elim "xCases")
(drop "xCases")
(assume "x=0")
;; We distinguish cases on CoI y
(inst-with-to "CoIClause" (pt "y^") "CoIy" "yCases")
(elim "yCases")
(drop "yCases")
(assume "y=0")

;; Case N,N (i.e., x=0 and y=0)
(intro 0 (pt "x^"))
(intro 0 (pt "y^"))
(ex-intro (pt "MT"))
(split)
(use "Tx")
(split)
(use "Ty")
(split)
;; x+y=(x+y+0)/2 since x=0 and y=0
;; (use "Lemma1")
(ng #t)
(simp "x=0")
(simp "y=0")
(ng #t)
;; ?_30:0 eqd RealDiv 0 2
;; (display-pconst "RealDiv")
;; No rules.  Add them
(admit)
(split)
(use "CoIx")
(use "CoIy")

;; Case N,A (i.e., x=0 and y=(y1+e1)/2)
(drop "yCases")
(assume "yCases1")
(by-assume "yCases1" "y^1" "y1Prop")
(elim "y1Prop")
(assume "Ty1" "ExHyp")
(by-assume "ExHyp" "e1" "y1e1Prop")
(intro 0 (pt "x^"))
(intro 0 (pt "y^1"))
(ex-intro (pt "JOne Mid e1"))
(split)
(use "Tx")
(split)
(use "Ty1")
;; ?_49:x^ +y^ eqd(x^ +y^1+SDTwoToInt(JOne Mid e1))/2 & CoI x^ & CoI y^1
(split)
;; ?_50:x^ +y^ eqd(x^ +y^1+SDTwoToInt(JOne Mid e1))/2
;; ?_37:x +y eqd(x +y1+SDTwoToInt(JOne Mid e1))/2
;; ?_37: (P r)x^ y^ eqd(H r)((Pi r)((P r)x^ y^1)(SDTwoToInt(JOne Mid e1)))
;; JOneProp: all d,e SDToInt d+SDToInt e=SDTwoToInt(JOne d e)
(simp "<-" "JOneProp")
(ng #t)
;; ?_53:x +y eqd(x +y1+SDToInt e1)/2
;; x+y=(x+y1+e1)/2 since x=0 and y=(y1+e1)/2
;; (use "Lemma2")
;; (use "x=0")
(simp "x=0")
;; ?_41:0+y eqd(0+y1+SDToInt e1)/2
;; Problem:  0+y^ does not normalize to y^ since y^ is not total.
;; Use TotalRea y^.
;; (display-pconst "RealPlus")
(assert "all x 0+x eqd x")
 (assume "x")
 (ng #t)
 (use "InitEqD")
(assume "Assertion")
(assert "allnc x^(TotalRea x^ -> 0+x^ eqd x^)")
 (use "AllTotalElim")
 (use "Assertion")
(assume "Assertion1")
(drop "Assertion")
(inst-with-to "Assertion1" (pt "y^1") "Ty1" "0+y1=y1")
(simp "0+y1=y1")
(inst-with-to "Assertion1" (pt "y^") "Ty" "0+y=y")
(simp "0+y=y")
(use "y1e1Prop")
(split)
(use "CoIx")
(use "y1e1Prop")

;; Now the case x=(x1+d1)/2
(drop "xCases")
(assume "xCases1")
(by-assume "xCases1" "x^1" "x1Prop")
(elim "x1Prop")
(assume "Tx1" "ExHyp")
(by-assume "ExHyp" "d1" "x1d1Prop")
;; We again distinguish cases on CoI y^
(inst-with-to "CoIClause" (pt "y^") "CoIy" "yCases")
(elim "yCases")
(drop "yCases")
(assume "y=0")

;; Case A,N (i.e., x=(x1+d1)/2 and y=0)
(intro 0 (pt "x^1"))
(intro 0 (pt "y^"))
(ex-intro (pt "JOne d1 Mid"))
(split)
(use "Tx1")
(split)
(use "Ty")
(split)
(simp "<-" "JOneProp")
(ng #t)
(simp "y=0")
;; ?_100:x^ +0 eqd(x^1+0+(SDToInt d1+SDToInt Mid))/2
;; x+y=(x1+y+d1)/2 since x=(x1+d1)/2 and y=0
(assert "all x x+0 eqd x")
 (assume "x")
 (ng #t)
 (use "InitEqD")
(assume "Assertion")
(assert "allnc x^(TotalRea x^ -> x^ +0 eqd x^)")
 (use "AllTotalElim")
 (use "Assertion")
(assume "Assertion1")
(drop "Assertion")
(inst-with-to "Assertion1" (pt "x^1") "Tx1" "x1+0=x1")
(simp "x1+0=x1")
(inst-with-to "Assertion1" (pt "x^") "Tx" "0+x=x")
(simp "0+x=x")
(use "x1d1Prop")
(split)
(use "x1d1Prop")
(use "CoIy")

;; Case A,A (i.e., x=(x1+d1)/2 and y=(y1+e1)/2)
(drop "x1Prop" "yCases")
(assume "yCases1")
(by-assume "yCases1" "y^1" "y1Prop")
(elim "y1Prop")
(drop "y1Prop")
(assume "Ty1" "ExHyp1")
(by-assume "ExHyp1" "e1" "y1e1Prop")
(intro 0 (pt "x^1"))
(intro 0 (pt "y^1"))
(ex-intro (pt "JOne d1 e1"))
(split)
(use "Tx1")
(split)
(use "Ty1")
(split)
(simp "<-" "JOneProp")
;; ?_139:x^ +y^ eqd(x^1+y^1+(SDToInt d1+SDToInt e1))/2
;; x+y=(x1+y1+d1+e1)/2 since x=(x1+d1)/2 and y=(y1+e1)/2
(admit)
(split)
(use "x1d1Prop")
(use "y1e1Prop")
;; Proof finished.
(save "XSubY")
;; (remove-theorem "XSubY")

(define eterm (proof-to-extracted-term (theorem-name-to-proof "XSubY")))
(add-var-name "dv" (py "sd@@iv"))
(define neterm (nt eterm))
(pp neterm)

;; [v0,v1]
;;  [if (Des v0)
;;    [if (Des v1) (MT@v0@v1) ([dv2]JOne Mid left dv2@v0@right dv2)]
;;    ([dv2]
;;     [if (Des v1)
;;       (JOne left dv2 Mid@right dv2@v1)
;;       ([dv3]JOne left dv2 left dv3@right dv2@right dv3)])]

(ppc neterm)

;; [v0,v1]
;;  [case (Des v0)
;;    ((DummyL sd@@iv) -> 
;;    [case (Des v1)
;;      ((DummyL sd@@iv) -> MT@v0@v1)
;;      (Inr dv2 -> JOne Mid left dv2@v0@right dv2)])
;;    (Inr dv2 -> 
;;    [case (Des v1)
;;      ((DummyL sd@@iv) -> JOne left dv2 M@right dv2@v1)
;;      (Inr dv3 -> JOne left dv2 left dv3@right dv2@right dv3)])]

;; This term can be read as follows.  Given v0, v1, destruct both.
;; Assume that both are composed, i.e., of the form dv2 and dv3.  Take
;; their components d2,v2 and d3,v3.  Then the result is JOne d2 d3
;; pair v2 pair v3.

;; We define J: sd=>sd=>sdtwo=>sdtwo and D: sd=>sd=>sdtwo=>sd such that
;; d+e+2*i=J d e i+4*(D d e i).  For J'(d+e+2*i) := J d e i and
;; D'(d+e+2*i) := D d e i we want

;; J' k = [if (rem k 4=3) 1 (sg k)*(rem k 4)]
;; D' k = [if (abs k<=2) 0 (sg k)]

;; Hence J' should map
;; IntN 6 -> IntN 2
;; IntN 5 -> IntN 1
;; IntN 4 -> 0
;; IntN 3 -> 1
;; IntN 2 -> IntN 2
;; IntN 1 -> IntN 1
;; 0 -> 0
;; 1 -> 1
;; 2 -> 2
;; 3 -> IntN 1
;; 4 -> 0
;; 5 -> 1
;; 6 -> 2

;; Similarly D' should map
;; IntN 6 -> IntN 1
;; IntN 5 -> IntN 1
;; IntN 4 -> IntN 1
;; IntN 3 -> IntN 1
;; IntN 2 -> 0
;; IntN 1 -> 0
;; 0 -> 0
;; 1 -> 0
;; 2 -> 0
;; 3 -> 1
;; 4 -> 1
;; 5 -> 1
;; 6 -> 1

;; k        J'k      D'k      J'k+4*D'k
;; IntN 6   IntN 2   IntN 1   IntN 6
;; IntN 5   IntN 1   IntN 1   IntN 5
;; IntN 4   0        IntN 1   IntN 4
;; IntN 3   1        IntN 1   IntN 3
;; IntN 2   IntN 2   0        IntN 2
;; IntN 1   IntN 1   0        IntN 1
;; 0        0        0        0
;; 1        1        0        1
;; 2        2        0        2
;; 3        IntN 1   1        3
;; 4        0        1        4
;; 5        1        1        5
;; 6        2        1        6

;; Then for abs k<=6 we have k=J' k+D' k:
;; IntN 6=IntN 2+4*(IntN 1)
;; IntN 5=IntN 1+4*(IntN 1)
;; IntN 4=0+4*(IntN 1)
;; IntN 3=1+4*(IntN 1)
;; IntN 2=IntN 2
;; IntN 1=IntN 1
;; 0=0
;; 1=1
;; 2=2
;; 3=IntN 1+4
;; 4=0+4
;; 5=1+4
;; 6=2+4

(add-program-constant "J" (py "sd=>sd=>sdtwo=>sdtwo"))
(add-computation-rules
 "J Lft Lft LL" "LL"
 "J Lft Lft LT" "MT"
 "J Lft Lft MT" "LL"
 "J Lft Lft RT" "MT"
 "J Lft Lft RR" "RR"

 "J Lft Mid LL" "LT"
 "J Lft Mid LT" "RT"
 "J Lft Mid MT" "LT"
 "J Lft Mid RT" "RT"
 "J Lft Mid RR" "LT"

 "J Lft Rht LL" "MT"
 "J Lft Rht LT" "LL"
 "J Lft Rht MT" "MT"
 "J Lft Rht RT" "RR"
 "J Lft Rht RR" "MT"

 "J Mid Lft LL" "LT"
 "J Mid Lft LT" "RT"
 "J Mid Lft MT" "LT"
 "J Mid Lft RT" "RT"
 "J Mid Lft RR" "LT"

 "J Mid Mid LL" "MT"
 "J Mid Mid LT" "LL"
 "J Mid Mid MT" "MT"
 "J Mid Mid RT" "RR"
 "J Mid Mid RR" "MT"

 "J Mid Rht LL" "RT"
 "J Mid Rht LT" "LT"
 "J Mid Rht MT" "RT"
 "J Mid Rht RT" "LT"
 "J Mid Rht RR" "RT"

 "J Rht Lft LL" "MT"
 "J Rht Lft LT" "LL"
 "J Rht Lft MT" "MT"
 "J Rht Lft RT" "RR"
 "J Rht Lft RR" "MT"

 "J Rht Mid LL" "RT"
 "J Rht Mid LT" "LT"
 "J Rht Mid MT" "RT"
 "J Rht Mid RT" "LT"
 "J Rht Mid RR" "RT"

 "J Rht Rht LL" "LL"
 "J Rht Rht LT" "MT"
 "J Rht Rht MT" "RR"
 "J Rht Rht RT" "MT"
 "J Rht Rht RR" "RR")

;; "JTotal"
(set-goal (rename-variables (term-to-totality-formula (pt "J"))))
(assume "d^1" "Td1" "d^2" "Td2" "i^" "Ti")
(elim "Td1")

(elim "Td2")

(elim "Ti")
(ng #t)
(use "TotalSdtwoLL")
(ng #t)
(use "TotalSdtwoMT")
(ng #t)
(use "TotalSdtwoLL")
(ng #t)
(use "TotalSdtwoMT")
(ng #t)
(use "TotalSdtwoRR")

(elim "Ti")
(ng #t)
(use "TotalSdtwoLT")
(ng #t)
(use "TotalSdtwoRT")
(ng #t)
(use "TotalSdtwoLT")
(ng #t)
(use "TotalSdtwoRT")
(ng #t)
(use "TotalSdtwoLT")

(elim "Ti")
(ng #t)
(use "TotalSdtwoMT")
(ng #t)
(use "TotalSdtwoLL")
(ng #t)
(use "TotalSdtwoMT")
(ng #t)
(use "TotalSdtwoRR")
(ng #t)
(use "TotalSdtwoMT")

(elim "Td2")

(elim "Ti")
(ng #t)
(use "TotalSdtwoLT")
(ng #t)
(use "TotalSdtwoRT")
(ng #t)
(use "TotalSdtwoLT")
(ng #t)
(use "TotalSdtwoRT")
(ng #t)
(use "TotalSdtwoLT")

(elim "Ti")
(ng #t)
(use "TotalSdtwoMT")
(ng #t)
(use "TotalSdtwoLL")
(ng #t)
(use "TotalSdtwoMT")
(ng #t)
(use "TotalSdtwoRR")
(ng #t)
(use "TotalSdtwoMT")

(elim "Ti")
(ng #t)
(use "TotalSdtwoRT")
(ng #t)
(use "TotalSdtwoLT")
(ng #t)
(use "TotalSdtwoRT")
(ng #t)
(use "TotalSdtwoLT")
(ng #t)
(use "TotalSdtwoRT")

(elim "Td2")

(elim "Ti")
(ng #t)
(use "TotalSdtwoMT")
(ng #t)
(use "TotalSdtwoLL")
(ng #t)
(use "TotalSdtwoMT")
(ng #t)
(use "TotalSdtwoRR")
(ng #t)
(use "TotalSdtwoMT")

(elim "Ti")
(ng #t)
(use "TotalSdtwoRT")
(ng #t)
(use "TotalSdtwoLT")
(ng #t)
(use "TotalSdtwoRT")
(ng #t)
(use "TotalSdtwoLT")
(ng #t)
(use "TotalSdtwoRT")

(elim "Ti")
(ng #t)
(use "TotalSdtwoLL")
(ng #t)
(use "TotalSdtwoMT")
(ng #t)
(use "TotalSdtwoRR")
(ng #t)
(use "TotalSdtwoMT")
(ng #t)
(use "TotalSdtwoRR")
;; Proof finished.
(save "JTotal")

(add-program-constant "D" (py "sd=>sd=>sdtwo=>sd"))
(add-computation-rules
 "D Lft Lft LL" "Lft"
 "D Lft Lft LT" "Lft"
 "D Lft Lft MT" "Mid"
 "D Lft Lft RT" "Mid"
 "D Lft Lft RR" "Mid"

 "D Lft Mid LL" "Lft"
 "D Lft Mid LT" "Lft"
 "D Lft Mid MT" "Mid"
 "D Lft Mid RT" "Mid"
 "D Lft Mid RR" "Rht"

 "D Lft Rht LL" "Lft"
 "D Lft Rht LT" "Mid"
 "D Lft Rht MT" "Mid"
 "D Lft Rht RT" "Mid"
 "D Lft Rht RR" "Rht"

 "D Mid Lft LL" "Lft"
 "D Mid Lft LT" "Lft"
 "D Mid Lft MT" "Mid"
 "D Mid Lft RT" "Mid"
 "D Mid Lft RR" "Rht"

 "D Mid Mid LL" "Lft"
 "D Mid Mid LT" "Mid"
 "D Mid Mid MT" "Mid"
 "D Mid Mid RT" "Mid"
 "D Mid Mid RR" "Rht"

 "D Mid Rht LL" "Lft"
 "D Mid Rht LT" "Mid"
 "D Mid Rht MT" "Mid"
 "D Mid Rht RT" "Rht"
 "D Mid Rht RR" "Rht"

 "D Rht Lft LL" "Lft"
 "D Rht Lft LT" "Mid"
 "D Rht Lft MT" "Mid"
 "D Rht Lft RT" "Mid"
 "D Rht Lft RR" "Rht"

 "D Rht Mid LL" "Lft"
 "D Rht Mid LT" "Mid"
 "D Rht Mid MT" "Mid"
 "D Rht Mid RT" "Rht"
 "D Rht Mid RR" "Rht"

 "D Rht Rht LL" "Mid"
 "D Rht Rht LT" "Mid"
 "D Rht Rht MT" "Mid"
 "D Rht Rht RT" "Rht"
 "D Rht Rht RR" "Rht")

;; "DTotal"
(set-goal (rename-variables (term-to-totality-formula (pt "D"))))
(assume "d^1" "Td1" "d^2" "Td2" "i^" "Ti")
(elim "Td1")

(elim "Td2")

(elim "Ti")
(ng #t)
(use "TotalSdLft")
(ng #t)
(use "TotalSdLft")
(ng #t)
(use "TotalSdMid")
(ng #t)
(use "TotalSdMid")
(ng #t)
(use "TotalSdMid")

(elim "Ti")
(ng #t)
(use "TotalSdLft")
(ng #t)
(use "TotalSdLft")
(ng #t)
(use "TotalSdMid")
(ng #t)
(use "TotalSdMid")
(ng #t)
(use "TotalSdRht")

(elim "Ti")
(ng #t)
(use "TotalSdLft")
(ng #t)
(use "TotalSdMid")
(ng #t)
(use "TotalSdMid")
(ng #t)
(use "TotalSdMid")
(ng #t)
(use "TotalSdRht")

(elim "Td2")

(elim "Ti")
(ng #t)
(use "TotalSdLft")
(ng #t)
(use "TotalSdLft")
(ng #t)
(use "TotalSdMid")
(ng #t)
(use "TotalSdMid")
(ng #t)
(use "TotalSdRht")

(elim "Ti")
(ng #t)
(use "TotalSdLft")
(ng #t)
(use "TotalSdMid")
(ng #t)
(use "TotalSdMid")
(ng #t)
(use "TotalSdMid")
(ng #t)
(use "TotalSdRht")

(elim "Ti")
(ng #t)
(use "TotalSdLft")
(ng #t)
(use "TotalSdMid")
(ng #t)
(use "TotalSdMid")
(ng #t)
(use "TotalSdRht")
(ng #t)
(use "TotalSdRht")

(elim "Td2")

(elim "Ti")
(ng #t)
(use "TotalSdLft")
(ng #t)
(use "TotalSdMid")
(ng #t)
(use "TotalSdMid")
(ng #t)
(use "TotalSdMid")
(ng #t)
(use "TotalSdRht")

(elim "Ti")
(ng #t)
(use "TotalSdLft")
(ng #t)
(use "TotalSdMid")
(ng #t)
(use "TotalSdMid")
(ng #t)
(use "TotalSdRht")
(ng #t)
(use "TotalSdRht")

(elim "Ti")
(ng #t)
(use "TotalSdMid")
(ng #t)
(use "TotalSdMid")
(ng #t)
(use "TotalSdMid")
(ng #t)
(use "TotalSdRht")
(ng #t)
(use "TotalSdRht")
;; Proof finished.
(save "DTotal")

;; "JDProp"
(set-goal "all d,e,i
  SDToInt d+SDToInt e+2*SDTwoToInt i=SDTwoToInt(J d e i)+4*SDToInt(D d e i)")
(cases)
(cases)
(cases)
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")

(cases)
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")

(cases)
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")

(cases)
(cases)
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")

(cases)
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")

(cases)
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")

(cases)
(cases)
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")

(cases)
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")

(cases)
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
;; Proof finished.
(save "JDProp")

;; "YSatClause"
(set-goal "all i 
 allnc x^,y^(
  TotalRea x^ --> 
  TotalRea y^ --> 
  CoI x^ -> 
  CoI y^ -> 
  exr x^0,y^0 
   ex j,d(
    TotalRea x^0 andr 
    TotalRea y^0 andr 
    x^ +y^ +SDTwoToInt i eqd(x^0+y^0+(SDTwoToInt j+4*SDToInt d))/2 & 
    CoI x^0 & CoI y^0))")
(assume "i" "x^" "y^" "Tx" "Ty" "CoIx" "CoIy")
;; We distinguish cases on CoI x^
(inst-with-to "CoIClause" (pt "x^") "CoIx" "xCases")
(elim "xCases")
(drop "xCases")
(assume "x=0")
;; We distinguish cases on CoI y^
(inst-with-to "CoIClause" (pt "y^") "CoIy" "yCases")
(elim "yCases")
(drop "yCases")
(assume "y=0")

;; Case N,N (i.e., x=0 and y=0)
(intro 0 (pt "x^"))
(intro 0 (pt "y^"))
(ex-intro (pt "J Mid Mid i"))
(ex-intro (pt "D Mid Mid i"))
(split)
(use "Tx")
(split)
(use "Ty")
(split)
(simp "<-" "JDProp")
(ng #t)
;; ?_26:x^ +y^ +SDTwoToInt i eqd(x^ +y^ +2*SDTwoToInt i)/2
;; x+y+i=(x+y+2*i)/2 since x=0 and y=0
;; (use "Lemma5")
;; (use "x=0")
;; (use "y=0")
(simp "x=0")
(simp "y=0")
(ng #t)
;; ?_29:SDTwoToInt i eqd RealDiv(2*SDTwoToInt i)2
(admit)
(split)
(use "CoIx")
(use "CoIy")

;; Case N,A (i.e., x=0 and y=(y1+e1)/2)
(drop "yCases")
(assume "yCases1")
(by-assume "yCases1" "y^1" "y1Prop")
(elim "y1Prop")
(drop "y1Prop")
(assume "Ty1" "ExHyp")
(by-assume "ExHyp" "e1" "y1e1Prop")
(intro 0 (pt "x^"))
(intro 0 (pt "y^1"))
(ex-intro (pt "J Mid e1 i"))
(ex-intro (pt "D Mid e1 i"))
(split)
(use "Tx")
(split)
(use "Ty1")
(split)
(simp "<-" "JDProp")
(ng #t)
;; ?_54:x^ +y^ +SDTwoToInt i eqd(x^ +y^1+(SDToInt e1+2*SDTwoToInt i))/2
;; x+y+i=(x+y1+e1+2*i)/2 since x=0 and y=(y1+e1)/2
;; (use "Lemma6")
;; (use "x=0")
;; (use "y1e1Prop")
(admit)
(split)
(use "CoIx")
(use "y1e1Prop")

;; Now the case x=(x1+d1)/2
(drop "xCases")
(assume "xCases1")
(by-assume "xCases1" "x^1" "x1Prop")
(elim "x1Prop")
(drop "x1Prop")
(assume "Tx1" "ExHyp")
(by-assume "ExHyp" "d1" "x1d1Prop")
;; We again distinguish cases on CoI y^
(inst-with-to "CoIClause" (pt "y^") "CoIy" "yCases")
(elim "yCases")
(drop "yCases")
(assume "y=0")

;; Case A,N (i.e., x=(x1+d1)/2 and y=0)
(intro 0 (pt "x^1"))
(intro 0 (pt "y^"))
(ex-intro (pt "J d1 Mid i"))
(ex-intro (pt "D d1 Mid i"))
(split)
(use "Tx1")
(split)
(use "Ty")
(split)
(simp "<-" "JDProp")
(ng #t)
;; ?_85:x^ +y^ +SDTwoToInt i eqd(x^1+y^ +(SDToInt d1+2*SDTwoToInt i))/2
;; x+y+i=(x1+y+d1+2i)/2 since x=(x1+d1)/2 and y=0
;; (use "Lemma7")
;; (use "x1d1Prop")
;; (use "y=0")
(admit)
(split)
(use "x1d1Prop")
(use "CoIy")

;; Case A,A (i.e., x=(x1+d1)/2 and y=(y1+e1)/2)
(drop "yCases")
(assume "yCases1")
(by-assume "yCases1" "y^1" "y1Prop")
(elim "y1Prop")
(drop "y1Prop")
(assume "Ty1" "ExHyp1")
(by-assume "ExHyp1" "e1" "y1e1Prop")
(intro 0 (pt "x^1"))
(intro 0 (pt "y^1"))
(ex-intro (pt "J d1 e1 i"))
(ex-intro (pt "D d1 e1 i"))
(split)
(use "Tx1")
(split)
(use "Ty1")
(split)
(simp "<-" "JDProp")
;; ?:x^ +y^ +SDTwoToInt i eqd(x^1+y^1+(SDToInt d1+SDToInt e1+2*SDTwoToInt i))/2
;; x+y+i=(x1+y1+d1+e1+2*i)/2 since x=(x1+d1)/2 and y=(y1+e1)/2
;; (use "Lemma8")
;; (use "x1d1Prop")
;; (use "y1e1Prop")
(admit)
(split)
(use "x1d1Prop")
(use "y1e1Prop")
;; Proof finished.
(save "YSatClause")

(define eterm
  (proof-to-extracted-term (theorem-name-to-proof "YSatClause")))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [i,v,v0]
;;  [if (Des v)
;;    [if (Des v0)
;;     (J Mid Mid i@D Mid Mid i@v@v0)
;;     ([dv]J Mid left dv i@D Mid left dv i@v@right dv)]
;;    ([dv]
;;     [if (Des v0)
;;       (J left dv Mid i@D left dv Mid i@right dv@v0)
;;       ([dv0]J left dv left dv0 i@D left dv left dv0 i@right dv@right dv0)])]

(ppc neterm)

;; [i,v,v0]
;;  [case (Des v)
;;    ((DummyL sd@@iv) -> 
;;    [case (Des v0)
;;      ((DummyL sd@@iv) -> J Mid Mid i@D Mid Mid i@v@v0)
;;      (Inr dv -> J Mid left dv i@D Mid left dv i@v@right dv)])
;;    (Inr dv -> 
;;    [case (Des v0)
;;      ((DummyL sd@@iv) -> J left dv Mid i@D left dv Mid i@right dv@v0)
;;      (Inr dv0 ->
;;       J left dv left dv0 i@D left dv left dv0 i@right dv@right dv0)])]

;; This term can be read as follows.  Given i0, v1, v2, destruct the
;; latter two.  If both are composed, i.e., of the form dv3 and dv4,
;; take their components d3,v3 and d4,v4.  Then we obtain J d3 d4 i0
;; pair D d3 d4 i0 pair v3 pair v4.

;; Putting things together

;; "AverageAux"
(set-goal "all i8 allnc x^8,y^8(TotalRea x^8 --> TotalRea y^8 -->
       CoI x^8 -> CoI y^8 -> 
       CoI((x^8+y^8+SDTwoToInt i8)/2/2))")
(assume "i8" "x^8" "y^8" "Tx8" "Ty8" "CoIx8" "CoIy8")
(assert "exr x^1,y^1 ex i1(TotalRea x^1 andr TotalRea y^1 andr
         (x^8+y^8+SDTwoToInt i8)/2/2 eqd(x^1+y^1+SDTwoToInt i1)/2/2 &
         CoI x^1 & CoI y^1)")
 (intro 0 (pt "x^8"))
 (intro 0 (pt "y^8"))
 (ex-intro (pt "i8"))
 (split)
 (use "Tx8")
 (split)
 (use "Ty8")
 (split)
 (use "InitEqD")
 (split)
 (use "CoIx8")
 (use "CoIy8")
(drop "CoIx8")
(drop "CoIy8")
(assume "ExHyp")
(coind "ExHyp")
(drop "ExHyp")
(assume "x^2" "ExHixy")
(intro 1)
(by-assume "ExHixy" "x^" "HypI1")
(by-assume "HypI1" "y^" "HypI2")
(by-assume "HypI2" "i" "iProp")
(elim "iProp")
(drop "iProp")
(assume "Tx" "Ty&x2=(x+y+i)/4")
(elim "Ty&x2=(x+y+i)/4")
(drop "Ty&x2=(x+y+i)/4")
(assume "Ty" "iConj")
(inst-with-to "iConj" 'left "x2=(x+y+i)/4")
(inst-with-to "iConj" 'right "CoIxy")
(drop "iConj")
(inst-with-to "CoIxy" 'left "CoIx")
(inst-with-to "CoIxy" 'right "CoIy")

(cut "exr x^0,y^0 ex j,d(TotalRea x^0 andr TotalRea y^0 andr
    x^ +y^ +SDTwoToInt i eqd((x^0+y^0+ (SDTwoToInt j+4*SDToInt d))/2) &
    CoI x^0 & CoI y^0)")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "ExQuad")
(by-assume "ExQuad" "x^0" "x0Prop")
(by-assume "x0Prop" "y^0" "y0Prop")
(by-assume "y0Prop" "j" "jProp")
(by-assume "jProp" "d" "dProp")
(elim "dProp")
(drop "dProp")
(assume "Tx0" "Conjy0")
(elim "Conjy0")
(drop "Conjy0")
(assume "Ty0" "jdConj")
(inst-with-to "jdConj" 'left "x+y+i=(x0+y0+j+4d)/2")
(inst-with-to "jdConj" 'right "CoIx0y0")
(drop "jdConj")
(inst-with-to "CoIx0y0" 'left "CoIx0")
(inst-with-to "CoIx0y0" 'right "CoIy0")
(drop "CoIx0y0")

(intro 0 (pt "(x^0+y^0+SDTwoToInt j)/2/2"))
(split)
;; ?_80:TotalRea((x^0+y^0+SDTwoToInt j)/2/2)
(admit)
(ex-intro (pt "d"))
(split)
(intro 1)
(intro 0 (pt "x^0"))
(intro 0 (pt "y^0"))
(ex-intro (pt "j"))
(split)
(use "Tx0")
(split)
(use "Ty0")
(split)
(use "InitEqD")
(split)
(use "CoIx0")
(use "CoIy0")
(simp "x2=(x+y+i)/4")
(drop "x2=(x+y+i)/4")
;; ?_98:(x^ +y^ +SDTwoToInt i)/2/2 eqd((x^0+y^0+SDTwoToInt j)/2/2+SDToInt d)/2
(admit)
(use "YSatClause")
(use "Tx")
(use "Ty")
(use "CoIx")
(use "CoIy")
;; Proof finished.
(save "AverageAux")

;; "Average"
(set-goal "allnc x,y(CoI x -> CoI y -> CoI((x+y)/2))")
(assume "x" "y" "CoIx" "CoIy")
(assert "exr x^0,y^0 
  ex i(
   TotalRea x^0 andr 
   TotalRea y^0 andr x+y eqd(x^0+y^0+SDTwoToInt i)/2 & CoI x^0 & CoI y^0)")
 (use "XSubY")
 (use "CoIx")
 (use "CoIy")
(assume "ExHx0y0i")
(by-assume "ExHx0y0i" "x^0" "ExHy0i")
(by-assume "ExHy0i" "y^0" "ExHi")
(by-assume "ExHi" "i" "AndH")
(elim "AndH")
(drop "AndH")
(assume "Tx0" "y0Conj")
(elim "y0Conj")
(drop "y0Conj")
(assume "Ty0" "Hyp")
(inst-with-to  "Hyp" 'left "x+y=(x0+y0+i)/2")
(inst-with-to "Hyp" 'right "CoIx0y0")
(drop "Hyp")
(simp "x+y=(x0+y0+i)/2")
(drop "x+y=(x0+y0+i)/2")
(use "AverageAux")
(use "Tx0")
(use "Ty0")
(use "CoIx0y0")
(use "CoIx0y0")
;; Proof finished.
(save "Average")

(define eterm (proof-to-extracted-term (theorem-name-to-proof "Average")))
(define neterm (nt eterm))
(pp neterm)

(animate "AverageAux")
;; (animate "EqDCompatRev")

(add-var-name "ivw" (py "sdtwo@@iv@@iv"))
(add-var-name "jdvw" (py "sdtwo@@sd@@iv@@iv"))

(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [v,v0]
;;  (CoRec sdtwo@@iv@@iv=>iv)(cXSubY v v0)
;;  ([ivw]
;;    Inr[let jdvw
;;         (cYSatClause left ivw left right ivw right right ivw)
;;         (left right jdvw@
;;          (InR sdtwo@@iv@@iv iv)(left jdvw@right right jdvw))])

(animate "XSubY")
(animate "YSatClause")
(define neterm-average (rename-variables (nt eterm)))
(pp neterm-average)

;; [v,v0]
;;  (CoRec sdtwo@@iv@@iv=>iv)
;;  [if (Des v)
;;    [if (Des v0) (MT@v@v0) ([dv]JOne Mid left dv@v@right dv)]
;;    ([dv]
;;     [if (Des v0)
;;       (JOne left dv Mid@right dv@v0)
;;       ([dv0]JOne left dv left dv0@right dv@right dv0)])]
;;  ([ivw]
;;    Inr[let jdvw
;;         [if (Des left right ivw)
;;          [if (Des right right ivw)
;;           (J Mid Mid left ivw@D Mid Mid left ivw@right ivw)
;;           ([dv]
;;            J Mid left dv left ivw@
;;            D Mid left dv left ivw@left right ivw@right dv)]
;;          ([dv]
;;           [if (Des right right ivw)
;;             (J left dv Mid left ivw@
;;             D left dv Mid left ivw@right dv@right right ivw)
;;             ([dv0]
;;              J left dv left dv0 left ivw@
;;              D left dv left dv0 left ivw@right dv@right dv0)])]
;;         (left right jdvw@
;;          (InR sdtwo@@iv@@iv iv)(left jdvw@right right jdvw))])

(set! COMMENT-FLAG #t)

;; Examples and Haskell extraction
;; ===============================

;; Plan: transform reals into streams, using StandardSplit.  Define a
;; function from the reals into (the cototal ideals in) iv by
;; corecursion.

;; To enable normalization it is better to work with / rather than #

;; Standard Split
(set-goal "all a(a<IntN 1/4 orr IntN 1/4<=a & a<1/4 oru 1/4<=a)")
(cases)
(cases)
(assume "p" "q")
(ng #t)
(intro 1)
(cases (pt "SZero(SZero p)<q"))
(assume "4p<q")
(intro 0)
(split)
(use "Truth")
(use "Truth")
(assume "4p<q -> F")
(intro 1)
(use "PosNotLtToLe")
(use "4p<q -> F")
;; 4
(assume "p")
(ng #t)
(intro 1)
(intro 0)
(split)
(use "Truth")
(use "Truth")
;; 5
(assume "p" "q")
(ng #t)
(cases (pt "SZero(SZero p)<=q"))
(assume "4p<=q")
(intro 1)
(intro 0)
(split)
(use "Truth")
(use "Truth")
(assume "4p<=q -> F")
(intro 0)
(use "PosNotLeToLt")
(use "4p<=q -> F")
;; Proof finished.
(save "StandardSplit")

(ppc (rename-variables
      (nt (proof-to-extracted-term (theorem-name-to-proof "StandardSplit")))))

;; [a]
;;  [case a
;;    (k#p -> 
;;    [case k
;;      (p0 -> Inr(SZero(SZero p0)<p))
;;      (0 -> Inr True)
;;      (IntN p0 -> 
;;      [case (SZero(SZero p0)<=p)
;;        (True -> Inr True)
;;        (False -> (DummyL boole))])])]

;; SplitProp for concrete reals.

;; AxRealLeft
(pp (nf (pf "a<=(IntN 1#4) -> x<<=a+(1#4) -> x<<=0")))

;; AxRealMiddleLB
(pp (nf (pf "(IntN 1#4)<=a -> a-(1#4)<<=x -> (IntN 1#2)<<=x")))

;; AxRealMiddleUB
(pp (nf (pf "a<=(1#4) -> x<<=a+(1#4) -> x<<=(1#2)")))

;; AxRealLeftRight
(pp (nf (pf "(1#4)<=a -> a-(1#4)<<=x -> 0<<=x")))

;; AxVaIntroLB
(pp (nf (pf "a-(1#PosS p)<<=x -> 2*a-SDToInt d-(1#p)<<=2*x-SDToInt d")))

;; AxVaIntroUB
(pp (nf (pf "x<<=a+(1#PosS p) -> 2*x-SDToInt d<<=2*a-SDToInt d+(1#p)")))

;; ;; SplitProp
;; (set-goal "allnc x(ex a(a-(1#4)<<=x & x<<=a+(1#4)) ->
;;            exl d((SDToInt d-1#2)<<=x & x<<=(SDToInt d+1#2)))")
;; (assume "x")
;; (use "Id")
;; (assume "ExHyp")
;; (by-assume "ExHyp" "a" "aProp")
;; (inst-with-to "StandardSplit" (pt "a") "SSa")
;; (elim "SSa")
;; (drop "SSa")
;; ;a Left
;; (assume "a Left")
;; (intro 0 (pt "Lft"))
;; (ng #t)
;; ;; ?_15:(IntN 2#2)<<=x & x<<=(0#2)

;; (pp (nt (pt "0/2"))) ;0
;; (pp (nt (pt "IntN 2/2"))) ;IntN 1
;; Hence to enable normalization it is better to work with / rather than #
;; This should also apply to StandardSplit

(add-global-assumption
 "AxRealLeft"
 "all x,a(a<IntN 1/4 -> x<<=a+1/4 -> x<<=0)")
;;(remove-global-assumption "AxRealLeft")

(add-global-assumption
 "AxRealMiddleLB"
 "all x,a(IntN 1/4<=a -> a-1/4<<=x -> IntN 1/2<<=x)")

(add-global-assumption
 "AxRealMiddleUB"
 "all x,a(a<=1/4 -> x<<=a+1/4 -> x<<=1/2)")

(add-global-assumption
 "AxRealRight"
 "all x,a(1/4<=a -> a-1/4<<=x -> 0<<=x)")

(add-global-assumption
 "RatLtToLe"
 "all rat1,rat2(rat1<rat2 -> rat1<=rat2)")

;; SplitProp
(set-goal "allnc x^(TotalRea x^ -->
           IntN 1<<=x^ -> x^ <<=1 -> ex a(a-1/4<<=x^ & x^ <<=a+1/4) ->
           ex d((SDToInt d-1)/2<<=x^ & x^ <<=(SDToInt d+1)/2))")
(use "AllncTotalElim")
(assume "x" "-1<=x" "x<=1")
;; (use "Id")
(assume "ExHyp")
(by-assume "ExHyp" "a" "aProp")
(inst-with-to "StandardSplit" (pt "a") "SSa")
(elim "SSa")
(drop "SSa")
;a Left
(assume "a Left")
(ex-intro (pt "Lft"))
(ng #t)
;; ?_15:IntN 1<<=x & x<<=0
(split)
(use "-1<=x")
(use "AxRealLeft" (pt "a"))
(use "a Left")
(use "aProp")
(assume "SSa Mid Right")
(elim "SSa Mid Right")
;a Middle
(assume "a Middle")
(ex-intro (pt "Mid"))
(ng #t)
(split)
(use "AxRealMiddleLB" (pt "a"))
(use "a Middle")
(use "aProp")
(use "AxRealMiddleUB" (pt "a"))
(use "RatLtToLe")
(use "a Middle")
(use "aProp")
;a Right
(assume "a Right")
(ex-intro (pt "Rht"))
(ng #t)
(split)
(use "AxRealRight" (pt "a"))
(use "a Right")
(use "aProp")
(use "x<=1")
;; Proof finished.
(save "SplitProp")
;; (remove-theorem "SplitProp")

(define eterm (proof-to-extracted-term (theorem-name-to-proof "SplitProp")))

(animate "StandardSplit")
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [a]
;;  [case a
;;    (k#p -> 
;;    [case k
;;      (p0 -> [case (SZero(SZero p0)<p) (True -> Mid) (False -> Rht)])
;;      (0 -> Mid)
;;      (IntN p0 -> [case (SZero(SZero p0)<=p) (True -> Mid) (False -> Lft)])])]

(add-global-assumption
 "AxVaIntroLB"
 "all x^,a,n,d(TotalRea x^ ->
  a-1/2**Succ n<<=x^ -> 2*a-SDToInt d-1/2**n<<=2*x^ -SDToInt d)")

;; "CauchySds"
(set-goal "allnc x^(
 TotalRea x^ andr IntN 1<<=x^ & x^ <<=1 &
 all n ex a(a-1/2**n<<=x^ & x^ <<=a+1/2**n) -> CoI x^)")
(assume "x^" "Qx")
(coind "Qx") ;produces ex d
(drop "Qx")
(assume "x^1" "Qx1")
(intro 1)
(elim "Qx1")
(drop "Qx1")
(assume "Tx1" "Conj1")
(inst-with-to "Conj1" 'left "-1<=x1")
(inst-with-to "Conj1" 'right 'left "x1<=1")
(inst-with-to "Conj1" 'right 'right "AEHyp")
(drop "Conj1")
(assert "ex d((SDToInt d-1)/2<<=x^1& x^1 <<=(SDToInt d+1)/2)")
 (use "SplitProp")
 (use "Tx1")
 (use "-1<=x1")
 (use "x1<=1")
 (inst-with-to "AEHyp" (pt "Succ(Succ Zero)") "AEHypInst")
 (ng "AEHypInst")
 (use "AEHypInst")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "ExHyp")
(by-assume "ExHyp" "d" "dProp")
(intro 0 (pt "2*x^1-SDToInt d"))
(split)
(use "RealMinusTotal")
(use "RealTimesTotal")
(use "TotalReaPos")
(use "Tx1")
(use "TotalReaInt")
(ex-intro (pt "d"))
(split)
(intro 1)
(split)
(use "RealMinusTotal")
(use "RealTimesTotal")
(use "TotalReaPos")
(use "Tx1")
(use "TotalReaInt")
(split)
;; ?_48:IntN 1<<=2*x^1-SDToInt d follows from (SDToInt d-1)/2<<=x^1
(admit)
(split)
;; ?_50:2*x^1-SDToInt d<<=1 follows from x^1<<=(SDToInt d+1)/2
(admit)
(assume "n")
(inst-with-to "AEHyp" (pt "Succ n") "ExHyp1")
(by-assume "ExHyp1" "a" "aProp")
(ex-intro (pt "2*a-SDToInt d"))
(split)
(use "AxVaIntroLB")
(use "Tx1")
(use "aProp")
(drop "AEHyp")
;; ?_63:2*x^1-SDToInt d<<=2*a-SDToInt d+1/2**n follows from x^1<<=a+1/2**Succ n
(admit)
;; ?_40:x^1 eqd(2*x^1-SDToInt d+SDToInt d)/2
(admit)
;; Proof finished.
(save "CauchySds")

;; ;; "PropA"
;; (set-goal "allnc x^(
;;  TotalRea x^ andr IntN 1<<=x^ andr x^ <<=1 andr
;;  all n ex a(a-1/2**n<<=x^ & x^ <<=a+1/2**n) -> CoI x^)")
;; (assume "x^" "Qx")
;; (coind "Qx") ;produces ex d
;; (drop "Qx")
;; (assume "x^1" "Qx1")
;; (intro 1)
;; (elim "Qx1")
;; (drop "Qx1")
;; (assume "Tx1" "Conj1")
;; (elim "Conj1")
;; (drop "Conj1")
;; (assume "-1<=x1" "Conj2")
;; (elim "Conj2")
;; (drop "Conj2")
;; (assume "x1<=1" "AEHyp")
;; (assert "ex d((SDToInt d-1)/2<<=x^1& x^1 <<=(SDToInt d+1)/2)")
;;  (use "SplitProp")
;;  (use "Tx1")
;;  (use "-1<=x1")
;;  (use "x1<=1")
;;  (inst-with-to "AEHyp" (pt "Succ(Succ Zero)") "AEHypInst")
;;  (ng "AEHypInst")
;;  (use "AEHypInst")
;; (use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
;; (assume "ExHyp")
;; (by-assume "ExHyp" "d" "dProp")
;; (intro 0 (pt "2*x^1-SDToInt d"))
;; (split)
;; (admit)
;; (ex-intro (pt "d"))
;; (split)
;; (intro 1)
;; (split)
;; (admit)
;; (split)
;; (admit)
;; (split)
;; (admit)
;; (assume "n")
;; (inst-with-to "AEHyp" (pt "Succ n") "Hex")
;; (by-assume "Hex" "a" "aProp")
;; (ex-intro (pt "2*a-SDToInt d"))
;; (split)
;; (add-global-assumption
;;  "AxVaIntroLB"
;;  "all x^,a,n,d(TotalRea x^ ->
;;   a-1/2**Succ n<<=x^ -> 2*a-SDToInt d-1/2**n<<=2*x^ -SDToInt d)")
;; (use "AxVaIntroLB")
;; (use "Tx1")
;; (use "aProp")
;; (drop "AEHyp")
;; (admit) ;follows from aProp
;; (admit)
;; ;; Proof finished.
;; (save "PropA")

(define eterm-cauchysds
  (proof-to-extracted-term (theorem-name-to-proof "CauchySds")))

(animate "SplitProp")
(define neterm-cauchysds (rename-variables (nt eterm-cauchysds)))
(pp neterm-cauchysds)

;; [as]
;;  (CoRec (nat=>rat)=>iv)as
;;  ([as0]
;;    Inr[let d
;;         [if (as0(Succ(Succ Zero)))
;;          ([k,p]
;;           [if k
;;             ([p0][if (SZero(SZero p0)<p) Mid Rht])
;;             Mid
;;             ([p0][if (SZero(SZero p0)<=p) Mid Lft])])]
;;         (d@(InR nat=>rat iv)([n]2*as0(Succ n)-SDToInt d))])

(ppc neterm-cauchysds)

;; [as]
;;  (CoRec (nat=>rat)=>iv)as
;;  ([as0]
;;    Inr[let d
;;         [case (as0(Succ(Succ Zero)))
;;          (k#p -> 
;;          [case k
;;            (p0 -> [case (SZero(SZero p0)<p) (True -> Mid) (False -> Rht)])
;;            (0 -> Mid)
;;            (IntN p0 -> 
;;            [case (SZero(SZero p0)<=p) (True -> Mid) (False -> Lft)])])]
;;         (d@(InR nat=>rat iv)([n]2*as0(Succ n)-SDToInt d))])

(add-program-constant "Sqrt" (py "rat=>nat=>rat"))

(add-computation-rules
 "Sqrt a Zero" "Succ Zero"
 "Sqrt a(Succ n)" "(Sqrt a n+a/Sqrt a n)/2")

;; (pp (nt (pt "Sqrt 2(PosToNat 3)"))) ;577#408

(add-program-constant "HalfSqrtTwo" (py "nat=>rat"))

(add-computation-rules
 "HalfSqrtTwo n" "Sqrt 2 n/2")

(define halfsqrttwo (pt "HalfSqrtTwo"))

(define threebyfour (pt "[n](3#4)"))

'(
(terms-to-haskell-program
 "~/temp/average.hs"
 (list (list neterm-average "neterm_average")
       (list neterm-cauchysds "neterm_cauchysds")
       (list halfsqrttwo "halfsqrttwo")
       (list threebyfour "threebyfour")))
)

'(
{- takeIv -}
takeIv _ II = []
takeIv 0 (C d x) = []
takeIv n (C d x) = (show d) : (takeIv (n-1) x)
)

;; How to run the haskell program.
;; 1.  evaluate 
'(
(terms-to-haskell-program
 "~/temp/average.hs"
 (list (list neterm-average "neterm_average")
       (list neterm-cauchysds "neterm_cauchysds")
       (list halfsqrttwo "halfsqrttwo")
       (list threebyfour "threebyfour")))
)
;; 2.  Copy into avarage.hs the definition of takeIv:
'(
{- takeIv -}
takeIv _ II = []
takeIv 0 (C d x) = []
takeIv n (C d x) = (show d) : (takeIv (n-1) x)
)
;; 3.  In a terminal type ghci average.hs.  The result is
'(
GHCi, version 7.0.4: http://www.haskell.org/ghc/  :? for help
Loading package ghc-prim ... linking ... done.
Loading package integer-gmp ... linking ... done.
Loading package base ... linking ... done.
Loading package ffi-1.0 ... linking ... done.
[1 of 1] Compiling Main             ( average.hs, interpreted )
Ok, modules loaded: Main.
*Main> 
)
;; 4.  In *Main: type takeIv 10 (neterm_cauchysds halfsqrttwo)
;; The result is
'(
["Rht","Rht","Mid","Lft","Rht","Lft","Rht","Lft","Mid","Mid"]
)
;; 5.  Type further commands, for instance
'(
*Main> takeIv 9 (neterm_average (neterm_cauchysds halfsqrttwo) (neterm_cauchysds threebyfour))
["Rht","Rht","Mid","Mid","Lft","Rht","Lft","Mid","Rht","Mid"]
)
;; 6.  To quit type *Main> :q.  The result is
'(
Leaving GHCi.
bash-3.2$ 
)

(define (sds-to-number sds)
  (if (null? sds)
      0
      (let ((prev (sds-to-number (cdr sds)))
	    (sd (car sds)))
	(cond ((equal? "Lft" sd) (- (/ prev 2) .5))
	      ((equal? "Mid" sd) (/ prev 2))
	      ((equal? "Rht" sd) (+ (/ prev 2) .5))
	      (else (myerror "Unexpected argument"))))))

(sds-to-number '("Rht" "Rht" "Mid" "Mid" "Lft" "Rht" "Lft" "Mid" "Rht"))
;; 0.728515625

(/ (+ (/ (sqrt 2) 2) (/ 3 4)) 2)
;; 0.7285533905932737

(/ 1.0 256)
