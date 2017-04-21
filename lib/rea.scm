;; 2017-04-19.  rea.scm.  Based on numbers.scm.

;; (load "~/git/minlog/init.scm")

;; (set! COMMENT-FLAG #f)
;; (libload "nat.scm")
;; (libload "pos.scm")
;; (libload "int.scm")
;; (libload "rat.scm")
;; (set! COMMENT-FLAG #t)

(if (not (assoc "nat" ALGEBRAS))
    (myerror "First execute (libload \"nat.scm\")")
    (if (not (assoc "pos" ALGEBRAS))
	(myerror "First execute (libload \"pos.scm\")")
	(if (not (assoc "int" ALGEBRAS))
	    (myerror "First execute (libload \"int.scm\")")
	    (if (not (assoc "rat" ALGEBRAS))
		(myerror "First execute (libload \"rat.scm\")")))))

(display "loading rea.scm ...") (newline)

;; 1.  Real numbers
;; ================

;; We introduce the reals.  A real is a pair of a Cauchy sequence of
;; rationals and a modulus.  We view real as a data type (i.e., no
;; properties), and within this data type inductively define the
;; predicate Real x, meaning that x is a (proper) real.

(add-alg "rea" (list "RealConstr" "(nat=>rat)=>(pos=>nat)=>rea"))
(add-totality "rea")
(add-totalnc "rea")
(add-co "TotalRea")
;; (add-co "TotalReaNc")

;; (add-eqp "rea")
;; (add-co "EqPRea")
;; (add-eqpnc "rea")
;; (add-co "EqPReaNc")
(add-var-name "as" "bs" "cs" "ds" (py "nat=>rat"))
(add-var-name "M" "N" "L" (py "pos=>nat"))
(add-var-name "x" "y" "z" (py "rea"))

;; ReaTotalVar
(set-goal "all x TotalRea x")
(cases)
(assume "as" "M")
(use "TotalReaRealConstr")
(use "AllTotalElim")
(assume "n")
(use "RatTotalVar")
(use "AllTotalElim")
(assume "p")
(use "NatTotalVar")
;; Proof finished.
(save "ReaTotalVar")

;; To conveniently access the two fields of a real, we provide seq and
;; mod as informative names to be used (postfix) in display strings.

(add-program-constant "RealSeq" (py "rea=>nat=>rat") t-deg-zero 'const 1)

(add-token
 "seq"
 'postfix-op
 (lambda (x)
   (mk-term-in-app-form
    (make-term-in-const-form (pconst-name-to-pconst "RealSeq"))
    x)))

(add-display
 (py "nat=>rat")
 (lambda (x)
   (let ((op (term-in-app-form-to-final-op x))
	 (args (term-in-app-form-to-args x)))
     (if (and (term-in-const-form? op)
	      (string=? "RealSeq"
			(const-to-name (term-in-const-form-to-const op)))
	      (= 1 (length args)))
	 (let ((arg (car args)))
	   (list
	    'postfix-op "seq"
	    (term-to-token-tree arg)))
	 #f))))

(add-computation-rules
 "(RealConstr as M)seq" "as")

;; RealSeqTotal
(set-totality-goal "RealSeq")
(use "AllTotalElim")
(cases)
(assume "as" "M")
(use "AllTotalElim")
(assume "n")
(ng)
(use "RatTotalVar")
;; Proof finished.
(save-totality)

(add-program-constant "RealMod" (py "rea=>pos=>nat") t-deg-zero 'const 1)

(add-token
 "mod"
 'postfix-op
 (lambda (x)
   (mk-term-in-app-form
    (make-term-in-const-form (pconst-name-to-pconst "RealMod"))
    x)))

(add-display
 (py "pos=>nat")
 (lambda (x)
   (let ((op (term-in-app-form-to-final-op x))
	 (args (term-in-app-form-to-args x)))
     (if (and (term-in-const-form? op)
	      (string=? "RealMod"
			(const-to-name (term-in-const-form-to-const op)))
	      (= 1 (length args)))
	 (let ((arg (car args)))
	   (list
	    'postfix-op "mod"
	    (term-to-token-tree arg)))
	 #f))))

(add-computation-rules
 "(RealConstr as M)mod" "M")

;; RealModTotal
(set-totality-goal "RealMod")
(use "AllTotalElim")
(cases)
(assume "as" "M")
(use "AllTotalElim")
(assume "p")
(ng)
(use "NatTotalVar")
;; Proof finished.
(save-totality)

;; (pp (pt "x seq n"))
;; (pp (pt "x mod p"))

;; 2. Parsing and display for arithmetical operations
;; ==================================================

(add-item-to-algebra-edge-to-embed-term-alist
 "rat" "rea"
 (let ((var (make-var (make-alg "rat") -1 t-deg-one ""))
       (n (make-var (make-alg "nat") -1 t-deg-one ""))
       (l (make-var (make-alg "nat") -1 t-deg-one "")))
   (make-term-in-abst-form
    var (mk-term-in-app-form
         (make-term-in-const-form
          (constr-name-to-constr "RealConstr"))
         (make-term-in-abst-form ;constant Cauchy sequence
          n (make-term-in-var-form var))
         (make-term-in-abst-form ;Zero modulus
          l (make-term-in-const-form
             (constr-name-to-constr "Zero")))))))

;; (alg-le? (make-alg "rat") (make-alg "rea"))

(add-program-constant "RealPlus" (py "rea=>rea=>rea"))
(add-program-constant "RealUMinus" (py "rea=>rea"))
(add-program-constant "RealMinus" (py "rea=>rea=>rea"))
(add-program-constant "RealTimes" (py "rea=>rea=>rea"))
(add-program-constant "RealDiv" (py "rea=>rea=>rea"))
(add-program-constant "RealAbs" (py "rea=>rea"))
(add-program-constant "RealExp" (py "rea=>int=>rea"))
(add-program-constant "RealMax" (py "rea=>rea=>rea"))
(add-program-constant "RealMin" (py "rea=>rea=>rea"))

(add-token-and-type-to-name "+" (py "rea") "RealPlus")
(add-token-and-type-to-name "~" (py "rea") "RealUMinus")
(add-token-and-type-to-name "-" (py "rea") "RealMinus")
(add-token-and-type-to-name "*" (py "rea") "RealTimes")
(add-token-and-type-to-name "/" (py "rea") "RealDiv")
(add-token-and-type-to-name "abs" (py "rea") "RealAbs")

(add-token-and-types-to-name "**" (list (py "rea") (py "pos")) "RealExp")
(add-token-and-types-to-name "**" (list (py "rea") (py "nat")) "RealExp")
(add-token-and-types-to-name "**" (list (py "rea") (py "int")) "RealExp")

(add-token-and-type-to-name "max" (py "rea") "RealMax")
(add-token-and-type-to-name "min" (py "rea") "RealMin")

(add-display (py "rea") (make-display-creator "RealPlus" "+" 'add-op))
(add-display (py "rea") (make-display-creator1 "RealUMinus" "~" 'prefix-op))
(add-display (py "rea") (make-display-creator "RealMinus" "-" 'add-op))
(add-display (py "rea") (make-display-creator "RealTimes" "*" 'mul-op))
(add-display (py "rea") (make-display-creator "RealDiv" "/" 'mul-op))
(add-display (py "rea") (make-display-creator1 "RealAbs" "abs" 'prefix-op))
(add-display (py "rea") (make-display-creator "RealExp" "**" 'exp-op))
(add-display (py "rea") (make-display-creator "RealMax" "max" 'mul-op))
(add-display (py "rea") (make-display-creator "RealMin" "min" 'mul-op))

(add-display
 (py "rea")
 (lambda (x)
   (let ((op (term-in-app-form-to-final-op x))
	 (args (term-in-app-form-to-args x)))
     (if (and (term-in-const-form? op)
	      (string=? "RealConstr"
			(const-to-name (term-in-const-form-to-const op)))
	      (= 2 (length args))
	      (term-in-abst-form? (car args))
	      (not (member (term-in-abst-form-to-var (car args))
			   (term-to-free
			    (term-in-abst-form-to-kernel (car args))))))
	 (term-to-token-tree (term-to-original
			      (term-in-abst-form-to-kernel (car args))))
	 #f))))

;; (pp (pt "(IntN p#q)+RealConstr([n]1)([p]7)"))
;; (IntN p#q)+1

;; 3.  Arithmetic
;; ==============

;; RealPos is a decidable property and hence can be considered as a
;; program constant.

(add-program-constant "RealPos" (py "rea=>pos=>boole"))

(add-display
 (make-alg "boole")
 (lambda (x)
   (let ((op (term-in-app-form-to-final-op x))
	 (args (term-in-app-form-to-args x)))
     (if (and (term-in-const-form? op)
	      (string=? "RealPos"
			(const-to-name (term-in-const-form-to-const op)))
	      (= 2 (length args)))
	 (let ((arg1 (car args))
	       (arg2 (cadr args)))
	   (list
	    'appterm ""
	    (list
	     'appterm ""
	     (list 'const "RealPos")
	     (term-to-token-tree (term-to-original arg1)))
	    (term-to-token-tree (term-to-original arg2))))
	 #f))))

(add-computation-rules "RealPos(RealConstr as M)p" "(1#2**p)<=as(M(p+1))")

;; RealPosTotal
(set-totality-goal "RealPos")
(use "AllTotalElim")
(cases)
(assume "as" "M")
(use "AllTotalElim")
(assume "p")
(ng)
(use "BooleTotalVar")
;; Proof finished.
(save-totality)

;; RealLt is a decidable property and hence can be considered as a
;; program constant.

(add-program-constant "RealLt" (py "rea=>rea=>pos=>boole"))

(add-display
 (make-alg "boole")
 (lambda (x)
   (let ((op (term-in-app-form-to-final-op x))
	 (args (term-in-app-form-to-args x)))
     (if (and (term-in-const-form? op)
	      (string=? "RealLt"
			(const-to-name (term-in-const-form-to-const op)))
	      (= 3 (length args)))
	 (let ((arg1 (car args))
	       (arg2 (cadr args))
	       (arg3 (caddr args)))
	   (list
	    'appterm ""
	    (list
	     'appterm ""
	     (list
	      'appterm ""
	      (list 'const "RealLt")
	      (term-to-token-tree (term-to-original arg1)))
	     (term-to-token-tree (term-to-original arg2)))
	    (term-to-token-tree (term-to-original arg3))))
	 #f))))

(add-computation-rules
 "RealLt(RealConstr as M)(RealConstr bs N)p"
 "RealPos(RealConstr bs N-RealConstr as M)p")

;; Rules for RealUMinus

(add-computation-rules
 "~(RealConstr as M)" "RealConstr([n]~(as n))M")

;; RealUMinusTotal
(set-totality-goal "RealUMinus")
(use "AllTotalElim")
(cases)
(assume "as" "M")
(ng)
(use "ReaTotalVar")
;; Proof finished.
(save "RealUMinusTotal")

;; Rules for RealPlus

(add-computation-rules
 "RealConstr as M+RealConstr bs N"
 "RealConstr([n]as n+bs n)([p]M(PosS p)max N(PosS p))")

;; RealPlusTotal
(set-totality-goal "RealPlus")
(use "AllTotalElim")
(cases)
(assume "as" "M")
(use "AllTotalElim")
(cases)
(assume "bs" "N")
(ng)
(use "ReaTotalVar")
;; Proof finished.
(save-totality)

;; Rules for RealMinus

(add-computation-rules
 "x-y" "x+ ~y")

;; Code discarded 2016-06-23
;; (add-computation-rules
;;  "RealConstr as M-RealConstr bs N"
;;  "RealConstr([n]as n-bs n)([p]M(PosS p)max N(PosS p))")

;; RealMinusTotal
(set-totality-goal "RealMinus")
(use "AllTotalElim")
(assume "x")
(use "AllTotalElim")
(assume "y")
(ng)
(use "ReaTotalVar")
;; Proof finished.
(save-totality)

;; RealLtTotal
(set-totality-goal "RealLt")
(use "AllTotalElim")
(cases)
(assume "as" "M")
(use "AllTotalElim")
(cases)
(assume "bs" "N")
(use "AllTotalElim")
(assume "p")
(ng)
(use "BooleTotalVar")
;; Proof finished.
(save-totality)

;; Rules for RealAbs

(add-computation-rules
 "abs(RealConstr as M)" "RealConstr([n]abs(as n))M")

;; RealAbsTotal
(set-totality-goal "RealAbs")
(use "AllTotalElim")
(cases)
(assume "as" "M")
(ng)
(use "ReaTotalVar")
;; Proof finished.
(save-totality)

(add-program-constant "RealInv" (py "rea=>pos=>rea"))

(add-computation-rules
 "RealInv(RealConstr as M)q"
 "RealConstr([n]1/as n)([p]M(2*PosS q+p)max M(PosS q))")

;; RealInvTotal
(set-totality-goal "RealInv")
(use "AllTotalElim")
(cases)
(assume "as" "M")
(use "AllTotalElim")
(assume "p")
(ng)
(use "ReaTotalVar")
;; Proof finished.
(save-totality)

;; Rules for RealExp : rea=>int=>rea

(add-computation-rules
 "x**(IntP One)" "x"
 "x**(IntP(SZero p))" "(x**(IntP p))*(x**(IntP p))"
 "x**(IntP(SOne p))" "(x**(IntP(SZero p)))*x"
 "x**IntZero" "RealConstr([n](RatConstr(IntPos One)One))([p]Zero)")

;; Rules for RealTimes require RealBound and hence can only be added later

;; 4.  Inductive predicates Cauchy, Mon, Real
;; ==========================================

;; To work with reals, we use a predicate constant Cauchy which takes
;; two arguments, a sequence of rationals and a modulus.

;; We introduce Cauchy as an inductively defined predicate (which may
;; in this case also be called a record).

(add-ids
 (list (list "Cauchy" (make-arity (py "nat=>rat") (py "pos=>nat"))))
 '("all as,M(
    all p,n,m(M p<=n -> M p<=m -> abs(as n+ ~(as m))<=(1#2**p)) -> Cauchy as M)"
   "CauchyIntro"))

;; Similarly, we introduce a predicate constant Mon, taking a sequence
;; of positive numbers as argument, to express monotonicity.

(add-ids (list (list "Mon" (make-arity (py "pos=>nat"))))
	 '("all M(all p,q(p<=q -> M p<=M q) -> Mon M)" "MonIntro"))

;; CauchyElim
(set-goal
 "all as,M(Cauchy as M ->
           all p,n,m(M p<=n -> M p<=m -> abs(as n+ ~(as m))<=(1#2**p)))")
(assume "as" "M")
(elim)
(search)
;; Proof finished.
(save "CauchyElim")

;; MonElim
(set-goal "all M(Mon M -> all p,q(p<=q -> M p<=M q))")
(assume "M")
(elim)
(search)
;; Proof finished.
(save "MonElim")

;; We introduce Real as an inductively defined predicate (which in this
;; case may also be called a record).  Then we can prove theorems:

;; RealIntro: all x(Cauchy(x seq)(x mod) -> Mon(x mod) -> Real x)
;; RealToCauchySeq: all as,M(Real(RealConstr as M) -> Cauchy as M)
;; RealToMonMod: all as,M(Real(RealConstr as M) -> Mon M)

;; Alternative formulation (worse, since usability is restricted)
;; RealIntro: all as,M(Cauchy as M -> Mon M -> Real RealConstr as M) 
;; RealToCauchySeq: all x(Real x -> Cauchy(x seq)(x mod))
;; RealToMonMod: all x(Real x -> Mon(x mod))

(add-ids
 (list (list "Real" (make-arity (py "rea"))))
 '("all x(Cauchy(x seq)(x mod) -> Mon(x mod) -> Real x)" "RealIntro"))

;; RealToCauchy
(set-goal "all x(Real x -> Cauchy(x seq)(x mod))")
(assume "x")
(elim)
(auto)
;; Proof finished.
(save "RealToCauchy")

;; RealToMon
(set-goal "all x(Real x -> Mon(x mod))")
(assume "x")
(elim)
(auto)
;; Proof finished.
(save "RealToMon")

;; The following variants will be more useful, because their heads will
;; be more often of the form of a given goal.

;; RealConstrToCauchy
(set-goal "all as,M(Real(RealConstr as M) -> Cauchy as M)")
(strip)
(use-with "RealToCauchy" (pt "RealConstr as M") 1)
;; Proof finished.
(save "RealConstrToCauchy")

;; RealConstrToMon
(set-goal "all as,M(Real(RealConstr as M) -> Mon M)")
(strip)
(use-with "RealToMon" (pt "RealConstr as M") 1)
;; Proof finished.
(save "RealConstrToMon")

;; RealRat
(set-goal "all a Real a")
(assume "a")
(use "RealIntro")
(use "CauchyIntro")
(assume "p" "n" "m" "Useless1" "Useless2")
(ng #t)
(simprat (pf "a+ ~a==0"))
(use "Truth")
(use "Truth")
(use "MonIntro")
(assume "p" "q" "p<=q")
(ng)
(use "Truth")
;; Proof finished.
(save "RealRat")

;; 4a.  RealTimes
;; ==============

;; Rules for RealTimes require RealBound and hence can only be defined
;; when Cauchy is defined.

;; Use cNatPos instead of the pconst NatToPos to block unwanted unfoldings

;; NatPos
(set-goal "all n exl p p=NatToPos n")
(assume "n")
(intro 0 (pt "NatToPos n"))
(use "Truth")
;; Proof finished.
(save "NatPos")

(animate "NatPos")

;; NatPosExFree
(set-goal "all n cNatPos n=NatToPos n")
(assume "n")
(use "Truth")
;; Proof finished.
(save "NatPosExFree")

(deanimate "NatPos")

;; Every real has an upper bound, that is the reals are Archimedian ordered.

;; RatLeAbsBoundSeq
(set-goal "all as,l exl n all m(m<l -> abs(as m)<=2**n)")
(assume "as")
(ind)
;; 3,4
(intro 0 (pt "Zero"))
(assume "m" "Absurd")
(use "EfqAtom")
(use "Absurd")
;; 4
(assume "l" "IH")
(by-assume "IH" "n" "nProp")
(inst-with-to "RatLeAbsBound" (pt "as l") "ExHyp")
(by-assume "ExHyp" "n1" "n1Prop")
(intro 0 (pt "n max n1"))
(assume "m" "m<l+1")
(use "NatLtSuccCases" (pt "m") (pt "l"))
(use "m<l+1")
(assume "m<l")
(use "RatLeTrans" (pt "(2**n#One)"))
(use "nProp")
(use "m<l")
(ng)
(use "PosLeMonPosExp")
(use "NatMaxUB1")
(assume "m=l")
(simp "m=l")
(use "RatLeTrans" (pt "(2**n1#One)"))
(use "n1Prop")
(ng)
(use "PosLeMonPosExp")
(use "NatMaxUB2")
;; Proof finished.
(save "RatLeAbsBoundSeq")

(pp (rename-variables
     (nt (proof-to-extracted-term (theorem-name-to-proof "RatLeAbsBoundSeq")))))
;; [as,n](Rec nat=>nat)n Zero([n0,n1]n1 max cRatLeAbsBound(as n0))

(animate "RatLeAbsBoundSeq")

;; RatLeAbsBoundSeqExFree
(set-goal "all as,l,m(m<l -> abs(as m)<=2**cRatLeAbsBoundSeq as l)")
(assume "as")
(ind)
;; 3,4
(assume "m" "Absurd")
(use "EfqAtom")
(use "Absurd")
;; 4
(assume "l" "IH" "m" "m<l+1")
(use "NatLtSuccCases" (pt "m") (pt "l"))
(use "m<l+1")
(assume "m<l")
(use "RatLeTrans" (pt "(2**cRatLeAbsBoundSeq as l#1)"))
(use "IH")
(use "m<l")
(ng)
(use "PosLeMonPosExp")
(use "NatMaxUB1")
(assume "m=l")
(simp "m=l")
(assert "cRatLeAbsBoundSeq as(Succ l)=
         cRatLeAbsBoundSeq as l max cRatLeAbsBound(as l)")
 (use "Truth")
(assume "EqHyp")
(simp "EqHyp")
(drop "EqHyp")
(use "RatLeTrans" (pt "(2**cRatLeAbsBound(as l)#One)"))
(use "RatLeAbsBoundExFree")
(use "PosLeMonPosExp")
(use "NatMaxUB2")
;; Proof finished.
(save "RatLeAbsBoundSeqExFree")

;; RatLeAbsBoundSeqUMinusEq
(set-goal "all as,n cRatLeAbsBoundSeq as n=cRatLeAbsBoundSeq([n0]~(as n0))n")
(assume "as")
(ind)
;; 3,4
(use "Truth")
;; 4
(assume "n" "IH")
(ng)
(simp "IH")
(simp (pf "cRatLeAbsBound(as n)=cRatLeAbsBound~(as n)"))
(use "Truth")
(use "RatLeAbsBoundUMinusEq")
;; Proof finshed.
(save "RatLeAbsBoundSeqUMinusEq")

(deanimate "RatLeAbsBoundSeq")

;; RealBound
(set-goal "all as,M(Cauchy as M -> exl m all n abs(as n)<=2**m)")
(assume "as" "M" "CasM")
(cut "exl m all n(n<=M 1 -> abs(as n)<=2**m)")
(assume "ExHyp")
(by-assume "ExHyp" "m" "FinBound")
(intro 0 (pt "m+1"))
;; ?_9:all n abs(as n)<=2**(m+1)
(assume "n")
(cases (pt "n<=M 1"))
;; 11,12
(assume "n<=M 1")
(use "RatLeTrans" (pt "(2**m#1)"))
(use "FinBound")
(use "n<=M 1")
(use "Truth")
;; ?_12:(n<M 1 -> F) -> abs(as n)<=2**(m+1)
(assume "n<M 1 -> F")
(use "RatLeTrans" (pt "abs(as(M 1))+(abs(as n)+ ~(abs(as(M 1))))"))
(assert "all b,c b<=c+(b+ ~c)")
 (assume "b" "c")
 (simp "RatPlusComm")
 (simp "<-" "RatPlusAssoc")
 (simprat (pf "~c+c==0"))
 (use "Truth")
 (use "Truth") 
(assume "Assertion")
(use "Assertion")
;; ?_21:abs(as(M 1))+(abs(as n)+ ~abs(as(M 1)))<=2**(m+1)
(use "RatLeTrans" (pt "(2**m#1)+(1#2**1)"))
(use "RatLeMonPlus")
(use "FinBound")
(use "Truth")
;; ?_31:abs(as n)+ ~abs(as(M 1))<=(1#2)
(use "RatLeTrans" (pt "abs(abs(as n)+ ~abs(as(M 1)))"))
(use "Truth")
(use "RatLeTrans" (pt "abs(as n+ ~(as(M 1)))"))
(use "RatLeAbsMinusAbs")
;; ?_36:abs(as n+ ~(as(M 1)))<=(1#2)
(use "CauchyElim" (pt "M"))
(use "CasM")
(use "NatNotLtToLe")
(assume "n<M 1")
(use "n<M 1 -> F")
(use "NatLtToLe")
(use "n<M 1")
(use "Truth")
(simp (pf "2**(m+1)=2**m+2**m"))
(use "Truth")
(ng)
(simp "SZeroPosPlus")
(use "Truth")
(intro 0 (pt "cRatLeAbsBoundSeq as(Succ(M 1))"))
(assume "n" "n<=M 1")
(use "RatLeAbsBoundSeqExFree")
(use "NatLeToLtSucc")
(use "n<=M 1")
;; Proof finished.
(save "RealBound")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [as,M]Succ(cRatLeAbsBoundSeq as(Succ(M 1)))

(animate "RealBound")

;; RealBoundPos
(set-goal "all as,M Zero<cRealBound as M")
(assume "as" "M")
(use "Truth")
;; Proof finished.
(save "RealBoundPos")

;; RealBoundExFree
(set-goal "all as,M(Cauchy as M -> all n abs(as n)<=2**cRealBound as M)")
(assume "as" "M" "CasM")
(assert "all n(n<=M 1 -> abs(as n)<=2**cRatLeAbsBoundSeq as(Succ(M 1)))")
(assume "n" "n<=M 1")
(use "RatLeAbsBoundSeqExFree")
(use "NatLeToLtSucc")
(use "n<=M 1")
(assume "FinBound" "n")
(cases (pt "n<=M 1"))
;; 9,10
(assume "n<=M 1")
(ng)
(simp "SZeroPosPlus")
(use "RatLeTrans" (pt "(2**cRatLeAbsBoundSeq as(Succ(M 1))#1)"))
(use "FinBound")
(use "n<=M 1")
(use "Truth")
;; ?_10:(n<=M 1 -> F) -> abs(as n)<=2**cRealBound as M
(assume "n<M 1 -> F")
(ng)
(simp "SZeroPosPlus")
(use "RatLeTrans" (pt "abs(as(M 1))+(abs(as n)+ ~(abs(as(M 1))))"))
(assert "all b,c b<=c+(b+ ~c)")
 (assume "b" "c")
 (simp "RatPlusComm")
 (simp "<-" "RatPlusAssoc")
 (simprat (pf "~c+c==0"))
 (use "Truth")
 (use "Truth") 
(assume "Assertion")
(use "Assertion")
;; ?_21:abs(as(M 1))+(abs(as n)+ ~abs(as(M 1)))<=
;;      2**cRatLeAbsBoundSeq as(Succ(M 1))+2**cRatLeAbsBoundSeq as(Succ(M 1))
(use "RatLeTrans" (pt "(2**cRatLeAbsBoundSeq as(Succ(M 1))#1)+(1#2**1)"))
(use "RatLeMonPlus")
(use "FinBound")
(use "Truth")
;; ?_33:abs(as n)+ ~abs(as(M 1))<=(1#2**1)
(use "RatLeTrans" (pt "abs(abs(as n)+ ~abs(as(M 1)))"))
(use "Truth")
(use "RatLeTrans" (pt "abs(as n+ ~(as(M 1)))"))
(use "RatLeAbsMinusAbs")
;; ?_38:abs(as n+ ~(as(M 1)))<=(1#2**1)
(use "CauchyElim" (pt "M"))
(use "CasM")
(use "NatNotLtToLe")
(assume "n<M 1")
(use "n<M 1 -> F")
(use "NatLtToLe")
(use "n<M 1")
(use "Truth")
(use "Truth")
;; Proof finished.
(save "RealBoundExFree")

;; RealBoundUMinusEq
(set-goal "all as,M cRealBound as M=cRealBound([n]~(as n))M")
(assume "as" "M")
(ng)
(use "RatLeAbsBoundSeqUMinusEq")
;; Proof finshed.
(save "RealBoundUMinusEq")

(deanimate "RealBound")

(add-computation-rules
 "(RealConstr as M)*(RealConstr bs N)"
 "RealConstr([n]as n*bs n)
            ([p]M(PosS(p+cNatPos(cRealBound bs N)))max
                N(PosS(p+cNatPos(cRealBound as M))))")

(set-totality-goal "RealTimes")
(use "AllTotalElim")
(cases)
(assume "as" "M")
(use "AllTotalElim")
(cases)
(assume "bs" "N")
(ng)
(use "ReaTotalVar")
;; Proof finished.
(save-totality)

;; 5.  Equality and order
;; ======================

;; We introduce an inductively defined predicate RealEq x y

(add-ids
 (list (list "RealEq" (make-arity (py "rea") (py "rea"))))
 '("all x,y(Real x -> Real y ->
    all p abs(x seq(x mod(PosS p))+ ~(y seq(y mod(PosS p))))<=(1#2**p) ->
    RealEq x y)" "RealEqIntro"))

;; Notice that we cannot take = and use overloading, because the token
;; = has token type rel-op and hence produces a term, not a predicate.

;; predicate creator

(define (make-predicate-creator token min-type-string)
  (lambda (x y)
    (let* ((type1 (term-to-type x))
	   (type2 (term-to-type y))
	   (min-type (py min-type-string))
	   (type (types-lub type1 type2 min-type))
	   (internal-name (token-and-types-to-name token (list type))))
      (make-predicate-formula (make-idpredconst internal-name '() '()) x y))))

(add-token "===" 'pred-infix (make-predicate-creator "===" "rea"))

(add-token-and-type-to-name "===" (py "rea") "RealEq")

(add-idpredconst-display "RealEq" 'pred-infix "===")

;; We introduce an inductively defined predicate RealEqS x y
;; expressing extensional equality of the Cauchy sequences.

(add-ids
 (list (list "RealEqS" (make-arity (py "rea") (py "rea"))))
 '("all x,y(all n x seq n==y seq n -> RealEqS x y)" "RealEqSIntro"))

;; (add-ids
;;  (list (list "RealEqS" (make-arity (py "rea") (py "rea"))))
;;  '("all x,y(Real x -> Real y ->
;;     all n x seq n==y seq n -> RealEqS x y)" "RealEqSIntro"))

(add-token "=+=" 'pred-infix (make-predicate-creator "=+=" "rea"))

(add-token-and-type-to-name "=+=" (py "rea") "RealEqS")

(add-idpredconst-display "RealEqS" 'pred-infix "=+=")

;; Non-negative reals are defined inductively

(add-ids
 (list (list "RealNNeg" (make-arity (py "rea"))))
 '("all x(Real x -> all p 0<=x seq(x mod p)+(1#2**p) -> RealNNeg x)"
 "RealNNegIntro"))

;; For reals less-than-or-equal-to is undecidable and hence must be
;; treated as an inductively defined predicate.

(add-ids
 (list (list "RealLe" (make-arity (py "rea") (py "rea"))))
 '("all x,y(Real x -> Real y -> RealNNeg(y+ ~x) -> RealLe x y)" "RealLeIntro"))

;; Notice that we cannot take <= and use overloading, because the token
;; <= has token type rel-op and hence produces a term, not a predicate.

(add-token
 "<<="
 'pred-infix
 (lambda (x y)
   (make-predicate-formula (make-idpredconst "RealLe" '() '()) x y)))

(add-idpredconst-display "RealLe" 'pred-infix "<<=")

;; Properties of RealEq, RealEqS, RealNNeg and RealLe

;; RealEqElim0
(set-goal "all x,y(x===y -> Real x)")
(assume "x" "y" "x=y")
(elim "x=y")
(search)
;; Proof finished.
(save "RealEqElim0")

;; RealEqElim1
(set-goal "all x,y(x===y -> Real y)")
(assume "x" "y" "x=y")
(elim "x=y")
(search)
;; Proof finished.
(save "RealEqElim1")

;; RealEqElim2
(set-goal
 "all x,y(x===y ->
          all p abs(x seq(x mod(PosS p))+ ~(y seq(y mod(PosS p))))<=(1#2**p))")
(assume "x" "y" "x=y")
(elim "x=y")
(search)
;; Proof finished.
(save "RealEqElim2")

;; The following variants will be useful, because their heads will be
;; more often of the form of a given goal.

;; RealConstrEqElim0
(set-goal
 "all as,M,bs,N(RealConstr as M===RealConstr bs N -> Real(RealConstr as M))")
(assume "as" "M" "bs" "N" "EqHyp")
(use "RealEqElim0" (pt "RealConstr bs N"))
(use "EqHyp")
;; Proof finished.
(save "RealConstrEqElim0")

;; RealConstrEqElim1
(set-goal
 "all as,M,bs,N(RealConstr as M===RealConstr bs N -> Real(RealConstr bs N))")
(assume "as" "M" "bs" "N" "EqHyp")
(use "RealEqElim1" (pt "RealConstr as M"))
(use "EqHyp")
;; Proof finished.
(save "RealConstrEqElim1")

;; RealConstrEqElim2
(set-goal
 "all as,M,bs,N(RealConstr as M===RealConstr bs N ->
                all p abs(as(M(PosS p))+ ~(bs(N(PosS p))))<=(1#2**p))")
(assume "as" "M" "bs" "N" "EqHyp" "p")
(use-with "RealEqElim2"
	  (pt "RealConstr as M") (pt "RealConstr bs N") "EqHyp" (pt "p"))
;; Proof finished.
(save "RealConstrEqElim2")

;; RealEqSElim
(set-goal "all x,y(x=+=y -> all n x seq n==y seq n)")
(assume "x" "y" "x=y")
(elim "x=y")
(search)
;; Proof finished.
(save "RealEqSElim")

;; RealConstrEqSElim
(set-goal
 "all as,M,bs,N(RealConstr as M=+=RealConstr bs N -> all n as n==bs n)")
(assume "as" "M" "bs" "N" "EqSHyp" "n")
(use-with "RealEqSElim"
	  (pt "RealConstr as M") (pt "RealConstr bs N") "EqSHyp" (pt "n"))
;; Proof finished.
(save "RealConstrEqSElim")

;; TotalReaToEqD
(set-goal "all x^(TotalRea x^ -> x^ eqd RealConstr x^ seq x^ mod)")
(assume "x^")
(elim)
(ng)
(strip)
(use "InitEqD")
;; Proof finished.
(save "TotalReaToEqD")

;; RealNNegElim0
(set-goal "all x(RealNNeg x -> Real x)")
(assume "x" "NNegx")
(elim "NNegx")
(search)
;; Proof finished.
(save "RealNNegElim0")

;; RealNNegElim1
(set-goal "all x(RealNNeg x -> all p 0<=x seq(x mod p)+(1#2**p))")
(assume "x" "NNegx")
(elim "NNegx")
(search)
;; Proof finished.
(save "RealNNegElim1")

;; The following variants will be useful, because their heads will be
;; more often of the form of a given goal.

;; RealConstrNNegElim0
(set-goal
 "all as,M(RealNNeg(RealConstr as M) -> Real(RealConstr as M))")
(assume "as" "M" "NNegHyp")
(use "RealNNegElim0")
(use "NNegHyp")
;; Proof finished.
(save "RealConstrNNegElim0")

;; RealConstrNNegElim1
(set-goal
 "all as,M(RealNNeg(RealConstr as M) -> all p 0<=as(M p)+(1#2**p))")
(assume "as" "M" "NNegHyp" "p")
(use-with "RealNNegElim1" (pt "RealConstr as M") "NNegHyp" (pt "p"))
;; Proof finished.
(save "RealConstrNNegElim1")

;; RealLeElim0
(set-goal "all x,y(x<<=y -> Real x)")
(assume "x" "y" "x<=y")
(elim "x<=y")
(search)
;; Proof finished.
(save "RealLeElim0")

;; RealLeElim1
(set-goal "all x,y(x<<=y -> Real y)")
(assume "x" "y" "x<=y")
(elim "x<=y")
(search)
;; Proof finished.
(save "RealLeElim1")

;; RealLeElim2
(set-goal "all x,y(x<<=y -> RealNNeg(y+ ~x))")
(assume "x" "y" "x<=y")
(elim "x<=y")
(search)
;; Proof finished.
(save "RealLeElim2")

;; The following variants will be useful, because their heads will be
;; more often of the form of a given goal.

;; RealConstrLeElim0
(set-goal
 "all as,M,bs,N(RealConstr as M<<=RealConstr bs N -> Real(RealConstr as M))")
(assume "as" "M" "bs" "N" "LeHyp")
(use "RealLeElim0" (pt "RealConstr bs N"))
(use "LeHyp")
;; Proof finished.
(save "RealConstrLeElim0")

;; RealConstrLeElim1
(set-goal
 "all as,M,bs,N(RealConstr as M<<=RealConstr bs N -> Real(RealConstr bs N))")
(assume "as" "M" "bs" "N" "LeHyp")
(use "RealLeElim1" (pt "RealConstr as M"))
(use "LeHyp")
;; Proof finished.
(save "RealConstrLeElim1")

;; RealConstrLeElim2
(set-goal "all as,M,bs,N(
 RealConstr as M <<=RealConstr bs N ->
 RealNNeg(RealConstr([n]bs n+ ~(as n))([p]N(PosS p)max M(PosS p))))")
(assume "as" "M" "bs" "N" "LeHyp")
(use-with "RealLeElim2" (pt "RealConstr as M") (pt "RealConstr bs N") "LeHyp")
;; Proof finished.
(save "RealConstrLeElim2")

;; We now prove further properties of RealEq, RealEqS, RealNNe, RealLe

;; RealEqRefl
(set-goal "all x(Real x -> x===x)")
(cases)
(assume "as" "M" "Rx")
(use "RealEqIntro")
(use "Rx")
(use "Rx")
(assume "p")
(ng)
(simprat (pf "as(M(PosS p))+ ~(as(M(PosS p)))==0"))
(use "Truth")
(use "Truth")
;; Proof finished.
(save "RealEqRefl")

;; RealEqSym
(set-goal "all x,y(x===y -> y===x)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "x=y")
(elim "x=y")
(cases)
(assume "as1" "M1")
(cases)
(assume "bs1" "N1" "Rx1" "Ry1" "LeHyp")
(intro 0)
(use "Ry1")
(use "Rx1")
(assume "p")
(ng)
(simp "<-" "RatAbs0RewRule")
(ng)
(simp "RatPlusComm")
(use "LeHyp")
;; Proof finished.
(save "RealEqSym")

;; To prove transitivity of equality, we need a characterization of
;; equality.

;; RealEqCharOne
(set-goal "allnc as,bs all M,N(RealConstr as M===RealConstr bs N -> 
      all p exl n1 all n(n1<=n -> abs(as n-bs n)<=(1#2**p)))")
(assume "as" "bs" "M" "N" "x=y" "p")
(intro 0 (pt "M(PosS(PosS p))max N(PosS(PosS p))"))
(assume "n" "BdHyp")
(use "RatLeTrans"
     (pt "(1#2**(PosS(PosS p)))+(1#2**(PosS p))+(1#2**(PosS(PosS p)))"))
(use "RatLeTrans" (pt "abs(as n+ ~(as(M(PosS(PosS p)))))+
                       abs(as(M(PosS(PosS p)))+ ~(bs(N(PosS(PosS p)))))+
                       abs(bs(N(PosS(PosS p)))+ ~(bs n))"))
(assert "all a,b,c,d abs(a+ ~b)<=abs(a+ ~c)+abs(c+ ~d)+abs(d+ ~b)")
 (assume "a" "b" "c" "d")
 (use "RatLeTrans" (pt "abs(a+ ~d)+abs(d+ ~b)"))
 (use "RatLeAbsMinus")
 (use "RatLeMonPlus")
 (use "RatLeAbsMinus")
 (use "Truth")
;; Assertion proved
(assume "RatLeAbsMinus3")
(use "RatLeAbsMinus3")
(assert
 "all a1,a2,b1,b2,c1,c2(a1<=a2 -> b1<=b2 -> c1<=c2 -> a1+b1+c1<=a2+b2+c2)")
 (assume "a1" "a2" "b1" "b2" "c1" "c2" "a1<=a2" "b1<=b2" "c1<=c2")
 (use "RatLeMonPlus")
 (use "RatLeMonPlus")
 (use "a1<=a2")
 (use "b1<=b2")
 (use "c1<=c2")
;; Assertion proved
(assume "RatLeMonPlus3")
(use "RatLeMonPlus3")
;; 25-27
(use "CauchyElim" (pt "M"))
(use "RealConstrToCauchy")
(use "RealConstrEqElim0" (pt "bs") (pt "N"))
(use "x=y")
(use "NatLeTrans" (pt "(M(PosS(PosS p)))max(N(PosS(PosS p)))"))
(use "NatMaxUB1")
(use "BdHyp")
(use "Truth")
;; 26
(use "RealConstrEqElim2")
(use "x=y")
;; 27
(use "CauchyElim" (pt "N"))
(use "RealConstrToCauchy")
(use "RealConstrEqElim0" (pt "as") (pt "M"))
(use "RealEqSym")
(use "x=y")
(use "Truth")
(use "NatLeTrans" (pt "(M(PosS(PosS p)))max(N(PosS(PosS p)))"))
(use "NatMaxUB2")
(use "BdHyp")
;; 6: (1#2**PosS(PosS p))+(1#2**PosS p)+(1#2**PosS(PosS p))<=(1#2**p)
;; Use RatPlusHalfExpPosS :
;; all p (1#2**PosS p)+(1#2**PosS p)==(1#2**p)
(assert "(1#2**PosS(PosS p))+(1#2**PosS p)=(1#2**PosS p)+(1#2**PosS(PosS p))")
 (use "RatPlusComm")
(assume "Assertion")
(simp "Assertion")
(drop "Assertion")
(simp "<-" "RatPlusAssoc")
(simprat "RatPlusHalfExpPosS")
(simprat "RatPlusHalfExpPosS")
(use "Truth")
;; Proof finished.
(save "RealEqCharOne")

(pp (rename-variables
     (nt (proof-to-extracted-term (theorem-name-to-proof "RealEqCharOne")))))
;; [M,M0,p]M(PosS(PosS p))max M0(PosS(PosS p))

(animate "RealEqCharOne")

;; RealEqCharOneExFree
(set-goal "allnc as,bs all M,N(RealConstr as M===RealConstr bs N -> 
      all p,n(cRealEqCharOne M N p<=n -> abs(as n-bs n)<=(1#2**p)))")
(assume "as" "bs" "M" "N" "x=y" "p")
(ng)
(assume "n" "BdHyp")
(use "RatLeTrans"
     (pt "(1#2**(PosS(PosS p)))+(1#2**(PosS p))+(1#2**(PosS(PosS p)))"))
(use "RatLeTrans" (pt "abs(as n+ ~(as(M(PosS(PosS p)))))+
                       abs(as(M(PosS(PosS p)))+ ~(bs(N(PosS(PosS p)))))+
                       abs(bs(N(PosS(PosS p)))+ ~(bs n))"))
(assert "all a,b,c,d abs(a+ ~b)<=abs(a+ ~c)+abs(c+ ~d)+abs(d+ ~b)")
 (assume "a" "b" "c" "d")
 (use "RatLeTrans" (pt "abs(a+ ~d)+abs(d+ ~b)"))
 (use "RatLeAbsMinus")
 (use "RatLeMonPlus")
 (use "RatLeAbsMinus")
 (use "Truth")
;; Assertion proved
(assume "RatLeAbsMinus3")
(use "RatLeAbsMinus3")
(assert
 "all a1,a2,b1,b2,c1,c2(a1<=a2 -> b1<=b2 -> c1<=c2 -> a1+b1+c1<=a2+b2+c2)")
 (assume "a1" "a2" "b1" "b2" "c1" "c2" "a1<=a2" "b1<=b2" "c1<=c2")
 (use "RatLeMonPlus")
 (use "RatLeMonPlus")
 (use "a1<=a2")
 (use "b1<=b2")
 (use "c1<=c2")
;; Assertion proved
(assume "RatLeMonPlus3")
(use "RatLeMonPlus3")
;; 26-28
(use "CauchyElim" (pt "M"))
(use "RealConstrToCauchy")
(use "RealConstrEqElim0" (pt "bs") (pt "N"))
(use "x=y")
(use "NatLeTrans" (pt "(M(PosS(PosS p)))max(N(PosS(PosS p)))"))
(use "NatMaxUB1")
(use "BdHyp")
(use "Truth")
;; 27
(use "RealConstrEqElim2")
(use "x=y")
;; 28
(use "CauchyElim" (pt "N"))
(use "RealConstrToCauchy")
(use "RealConstrEqElim0" (pt "as") (pt "M"))
(use "RealEqSym")
(use "x=y")
(use "Truth")
(use "NatLeTrans" (pt "(M(PosS(PosS p)))max(N(PosS(PosS p)))"))
(use "NatMaxUB2")
(use "BdHyp")
;; 7: (1#2**PosS(PosS p))+(1#2**PosS p)+(1#2**PosS(PosS p))<=(1#2**p)
;; Use RatPlusHalfExpPosS :
;; all p (1#2**PosS p)+(1#2**PosS p)==(1#2**p)
(assert "(1#2**PosS(PosS p))+(1#2**PosS p)=(1#2**PosS p)+(1#2**PosS(PosS p))")
 (use "RatPlusComm")
(assume "Assertion")
(simp "Assertion")
(drop "Assertion")
(simp "<-" "RatPlusAssoc")
(simprat "RatPlusHalfExpPosS")
(simprat "RatPlusHalfExpPosS")
(use "Truth")
;; Proof finished.
(save "RealEqCharOneExFree")

(deanimate "RealEqCharOne")

;; RealEqChar2
(set-goal "all as,M,bs,N(Real(RealConstr as M) -> Real(RealConstr bs N) ->
           all p exl n0 all n(n0<=n -> abs(as n-bs n)<=(1#2**p)) ->
           RealConstr as M===RealConstr bs N)")
(assume "as" "M" "bs" "N" "Rx" "Ry" "Est")
(use "RealEqIntro")
(use "Rx")
(use "Ry")
(ng #t)
(assume "p")
(use "RatLeAllPlusToLe")
(assume "q")
;; abs(as(M(PosS p))+ ~(bs(N(PosS p))))<=(1#2**p)+(1#2**q)
(inst-with-to "Est" (pt "q") "InstEst")
(drop "Est")
(by-assume "InstEst" "n0" "n0Prop")
;; We now want to use n as an abbreviation for the complex term
;; ((M(PosS p))max(N(PosS p)))max n0.  Hence we introduce via cut the
;; formula all n(n=term -> goal)
(cut "all n(n=((M(PosS p))max(N(PosS p)))max n0 ->
             abs(as(M(PosS p))+ ~(bs(N(PosS p))))<=(1#2**p)+(1#2**q))")
(assume "AllHyp")
(use "AllHyp" (pt "((M(PosS p))max(N(PosS p)))max n0"))
(use "Truth")
(assume "n" "nDef")
(use "RatLeTrans"
     (pt "abs(as(M(PosS p))+ ~(as n))+
          abs(as n+ ~(bs n))+
          abs(bs n+ ~(bs(N(PosS p))))"))
(assert "all a,b,c,d abs(a+ ~b)<=abs(a+ ~c)+abs(c+ ~d)+abs(d+ ~b)")
 (assume "a" "b" "c" "d")
 (use "RatLeTrans" (pt "abs(a+ ~d)+abs(d+ ~b)"))
 (use "RatLeAbsMinus")
 (use "RatLeMonPlus")
 (use "RatLeAbsMinus")
 (use "Truth")
;; Assertion proved
(assume "RatLeAbsMinus3")
(use "RatLeAbsMinus3")
(use "RatLeTrans" (pt "(1#2**(PosS p))+(1#2**q)+(1#2**(PosS p))"))
(assert
 "all a1,a2,b1,b2,c1,c2(a1<=a2 -> b1<=b2 -> c1<=c2 -> a1+b1+c1<=a2+b2+c2)")
 (assume "a1" "a2" "b1" "b2" "c1" "c2" "a1<=a2" "b1<=b2" "c1<=c2")
 (use "RatLeMonPlus")
 (use "RatLeMonPlus")
 (use "a1<=a2")
 (use "b1<=b2")
 (use "c1<=c2")
;; Assertion proved
(assume "RatLeMonPlus3")
(use "RatLeMonPlus3")
;; 41-43
(drop "RatLeMonPlus3")
(use "CauchyElim" (pt "M"))
(use "RealConstrToCauchy")
(use "Rx")
(use "Truth")
(simp "nDef")
(use "NatLeTrans" (pt "M(PosS p)max N(PosS p)"))
(use "NatMaxUB1")
(use "NatMaxUB1")
;; 42
(use "n0Prop")
(simp "nDef")
(use "NatMaxUB2")
;; 43
(use "CauchyElim" (pt "N"))
(use "RealConstrToCauchy")
(use "Ry")
(simp "nDef")
(use "NatLeTrans" (pt "M(PosS p)max N(PosS p)"))
(use "NatMaxUB2")
(use "NatMaxUB1")
(use "Truth")
;; 32 (1#2**PosS p)+(1#2**q)+(1#2**PosS p)<=(1#2**p)+(1#2**q)
;; Use RatPlusHalfExpPosS :
;; all p (1#2**PosS p)+(1#2**PosS p)==(1#2**p)
(simprat (pf "(1#2**PosS p)+(1#2**q)==(1#2**q)+(1#2**PosS p)"))
(simp "<-" "RatPlusAssoc")
(simprat "RatPlusHalfExpPosS")
(simp "RatPlusComm")
(use "Truth")
(simp "RatPlusComm")
(use "Truth")
;; Proof finished.
(save "RealEqChar2")

;; An immediate consequence of RealEqChar2 is that any two reals with the
;; same Cauchy sequence (but possibly different moduli) are equal.

;; RealSeqEqToEq
(set-goal "all x,y,n1(Real x -> Real y ->
 all n(n1<=n -> x seq n==y seq n) -> x===y)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "n1" "Rx" "Ry" "SeqEqHyp")
(ng)
(use "RealEqChar2")
(use "Rx")
(use "Ry")
(assume "p")
(intro 0 (pt "n1"))
(assume "n" "n1<=n")
(simprat "SeqEqHyp")
(ng)
(simprat (pf "bs n+ ~(bs n)==0"))
(use "Truth")
(use "Truth")
(use "n1<=n")
;; Proof finished.
(save "RealSeqEqToEq")

;; RealEqSToEq
(set-goal "all x,y(Real x -> Real y -> x=+=y -> x===y)")
(assume "x" "y" "Rx" "Ry" "x=+=y")
(use "RealSeqEqToEq" (pt "Zero"))
(use "Rx")
(use "Ry")
(assume "n" "Useless")
(use "RealEqSElim")
(use "x=+=y")
;; Proof finished.
(save "RealEqSToEq")

;; RealEqTrans
(set-goal "all x,y,z(x===y -> y===z -> x===z)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N")
(cases)
(assume "cs" "L" "x=y" "y=z")
(use "RealEqChar2")
(use "RealConstrEqElim0" (pt "bs") (pt "N"))
(use "x=y")
(use "RealConstrEqElim0" (pt "bs") (pt "N"))
(use "RealEqSym")
(use "y=z")
(assume "p")
;; Use RealEqCharOne for x=y
(assert "exl n all n0(n<=n0 -> abs(as n0-bs n0)<=(1#2**(PosS p)))")
 (use "RealEqCharOne" (pt "M") (pt "N"))
 (use "x=y")
(assume "xyExHyp")
(by-assume "xyExHyp" "m" "mProp")
;; Use RealEqCharOne for y=z
(assert "exl n all n0(n<=n0 -> abs(bs n0-cs n0)<=(1#2**(PosS p)))")
 (use "RealEqCharOne" (pt "N") (pt "L"))
 (use "y=z")
(assume "yzExHyp")
(by-assume "yzExHyp" "l" "lProp")
;; Take m max l for n
(intro 0 (pt "m max l"))
(assume "n" "BdHyp")
(use "RatLeTrans" (pt "abs(as n-bs n)+abs(bs n-cs n)"))
(use "Truth")
(simprat "<-" "RatPlusHalfExpPosS")
(use "RatLeMonPlus")
(use "mProp")
(use "NatLeTrans" (pt "m max l"))
(use "NatMaxUB1")
(use "BdHyp")
(use "lProp")
(use "NatLeTrans" (pt "m max l"))
(use "NatMaxUB2")
(use "BdHyp")
;; Proof finished.
(save "RealEqTrans")

;; RealNNegCharOne
(set-goal "allnc as all M(RealNNeg(RealConstr as M) -> 
      all p exl n1 all n(n1<=n -> ~(1#2**p)<=as n))")
(assume "as" "M" "0<=x" "p")
(intro 0 (pt "M(PosS p)"))
(assume "n" "BdHyp")
(use "RatLeTrans" (pt "~(1#2**(PosS p))+(as(M(PosS p))+ ~(as n))+as n"))
;; 5,6
(use "RatLeTrans" (pt "~(1#2**(PosS p))+as(M(PosS p))"))
(use "RatLePlusR")
(assert "(1#2**p)==(1#2**PosS p)+(1#2**PosS p)")
 (use "RatEqvSym")
 (use "RatPlusHalfExpPosS")
(assume "RatPlusHalfExpPosSCor")
(simprat "RatPlusHalfExpPosSCor")
(drop "RatPlusHalfExpPosSCor")
(simp "RatUMinus1RewRule")
(simp "RatUMinus2RewRule")
(simp "RatPlusAssoc")
(use "RatLeTrans" (pt "0+ ~(1#2**PosS p)"))
(use "RatLeMonPlus")
(use "Truth")
(use "Truth")
(use "RatLeTrans" (pt "as(M(PosS p))+(1#2**PosS p)+ ~(1#2**PosS p)"))
(use "RatLeMonPlus")
(use "RealConstrNNegElim1")
(use "0<=x")
(use "Truth")
(simprat "RatEqvPlusMinusRev")
(use "RatLeRefl")
(use "Truth")
;; 8
(simp "<-" "RatPlusAssoc")
(use "RatLeMonPlus")
(ng)
(use "Truth")
(simprat "RatEqvPlusMinus")
(use "Truth")
;; 6
;; The following argument is repeated in the proof of RealPosCharOne below
(assert
 "all a1,a2,b1,b2,c1,c2(a1<=a2 -> b1<=b2 -> c1<=c2 -> a1+b1+c1<=a2+b2+c2)")
 (assume "a1" "a2" "b1" "b2" "c1" "c2" "a1<=a2" "b1<=b2" "c1<=c2")
 (use "RatLeMonPlus")
 (use "RatLeMonPlus")
 (use "a1<=a2")
 (use "b1<=b2")
 (use "c1<=c2")
;; Assertion proved
(assume "RatLeMonPlus3")
(use "RatLeTrans" (pt "~(1#2**PosS p)+(1#2**PosS p)+as n"))
(use "RatLeMonPlus3")
(drop "RatLeMonPlus3")
(use "Truth")
(use "RatLeTrans" (pt "abs(as(M(PosS p))+ ~(as n))"))
(use "Truth")
(use "CauchyElim" (pt "M"))
(use "RealConstrToCauchy")
(use "RealNNegElim0")
(use "0<=x")
(use "Truth")
(use "BdHyp")
(use "Truth")
(simp "RatPlusComm")
(simp "RatPlusAssoc")
(simprat "RatEqvPlusMinus")
(use "Truth")
;; Proof finished.
(save "RealNNegCharOne")

(pp (rename-variables
     (nt (proof-to-extracted-term (theorem-name-to-proof "RealNNegCharOne")))))
;; [M,p]M(PosS p)

(animate "RealNNegCharOne")

;; RealNNegCharOneExFree
(set-goal "all as,M(RealNNeg(RealConstr as M) -> 
      all p,n(cRealNNegCharOne M p<=n -> ~(1#2**p)<=as n))")
(assume "as" "M" "0<=x" "p" "n" "BdHyp")
(use "RatLeTrans" (pt "~(1#2**(PosS p))+(as(M(PosS p))+ ~(as n))+as n"))
;; 3,4
(use "RatLeTrans" (pt "~(1#2**(PosS p))+as(M(PosS p))"))
(use "RatLePlusR")
(assert "(1#2**p)==(1#2**PosS p)+(1#2**PosS p)")
 (use "RatEqvSym")
 (use "RatPlusHalfExpPosS")
(assume "RatPlusHalfExpPosSCor")
(simprat "RatPlusHalfExpPosSCor")
(drop "RatPlusHalfExpPosSCor")
(simp "RatUMinus1RewRule")
(simp "RatUMinus2RewRule")
(simp "RatPlusAssoc")
(use "RatLeTrans" (pt "0+ ~(1#2**PosS p)"))
(use "RatLeMonPlus")
(use "Truth")
(use "Truth")
(use "RatLeTrans" (pt "as(M(PosS p))+(1#2**PosS p)+ ~(1#2**PosS p)"))
(use "RatLeMonPlus")
(use "RealConstrNNegElim1")
(use "0<=x")
(use "Truth")
(simprat "RatEqvPlusMinusRev")
(use "RatLeRefl")
(use "Truth")
;; 6
(simp "<-" "RatPlusAssoc")
(use "RatLeMonPlus")
(ng)
(use "Truth")
(simprat "RatEqvPlusMinus")
(use "Truth")
;; 4
;; The following argument is repeated in the proof of RealPosCharOne below
(assert
 "all a1,a2,b1,b2,c1,c2(a1<=a2 -> b1<=b2 -> c1<=c2 -> a1+b1+c1<=a2+b2+c2)")
 (assume "a1" "a2" "b1" "b2" "c1" "c2" "a1<=a2" "b1<=b2" "c1<=c2")
 (use "RatLeMonPlus")
 (use "RatLeMonPlus")
 (use "a1<=a2")
 (use "b1<=b2")
 (use "c1<=c2")
;; Assertion proved
(assume "RatLeMonPlus3")
(use "RatLeTrans" (pt "~(1#2**PosS p)+(1#2**PosS p)+as n"))
(use "RatLeMonPlus3")
(drop "RatLeMonPlus3")
(use "Truth")
(use "RatLeTrans" (pt "abs(as(M(PosS p))+ ~(as n))"))
(use "Truth")
(use "CauchyElim" (pt "M"))
(use "RealConstrToCauchy")
(use "RealNNegElim0")
(use "0<=x")
(use "Truth")
(use "BdHyp")
(use "Truth")
(simp "RatPlusComm")
(simp "RatPlusAssoc")
(simprat "RatEqvPlusMinus")
(use "Truth")
;; Proof finished.
(save "RealNNegCharOneExFree")

(deanimate "RealNNegCharOne")

;; RealNNegChar2
(set-goal "all as,M(Real(RealConstr as M) ->
      all p exl n1 all n(n1<=n -> ~(1#2**p)<=as n) ->
      RealNNeg(RealConstr as M))")
(assume "as" "M" "Rx" "Est")
(use "RealNNegIntro")
(use "Rx")
(ng #t)
(assume "p")
(use "RatLeAllPlusToLe")
(assume "q")
(inst-with-to "Est" (pt "q") "EstInst")
(drop "Est")
(by-assume "EstInst" "n0" "n0Prop")
(inst-with-to "n0Prop" (pt "M(p)max n0") "EstInstInst")
(use "RatLeTrans" (pt "as(M p)+(1#2**p)+ ~(as(M p max n0))"))
(simp "RatPlusComm")
(simp "RatPlusAssoc")
(use "RatLeTrans" (pt "~(1#2**p)+(1#2**p)"))
(use "Truth")
(use "RatLeMonPlus")
(simp "<-" "RatLeUMinus")
(ng #t)
(use "RatLeTrans" (pt "abs(as(M p max n0)+ ~(as(M p)))"))
(use "Truth")
(use "CauchyElim" (pt "M"))
(use "RealConstrToCauchy")
(use "Rx")
(use "NatMaxUB1")
(use "Truth")
(use "Truth")
(use "RatLeMonPlus")
(use "Truth")
(simp "<-" "RatLeUMinus")
(use "EstInstInst")
(use "NatMaxUB2")
;; Proof finished.
(save "RealNNegChar2")

;; RealPosChar1
(set-goal "all as,M,p(
 Real(RealConstr as M) -> RealPos(RealConstr as M)p ->
 all n(M(PosS p)<=n -> (1#2**PosS p)<=as n))")
(assume "as" "M" "p" "Rx" "xPos" "n" "BdHyp")
(use "RatLeTrans" (pt "~(1#2**(PosS p))+(as(M(PosS p))+ ~(as n))+as n"))
;; 3,4
(use "RatLePlusR")
(ng)
(simp "RatPlusComm")
(simp "<-" "RatPlusAssoc")
(simp "RatPlusAssoc")
(simprat "RatPlusHalfExpPosS")
(use "RatLeTrans" (pt "as(M(PosS p))+(~(as(M(PosS p)))+as n)"))
(use "RatLeMonPlus")
(use "xPos")
(use "Truth")
(ng)
(simp "RatPlusComm")
(ng)
(simprat "RatEqvPlusMinusRev")
(use "Truth")
;; 4
;; The following is similar to what was done for RealNNegCharOne
(assert
 "all a1,a2,b1,b2,c1,c2(a1<=a2 -> b1<=b2 -> c1<=c2 -> a1+b1+c1<=a2+b2+c2)")
 (assume "a1" "a2" "b1" "b2" "c1" "c2" "a1<=a2" "b1<=b2" "c1<=c2")
 (use "RatLeMonPlus")
 (use "RatLeMonPlus")
 (use "a1<=a2")
 (use "b1<=b2")
 (use "c1<=c2")
;; Assertion proved
(assume "RatLeMonPlus3")
(use "RatLeTrans" (pt "~(1#2**PosS p)+(1#2**PosS p)+as n"))
(use "RatLeMonPlus3")
(drop "RatLeMonPlus3")
(use "Truth")
(use "RatLeTrans" (pt "abs(as(M(PosS p))+ ~(as n))"))
(use "Truth")
(use "CauchyElim" (pt "M"))
(use "RealConstrToCauchy")
(use "Rx")
(use "Truth")
(use "BdHyp")
(use "Truth")
(simp "RatPlusComm")
(simp "RatPlusAssoc")
(simprat "RatEqvPlusMinus")
(use "Truth")
;; Proof finished.
(save "RealPosChar1")

;; RealPosChar2
(set-goal "all as,M,n1,q(Real(RealConstr as M) -> 
                               all n(n1<=n -> (1#2**q)<=as n) ->
                               RealPos(RealConstr as M)(PosS q))")
(assume "as" "M" "n1" "q" "Rx" "Est")
(ng)
(use "RatLeTrans" (pt "~(1#2**(PosS(PosS q)))+(1#2**q)"))
(use "RatLeTrans" (pt "~(1#2**(PosS q))+(1#2**q)"))
(simprat (pf "(1#2**q)==(1#2**PosS q)+(1#2**PosS q)"))
(simp "RatPlusComm")
(simprat "RatEqvPlusMinusRev")
(use "Truth")
(use "RatEqvSym")
(use "RatPlusHalfExpPosS")
(use "RatLeMonPlus")
(simp "RatLeUMinus")
(ng)
(assert "all p 2**p<=2**PosS p")
 (assume "p")
 (simp "PosSSucc")
 (ng)
 (use "Truth")
(assume "Assertion")
(use "Assertion")
(use "Truth")
;; 5
;; We now want to use n as an abbreviation for n1 max M(PosS(PosS q)).
;; Hence we introduce via cut the formula all n(n=term -> goal)
(cut "all n(n=n1 max M(PosS(PosS q)) ->
             ~(1#2**PosS(PosS q))+(1#2**q)<=as(M(PosS(PosS q))))")
(assume "AllHyp")
(use "AllHyp" (pt "n1 max M(PosS(PosS q))"))
(use "Truth")
(assume "n" "nDef")
(use "RatLeTrans" (pt "~(1#2**PosS(PosS q))+as n"))
(use "RatLeMonPlus")
(use "Truth")
(use "Est")
(simp "nDef")
(use "NatMaxUB1")
(use "RatLeTrans" (pt "as(M(PosS(PosS q)))+ ~(as n) +as n"))
(use "RatLeMonPlus")
(simp "<-" "RatLeUMinus")
(ng)
(simp "RatPlusComm")
(use "RatLeTrans" (pt "abs(as n+ ~(as(M(PosS(PosS q)))))"))
(use "Truth")
(use "CauchyElim" (pt "M"))
(use "RealConstrToCauchy")
(use "Rx")
(simp "nDef")
(use "NatMaxUB2")
(use "Truth")
(use "Truth")
(simprat "RatEqvPlusMinus")
(use "Truth")
;; Proof finished.
(save "RealPosChar2")

;; From Nils Koepps compreal.scm:

;; RealNNegChar2RealConstrFree
(set-goal
 "all x(Real x -> all p exl n all n0(n<=n0 -> ~(1#2**p)<=(x seq) n0) ->
        RealNNeg(x))")
(cases)
(assume "as" "M" "Rx" "Char")
(use "RealNNegChar2")
(use "Rx")
(use "Char")
;; Proof finished.
(save "RealNNegChar2RealConstrFree")

;; RealPosChar1RealConstrFree
(set-goal "all x,p(Real x -> RealPos x p ->
                   all n(x mod(PosS p)<=n -> (1#2**PosS p)<=x seq n))")
(cases)
(assume "as" "M" "p" "Rx" "x ppos" "n" "Char")
(use "RealPosChar1" (pt "M"))
(ng)
(use "Rx")
(ng)
(use "x ppos")
(use "Char")
;; Proof finished.
(save "RealPosChar1RealConstrFree")

;; RealPosChar2RealConstrFree
(set-goal "all x,n,q(Real x -> all n0(n<=n0 -> (1#2**q)<=x seq n0) ->
                     RealPos x(PosS q))")
(cases)
(assume "as" "M" "n" "q" "Rx" "hyp")
(use "RealPosChar2" (pt "n"))
(use "Rx")
(assume "n0" "n<=n0")
(inst-with-to "hyp" (pt "n0") "hypInst")
(simp "RatLeCompat" (pt "(1#2**q)") (pt "(RealConstr as M)seq n0"))
(use "hypInst")
(use "n<=n0")
(ng)
(use "Truth")
(use "Truth")
;; Proof finished.
(save "RealPosChar2RealConstrFree")

;; 6.  Closure properties
;; ======================

;; RealPlusReal
(set-goal "all x,y(Real x -> Real y -> Real(RealPlus x y))")
(assume "x" "y" "Rx" "Ry")
(elim "Rx")
(cases)
(assume "as" "M" "CasM" "MonM")
(elim "Ry")
(cases)
(assume "bs" "N" "CbsN" "MonN")
(use "RealIntro")
(ng)
(use "CauchyIntro")
(assume "p" "n" "m" "nBd" "mBd")
(ng)
(simp (pf "as n+ bs n+ ~(as m)+ ~(bs m)=as n+ ~(as m)+(bs n+ ~(bs m))"))
;; Could also use == here.
;; 15,16
(use "RatLeTrans" (pt "abs(as n+ ~(as m))+abs(bs n+ ~(bs m))"))
(use "RatLeAbsPlus")
(use "RatLeTrans" (pt "(1#2**(PosS p))+(1#2**(PosS p))"))
(use "RatLeMonPlus")

(use "CauchyElim" (pt "M"))
(use "CasM")
(use "NatLeTrans" (pt "(M(PosS p))max(N(PosS p))"))
(use "NatMaxUB1")
(use "nBd")
(use "NatLeTrans" (pt "(M(PosS p))max(N(PosS p))"))
(use "NatMaxUB1")
(use "mBd")

;; ?_22:abs(bs n+ ~(bs m))<=(1#2**PosS p)
(use "CauchyElim" (pt "N"))
(use "CbsN")
(use "NatLeTrans" (pt "(M(PosS p))max(N(PosS p))"))
(use "NatMaxUB2")
(use "nBd")
(use "NatLeTrans" (pt "(M(PosS p))max(N(PosS p))"))
(use "NatMaxUB2")
(use "mBd")

;; ?_20:(1#2**PosS p)+(1#2**PosS p)<=(1#2**p)
(simprat "RatPlusHalfExpPosS")
(use "Truth")

;; ?_16:as n+bs n+ ~(as m)+ ~(bs m)=as n+ ~(as m)+(bs n+ ~(bs m))
(ng)
(simp (pf "as n+bs n+ ~(as m)=as n+ ~(as m)+bs n"))
(use "Truth")
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp (pf "bs n+ ~(as m)= ~(as m)+bs n"))
(use "Truth")
(use "RatPlusComm")

;; ?_10:Mon(RealMod(RealConstr as M+RealConstr bs N))
(ng)
(use "MonIntro")
(ng)
(assume "p" "q" "p<=q")
(use "NatMaxLUB")
(use "NatLeTrans" (pt "M(PosS q)"))
(use "MonElim")
(use "MonM")
(ng)
(use "p<=q")
(use "NatMaxUB1")
(use "NatLeTrans" (pt "N(PosS q)"))
(use "MonElim")
(use "MonN")
(ng)
(use "p<=q")
(use "NatMaxUB2")
;; Proof finished.
(save "RealPlusReal")

;; RealUMinusReal
(set-goal "all x(Real x -> Real(~x))")
(assume "x" "Rx")
(elim "Rx")
(cases)
(assume "as" "M" "CasM" "MonM")
(use "RealIntro")
(ng)
(use "CauchyIntro")
(assume "p" "n" "m" "nBd" "mBd")
(ng)
(simp "RatPlusComm")
(use "CauchyElim" (pt "M"))
(use "CasM")
(use "mBd")
(use "nBd")
;; ?_7:Mon(RealMod~(RealConstr as M))
(ng)
(use "MonM")
;; Proof finished.
(save "RealUMinusReal")

;; RealUMinusRealInv
(set-goal "all x(Real(~ x) -> Real x)")
(cases)
(ng)
(assume "as" "M" "RHyp")
(use "RealIntro")
;; 5,6
(ng)
(inst-with-to "RealToCauchy" (pt "RealConstr([n]~(as n))M") "RHyp" "C~asM")
(ng)
(use "CauchyIntro")
(assume "p" "n" "m" "nBd" "mBd")
(inst-with-to "CauchyElim" (pt "[n]~(as n)") (pt "M") "C~asM"
	      (pt "p") (pt "n") (pt "m") "nBd" "mBd" "CauchyElimInst")
(ng "CauchyElimInst")
(simp "<-" "RatAbs0RewRule")
(ng)
(use "CauchyElimInst")
;; 6
(inst-with-to "RealToMon" (pt "RealConstr([n]~(as n))M") "RHyp" "MonM")
(ng)
(use "MonM")
;; Proof finished.
(save "RealUMinusRealInv")

;; RealAbsReal
(set-goal "all x(Real x -> Real(abs x))")
(assume "x" "Rx")
(elim "Rx")
(cases)
(assume "as" "M" "CasM" "MonM")
(use "RealIntro")
(ng)
(use "CauchyIntro")
(assume "p" "n" "m" "nBd" "mBd")
(ng)
(use "RatLeAbs")
;; 12,13
(use "RatLeTrans" (pt "abs(as n+ ~(as m))"))
(use "RatLeMinusAbs")
(use "CauchyElim" (pt "M"))
(use "CasM")
(use "nBd")
(use "mBd")
;; 13
(ng)
(simp "RatPlusComm")
(use "RatLeTrans" (pt "abs(as m+ ~(as n))"))
(use "RatLeMinusAbs")
(use "CauchyElim" (pt "M"))
(use "CasM")
(use "mBd")
(use "nBd")
;; ?_7:Mon(RealMod abs(RealConstr as M))
(ng)
(use "MonM")
;; Proof finished.
(save "RealAbsReal")

;; CauchyTimes
(set-goal "all as,M,bs,N,p1,p2(
      Cauchy as M -> 
      Cauchy bs N -> 
      Mon M -> 
      Mon N -> 
      all n abs(as n)<=2**p1 -> 
      all n abs(bs n)<=2**p2 -> 
      Cauchy([n]as n*bs n)([p]M(PosS(p+p2))max N(PosS(p+p1))))")
(assume "as" "M" "bs" "N" "p1" "p2" "CasM" "CbsN" "MonM" "MonN" "p1Bd" "p2Bd")
(use "CauchyIntro")
(assume "p" "n" "m" "nBd" "mBd")
(ng)
(simprat
 (pf "as n*bs n+ ~(as m*bs m)==as n*(bs n+ ~(bs m))+(as n+ ~(as m))*bs m"))
;; 6,7
(use "RatLeTrans" (pt "abs(as n*(bs n+ ~(bs m)))+abs((as n+ ~(as m))*bs m)"))
;; 8,9
(use "RatLeAbsPlus")
(use "RatLeTrans" (pt "(1#2**PosS p)+(1#2**PosS p)"))
;; 10,11
(use "RatLeMonPlus")
;; 12,13

;; ?_12:abs(as n*(bs n+ ~(bs m)))<=(1#2**PosS p)
(simp "RatAbsTimes")
(use "RatLeTrans" (pt "(2**p1)*(1#2**(p+p1+1))"))
(use "RatLeMonTimesTwo")
(use "Truth")
(use "Truth")
(use "p1Bd")

;; ?_20:abs(bs n+ ~(bs m))<=(1#2**(p+p1+1))
(use "CauchyElim" (pt "N"))
(use "CbsN")
(use "NatLeTrans" (pt "M(PosS(p+p2))max N(PosS(p+p1))"))
(use "NatMaxUB2")
(use "nBd")
(use "NatLeTrans" (pt "M(PosS(p+p2))max N(PosS(p+p1))"))
(use "NatMaxUB2")
(use "mBd")

;; ?_16:2**p1*(1#2**(p+p1+1))<=(1#2**PosS p)
(ng)
(simp "PosSSucc")
(simp "PosSSucc")
(ng)
(simp "PosExpTwoPosPlus")
(simp "PosPlusComm")
(use "Truth")

;; ?_13:abs((as n+ ~(as m))*bs m)<=(1#2**PosS p)
(simp "RatAbsTimes")
(use "RatLeTrans" (pt "(1#2**(p+p2+1))*(2**p2)"))
(use "RatLeMonTimesTwo")
(use "Truth")
(use "Truth")

;; ?_39:abs(as n+ ~(as m))<=(1#2**(p+p2+1))
(use "CauchyElim" (pt "M"))
(use "CasM")
(use "NatLeTrans" (pt "M(PosS(p+p2))max N(PosS(p+p1))"))
(use "NatMaxUB1")
(use "nBd")
(use "NatLeTrans" (pt "M(PosS(p+p2))max N(PosS(p+p1))"))
(use "NatMaxUB1")
(use "mBd")
(use "p2Bd")

;; ?_36:(1#2**(p+p2+1))*2**p2<=(1#2**PosS p)
(ng)
(simp "PosSSucc")
(simp "PosSSucc")
(ng)
(simp "PosExpTwoPosPlus")
(simp "PosPlusComm")
(use "Truth")

;; ?_11:(1#2**PosS p)+(1#2**PosS p)<=(1#2**p)
(simprat "RatPlusHalfExpPosS")
(use "Truth")

;; ?_7:as n*bs n+ ~(as m*bs m)==as n*(bs n+ ~(bs m))+(as n+ ~(as m))*bs m
(simprat "RatTimesPlusDistr")
(simprat "RatTimesPlusDistrLeft")
(ng)
(assert "as n*bs n+ ~(as n*bs m)+as n*bs m==as n*bs n+(~(as n*bs m)+as n*bs m)")
 (use "RatPlusAssoc" (pt "as n*bs n") (pt "~(as n*bs m)") (pt "as n*bs m"))
(assume "Assertion")
(simprat "Assertion")
(drop "Assertion")
(assert "~(as n*bs m)+as n*bs m==0")
 (use "Truth")
(assume "Assertion1")
(simprat "Assertion1")
(use "Truth")
;; Proof finished.
(save "CauchyTimes")

;; RealTimesReal
(set-goal "all x,y(Real x -> Real y -> Real(x*y))")
(assume "x" "y" "Rx" "Ry")
(elim "Rx")
(cases)
(assume "as" "M" "CasM" "MonM")
(elim "Ry")
(cases)
(assume "bs" "N" "CbsN" "MonN")
(ng)
(use "RealIntro")
(ng)
(use "CauchyIntro")
(assume "p" "n" "m" "nBd" "mBd")
(ng)
(use-with "CauchyElim"
	  (pt "[n]as n*bs n")
	  (pt "[p]M(PosS(p+cNatPos(cRealBound bs N)))max
                  N(PosS(p+cNatPos(cRealBound as M)))")
	  "?" (pt "p") (pt "n") (pt "m") "?" "?")
(use "CauchyTimes")
(use "CasM")
(use "CbsN")
(use "MonM")
(use "MonN")
;; ?_23:all n abs(as n)<=2**cNatPos(cRealBound as M)
(assert "PosToNat(cNatPos(cRealBound as M))=cRealBound as M")
 (simp "NatPosExFree")
 (use "PosToNatToPosId")
 (use "RealBoundPos")
(assume "EqHyp")
(simp "EqHyp")
(use "RealBoundExFree")
(use "CasM")

;; ?_24:all n abs(bs n)<=2**cNatPos(cRealBound bs N)
(assert "PosToNat(cNatPos(cRealBound bs N))=cRealBound bs N")
 (simp "NatPosExFree")
 (use "PosToNatToPosId")
 (use "RealBoundPos")
(assume "EqHyp")
(simp "EqHyp")
(use "RealBoundExFree")
(use "CbsN")

(use "nBd")
(use "mBd")

;; ?_11:Mon
;;      ((RealConstr([n]as n*bs n)
;;        ([p]
;;          M(PosS(p+cNatPos(cRealBound bs N)))max 
;;          N(PosS(p+cNatPos(cRealBound as M)))))mod)

(ng)
(use "MonIntro")
(ng)
(assume "p" "q" "p<=q")
(use "NatMaxLUB")

(use "NatLeTrans" (pt "M(PosS(q+cNatPos(cRealBound bs N)))"))
(use "MonElim")
(use "MonM")
(ng)
(use "p<=q")
(use "NatMaxUB1")

(use "NatLeTrans" (pt "N(PosS(q+cNatPos(cRealBound as M)))"))
(use "MonElim")
(use "MonN")
(ng)
(use "p<=q")
(use "NatMaxUB2")
;; Proof finished.
(save "RealTimesReal")

;; RealNNegPlusNNeg
(set-goal "all x,y(RealNNeg x -> RealNNeg y -> RealNNeg(x+y))")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "NNegx" "NNegy")
(use "RealNNegChar2RealConstrFree")
(realproof)
(assume "p")
(inst-with-to "RealNNegCharOne"
	      (pt "as") (pt "M") "NNegx" (pt "PosS p") "RealNNegCharOneInstx")
(by-assume "RealNNegCharOneInstx" "n1" "n1Prop")
(inst-with-to "RealNNegCharOne"
	      (pt "bs") (pt "N") "NNegy" (pt "PosS p") "RealNNegCharOneInsty")
(by-assume "RealNNegCharOneInsty" "n2" "n2Prop")
(intro 0 (pt "n1 max n2"))
(assume "n" "nBd")
(simprat "<-" "RatPlusHalfExpPosS")
(simp "RatUMinus2RewRule")
(use "RatLeTrans" (pt "as n+bs n"))
(use "RatLeMonPlus")
(use "n1Prop")
(use "NatLeTrans" (pt "n1 max n2"))
(use "NatMaxUB1")
(use "nBd")
(use "n2Prop")
(use "NatLeTrans" (pt "n1 max n2"))
(use "NatMaxUB2")
(use "nBd")
(ng)
(use "Truth")
;; Proof finished.
(save "RealNNegPlusNNeg")
;; (cdp)
;; ok

;; RealNNegTimesNNeg
(set-goal "all x,y (RealNNeg x -> RealNNeg y -> RealNNeg(x*y))")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "0<=x" "0<=y")
(inst-with-to "RealNNegCharOneExFree" (pt "as") (pt "M") "0<=x" "aProp")
(inst-with-to "RealNNegCharOneExFree" (pt "bs") (pt "N") "0<=y" "bProp")
(cut "all n(n=(cRealBound as M)max(cRealBound bs N) ->
               RealNNeg(RealConstr as M*RealConstr bs N))")
(assume "EqHyp")
(use "EqHyp" (pt "(cRealBound as M)max(cRealBound bs N)"))
(use "Truth")
(assume "n" "nDef")
(use "RealNNegChar2RealConstrFree")
(realproof)
(assume "p")
(cut "all m(
 m=cRealNNegCharOne M(NatToPos(p+n))max cRealNNegCharOne N(NatToPos(p+n)) ->
 exl n all l(n<=l -> ~(1#2**p)<=(RealConstr as M*RealConstr bs N)seq l))")
(assume "EqHyp")
(use "EqHyp"
 (pt "cRealNNegCharOne M(NatToPos(p+n))max cRealNNegCharOne N(NatToPos(p+n))"))
(use "Truth")
(assume "m" "mDef")
(intro 0 (pt "m"))
(assume "l" "m<=l")
(ng #t)
;;   x45609  as  M  y45613  bs  N  Rx:
;;     Real(RealConstr as M)
;;   Ry:Real(RealConstr bs N)
;;   0<=x:RealNNeg(RealConstr as M)
;;   0<=y:RealNNeg(RealConstr bs N)
;;   aProp:all p,n(cRealNNegCharOne M p<=n -> ~(1#2**p)<=as n)
;;   bProp:all p,n(cRealNNegCharOne N p<=n -> ~(1#2**p)<=bs n)
;;   n  nDef:n=cRealBound as M max cRealBound bs N
;;   p  m  mDef:m=cRealNNegCharOne M(NatToPos(p+n))max 
;;              cRealNNegCharOne N(NatToPos(p+n))
;;   l  m<=l:m<=l
;; -----------------------------------------------------------------------------
;; ?_25:(IntN 1#2**p)<=as l*bs l
;; Now the case distinctions
(casedist (pt "as l<=0"))
(assume "as l<=0")
(casedist (pt "bs l<=0"))
(assume "bs l<=0")
;; Case a<=0 & b<=0
(use "RatLeTrans" (pt "0#1"))
(use "Truth")
(simp (pf "(0<=as l*bs l)=(0* ~(bs l)<= ~(as l)* ~(bs l))"))
(use "RatLeMonTimes")
(simp "<-" "RatLeUMinus")
(use "bs l<=0")
(simp "<-" "RatLeUMinus")
(use "as l<=0")
(ng #t)
(use "RatLeCompat")
(simprat (pf "0*bs l==0"))
(use "Truth")
(use "RatTimesZeroL")
(use "Truth")
(assume "bs l<=0 -> F")
;; Case a<=0 & 0<b
(assert "0<bs l")
(use "RatNotLeToLt")
(use "bs l<=0 -> F")
(assume "0<bs l")
(assert "bs l<=2**n")
(use "RatLeTrans" (pt "(2**cRealBound bs N#1)"))
(use "RatLeTrans" (pt "abs(bs l)"))
(use "Truth")
(use "RealBoundExFree")
(use "RealConstrToCauchy")
(realproof)
(simp "nDef")
(ng #t)
(use "PosLeMonPosExp")
(use "NatMaxUB2")
(assume "bs l<=2**n")
(use "RatLeTrans" (pt "~(1#2**(NatToPos(p+n)))*2**n"))
(simp (pf "NatToPos(p+n)=p+n"))
(ng #t)
(simp "PosExpTwoNatPlus")
(simp "NatPlusComm")
(use "Truth")
(use "PosToNatToPosId")
(use "NatLtLeTrans" (pt "Succ Zero"))
(use "Truth")
(use "NatLeTrans" (pt "PosToNat p"))
(simp (pf "Succ Zero=PosToNat 1"))
(simp "PosToNatLe")
(use "Truth")
(use "Truth")
(use "Truth")
(use "RatLeTrans" (pt "as l*2**n"))
(use "RatLeMonTimes")
(use "Truth")
(use "aProp")
(use "NatLeTrans" (pt "m"))
(simp "mDef")
(use "NatMaxUB1")
(use "m<=l")
(simp "<-" "RatLeUMinus")
(simprat (pf "~(as l*bs l)==bs l* ~(as l)"))
(simprat (pf "~(as l*2**n)==2**n* ~(as l)"))
(use "RatLeMonTimes")
(simp "<-" "RatLeUMinus")
(use "as l<=0")
(use "bs l<=2**n")
(ng #t)
(simp "RatTimesComm")
(use "Truth")
(ng #t)
(simp "RatTimesComm")
(use "Truth")
;; Case 0<a
(assume "as l<=0 -> F")
(assert "0<as l")
(use "RatNotLeToLt")
(use "as l<=0 -> F")
(assume "0<as l")
(casedist (pt "0<=bs l"))
;; Case 0<a & 0<=b
(assume "0<=bs l")
(use "RatLeTrans" (pt "0#1"))
(use "Truth")
(use "RatLeTrans" (pt "0*(0#1)"))
(use "Truth")
(use "RatLeMonTimesTwo")
(use "Truth")
(use "Truth")
(use "RatLtToLe")
(use "0<as l")
(use "0<=bs l")
;; Case 0<a & b<=0
(assume "0<=bs l -> F")
(assert "bs l<=0")
(use "RatLtToLe")
(use "RatNotLeToLt")
(use "0<=bs l -> F")
(assume "bs l<=0")
(assert "as l<=2**n")
(use "RatLeTrans" (pt "(2**cRealBound as M#1)"))
(use "RatLeTrans" (pt "abs(as l)"))
(use "Truth")
(use "RealBoundExFree")
(use "RealConstrToCauchy")
(realproof)
(simp "nDef")
(ng #t)
(use "PosLeMonPosExp")
(use "NatMaxUB1")
(assume "as l<=2**n")
(use "RatLeTrans" (pt "~(1#2**(NatToPos(p+n)))*2**n"))
(simp (pf "NatToPos(p+n)=p+n"))
(ng #t)
(simp "PosExpTwoNatPlus")
(simp "NatPlusComm")
(use "Truth")
(use "PosToNatToPosId")
(use "NatLtLeTrans" (pt "Succ Zero"))
(use "Truth")
(use "NatLeTrans" (pt "PosToNat p"))
(simp (pf "Succ Zero=PosToNat 1"))
(simp "PosToNatLe")
(use "Truth")
(use "Truth")
(use "Truth")
(use "RatLeTrans" (pt "bs l*2**n"))
(use "RatLeMonTimes")
(use "Truth")
(use "bProp")
(use "NatLeTrans" (pt "m"))
(simp "mDef")
(use "NatMaxUB2")
(use "m<=l")
(simp "<-" "RatLeUMinus")
(simprat (pf "~(as l*bs l)==as l* ~(bs l)"))
(simprat (pf "~(bs l*2**n)==2**n* ~(bs l)"))
(use "RatLeMonTimes")
(simp "<-" "RatLeUMinus")
(use "bs l<=0")
(use "as l<=2**n")
(ng #t)
(simp "RatTimesComm")
(use "Truth")
(ng #t)
(use "Truth")
;; Proof finished.
(save "RealNNegTimesNNeg")

;; 7.  Compatibilities
;; ===================

;; RealEqCompat
(set-goal "all x,y,z,z1(x===y -> z===z1 -> x===z -> y===z1)")
(assume "x" "y" "z" "z1" "x=y" "z=z1" "x=z")
(use "RealEqTrans" (pt "x"))
(use "RealEqSym")
(use "x=y")
(use "RealEqTrans" (pt "z"))
(use "x=z")
(use "z=z1")
;; Proof finished.
(save "RealEqCompat")

;; RealPosCompat
(set-goal "all as,M,bs,N(
     RealConstr as M===RealConstr bs N -> all p(
     RealPos(RealConstr as M)p ->
     RealPos(RealConstr bs N)(PosS(PosS p))))")
(assume "as" "M" "bs" "N" "x=y" "p" "0<x")
(ng)
;; (1#2**PosS(PosS p))<=bs(N(PosS(PosS(PosS p))))
(use "RatLeTrans" (pt "(1#2**PosS p)+ ~(1#2**PosS(PosS p))"))
;; 4,5
(inst-with-to "RatPlusHalfExpPosS" (pt "PosS p") "RatPlusHalfExpPosSInst")
(simprat "<-" "RatPlusHalfExpPosSInst")
(simp "<-" "RatPlusAssoc")
(use "Truth")
;; ?_5:(1#2**PosS p)+ ~(1#2**PosS(PosS p))<=bs(N(PosS(PosS(PosS p))))
(inst-with-to "RatEqvPlusMinus"
	      (pt "bs(N(PosS(PosS(PosS p))))")
	      (pt "as(M(PosS(PosS(PosS p))))")
	      "RatEqvPlusMinusInst")
(simphyp-to "RatEqvPlusMinusInst" "RatPlusComm" "RatEqvPlusMinusInstSimp")
(drop "RatEqvPlusMinusInst")
(simprat "<-" "RatEqvPlusMinusInstSimp")
(drop "RatEqvPlusMinusInstSimp")
(use "RatLeMonPlus")
;; 17,18
;; ?_17:(1#2**PosS p)<=as(M(PosS(PosS(PosS p))))
(use "RealPosChar1" (pt "M"))
(use "RealEqElim0" (pt "RealConstr bs N"))
(use "x=y")
(use "0<x")
(use "MonElim")
(use "RealConstrToMon" (pt "as"))
(use "RealEqElim0" (pt "RealConstr bs N"))
(use "x=y")
(use "PosLeTrans" (pt "PosS(PosS p)"))
(use "Truth")
(use "Truth")
;; ?_18:~(1#2**PosS(PosS p))<=
;;      bs(N(PosS(PosS(PosS p))))+ ~(as(M(PosS(PosS(PosS p)))))
(use "RatLeTrans"
     (pt "~(as(M(PosS(PosS(PosS p))))+ ~(bs(N(PosS(PosS(PosS p))))))"))
(simp "RatLeUMinus")
(use "RatLeTrans"
     (pt "abs(as(M(PosS(PosS(PosS p))))+ ~(bs(N(PosS(PosS(PosS p))))))"))
(use "Truth")
(use "RealConstrEqElim2")
(use "x=y")
(simp "RatPlusComm")
(use "Truth")
;; Proof finished.
(save "RealPosCompat")

;; RealPosCompatRealConstrFree
(set-goal "all x,y(x===y -> all p(RealPos x p -> RealPos y(PosS(PosS p))))")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "x=y" "p" "0<x")
(use "RealPosCompat" (pt "as") (pt "M"))
(use "x=y")
(use "0<x")
;; Proof finished.
(save "RealPosCompatRealConstrFree")

;; RealNNegCompat
(set-goal "all x,y(x===y -> RealNNeg x -> RealNNeg y)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "x=y" "0<=x")
(use "RealNNegChar2")
(use "RealEqElim1" (pt "RealConstr as M"))
(use "x=y")
(assume "p")
(inst-with-to "RealNNegCharOne"
	      (pt "as") (pt "M") "0<=x" (pt "PosS p") "CharOneInst")
(by-assume "CharOneInst" "n0" "n0Prop")
(inst-with-to "RealEqCharOne" (pt "as") (pt "bs") (pt "M") (pt "N")
	      "x=y" (pt "PosS p") "EqCharOneInst")
(by-assume "EqCharOneInst" "n1" "n1Prop")
(intro 0 (pt "n0 max n1"))
(assume "n" "nBd")
(use "RatLeTrans" (pt "~(1#2**PosS p)+(as n)"))
(simprat "<-" "RatPlusHalfExpPosS")
(simp "RatUMinus2RewRule")
(use "RatLeMonPlus")
(use "Truth")
(use "n0Prop")
(use "NatLeTrans" (pt "n0 max n1"))
(use "NatMaxUB1")
(use "nBd")
(use "RatLePlusRInv")
(use "RatLeTrans" (pt "abs(as n-bs n)+bs n"))
(use "RatLeTrans" (pt "(as n-bs n)+bs n"))
(ng)
(simprat "RatEqvPlusMinus")
(use "Truth")
(use "RatLeMonPlus")
(ng)
(use "Truth")
(use "Truth")
(use "RatLeMonPlus")
(use "n1Prop")
(use "NatLeTrans" (pt "n0 max n1"))
(use "NatMaxUB2")
(use "nBd")
(use "Truth")
;; Proof finished.
(save "RealNNegCompat")

;; In the proof of RealPlusCompat we use RealPlusComm, whose proof
;; (via realproof) uses RealPlusReal.

;; RealPlusComm
(set-goal "all x,y(Real x -> Real y -> x+y===y+x)")
(assert "all x,y x+y=+=y+x")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N")
(use "RealEqSIntro")
(assume "n")
(ng)
(simp "RatPlusComm")
(use "Truth")
;; Assertion proved.
(assume "RealPlusCommEqS")
(assume "x" "y" "Rx" "Ry")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealPlusCommEqS")
;; Proof finished.
(save "RealPlusComm")

;; RealPlusCompat
(set-goal "all x,y,z,z1(x===y -> z===z1 -> x+z===y+z1)")
;; We first proof RealPlusCompatAux
(assert "all x,y,z(Real z -> x===y -> x+z===y+z)")
(assume "x" "y" "z" "Rz" "x=y")
(assert "Real x")
(use "RealEqElim0" (pt "y"))
(use "x=y")
(assume "Rx")
(assert  "Real y")
(use "RealEqElim1" (pt "x"))
(use "x=y")
(assume "Ry")

(assert "Real(y+z)")
(use "RealPlusReal")
(use "Ry")
(use "Rz")
(assert "Real (x+z)")
(use "RealPlusReal")
(use "Rx")
(use "Rz")
(assert "x===y")
(use "x=y")

(elim "Rx")
(cases)
(assume "as" "M" "CasM" "MonM")
(elim "Ry")
(cases)
(assume "bs" "N" "CbsN" "MonN")
(elim "Rz")
(cases)
(assume "cs" "L" "CcsL" "MonL" "asM=bsN" "Rx+z" "Ry+z")
(ng)
(use "RealEqChar2")
(use "Rx+z")
(use "Ry+z")
;; ?_35:all p 
;;      exl n 
;;       all n0(
;;        n<=n0 -> abs(([n1]as n1+cs n1)n0-([n1]bs n1+cs n1)n0)<=(1#2**p))
(assume "p")
;; n0=cRealEqCharOne M N p
(intro 0 (pt "cRealEqCharOne M N p"))
(assume "n" "n0<=n")
(ng)
(simp "<-" "RatPlusAssoc")
(simp "<-" "RatPlusAssoc")
(simp-with "RatPlusComm" (pt "cs n") (pt "~(bs n)+ ~(cs n)"))
(simp "RatPlusAssoc")
(simp "RatPlusAssoc")
(simprat "RatEqvPlusMinus")
(use "RealEqCharOneExFree" (pt "M") (pt "N"))
(use "asM=bsN")
(use "n0<=n")
;; Assertion proved.
(assume "RealPlusCompatAux")
(assume "x" "y" "z" "z1" "x=y" "z=z1")
(assert "Real y")
(use "RealEqElim1" (pt "x"))
(use "x=y")
(assume "Ry")
(assert "Real z")
(use "RealEqElim0" (pt "z1"))
(use "z=z1")
(assume "Rz")
(use "RealEqTrans" (pt "y+z"))
(use "RealPlusCompatAux")
(use "Rz")
(use "x=y")
(use "RealEqTrans" (pt "z+y"))
(use "RealPlusComm")
(use "Ry")
(use "Rz")
(use "RealEqTrans" (pt "z1+y"))
(use "RealPlusCompatAux")
(use "Ry")
(use "z=z1")
(use "RealPlusComm")
(use "RealEqElim1" (pt "z"))
(use "z=z1")
(use "Ry")
;; Proof finished
(save "RealPlusCompat")

;; RealUMinusCompat
(set-goal "all x,y(x===y -> ~x=== ~y)")
(assert "all x,y(x=+=y -> ~x=+= ~y)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "x=+=y")
(assert "all n as n==bs n")
 (use "RealConstrEqSElim" (pt "M") (pt "N"))
 (use "x=+=y")
(assume "xyAllHyp")
(drop "x=+=y")
(use "RealEqSIntro")
(assume "n")
(ng)
(use "RatUMinusCompat")
(use "xyAllHyp")
;; Assertion proved.
(assume "RealUMinusCompatEqS" "x" "y" "x=y")
(assert  "Real x")
(use "RealEqElim0" (pt "y"))
(use "x=y")
(assume "Rx")
(assert "Real y")
(use "RealEqElim1" (pt "x"))
(use "x=y")
(assume "Ry")
(use "RealEqIntro")
;; ?_11: Real(~x)
(use "RealUMinusReal")
(use "Rx")
;; ?_12: Real(~y)
(use "RealUMinusReal")
(use "Ry")
;; all p abs((~x)seq((~x)mod(PosS p))+ ~((~y)seq((~y)mod(PosS p))))<=(1#2**p)
(assume "p")
(assert "x===y")
(use "x=y")
(elim "Rx")
(cases)
(assume "as" "M" "CasM" "MonM")
(elim "Ry")
(cases)
(assume "bs" "N" "CbsN" "MonN" "RasM=RbsN")
(ng)
(assert "all c abs(~c)=abs(c)")
(assume "c")
(use "Truth")
(assume "RatAbsUMinus")
(simp-with "RatAbsUMinus" (pt "as (M(PosS p)) - bs (N(PosS p))"))
(use "RealConstrEqElim2")
(use "RasM=RbsN")
;; Proof finished.
(save "RealUMinusCompat")

;; RealUMinusUMinus
(set-goal "all x(Real x -> ~ ~x===x)")
(assume "x" "Rx")
(use "RealEqSToEq")
(realproof)
(realproof)
(cases (pt "x"))
(assume "as" "M" "xDef")
(use "RealEqSIntro")
(assume "n")
(use "Truth")
;; Proof finished.
(save "RealUMinusUMinus")

;; RealUMinusInj
(set-goal "all x,y(~x=== ~y -> x=== y)")
(assume "x" "y" "EqHyp")
(assert "Real x")
(use "RealUMinusRealInv")
(realproof)
(assume "Rx")
(use "RealEqTrans" (pt "~ ~x"))
(use "RealEqSym")
(use "RealUMinusUMinus")
(realproof)
(use "RealEqTrans" (pt "~ ~y"))
(use "RealUMinusCompat")
(use "EqHyp")
(use "RealUMinusUMinus")
(use "RealUMinusRealInv")
(realproof)
;; Proof finished.
(save "RealUMinusInj")

;; RealAbsCompat
(set-goal  "all x,y(x===y -> abs x===abs y)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "x=y")
(use "RealEqIntro")
(use "RealAbsReal")
(realproof)
(use "RealAbsReal")
(realproof)
(assume "p")
(ng)
(use "RatLeTrans" (pt "abs(as(M(PosS p))+ ~(bs(N(PosS p))))"))
(use "RatLeAbsMinusAbs")
(use "RealConstrEqElim2")
(use "x=y")
;; Proof finished.
(save "RealAbsCompat")

;; In the proof of RealTimesCompat we use RealTimesComm, whose proof
;; (via realproof) uses RealTimesReal.

;; RealTimesComm
(set-goal "all x,y(Real x -> Real y -> x*y===y*x)")
(assert "all x,y x*y=+=y*x")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N")
(use "RealEqSIntro")
(assume "n")
(ng)
(simp "RatTimesComm")
(use "Truth")
;; Assertion proved.
(assume "RealTimesCommEqS" "x" "y" "Rx" "Ry")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealTimesCommEqS")
;; Proof finished.
(save "RealTimesComm")

;; RealTimesCompat
(set-goal "all x,y,z,z1(x===y -> z===z1 -> x*z===y*z1)")
;; We first prove RealTimesCompatAux
(assert  "all x,y,z(Real z -> x===y -> x*z===y*z)")
(assume "x" "y" "z" "Rz" "x=y")
(assert "Real x")
(use "RealEqElim0" (pt "y"))
(use "x=y")
(assume "Rx")
(assert "Real y")
(use "RealEqElim1" (pt "x"))
(use "x=y")
(assume "Ry")

(assert "Real (y*z)")
(use "RealTimesReal")
(use "Ry")
(use "Rz")
(assert "Real (x*z)")
(use "RealTimesReal")
(use "Rx")
(use "Rz")
(assert "x===y")
(use "x=y")

(elim "Rx")
(cases)
(assume "as" "M" "CasM" "MonM")
(elim "Ry")
(cases)
(assume "bs" "N" "CbsN" "MonN")
(elim "Rz")
(cases)
(assume "cs" "L" "CcsL" "MonL" "asM=bsN" "Rxz" "Ryz")
(ng)
(use "RealEqChar2")
(use "Rxz")
(use "Ryz")
;; ?_35:all p 
;;      exl n 
;;       all n0(
;;        n<=n0 -> abs(([n1]as n1*cs n1)n0-([n1]bs n1*cs n1)n0)<=(1#2**p))
(assume "p")
;; n0=cRealEqCharOne M N (p+cRealBound cs L)
(intro 0 (pt "cRealEqCharOne M N (p+cNatPos(cRealBound cs L))"))
(assume "n" "n0<=n")
(ng)
(simp (pf "~(bs n*cs n)= ~(bs n)*cs n"))
(simprat-with "<-" "RatTimesPlusDistrLeft"
	      (pt "as n")(pt "~(bs n)") (pt "cs n"))
(simp "RatAbsTimes")
(use "RatLeTrans"
     (pt "(1#2**(p+cNatPos(cRealBound cs L)))*(2**cRealBound cs L)"))
(use "RatLeMonTimesTwo")
(use "Truth")
(use "Truth")
;; ?_48:abs(as n+ ~(bs n))<=(1#2**(p+cNatPos(cRealBound cs L)))
(use "RealEqCharOneExFree" (pt "M") (pt "N"))
(use "asM=bsN")
(use "n0<=n")
;; ?_49:abs(cs n)<=2**cRealBound cs L
(use "RealBoundExFree")
(use "CcsL")
(ng)
(simp "<-" "PosExpTwoPosPlus")
(assert "PosToNat(cNatPos(cRealBound cs L))=cRealBound cs L")
 (simp "NatPosExFree")
 (use "PosToNatToPosId")
(use "RealBoundPos")
(assume "EqHyp")
(simp "EqHyp")
(simp "PosTimesComm")
(use "Truth")
(use "Truth")
;; Assertion proved.
(assume "RealTimesCompatAux")
(assume "x" "y" "z" "z1" "x=y" "z=z1")
(assert "Real y")
(use "RealEqElim1" (pt "x"))
(use "x=y")
(assume "Ry")
(assert "Real z")
(use "RealEqElim0" (pt "z1"))
(use "z=z1")
(assume "Rz")
(use "RealEqTrans" (pt "y*z"))
(use "RealTimesCompatAux")
(use "Rz")
(use "x=y")
(use "RealEqTrans" (pt "z*y"))
(use "RealTimesComm")
(use "Ry")
(use "Rz")
(use "RealEqTrans" (pt "z1*y"))
(use "RealTimesCompatAux")
(use "Ry")
(use "z=z1")
(use "RealTimesComm")
(use "RealEqElim1" (pt "z"))
(use "z=z1")
(use "Ry")
;; Proof finished
(save "RealTimesCompat")

;; RealLeCompat
(set-goal "all x,y,z,z1(x===y -> z===z1 -> x<<=z -> y<<=z1)")
(assume "x" "y" "z" "z1" "x=y" "z=z1" "x<<=z")
(use "RealLeIntro")
(use "RealEqElim1" (pt "x"))
(use "x=y")
(use "RealEqElim1" (pt "z"))
(use "z=z1")
(use "RealNNegCompat" (pt "z+ ~x"))
(use "RealPlusCompat")
(use "z=z1")
(use "RealUMinusCompat")
(use "x=y")
(use "RealLeElim2")
(use "x<<=z")
;; Proof finished.
(save "RealLeCompat")

;; 8.  Further properties
;; ======================

;; RealPlusAssoc
(set-goal "all x,y,z(Real x -> Real y -> Real z -> x+(y+z)===x+y+z)")
(assert "all x,y,z x+(y+z)=+=x+y+z")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N")
(cases)
(assume "cs" "L")
(use "RealEqSIntro")
(assume "n")
(ng)
(use "Truth")
;; Assertion proved.
(assume "RealPlusAssocEqS" "x" "y" "z" "Rx" "Ry" "Rz")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealPlusAssocEqS")
;; Proof finished.
(save "RealPlusAssoc")

;; RealTimesAssoc
(set-goal "all x,y,z(Real x -> Real y -> Real z -> x*(y*z)===x*y*z)")
(assert "all x,y,z x*(y*z)=+=x*y*z")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N")
(cases)
(assume "cs" "L")
(use "RealEqSIntro")
(assume "n")
(ng)
(use "Truth")
;; Assertion proved.
(assume "RealTimesAssocEqS" "x" "y" "z" "Rx" "Ry" "Rz")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealTimesAssocEqS")
;; Proof finished.
(save "RealTimesAssoc")

;; RealTimesPlusDistr
(set-goal "all x,y,z(Real x -> Real y -> Real z -> x*(y+z)===x*y+x*z)")
(assert "all x,y,z x*(y+z)=+=x*y+x*z")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N")
(cases)
(assume "cs" "L")
(use "RealEqSIntro")
(assume "n")
(ng)
(use "RatTimesPlusDistr")
;; Assertion proved.
(assume "RealTimesPlusDistrEqS" "x" "y" "z" "Rx" "Ry" "Rz")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealTimesPlusDistrEqS")
;; Proof finished.
(save "RealTimesPlusDistr")

;; RealTimesPlusDistrLeft
(set-goal "all x,y,z(Real x -> Real y -> Real z -> (x+y)*z===x*z+y*z)")
(assert "all x,y,z (x+y)*z=+=x*z+y*z")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N")
(cases)
(assume "cs" "L")
(use "RealEqSIntro")
(assume "n")
(ng)
(use "RatTimesPlusDistrLeft")
;; Assertion proved
(assume "RealTimesPlusDistrLeftEqS" "x" "y" "z" "Rx" "Ry" "Rz")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealTimesPlusDistrLeftEqS")
;; Proof finished.
(save "RealTimesPlusDistrLeft")

;; RealTimesOne
(set-goal "all x(Real x -> x*1===x)")
(assert "all x x*1=+=x")
(cases)
(assume "as" "M")
(use "RealEqSIntro")
(assume "n")
(ng)
(use "Truth")
;; Assertion proved.
(assume "RealTimesOneEqS" "x" "Rx")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealTimesOneEqS")
;; Proof finished.
(save "RealTimesOne")

;; RealOneTimes
(set-goal "all x(Real x -> 1*x===x)")
(assert "all x 1*x=+=x")
(cases)
(assume "as" "M")
(use "RealEqSIntro")
(assume "n")
(ng)
(use "Truth")
;; Assertion proved.
(assume "RealOneTimesEqS" "x" "Rx")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealOneTimesEqS")
;; Proof finished.
(save "RealOneTimes")

;; RealTimesIntNOne
(set-goal "all x(Real x -> x*IntN 1=== ~x)")
(assert "all x x*IntN 1=+= ~x")
(cases)
(assume "as" "M")
(use "RealEqSIntro")
(assume "n")
(ng)
(use "Truth")
;; Assertion proved.
(assume "RealTimesIntNOneEqS" "x" "Rx")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealTimesIntNOneEqS")
;; Proof finished.
(save "RealTimesIntNOne")

;; RealIntNOneTimes
(set-goal "all x(Real x -> IntN 1*x=== ~x)")
(assert "all x IntN 1*x=+= ~x")
(cases)
(assume "as" "M")
(use "RealEqSIntro")
(assume "n")
(ng)
(use "Truth")
;; Assertion proved.
(assume "RealIntNOneTimesEqS" "x" "Rx")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealIntNOneTimesEqS")
;; Proof finished.
(save "RealIntNOneTimes")

;; RealTimesIdUMinus
(set-goal "all x,y(Real x -> Real y -> x* ~y=== ~(x*y))")
(assert "all x,y x* ~y=+= ~(x*y)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N")
(use "RealEqSIntro")
(assume "n")
(ng)
(use "Truth")
;; Assertion proved.
(assume "RealTimesIdUMinusEqS" "x" "y" "Rx" "Ry")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealTimesIdUMinusEqS")
;; Proof finished.
(save "RealTimesIdUMinus")

;; RealTimesIdRatUMinus
(set-goal "all x,k(Real x -> x* ~k=== ~(x*k))")
(assert "all x,k x* ~k=+= ~(x*k)")
(cases)
(assume "as" "M" "k")
(use "RealEqSIntro")
(assume "n")
(ng)
(use "Truth")
;; Assertion proved.
(assume "RealTimesIdRatUMinusEqS" "x" "k" "Rx")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealTimesIdRatUMinusEqS")
;; Proof finished.
(save "RealTimesIdRatUMinus")

;; RealUMinusPlus
(set-goal "all x,y(Real x -> Real y -> ~(x+y)=== ~x+ ~y)")
(assert "all x,y(Real x -> Real y -> ~(x+y)=+= ~x+ ~y)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "Rx" "Ry")
(use "RealEqSIntro")
(assume "n")
(ng)
(use "Truth")
;; Assertion proved.
(assume "RealUMinusPlusEqS" "x" "y" "Rx" "Ry")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealUMinusPlusEqS")
(use "Rx")
(use "Ry")
;; Proof finished.
(save "RealUMinusPlus")

;; RealUMinusPlusRat
(set-goal "all x,k(Real x -> ~(x+k)=== ~x+ ~k)")
(assert "all x,k(Real x -> ~(x+k)=+= ~x+ ~k)")
(cases)
(assume "as" "M" "k" "Rx")
(use "RealEqSIntro")
(assume "n")
(ng)
(use "Truth")
;; Assertion proved.
(assume "RealUMinusPlusRatEqS" "x" "k" "Rx")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealUMinusPlusRatEqS")
(use "Rx")
;; Proof finished.
(save "RealUMinusPlusRat")

;; RealAbsUMinus
(set-goal "all x(Real x -> abs~x===abs x)")
(assert "all x abs~x=+=abs x")
(cases)
(assume "as" "M")
(use "RealEqSIntro")
(assume "n")
(use "Truth")
;; Assertion proved.
(assume "RealAbsUMinusEqS" "x" "Rx")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealAbsUMinusEqS")
;; Proof finished.
(save "RealAbsUMinus")

;; RealLeUMinus
(set-goal "all x,y(x<<=y -> ~y<<= ~x)")
(assume "x" "y" "x<=y")
(use "RealLeIntro")
(realproof)
(realproof)
(inst-with-to "RealLeElim2" (pt "x") (pt "y") "x<=y" "RealLeElimInst")
(simpreal "RealUMinusUMinus")
(simpreal "RealPlusComm")
(use "RealLeElimInst")
(realproof)
(realproof)
(realproof)
;; Proof finished.
(save "RealLeUMinus")

;; RealLeUMinusInv
(set-goal "all x,y(~y<<= ~x -> x<<=y)")
(assume "x" "y" "~y<=~x")
(assert "Real x")
(use "RealUMinusRealInv")
(realproof)
(assume "Rx")
(assert "Real y")
(use "RealUMinusRealInv")
(realproof)
(assume "Ry")
(simpreal (pf "x=== ~ ~x")) ;here we need RealLeCompat
(simpreal (pf "y=== ~ ~y"))
(use "RealLeUMinus")
(use "~y<=~x")
(use "RealEqSym")
(use "RealUMinusUMinus")
(use "Ry")
(use "RealEqSym")
(use "RealUMinusUMinus")
(use "Rx")
;; Proof finished.
(save "RealLeUMinusInv")

;; Similar to  RealSeqEqToEq we have a pointwise criterium for RealNNeg

;; For RealLeTrans we need a stronger form of RealSeqLeToLe: it
;; suffices to have x seq n<=y seq n from one point onwards.

;; RealSeqLeNNegToNNeg
(set-goal "all x,y,n1(Real y ->
 all n(n1<=n -> x seq n<=y seq n) -> RealNNeg x -> RealNNeg y)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "n1" "Ry" "LeHyp" "xNNeg")
(use "RealNNegChar2")
(use "Ry")
(assume "p")
(inst-with-to "RealNNegCharOne" (pt "as") (pt "M") "xNNeg" (pt "p")
	      "RealNNegCharOneInst")
(by-assume "RealNNegCharOneInst" "n2" "n2Prop")
(intro 0 (pt "n1 max n2"))
(assume "n" "nBd")
(use "RatLeTrans" (pt "as n"))
(use "n2Prop")
(use "NatLeTrans" (pt "n1 max n2"))
(use "NatMaxUB2")
(use "nBd")
(use "LeHyp")
(use "NatLeTrans" (pt "n1 max n2"))
(use "NatMaxUB1")
(use "nBd")
;; Proof finished.
(save "RealSeqLeNNegToNNeg")

;; RealSeqLeToLe
(set-goal "all x,y,n1(Real x -> Real y ->
 all n(n1<=n -> x seq n<=y seq n) -> x<<=y)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "n1" "Rx" "Ry" "SeqLeHyp")
(ng)
(use "RealLeIntro")
(use "Rx")
(use "Ry")
(inst-with-to "RealSeqLeNNegToNNeg"
	      (pt "RealConstr([n](0#1))([p]Zero)")
	      (pt "RealConstr bs N+ ~(RealConstr as M)") (pt "n1")
	      "RealSeqLeNNegToNNegInst")
(use "RealSeqLeNNegToNNegInst")
(realproof)
(assume "n" "nBd")
(ng)
(assert "all a,b(a<=b -> 0<=b+ ~a)")
 (assume "a" "b" "a<=b")
 (use "RatLeTrans" (pt "a+ ~a"))
 (simprat (pf "a+ ~a==0"))
 (use "Truth")
 (use "Truth")
 (use "RatLeMonPlus")
 (use "a<=b")
 (use "Truth")
(assume "RatLeToZeroLePlusMinus")
(use "RatLeToZeroLePlusMinus")
(use "SeqLeHyp")
(use "nBd")
(drop "RealSeqLeNNegToNNegInst")
(use "RealNNegIntro")
(use "RealRat")
(assume "p")
(ng)
(use "Truth")
;; Proof finished.
(save "RealSeqLeToLe")

;; RealLeTrans we need closure of RealNNeg under RealPlus (Lemma 5.5
;; in constr16)
;; RealLeAbsPlus
(set-goal "all x,y(Real x -> Real y -> abs(x+y)<<=abs x+abs y)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "Rx" "Ry")
(use "RealSeqLeToLe" (pt "Zero"))
(use "RealAbsReal")
(use "RealPlusReal")
(use "Rx")
(use "Ry")
(use "RealPlusReal")
(use "RealAbsReal")
(use "Rx")
(use "RealAbsReal")
(use "Ry")
(assume "n" "Useless")
(use "Truth")
;; Proof finished.
(save "RealLeAbsPlus")

;; 2016-11-30.  Additions to rea.scm from Nils Koepp

;; RealPlusMinusZero
(set-goal "all x(Real x -> x+ ~x===0)")
(assert "all x x+ ~x=+=0")
(cases)
(assume "as" "M")
(use "RealEqSIntro")
(assume "n")
(ng)
(use "Truth")
;; Assertion proved.
(assume "RealPlusMinusZeroEqS" "x" "Rx")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealPlusMinusZeroEqS")
;; Proof finished.
(save "RealPlusMinusZero")

;; RealNNegToEq
(set-goal "all x(RealNNeg x -> RealNNeg(~x) -> x===0)")
(cases)
(assume "as" "M" "NNegx" "NNeg~x")
(use "RealEqIntro")
(realproof)
(use "RealRat")
(assume "p")
(ng)
(use "RatLeAbs")
(use "RatLeTrans" (pt "(1#2**PosS p)"))
(simprat (pf "as(M(PosS p))== ~(([n]~(as n))(M(PosS p)))+0"))
(use "RatLePlusRInv")
(use "RealConstrNNegElim1")
(use "NNeg~x")
(use "Truth")
(simp "<-" "RatLeUMinus")
(simprat "<-" "RatPlusHalfExpPosS")
(simp "RatLeUMinus")
(use "Truth")
(use "RatLeTrans" (pt "(1#2**PosS p)"))
(simprat (pf "~(as(M(PosS p)))== ~(as(M(PosS p)))+0"))
(use "RatLePlusRInv")
(use "RealConstrNNegElim1")
(use "NNegx")
(use "Truth")
(simp "<-" "RatLeUMinus")
(simprat "<-" "RatPlusHalfExpPosS")
(simp "RatLeUMinus")
(use "Truth")
;; Proof finished.
(save "RealNNegToEq")

;; RealAbsId
(set-goal "all x(RealNNeg x -> abs x<<=x)")
(cases)
(assume "as" "M" "0<=x")
(use "RealLeIntro")
(realproof)
(realproof)
(use "RealNNegChar2RealConstrFree")
(realproof)
(assume "p")
(ng)
(inst-with-to "RealNNegCharOne"
	      (pt "as") (pt "M") "0<=x" (pt "PosS p") "RealNNegCharOneInst")
(by-assume "RealNNegCharOneInst" "n" "nProp")
(intro 0 (pt "n"))
(assume "n0" "n0Bd")
(simprat (pf "(IntN 1#2**p)== ~((1#2**PosS p)+(1#2**PosS p))"))
(cases (pt "0<= as n0"))
(assume "0<=a")
(simp "RatAbsId")
(use "RatLeTrans" (pt "(0#1)"))
(use "Truth")
(assert "(as n0+ ~(as n0))==0")
(use "RatEqv2RewRule" (pt "as n0"))
(assume "EqHyp")
(simprat "EqHyp")
(use "Truth")
(use "0<=a")
(assume "0<=a -> F")
(assert "all a ~(a+a)== ~a+ ~a")
(cases)
(strip)
(use "Truth")
(assume "Assertion")
(simprat "Assertion")
(use "RatLeMonPlus")
(use "nProp")
(use "n0Bd")
(drop "Assertion")
(simp "RatLe7RewRule")
(use "RatLeAbs")
(use "RatLeTrans" (pt "(0#1)"))
(use "RatLtToLe")
(use "RatNotLeToLt")
(use "0<=a -> F")
(use "Truth")
(simp (pf "(1#2**PosS p)= ~ ~(1#2**PosS p)"))
(simp "RatLe7RewRule")
(use "nProp")
(use "n0Bd")
(use "Truth")
(simprat "RatPlusHalfExpPosS")
(use "Truth")
;; Proof finished.
(save "RealAbsId")

;; RealLeAbsId
(set-goal "all x(Real x -> x<<=abs x)")
(cases)
(assume "as" "M" "Rx")
(use "RealSeqLeToLe" (pt "Zero"))
(use "Rx")
(realproof)
(assume "n" "Useless")
(use "Truth")
;; Proof finished.
(save "RealLeAbsId")

;; RealNNegAbs
(set-goal "all x(Real x -> RealNNeg(abs x))")
(assume "x" "Rx")
(use "RealNNegChar2RealConstrFree")
(realproof)
(assume "p")
(intro 0 (pt "Zero"))
(assume "n" "Useless")
(cases (pt "x"))
(assume "as" "M" "xDef")
(ng #t)
(use "RatLeTrans" (pt "(0#1)"))
(use "Truth")
(use "Truth")
;; Proof finished.
(save "RealNNegAbs")

;; RealPosMonPlus
(set-goal "all x,y,p,q(Real x -> Real y -> RealPos x p -> RealPos y q ->
                       RealPos(x+y)(PosS(PosS(p min q))))")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "p" "q" "Rx" "Ry" "x ppos" "y qpos")
(use "RealPosChar2RealConstrFree" (pt "M(PosS p)max N(PosS q)"))
(realproof)
(assume "n" "n0<=n")
(assert "(1#2**PosS p)<=as n")
(use "RealPosChar1" (pt "M"))
(use "Rx")
(use "x ppos")
(use "NatLeTrans" (pt "M(PosS p)max N(PosS q)"))
(use "NatMaxUB1")
(use "n0<=n")
(assume "ineq01")
(assert "(1#2**PosS q)<=bs n")
(use "RealPosChar1" (pt "N"))
(use "Ry")
(use "y qpos")
(use "NatLeTrans" (pt "M(PosS p)max N(PosS q)"))
(use "NatMaxUB2")
(use "n0<=n")
(assume "ineq02")
(use "RatLeTrans" (pt "(1#2**PosS p)+(1#2**PosS q)"))
(casedist (pt "p<=q"))
(assume "p<=q")
(assert "p min q=p")
(use "PosMinEq2")
(use "p<=q")
(assume "hyp")
(simp "hyp")
(simp "RatPlusComm")
(use "Truth")
(assume "p<=q -> F")
(assert "q<=p")
(use "PosNotLtToLe")
(assume "p<q")
(use "p<=q -> F")
(use "PosLtToLe")
(use "p<q")
(assume "q<=p")
(assert "p min q=q")
(use "PosMinEq1")
(use "q<=p")
(assume "hyp")
(simp "hyp")
(use "Truth")
(simp "RatLeCompat" (pt "(1#2**PosS p)+(1#2**PosS q)") (pt "as n+bs n"))
(use "RatLeMonPlus")
(use "ineq01")
(use "ineq02")
(ng)
(use "Truth")
(use "Truth")
;; Proof finished.
(save "RealPosMonPlus")

;; RealApprox
(set-goal "all x,p(Real x -> exl a abs(a+ ~x)<<=(1#2**p))")
(cases)
(assume "as" "M" "p" "Rx")
(intro 0 (pt "as (M p)"))
(use "RealLeIntro")
(realproof)
(use "RealRat")
(use "RealNNegIntro")
(realproof)
(assume "p0")
(ng)
(simp "RatPlusComm")
(simp "RatPlusAssoc")
(use "RatLePlusR")
(simp "<-" "RatLeUMinus")
(simprat (pf "~ ~abs(as(M p)+ ~(as(M(PosS(PosS p0)))))==
              abs(as(M p)+ ~(as(M(PosS(PosS p0)))))"))
(simprat (pf "~(~((1#2**p0)+(1#2**p))+0)==(1#2**p0)+(1#2**p)"))
(use "RatLeTrans" (pt "abs(as(M p)+ ~(as(M (p+(PosS(PosS p0))))))+
                       abs(as(M(p+(PosS(PosS p0))))+ ~(as(M(PosS(PosS p0)))))"))
(use "RatLeAbsMinus")
(simp "RatPlusComm")
(use "RatLeMonPlus")
(use "CauchyElim" (pt "M"))
(use "RealConstrToCauchy")
(use "Rx")
(use "MonElim")
(use "RealConstrToMon" (pt "as"))
(use "Rx")
(use "PosLeTrans" (pt "(PosS(PosS p0))"))
(use "PosLeTrans" (pt "PosS p0"))
(use "Truth")
(use "Truth")
(ng)
(use "Truth")
(use "MonElim")
(use "RealConstrToMon" (pt "as"))
(use "Rx")
(use "PosLeTrans" (pt "PosS p0"))
(use "Truth")
(use "Truth")
(use "CauchyElim" (pt "M"))
(use "RealConstrToCauchy")
(use "Rx")
(use "MonElim")
(use "RealConstrToMon" (pt "as"))
(use "Rx")
(ng)
(use "Truth")
(use "MonElim")
(use "RealConstrToMon" (pt "as"))
(use "Rx")
(use "PosLeTrans" (pt "(PosS(PosS p))"))
(use "PosLeTrans" (pt "PosS p"))
(use "Truth")
(use "Truth")
(ng)
(use "Truth")
(use "Truth")
(use "Truth")
;; Proof finished.
(save "RealApprox")
;; (cdp)

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [x,p][if x ([as,M]as(M p))]

;; RealLeRefl
(set-goal "all x(Real x -> x<<=x)")
(cases)
(assume "as" "M" "Rx")
(use "RealLeIntro")
(use "Rx")
(use "Rx")
(use "RealNNegIntro")
(realproof)
(assume "p")
(ng)
(simprat (pf "as(M(PosS p))+ ~(as(M(PosS p)))==0"))
(ng)
(use "Truth")
(ng)
(use "Truth")
;; Proof finished.
(save "RealLeRefl")
;; (cdp)

;; RealPlusZero
(set-goal "all x(Real x -> x+0===x)")
(assert "all x x+0=+=x")
(cases)
(assume "as" "M")
(use "RealEqSIntro")
(assume "n")
(ng)
(use "Truth")
;; Assertion proved.
(assume "RealPlusZeroEqS" "x" "Rx")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealPlusZeroEqS")
;; Proof finished.
(save "RealPlusZero")

;; RealTimesZero
(set-goal "all x(Real x -> x*0===0)")
(assert "all x x*0=+=0")
(cases)
(assume "as" "M")
(use "RealEqSIntro")
(assume "n")
(ng)
(use "RatTimesZeroR")
;; Assertion proved.
(assume "RealTimesZeroEqS" "x" "Rx")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealTimesZeroEqS")
;; Proof finished.
(save "RealTimesZero")

;; RealZeroTimes
(set-goal "all x(Real x -> 0*x===0)")
(assert "all x 0*x=+=0")
(cases)
(assume "as" "M")
(use "RealEqSIntro")
(assume "n")
(ng)
(use "RatTimesZeroL")
;; Assertion proved.
(assume "RealZeroTimesEqS" "x" "Rx")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealZeroTimesEqS")
;; Proof finished.
(save "RealZeroTimes")

;; RealEqPlusMinus
(set-goal "all x,y(Real x -> Real y -> x+ ~y+y===x)")
(assume "x" "y" "Rx" "Ry")
(simpreal "<-" "RealPlusAssoc")
(simpreal (pf "~y+y===y+ ~y"))
(simpreal "RealPlusMinusZero")
(use "RealPlusZero")
(use "Rx")
(use "Ry")
(use "RealPlusComm")
(realproof)
(use "Ry")
(use "Ry")
(realproof)
(use "Rx")
;; Proof finished.
(save "RealEqPlusMinus")

;; RealNNegLeToNNeg
(set-goal "all x,y(RealNNeg x -> x<<=y -> RealNNeg y)")
(assume "x" "y" "NNegx" "x<=y")
(simpreal "<-" (pf "y+ ~x+x===y"))
(use "RealNNegPlusNNeg")
(use "RealLeElim2")
(use "x<=y")
(use "NNegx")
(use "RealEqPlusMinus")
(realproof)
(realproof)
;; Proof finished.
(save "RealNNegLeToNNeg")

;; RealLeAntiSym
(set-goal "allnc x,y(x<<=y -> y<<=x -> x===y)")
(assume "x" "y" "x<=y" "y<=x")
(assert "x+ ~y===0")
(assert "RealNNeg(y+ ~x)")
(use "RealLeElim2")
(use "x<=y")
(assume "y-x>=0")
(assert "RealNNeg(x+ ~y)")
(use "RealLeElim2")
(use "y<=x")
(assume "x-y>=0")
(use "RealNNegToEq" (pt "x+ ~y"))
(use "x-y>=0")
(use "RealNNegCompat" (pt "y+ ~x"))
(use "RealEqSym")
(use "RealEqTrans" (pt "~x + ~ ~y"))
(use "RealUMinusPlus")
(realproof)
(realproof)
(use "RealEqTrans" (pt "~x +y"))
(use "RealPlusCompat" (pt "~x") (pt "~x") (pt "~ ~y") (pt "y"))
(use "RealEqRefl")
(realproof)
(use "RealUMinusUMinus")
(realproof)
(use "RealPlusComm")
(realproof)
(realproof)
(use "y-x>=0")
(assume "x-y=0")
(use "RealEqTrans" (pt "x+0"))
(use "RealEqSym")
(use "RealPlusZero")
(realproof)
(use "RealEqTrans" (pt "x+ ~y+y"))
(use "RealEqTrans" (pt "x+(~y+y)"))
(use "RealPlusCompat")
(use "RealEqRefl")
(realproof)
(use "RealEqSym")
(use "RealEqTrans" (pt "y+ ~y"))
(use "RealPlusComm")
(realproof)
(realproof)
(use "RealPlusMinusZero")
(realproof)
(use "RealPlusAssoc")
(realproof)
(realproof)
(realproof)
(use "RealEqTrans" (pt "0+y"))
(use "RealPlusCompat")
(use "x-y=0")
(use "RealEqRefl")
(realproof)
(use "RealEqTrans" (pt "y+0"))
(use "RealPlusComm")
(use "RealRat")
(realproof)
(use "RealPlusZero")
(realproof)
;; Proof finished.
(save "RealLeAntiSym")

;; RealLeTrans
(set-goal "allnc x,y,z(x<<=y -> y<<=z -> x<<=z)")
(assume "x" "y" "z" "x<=y" "y<=z")
(use "RealLeIntro")
(realproof)
(realproof)
(use "RealNNegCompat" (pt "z+ ~y+(y+ ~x)"))
;;z-y+(y-x)=z-x
(use "RealEqTrans" (pt "z+(~y+(y+ ~x))"))
(use "RealEqSym")
(use "RealPlusAssoc")
(realproof)
(use "RealUMinusReal")
(realproof)
(use "RealPlusReal")
(realproof)
(use "RealUMinusReal")
(realproof)
(use "RealPlusCompat")
(use "RealEqRefl")
(realproof)
(use "RealEqTrans" (pt "~y+y+ ~x"))
(use "RealPlusAssoc")
(use "RealUMinusReal")
(realproof)
(realproof)
(use "RealUMinusReal")
(realproof)
(use "RealEqTrans" (pt "0+ ~x"))
(use "RealPlusCompat")
(use "RealEqTrans" (pt "y+ ~y"))
(use "RealPlusComm")
(use "RealUMinusReal")
(realproof)
(realproof)
(use "RealPlusMinusZero")
(realproof)
(use "RealEqRefl")
(use "RealUMinusReal")
(realproof)
(use "RealEqTrans" (pt "~x +0"))
(use "RealPlusComm")
(use "RealRat")
(use "RealUMinusReal")
(realproof)
(use "RealPlusZero")
(use "RealUMinusReal")
(realproof)
;; arithmetic done
(use "RealNNegPlusNNeg")
(use "RealLeElim2")
(use "y<=z")
(use "RealLeElim2")
(use "x<=y")
;; Proof finished.
(save "RealLeTrans")

;; RealLeMonPlus
(set-goal "allnc x,y,z,z0(x<<=y -> z<<=z0 -> x+z<<=y+z0)")
;; First we prove a special case
(assert "allnc x,y,z(Real z -> x<<=y -> x+z<<=y+z)")
(assume "x" "y" "z" "Rz" "x<=y")
(use "RealLeIntro")
(realproof)
(realproof)
(use "RealNNegCompat" (pt "y+ ~x"))
(use "RealEqSym")
(use "RealEqTrans" (pt "y+z+( ~x+ ~z)"))
(use "RealPlusCompat" (pt "y+z") (pt "y+z"))
(use "RealEqRefl")
(realproof)
(use "RealUMinusPlus")
(realproof)
(use "Rz")
(use "RealEqTrans" (pt "y+(z+(~x+ ~z))"))
(use "RealEqSym")
(use "RealPlusAssoc")
(realproof)
(use "Rz")
(realproof)
(use "RealEqTrans" (pt "y+(z+(~z+ ~x))" ))
(use "RealPlusCompat")
(use "RealEqRefl")
(realproof)
(use "RealPlusCompat")
(use "RealEqRefl")
(use "Rz")
(use "RealPlusComm")
(realproof)
(realproof)
(use "RealEqTrans" (pt "y+(z+ ~z+ ~x)"))
(use "RealPlusCompat")
(use "RealEqRefl")
(realproof)
(use "RealPlusAssoc")
(use "Rz")
(use "RealUMinusReal")
(use "Rz")
(use "RealUMinusReal")
(realproof)
(use "RealEqTrans" (pt "y+(0+ ~x)"))
(use "RealPlusCompat")
(use "RealEqRefl")
(realproof)
(use "RealPlusCompat")
(use "RealPlusMinusZero")
(use "Rz")
(use "RealEqRefl")
(use "RealUMinusReal")
(realproof)
(use "RealPlusCompat")
(use "RealEqRefl")
(realproof)
(use "RealEqTrans" (pt "~x+0"))
(use "RealPlusComm")
(use "RealRat")
(use "RealUMinusReal")
(realproof)
(use "RealPlusZero")
(use "RealUMinusReal")
(realproof)
(use "RealLeElim2")
(use "x<=y")
;; Assertion proved.
(assume "RealLeMonPlusAux" "x" "y" "z" "z0" "x<=y" "z<=z0")
(use "RealLeTrans" (pt "y+z"))
(use "RealLeMonPlusAux")
(realproof)
(use "x<=y")
(simpreal "RealPlusComm")
(simpreal (pf "y+z0===z0+y"))
(use "RealLeMonPlusAux")
(realproof)
(use "z<=z0")
(use "RealPlusComm")
(realproof)
(realproof)
(realproof)
(realproof)
;; Proof finished.
(save "RealLeMonPlus")

;; RealLeMonTimes
(set-goal "all x,y,z(RealNNeg x -> y<<=z -> x*y<<=x*z)")
(assume "x" "y" "z" "NNegx" "y<=z")
(use "RealLeIntro")
(realproof)
(realproof)
(simpreal "<-" "RealTimesIdUMinus")
(simpreal "<-" "RealTimesPlusDistr")
(use "RealNNegTimesNNeg")
(use "NNegx")
(use "RealLeElim2")
(use "y<=z")
(realproof)
(realproof)
(realproof)
(realproof)
(realproof)
;; Proof finished.
(save "RealLeMonTimes")

;; RealLeMonTimesTwo
(set-goal
 "all x,y,z,z0(RealNNeg x -> RealNNeg z -> x<<=y -> z<<=z0 -> x*z<<=y*z0)")
(assume "x" "y" "z" "z0" "NNegx" "NNegz" "x<=y" "z<=z0")
(use "RealLeTrans" (pt "x*z0"))
(use "RealLeMonTimes")
(use "NNegx")
(use "z<=z0")
(simpreal "RealTimesComm")
(simpreal (pf "y*z0===z0*y"))
(use "RealLeMonTimes")
(use "RealNNegLeToNNeg" (pt "z"))
(use "NNegz")
(use "z<=z0")
(use "x<=y")
(use "RealTimesComm")
(realproof)
(realproof)
(realproof)
(realproof)
;; Proof finished.
(save "RealLeMonTimesTwo")

;; ApproxSplit
(set-goal "all x,y,z,p(Real x -> Real y -> Real z -> RealLt x y p ->
                       z<<=y ori x<<=z)")
(cases)
(assume "as" "M")
(cases)
(assume "as0" "M0")
(cases)
(assume "as1" "M1" "p" "Rx" "Ry" "Rz" "y<x")
(cut "all n,m(n=M0(PosS(PosS p))max M(PosS(PosS p)) -> 
 m=M1(PosS(PosS p))max M0(PosS(PosS p))max M(PosS(PosS p)) -> 
 RealConstr as1 M1<<=RealConstr as0 M0 ori
 RealConstr as M<<=RealConstr as1 M1)")
(assume "allhyp")
(use "allhyp" (pt "M0(PosS(PosS p))max M(PosS(PosS p))")
     (pt "M1(PosS(PosS p))max M0(PosS(PosS p))max M(PosS(PosS p))"))
(use "Truth")
(use "Truth")
(assume "n" "m" "n=" "m=")
(casedist (pt "as1 m <= (as n+as0 n)*(1#2)"))
(assume "hyp")
(intro 0)
(use "RealLeIntro")
(use "Rz")
(use "Ry")
(use "RealNNegChar2RealConstrFree")
(realproof)
(assume "p0")
(intro 0 (pt "m"))
(assume "l" "m<=l")
(use "RatLeTrans" (pt "(0#1)"))
(use "Truth")
(simprat (pf "(RealConstr as0 M0+ ~(RealConstr as1 M1))seq l==as0 l+ ~(as1 l)"))
(simp "RatPlusComm")
(use "RatLePlusR")
(simprat (pf "~ ~(as1 l)+0==as1 l"))
(use "RatLeTrans" (pt "as1 m+(1#2**PosS(PosS p))"))
(use "RatLePlusR")
(use "RatLeTrans" (pt "abs(as1 l+ ~(as1 m))"))
(simp "RatPlusComm")
(ng)
(use "Truth")
(use "CauchyElim" (pt "M1"))
(use "RealConstrToCauchy")
(use "Rz")
(use "NatLeTrans" (pt "m"))
(simp "m=")
(use "NatLeTrans" (pt "M1(PosS(PosS p))max M0(PosS(PosS p))"))
(use "NatMaxUB1")
(use "NatMaxUB1")
(use "m<=l")
(use "NatLeTrans" (pt "m"))
(simp "m=")
(use "NatLeTrans" (pt "M1(PosS(PosS p))max M0(PosS(PosS p))"))
(use "NatMaxUB1")
(use "NatMaxUB1")
(use "Truth")
(use "RatLeTrans" (pt "(as n+as0 n)*(1#2)+(as0 n+ ~(as n))*(1#2**2)"))
(use "RatLeMonPlus")
(use "hyp")
(simprat (pf "(1#2**PosS(PosS p))==(1#2**p)*(1#2**2)"))
(use "RatLeMonTimes")
(use "Truth")
(ng "y<x")
(simp "n=")
(use "y<x")
(assert "(1#2)**PosS(PosS p)==(1#2)**p*(1#2)**2")
(simprat "RatExpPosS")
(simprat "RatExpPosS")
(ng)
(use "Truth")
(assume "arithm")
(use "arithm")
(simprat (pf "(as n+as0 n)*(1#2)+(as0 n+ ~(as n))*(1#2**2)==
              as0 n+ ~(as0 n+ ~(as n))*(1#2**2)"))
(use "RatLeTrans" (pt "as0 n+ ~(1#2**PosS(PosS p))"))
(use "RatLeMonPlus")
(use "Truth")
(simprat (pf "(1#2**PosS(PosS p))==(1#2**p)*(1#2**2)"))
(simprat (pf "~((1#2**p)*(1#2**2))== ~(1#2**p)*(1#2**2)"))
(use "RatLeMonTimes")
(use "Truth")
(simp "RatLeUMinus")
(simp "n=")
(use "y<x")
(use "Truth")
(assert "(1#2)**PosS(PosS p)==(1#2)**p*(1#2)**2")
(simprat "RatExpPosS")
(simprat "RatExpPosS")
(ng)
(use "Truth")
(assume "arithm")
(use "arithm")
(simp "RatPlusComm")
(use "RatLePlusRInv")
(simp "RatPlusComm")
(use "RatLePlusR")
(use "RatLeTrans" (pt "abs(as0 n+ ~(as0 l))"))
(simp "RatPlusComm")
(use "Truth")
(use "CauchyElim" (pt "M0"))
(use "RealConstrToCauchy")
(use "Ry")
(simp "n=")
(use "NatMaxUB1")
(use "NatLeTrans" (pt "m"))
(simp "m=")
(use "NatLeTrans" (pt "M1(PosS(PosS p))max M0(PosS(PosS p))"))
(use "NatMaxUB2")
(use "NatMaxUB1")
(use "m<=l")
;; Rational arithmetic begins
(simprat (pf "~(as0 n+ ~(as n))*(1#2**2)==
               ~(as0 n+ ~(as n))*(1#2)+(as0 n+ ~(as n))*(1#2**2)"))
(simprat (pf "(as0 n+ ~(as n))*(1#2**2)== ~(as0 n+ ~(as n))* ~(1#2**2)"))
(simp "RatPlusAssoc")
(use "RatPlusCompat")
(simprat "RatTimesPlusDistrLeft")
(simprat (pf "~(as0 n+ ~(as n))== ~(as0 n)+as n"))
(simprat "RatTimesPlusDistrLeft")
(simp "RatPlusAssoc")
(simp "RatPlusComm")
(use "RatPlusCompat")
(simprat (pf "~(as0 n)*(1#2)==(as0 n)* ~(1#2)"))
(simprat "RatEqvSym")
(use "Truth")
(simprat (pf "as0 n==as0 n*1"))
(simp "<-" "RatTimesAssoc")
(simprat "<-" "RatTimesPlusDistr")
(use "Truth")
(use "Truth")
(assert "all c,c1 ~c*c1==c* ~c1")
(assume "c" "c1")
(ng)
(use "Truth")
(assume "arithm")
(simprat "arithm")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
(assert "all c,c1 c*c1== ~c* ~c1")
(assume "c" "c1")
(use "Truth")
(assume "arithm")
(simprat "arithm")
(use "Truth")
(simprat (pf "(as0 n+ ~(as n))*(1#2**2)== ~(as0 n+ ~(as n))* ~(1#2**2)"))
(simprat "<-" "RatTimesPlusDistr")
(ng)
(use "Truth")
(assert "all c,c1 c*c1== ~c* ~c1")
(assume "c" "c1")
(use "Truth")
(assume "arithm")
(simprat "arithm")
(use "Truth")
(use "Truth")
(use "Truth")
;; done, now 2nd case
(assume "hyp")
(intro 1)
(use "RealLeIntro")
(use "Rx")
(use "Rz")
(use "RealNNegChar2RealConstrFree")
(realproof)
(assume "p0")
(intro 0 (pt "m"))
(assume "l" "m<=l")
(use "RatLeTrans" (pt "(0#1)"))
(use "Truth")
(ng)
(simp "RatPlusComm")
(use "RatLePlusR")
(ng)
(use "RatLeTrans" (pt "as n+(1#2**PosS(PosS p))"))
(use "RatLePlusR")
(simp "RatPlusComm")
(use "RatLeTrans" (pt "abs(as l+ ~(as n))"))
(use "Truth")
(use "CauchyElim" (pt "M"))
(use "RealConstrToCauchy")
(use "Rx")
(use "NatLeTrans" (pt "m"))
(simp "m=")
(use "NatMaxUB2")
(use "m<=l")
(simp "n=")
(use "NatMaxUB2")
(use "RatLeTrans" (pt "as n+(as0 n+ ~(as n))*(1#2**2)"))
(use "RatLeMonPlus")
(use "Truth")
(simprat (pf "(1#2**PosS(PosS p))==(1#2**p)*(1#2**2)"))
(use "RatLeMonTimes")
(use "Truth")
(simp "n=")
(use "y<x")
(assert "(1#2)**PosS(PosS p)==(1#2)**p*(1#2)**2")
(simprat "RatExpPosS")
(simprat "RatExpPosS")
(ng)
(use "Truth")
(assume "arithm")
(use "arithm")
(simprat (pf "as n+ (as0 n+ ~(as n))*(1#2**2)==
              (as n+as0 n)*(1#2)+ ~(as0 n+ ~(as n))*(1#2**2)"))
(use "RatLeTrans" (pt "as1 m+ ~(1#2**PosS(PosS p))"))
(use "RatLeMonPlus")
(use "RatLtToLe")
(use "RatNotLeToLt")
(use "hyp")
(simprat (pf "(1#2**PosS(PosS p))==(1#2**p)*(1#2**2)"))
(simprat (pf "~((1#2**p)*(1#2**2))== ~(1#2**p)*(1#2**2)"))
(use "RatLeMonTimes")
(use "Truth")
(simp "RatLeUMinus")
(simp "n=")
(use "y<x")
(use "Truth")
(assert "(1#2)**PosS(PosS p)==(1#2)**p*(1#2)**2")
(simprat "RatExpPosS")
(simprat "RatExpPosS")
(ng)
(use "Truth")
(assume "arithm")
(use "arithm")
(simp "RatPlusComm")
(use "RatLePlusRInv")
(simp "RatPlusComm")
(use "RatLePlusR")
(use "RatLeTrans" (pt "abs(as1 m+ ~(as1 l))"))
(simp "RatPlusComm")
(use "Truth")
(use "CauchyElim" (pt "M1"))
(use "RealConstrToCauchy")
(use "Rz")
(simp "m=")
(use "NatLeTrans" (pt "M1(PosS(PosS p))max M0(PosS(PosS p))"))
(use "NatMaxUB1")
(use "NatMaxUB1")
(use "NatLeTrans" (pt "m"))
(simp "m=")
(use "NatLeTrans" (pt "M1(PosS(PosS p))max M0(PosS(PosS p))"))
(use "NatMaxUB1")
(use "NatMaxUB1")
(use "m<=l")
;; remaining: rational arithmetic
(simprat (pf "as n+(as0 n+ ~(as n))*(1#2**2)==
              4*as n*(1#2**2)+(as0 n+ ~(as n))*(1#2**2)"))
(simprat "<-" "RatTimesPlusDistrLeft")
(simprat (pf "(as n+ as0 n)*(1#2)==2*(as n+ as0 n)*(1#2**2)"))
(simprat "<-" "RatTimesPlusDistrLeft")
(use "RatTimesCompat")
(ng)
(simp "RatPlusComm")
(simp "RatPlusAssoc")
(simprat (pf "~(as n)+4*as n==3*as n"))
(simprat (pf "2*(as n+as0 n)+ ~(as0 n)==2*as n+as0 n"))
(use "RatEqvSym")
(simp "RatPlusComm")
(simp "RatPlusAssoc")
(simprat (pf "as n+ 2*as n==3*as n"))
(use "Truth")
(simprat (pf "as n+2*as n==1*as n+2*as n"))
(simprat "<-" "RatTimesPlusDistrLeft")
(use "Truth")
(use "Truth")
(simprat "RatTimesPlusDistr")
(simp "<-" "RatPlusAssoc")
(use "RatPlusCompat")
(use "Truth")
(simprat (pf "~(as0 n)== ~1*as0 n"))
(simprat "<-" "RatTimesPlusDistrLeft")
(use "Truth")
(use "RatEqvTrans" (pt "~(1*as0 n)"))
(use "Truth")
(assert "all c,c1(~(c*c1)== ~c*c1)")
(assume "c" "c1")
(use "Truth")
(assume "arithm")
(simprat "arithm")
(use "Truth")
(simprat (pf "~(as n)== ~1*as n"))
(simprat "<-" "RatTimesPlusDistrLeft")
(use "Truth")
(use "RatEqvTrans" (pt "~(1*as n)"))
(use "Truth")
(assert "all c,c1(~(c*c1)== ~c*c1)")
(assume "c" "c1")
(use "Truth")
(assume "arithm")
(simprat "arithm")
(use "Truth")
(use "Truth")
(use "RatEqvSym")
(simp "RatTimesComm")
(simp "RatTimesAssoc")
(simprat (pf "(1#2**2)*2==(1#2)"))
(simp "RatTimesComm")
(use "Truth")
(use "Truth")
(use "RatPlusCompat")
(simp "RatTimesComm")
(simp "RatTimesAssoc")
(simprat (pf "(1#2**2)*4==1"))
(use "Truth")
(use "Truth")
(use "Truth")
;; Proof finished.
(save "ApproxSplit")
;; (cdp)

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [x,x0,x1,p]
;;  [case x
;;    (RealConstr as M -> 
;;    [case x0
;;      (RealConstr as0 M0 -> 
;;      [case x1
;;        (RealConstr as1 M1 -> 
;;        as1(M1(PosS(PosS p))max M0(PosS(PosS p))max M(PosS(PosS p)))<=
;;        (as(M0(PosS(PosS p))max M(PosS(PosS p)))+
;;         as0(M0(PosS(PosS p))max M(PosS(PosS p))))*
;;        (1#2))])])]

;; RealNNegPos
(set-goal "all p,q RealNNeg(p#q)")
(assume "p" "q")
(use "RealNNegIntro")
(use "RealRat")
(assume "p1")
(use "Truth")
;; Proof finished.
(save "RealNNegPos")

;; RealLeAbs
(set-goal "all x,y(x<<=y -> ~x<<=y -> abs x<<=y)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "x<=y" "~x<=y")
(use "RealLeIntro")
(realproof)
(realproof)
(inst-with-to "RealConstrLeElim2"
	      (pt "as") (pt "M") (pt "bs") (pt "N") "x<=y" "x<=yInst")
(inst-with-to "RealConstrLeElim2"
	      (pt "[n]~(as n)") (pt "M") (pt "bs") (pt "N") "~x<=y" "~x<=yInst")
(use "RealNNegIntro")
(realproof)
(assume "p")
(inst-with-to "RealConstrNNegElim1"
	      (pt "[n]bs n+ ~(as n)") (pt "[p]N(PosS p)max M(PosS p)")
	      "x<=yInst" (pt "p") "+Hyp")
(inst-with-to "RealConstrNNegElim1"
	      (pt "[n]bs n+ ~(([n0]~(as n0))n)")
	      (pt "[p]N(PosS p)max M(PosS p)")
	      "~x<=yInst" (pt "p") "-Hyp")
(drop "x<=yInst" "~x<=yInst")
(ng)
(use-with "RatAbsCases"
	  (make-cterm (pv "a")
		      (pf "0<=bs(N(PosS p)max M(PosS p))+ ~abs a+(1#2**p)"))
	  (pt "as(N(PosS p)max M(PosS p))") "?" "?")
(assume "+Eq")
(simp "+Eq")
(use "+Hyp")
(assume "-Eq")
(simp "-Eq")
(use "-Hyp")
;; Proof finished.
(save "RealLeAbs")

;; RealAbsTimes
(set-goal "all x,y(Real x -> Real y -> abs(x*y)===abs x*abs y)")
(assert "all x,y(Real x -> Real y -> abs(x*y)=+=abs x*abs y)")
(cases)
(assume "as" "M")
(cases)
(assume "bs" "N" "Rx" "Ry")
(use "RealEqSIntro")
(assume "n")
(ng)
(simp "RatAbsTimes")
(use "Truth")
;; Assertion proved.
(assume "RealAbsTimesEqS" "x" "y" "Rx" "Ry")
(use "RealEqSToEq")
(realproof)
(realproof)
(use "RealAbsTimesEqS")
(use "Rx")
(use "Ry")
;; Proof finished.
(save "RealAbsTimes")

;; RealAllncTotalIntro
(set-goal "allnc as,M (Pvar rea)(RealConstr as M) -> allnc x (Pvar rea)x")
(assume "asMHyp")
(use "AllncTotalIntro")
(assume "x^" "Tx")
(simp "TotalReaToEqD")
(assert "allnc as^(Total as^ --> allnc M (Pvar rea)(RealConstr as^ M))")
(use-with "AllncTotalElim" (py "nat=>rat")
 (make-cterm (pv "as^") (pf "allnc M (Pvar rea)(RealConstr as^ M)")) "?")
(use "asMHyp")
(assume "Assertion")
(inst-with-to "Assertion" (pt "x^ seq") "AssInst")
(assert "allnc M^(Total M^ --> (Pvar rea)(RealConstr x^ seq M^))")
(use-with "AllncTotalElim" (py "pos=>nat")
 (make-cterm (pv "M^") (pf "(Pvar rea)(RealConstr x^ seq M^)")) "?")
(use "AssInst")
(elim "Tx")
(assume "as^" "Tas" "M^" "TM" "n^" "Tn")
(use "Tas")
(use "Tn")
;; Assertion proved
(assume "Assertion2")
(use "Assertion2")
(elim "Tx")
(assume "as^" "Tas" "M^" "TM" "p^" "Tp")
(use "TM")
(use "Tp")
(use "Tx")
;; Proof finished.
(save "RealAllncTotalIntro")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [alpha3697]alpha3697

;; RealAllncTotalElim
(set-goal "allnc x (Pvar rea)x -> allnc as,M (Pvar rea)(RealConstr as M)")
(assume "xHyp")
(assert "allnc x^(TotalRea x^ --> (Pvar rea)x^)")
 (use "AllncTotalElim")
 (use "xHyp")
(assume "Assertion")
(use "AllncTotalIntro")
(assume "as^" "Tas")
(use "AllncTotalIntro")
(assume "M^" "TM")
(use "Assertion")
(use "TotalReaRealConstr")
(use "Tas")
(use "TM")
;; Proof finished.
(save "RealAllncTotalElim")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [alpha3697]alpha3697

