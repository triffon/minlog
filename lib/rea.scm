;; 2016-07-05.  rea.scm.  Based on numbers.scm

;; New: 

;; 2016-06-26.  rea.scm.  Based on numbers.scm.

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
(add-mr-ids "TotalRea")

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
 (py "nat=>nat")
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

;; 3. Arithmetic
;; =============

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

;; 4.  Constructive Reals
;; ======================

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

;; Properties of RealEq, RealNNeg and RealLe

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

;; We now prove further properties of RealEq, RealNNe, RealLe

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
      all p ex n1 all n(n1<=n -> abs(as n-bs n)<=(1#2**p)))")
(assume "as" "bs" "M" "N" "x=y" "p")
(ex-intro "M(PosS(PosS p))max N(PosS(PosS p))")
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

(define proof (current-proof))
(define eterm (proof-to-extracted-term proof))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [M,M0,p]M(PosS(PosS p))max M0(PosS(PosS p))

;; RealEqChar2
(set-goal "all as,M,bs,N(Real(RealConstr as M) -> Real(RealConstr bs N) ->
           all p ex n0 all n(n0<=n -> abs(as n-bs n)<=(1#2**p)) ->
           RealConstr as M===RealConstr bs N)")
(assume "as" "M" "bs" "N" "Rx" "Ry" "Est")
(use "RealEqIntro")
(use "Rx")
(use "Ry")
(ng #t)
(assume "p")
(use "RatLeAllPlusToLe")
(assume "q")
;; :abs(as(M(PosS p))+ ~(bs(N(PosS p))))<=(1#2**p)+(1#2**q)
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
(assert "ex n all n0(n<=n0 -> abs(as n0-bs n0)<=(1#2**(PosS p)))")
(use "RealEqCharOne" (pt "M") (pt "N"))
(use "x=y")
(assume "xyExHyp")
(by-assume "xyExHyp" "m" "mProp")
;; Use RealEqCharOne for y=z
(assert "ex n all n0(n<=n0 -> abs(bs n0-cs n0)<=(1#2**(PosS p)))")
(use "RealEqCharOne" (pt "N") (pt "L"))
(use "y=z")
(assume "yzExHyp")
(by-assume "yzExHyp" "l" "lProp")
;; Take m max l for n
(ex-intro "m max l")
(assume "n" "BdHyp")
(use "RatLeTrans" (pt "abs(as n-bs n)+abs(bs n-cs n)"))
(use "RatLeAbsMinus")
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

;; 2016-07-05.  Done up to this point without admit

;; RealNNegCharOne
(set-goal "allnc as all M(RealNNeg(RealConstr as M) -> 
      all p ex n1 all n(n1<=n -> ~(1#2**p)<=as n))")
(assume "as" "M" "0<=x" "p")
(ex-intro "M(PosS p)")
(assume "n" "BdHyp")
(use "RatLeTrans" (pt "~(1#2**(PosS p))+(as(M(PosS p))+ ~(as n))+as n"))
;; 5,6
(admit)
(admit)
(save "RealNNegCharOne")

(define proof (current-proof))
(define eterm (proof-to-extracted-term proof))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [M,p]M(PosS p)

;; RealNNegChar2
(set-goal "allnc as all M(Real(RealConstr as M) ->
      all p ex n1 all n(n1<=n -> ~(1#2**p)<=as n) ->
      RealNNeg(RealConstr as M))")
(assume "as" "M" "Rx" "Est")
(use "RealNNegIntro")
(use "Rx")
(ng)
;;   {as}  M  Rx:Real(RealConstr as M)
;;   Est:all p ex n all n0(n<=n0 -> (IntN 1#2**p)<=as n0)
;; -----------------------------------------------------------------------------
;; ?_5:all p 0<=as(M p)+(1#2**p)
(admit)
(save "RealNNegChar2")

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
;; Use RealNNegCharOne for 0<=x
(use "RealNNegCharOne" (pt "N"))
(admit) ;check
(save "RealNNegCompat")

;; RealPosChar1
(set-goal "allnc as all M,p(RealPos(RealConstr as M)p ->
 ex q,n1 all n(n1<=n -> (1#2**q)<=as n))")
(assume "as" "M" "p" "xPos")
(ex-intro "PosS p")
(ex-intro "M(PosS p)")
(assume "n" "BdHyp")
(admit)
(save "RealPosChar1")

(define proof (current-proof))
(define eterm (proof-to-extracted-term proof))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [M,p]PosS p@M(PosS p)

;; RealPosChar2
(set-goal "all as,M,p,q,n1(all n(n1<=n -> (1#2**q)<=as n) ->
                           RealPos(RealConstr as M)p)")
(assume "as" "M" "p" "q" "n1" "Est")
(ng)
(admit)
(save "RealPosChar2")

;; RealPosCompat
(set-goal "allnc as,M,bs,N(
     RealConstr as M===RealConstr bs N -> 
     all p((1#2**p)<=as(M(PosS p)) -> ex q (1#2**q)<=bs(N(PosS q))))")
(assume "as" "M" "bs" "N" "x=y" "p" "0<x")
(ex-intro "PosS p")
(admit)
(save "RealPosCompat")
;; (remove-theorem "RealPosCompat")

(define proof (current-proof))
(define eterm (proof-to-extracted-term proof))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; PosS

;; RealUMinusCompat
(set-goal "all x,y(x===y -> ~x=== ~y)")
(assume "x" "y" "x=y")
(admit)
(save "RealUMinusCompat")

;; RealPlusCompat
(set-goal "all x,y,z,z1(x===y -> z===z1 -> x+z===y+z1)")
(assume "x" "y" "z" "z1" "x=y" "z=z1")
(admit)
(save "RealPlusCompat")

(pp "RealEqCompat")

;; RealLeCompat
(set-goal "all x,y,z,z1(x===y -> z===z1 -> x<<=z -> y<<=z1)")
(admit)
(save "RealLeCompat")

;; RealTimesCompat
(set-goal "all x,y,z,z1(x===y -> z===z1 -> x*z===y*z1)")
(assume "x" "y" "z" "z1" "x=y" "z=z1")
(admit)
(save "RealTimesCompat")

;; RealMinusCompat
(set-goal "all x,y,z,z1(x===y -> z===z1 -> x-z===y-z1)")
(assume "x" "y" "z" "z1" "x=y" "z=z1")
(admit)
(save "RealMinusCompat")

(add-global-assumption
 "RealAbsCompat"
 "all x,y(x===y -> abs x===abs y)")

;; Generally we also need that RealAbs etc maps reals to reals

(add-global-assumption
 "RealAbsReal"
 "all x(Real x -> Real(abs x))")

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
(simp (pf "as n+ bs n+ ~(as m)+ ~(bs m)= as n+ ~(as m)+(bs n+ ~(bs m))"))
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
(admit) ;use RatPlusComm RatPlusAssoc

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

;; For the admit do something like
(set-goal "all a,b,c b+ ~a+c= ~a+(b+c)")
(assume "a" "b" "c")
(simp "<-" "RatPlusComm")
(simp "RatPlusAssoc")
(simp "RatPlusComm")
(simp (pf "c+b=b+c"))
(use "Truth")
(use "RatPlusComm")
;; Proof finished

;; Every real has an upper bound, that is the reals are Archimedian ordered.

(add-global-assumption "RatMaxUB1" "all a,b a<=a max b")
(add-global-assumption "RatMaxUB2" "all a,b b<=a max b")

;; We prove an auxiliary lemma.

;; RatSeqFinBound
(set-goal "all as,n ex a all m(m<n -> as m<=a)")
(assume "as")
(ind)
  (ex-intro "IntP One#One")
  (assume "m" "Absurd")
  (use "EfqAtom")
  (use "Absurd")
(assume "n" "IH")
(by-assume "IH" "a" "H")
(ex-intro "a max as n")
(assume "m" "m<Succ n")
(use "NatLtSuccCases" (pt "m") (pt "n"))
(use "m<Succ n")
(assume "m<n")
(use "RatLeTrans" (pt "a"))
(use-with "H" (pt "m") "m<n")
(use "RatMaxUB1")
(assume "m=n")
(simp "m=n")
(use "RatMaxUB2")
;; Proof finished.
(save "RatSeqFinBound")

;; RealBound
(set-goal "all as,M(Cauchy as M -> ex a all n as n<=a)")
(assume "as" "M" "CasM")
(cut "ex a all m(m<M 1 -> as m<=a)")
(assume "ExHyp")
(by-assume "ExHyp" "a" "FinBound")
(ex-intro "a max(as(M 1))+1")

;; ?_9:all n as n<=a max as(M 1)+1
(assume "n")
(cases (pt "n<M 1"))
(assume "n<M 1")
(use "RatLeTrans" (pt "a"))
(use "FinBound")
(use "n<M 1")
(use "RatLeTrans" (pt "a max(as(M 1))"))
(use "RatMaxUB1")
(use "Truth")

;; ?_12:(n<M 1 -> F) -> as n<=a max as(M 1)+1
(assume "n<M 1 -> F")
(use "RatLeTrans" (pt "as(M 1)+(as n+ ~(as(M 1)))"))
(assert "all b,c b<=c+(b+ ~c)")
 (assume "b" "c")
 (simp "RatPlusComm")
 (simp "<-" "RatPlusAssoc")
 (simprat (pf "~c+c==0"))
 (use "Truth")
 (use "Truth")
(assume "Assertion")
(use "Assertion")

;; ?_21:as(M 1)+(as n+ ~(as(M 1)))<=a max as(M 1)+1
(use "RatLeMonPlus")
(use "RatMaxUB2")

;; ?_23: as n-as(M 1)<=1 
(use "RatLeTrans" (pt "abs(as n+ ~(as(M 1)))"))
(use "Truth")

;; ?_33:abs(as n+ ~(as(M 1)))<=1
(use "RatLeTrans" (pt "(1#2**1)"))
(use "CauchyElim" (pt "M"))
(use "CasM")
(use "NatNotLtToLe")
(use "n<M 1 -> F")
(use "Truth")
(use "Truth")
(use "RatSeqFinBound")
;; Proof finished.
(save "RealBound")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [as,M]cRatSeqFinBound as(M 1)max as(M 1)+1

;; CauchyTimes
(set-goal "all as,M,bs,N,p1,p2(
      Cauchy as M -> 
      Cauchy bs N -> 
      Mon M -> 
      Mon N -> 
      all n abs(as n)<=2**p1 -> 
      all n abs(bs n)<=2**p2 -> 
      Cauchy([n]as n*bs n)([p]M(p+1+p2)max N(p+1+p1)))")
(assume "as" "M" "bs" "N" "p1" "p2" "CasM" "CbsN" "MonM" "MonN" "p1Bd" "p2Bd")
(use "CauchyIntro")
(assume "p" "n" "m" "nBd" "mBd")
(ng)
(simprat
 (pf "as n*bs n+ ~(as m*bs m)==as n*(bs n+ ~(bs m))+(as n+ ~(as m))*bs m"))
;; 6,7
(use "RatLeTrans" (pt "abs(as n*(bs n+ ~(bs m)))+abs((as n+ ~(as m))*bs m)"))
(use "RatLeAbsPlus")
(use "RatLeTrans" (pt "(1#2**PosS p)+(1#2**PosS p)"))
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

(pp (rename-variables
     (nt (proof-to-extracted-term (theorem-name-to-proof "RatSeqFinBound")))))
;; [as,n](Rec nat=>rat)n 1([n0,a]a max as n0)

(pp (rename-variables
     (nt (proof-to-extracted-term (theorem-name-to-proof "RealBound")))))
;; [as,M]cRatSeqFinBound as(M 1)max as(M 1)+1

;; Use cNatPos instead of the pconst NatToPos to block unwanted unfoldings

;; NatPos
(set-goal "all n ex p p=NatToPos n")
(assume "n")
(ex-intro "NatToPos n")
(use "Truth")
;; Proof finished.
(save "NatPos")
;; Rules for RealTimes.

(add-computation-rules
 "(RealConstr as M)*(RealConstr bs N)"
 "RealConstr([n]as n*bs n)
            ([p]M(p+1+cNatPos(cRatLeAbsBound(cRealBound as M)))max
                N(p+1+cNatPos(cRatLeAbsBound(cRealBound bs N))))")

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
;;   x  y  Rx:Real x
;;   Ry:Real y
;;   x22009  as  M  CasM:Cauchy as M
;;   MonM:Mon M
;;   x22015  bs  N  CbsN:Cauchy bs N
;;   MonN:Mon N
;;   p  n  m  nBd:M(PosS(p+cNatPos(cRatLeAbsBound(cRealBound as M))))max 
;;                N(PosS(p+cNatPos(cRatLeAbsBound(cRealBound bs N))))<=
;;                n
;;   mBd:M(PosS(p+cNatPos(cRatLeAbsBound(cRealBound as M))))max 
;;       N(PosS(p+cNatPos(cRatLeAbsBound(cRealBound bs N))))<=
;;       m
;; -----------------------------------------------------------------------------
;; ?_15:abs(as n*bs n+ ~(as m*bs m))<=(1#2**p)

(admit) ;use CauchyTimes
(use "MonIntro")
(assume "p" "q" "p<=q")
(ng)
;;   x  y  Rx:Real x
;;   Ry:Real y
;;   x22009  as  M  CasM:Cauchy as M
;;   MonM:Mon M
;;   x22015  bs  N  CbsN:Cauchy bs N
;;   MonN:Mon N
;;   p  q  p<=q:p<=q
;; -----------------------------------------------------------------------------
;; ?_18:M(PosS(p+cNatPos(cRatLeAbsBound(cRealBound as M))))max 
;;      N(PosS(p+cNatPos(cRatLeAbsBound(cRealBound bs N))))<=
;;      M(PosS(q+cNatPos(cRatLeAbsBound(cRealBound as M))))max 
;;      N(PosS(q+cNatPos(cRatLeAbsBound(cRealBound bs N))))

(admit) ;use MonM, MonN
(save "RealTimesReal")

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
