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

;; We introduce an inductively defined predicate RealEq x y by the
;; following clause.

(add-ids
 (list (list "RealEq" (make-arity (py "rea") (py "rea"))))
 '("all x,y(
    all p abs(x seq(x mod(PosS p))+ ~(y seq(y mod(PosS p))))<=(1#2**p) ->
    RealEq x y)" "RealEqIntro"))

;; Code discarded 2016-06-26
;; (add-ids
;;  (list (list "RealEq" (make-arity (py "rea") (py "rea"))))
;;  '("all x^,y^(
;;     all p abs(x^ seq(x^ mod(PosS p))-y^ seq(y^ mod(PosS p)))<=(1#2**p) ->
;;     RealEq x^ y^)" "RealEqIntro"))

;; (pp "RealEqIntro")

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

;; RealEqElim
(set-goal
 "all x,y(x ===y ->
          all p abs(x seq(x mod(PosS p))+ ~(y seq(y mod(PosS p))))<=(1#2**p))")
(assume "x" "y" "x=y")
(elim "x=y")
(search)
;; Proof finished.
(save "RealEqElim")

;; Code discarded 2016-06-26
;; ;; RealEqElim
;; (set-goal
;;  "all x^,y^(x^ ===y^ ->
;;           all p abs(x^ seq(x^ mod(PosS p))-y^ seq(y^ mod(PosS p)))<=(1#2**p))")
;; (assume "x^" "y^" "x=y")
;; (elim "x=y")
;; (search)
;; ;; Proof finished.
;; (save "RealEqElim")

;; The following variant will be more useful, because its head will be
;; more often of the form of a given goal.

;; RealConstrEqElim
(set-goal
 "all as,M,bs,N(RealConstr as M ===RealConstr bs N ->
                all p abs(as(M(PosS p))+ ~(bs(N(PosS p))))<=(1#2**p))")
(assume "as" "M" "bs" "N" "EqHyp" "p")
(use-with "RealEqElim"
	  (pt "RealConstr as M") (pt "RealConstr bs N") "EqHyp" (pt "p"))
;; Proof finished.
(save "RealConstrEqElim")

;; Code discarded 2016-06-26
;; ;; RealConstrEqElim
;; (set-goal
;;  "all as^,M^,bs^,N^(RealConstr as^ M^ ===RealConstr bs^ N^ ->
;;                     all p abs(as^(M^(PosS p))-bs^(N^(PosS p)))<=(1#2**p))")
;; (strip)
;; (use-with "RealEqElim"
;; 	  (pt "RealConstr as^ M^") (pt "RealConstr bs^ N^") 1 (pt "p"))
;; ;; Proof finished.
;; (save "RealConstrEqElim")

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

;; Non-negative reals are defined inductively

(add-ids
 (list (list "RealNNeg" (make-arity (py "rea"))))
 '("all x(all p 0<=x seq(x mod p)+(1#2**p) -> RealNNeg x)"
 "RealNNegIntro"))

;; Code discarded 2016-06-26
;; (add-ids
;;  (list (list "RealNNeg" (make-arity (py "rea"))))
;;  '("all x^(all p 0<=x^ seq(x^ mod p)+(1#2**p) -> RealNNeg x^)"
;;  "RealNNegIntro"))

;; RealNNegElim
(set-goal "all x(RealNNeg x -> all p 0<=x seq(x mod p)+(1#2**p))")
(assume "x" "NNegx")
(elim "NNegx")
(search)
;; Proof finished.
(save "RealNNegElim")

;; The following variant will be more useful, because its head will be
;; more often of the form of a given goal.

;; RealConstrNNegElim
(set-goal
 "all as,M(RealNNeg(RealConstr as M) -> all p 0<=as(M p)+(1#2**p))")
(assume "as" "M" "NNegHyp" "p")
(use-with "RealNNegElim" (pt "RealConstr as M") "NNegHyp" (pt "p"))
;; Proof finished.
(save "RealConstrNNegElim")

;; For reals less-than-or-equal-to is undecidable and hence must be
;; treated as an inductively defined predicate.

(add-ids
 (list (list "RealLe" (make-arity (py "rea") (py "rea"))))
 '("all x,y(RealNNeg(y+ ~x) -> RealLe x y)" "RealLeIntro"))

;; Code discarded 2016-06-26
;; (add-ids
;;  (list (list "RealLe" (make-arity (py "rea") (py "rea"))))
;;  '("all x^,y^(RealNNeg(y^ -x^) -> RealLe x^ y^)" "RealLeIntro"))

;; Notice that we cannot take <= and use overloading, because the token
;; <= has token type rel-op and hence produces a term, not a predicate.

(add-token
 "<<="
 'pred-infix
 (lambda (x y)
   (make-predicate-formula (make-idpredconst "RealLe" '() '()) x y)))

(add-idpredconst-display "RealLe" 'pred-infix "<<=")

;; RealLeElim
(set-goal "all x,y(x<<=y -> RealNNeg(y+ ~x))")
(assume "x" "y" "x<=y")
(elim "x<=y")
(search)
;; Proof finished.
(save "RealLeElim")

;; The following variant will be useful as well, when its head is of
;; the form of a given goal.

;; RealConstrLeElim
(set-goal "all as,M,bs,N(
 RealConstr as M <<=RealConstr bs N ->
 RealNNeg(RealConstr([n]bs n+ ~(as n))([p]N(PosS p)max M(PosS p))))")
(assume "as" "M" "bs" "N" "LeHyp")
(use-with "RealLeElim" (pt "RealConstr as M") (pt "RealConstr bs N") "LeHyp")
;; Proof finished.
(save "RealConstrLeElim")

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

;; Code discarded 2016-06-26
;; (add-ids
;;  (list (list "Cauchy" (make-arity (py "nat=>rat") (py "pos=>nat"))))
;;  '("all as^,M(
;;     all p,n,m(M p<=n -> M p<=m -> abs(as^ n-as^ m)<=(1#2**p)) -> Cauchy as^ M)"
;;    "CauchyIntro"))

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

;; RealToCauchySeq"
(set-goal "all x(Real x -> Cauchy(x seq)(x mod))")
(assume "x")
(elim)
(auto)
;; Proof finished.
(save "RealToCauchySeq")

;; RealToMonMod
(set-goal "all x(Real x -> Mon(x mod))")
(assume "x")
(elim)
(auto)
;; Proof finished.
(save "RealToMonMod")

;; The following variants will be more useful, because their heads will
;; be more often of the form of a given goal.

;; RealConstrToCauchy
(set-goal "all as,M(Real(RealConstr as M) -> Cauchy as M)")
(strip)
(use-with "RealToCauchySeq" (pt "RealConstr as M") 1)
;; Proof finished.
(save "RealConstrToCauchy")

;; RealConstrToMon
(set-goal "all as,M(Real(RealConstr as M) -> Mon M)")
(strip)
(use-with "RealToMonMod" (pt "RealConstr as M") 1)
;; Proof finished.
(save "RealConstrToMon")

;; RealEqRefl
(set-goal "all as,M RealConstr as M===RealConstr as M")
(assume "as" "M")
(intro 0)
(assume "p")
(ng)
(simprat (pf "as(M(PosS p))+ ~(as(M(PosS p)))==0"))
(use "Truth")
(use "Truth")
;; Proof finished.
(save "RealEqRefl")

;; RealEqSym
(set-goal "all as,M,bs,N(RealConstr as M===RealConstr bs N ->
                         RealConstr bs N===RealConstr as M)")
(assume "as" "M" "bs" "N" "x=y")
(intro 0)
(assume "p")
(ng)
(simp "<-" "RatAbs0RewRule")
(ng)
(simp "RatPlusComm")
(use "RealConstrEqElim")
(use "x=y")
;; Proof finished.
(save "RealEqSym")

;; Code discarded 2016-06-26
;; ;; RealEqRefl
;; (set-goal "all x x===x")
;; (cases)
;; (assume "as" "M")
;; (intro 0)
;; (assume "p")
;; (ng)
;; (simprat (pf "as(M(PosS p))+ ~(as(M(PosS p)))==0"))
;; (use "Truth")
;; (use "Truth")
;; ;; Proof finished.
;; (save "RealEqRefl")

;; ;; RealEqSym
;; (set-goal "all x,y(x===y -> y===x)")
;; (cases)
;; (assume "as" "M")
;; (cases)
;; (assume "bs" "N" "x=y")
;; (intro 0)
;; (assume "p")
;; (ng)
;; (simp "<-" "RatAbs0RewRule")
;; (ng)
;; (simp "RatPlusComm")
;; (use "RealConstrEqElim")
;; (use "x=y")
;; ;; Proof finished.
;; (save "RealEqSym")

;; To prove transitivity of equality, we need a characterization of
;; equality.

;; RealEqChar1
(set-goal "allnc as all M(Cauchy as M ->  allnc bs all N(Cauchy bs N ->
      RealConstr as M===RealConstr bs N -> 
      all p ex n1 all n(n1<=n -> abs(as n-bs n)<=(1#2**p))))")
(assume "as" "M" "CasM" "bs" "N" "CbsN" "x=y" "p")
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
;; 17-19
(use "CauchyElim" (pt "M"))
(use "CasM")
(use "NatLeTrans" (pt "(M(PosS(PosS p)))max(N(PosS(PosS p)))"))
(use "NatMaxUB1")
(use "BdHyp")
(use "Truth")
;; 18
(use "RealConstrEqElim")
(use "x=y")
;; 19
(use "CauchyElim" (pt "N"))
(use "CbsN")
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
(save "RealEqChar1")

(define proof (current-proof))
(define eterm (proof-to-extracted-term proof))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [M,M0,p]M(PosS(PosS p))max M0(PosS(PosS p))

;; RealEqChar2
(set-goal "all as,M(Cauchy as M -> all bs,N(Cauchy bs N ->
           all p ex n0 all n(n0<=n -> abs(as n-bs n)<=(1#2**p)) ->
           RealConstr as M===RealConstr bs N))")
(assume "as" "M" "CasM" "bs" "N" "CbsN" "Est")
(use "RealEqIntro")
(ng #t)
(assume "p")
(use "RatLeAllPlusToLe")
(assume "q")
;; ?_7:abs(as(M(PosS p))+ ~(bs(N(PosS p))))<=(1#2**p)+(1#2**q)
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
;; 39-41
(drop "RatLeMonPlus3")
(use "CauchyElim" (pt "M"))
(use "CasM")
(use "Truth")
(simp "nDef")
(use "NatLeTrans" (pt "M(PosS p)max N(PosS p)"))
(use "NatMaxUB1")
(use "NatMaxUB1")
;; 40
(use "n0Prop")
(simp "nDef")
(use "NatMaxUB2")
;; 41
(use "CauchyElim" (pt "N"))
(use "CbsN")
(simp "nDef")
(use "NatLeTrans" (pt "M(PosS p)max N(PosS p)"))
(use "NatMaxUB2")
(use "NatMaxUB1")
(use "Truth")
;; 30 (1#2**PosS p)+(1#2**q)+(1#2**PosS p)<=(1#2**p)+(1#2**q)
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
(set-goal "all as,M(
 Cauchy as M -> all bs,N(Cauchy bs N -> all cs,L(Cauchy cs L ->
 RealConstr as M===RealConstr bs N ->
 RealConstr bs N===RealConstr cs L ->
 RealConstr as M===RealConstr cs L)))")
(assume "as" "M" "CasM" "bs" "N" "CbsN" "cs" "L" "CcsL" "x=y" "y=z")
(use "RealEqChar2")
(use "CasM")
(use "CcsL")
(assume "p")
;; Use RealEqChar1 for x=y
(assert "ex n all n0(n<=n0 -> abs(as n0-bs n0)<=(1#2**(PosS p)))")
(use "RealEqChar1" (pt "M") (pt "N"))
(use "CasM")
(use "CbsN")
(use "x=y")
(assume "xyExHyp")
(by-assume "xyExHyp" "m" "mProp")
;; Use RealEqChar1 for y=z
(assert "ex n all n0(n<=n0 -> abs(bs n0-cs n0)<=(1#2**(PosS p)))")
(use "RealEqChar1" (pt "N") (pt "L"))
(use "CbsN")
(use "CcsL")
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
(set-goal "all as,M(Cauchy as M -> all bs,N(Cauchy bs N ->
 all cs,L(Cauchy cs L -> all cs1,L1(Cauchy cs1 L1 ->
 RealConstr as M===RealConstr bs N ->
 RealConstr cs L===RealConstr cs1 L1 ->
 RealConstr as M===RealConstr cs L ->
 RealConstr bs N===RealConstr cs1 L1))))")
(assume "as" "M" "CasM" "bs" "N" "CbsN" "cs" "L" "CcsL" "cs1" "L1" "Ccs1L1"
	"x=y" "z=z1" "x=z")
(use "RealEqTrans" (pt "as") (pt "M"))
(use "CbsN")
(use "CasM")
(use "Ccs1L1")
(use "RealEqSym")
(use "x=y")
(use "RealEqTrans" (pt "cs") (pt "L"))
(use "CasM")
(use "CcsL")
(use "Ccs1L1")
(use "x=z")
(use "z=z1")
;; Proof finished.
(save "RealEqCompat")

;; Code discarded 2016-06-26
;; ;; RealEqTrans
;; (set-goal "all x(Real x -> all y(Real y -> all z(Real z ->
;;            x===y -> y===z -> x===z)))")
;; (cases)
;; (assume "as" "M" "Rx")
;; (cases)
;; (assume "bs" "N" "Ry")
;; (cases)
;; (assume "cs" "L" "Rz" "x=y" "y=z")
;; (use "RealEqChar2")
;; (use "RealConstrToCauchy")
;; (use "Rx")
;; (use "RealConstrToCauchy")
;; (use "Rz")
;; (assume "p")
;; ;; Use RealEqChar1 for x=y
;; (assert "ex n all n0(n<=n0 -> abs(as n0-bs n0)<=(1#2**(PosS p)))")
;; (use "RealEqChar1" (pt "M") (pt "N"))
;; (use "RealConstrToCauchy")
;; (use "Rx")
;; (use "RealConstrToCauchy")
;; (use "Ry")
;; (use "x=y")
;; (assume "xyExHyp")
;; (by-assume "xyExHyp" "m" "mProp")
;; ;; Use RealEqChar1 for y=z
;; (assert "ex n all n0(n<=n0 -> abs(bs n0-cs n0)<=(1#2**(PosS p)))")
;; (use "RealEqChar1" (pt "N") (pt "L"))
;; (use "RealConstrToCauchy")
;; (use "Ry")
;; (use "RealConstrToCauchy")
;; (use "Rz")
;; (use "y=z")
;; (assume "yzExHyp")
;; (by-assume "yzExHyp" "l" "lProp")
;; ;; Take m max l for n
;; (ex-intro "m max l")
;; (assume "n" "BdHyp")
;; (use "RatLeTrans" (pt "abs(as n-bs n)+abs(bs n-cs n)"))
;; (use "RatLeAbsMinus")
;; (simprat "<-" "RatPlusHalfExpPosS")
;; (use "RatLeMonPlus")
;; (use "mProp")
;; (use "NatLeTrans" (pt "m max l"))
;; (use "NatMaxUB1")
;; (use "BdHyp")
;; (use "lProp")
;; (use "NatLeTrans" (pt "m max l"))
;; (use "NatMaxUB2")
;; (use "BdHyp")
;; ;; Proof finished.
;; (save "RealEqTrans")

;; ;; RealEqCompat
;; (set-goal "all x(Real x -> all y(Real y -> all z(Real z -> all z1(Real z1 ->
;;                  x===y -> z===z1 -> x===z -> y===z1))))")
;; (cases)
;; (assume "as" "M" "Rx")
;; (cases)
;; (assume "bs" "N" "Ry")
;; (cases)
;; (assume "cs" "L" "Rz")
;; (cases)
;; (assume "cs1" "L1" "Rz1" "x=y" "z=z1" "x=z")
;; (use "RealEqTrans" (pt "RealConstr as M"))
;; (use "Ry")
;; (use "Rx")
;; (use "Rz1")
;; (use "RealEqSym")
;; (use "x=y")
;; (use "RealEqTrans" (pt "RealConstr cs L"))
;; (use "Rx")
;; (use "Rz")
;; (use "Rz1")
;; (use "x=z")
;; (use "z=z1")
;; ;; Proof finished.
;; (save "RealEqCompat")

;; RealNNegChar1
(set-goal "allnc as all M(Cauchy as M ->
      RealNNeg(RealConstr as M) -> 
      all p ex n1 all n(n1<=n -> ~(1#2**p)<=as n))")
(assume "as" "M" "CasM" "0<=x" "p")
(ex-intro "M(PosS p)")
(assume "n" "BdHyp")
(use "RatLeTrans" (pt "~(1#2**(PosS p))+(as(M(PosS p))+ ~(as n))+as n"))
;; 5,6
(admit)
(admit)
(save "RealNNegChar1")

(define proof (current-proof))
(define eterm (proof-to-extracted-term proof))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [M,p]M(PosS p)

;; RealNNegChar2
(set-goal "allnc as all M(Cauchy as M ->
      all p ex n1 all n(n1<=n -> ~(1#2**p)<=as n) ->
      RealNNeg(RealConstr as M))")
(assume "as" "M" "CasM" "Est")
(use "RealNNegIntro")
(ng)
;;   {as}  M  CasM:Cauchy as M
;;   Est:all p ex n all n0(n<=n0 -> (IntN 1#2**p)<=as n0)
;; -----------------------------------------------------------------------------
;; ?_4:all p 0<=as(M p)+(1#2**p)
(admit)
(save "RealNNegChar2")

;; RealNNegCompat
(set-goal "all as,M(Cauchy as M -> all bs,N(Cauchy bs N ->
 RealConstr as M===RealConstr bs N ->
 RealNNeg(RealConstr as M) -> RealNNeg(RealConstr bs N)))")
(assume "as" "M" "CasM" "bs" "N" "CbsN" "x=y" "0<=x")
(use "RealNNegChar2")
(use "CbsN")
(assume "p")
;; Use RealNNegChar1 for 0<=x
(use "RealNNegChar1" (pt "N"))
(use "CbsN")
(admit)
(save "RealNNegCompat")

;; ;; RealNNegCompat
;; (set-goal "all x(Real x -> all y(Real y -> x===y -> RealNNeg x -> RealNNeg y))")
;; (cases)
;; (assume "as" "M" "Rx")
;; (cases)
;; (assume "bs" "N" "Ry" "x=y" "0<=x")
;; (use "RealNNegChar2")
;; (use "RealConstrToCauchy")
;; (use "Ry")
;; (assume "p")
;; ;; Use RealNNegChar1 for 0<=x
;; (use "RealNNegChar1" (pt "N"))
;; (use "RealConstrToCauchy")
;; (use "Ry")
;; (admit)
;; (save "RealNNegCompat")

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

;; Code discarded 2016-06-26
;; ;; RealPosChar1
;; (set-goal "all as,M,p(RealPos(RealConstr as M)p ->
;;                       ex q,n1 all n(n1<=n -> (1#2**q)<=as n))")
;; (assume "as" "M" "p" "xPos")
;; (ex-intro "PosS p")
;; (ex-intro "M(PosS p)")
;; (assume "n" "BdHyp")
;; (admit)
;; (save "RealPosChar1")

;; (define proof (current-proof))
;; (define eterm (proof-to-extracted-term proof))
;; (define neterm (rename-variables (nt eterm)))
;; (pp neterm)
;; ;; [as,M,p]PosS p@M(PosS p)

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

;; Code discarded 2016-06-26
;; (set-goal "allnc as,M,bs,N(
;;      RealConstr as M===RealConstr bs N -> 
;;      all p((1#2**p)<=as(M(PosS p)) -> ex q (1#2**q)<=bs(N(PosS q))))")
;; (assume "as" "M" "bs" "N" "x=y" "p" "0<x")
;; (ex-intro "PosS p")
;; (admit)
;; (save "RealPosCompatAux")
;; ;; (remove-theorem "RealPosCompat")

;; (define proof (current-proof))
;; (define eterm (proof-to-extracted-term proof))
;; (define neterm (rename-variables (nt eterm)))
;; (pp neterm)
;; ;; PosS

;; ;; RealPosCompat
;; (set-goal "all x(Real x -> all y(Real y -> x===y ->
;;                  all p(RealPos x p -> ex q RealPos y q)))")
;; (cases)
;; (assume "as" "M" "Rx")
;; (cases)
;; (assume "bs" "N" "Ry" "x=y" "p" "0<x")
;; (ex-intro "PosS p")
;; (admit)
;; (save "RealPosCompat")

;; (define proof (current-proof))
;; (define eterm (proof-to-extracted-term proof))
;; (define neterm (rename-variables (nt eterm)))
;; (pp neterm)
;; ;; [x,x0]PosS

;; RealUMinusCompat
(set-goal "all as,M,bs,N(
     RealConstr as M===RealConstr bs N -> 
     RealConstr([n]~(as n))M===RealConstr([n]~(bs n))N)")
(assume "as" "M" "bs" "N" "x=y")
(admit)
(save "RealUMinusCompat")

;; RealPlusCompat
(set-goal "all as,M(Cauchy as M -> all bs,N(Cauchy bs N ->
 all cs,L(Cauchy cs L -> all cs1,L1(Cauchy cs1 L1 ->
 RealConstr as M===RealConstr bs N ->
 RealConstr cs L===RealConstr cs1 L1 ->
 RealConstr([n]as n+cs n)([p]M(PosS p)max L(PosS p))===
 RealConstr([n]bs n+cs1 n)([p]N(PosS p)max L1(PosS p))))))")
(assume "as" "M" "CasM" "bs" "N" "CbsN" "cs" "L" "CcsL" "cs1" "L1" "Ccs1L1"
	"x=y" "z=z1")
(admit)
(save "RealPlusCompat")

;; RealLeCompat
(set-goal "all as,M(Cauchy as M -> all bs,N(Cauchy bs N ->
 all cs,L(Cauchy cs L -> all cs1,L1(Cauchy cs1 L1 ->
 RealConstr as M===RealConstr bs N ->
 RealConstr cs L===RealConstr cs1 L1 ->
 RealLe(RealConstr as M)(RealConstr cs L) ->
 RealLe(RealConstr bs N)(RealConstr cs1 L1)))))")
(assume "as" "M" "CasM" "bs" "N" "CbsN" "cs" "L" "CcsL" "cs1" "L1" "Ccs1L1"
	"x=y" "z=z1" "x<=z")
(intro 0)
(ng)
(elim "x<=z")
(cases)
(assume "as1" "M1")
(cases)
(assume "bs1" "N1")
(admit)
(save "RealLeCompat")

;; Code discarded 2016-06-26
;; ;; RealPlusCompat
;; (set-goal "all x,y,z,z1(x===y -> z===z1 -> x+z===y+z1)")
;; (assume "x" "y" "z" "z1" "x=y" "z=z1")
;; (admit)
;; (save "RealPlusCompat")

;; ;; RealTimesCompat
;; (set-goal "all x,y,z,z1(x===y -> z===z1 -> x*z===y*z1)")
;; (assume "x" "y" "z" "z1" "x=y" "z=z1")
;; (admit)
;; (save "RealTimesCompat")

;; ;; RealUMinusCompat
;; (set-goal "all x,y(x===y -> ~x=== ~y)")
;; (assume "x" "y" "x=y")
;; (admit)
;; (save "RealUMinusCompat")

;; ;; RealMinusCompat
;; (set-goal "all x,y,z,z1(x===y -> z===z1 -> x-z===y-z1)")
;; (assume "x" "y" "z" "z1" "x=y" "z=z1")
;; (admit)
;; (save "RealMinusCompat")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ;; 2016-04-17.  Attempt to include the essential parts of the former
;; ;; lib/real.scm but avoiding global assumptions and simpreal.  The
;; ;; order follows semws15/constr15.pdf

;; (set-goal "all x,y(Real x -> Real y -> x+y===y+x)")
;; (strip)
;; (ord-field-simp-bwd)
;; (use 1)
;; (use 2)

;; ;; Attempt to avoid ord-field-simp-bwd
;; (set-goal "all x,y(Real x -> Real y -> x+y===y+x)")
;; (assume "x" "y" "Rx" "Ry")
;; (use "RealEqIntro")
;; (assume "k")
;; (elim "Rx")
;; (assume "x1" "Cx1" "Mx1")
;; (elim "Ry")
;; (assume "y1" "Cy1" "My1")
;; (elim "Cx1")
;; (assume "as^" "M" "MProp")
;; (elim "My1")
;; (assume "M1" "M1Prop")
;; ;; etc

;; ;; as^ should be avoided, take as instead

;; ;; Maybe better to have a new file real.scm, where simpreal is
;; ;; available.

;; ;; 2016-04-17.  Prove axioms of an ordered field for rea, with RealEq
;; ;; === as equality.  Define RealUDiv.
