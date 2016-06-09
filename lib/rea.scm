;; 2016-05-01.  rea.scm.  Based on numbers.scm.

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

(add-alg "rea" (list "RealConstr" "(nat=>rat)=>(nat=>nat)=>rea"))
(add-totality "rea")
(add-mr-ids "TotalRea")

(add-var-name "as" "bs" "cs" "ds" (py "nat=>rat"))
(add-var-name "M" "N" (py "nat=>nat"))
(add-var-name "x" "y" (py "rea"))

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

(add-program-constant "RealMod" (py "rea=>nat=>nat") t-deg-zero 'const 1)

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
;; (pp (pt "x mod l"))

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
(add-program-constant "RealMinus" (py "rea=>rea=>rea"))
(add-program-constant "RealTimes" (py "rea=>rea=>rea"))
(add-program-constant "RealDiv" (py "rea=>rea=>rea"))
(add-program-constant "RealAbs" (py "rea=>rea"))
(add-program-constant "RealExp" (py "rea=>int=>rea"))
(add-program-constant "RealMax" (py "rea=>rea=>rea"))
(add-program-constant "RealMin" (py "rea=>rea=>rea"))

(add-token-and-type-to-name "+" (py "rea") "RealPlus")
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

;; (pp (pt "(IntN p#q)+RealConstr([n]1)([k]7)"))

;; We introduce an inductively defined predicate RealEq x y by the
;; following clause.

;; (pp (pt "abs(x seq(x mod(IntS k))-y seq(y mod(IntS k)))"))

;; ;; (pp (pt "1#2**k"))
;; ;; (ppn (pt "(1#2)**k"))
;; ;; (pp (pt "1/2**k"))
;; ;; (ppn (pt "1/2**k"))
;; (pp (pt "eps k"))

;; 2016-04-28.  Experiments with eps.  Goal: convenient estimates

;; (set-goal "all k eps(IntS k)+eps(IntS k)==eps k")
;; (assume "k")
;; (ng) ;no change

;; (set-goal "all k (1#2)**IntS k+(1#2)**IntS k==(1#2)**k")
;; (assume "k")
;; (ng) ;no change

;; (display-pconst "RatExp" "IntExp" "PosExp")
;; ;; no rewrite rules for RatExp

;; (ppn (pt "p**n"))
;; (ppn (pt "k**n"))
;; (ppn (pt "a**n"))

;; > (p PosExp n)
;; > (k IntExp n)
;; > (a RatExp (NatToInt n))

;; (pp (pf "abs(x seq(x mod(IntS k))-y seq(y mod(IntS k))) <= 1/2**k"))

(add-ids
 (list (list "RealEq" (make-arity (py "rea") (py "rea"))))
 '("all x^,y^(
    all k abs(x^ seq(x^ mod(IntS k))-y^ seq(y^ mod(IntS k)))<=1/2**k ->
    RealEq x^ y^)" "RealEqIntro"))

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
 "all x^,y^(x^ ===y^ ->
          all k abs(x^ seq(x^ mod(IntS k))-y^ seq(y^ mod(IntS k)))<=1/2**k)")
(assume "x^" "y^" "x=y")
(elim "x=y")
(search)
;; Proof finished.
(save "RealEqElim")

;; The following variant will be more useful, because its head will be
;; more often of the form of a given goal.

;; RealEqElimVariant
(set-goal
 "all as^,M^,bs^,N^(RealConstr as^ M^ ===RealConstr bs^ N^ ->
                    all k abs(as^(M^(IntS k))-bs^(N^(IntS k)))<=1/2**k)")
(strip)
(use-with "RealEqElim"
	  (pt "RealConstr as^ M^") (pt "RealConstr bs^ N^") 1 (pt "k"))
;; Proof finished.
(save "RealEqElimVariant")

;; RealPos is a decidable property and hence can be considered as a
;; program constant.

(add-program-constant "RealPos" (py "rea=>int=>boole"))

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

(add-computation-rules "RealPos(RealConstr as M)k" "1/2**k<=as(M(k+1))")

;; RealPosTotal
(set-totality-goal "RealPos")
(use "AllTotalElim")
(cases)
(assume "as" "M")
(use "AllTotalElim")
(assume "k")
(ng)
(use "BooleTotalVar")
;; Proof finished.
(save-totality)

;; RealLt is a decidable property and hence can be considered as a
;; program constant.

(add-program-constant "RealLt" (py "rea=>rea=>int=>boole"))

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
 "RealLt(RealConstr as M)(RealConstr bs N)k"
 "RealPos(RealConstr bs N-RealConstr as M)k")

;; Rules for RealMinus

(add-computation-rules
 "RealConstr as M-RealConstr bs N"
 "RealConstr([n]as n-bs n)([k]M(k+1)max N(k+1))")

;; RealMinusTotal
(set-totality-goal "RealMinus")
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

;; RealLtTotal
(set-totality-goal "RealLt")
(use "AllTotalElim")
(cases)
(assume "as" "M")
(use "AllTotalElim")
(cases)
(assume "bs" "N")
(use "AllTotalElim")
(assume "k")
(ng)
(use "BooleTotalVar")
;; Proof finished.
(save-totality)

;; Non-negative reals are defined inductively

(add-ids
 (list (list "RealNNeg" (make-arity (py "rea"))))
 '("all x^(all k 0<=x^ seq(x^ mod k)+1/2**k -> RealNNeg x^)"
 "RealNNegIntro"))

;; RealNNegElim
(set-goal "all x^(RealNNeg x^ -> all k 0<=x^ seq(x^ mod k)+1/2**k)")
(assume "x^" "NNegx")
(elim "NNegx")
(search)
;; Proof finished.
(save "RealNNegElim")

;; The following variant will be more useful, because its head will be
;; more often of the form of a given goal.

;; RealNNegElimVariant
(set-goal
 "all as^,M^(RealNNeg(RealConstr as^ M^) -> all k 0<=as^(M^ k)+1/2**k)")
(strip)
(use-with "RealNNegElim" (pt "RealConstr as^ M^") 1 (pt "k"))
;; Proof finished.
(save "RealNNegElimVariant")

;; For reals less-than-or-equal-to is undecidable and hence must be
;; treated as an inductively defined predicate.

(add-ids
 (list (list "RealLe" (make-arity (py "rea") (py "rea"))))
 '("all x^,y^(RealNNeg(y^ -x^) -> RealLe x^ y^)" "RealLeIntro"))

;; Notice that we cannot take <= and use overloading, because the token
;; <= has token type rel-op and hence produces a term, not a predicate.

(add-token
 "<<="
 'pred-infix
 (lambda (x y)
   (make-predicate-formula (make-idpredconst "RealLe" '() '()) x y)))

(add-idpredconst-display "RealLe" 'pred-infix "<<=")

;; RealLeElim
(set-goal "all x^,y^(x^ <<=y^ -> RealNNeg(y^ -x^))")
(assume "x^" "y^" "x<=y")
(elim "x<=y")
(search)
;; Proof finished.
(save "RealLeElim")

;; The following variant will be useful as well, when its head is of
;; the form of a given goal.

(set-goal "all as^,M^,bs^,N^(
 RealConstr as^ M^ <<=RealConstr bs^ N^ ->
 RealNNeg(RealConstr([n]bs^ n-as^ n)([k]N^(k+1)max M^(k+1))))")
(strip)
(use-with "RealLeElim" (pt "RealConstr as^ M^") (pt "RealConstr bs^ N^") 1)
;; Proof finished.
(save "RealLeElimVariant")

;; 3. Arithmetic
;; =============

;; Rules for RealPlus

(add-computation-rules
 "RealConstr as M+RealConstr bs N"
 "RealConstr([n]as n+bs n)([k]M(k+1)max N(k+1))")

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

(add-program-constant "RealInv" (py "rea=>int=>rea"))

(add-computation-rules
 "RealInv(RealConstr as M)j"
 "RealConstr([n]1/as n)([k]M(2*IntS j+k)max M(IntS j))")

;; RealInvTotal
(set-totality-goal "RealInv")
(use "AllTotalElim")
(cases)
(assume "as" "M")
(use "AllTotalElim")
(assume "k")
(ng)
(use "ReaTotalVar")
;; Proof finished.
(save-totality)

;; Rules for RealExp : rea=>int=>rea

(add-computation-rules
 "x**(IntP One)" "x"
 "x**(IntP(SZero p))" "(x**(IntP p))*(x**(IntP p))"
 "x**(IntP(SOne p))" "(x**(IntP(SZero p)))*x"
 "x**IntZero" "RealConstr([n](RatConstr(IntPos One)One))([k]Zero)")

;; 4.  Constructive Reals
;; ======================

;; To work with reals, we use a predicate constant Cauchy which takes
;; two arguments, a sequence of rationals and a modulus.

;; We introduce Cauchy as an inductively defined predicate (which may
;; in this case also be called a record).

(add-ids
 (list (list "Cauchy" (make-arity (py "nat=>rat") (py "int=>nat"))))
 '("all as^,M(
    all k,n,m(M k<=n -> M k<=m -> abs(as^ n-as^ m)<=1/2**k) -> Cauchy as^ M)"
   "CauchyIntro"))

;; Similarly, we introduce a predicate constant Mon, taking a sequence
;; of positive numbers as argument, to express monotonicity.

(add-ids (list (list "Mon" (make-arity (py "int=>nat"))))
	 '("all M(all k,j(k<=j -> M k<=M j) -> Mon M)" "MonIntro"))

;; "CauchyElim"
(set-goal
 "all as^,M(Cauchy as^ M ->
            all k,n,m(M k<=n -> M k<=m -> abs(as^ n-as^ m)<=1/2**k))")
(assume "as^" "M")
(elim)
(search)
;; Proof finished.
(save "CauchyElim")

;; "MonElim"
(set-goal "all M(Mon M -> all k,j(k<=j -> M k<=M j))")
(assume "M")
(elim)
(search)
;; Proof finished.
(save "MonElim")

;; We introduce Real as an inductively defined predicate (which in this
;; case may also be called a record).  Then we can prove theorems:

;; RealIntro: all x(Cauchy(x seq)(x mod) -> Mon(x mod) -> Real x)
;; RealElim1: all as,M(Real(RealConstr as M) -> Cauchy as M)
;; RealElim2: all as,M(Real(RealConstr as M) -> Mon M)

;; Alternative formulation (worse, since usability is restricted)
;; RealIntro: all as,M(Cauchy as M -> Mon M -> Real RealConstr as M) 
;; RealElim1: all x(Real x -> Cauchy(x seq)(x mod))
;; RealElim2: all x(Real x -> Mon(x mod))

(add-ids
 (list (list "Real" (make-arity (py "rea"))))
 '("all x(Cauchy(x seq)(x mod) -> Mon(x mod) -> Real x)" "RealIntro"))

;; RealElim1"
(set-goal "all x(Real x -> Cauchy(x seq)(x mod))")
(assume "x")
(elim)
(auto)
;; Proof finished.
(save "RealElim1")

;; "RealElim2"
(set-goal "all x(Real x -> Mon(x mod))")
(assume "x")
(elim)
(auto)
;; Proof finished.
(save "RealElim2")

;; The following variants will be more useful, because their heads will
;; be more often of the form of a given goal.

;; "RealElimVariant1"
(set-goal "all as,M(Real(RealConstr as M) -> Cauchy as M)")
(strip)
(use-with "RealElim1" (pt "RealConstr as M") 1)
;; Proof finished.
(save "RealElimVariant1")

;; "RealElimVariant2"
(set-goal "all as,M(Real(RealConstr as M) -> Mon M)")
(strip)
(use-with "RealElim2" (pt "RealConstr as M") 1)
;; Proof finished.
(save "RealElimVariant2")

;; To prove transitivity of equality, we need a characterization of
;; equality.

;; RealEqChar1
(set-goal "all as,M,bs,N(Cauchy as M -> Cauchy bs N ->
      RealConstr as M===RealConstr bs N -> 
      all k ex n1 all n(n1<=n -> abs(as n-bs n)<=1/2**k))")
(assume "as" "M" "bs" "N" "CasM" "CbsN" "x=y" "k")
(ex-intro "M(IntS(IntS k))max N(IntS(IntS k))")
(assume "n" "BdHyp")
(use "RatLeTrans" (pt "1/2**(IntS(IntS k))+1/2**(IntS k)+1/2**(IntS(IntS k))"))
(use "RatLeTrans" (pt "abs(as n-as(M(IntS(IntS k))))+
                       abs(as(M(IntS(IntS k)))-bs(N(IntS(IntS k))))+
                       abs(bs(N(IntS(IntS k)))-bs n)"))

(search-about "Rat" "Abs")
(display-pconst "RatAbs")
(display-pconst "RatMinus" "RatPlus")
(display-pconst "PosPlus")
(search-about "Pos" "Plus")
(search-about "Int" "Abs")
;; RatLeAbsPlus
;; all a,b abs(a+b)<=abs a+abs b
(display-pconst "IntAbs")

(ppn (pt "M(k+2)max N(k+2)"))

;; (set-goal "all r 0**r=0")
;; (assume "r")
;; (use "PosLeLtCases" (pt "r") (pt "1"))
;; (ng)
;; (assume "r=1")
;; (simp "r=1")
;; (use "Truth")
;; (assume "1<r")
;; (simp "SuccPosPred")

(search-about "Pos" "Le" "Not")
(search-about "Pos" "Log")

;; Better: prove and use this for positive k only
(set-goal "all k (1#2)**(k+1)+(1#2)**(k+1)==(1#2)**k")
;; Using all a,r a**PosS r==a**r*a and all a,r a**IntN r==(a**IntN 1)**r
;; we prove a**(k+1)+a**(k+1)==a**k for a := (1#2).
(cases)
(assume "r")
(assert "IntP r+1=PosS r")
 (use "Truth")
(assume "IntP r+1=PosS r")
(simp "IntP r+1=PosS r")
(drop "IntP r+1=PosS r")
(simprat "RatExpPosS")
(simprat "<-" "RatTimesPlusDistr")
(ng)
(use "Truth")
;; 3
(use "Truth")
;; 4
(assume "r")
(use "PosLeLtCases" (pt "r") (pt "1"))
(ng)
(assume "r=1")
(simp "r=1")
(ng)
(simp "r=1")
(use "Truth")
(assume "1<r")

;; Need
(set-goal "all r (2#1)**PosPred r+(2#1)**PosPred r==2**r")
(ng)

(set-goal "all r (2#1)**r+(2#1)**r==2**PosS r")
(ng)
(assume "r")
(use "PosLeLtCases" (pt "r") (pt "1"))
(ng)
(assume "r=1")
(simp "r=1")
(use "Truth")
(assume "1<r")
(simp "SuccPosPred")
(ng)(undo)

(ppn "SuccPosPred")

(ppn (goal-to-formula (current-goal)))
(ppn (pt "a**PosS r"))
(display-pconst "RatExp")
(display-pconst "IntExp")
(display-pconst "PosExp")
(ppn (pt "(1#2)**(k+1)"))
(ppn (pt "(1#2)**IntS k"))
(display-pconst "IntPlus" "IntS" "IntPred")
(search-about "Nat" "Int")
(ppn "PosToNatToIntId")
(display-pconst "NatToInt")
(search-about "Nat" "Pos" "Id")
(display-pconst "PosPred")
(search-about "PosPred")
(display-pconst "IntUMinus")
(ppn "RatExp4CompRule")

;; First
;; RatExpPosS
(set-goal "all a,r a**PosS r==a**r*a")
(assert "all a,r a**PosToNat(PosS r)==a**PosToNat r*a")
(cases)
(cases)
;; 3-5
(assume "p" "q" "r")
(simp "SuccPosPred")
(simp "<-" "IntPNatToPosEqNatToInt")
(simp "RatExp0CompRule")
(simp "<-" "IntPNatToPosEqNatToInt")
(simp "PosToNatToPosId")
(simp "PosPred0RewRule")
(simp "NatToPosToNatId")
(use "Truth")
(use "Truth")
(use "NatLt0Pos")
(use "Truth")
(use "Truth")
;; 4
(assume "p" "r")
(simp "<-" "IntPNatToPosEqNatToInt")
(simp "RatExp0CompRule")
(simp "PosToNatToPosId")
(simp "<-" "IntPNatToPosEqNatToInt")
(simp "NatToPosToNatId")
(ng)
(simp "SuccPosPred")
(ng)
(use "Truth")
(use "Truth")
(use "NatLt0Pos")
(simp "SuccPosPred")
(use "Truth")
(use "Truth")
(use "NatLt0Pos")
;; 5
(assume "p" "q" "r")
(simp "SuccPosPred")
(simp "<-" "IntPNatToPosEqNatToInt")
(simp "RatExp0CompRule")
(simp "<-" "IntPNatToPosEqNatToInt")
(simp "PosToNatToPosId")
(simp "PosPred0RewRule")
(simp "NatToPosToNatId")
(use "Truth")
(use "Truth")
(use "NatLt0Pos")
(use "Truth")
(use "Truth")
;; Assertion proved
(assume "Assertion" "a" "r")
(simp "<-" "PosToNatToIntId")
(simp "<-" "PosToNatToIntId")
(use "Assertion")
;; Proof finished
(save "RatExpPosS")

;; To extend this to negative exponents use
(set-goal "all a,r a**IntN r==(a**IntN 1)**r")
(cases)
(cases)
;; 3-5
(assume "p" "q" "r")
(ng)
(use "Truth")
;; 4
(assume "q" "r")
(ng)
(use "Truth")
;; 5
(assume "p" "q" "r")
(ng)
(use "Truth")
;; Proof finished.

(display-pconst "RatExp" "IntExp")
(ppn (goal-to-formula (current-goal)))
(ppn "IntExp0RewRule")

;; Transferred to int.scm
;; (set-goal "all r 0**r=0")
;; (assume "r")
;; (use "PosLeLtCases" (pt "r") (pt "1"))
;; (ng)
;; (assume "r=1")
;; (simp "r=1")
;; (use "Truth")
;; (assume "1<r")
;; (simp "SuccPosPred")
;; (ng)
;; (use "Truth")
;; (use "1<r")
;; ;; Proof finished.

(ppn (pf "all r 0**r=0"))

(search-about "Pos" "Cases")
(search-about "Pos" "Succ")
(search-about "Pos" "Pred")
(display-pconst "PosToNat")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2016-04-17.  Attempt to include the essential parts of the former
;; lib/real.scm but avoiding global assumptions and simpreal.  The
;; order follows semws15/constr15.pdf

(set-goal "all x,y(Real x -> Real y -> x+y===y+x)")
(strip)
(ord-field-simp-bwd)
(use 1)
(use 2)

;; Attempt to avoid ord-field-simp-bwd
(set-goal "all x,y(Real x -> Real y -> x+y===y+x)")
(assume "x" "y" "Rx" "Ry")
(use "RealEqIntro")
(assume "k")
(elim "Rx")
(assume "x1" "Cx1" "Mx1")
(elim "Ry")
(assume "y1" "Cy1" "My1")
(elim "Cx1")
(assume "as^" "M" "MProp")
(elim "My1")
(assume "M1" "M1Prop")
;; etc

;; as^ should be avoided, take as instead

;; Maybe better to have a new file real.scm, where simpreal is
;; available.

;; 2016-04-17.  Prove axioms of an ordered field for rea, with RealEq
;; === as equality.  Define RealUDiv.
