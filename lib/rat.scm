;; 2016-06-16.  rat.scm.  Based on numbers.scm.

;; (load "~/git/minlog/init.scm")

;; (set! COMMENT-FLAG #f)
;; (libload "nat.scm")
;; (libload "pos.scm")
;; (libload "int.scm")
;; (set! COMMENT-FLAG #t)

(if (not (assoc "nat" ALGEBRAS))
    (myerror "First execute (libload \"nat.scm\")")
    (if (not (assoc "pos" ALGEBRAS))
	(myerror "First execute (libload \"pos.scm\")")
	(if (not (assoc "int" ALGEBRAS))
	    (myerror "First execute (libload \"int.scm\")"))))

(display "loading rat.scm ...") (newline)

;; We change term-to-t-deg-aux in case of division by a non-zero term,
;; or exponentiation of zero with a negative exponent.

(define (term-to-t-deg-aux term bound-vars)
  (case (tag term)
    ((term-in-var-form)
     (let ((var (term-in-var-form-to-var term)))
       (if (member var bound-vars) t-deg-one (var-to-t-deg var))))
    ((term-in-const-form) (const-to-t-deg
			   (term-in-const-form-to-const term)))
    ((term-in-abst-form)
     (let ((var (term-in-abst-form-to-var term))
	   (kernel (term-in-abst-form-to-kernel term)))
       (term-to-t-deg-aux kernel (cons var bound-vars))))
    ((term-in-app-form)
     (let* ((op (term-in-app-form-to-op term))
	    (arg (term-in-app-form-to-arg term))
	    (t-deg-op (term-to-t-deg-aux op bound-vars))
	    (t-deg-arg (term-to-t-deg-aux arg bound-vars)))
       (if
	(or (and (t-deg-one? t-deg-op) (t-deg-one? t-deg-arg))
	    (and (term-in-app-form? op)
		 (let* ((opop (term-in-app-form-to-op op))
			(oparg (term-in-app-form-to-arg op))
			(t-deg-oparg (term-to-t-deg-aux oparg bound-vars)))
		   (and (t-deg-one? t-deg-oparg)
			(term-in-const-form? opop)
			(let* ((const (term-in-const-form-to-const opop))
			       (name (const-to-name const)))
			  (or (and (member name '("RatDiv" "RealDiv" "CpxDiv"))
				   (synt-non-zero? arg))
			      (and (member name '("RatExp" "RealExp" "CpxExp"))
				   (or (synt-non-zero? oparg)
				       (synt-nneg? arg)))))))))
	t-deg-one
	t-deg-zero)))
    ((term-in-pair-form)
     (let* ((left (term-in-pair-form-to-left term))
	    (right (term-in-pair-form-to-right term))
	    (t-deg-left (term-to-t-deg-aux left bound-vars))
	    (t-deg-right (term-to-t-deg-aux right bound-vars)))
       (if (and (t-deg-one? t-deg-left) (t-deg-one? t-deg-right))
	   t-deg-one
	   t-deg-zero)))
    ((term-in-lcomp-form)
     (term-to-t-deg-aux (term-in-lcomp-form-to-kernel term) bound-vars))
    ((term-in-rcomp-form)
     (term-to-t-deg-aux (term-in-rcomp-form-to-kernel term) bound-vars))
    ((term-in-if-form)
     (let* ((test (term-in-if-form-to-test term))
	    (alts (term-in-if-form-to-alts term))
	    (t-deg-test (term-to-t-deg-aux test bound-vars))
	    (t-deg-alts (map (lambda (x) (term-to-t-deg-aux x bound-vars))
			     alts)))
       (if (apply and-op (cons (t-deg-one? t-deg-test)
			       (map t-deg-one? t-deg-alts)))
	   t-deg-one
	   t-deg-zero)))
    (else (myerror "term-to-t-deg-aux" "term expected" term))))

(define (synt-non-zero? term)
  (let ((op (term-in-app-form-to-final-op term))
	(args (term-in-app-form-to-args term))
	(type (term-to-type term)))
    (and
     (alg-form? type)
     (or
      (string=? (alg-form-to-name type) "pos")
      (and
       (term-in-const-form? op)
       (let* ((const (term-in-const-form-to-const op))
	      (name (const-to-name const)))
	 (cond
	  ((member name '("PosToNat" "Succ" "IntPos" "IntNeg")) #t)
	  ((member name '("NatToPos"))
	   (synt-non-zero? (car args)))
	  ((member name '("NatPlus" "IntPlus" "RatPlus" "RealPlus" "CpxPlus"))
	   (or (and (synt-pos? (car args)) (synt-nneg? (cadr args)))
	       (and (synt-nneg? (car args)) (synt-pos? (cadr args)))))
	  ((member name
		   '("NatTimes" "IntTimes" "RatTimes" "RealTimes" "CpxTimes"))
	   (and (synt-non-zero? (car args)) (synt-non-zero? (cadr args))))
	  ((member name '("NatExp" "IntExp" "RatExp" "RealExp" "CpxExp"))
	   (synt-non-zero? (car args)))
	  ((member name '("NatToInt" "RatConstr"))
	   (synt-non-zero? (car args)))
	  ((member name '("RealConstr"))
	   (and (term-in-abst-form? (car args))
		(let ((var (term-in-abst-form-to-var (car args)))
		      (kernel (term-in-abst-form-to-kernel (car args))))
		  (and (not (member var (term-to-free kernel)))
		       (synt-non-zero? kernel)))))
	  (else #f))))))))

(define (synt-pos? term)
  (let ((op (term-in-app-form-to-final-op term))
	(args (term-in-app-form-to-args term))
	(type (term-to-type term)))
    (and
     (alg-form? type)
     (or
      (string=? (alg-form-to-name type) "pos")
      (and
       (term-in-const-form? op)
       (let* ((const (term-in-const-form-to-const op))
	      (name (const-to-name const)))
	 (cond
	  ((member name '("PosToNat" "Succ" "IntPos")) #t)
	  ((member name '("NatPlus" "IntPlus" "RatPlus" "RealPlus"))
	   (or (and (synt-pos? (car args)) (synt-nneg? (cadr args)))
	       (and (synt-nneg? (car args)) (synt-pos? (cadr args)))))
	  ((member name '("NatTimes" "IntTimes" "RatTimes" "RealTimes"))
	   (or (and (synt-pos? (car args)) (synt-pos? (cadr args)))
	       (and (synt-neg? (car args)) (synt-neg? (cadr args)))))
	  ((member name '("NatExp" "IntExp" "RatExp" "RealExp"))
	   (synt-pos? (car args)))
	  ((member name '("NatToInt" "RatConstr"))
	   (synt-pos? (car args)))
	  ((member name '("RealConstr"))
	   (and (term-in-abst-form? (car args))
		(let ((var (term-in-abst-form-to-var (car args)))
		      (kernel (term-in-abst-form-to-kernel (car args))))
		  (and (not (member var (term-to-free kernel)))
		       (synt-pos? kernel)))))
	  (else #f))))))))

(define (synt-nneg? term)
  (let ((op (term-in-app-form-to-final-op term))
	(args (term-in-app-form-to-args term))
	(type (term-to-type term)))
    (and
     (alg-form? type)
     (or
      (member (alg-form-to-name type) '("pos" "nat"))
      (and
       (term-in-const-form? op)
       (let* ((const (term-in-const-form-to-const op))
	      (name (const-to-name const)))
	 (cond
	  ((member name '("IntZero" "IntPos")) #t)
	  ((member name '("IntPlus" "RatPlus" "RealPlus"))
	   (and (synt-nneg? (car args) (synt-nneg? (cadr args)))))
	  ((member name '("IntTimes" "RatTimes" "RealTimes"))
	   (or (and (synt-nneg? (car args)) (synt-nneg? (cadr args)))
	       (and (synt-neg? (car args)) (synt-neg? (cadr args)))))
	  ((member name '("IntExp" "RatExp" "RealExp"))
	   (synt-nneg? (car args)))
	  ((member name '("NatToInt" "RatConstr"))
	   (synt-nneg? (car args)))
	  ((member name '("RealConstr"))
	   (and (term-in-abst-form? (car args))
		(let ((var (term-in-abst-form-to-var (car args)))
		      (kernel (term-in-abst-form-to-kernel (car args))))
		  (and (not (member var (term-to-free kernel)))
		       (synt-nneg? kernel)))))
	  (else #f))))))))

(define (synt-neg? term)
  (let ((op (term-in-app-form-to-final-op term))
	(args (term-in-app-form-to-args term))
	(type (term-to-type term)))
    (and
     (alg-form? type)
     (term-in-const-form? op)
     (let* ((const (term-in-const-form-to-const op))
	    (name (const-to-name const)))
       (cond
	((member name '("IntNeg")) #t)
	((member name '("NatPlus" "IntPlus" "RatPlus" "RealPlus"))
	 (or (and (synt-neg? (car args)) (synt-npos? (cadr args)))
	     (and (synt-npos? (car args)) (synt-neg? (cadr args)))))
	((member name '("NatTimes" "IntTimes" "RatTimes" "RealTimes"))
	 (or (and (synt-pos? (car args)) (synt-neg? (cadr args)))
	     (and (synt-neg? (car args)) (synt-pos? (cadr args)))))
	((member name '("RatConstr"))
	 (synt-neg? (car args)))
	((member name '("RealConstr"))
	 (and (term-in-abst-form? (car args))
	      (let ((var (term-in-abst-form-to-var (car args)))
		    (kernel (term-in-abst-form-to-kernel (car args))))
		(and (not (member var (term-to-free kernel)))
		     (synt-neg? kernel)))))
	(else #f))))))

(define (synt-npos? term)
  (let ((op (term-in-app-form-to-final-op term))
	(args (term-in-app-form-to-args term))
	(type (term-to-type term)))
    (and
     (alg-form? type)
     (term-in-const-form? op)
     (let* ((const (term-in-const-form-to-const op))
	    (name (const-to-name const)))
       (cond
	((member name '("Zero" "IntZero" "IntNeg")) #t)
	((member name '("NatPlus" "IntPlus" "RatPlus" "RealPlus"))
	 (and (synt-npos? (car args)) (synt-npos? (cadr args))))
	((member name '("IntTimes" "RatTimes" "RealTimes"))
	 (or (and (synt-npos? (car args) (synt-nneg? (cadr args))))
	     (and (synt-nneg? (car args) (synt-npos? (cadr args))))))
	((member name '("RatConstr"))
	 (synt-npos? (car args)))
	((member name '("RealConstr"))
	 (and (term-in-abst-form? (car args))
	      (let ((var (term-in-abst-form-to-var (car args)))
		    (kernel (term-in-abst-form-to-kernel (car args))))
		(and (not (member var (term-to-free kernel)))
		     (synt-npos? kernel)))))
	(else #f))))))

;; 1.  Rational numbers
;; ====================

;; We want to overload operators like +,*,/,<=,<, and automatically
;; raise the type of arguments when reading.  For instance, + should
;; take its arguments, compute the lub rho of their types, raise the
;; type of both arguments to type rho, apply RhoPlus to the results.

;; A special situation occurs with exponentiation **: 2**3 is pos, and
;; 2** -3 is rat.  We need both types to determine the value type.

;; Moreover, a number should be displayed at the lowest possible level.

;; We introduce the rationals.  A rational is a pair i#p of an integer
;; i and a positive natural number p, interpreted as i/p.

(add-algs "rat" '("RatConstr" "int=>pos=>rat"))
(add-var-name "a" "b" "c" "d" (py "rat"))

(add-totality "rat")
(add-mr-ids "TotalRat")

;; RatTotalVar
(set-goal "all a TotalRat a")
(cases)
(assume "k" "p")
(use "TotalRatRatConstr")
(use "IntTotalVar")
(use "PosTotalVar")
;; Proof finished.
(save "RatTotalVar")

;; RatEqToEqD
(set-goal "all a,b(a=b -> a eqd b)")
(cases)
(assume "k" "p")
(cases)
(assume "j" "q")
(ng #t)
(assume "k=j andb p=q")
(assert "k=j")
 (use "k=j andb p=q")
(assume "k=j")
(simp "k=j")
(assert "p=q")
 (use "k=j andb p=q")
(assume "p=q")
(simp "p=q")
(use "InitEqD")
;; Proof finished.
(save "RatEqToEqD")

;; RatIfTotal
(set-goal "allnc a^(TotalRat a^ ->
 allnc (int=>pos=>alpha)^(
  allnc k^,p^(TotalInt k^ -> TotalPos p^ ->
                  Total((int=>pos=>alpha)^ k^ p^)) ->
  Total[if a^ (int=>pos=>alpha)^]))")
(assume "a^" "Ta" "(int=>pos=>alpha)^" "Tf")
(elim "Ta")
(assume "k^" "Tk" "p^" "Tp")
(ng #t)
(use "Tf")
(use "Tk")
(use "Tp")
;; Proof finished.
(save "RatIfTotal")

(add-token
 "#"
 'pair-op
 (lambda (x y)
   (mk-term-in-app-form
    (make-term-in-const-form (constr-name-to-constr "RatConstr"))
    x y)))

(add-display
 (py "rat")
 (lambda (x)
   (let ((op (term-in-app-form-to-final-op x))
	 (args (term-in-app-form-to-args x)))
     (if (and (term-in-const-form? op)
	      (string=? "RatConstr"
			(const-to-name (term-in-const-form-to-const op)))
	      (= 2 (length args)))
	 (if (and (term-in-const-form? (cadr args))
		  (string=? "One" (const-to-name
				   (term-in-const-form-to-const (cadr args)))))
	     (term-to-token-tree (car args))
	     (list 'pair-op "#"
		   (term-to-token-tree (car args))
		   (term-to-token-tree (cadr args))))
	 #f))))

;; 2. Parsing and display for arithmetical operations
;; ==================================================

;; We now come to some generalities concerning overloading and coercion.
;; Requirements:
;; - Internally every application is type correct
;; - Displaying a term can lower its type.
;; - Parsing (1) a term and (2) a new term obtained from it by lowering
;;   the type of some of its subterms must always return the same result,
;;   possibly up to lowering of its type.

;; Possible problems with usage of terms as arguments of predicates:
;; (P(3#1) is displayed as P 3, which is not type correct) or in lists:
;; (3#1)::(1#2): is displayed as 3::(1#2): , which is not type correct.

;; Solution: change make-term-in-app-form and make-predicate-formula.
;; If the types do not fit, raise the types of the offending arguments.

(add-item-to-algebra-edge-to-embed-term-alist
 "int" "rat"
 (let ((var (make-var (make-alg "int") -1 t-deg-one "")))
   (make-term-in-abst-form
    var (mk-term-in-app-form
         (make-term-in-const-form
          (constr-name-to-constr "RatConstr"))
         (make-term-in-var-form var)
         (make-term-in-const-form
          (constr-name-to-constr "One"))))))

(add-program-constant "RatPlus" (py "rat=>rat=>rat"))
(add-program-constant "RatUMinus" (py "rat=>rat"))
(add-program-constant "RatMinus" (py "rat=>rat=>rat"))
(add-program-constant "RatTimes" (py "rat=>rat=>rat"))
(add-program-constant "RatDiv" (py "rat=>rat=>rat"))
(add-program-constant "RatAbs" (py "rat=>rat"))
(add-program-constant "RatExp" (py "rat=>int=>rat"))
(add-program-constant "RatMax" (py "rat=>rat=>rat"))
(add-program-constant "RatMin" (py "rat=>rat=>rat"))

;; We define the intended equivalence relations on rat.  It is
;; decidable and hence can be introduced by a program constant.  We
;; need an extra token == here, since the standard equality = for
;; finitary algebras is available for rat as well.  Equality for reals
;; is not decidable.  We view it as a defined predicate constant.  For
;; convenience we use the setup of inductively defined predicates,
;; although the "inductive" definition is in fact explicit, i.e., does
;; not contain recursive calls.

(add-program-constant "RatEqv" (py "rat=>rat=>boole"))

(add-program-constant "RatLt" (py "rat=>rat=>boole"))
(add-program-constant "RatLe" (py "rat=>rat=>boole"))

;; Program constants used for extraction of program constants to
;; Haskell, where computation rules
;;
;;    f (SZero x) = ... x ...
;;
;; must be transformed into
;;    f n | even n = ... TranslationPosHalfEven n ...

(add-program-constant "TranslationNumerator" (py "rat=>int"))
(add-program-constant "TranslationDenominator" (py "rat=>pos"))

(add-token-and-type-to-name "+" (py "rat") "RatPlus")
(add-token-and-type-to-name "~" (py "rat") "RatUMinus")
(add-token-and-type-to-name "-" (py "rat") "RatMinus")
(add-token-and-type-to-name "*" (py "rat") "RatTimes")

(add-token "/" 'mul-op (make-term-creator "/" "rat"))
(add-token-and-type-to-name "/" (py "rat") "RatDiv")

(add-token-and-type-to-name "abs" (py "rat") "RatAbs")

(add-token-and-types-to-name "**" (list (py "pos") (py "int")) "RatExp")
(add-token-and-types-to-name "**" (list (py "nat") (py "int")) "RatExp")
(add-token-and-types-to-name "**" (list (py "int") (py "int")) "RatExp")
(add-token-and-types-to-name "**" (list (py "rat") (py "pos")) "RatExp")
(add-token-and-types-to-name "**" (list (py "rat") (py "nat")) "RatExp")
(add-token-and-types-to-name "**" (list (py "rat") (py "int")) "RatExp")

;; (1#2)**(IntN 1) has type rat, but (IntN 1)**(1#2) as type cpx.
;; Hence generally we will need token-and-types-to-name for Exp.

(add-token-and-type-to-name "max" (py "rat") "RatMax")
(add-token-and-type-to-name "min" (py "rat") "RatMin")

(add-token "==" 'rel-op (make-term-creator "==" "rat"))
(add-token-and-type-to-name "==" (py "rat") "RatEqv")

(add-token-and-type-to-name "<" (py "rat") "RatLt")
(add-token-and-type-to-name "<=" (py "rat") "RatLe")

(add-display (py "rat") (make-display-creator "RatPlus" "+" 'add-op))
(add-display (py "rat") (make-display-creator1 "RatUMinus" "~" 'prefix-op))
(add-display (py "rat") (make-display-creator "RatMinus" "-" 'add-op))
(add-display (py "rat") (make-display-creator "RatTimes" "*" 'mul-op))
(add-display (py "rat") (make-display-creator "RatDiv" "/" 'mul-op))
(add-display (py "rat") (make-display-creator1 "RatAbs" "abs" 'prefix-op))
(add-display (py "rat") (make-display-creator "RatExp" "**" 'exp-op))
(add-display (py "rat") (make-display-creator "RatMax" "max" 'mul-op))
(add-display (py "rat") (make-display-creator "RatMin" "min" 'mul-op))
(add-display (py "boole") (make-display-creator "RatEqv" "==" 'rel-op))
(add-display (py "boole") (make-display-creator "RatLt" "<" 'rel-op))
(add-display (py "boole") (make-display-creator "RatLe" "<=" 'rel-op))

;; 3. Arithmetic for rationals
;; ===========================

;; RatEqTotal
(set-goal "allnc a^(
 TotalRat a^ -> allnc b^(TotalRat b^ -> TotalBoole(a^ =b^)))")
(use "AllTotalElim")
(cases)
(assume "k" "p")
(use "AllTotalElim")
(cases)
(assume "j" "q")
(ng)
(use "BooleTotalVar")
;; Proof finished.
(save "RatEqTotal")

;; Rules for RatPlus

(add-computation-rules
 "(k#p)+(j#q)" "k*q+j*p#p*q")

;; RatPlusTotal
(set-totality-goal "RatPlus")
(use "AllTotalElim")
(cases)
(assume "k" "p")
(use "AllTotalElim")
(cases)
(assume "j" "q")
(ng)
(use "TotalRatRatConstr")
(use "IntTotalVar")
(use "PosTotalVar")
;; Proof finished.
(save-totality)

;; Code discarded 2016-04-10
;; ;; RatPlusTotalReal
;; (set-goal (rename-variables
;; 	   (real-and-formula-to-mr-formula
;; 	    (pt "RatPlus")
;; 	    (proof-to-formula (theorem-name-to-proof "RatPlusTotal")))))
;; (assume "a^" "a^0" "TMRa0a" "b^" "b^0" "TMRb0b")
;; (elim "TMRa0a")
;; (assume "k^" "k^0" "TMRk0k" "p^" "p^0" "TMRp0p")
;; (elim "TMRb0b")
;; (assume "l^" "l^0" "TMRl0l" "q^" "q^0" "TMRq0q")
;; (ng #t)
;; (use "TotalRatRatConstrMR")
;; (use "IntPlusTotalReal")
;; (use "IntTimesTotalReal")
;; (use "TMRk0k")
;; (use "TotalIntIntPosMR")
;; (use "TMRq0q")
;; (use "IntTimesTotalReal")
;; (use "TMRl0l")
;; (use "TotalIntIntPosMR")
;; (use "TMRp0p")
;; (use "PosTimesTotalReal")
;; (use "TMRp0p")
;; (use "TMRq0q")
;; ;; Proof finished.
;; (save "RatPlusTotalReal")

(set-goal "all a a+0=a")
(cases)
(assume "int" "pos")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "a+0" "a")

(set-goal "all a 0+a=a")
(cases)
(assume "int" "pos")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "0+a" "a")

;; RatPlusComm
(set-goal "all a,b a+b=b+a")
(cases)
(assume "k" "p")
(cases)
(assume "j" "q")
(ng)
(split)
(use "IntPlusComm")
(use "PosTimesComm")
;; Proof finished.
(save "RatPlusComm")

;; RatPlusAssoc
(set-goal "all a,b,c a+(b+c)=a+b+c")
(cases)
(assume "k" "p")
(cases)
(assume "j" "q")
(cases)
(assume "i" "r")
(ng)
(simp "<-" "IntTimesAssoc")
(simp "<-" "IntTimesAssoc")
(simp "<-" "IntTimesAssoc")
(simp "<-" "IntTimesAssoc")
(assert "IntTimes r p=IntTimes p r")
 (use "IntTimesComm")
(assume "rp=pr")
(simp "rp=pr")
(drop "rp=pr")
(assert "IntTimes q p=IntTimes p q")
 (use "IntTimesComm")
(assume "qp=pq")
(simp "qp=pq")
(drop "qp=pq")
(ng)
(use "Truth")
;; Proof finished.
(save "RatPlusAssoc")
(add-rewrite-rule "a+(b+c)" "a+b+c")

;; (display-pconst "RatPlus")
;; (display-pconst "IntPlus")
;; (display-pconst "PosPlus")
;; (display-pconst "IntMinus")
;; (display-pconst "PosMinus")
;; (search-about 'all "Int" "Times" "Assoc")
;; (search-about "Times" "Int")
;; (search-about "Inj")

;; Rules for RatUMinus

(add-computation-rules
 "~(IntZero#p)" "IntZero#p"
 "~(IntP p#q)" "(IntN p#q)"
 "~(IntN p#q)" "(IntP p#q)")

;; RatUMinusTotal
(set-totality-goal "RatUMinus")
(use "AllTotalElim")
(cases)
(cases)
;; 4-6
(assume "p" "q")
(ng)
(use "RatTotalVar")
;; 5
(ng)
(assume "p")
(use "RatTotalVar")
;; 6
(assume "p" "q")
(ng)
(use "RatTotalVar")
;; Proof finished.
(save-totality)

(set-goal "all k,p ~(k#p)=(~k#p)")
(cases)
;;  2-4
(assume "p" "q")
(use "Truth")
;; 3
(assume "p")
(use "Truth")
;; 4
(assume "p" "q")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "~(k#p)" "~k#p")

;; RatUMinusUMinus
(set-goal "all a ~ ~a=a")
(cases)
(assume "k" "p")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "~ ~a" "a")

(set-goal "all a,b ~(a+b)= ~a+ ~b")
(cases)
(assume "k" "p")
(cases)
(assume "j" "q")
(ng)
(use "Truth")
;; Proof finished.
(add-rewrite-rule "~(a+b)" "~a+ ~b")

;; RatUMinusInj
(set-goal "all a,b (~a= ~b)=(a=b)")
(cases)
(assume "k" "p")
(cases)
(assume "j" "q")
(ng)
(simp "IntUMinusInj")
(use "Truth")
;; Proof finished.
(save "RatUMinusInj")

;; (display-pconst "RatUMinus")

;; Rules for RatMinus

(add-computation-rules
 "a-b" "a+ ~b")

;; RatMinusTotal
(set-totality-goal "RatMinus")
(use "AllTotalElim")
(assume "a")
(use "AllTotalElim")
(assume "b")
(ng)
(use "RatTotalVar")
;; Proof finished.
(save-totality)

;; Code discarded 2016-04-10
;; ;; RatMinusTotalReal
;; (set-goal (rename-variables
;; 	   (real-and-formula-to-mr-formula
;; 	    (pt "RatMinus")
;; 	    (proof-to-formula (theorem-name-to-proof "RatMinusTotal")))))
;; (assume "a^" "a^0" "TMRa0a" "b^" "b^0" "TMRb0b")
;; (elim "TMRa0a")
;; (assume "k^" "k^0" "TMRk0k" "p^" "p^0" "TMRp0p")
;; (elim "TMRb0b")
;; (assume "l^" "l^0" "TMRl0l" "q^" "q^0" "TMRq0q")
;; (ng #t)
;; (use "TotalRatRatConstrMR")
;; (use "IntMinusTotalReal")
;; (use "IntTimesTotalReal")
;; (use "TMRk0k")
;; (use "TotalIntIntPosMR")
;; (use "TMRq0q")
;; (use "IntTimesTotalReal")
;; (use "TMRl0l")
;; (use "TotalIntIntPosMR")
;; (use "TMRp0p")
;; (use "PosTimesTotalReal")
;; (use "TMRp0p")
;; (use "TMRq0q")
;; ;; Proof finished.
;; (save "RatMinusTotalReal")

;; Rules for RatTimes

(add-computation-rules
 "(k#p)*(j#q)" "k*j#p*q")

;; RatTimesTotal
(set-totality-goal "RatTimes")
(use "AllTotalElim")
(cases)
(assume "k" "p")
(use "AllTotalElim")
(cases)
(assume "j" "q")
(ng)
(use "RatTotalVar")
;; Proof finished.
(save-totality)

;; Code discarded 2016-04-10
;; ;; RatTimesTotalReal
;; (set-goal (rename-variables
;; 	   (real-and-formula-to-mr-formula
;; 	    (pt "RatTimes")
;; 	    (proof-to-formula (theorem-name-to-proof "RatTimesTotal")))))
;; (assume "a^" "a^0" "TMRa0a" "b^" "b^0" "TMRb0b")
;; (elim "TMRa0a")
;; (assume "k^" "k^0" "TMRk0k" "p^" "p^0" "TMRp0p")
;; (elim "TMRb0b")
;; (assume "l^" "l^0" "TMRl0l" "q^" "q^0" "TMRq0q")
;; (ng #t)
;; (use "TotalRatRatConstrMR")
;; (use "IntTimesTotalReal")
;; (use "TMRk0k")
;; (use "TMRl0l")
;; (use "PosTimesTotalReal")
;; (use "TMRp0p")
;; (use "TMRq0q")
;; ;; Proof finished.
;; (save "RatTimesTotalReal")

(set-goal "all a a*1=a")
(cases)
(assume "k" "p")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "a*1" "a")

(set-goal "all a 1*a=a")
(cases)
(assume "k" "p")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "1*a" "a")

;; RatTimesComm
(set-goal "all a,b a*b=b*a")
(cases)
(assume "k" "p")
(cases)
(assume "j" "q")
(ng)
(split)
(use "IntTimesComm")
(use "PosTimesComm")
;; Proof finished.
(save "RatTimesComm")

;; RatTimesAssoc
(set-goal "all a,b,c a*(b*c)=a*b*c")
(cases)
(assume "k" "p")
(cases)
(assume "j" "q")
(cases)
(assume "i" "r")
(ng)
(use "Truth")
;; Proof finished.
(save "RatTimesAssoc")
(add-rewrite-rule "a*(b*c)" "a*b*c")

;; We show that one RatUMinus can be moved out of a product.

;; ;; RatTimesIdUMinus
(set-goal "all a,b a* ~b= ~(a*b)")
(cases)
(assume "k" "p")
(cases)
(assume "j" "q")
(ng)
(use "Truth")
;; Proof finished.
;; (save "RatTimesIdUMinus")
(add-rewrite-rule "a* ~b" "~(a*b)")

;; ;; RatTimesUMinusId
(set-goal "all a,b ~a*b= ~(a*b)")
(cases)
(assume "k" "p")
(cases)
(assume "j" "q")
(ng)
(use "Truth")
;; Proof finished.
;; (save "RatTimesUMinusId")
(add-rewrite-rule "~a*b" "~(a*b)")

;; Rules for RatDiv.  They give correct results for a/b (only) if b not 0.

(add-computation-rules
 "(k#p)/(IntP r#q)" "(k*q#r*p)"
 "(k#p)/(IntZero#q)" "RatConstr IntZero One"
 "(k#p)/(IntN r#q)" "((IntZero-k)*q#r*p)")

;; RatDivTotal
(set-totality-goal "RatDiv")
(use "AllTotalElim")
(cases)
(assume "k" "p")
(use "AllTotalElim")
(cases)
(cases)
;; 7-9
(assume "r" "q")
(ng)
(use "RatTotalVar")
;; 8
(assume "q")
(ng)
(use "RatTotalVar")
;; 9
(assume "r" "q")
(ng)
(use "RatTotalVar")
;; Proof finshed.
(save-totality)

;; Rules for RatAbs

(add-computation-rules
 "abs(IntZero#q)" "IntZero#q"
 "abs(IntP p#q)" "IntP p#q"
 "abs(IntN p#q)" "IntP p#q")

;; RatAbsTotal
(set-totality-goal "RatAbs")
(use "AllTotalElim")
(cases)
(cases)
;; 4-6
(assume "p" "q")
(ng)
(use "RatTotalVar")
;; 5
(assume "q")
(ng)
(use "RatTotalVar")
;; 6
(assume "p" "q")
(ng)
(use "RatTotalVar")
;; Proof finshed.
(save-totality)

(set-goal "all a abs(~a)=abs a")
(cases)
(cases)
(assume "p" "q")
(ng)
(use "Truth")
(assume "q")
(ng)
(use "Truth")
(assume "p" "q")
(ng)
(use "Truth")
;; Proof finished.
(add-rewrite-rule "abs(~a)" "abs a")

(set-goal "all k,p abs(k#p)=(abs k#p)")
(cases)
(assume "p" "q")
(use "Truth")
(assume "q")
(use "Truth")
(assume "p" "q")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "abs(k#p)" "(abs k#p)")

;; Rules for RatExp : rat=>int=>rat

(add-computation-rules
 "(k#q)**(IntP r)" "(k**r)#(q**r)"
 "rat**IntZero" "IntP One#One"
 "(IntZero#q)**(IntN r)" "IntZero#q"
 "((IntP p)#q)**(IntN r)" "IntP(q**r)#(p**r)"
 "((IntN p)#q)**(IntN r)" "((IntN q)**r)#(p**r)")

;; RatExpTotal
(set-totality-goal "RatExp")
(use "AllTotalElim")
(cases)
(assume "k" "q")
(use "AllTotalElim")
(cases)
;; 6-8
(assume "p")
(use "RatTotalVar")
;; 7
(ng)
(use "RatTotalVar")
;; 8
(assume "p")
(cases (pt "k"))
;; 12-14
(assume "r" "k=r")
(ng)
(use "RatTotalVar")
;; 13
(assume "k=0")
(ng)
(use "RatTotalVar")
;; 14
(assume "r" "k=IntN r")
(ng)
(use "RatTotalVar")
;; Proof finished.
(save-totality)

;; Rules for RatMax

(add-computation-rules
 "(k#p)max(j#q)"
 "[if (k*q<=j*p) (j#q) (k#p)]")

;; RatMaxTotal
(set-totality-goal "RatMax")
(use "AllTotalElim")
(cases)
(assume "k" "p")
(use "AllTotalElim")
(cases)
(assume "j" "q")
(ng)
(use "RatTotalVar")
;; Proof finished.
(save-totality)

;; Rules for RatMin

(add-computation-rules
 "(k#p)min(j#q)"
 "[if (k*q<=j*p) (k#p) (j#q)]")

;; RatMinTotal
(set-totality-goal "RatMin")
(use "AllTotalElim")
(cases)
(assume "k" "p")
(use "AllTotalElim")
(cases)
(assume "j" "q")
(ng)
(use "RatTotalVar")
;; Proof finished.
(save-totality)

;; Rules for RatEqv

(add-computation-rules
 "(k#p)==(j#q)" "k*q=j*p")

;; RatEqvTotal
(set-totality-goal "RatEqv")
(use "AllTotalElim")
(cases)
(assume "k" "p")
(use "AllTotalElim")
(cases)
(assume "j" "q")
(ng)
(use "BooleTotalVar")
;; Proof finished.
(save-totality)

;; RatEqvRefl
(set-goal "all a a==a")
(cases)
(assume "k" "p")
(use "Truth")
;; Proof finished.
;; (save "RatEqvRefl")
(add-rewrite-rule "a==a" "True")

(set-goal "all a ~a+a==0")
(cases)
(assume "k" "p")
(use "Truth")
;; Proof finished
(add-rewrite-rule "~a+a==0" "True")

(set-goal "all a a+ ~a==0")
(cases)
(assume "k" "p")
(use "Truth")
;; Proof finished
(add-rewrite-rule "a+ ~a==0" "True")

;; RatTimesIdZero
(set-goal "all a,p a*(0#p)==0")
(cases)
(strip)
(use "Truth")
;; Proof finished.
(save "RatTimesIdZero")

;; RatTimesZeroId
(set-goal "all a,p (0#p)*a==0")
(cases)
(strip)
(use "Truth")
;; Proof finished.
(save "RatTimesZeroId")

;; RatEqvSym
(set-goal "all a,b(a==b -> b==a)")
(cases)
(assume "k" "p")
(cases)
(assume "j" "q")
(ng)
(assume "EqHyp")
(simp "EqHyp")
(use "Truth")
;; Proof finished.
(save "RatEqvSym")

;; Other properties of RatEqv are postponed after RatLe

;; Rules for RatLt

(add-computation-rules
 "(k#p)<(j#q)" "k*q<j*p")

;; RatLtTotal
(set-totality-goal "RatLt")
(use "AllTotalElim")
(cases)
(assume "k" "p")
(use "AllTotalElim")
(cases)
(assume "j" "q")
(ng)
(use "BooleTotalVar")
;; Proof finished.
(save-totality)

;; Rules for RatLe

(add-computation-rules
 "(k#p)<=(j#q)" "k*q<=j*p")

;; RatLeTotal
(set-totality-goal "RatLe")
(use "AllTotalElim")
(cases)
(assume "k" "p")
(use "AllTotalElim")
(cases)
(assume "j" "q")
(ng)
(use "BooleTotalVar")
;; Proof finished.
(save-totality)

;; (display-pconst "RatLe")
;; (display-pconst "IntLe")

(set-goal "all a a<=a")
(cases)
(assume "k" "p")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "a<=a" "True")

(set-goal "all a,p a<=a+p")
(cases)
(assume "k" "p" "q")
(ng)
(use "Truth")
;; Proof finished.
(add-rewrite-rule "a<=a+p" "True")

;; RatLeTrans
(set-goal "all a,b,c(a<=b -> b<=c -> a<=c)")
(cases)
(assume "k" "p")
(cases)
(assume "j" "q")
(cases)
(assume "i" "r")
(ng)
(assume "kq<=jp" "jr<=iq")
(simp "<-" "IntLe7RewRule" (pt "q"))
(simp "<-" "IntTimesAssoc")
(simp "<-" "IntTimesAssoc")
(use "IntLeTrans" (pt "j*IntTimes p r"))
;; 13,14
(assert "IntTimes r q=IntTimes q r")
 (use "IntTimesComm")
(assume "IntTimes r q=IntTimes q r")
(simp "IntTimes r q=IntTimes q r")
(drop "IntTimes r q=IntTimes q r")
(simp "IntTimesAssoc")
(simp "IntTimesAssoc")
(simp "IntLe7RewRule")
(use "kq<=jp")
;; 14
(assert "IntTimes p r=IntTimes r p")
 (use "IntTimesComm")
(assume "IntTimes p r=IntTimes r p")
(simp "IntTimes p r=IntTimes r p")
(drop "IntTimes p r=IntTimes r p")
(assert "IntTimes p q=IntTimes q p")
 (use "IntTimesComm")
(assume "IntTimes p q=IntTimes q p")
(simp "IntTimes p q=IntTimes q p")
(drop "IntTimes p q=IntTimes q p")
(simp "IntTimesAssoc")
(simp "IntTimesAssoc")
(simp "IntLe7RewRule")
(use "jr<=iq")
;; Proof finished.
(save "RatLeTrans")

;; RatLeRefl
(set-goal "all a,b(a==b -> a<=b)")
(cases)
(assume "k" "p")
(cases)
(assume "j" "q")
(ng)
(assume "kq=jp")
(simp "kq=jp")
(use "Truth")
;; Proof finished.
(save "RatLeRefl")

;; RatLeCompat
(set-goal "all a,b,c,d(a==b -> c==d -> (a<=c)=(b<=d))")
(assert "all a,b,c,d(a==b -> c==d -> a<=c -> b<=d)")
 (assume "a" "b" "c" "d" "a=b" "c=d" "a<=c")
 (use "RatLeTrans" (pt "a"))
 (use "RatLeRefl")
 (use "RatEqvSym")
 (use "a=b")
 (use "RatLeTrans" (pt "c"))
 (use "a<=c")
 (use "RatLeRefl")
 (use "c=d")
;; Assertion proved
(assume "RatLeCompatAux" "a" "b" "c" "d" "a=b" "c=d")
(cases (pt "a<=c"))
;; Case a<=c
(assume "a<=c")
(assert "b<=d")
 (use "RatLeCompatAux" (pt "a") (pt "c"))
 (use "a=b")
 (use "c=d")
 (use "a<=c")
(assume "b<=d")
(simp "b<=d")
(use "Truth")
;; Case a<=c -> F
(assume "a<=c -> F")
(assert "b<=d -> F")
 (assume "b<=d")
 (use "a<=c -> F")
 (use "RatLeCompatAux" (pt "b") (pt "d"))
 (use "RatEqvSym")
 (use "a=b")
 (use "RatEqvSym")
 (use "c=d")
 (use "b<=d")
(assume "b<=d -> F")
(simp "b<=d -> F")
(use "Truth")
;; Proof finished.
(save "RatLeCompat")

;; Code discarded 2016-04-21
;; ;; RatLeCompat
;; (set-goal "all a,b,c,d(a==b -> c==d -> a<=c -> b<=d)")
;; (assume "a" "b" "c" "d" "a=b" "c=d" "a<=c")
;; (use "RatLeTrans" (pt "a"))
;; (use "RatLeRefl")
;; (use "RatEqvSym")
;; (use "a=b")
;; (use "RatLeTrans" (pt "c"))
;; (use "a<=c")
;; (use "RatLeRefl")
;; (use "c=d")
;; ;; Proof finished.
;; (save "RatLeCompat")

;; RatLeMonPlus
(set-goal "all a,b,c,d(a<=b -> c<=d -> a+c<=b+d)")
;; RatLeMonPlusAux
(assert "all a,b,c(a<=b -> a+c<=b+c)")
(cases)
(assume "k" "p")
(cases)
(assume "j" "q")
(cases)
(assume "i" "r")
(ng)
(assume "kq<=jp")
;; ?_9:k*r*(q*r)+i*p*(q*r)<=
;;     j*r*(p*r)+i*q*(p*r)
(use "IntLeMonPlus")
;; 10,11
(simp "<-" "IntTimesAssoc")
(simp "<-" "IntTimesAssoc")
(simp "<-" "IntTimes2CompRule")
(simp "<-" "IntTimes2CompRule")
(assert "r*IntTimes q r=(r*IntP q)*r")
 (ng)
 (use "Truth")
(assume "r*IntTimes q r=(r*IntP q)*r")
(simp "r*IntTimes q r=(r*IntP q)*r")
(drop "r*IntTimes q r=(r*IntP q)*r")
(assert "IntTimes r q=IntTimes q r")
 (use "IntTimesComm")
(assume "IntTimes r q=IntTimes q r")
(simp "IntTimes r q=IntTimes q r")
(drop "IntTimes r q=IntTimes q r")
(assert "r*IntTimes p r=(r*IntP p)*r")
 (ng)
 (use "Truth")
(assume "r*IntTimes p r=(r*IntP p)*r")
(simp "r*IntTimes p r=(r*IntP p)*r")
(drop "r*IntTimes p r=(r*IntP p)*r")
(assert "IntTimes r p=IntTimes p r")
 (use "IntTimesComm")
(assume "IntTimes r p=IntTimes p r")
(simp "IntTimes r p=IntTimes p r")
(drop "IntTimes r p=IntTimes p r")
(simp "IntTimesAssoc")
(use "IntLeTrans" (pt "j*IntTimes p r*r"))
(simp "IntTimesAssoc")
(simp "IntTimesAssoc")
(use "kq<=jp")
(assert "j*IntTimes p r*r=j*(IntTimes p r*r)")
 (simp "<-" "IntTimesAssoc")
 (use "Truth")
(assume "j*IntTimes p r*r=j*(IntTimes p r*r)")
(simp "j*IntTimes p r*r=j*(IntTimes p r*r)")
(use "Truth")
;; 11
;; (assert "i*p*(q*r)=i*q*(p*r)")
(simp "<-" "IntTimes2CompRule")
(simp "<-" "IntTimes2CompRule")
(simp "<-" "IntTimesAssoc")
(simp "<-" "IntTimesAssoc")
(assert "p*IntTimes q r=(p*IntP q)*r")
 (ng)
 (use "Truth")
(assume "p*IntTimes q r=(p*IntP q)*r")
(simp "p*IntTimes q r=(p*IntP q)*r")
(drop "p*IntTimes q r=(p*IntP q)*r")
(assert "q*IntTimes p r=(q*IntP p)*r")
 (ng)
 (use "Truth")
(assume "q*IntTimes p r=(q*IntP p)*r")
(simp "q*IntTimes p r=(q*IntP p)*r")
(drop "q*IntTimes p r=(q*IntP p)*r")
(assert "IntTimes p q=IntTimes q p")
 (use "IntTimesComm")
(assume "IntTimes p q=IntTimes q p")
(simp "IntTimes p q=IntTimes q p")
(drop "IntTimes p q=IntTimes q p")
(ng)
(use "Truth")
;; Proof of assertion finished.
(assume "RatLeMonPlusAux" "a" "b" "c" "d" "a<=b" "c<=d")
(use "RatLeTrans" (pt "b+c"))
(use "RatLeMonPlusAux")
(use "a<=b")
(simp "RatPlusComm")
(use "RatLeTrans" (pt "d+b"))
(use "RatLeMonPlusAux")
(use "c<=d")
(simp "RatPlusComm")
(use "Truth")
;; Proof finished.
(save "RatLeMonPlus")

;; RatLeAntiSym
(set-goal "all a,b(a<=b -> b<=a -> a==b)")
(cases)
(assume "k" "p")
(cases)
(assume "j" "q")
(ng)
(use "IntLeAntiSym")
;; Proof finished
(save "RatLeAntiSym")

;; Now we can prove transitivity of RatEqv.

;; RatEqvTrans
(set-goal "all a,b,c(a==b -> b==c -> a==c)")
(assume "a" "b" "c" "a=b" "b=c")
(use "RatLeAntiSym")
;; 3,4
(use "RatLeTrans" (pt "b"))
(use "RatLeRefl")
(use "a=b")
(use "RatLeRefl")
(use "b=c")
;; 4
(use "RatLeTrans" (pt "b"))
(use "RatLeRefl")
(use "RatEqvSym")
(use "b=c")
(use "RatLeRefl")
(use "RatEqvSym")
(use "a=b")
;; Proof finished.
(save "RatEqvTrans")

;; RatEqvCompat
(set-goal "all a,b,c,d(a==b -> c==d -> (a==c)=(b==d))")
(assume "a" "b" "c" "d" "a=b" "c=d")
(cases (pt "a==c"))
(assume "a=c")
(assert "b==d")
(use "RatEqvTrans" (pt "c"))
(use "RatEqvTrans" (pt "a"))
(use "RatEqvSym")
(use "a=b")
(use "a=c")
(use "c=d")
(assume "b=d")
(simp "b=d")
(use "Truth")
(assume "a=c -> F")
(assert "b==d -> F")
(assume "b=d")
(use "a=c -> F")
(use "RatEqvTrans" (pt "b"))
(use "a=b")
(use "RatEqvTrans" (pt "d"))
(use "b=d")
(use "RatEqvSym")
(use "c=d")
(assume "b=d -> F")
(simp "b=d -> F")
(use "Truth")
;; Proof finished.
(save "RatEqvCompat")

;; RatPlusCompat
(set-goal "all a,b,c,d(a==b -> c==d -> a+c==b+d)")
(assume "a" "b" "c" "d" "a=b" "c=d")
(use "RatLeAntiSym")
;; 3,4
(use "RatLeMonPlus")
(use "RatLeRefl")
(use "a=b")
(use "RatLeRefl")
(use "c=d")
;; 4
(use "RatLeMonPlus")
(use "RatLeRefl")
(use "RatEqvSym")
(use "a=b")
(use "RatLeRefl")
(use "RatEqvSym")
(use "c=d")
;; Proof finished.
(save "RatPlusCompat")

;; RatEqvPlusMinus
(set-goal "all a,b a+ ~b+b==a")
(assume "a" "b")
(simp "<-" "RatPlusAssoc")
(simprat (pf "~b+b==0")) ;needs RatPlusCompat
(use "Truth")
(use "Truth")
;; Proof finished.
(save "RatEqvPlusMinus")

(set-goal "all p,q,r,r0((IntN p#q)<=(IntN r#r0))=((r#r0)<=(p#q))")
(assume "p" "q" "r" "r0")
(ng)
(use "Truth")
;; Proof finished.
(add-rewrite-rule
 "(IntN p#q)<=(IntN r#r0)" "(r#r0)<=(p#q)")

;; RatLeTimes
(set-goal "all a,b,r,r0
 (a*(r#r0)<=b*(r#r0))=(a<=b)")
;; We insert a general lemma
(assert "all p,q,r p*IntTimes q r=q*IntTimes p r")
 (assume "p" "q" "r")
 (ng)
 (assert "p*q=q*p")
  (use "PosTimesComm")
 (assume "p*q=q*p")
 (simp "p*q=q*p")
 (use "Truth")
;; Subproof finished.
(assume "Lemma")
;; Now the proper proof starts
(cases)
(assume "k" "p")
(cases)
(assume "j" "q" "r" "r0")
(ng #t)
(simp "<-" "IntTimesAssoc")
(simp "<-" "IntTimesAssoc")
(simp "<-" "IntTimes2CompRule")
(simp "<-" "IntTimes2CompRule")
;; ?_10:(k*(r*IntTimes q r0)<=j*(r*IntTimes p r0))=
;;      (k*q<=j*p)
(simp "Lemma")
(inst-with-to "Lemma" (pt "r")  (pt "p")  (pt "r0") "Lemmarpr0")
(simp "Lemmarpr0")
(drop "Lemma" "Lemmarpr0")
(simp "IntTimesAssoc")
(assert "j*(p*IntTimes r r0)=j*p*IntTimes r r0")
 (use "IntTimesAssoc")
(assume "j*(p*IntTimes r r0)=j*p*IntTimes r r0")
(simp "j*(p*IntTimes r r0)=j*p*IntTimes r r0")
(drop "j*(p*IntTimes r r0)=j*p*IntTimes r r0")
(ng)
(use "Truth")
;; Proof finished.
(add-rewrite-rule "a*(r#r0)<=b*(r#r0)" "a<=b")

;; RatLeMonTimes
(set-goal "all a,b,c(0<=a -> b<=c -> b*a<=c*a)")
(cases)
(cases)
;; 3-5
(assume "p" "q" "b" "c" "Useless" "b<=c")
(ng)
(use "b<=c")
;; 4
(assume "pos" "b" "c" "Useless1" "Useless2")
(use "RatLeRefl")
(use "RatEqvTrans" (pt "(0#1)"))
(use "RatTimesIdZero")
(use "RatEqvSym")
(use "RatTimesIdZero")
;; 5
(assume "p" "q" "b" "c" "Absurd")
(use "Efq")
(use "Absurd")
;; Proof finished.
(save "RatLeMonTimes")

;; RatLeUMinus
(set-goal "all a,b (~b<= ~a)=(a<=b)")
(cases)
(cases)
;; 3-5
(assume "p" "q")
(cases)
(cases)
;; 8-10
(assume "r" "r0")
(ng)
(use "Truth")
;; 9
(ng)
(strip)
(use "Truth")
;; 10
(assume "r" "r0")
(ng)
(use "Truth")
;; 4
(cases)
;; 17-19
(cases)
(cases)
(ng)
(strip)
(use "Truth")
;; 22
(ng)
(strip)
(use "Truth")
;; 23
(ng)
(strip)
(use "Truth")
;; 18
(assume "q")
(cases)
(cases)
;; 32-34
(ng)
(strip)
(use "Truth")
;; 33
(ng)
(strip)
(use "Truth")
;; 34
(ng)
(strip)
(use "Truth")
;; 19
(assume "q")
(cases)
(cases)
;; 43-45
(ng)
(strip)
(use "Truth")
;; 44
(ng)
(strip)
(use "Truth")
;; 45
(ng)
(strip)
(use "Truth")
;; 5
(assume "p" "q")
(cases)
(cases)
;; 54-56
(assume "r" "r0")
(ng)
(use "Truth")
;; 55
(ng)
(strip)
(use "Truth")
;; 56
(assume "r" "r0")
(ng)
(use "Truth")
;; Proof finished.
(save "RatLeUMinus")
(add-rewrite-rule "~b<= ~a" "a<=b")

;; RatTimesCompat
(set-goal "all a,b,c,d(a==b -> c==d -> a*c==b*d)")
;; We need an auxiliary lemma
;; RatTimesAux
(assert "all c,a,b(a==b -> a*c==b*c)")
(cases)
(cases)
;; 5-7
(assume "p" "p0")
(cases)
(assume "j" "q")
(cases)
(assume "i" "r" "b=c")
(use "RatLeAntiSym")
;; 13,14
(simp "RatLe3RewRule")
(use "RatLeRefl")
(use "b=c")
;; 14
(simp "RatLe3RewRule")
(use "RatLeRefl")
(use "RatEqvSym")
(use "b=c")
;; 6
(assume "p" "a" "b" "a=b")
(use "RatEqvTrans" (pt "(0#1)"))
(use "RatTimesIdZero")
(use "RatEqvSym")
(use "RatTimesIdZero")
;; 7
(assume "p" "p0")
(cases)
(assume "j" "q")
(cases)
(assume "i" "r" "b=c")
(use "RatLeAntiSym")
;; 29,30
(simp "<-" "RatUMinus1CompRule")
(simp "RatTimes3RewRule")
(simp "RatTimes3RewRule")
(simp "RatLeUMinus")
(use "RatLeMonTimes")
(use "Truth")
(use "RatLeRefl")
(use "RatEqvSym")
(use "b=c")
;; 30
(simp "<-" "RatUMinus1CompRule")
(simp "RatTimes3RewRule")
(simp "RatTimes3RewRule")
(simp "RatLeUMinus")
(use "RatLeMonTimes")
(use "Truth")
(use "RatLeRefl")
(use "b=c")
;; Subproof finished.
(assume "RatTimesCompatAux")
;; Now the proof starts properly
(assume "a" "b" "c" "d" "a=b" "c=d")
(use "RatEqvTrans" (pt "b*c"))
(use "RatTimesCompatAux")
(use "a=b")
(use "RatEqvTrans" (pt "c*b"))
(simp "RatTimesComm")
(use "Truth")
(use "RatEqvTrans" (pt "d*b"))
(use "RatTimesCompatAux")
(use "c=d")
(simp "RatTimesComm")
(use "Truth")
;; Proof finished.
(save "RatTimesCompat")

;; RatTimesPlusDistr
(set-goal "all a,b,c a*(b+c)==a*b+a*c")
(cases)
(assume "k" "p")
(cases)
(assume "j" "q")
(cases)
(assume "i" "r")
(ng)
(simp (pf "k*i*q*(p*q*p*r)=k*i*(p*q)*(p*q*r)"))
(simp (pf "k*j*r*(p*q*p*r)=k*j*(p*r)*(p*q*r)"))
(use "Truth")
;; ?_12:k*j*r*(p*q*p*r)=k*j*(p*r)*(p*q*r)
(simp "<-" "IntTimesAssoc")
(simp "<-" "IntTimesAssoc")
(simp "<-" "IntTimesAssoc")
(simp "<-" "IntTimesAssoc")
(simp (pf "IntTimes r(p*q*p*r)=IntTimes(p*r)(p*q*r)"))
(use "Truth")
(ng)
;; ?_19:r*p*q*p*r=p*r*p*q*r
(simp (pf "r*p*q*p=p*r*p*q"))
(use "Truth")
(simp (pf "all p1,p2(p1=p2 -> p1*q*p=p2*p*q)"))
(use "Truth")
(use "PosTimesComm")
(assume "p1" "p2" "p1=p2")
(simp (pf "p1=p2"))
(simp "<-" "PosTimesAssoc")
(simp "<-" "PosTimesAssoc")
(simp (pf "q*p=p*q"))
(use "Truth")
(use "PosTimesComm")
(use "p1=p2")
;; ?_10:k*i*q*(p*q*p*r)=k*i*(p*q)*(p*q*r)
(simp "<-" "IntTimesAssoc")
(simp "<-" "IntTimesAssoc")
(simp "<-" "IntTimesAssoc")
(simp "<-" "IntTimesAssoc")
(simp (pf "IntTimes q(p*q*p*r)=IntTimes(p*q)(p*q*r)"))
(use "Truth")
(ng)
;; ?_38:q*p*q*p*r=p*q*p*q*r
(simp (pf "q*p*q*p=p*q*p*q"))
(use "Truth")
(simp (pf "all p1,p2(p1=p2 -> p1*q*p=p2*p*q)"))
(use "Truth")
(use "PosTimesComm")
(assume "p1" "p2" "p1=p2")
(simp (pf "p1=p2"))
(simp "<-" "PosTimesAssoc")
(simp "<-" "PosTimesAssoc")
(simp (pf "q*p=p*q"))
(use "Truth")
(use "PosTimesComm")
(use "p1=p2")
;; Proof finished.
(save "RatTimesPlusDistr")

;; RatTimesPlusDistrLeft
(set-goal "all a,b,c (a+b)*c==a*c+b*c")
(assume "a" "b" "c")
(simp "RatTimesComm")
(simp-with (pf "a*c=c*a"))
(simp-with (pf "b*c=c*b"))
(use "RatTimesPlusDistr")
(use "RatTimesComm")
(use "RatTimesComm")
;; Proof finished.
(save "RatTimesPlusDistrLeft")

;; Code discarded 2016-04-16
;; ;; RatLeCritPos
;; (set-goal "all p,q,r,r0(p<=q -> r<=r0 ->
;;  (p#r0)<=q/r)")
;; (ng #t)
;; (use "PosLeMonTimes")
;; ;; Proof finished.
;; (save "RatLeCritPos")

;; ;; RatLeBoundPos
;; (set-goal "all p,q(
;;  (p#q)<=(2**Succ(PosLog p))/(2**PosLog q))")
;; (assume "p" "q")
;; (use "RatLeCritPos")
;; (use "PosLtToLe")
;; (use "PosLtExpTwoSuccLog")
;; (use "PosLeExpTwoLog")
;; ;; Proof finished.
;; (save "RatLeBoundPos")

;; (pp "PosToNatMinus")
;; all pos,pos0(pos0<pos -> PosToNat(pos--pos0)=pos--pos0)

;; (ppn "PosToNatMinus")

;; (all (pos)
;;      (all (pos0)
;;           ((pos0 PosLt pos)
;;             imp
;;             ((PosToNat (pos PosMinus pos0))
;;               =
;;               ((PosToNat pos) NatMinus (PosToNat pos0))))))

;; RatUMinusCompat
(set-goal "all a,b(a==b -> ~a== ~b)")
(cases)
(assume "k" "p")
(cases)
(assume "j" "q")
(ng)
(assume "kq=jp")
(simp "kq=jp")
(use "Truth")
;; Proof finished.
(save "RatUMinusCompat")

;; RatMinusCompat
(set-goal "all a,b,c,d(a==b -> c==d -> a-c==b-d)")
(assume "a" "b" "c" "d" "a=b" "c=d")
(ng)
(use "RatPlusCompat")
(use "a=b")
(use "RatUMinusCompat")
(use "c=d")
;; Proof finished.
(save "RatMinusCompat")

;; RatAbsCompat
(set-goal "all a,b(a==b -> abs a==abs b)")
(cases)
(cases)
;; 3-5
(assume "p" "p0")
(cases)
(cases)
;; 8-10
(assume "q" "q0")
(ng)
(assume "EqHyp")
(use "EqHyp")
;; 9
(assume "q0")
(ng)
(assume "Absurd")
(use "Absurd")
;; 10
(assume "q" "q0")
(ng)
(assume "Absurd")
(use "EfqAtom")
(use "Absurd")
;; 4
(assume "p0")
(cases)
(cases)
;; 23-25
(assume "q" "q0")
(ng)
(assume "Absurd")
(use "Absurd")
;; 24
(strip)
(use "Truth")
;; 25
(assume "q" "q0")
(ng)
(assume "Absurd")
(use "Absurd")
;; 5
(assume "p" "p0")
(cases)
(cases)
;; 35-37
(assume "q" "q0")
(ng)
(assume "Absurd")
(use "EfqAtom")
(use "Absurd")
;; 36
(assume "q0")
(ng)
(assume "Absurd")
(use "Absurd")
;; 37
(assume "q" "q0")
(ng)
(assume "EqHyp")
(use "EqHyp")
;; Proof finished.
(save "RatAbsCompat")

;; PosExpTwoMinus
(set-goal "all n,m(m<=n -> 2**(n--m)*2**m=2**n)")
(ind)
(assume "m")
(ng)
(assume "m=0")
(simp "m=0")
(use "Truth")
;; Step
(assume "n" "IH")
(cases)
(strip)
(use "Truth")
(assume "m" "m<=n")
(ng)
(use "IH")
(use "m<=n")
;; Proof finished.
(save "PosExpTwoMinus")

;; (ppn "PosExpTwoMinus")

;; (all (n)
;;      (all (m)
;;           ((m NatLe n)
;;             imp
;;             (((2 PosExp (n NatMinus m)) PosTimes (2 PosExp m))
;;               =
;;               (2 PosExp n)))))

;; Code discarded 2016-04-16
;; ;; PosExpTwoMinus
;; (set-goal "all p,q(q<p -> 2**(p--q)*2**q=2**p)")
;; (assume "p" "q" "q<p")
;; (simp "PosToNatMinus")
;; (use "NatExpTwoMinus")
;; (simp "PosToNatLe")
;; (use "PosLtToLe")
;; (use "q<p")
;; (use "q<p")
;; ;; Proof finished.
;; (save "PosExpTwoMinus")

;; RatTimesTwoExp
(set-goal "all i,j 2**i*2**j==2**(i+j)")
;; We need PosExpTwoMinus with p,q for n,m
(assert "all p,q(q<p -> 2**(p--q)*2**q=2**p)")
 (assume "p" "q" "q<p")
 (simp "PosToNatMinus")
 (use "PosExpTwoMinus")
 (simp "PosToNatLe")
 (use "PosLtToLe")
 (use "q<p")
 (use "q<p")
;; Assertion proved
(assume "PosExpTwoMinusPos")
(assert "all p,q 2**p*2**IntN q==2**(p+IntN q)")
(assume "p" "q")
(ng)
(use "PosLeLtCases" (pt "p") (pt "q"))
(assume "p<=q")
(use "PosLeCases" (pt "p") (pt "q"))
(use "p<=q")
(assume "p<q")
(simp "p<q")
(ng)
(cases (pt "p=q"))
(assume "p=q")
(ng)
(simp "p=q")
(use "Truth")
(assume "Useless")
(ng)
(simp "PosTimesComm")
(use "PosExpTwoMinusPos")
(use "p<q")
;; 20
(assume "p=q")
(simp "p=q")
(ng)
(simp "p=q")
(use "Truth")
;; 16
(assume "q<p")
(assert "p=q -> F")
 (assume "p=q")
 (simphyp-with-to "q<p" "p=q" "Absurd")
 (use "Absurd")
(assume "p=q -> F")
(simp "p=q -> F")
(ng)
(drop "p=q -> F")
(assert "p<q -> F")
 (assume "p<q")
 (assert "q<q")
  (use "PosLtTrans" (pt "p"))
  (use "q<p")
  (use "p<q")
 (assume "Absurd")
 (use "Absurd")
(assume "p<q -> F")
(simp "p<q -> F")
(ng)
(drop "p<q -> F")
(simp "PosExpTwoMinusPos")
(use "Truth")
(use "q<p")
;; Assertion proved
(assume "Assertion")
(cases)
;; 62-64
(assume "p")
(cases)
;; 66-68
(assume "q")
(ng)
(use "PosExpTwoPosPlus")
;; 67
(ng)
(use "Truth")
;; 68
(assume "q")
(use "Assertion")
;; 63
(ng)
(strip)
(use "Truth")
;; 64
(assume "q")
(cases)
;; 76-78
(assume "p")
(simp "RatTimesComm")
(simp "IntPlusComm")
(use "Assertion")
;; 77
(ng)
(use "Truth")
;; 78
(assume "p")
(ng)
(simp "PosExpTwoPosPlus")
(use "Truth")
;; Proof finished.
(save "RatTimesTwoExp")

;; RatLePosExpTwo
(set-goal "all p,q (p#q)<=(2**Succ(PosLog p)#2**PosLog q)")
(assume "p" "q")
(ng)
(assert "p<2*2**PosLog p")
 (use "PosLtExpTwoSuccLog")
(assume "Assertion")
(use "PosLeTrans" (pt "2*2**PosLog p*2**PosLog q"))
(use "PosLeMonTimes")
(use "PosLtToLe")
(use "Assertion")
(use "Truth")
(ng)
(use "PosLeMonTimes")
(use "Truth")
(use "PosLeExpTwoLog")
;; Proof finished.
(save "RatLePosExpTwo")

;; RatLePosExpTwoMinus
(set-goal "all n,m (2**n#2**m)<=2**(n--m)")
(ind)
(assume "m")
(ng)
(use "Truth")
(assume "n" "IH")
(cases)
(ng)
(use "Truth")
(assume "m")
(ng)
(use "IH")
;; Proof finished.
(save "RatLePosExpTwoMinus")

;; RatLeBound
(set-goal "all p,q ex n (p#q)<=2**n")
(assume "p" "q")
(ex-intro (pt "Succ(PosLog p)--PosLog q"))
(use "RatLeTrans" (pt "2**Succ(PosLog p)#2**PosLog q"))
(use "RatLePosExpTwo")
(use "RatLePosExpTwoMinus")
;; Proof finished.
(save "RatLeBound")

;; (ppn (pf "(p#q)<=2**n"))
;; (((IntPos p) RatConstr q)
;;   RatLe
;;   ((IntPos (2 PosExp n)) RatConstr 1))

;; We show that (i) RatExp for (p#1) and positive exponents and (2)
;; PosExp (which has nat as exponent type) are isomorphic, using that
;; NatToPos and PosToNat are essentially inverse to each other.

;; RatExpEqPosExpPosToNat
(set-goal "all p,q (p#1)**q=p**(PosToNat q)")
(strip)
(use "Truth")
;; Proof finished.
(save "RatExpEqPosExpPosToNat")

;; (ppn (pf "(p#1)**q=p**(PosToNat q)"))
;; ((((IntPos p) RatConstr 1) RatExp (IntPos q))
;;   =
;;   ((IntPos (p PosExp (PosToNat q))) RatConstr 1))

;; RatExpNatToPosEqPosExp
(set-goal "all p,n(Zero<n -> (p#1)**(NatToPos n)=p**n)")
(assume "p")
(cases)
(assume "Absurd")
(use "EfqAtom")
(use "Absurd")
;; 4
(assume "n" "Useless")
(assert "p**PosToNat(NatToPos(Succ n))=p**Succ n")
 (simp "PosToNatToPosId")
 (use "Truth")
 (use "Truth")
(assume "Assertion")
(simp "<-" "Assertion")
(use "Truth")
;; Proof finished.
(save "RatExpNatToPosEqPosExp")

;; (ppn (pt "(p#1)**(NatToPos n)=p**n"))
;; ((((IntPos p) RatConstr 1) RatExp (IntPos (NatToPos n)))
;;   =
;;   ((IntPos (p PosExp n)) RatConstr 1))

;; RatLeBoundInt
(set-goal "all p,q ex i (p#q)<=2**i")
(assume "p" "q")
(inst-with-to "RatLeBound" (pt "p") (pt "q") "RatLeBoundInst")
(by-assume "RatLeBoundInst" "n" "nProp")
(ex-intro (pt "NatToInt n"))
(use "NatLeCases" (pt "Zero") (pt "n"))
(use "Truth")
;; Case 0<n
(assume "0<n")
(simp "<-" "IntPNatToPosEqNatToInt")
(simp "RatExpNatToPosEqPosExp")
(use "nProp")
(use "0<n")
(use "0<n")
;; Case 0=n
(assume "0=n")
(simphyp-with-to "nProp" "<-" "0=n" "nPropSimp")
(simp "<-" "0=n")
(use "nPropSimp")
;; Proof finished.
(save "RatLeBoundInt")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [p,p0]cRatLeBound p p0

;; (ppn neterm)
;; (lambda p (lambda p0 (NatToInt (p cRatLeBound p0))))

;; RatLeAbsBoundInt
(set-goal "all a ex i abs a<=2**i")
(cases)
(cases) ;3-5
(ng #t)
(use "RatLeBoundInt")
;; 4
(assume "p")
(ex-intro "0")
(use "Truth")
;; 5
(ng #t)
(use "RatLeBoundInt")
;; Proof finished.
(save "RatLeAbsBoundInt")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [a][case a
;;    (k#p -> 
;;    [case k
;;      (p0 -> cRatLeBoundInt p0 p)
;;      (0 -> 0)
;;      (IntN p0 -> cRatLeBoundInt p0 p)])]

;; RatLeAbs
(set-goal "all a a<=abs a")
(cases)
(cases)
;; 3-5
(assume "p" "q")
(ng)
(use "Truth")
;; 4
(assume "q")
(use "Truth")
;; 5
(assume "p" "q")
(ng)
(use "Truth")
;; Proof finished.
(add-rewrite-rule "a<=abs a" "True")

;; RatLeAbsPlus
(set-goal "all a,b abs(a+b)<=abs a+abs b")
(cases)
(assume "k" "p")
(cases)
(assume "j" "q")
(ng)
;; abs(k*q+j*p)*(p*q)<=abs k*q*(p*q)+abs j*p*(p*q)
(use "IntLeTrans" (pt "(abs(k*q)+abs(j*p))*(p*q)"))
(use "IntLeMonTimes")
(use "Truth")
(use "IntLeAbsPlus")
;; 8
(ng)
(use "Truth")
;; Proof finished.
(save "RatLeAbsPlus")
(add-rewrite-rule "abs(a+b)<=abs a+abs b" "True")

;; RatLeAbsMinus
(set-goal "all a,b,c abs(a+ ~b)<=abs(a+ ~c)+abs(c+ ~b)")
(assume "a" "b" "c")
(simp "RatLeCompat" (pt "abs(a+ ~c+c+ ~b)") (pt "abs(a+ ~c)+abs(c+ ~b)"))
(simp "<-" "RatPlusAssoc")
(use "RatLeAbsPlus")
(use "Truth")
(simprat "RatEqvPlusMinus")
(use "Truth")
;; Proof finished.
(save "RatLeAbsMinus")

;; (search-about "Int" "Times" "Mon")
;; (display-pconst "IntAbs")
;; (display-pconst "RatAbs")
;; (display-pconst "RatLe")

;; New attempt: (1#2**p) instead of 1/2**k.  Fits better with rat.
;; New attempt: eps k.  No.  1#2**p is more direct

;; (add-program-constant "RatEps" (py "int=>rat"))
;; (add-token "eps" 'prefix-op (make-term-creator1 "eps" "int"))
;; (add-token-and-type-to-name "eps" (py "int") "RatEps")
;; (add-display (py "rat") (make-display-creator1 "RatEps" "eps" 'prefix-op))

;; ;; (pp (pt "eps k"))

;; (add-computation-rules
;;  "eps 0" "(1#1)"
;;  "eps 1" "(1#2)"
;;  "eps(SZero p)" "eps p*eps p"
;;  "eps(SOne p)" "eps p*eps p*(1#2)"
;;  "eps(IntN p)" "2**p")

;; ;; (pp (nt (pt "eps 2")))
;; ;; (pp (nt (pt "eps 3")))
;; ;; (pp (nt (pt "eps 4")))
;; ;; (pp (nt (pt "eps 5")))
;; ;; (pp (nt (pt "eps 1")))
;; ;; (pp (nt (pt "eps 0")))
;; ;; (pp (nt (pt "eps ~1")))
;; ;; (pp (nt (pt "eps ~4")))

;; ;; RatEpsTotal
;; (set-totality-goal "RatEps")
;; (use "AllTotalElim")
;; (cases)
;; ;; 3-5
;; (ind)
;; ;; 6-8
;; (ng)
;; (use "RatTotalVar")
;; ;; 7
;; (assume "p" "IH")
;; (ng)
;; (use "RatTimesTotal")
;; (use "IH")
;; (use "IH")
;; ;; 8
;; (assume "p" "IH")
;; (ng)
;; (use "RatTimesTotal")
;; (use "RatTimesTotal")
;; (use "IH")
;; (use "IH")
;; (use "RatTotalVar")
;; ;; 4
;; (ng)
;; (use "RatTotalVar")
;; ;; 5
;; (assume "p")
;; (ng)
;; (use "RatTotalVar")
;; ;; Proof finished.
;; (save-totality)

;; Moved to pproof.scm:
;; 2016-04-23.  Make simp usable for RatEqv ==

;; In the following definition of simprat-with x is one of the following.
;; - A number or string identifying a hypothesis form the context.
;; - The name of a theorem or global assumption, but not one whose final
;;   conclusion is a predicate variable.
;; - A closed proof.
;; - A formula with free variables from the context, generating a new goal.
;; Moreover xs is a list consisting of
;; - a number or string identifying a hypothesis form the context,
;; - the name of a theorem or global assumption,
;; - a closed proof,
;; - the string "?" (value of DEFAULT-GOAL-NAME), generating a new goal,
;; - a symbol left or right,
;; - a term, whose free variables are added to the context,
;; - a type, which is substituted for the 1st tvar,
;; - a comprehension term, which is substituted for the 1st pvar.
;; This generates a used formula lhs==rhs with lhs or its normal form present
;; in the goal.  Replace lhs by rhs.  In case "<-" exchange lhs by rhs.

;; (define (simprat-with opt-dir-or-x . x-and-xs-or-xs)
;;   (let* ((num-goals (pproof-state-to-num-goals))
;; 	 (proof (pproof-state-to-proof))
;; 	 (maxgoal (pproof-state-to-maxgoal))
;; 	 (number (num-goal-to-number (car num-goals))))
;;     (set! PPROOF-STATE
;; 	  (apply simprat-with-intern
;; 		 num-goals proof maxgoal opt-dir-or-x x-and-xs-or-xs))
;;     (pproof-state-history-push PPROOF-STATE)
;;     (display-new-goals num-goals number)))

;; (define (simprat-with-intern num-goals proof maxgoal . rest)
;;   (let* ((opt-dir-or-x
;; 	  (if (null? rest)
;; 	      (myerror "simprat-with-intern" "more arguments expected")
;; 	      (car rest)))
;; 	 (left-to-right
;; 	  (not (and (string? opt-dir-or-x) (string=? "<-" opt-dir-or-x))))
;; 	 (x-and-x-list (if left-to-right
;; 			   rest
;; 			   (cdr rest)))
;; 	 (x (if (null? x-and-x-list)
;; 		(myerror "simprat-with-intern" "more arguments expected")
;; 		(car x-and-x-list)))
;; 	 (x-list (cdr x-and-x-list))
;; 	 (num-goal (car num-goals))
;; 	 (goal (num-goal-to-goal num-goal))
;; 	 (drop-info (num-goal-to-drop-info num-goal))
;; 	 (hypname-info (num-goal-to-hypname-info num-goal))
;; 	 (context (goal-to-context goal))
;; 	 (ncvars (goal-to-ncvars goal))
;; 	 (proof-and-new-num-goals-and-maxgoal
;; 	  (if (and (string? x)
;; 		   (let ((info (assoc x (append THEOREMS GLOBAL-ASSUMPTIONS))))
;; 		     (and info
;; 			  (let* ((aconst (cadr info))
;; 				 (aconst-formula (aconst-to-formula aconst))
;; 				 (final-concl
;; 				  (imp-impnc-all-allnc-form-to-final-conclusion
;; 				   aconst-formula)))
;; 			    (and (predicate-form? final-concl)
;; 				 (pvar? (predicate-form-to-predicate
;; 					 final-concl)))))))
;; 	      (myerror "simprat-with-intern" "unexpected aconst name" x)
;; 	      (apply x-and-x-list-to-proof-and-new-num-goals-and-maxgoal
;; 		     num-goal (+ 1 maxgoal) x x-list)))
;; 	 (eqv-proof (car proof-and-new-num-goals-and-maxgoal))
;; 	 (new-num-goals (cadr proof-and-new-num-goals-and-maxgoal))
;; 	 (new-maxgoal (caddr proof-and-new-num-goals-and-maxgoal))
;; 	 (goal-formula (goal-to-formula goal))
;; 	 (used-formula (proof-to-formula eqv-proof))
;; 	 (used-prime-formula
;; 	  (if (prime-form? used-formula) used-formula
;; 	      (myerror "simprat-with-intern" "prime formula expected"
;; 		       used-formula)))
;; 	 (used-nprime-formula (normalize-formula used-prime-formula))
;; 	 (used-kernel
;; 	  (if (atom-form? used-prime-formula)
;; 	      (atom-form-to-kernel used-prime-formula)
;; 	      (myerror "simprat-with-intern" "atom formula expected"
;; 		       used-prime-formula)))
;; 	 (used-nkernel (nt used-kernel))
;; 	 (op (term-in-app-form-to-final-op used-kernel))
;; 	 (nop (term-in-app-form-to-final-op used-nkernel))
;; 	 (ngoal-formula (nf goal-formula)))
;;     (cond
;;      ((and (term-in-const-form? op)
;; 	   (string=? "RatEqv" (const-to-name (term-in-const-form-to-const op)))
;; 	   (let* ((args (term-in-app-form-to-args used-kernel))
;; 		  (lhs (car args))
;; 		  (rhs (cadr args))
;; 		  (type (term-to-type lhs))
;; 		  (var (type-to-new-var type))
;; 		  (varterm (make-term-in-var-form var))
;; 		  (simprat-formula
;; 		   (if left-to-right
;; 		       (formula-gen-subst goal-formula lhs varterm)
;; 		       (formula-gen-subst goal-formula rhs varterm))))
;; 	     (not (formula=? simprat-formula goal-formula))))
;;       (let* ((args (term-in-app-form-to-args used-kernel))
;; 	     (lhs (car args))
;; 	     (rhs (cadr args))
;; 	     (type (term-to-type lhs))
;; 	     (var (type-to-new-var type))
;; 	     (varterm (make-term-in-var-form var))
;; 	     (simprat-formula
;; 	      (if left-to-right
;; 		  (formula-gen-subst goal-formula lhs varterm)
;; 		  (formula-gen-subst goal-formula rhs varterm)))
;; 	     (new-goal ;A(rhs) or A(lhs)
;; 	      (context-and-ncvars-and-formula-to-new-goal
;; 	       context ncvars
;; 	       (formula-subst simprat-formula var
;; 			      (if left-to-right rhs lhs))))
;; 	     (new-num-goal
;; 	      (make-num-goal
;; 	       (+ 1 maxgoal) new-goal drop-info hypname-info))
;; 	     (new-proof ;of A(lhs) or A(rhs)
;; 	      (mk-proof-in-elim-form
;; 	       (rateqv-formula-compat
;; 		 simprat-formula var
;; 		 (if left-to-right lhs rhs)
;; 		 (if left-to-right rhs lhs)
;; 		 eqv-proof new-goal))))
;; 	(make-pproof-state
;; 	 (append (list new-num-goal) new-num-goals (cdr num-goals))
;; 	 (goal-subst proof goal new-proof)
;; 	 new-maxgoal)))
;;      ((and (term-in-const-form? nop)
;; 	   (string=? "RatEqv" (const-to-name (term-in-const-form-to-const nop)))
;; 	   (let* ((args (term-in-app-form-to-args used-nkernel))
;; 		  (lhs (car args))
;; 		  (rhs (cadr args))
;; 		  (type (term-to-type lhs))
;; 		  (var (type-to-new-var type))
;; 		  (varterm (make-term-in-var-form var))
;; 		  (simprat-formula
;; 		   (if left-to-right
;; 		       (formula-gen-subst goal-formula lhs varterm)
;; 		       (formula-gen-subst goal-formula rhs varterm))))
;; 	     (not (formula=? simprat-formula goal-formula))))
;;       (let* ((args (term-in-app-form-to-args used-nkernel))
;; 	     (lhs (car args))
;; 	     (rhs (cadr args))
;; 	     (type (term-to-type lhs))
;; 	     (var (type-to-new-var type))
;; 	     (varterm (make-term-in-var-form var))
;; 	     (simprat-formula
;; 	      (if left-to-right
;; 		  (formula-gen-subst goal-formula lhs varterm)
;; 		  (formula-gen-subst goal-formula rhs varterm)))
;; 	     ;; (all-formula (mk-all var simprat-formula))
;; 	     (new-goal ;A(rhs) or A(lhs)
;; 	      (context-and-ncvars-and-formula-to-new-goal
;; 	       context ncvars
;; 	       (formula-subst simprat-formula var
;; 			      (if left-to-right rhs lhs))))
;; 	     (new-num-goal
;; 	      (make-num-goal
;; 	       (+ 1 maxgoal) new-goal drop-info hypname-info))
;; 	     (new-proof ;of A(lhs) or A(rhs)
;; 	      (mk-proof-in-elim-form
;; 	       (rateqv-formula-compat
;; 		 simprat-formula var
;; 		 (if left-to-right lhs rhs)
;; 		 (if left-to-right rhs lhs)
;; 		 eqv-proof new-goal))))
;; 	(make-pproof-state
;; 	 (append (list new-num-goal) new-num-goals (cdr num-goals))
;; 	 (goal-subst proof goal new-proof)
;; 	 new-maxgoal)))
;;      (else (myerror "simprat-with-intern" "goal cannot be simplified with"
;; 		    used-formula)))))

;; ;; Auxiliary functions

;; ;; Given t(x), x, lhs, rhs and a proof of lhs==rhs, rateqv-term-compat
;; ;; returns a proof of t(lhs)==t(rhs).  Here t(x), x, lhs, rhs are of
;; ;; type rat.

;; (define (rateqv-term-compat term var term1 term2 eqv-proof)
;;   (cond
;;    ((not (member var (term-to-free term)))
;;     (make-proof-in-aconst-form truth-aconst)) ;a==a -> True is a rewrite rule
;;    ((term-in-var-form? term) eqv-proof) ;of term1==term2, i.e., lhs==rhs
;;    ((term-in-app-form? term)
;;     (let* ((op (term-in-app-form-to-final-op term))
;; 	   (args (term-in-app-form-to-args term))
;; 	   (name (if (not (term-in-const-form? op))
;; 		     (myerror "rateqv-term-compat"
;; 			      "term in constant form expected" op)
;; 		     (string-append
;; 		      (const-to-name (term-in-const-form-to-const op))
;; 		      "Compat")))
;; 	   (unary-compat-names
;; 	    (list "RatUMinusCompat" "RatAbsCompat"))
;; 	   (binary-compat-names
;; 	    (list "RatPlusCompat" "RatTimesCompat" "RatMinusCompat")))
;;       (cond
;;        ((member name unary-compat-names)
;; 	(mk-proof-in-elim-form ;of ~t(lhs)== ~t(rhs)
;; 	 (make-proof-in-aconst-form ;of all a,b(a==b -> ~a== ~b))
;; 	  (theorem-name-to-aconst name))
;; 	 (term-subst (car args) var term1) ;t(lhs)
;; 	 (term-subst (car args) var term2) ;t(rhs)
;; 	 ;; (term-subst term var term1) ;t(lhs)
;; 	 ;; (term-subst term var term2) ;t(rhs)
;; 	 (rateqv-term-compat (car args) var term1 term2 eqv-proof)))
;;        ((member name binary-compat-names)
;; 	(mk-proof-in-elim-form ;of t(lhs)+s(lhs)==t(rhs)+s(rhs)
;; 	 (make-proof-in-aconst-form ;of all a,b,c,d(a==b -> c==d -> a+c==b+d))
;; 	  (theorem-name-to-aconst name))
;; 	 (term-subst (car args) var term1) ;t(lhs)
;; 	 (term-subst (car args) var term2) ;t(rhs)
;; 	 (term-subst (cadr args) var term1) ;s(lhs)
;; 	 (term-subst (cadr args) var term2) ;s(rhs)
;; 	 ;; (term-subst term var term1) ;t(lhs)+s(lhs)
;; 	 ;; (term-subst term var term2) ;t(rhs)+s(rhs)
;; 	 (rateqv-term-compat ;proves t(lhs)==t(rhs) from lhs==rhs by IH
;; 	  (car args) var term1 term2 eqv-proof)
;; 	 (rateqv-term-compat ;proves s(lhs)==s(rhs) from lhs==rhs by IH
;; 	  (cadr args) var term1 term2 eqv-proof)))
;;        (else (apply myerror "rateqv-term-compat" name
;; 		    "expected to be among" (append unary-compat-names
;; 						   binary-compat-names))))))
;;    (else (myerror "rateqv-term-compat" "unexpected term" term))))

;; ;; Given A(x), x, lhs, rhs and proofs eqv-proof of lhs==rhs and new-goal
;; ;; of A(rhs) returns a proof of A(lhs).  Here x, lhs, rhs are of type
;; ;; rat.

;; (define (rateqv-formula-compat fla var term1 term2 eqv-proof new-goal)
;;   (cond
;;    ((not (member var (formula-to-free fla))) new-goal)
;;    ((atom-form? fla)
;;     (let* ((kernel (atom-form-to-kernel fla)) ;t(x)<=s(x)
;; 	   (op (if (not (term-in-app-form? kernel))
;; 		   (myerror "rateqv-formula-compat"
;; 			    "term in application form expected" kernel)
;; 		   (term-in-app-form-to-final-op kernel)))
;; 	   (args (term-in-app-form-to-args kernel)) ;(t(x) s(x))
;; 	   (name (if (not (term-in-const-form? op))
;; 		     (myerror "rateqv-formula-compat"
;; 			      "term in constant form expected" op)
;; 		     (string-append
;; 		      (const-to-name (term-in-const-form-to-const op))
;; 		      "Compat")))
;; 	   (compat-names (list "RatLeCompat" "RatEqvCompat")))
;;       (if
;;        (member name compat-names)
;;        (let* ((elim-proof1 ;of t(lhs)==t(rhs)
;; 	       (rateqv-term-compat (car args) var term1 term2 eqv-proof))
;; 	      (elim-proof2 ;of s(lhs)==s(rhs)
;; 	       (rateqv-term-compat (cadr args) var term1 term2 eqv-proof))
;; 	      (elim-proof3 ;of (t(lhs)<=s(lhs))=(t(rhs)<=s(rhs))
;; 	       (mk-proof-in-elim-form
;; 		(make-proof-in-aconst-form (theorem-name-to-aconst name))
;; 		;; (theorem-name-to-proof name) ;all a,b,c,d(a==b -> c==d ->
;; 		;; 			;                 (a<=c)=(b<=d))
;; 		(term-subst (car args) var term1) ;t(lhs)
;; 		(term-subst (car args) var term2) ;t(rhs)
;; 		(term-subst (cadr args) var term1) ;s(lhs)
;; 		(term-subst (cadr args) var term2) ;s(rhs)
;; 		elim-proof1 elim-proof2))
;; 	      (eq-fla (proof-to-formula elim-proof3)) 
;; 	      (booleterms (term-in-app-form-to-args
;; 			   (atom-form-to-kernel eq-fla)))
;; 	      (booleterm1 (car booleterms)) ;t(lhs)<=s(lhs)
;; 	      (booleterm2 (cadr booleterms))) ;t(rhs)<=s(rhs)
;; 	 (mk-proof-in-elim-form
;; 	  (make-proof-in-aconst-form
;; 	   (theorem-name-to-aconst "BooleEqToAeqRight"))
;; 	  ;; (theorem-name-to-proof "BooleEqToAeqRight")
;; 					;of all boole1,boole2(boole1=boole2 ->
;; 					;                     boole2 -> boole1)
;; 	  booleterm1 booleterm2 elim-proof3 new-goal))
;;        (myerror "rateqv-formula-compat" "RatLeCompat or RatEqvCompat expected"
;; 		name))))
;;    (else (myerror "rateqv-formula-compat" "not implemented for formula" fla))))

;; (define (simprat opt-dir-or-x . x-and-xs-or-xs)
;;   (let* ((num-goals (pproof-state-to-num-goals))
;; 	 (proof (pproof-state-to-proof))
;; 	 (maxgoal (pproof-state-to-maxgoal))
;; 	 (number (num-goal-to-number (car num-goals)))
;; 	 (simprat-result
;; 	  (apply simprat-intern
;; 		 num-goals proof maxgoal opt-dir-or-x x-and-xs-or-xs)))
;;     (if (not simprat-result)
;; 	(begin (display-comment "no simplification possible")
;; 	       (if COMMENT-FLAG (newline)))
;; 	(begin
;; 	  (set! PPROOF-STATE simprat-result)
;; 	  (pproof-state-history-push PPROOF-STATE)
;; 	  (display-new-goals num-goals number)))))

;; (define (simprat-intern num-goals proof
;; 		     maxgoal . opt-dir-and-x-and-elab-path-and-terms)
;;   (let* ((opt-dir (if (null? opt-dir-and-x-and-elab-path-and-terms)
;; 		      (myerror "simprat-intern" "more arguments expected")
;; 		      (car opt-dir-and-x-and-elab-path-and-terms)))
;; 	 (left-to-right (not (and (string? opt-dir) (string=? "<-" opt-dir))))
;; 	 (x-and-elab-path-and-terms
;; 	  (if left-to-right
;; 	      opt-dir-and-x-and-elab-path-and-terms
;; 	      (cdr opt-dir-and-x-and-elab-path-and-terms)))
;; 	 (x (if (null? x-and-elab-path-and-terms)
;; 		(myerror "simprat-intern" "more arguments expected")
;; 		(car x-and-elab-path-and-terms)))
;; 	 (elab-path-and-terms (cdr x-and-elab-path-and-terms))
;; 	 (num-goal (car num-goals))
;; 	 (goal (num-goal-to-goal num-goal))
;; 	 (hypname-info (num-goal-to-hypname-info num-goal))
;; 	 (context (goal-to-context goal))
;; 	 (ncvars (goal-to-ncvars goal))
;; 	 (avars (context-to-avars context))
;; 	 (maxhyp (length avars))
;; 	 (goal-formula (goal-to-formula goal))
;; 	 (leaf (if (formula-form? x)
;; 		   (context-and-ncvars-and-formula-to-new-goal
;; 		    context ncvars x)
;; 		   (hyp-info-to-leaf num-goal x)))
;; 	 (used-formula
;; 	  (unfold-formula (if (formula-form? x) x (proof-to-formula leaf))))
;; 	 (sig-vars (context-to-vars context))
;; 	 (sig-tvars-and-sig-vars
;; 	  (if (assoc x (append THEOREMS GLOBAL-ASSUMPTIONS))
;; 	      sig-vars
;; 	      (append (formula-to-tvars used-formula) sig-vars)))
;; 	 (elab-path (do ((l elab-path-and-terms (cdr l))
;; 			 (res '() (if (memq (car l) '(left right))
;; 				      (cons (car l) res)
;; 				      res)))
;; 			((null? l) (reverse res))))
;; 	 (xs-and-vars-and-toinst1
;; 	  (apply
;; 	   fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data
;; 	   used-formula sig-tvars-and-sig-vars
;; 	   goal-formula left-to-right
;; 	   elab-path))
;; 	 (xs-and-vars-and-toinst
;; 	  (if xs-and-vars-and-toinst1
;; 	      xs-and-vars-and-toinst1
;; 	      (apply
;; 	       fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data
;; 	       (normalize-formula used-formula)
;; 	       sig-tvars-and-sig-vars
;; 	       (normalize-formula goal-formula)
;; 	       left-to-right
;; 	       elab-path))))
;;     (if
;;      (not xs-and-vars-and-toinst)
;;      #f
;;      (let* ((xs (car xs-and-vars-and-toinst))
;; 	    (vars (cadr xs-and-vars-and-toinst))
;; 	    (toinst (caddr xs-and-vars-and-toinst))
;; 	    (terms (do ((l elab-path-and-terms (cdr l))
;; 			(res '() (if (memq (car l) '(left right))
;; 				     res
;; 				     (cons (car l) res))))
;; 		       ((null? l) (reverse res))))
;; 	    (subst (if (<= (length vars) (length terms))
;; 		       (map list vars (list-head terms (length vars)))
;; 		       empty-subst))
;; 	    (subst-xs (map (lambda (x) (if (term-form? x)
;; 					   (term-substitute x subst)
;; 					   x))
;; 			   xs))
;; 	    (types (let ((info1 (assoc x THEOREMS))
;; 			 (info2 (assoc x GLOBAL-ASSUMPTIONS))
;; 			 (tsubst (list-transform-positive toinst
;; 				   (lambda (x) (tvar-form? (car x))))))
;; 		     (if
;; 		      (and (or info1 info2) (pair? tsubst)) ;else '()
;; 		      (let* ((aconst (if info1
;; 					 (theorem-name-to-aconst x)
;; 					 (global-assumption-name-to-aconst x)))
;; 			     (fla (aconst-to-formula aconst))
;; 			     (tvars (formula-to-tvars fla)))
;; 			(map (lambda (tvar) (type-substitute tvar tsubst))
;; 			     tvars))
;; 		      '()))))
;;        (if (> (length vars) (length terms))
;; 	   (apply myerror
;; 		  "simprat-intern" "more terms expected, to be substituted for"
;; 		  (list-tail vars (length terms))))
;;        (if (and COMMENT-FLAG (< (length vars) (length terms)))
;; 	   (begin
;; 	     (comment "warning: superfluous terms")
;; 	     (for-each comment
;; 		       (map term-to-string (list-tail terms (length vars))))))
;;        (apply simprat-with-intern
;; 	      (if left-to-right
;; 		  (append (list num-goals proof maxgoal x)
;; 			  (append types subst-xs))
;; 		  (append (list num-goals proof maxgoal "<-" x)
;; 			  (append types subst-xs))))))))

;; ;; fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data is #f if
;; ;; (a) no atomic or negated atomic head of formula and also (b) no lhs
;; ;; (resp. rhs) of an equality head of formula is a pattern in the goal
;; ;; formula.  Otherwise the following data are returned: (1) the
;; ;; arguments xs for the hypothesis x that produce the instance, (2)
;; ;; vars (from xs) whose instantiations cannot be inferred, hence need
;; ;; to be provided, (3) a tosubst that produces the instance.

;; (define (fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data
;; 	 used-formula sig-tvars-and-sig-vars goal-formula
;; 	 left-to-right . elab-path)
;;   (let ((match-res
;; 	 (cond
;; 	  ((imp-form? used-formula)
;; 	   (let ((prem (imp-form-to-premise used-formula))
;; 		 (concl (imp-form-to-conclusion used-formula)))
;; 	     (and (atom-form? prem)
;; 		  (classical-formula=? falsity concl)
;; 		  (let ((kernel (atom-form-to-kernel prem)))
;; 		    (first-match sig-tvars-and-sig-vars
;; 				 kernel goal-formula)))))
;; 	  ((impnc-form? used-formula)
;; 	   (let ((prem (impnc-form-to-premise used-formula))
;; 		 (concl (impnc-form-to-conclusion used-formula)))
;; 	     (and (atom-form? prem)
;; 		  (classical-formula=? falsity concl)
;; 		  (let ((kernel (atom-form-to-kernel prem)))
;; 		    (first-match sig-tvars-and-sig-vars
;; 				 kernel goal-formula)))))
;; 	  ((atom-form? used-formula)
;; 	   (let* ((kernel (atom-form-to-kernel used-formula))
;; 		  (op (term-in-app-form-to-final-op kernel))
;; 		  (res (first-match sig-tvars-and-sig-vars
;; 				    kernel goal-formula)))
;; 	     (if res res
;; 		 (if (and (term-in-const-form? op)
;; 		      (member (const-to-name
;; 			       (term-in-const-form-to-const op))
;; 			      (list "=" "RatEqv")))
;; 		     (let* ((args (term-in-app-form-to-args kernel))
;; 			    (lhs (car args))
;; 			    (rhs (cadr args)))
;; 		       (if left-to-right
;; 			   (first-match sig-tvars-and-sig-vars
;; 					lhs goal-formula)
;; 			   (first-match sig-tvars-and-sig-vars
;; 					rhs goal-formula)))
;; 		     #f))))
;; 	  ;; ((atom-form? used-formula)
;; 	  ;;  (let ((kernel (atom-form-to-kernel used-formula)))
;; 	  ;;    (first-match sig-tvars-and-sig-vars
;; 	  ;; 		  kernel goal-formula)))
;; 	  ;; ((atom-form? used-formula)
;; 	  ;;  (let* ((kernel (atom-form-to-kernel used-formula))
;; 	  ;; 	  (op (term-in-app-form-to-final-op kernel)))
;; 	  ;;    (if (and (term-in-const-form? op)
;; 	  ;; 	      (member (const-to-name
;; 	  ;; 		       (term-in-const-form-to-const op))
;; 	  ;; 		      (list "=" "RatEqv")))
;; 	  ;; 	 (let* ((args (term-in-app-form-to-args kernel))
;; 	  ;; 		(lhs (car args))
;; 	  ;; 		(rhs (cadr args)))
;; 	  ;; 	   (if left-to-right
;; 	  ;; 	       (first-match sig-tvars-and-sig-vars
;; 	  ;; 			    lhs goal-formula)
;; 	  ;; 	       (first-match sig-tvars-and-sig-vars
;; 	  ;; 			    rhs goal-formula)))
;; 	  ;; 	 #f)))
;; 	  ((predicate-form? used-formula)
;; 	   (let ((predicate (predicate-form-to-predicate used-formula)))
;; 	     (if (idpredconst-form? predicate)
;; 		 (if (string=? "EqD" (idpredconst-to-name predicate))
;; 		     (let* ((args (predicate-form-to-args used-formula))
;; 			    (lhs (car args))
;; 			    (rhs (cadr args)))
;; 		       (if left-to-right
;; 			   (first-match sig-tvars-and-sig-vars
;; 					lhs goal-formula)
;; 			   (first-match sig-tvars-and-sig-vars
;; 					rhs goal-formula)))
;; 		     #f)
;; 		 #f)))
;; 	  (else #f))))
;;     (if
;;      match-res
;;      (list '() '() match-res)
;;      (cond
;;       ((atom-form? used-formula) #f)
;;       ((ex-form? used-formula) #f)
;;       ((imp-form? used-formula)
;;        (let* ((concl (imp-form-to-conclusion used-formula))
;; 	      (prev
;; 	       (apply
;; 		fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data
;; 		concl sig-tvars-and-sig-vars
;; 		goal-formula left-to-right
;; 		elab-path)))
;; 	 (if (not prev)
;; 	     #f
;; 	     (let* ((xs (car prev))
;; 		    (vars (cadr prev))
;; 		    (toinst (caddr prev)))
;; 	       (list (cons DEFAULT-GOAL-NAME xs) vars toinst)))))
;;       ((impnc-form? used-formula)
;;        (let* ((concl (impnc-form-to-conclusion used-formula))
;; 	      (prev
;; 	       (apply
;; 		fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data
;; 		concl sig-tvars-and-sig-vars
;; 		goal-formula left-to-right
;; 		elab-path)))
;; 	 (if (not prev)
;; 	     #f
;; 	     (let* ((xs (car prev))
;; 		    (vars (cadr prev))
;; 		    (toinst (caddr prev)))
;; 	       (list (cons DEFAULT-GOAL-NAME xs) vars toinst)))))
;;        ((all-form? used-formula)
;; 	(let* ((var (all-form-to-var used-formula))
;; 	       (kernel (all-form-to-kernel used-formula))
;; 	       (new-var (var-to-new-var var))
;; 	       (new-kernel
;; 		(formula-subst kernel var (make-term-in-var-form new-var)))
;; 	       (prev
;; 		(apply
;; 		 fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data
;; 		 new-kernel sig-tvars-and-sig-vars
;; 		 goal-formula left-to-right
;; 		 elab-path)))
;; 	  (if (not prev)
;; 	      #f
;; 	      (let* ((xs (car prev))
;; 		     (vars (cadr prev))
;; 		     (toinst (caddr prev))
;; 		     (info (assoc new-var toinst)))
;; 		(if
;; 		 info ;instance found by matching
;; 		 (list ;insert instance into xs
;; 		  (cons (cadr info) xs) vars toinst)
;; 		 (list ;else insert new-var into xs, and new-var to vars
;; 		  (cons (make-term-in-var-form new-var) xs)
;; 		  (cons new-var vars)
;; 		  toinst))))))
;;        ((allnc-form? used-formula)
;; 	(let* ((var (allnc-form-to-var used-formula))
;; 	       (kernel (allnc-form-to-kernel used-formula))
;; 	       (new-var (var-to-new-var var))
;; 	       (new-kernel
;; 		(formula-subst kernel var (make-term-in-var-form new-var)))
;; 	       (prev
;; 		(apply
;; 		 fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data
;; 		 new-kernel sig-tvars-and-sig-vars
;; 		 goal-formula left-to-right
;; 		 elab-path)))
;; 	  (if (not prev)
;; 	      #f
;; 	      (let* ((xs (car prev))
;; 		     (vars (cadr prev))
;; 		     (toinst (caddr prev))
;; 		     (info (assoc new-var toinst)))
;; 		(if
;; 		 info ;instance found by matching
;; 		 (list ;insert instance into xs
;; 		  (cons (cadr info) xs) vars toinst)
;; 		 (list ;else insert new-var into xs, and new-var to vars
;; 		  (cons (make-term-in-var-form new-var) xs)
;; 		  (cons new-var vars)
;; 		  toinst))))))
;;        ((or (and-form? used-formula)
;; 	    (andd-form? used-formula)
;; 	    (andl-form? used-formula)
;; 	    (andr-form? used-formula)
;; 	    (andu-form? used-formula))
;; 	(let ((left-conjunct (bicon-form-to-left used-formula))
;; 	      (right-conjunct (bicon-form-to-right used-formula)))
;; 	  (if
;; 	   (pair? elab-path)
;; 	   (let* ((direction (car elab-path))
;; 		  (conjunct (cond ((eq? 'left direction) left-conjunct)
;; 				  ((eq? 'right direction) right-conjunct)
;; 				  (else (myerror "left or right expected"
;; 						 direction))))
;; 		  (prev
;; 		   (apply
;; 		    fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data
;; 		    conjunct sig-tvars-and-sig-vars
;; 		    goal-formula left-to-right
;; 		    (cdr elab-path))))
;; 	     (if (not prev)
;; 		 #f
;; 		 (let* ((xs (car prev))
;; 			(vars (cadr prev))
;; 			(toinst (caddr prev)))
;; 		   (list (cons direction xs) vars toinst))))
;; 	   (let ((prev1
;; 		  (fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data
;; 		   left-conjunct sig-tvars-and-sig-vars
;; 		   goal-formula left-to-right)))
;; 	     (if
;; 	      prev1
;; 	      (let* ((xs (car prev1))
;; 		     (vars (cadr prev1))
;; 		     (toinst (caddr prev1)))
;; 		(list (cons 'left xs) vars toinst))
;; 	      (let ((prev2
;; 		     (fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data
;; 		      right-conjunct sig-tvars-and-sig-vars
;; 		      goal-formula left-to-right)))
;; 		(if prev2
;; 		    (let* ((xs (car prev2))
;; 			   (vars (cadr prev2))
;; 			   (toinst (caddr prev2)))
;; 		      (list (cons 'right xs) vars toinst))
;; 		    #f)))))))
;;        ((predicate-form? used-formula) #f)
;;        (else (myerror
;; 	      "fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data"
;; 	      "formula expected"
;; 	      used-formula))))))

;; (define (fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data
;; 	 used-formula sig-tvars-and-sig-vars goal-formula
;; 	 left-to-right . elab-path)
;;   (let ((match-res
;; 	 (or (and (imp-form? used-formula)
;; 		  (let ((prem (imp-form-to-premise used-formula))
;; 			(concl (imp-form-to-conclusion used-formula)))
;; 		    (and (atom-form? prem)
;; 			 (classical-formula=? falsity concl)
;; 			 (let ((kernel (atom-form-to-kernel prem)))
;; 			   (first-match sig-tvars-and-sig-vars
;; 					kernel goal-formula)))))
;; 	     (and (impnc-form? used-formula)
;; 		  (let ((prem (impnc-form-to-premise used-formula))
;; 			(concl (impnc-form-to-conclusion used-formula)))
;; 		    (and (atom-form? prem)
;; 			 (classical-formula=? falsity concl)
;; 			 (let ((kernel (atom-form-to-kernel prem)))
;; 			   (first-match sig-tvars-and-sig-vars
;; 					kernel goal-formula)))))
;; 	     (and (atom-form? used-formula)
;; 		  (let ((kernel (atom-form-to-kernel used-formula)))
;; 		    (first-match sig-tvars-and-sig-vars
;; 				 kernel goal-formula)))
;; 	     (and (atom-form? used-formula)
;; 		  (let* ((kernel (atom-form-to-kernel used-formula))
;; 			 (op (term-in-app-form-to-final-op kernel)))
;; 		    (and
;; 		     (term-in-const-form? op)`
;; 		     (member (const-to-name (term-in-const-form-to-const op))
;; 			     (list "=" "RatEqv"))
;; 		     (let* ((args (term-in-app-form-to-args kernel))
;; 			    (lhs (car args))
;; 			    (rhs (cadr args)))
;; 		       (if left-to-right
;; 			   (first-match sig-tvars-and-sig-vars
;; 					lhs goal-formula)
;; 			   (first-match sig-tvars-and-sig-vars
;; 					rhs goal-formula))))))
;; 	     (and (predicate-form? used-formula)
;; 		  (let ((predicate (predicate-form-to-predicate
;; 				    used-formula)))
;; 		    (and
;; 		     (idpredconst-form? predicate)
;; 		     (string=? "EqD" (idpredconst-to-name predicate))
;; 		     (let* ((args (predicate-form-to-args used-formula))
;; 			    (lhs (car args))
;; 			    (rhs (cadr args)))
;; 		       (if left-to-right
;; 			   (first-match sig-tvars-and-sig-vars
;; 					lhs goal-formula)
;; 			   (first-match sig-tvars-and-sig-vars
;; 					rhs goal-formula)))))))))
;;     (if
;;      match-res
;;      (list '() '() match-res)
;;      (cond
;;       ((atom-form? used-formula) #f)
;;       ((ex-form? used-formula) #f)
;;       ((imp-form? used-formula)
;;        (let* ((concl (imp-form-to-conclusion used-formula))
;; 	      (prev
;; 	       (apply
;; 		fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data
;; 		concl sig-tvars-and-sig-vars
;; 		goal-formula left-to-right
;; 		elab-path)))
;; 	 (if (not prev)
;; 	     #f
;; 	     (let* ((xs (car prev))
;; 		    (vars (cadr prev))
;; 		    (toinst (caddr prev)))
;; 	       (list (cons DEFAULT-GOAL-NAME xs) vars toinst)))))
;;       ((impnc-form? used-formula)
;;        (let* ((concl (impnc-form-to-conclusion used-formula))
;; 	      (prev
;; 	       (apply
;; 		fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data
;; 		concl sig-tvars-and-sig-vars
;; 		goal-formula left-to-right
;; 		elab-path)))
;; 	 (if (not prev)
;; 	     #f
;; 	     (let* ((xs (car prev))
;; 		    (vars (cadr prev))
;; 		    (toinst (caddr prev)))
;; 	       (list (cons DEFAULT-GOAL-NAME xs) vars toinst)))))
;;        ((all-form? used-formula)
;; 	(let* ((var (all-form-to-var used-formula))
;; 	       (kernel (all-form-to-kernel used-formula))
;; 	       (new-var (var-to-new-var var))
;; 	       (new-kernel
;; 		(formula-subst kernel var (make-term-in-var-form new-var)))
;; 	       (prev
;; 		(apply
;; 		 fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data
;; 		 new-kernel sig-tvars-and-sig-vars
;; 		 goal-formula left-to-right
;; 		 elab-path)))
;; 	  (if (not prev)
;; 	      #f
;; 	      (let* ((xs (car prev))
;; 		     (vars (cadr prev))
;; 		     (toinst (caddr prev))
;; 		     (info (assoc new-var toinst)))
;; 		(if
;; 		 info ;instance found by matching
;; 		 (list ;insert instance into xs
;; 		  (cons (cadr info) xs) vars toinst)
;; 		 (list ;else insert new-var into xs, and new-var to vars
;; 		  (cons (make-term-in-var-form new-var) xs)
;; 		  (cons new-var vars)
;; 		  toinst))))))
;;        ((allnc-form? used-formula)
;; 	(let* ((var (allnc-form-to-var used-formula))
;; 	       (kernel (allnc-form-to-kernel used-formula))
;; 	       (new-var (var-to-new-var var))
;; 	       (new-kernel
;; 		(formula-subst kernel var (make-term-in-var-form new-var)))
;; 	       (prev
;; 		(apply
;; 		 fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data
;; 		 new-kernel sig-tvars-and-sig-vars
;; 		 goal-formula left-to-right
;; 		 elab-path)))
;; 	  (if (not prev)
;; 	      #f
;; 	      (let* ((xs (car prev))
;; 		     (vars (cadr prev))
;; 		     (toinst (caddr prev))
;; 		     (info (assoc new-var toinst)))
;; 		(if
;; 		 info ;instance found by matching
;; 		 (list ;insert instance into xs
;; 		  (cons (cadr info) xs) vars toinst)
;; 		 (list ;else insert new-var into xs, and new-var to vars
;; 		  (cons (make-term-in-var-form new-var) xs)
;; 		  (cons new-var vars)
;; 		  toinst))))))
;;        ((or (and-form? used-formula)
;; 	    (andd-form? used-formula)
;; 	    (andl-form? used-formula)
;; 	    (andr-form? used-formula)
;; 	    (andu-form? used-formula))
;; 	(let ((left-conjunct (bicon-form-to-left used-formula))
;; 	      (right-conjunct (bicon-form-to-right used-formula)))
;; 	  (if
;; 	   (pair? elab-path)
;; 	   (let* ((direction (car elab-path))
;; 		  (conjunct (cond ((eq? 'left direction) left-conjunct)
;; 				  ((eq? 'right direction) right-conjunct)
;; 				  (else (myerror "left or right expected"
;; 						 direction))))
;; 		  (prev
;; 		   (apply
;; 		    fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data
;; 		    conjunct sig-tvars-and-sig-vars
;; 		    goal-formula left-to-right
;; 		    (cdr elab-path))))
;; 	     (if (not prev)
;; 		 #f
;; 		 (let* ((xs (car prev))
;; 			(vars (cadr prev))
;; 			(toinst (caddr prev)))
;; 		   (list (cons direction xs) vars toinst))))
;; 	   (let ((prev1
;; 		  (fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data
;; 		   left-conjunct sig-tvars-and-sig-vars
;; 		   goal-formula left-to-right)))
;; 	     (if
;; 	      prev1
;; 	      (let* ((xs (car prev1))
;; 		     (vars (cadr prev1))
;; 		     (toinst (caddr prev1)))
;; 		(list (cons 'left xs) vars toinst))
;; 	      (let ((prev2
;; 		     (fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data
;; 		      right-conjunct sig-tvars-and-sig-vars
;; 		      goal-formula left-to-right)))
;; 		(if prev2
;; 		    (let* ((xs (car prev2))
;; 			   (vars (cadr prev2))
;; 			   (toinst (caddr prev2)))
;; 		      (list (cons 'right xs) vars toinst))
;; 		    #f)))))))
;;        ((predicate-form? used-formula) #f)
;;        (else (myerror
;; 	      "fla-and-sig-tvars-and-vars-and-goal-fla-to-fst-match-data"
;; 	      "formula expected"
;; 	      used-formula))))))

;; Test

;; (set-goal "all a,b(a==b -> 0<=a)")
;; (assume "a" "b" "EqHyp")
;; (simprat "EqHyp")

;; (define proof (current-proof))
;; (define nproof (np proof))
;; (cdp nproof)
;; (proof-to-expr-with-formulas nproof)

;; (set-goal "all a,b(a==b -> 0<=a+b)")
;; (assume "a" "b" "EqHyp")
;; (simprat "EqHyp")

;; (set-goal "all a,b(a==b -> 0<= ~a)")
;; (assume "a" "b" "EqHyp")
;; (simprat "EqHyp")

;; (set-goal "all k eps(IntS k)+eps(IntS k)==eps k")
;; (cases)
;; ;; 2-4
;; (ind)
;; ;; 5-7
;; (ng)
;; (use "Truth")
;; ;; 6
;; (assume "p" "IH")
;; (ng)
;; (simprat "<-" "RatTimesPlusDistr")
;; (simprat (pf "(1#2)+(1#2)==1"))
;; (ng)
;; (use "Truth")
;; (ng)
;; (use "Truth")
;; ;; 7
;; (assume "p" "IH")
;; (ng)

;; End of tests

;; As further examples of simprat we prove some inequalities useful
;; later for estimates.

;; RatExpPosS
(set-goal "all a,r a**PosS r==a**r*a")
(assert "all a,r a**PosToNat(PosS r)==a**PosToNat r*a")
(cases)
(cases)
;; 5-7
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
;; 6
(assume "p" "r")
(simp "<-" "IntPNatToPosEqNatToInt")
(simp "RatExp0CompRule")
(simp "PosToNatToPosId")
(simp "<-" "IntPNatToPosEqNatToInt")
(simp "NatToPosToNatId")
(ng)
(use "Truth")
(use "NatLt0Pos")
(simp "SuccPosPred")
(use "Truth")
(use "Truth")
(use "NatLt0Pos")
;; 7
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

(set-goal "all p (1#2**PosS p)+(1#2**PosS p)==(1#2**p)")
(assume "p")
(assert "(1#2)**PosS p+(1#2)**PosS p==(1#2)**p")
 (simprat "RatExpPosS")
 (simprat "<-" "RatTimesPlusDistr")
 (ng)
 (use "Truth")
(assume "Assertion")
(use "Assertion")
;; Proof finished.
(save "RatPlusHalfExpPosS")

(set-goal "all p (1#2)**PosS p+(1#2)**PosS p==(1#2)**p")
(assume "p")
(simprat "RatExpPosS")
(simprat "<-" "RatTimesPlusDistr")
(ng)
(use "Truth")
;; Proof finished.

(set-goal "all p (1#2)**(p+1)+(1#2)**(p+1)==(1#2)**p")
(assume "p")
(assert "p+1=PosS p")
 (use "Truth")
(assume "p+1=PosS p")
(simp "p+1=PosS p")
(drop "p+1=PosS p")
(simprat "RatExpPosS")
(simprat "<-" "RatTimesPlusDistr")
(ng)
(use "Truth")
;; Proof finished.

(set-goal "all p,r p**PosS r=p**r*p")
(assume "p" "r")
(simp "SuccPosPred")
(use "Truth")
(use "Truth")
;; Proof finished.

(set-goal "all p,r p**(r+1)=p**r*p")
(assume "p" "r")
(ng)
(simp "SuccPosPred")
(use "Truth")
(use "Truth")
;; Proof finished.

;; Need PosMaxUB1 (done 2016-04-30) RatLeAntiSym (done as well)
;; (see global assumptions in lib/real.scm)

;; 2016-04-17.  Prove axioms of an ordered field for rat, with RatEqv
;; == as equality.  Define RatUDiv.

;; 2015-11-29.  Done up to this point.

;; Added rules for RatPlus.  Goal: {1} Bring / out.  (2) Delete /.

;; (add-rewrite-rule "(a1/b1)+(a2/b2)" "(a1*b2+a2*b1)/(b1*b2)")
;; (add-rewrite-rule "a1+a2/b2" "(a1*b2+a2)/b2")
;; (add-rewrite-rule "a1/b1+a2" "(a1+a2*b1)/b1")

;; (add-rewrite-rule "(a1/b1)+(j#q)" "(a1*q+j*b1)/(b1*q)")
;; (add-rewrite-rule "(k#p)+(a2/b2)" "(k*b2+a2*p)/(p*b2)")
;; ;; The following leads to non-termination for a*b+1
;; ;; (add-rewrite-rule "a1+(j#q)" "(a1*q+j)/q")
;; ;; (add-rewrite-rule "(k#p)+a2" "(k+a2*p)/p")

;; ;; Added 2007-08-28

;; (add-rewrite-rule "a+(RatConstr IntZero One)" "a")
;; (add-rewrite-rule "(RatConstr IntZero One)+a" "a")
;; (add-rewrite-rule "a1+(a2+a3)" "a1+a2+a3")

;; (add-rewrite-rule "(a1/b1)-(a2/b2)" "(a1*b2-a2*b1)/(b1*b2)")
;; (add-rewrite-rule "a1-a2/b2" "(a1*b2-a2)/b2")
;; (add-rewrite-rule "a1/b1-a2" "(a1-a2*b1)/b1")

;; (add-rewrite-rule "(a1/b1)-(j#q)" "(a1*q-j*b1)/(b1*q)")
;; (add-rewrite-rule "(k#p)-(a2/b2)" "(k*b2-a2*p)/(p*b2)")
;; ;; (add-rewrite-rule "a1-(j#q)" "(a1*q-j)/q")
;; ;; (add-rewrite-rule "(k#p)-a2" "(k-a2*p)/p")

;; ;; Added 2007-08-28

;; (add-rewrite-rule "a-(RatConstr IntZero One)" "a")
;; (add-rewrite-rule "a-a" "RatConstr IntZero One")

;; (add-rewrite-rule "(a1/b1)*(a2/b2)" "(a1*a2)/(b1*b2)")
;; ;; (add-rewrite-rule "a1*(a2/b2)" "(a1*a2)/b2")
;; ;; (add-rewrite-rule "(a1/b1)*a2" "(a1*a2)/b1")

;; (add-rewrite-rule "(a1/b1)*(j#q)" "(a1*j)/(b1*q)")
;; (add-rewrite-rule "(k#p)*(a2/b2)" "(k*a2)/(p*b2)")
;; ;; (add-rewrite-rule "a1*(j#q)" "(a1*j)/q")
;; ;; (add-rewrite-rule "(k#p)*a2" "(k*a2)/p")

;; ;; Added 2007-02-26
;; (add-rewrite-rule "RatConstr(IntP One)One*a" "a")
;; (add-rewrite-rule "a*RatConstr(IntP One)One" "a")

;; ;; Added 2007-08-28

;; (add-rewrite-rule "a*(RatConstr IntZero One)" "RatConstr IntZero One")
;; (add-rewrite-rule "(RatConstr IntZero One)*a" "RatConstr IntZero One")
;; (add-rewrite-rule "a1*(a2*a3)" "a1*a2*a3")

;; (add-rewrite-rule "(a1/b1)/(a2/b2)" "(a1*b2)/(b1*a2)")

;; ;; Normal forms, which makes equally displayed terms equal.  Strategy:
;; ;; do computations at the lowest possible level.  Raise the type outside.

;; (add-rewrite-rules
;;  "rat**(IntP One)" "rat"
;;  "a**(IntS j)" "a**j*a"

;;  "((IntP p)#One)**(IntP q)" "IntP(p**q)#One"
;;  "((IntP p)#One)**(IntN q)" "IntP One#(p**q)"
;;  "((IntP p)#One)**(NatToInt nat2)" "IntP(p**nat2)#One"

;;  "((NatToInt nat1)#One)**(IntP q)" "NatToInt(nat1**q)#One"
;;  "((NatToInt nat1)#One)**(NatToInt nat2)" "NatToInt(nat1**nat2)#One"

;;  "((IntN p)#One)**(IntP q)" "IntN(p**q)#One"
;;  "((IntN p)#One)**(IntN q)" "IntN One#(p**q)"
;;  "((IntN p)#One)**(NatToInt nat2)" "IntN(p**nat2)#One"

;;  "(k#One)**(IntP q)" "(k**q)#One")

;; 4.  Adding external code
;; ========================

;; We want to view RatPlus, RatMinus, RatTimes, RatDiv, RatLt, RatLe as
;; program constants with external code, using add-external-code.  The
;; external code - after evaluation and application to tsubst and the
;; arguments - should give either the final value (e.g., the numeral
;; for the sum) or else #f, in which case the rules are tried next on
;; the arguments.

(define (int-to-int-term n)
  (cond
   ((positive? n)
    (mk-term-in-app-form
     (make-term-in-const-form (constr-name-to-constr "IntPos"))
     (make-numeric-term-wrt-pos n)))
   ((zero? n) (make-term-in-const-form (constr-name-to-constr "IntZero")))
   ((negative? n)
    (mk-term-in-app-form
     (make-term-in-const-form (constr-name-to-constr "IntNeg"))
     (make-numeric-term-wrt-pos (- n))))
   (else (myerror "int-to-int-term" "integer expected" n))))

(define ratplus-code
  '(lambda (tsubst objs)
     (let ((val1 (nbe-object-to-value (car objs)))
	   (val2 (nbe-object-to-value (cadr objs))))
       (and (nbe-constr-value? val1) (nbe-constr-value? val2)
	    (let* ((args1 (nbe-constr-value-to-args val1))
		   (args2 (nbe-constr-value-to-args val2))
		   (vals1 (map nbe-object-to-value args1))
		   (vals2 (map nbe-object-to-value args2)))
	      (and (int-numeral-value? (car vals1))
		   (pos-numeral-value? (cadr vals1))
		   (int-numeral-value? (car vals2))
		   (pos-numeral-value? (cadr vals2))
		   (let* ((numer1 (int-numeral-value-to-number (car vals1)))
			  (denom1 (pos-numeral-value-to-number (cadr vals1)))
			  (numer2 (int-numeral-value-to-number (car vals2)))
			  (denom2 (pos-numeral-value-to-number (cadr vals2)))
			  (sum (+ (/ numer1 denom1) (/ numer2 denom2)))
			  (numer (numerator sum))
			  (denom (denominator sum))
			  (numer-term (int-to-int-term numer))
			  (denom-term (make-numeric-term denom))
			  (constr (constr-name-to-constr "RatConstr"))
			  (term (mk-term-in-app-form
				 (make-term-in-const-form constr)
				 numer-term denom-term)))
		     (nbe-term-to-object
		      term (nbe-make-bindings '() '())))))))))

(define ratminus-code
  '(lambda (tsubst objs)
     (let ((val1 (nbe-object-to-value (car objs)))
	   (val2 (nbe-object-to-value (cadr objs))))
       (and (nbe-constr-value? val1) (nbe-constr-value? val2)
	    (let* ((args1 (nbe-constr-value-to-args val1))
		   (args2 (nbe-constr-value-to-args val2))
		   (vals1 (map nbe-object-to-value args1))
		   (vals2 (map nbe-object-to-value args2)))
	      (and (int-numeral-value? (car vals1))
		   (pos-numeral-value? (cadr vals1))
		   (int-numeral-value? (car vals2))
		   (pos-numeral-value? (cadr vals2))
		   (let* ((numer1 (int-numeral-value-to-number (car vals1)))
			  (denom1 (pos-numeral-value-to-number (cadr vals1)))
			  (numer2 (int-numeral-value-to-number (car vals2)))
			  (denom2 (pos-numeral-value-to-number (cadr vals2)))
			  (diff (- (/ numer1 denom1) (/ numer2 denom2)))
			  (numer (numerator diff))
			  (denom (denominator diff))
			  (numer-term (int-to-int-term numer))
			  (denom-term (make-numeric-term denom))
			  (constr (constr-name-to-constr "RatConstr"))
			  (term (mk-term-in-app-form
				 (make-term-in-const-form constr)
				 numer-term denom-term)))
		     (nbe-term-to-object
		      term (nbe-make-bindings '() '())))))))))

(define rattimes-code
  '(lambda (tsubst objs)
     (let ((val1 (nbe-object-to-value (car objs)))
	   (val2 (nbe-object-to-value (cadr objs))))
       (and (nbe-constr-value? val1) (nbe-constr-value? val2)
	    (let* ((args1 (nbe-constr-value-to-args val1))
		   (args2 (nbe-constr-value-to-args val2))
		   (vals1 (map nbe-object-to-value args1))
		   (vals2 (map nbe-object-to-value args2)))
	      (and (int-numeral-value? (car vals1))
		   (pos-numeral-value? (cadr vals1))
		   (int-numeral-value? (car vals2))
		   (pos-numeral-value? (cadr vals2))
		   (let* ((numer1 (int-numeral-value-to-number (car vals1)))
			  (denom1 (pos-numeral-value-to-number (cadr vals1)))
			  (numer2 (int-numeral-value-to-number (car vals2)))
			  (denom2 (pos-numeral-value-to-number (cadr vals2)))
			  (prod (* (/ numer1 denom1) (/ numer2 denom2)))
			  (numer (numerator prod))
			  (denom (denominator prod))
			  (numer-term (int-to-int-term numer))
			  (denom-term (make-numeric-term denom))
			  (constr (constr-name-to-constr "RatConstr"))
			  (term (mk-term-in-app-form
				 (make-term-in-const-form constr)
				 numer-term denom-term)))
		     (nbe-term-to-object
		      term (nbe-make-bindings '() '())))))))))

(define ratdiv-code
  '(lambda (tsubst objs)
     (let ((val1 (nbe-object-to-value (car objs)))
	   (val2 (nbe-object-to-value (cadr objs))))
       (and (nbe-constr-value? val1) (nbe-constr-value? val2)
	    (let* ((args1 (nbe-constr-value-to-args val1))
		   (args2 (nbe-constr-value-to-args val2))
		   (vals1 (map nbe-object-to-value args1))
		   (vals2 (map nbe-object-to-value args2)))
	      (and (int-numeral-value? (car vals1))
		   (pos-numeral-value? (cadr vals1))
		   (int-numeral-value? (car vals2))
		   (pos-numeral-value? (cadr vals2))
		   (let* ((numer1 (int-numeral-value-to-number (car vals1)))
			  (denom1 (pos-numeral-value-to-number (cadr vals1)))
			  (numer2 (int-numeral-value-to-number (car vals2)))
			  (denom2 (pos-numeral-value-to-number (cadr vals2)))
			  (quot (/ (/ numer1 denom1) (/ numer2 denom2)))
			  (numer (numerator quot))
			  (denom (denominator quot))
			  (numer-term (int-to-int-term numer))
			  (denom-term (make-numeric-term denom))
			  (constr (constr-name-to-constr "RatConstr"))
			  (term (mk-term-in-app-form
				 (make-term-in-const-form constr)
				 numer-term denom-term)))
		     (nbe-term-to-object
		      term (nbe-make-bindings '() '())))))))))

(define ratlt-code
  '(lambda (tsubst objs)
     (let ((val1 (nbe-object-to-value (car objs)))
	   (val2 (nbe-object-to-value (cadr objs))))
       (and (nbe-constr-value? val1) (nbe-constr-value? val2)
	    (let* ((args1 (nbe-constr-value-to-args val1))
		   (args2 (nbe-constr-value-to-args val2))
		   (vals1 (map nbe-object-to-value args1))
		   (vals2 (map nbe-object-to-value args2)))
	      (and (int-numeral-value? (car vals1))
		   (pos-numeral-value? (cadr vals1))
		   (int-numeral-value? (car vals2))
		   (pos-numeral-value? (cadr vals2))
		   (let* ((numer1 (int-numeral-value-to-number (car vals1)))
			  (denom1 (pos-numeral-value-to-number (cadr vals1)))
			  (numer2 (int-numeral-value-to-number (car vals2)))
			  (denom2 (pos-numeral-value-to-number (cadr vals2)))
			  (res (< (/ numer1 denom1) (/ numer2 denom2)))
			  (const (if res true-const false-const))
			  (term (make-term-in-const-form const)))
		     (nbe-term-to-object
		      term (nbe-make-bindings '() '())))))))))

(define ratle-code
  '(lambda (tsubst objs)
     (let ((val1 (nbe-object-to-value (car objs)))
	   (val2 (nbe-object-to-value (cadr objs))))
       (and (nbe-constr-value? val1) (nbe-constr-value? val2)
	    (let* ((args1 (nbe-constr-value-to-args val1))
		   (args2 (nbe-constr-value-to-args val2))
		   (vals1 (map nbe-object-to-value args1))
		   (vals2 (map nbe-object-to-value args2)))
	      (and (int-numeral-value? (car vals1))
		   (pos-numeral-value? (cadr vals1))
		   (int-numeral-value? (car vals2))
		   (pos-numeral-value? (cadr vals2))
		   (let* ((numer1 (int-numeral-value-to-number (car vals1)))
			  (denom1 (pos-numeral-value-to-number (cadr vals1)))
			  (numer2 (int-numeral-value-to-number (car vals2)))
			  (denom2 (pos-numeral-value-to-number (cadr vals2)))
			  (res (<= (/ numer1 denom1) (/ numer2 denom2)))
			  (const (if res true-const false-const))
			  (term (make-term-in-const-form const)))
		     (nbe-term-to-object
		      term (nbe-make-bindings '() '())))))))))

(add-external-code "RatPlus" ratplus-code)
(add-external-code "RatMinus" ratminus-code)
(add-external-code "RatTimes" rattimes-code)
(add-external-code "RatDiv" ratdiv-code)
(add-external-code "RatLt" ratlt-code)
(add-external-code "RatLe" ratle-code)

