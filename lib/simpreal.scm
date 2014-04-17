;; $Id: simpreal.scm 2647 2013-09-16 07:38:37Z schwicht $

'(
(load "~/git/minlog/init.scm")
(set! COMMENT-FLAG #f)
(libload "nat.scm")
(libload "numbers.scm")
(set! COMMENT-FLAG #t)
)
(if (not (assoc "nat" ALGEBRAS))
    (begin
      (libload "nat.scm")
      (if (not (assoc "nat" ALGEBRAS))
	  (myerror "First execute (libload \"nat.scm\")"))))

(display "loading simpreal.scm ...") (newline)

;; We first provide some functions that were previously in numbers.scm

(define (int-term-to-rat-term term)
  (mk-term-in-app-form
   (make-term-in-const-form (constr-name-to-constr "RatConstr"))
   term (make-numeric-term-wrt-pos 1)))

(define (pos-term-to-rat-term term)
  (int-term-to-rat-term (pos-term-to-int-term term)))

(define (real-numeric-term-to-number term)
  (let ((args (term-in-app-form-to-args term)))
    (if (= 2 (length args))
	(rat-numeric-term-to-number
	 (if (term-in-abst-form? (car args))
	     (term-in-abst-form-to-kernel (car args))
	     (myerror "real-numeric-term-to-number"
		      "term in abst form expected"
		      (car args))))
	(myerror "real-numeric-term-to-number" "real numeric term expected"
		 term))))

(define (int-numeric-term-to-number term)
  (cond
   ((and (term-in-const-form? term)
	 (string=? "IntZero" (const-to-name
			      (term-in-const-form-to-const term))))
    0)
   ((term-in-app-form? term)
    (let ((op (term-in-app-form-to-op term))
	  (arg (term-in-app-form-to-arg term)))
      (if
       (term-in-const-form? op)
       (let ((name (const-to-name (term-in-const-form-to-const op))))
	 (cond
	  ((string=? name "IntPos") (numeric-term-wrt-pos-to-number arg))
	  ((string=? name "IntNeg") (- (numeric-term-wrt-pos-to-number arg)))
	  (else (myerror "int-numeric-term-to-number"
			 "int numeric term expected"
			 term))))
       (myerror "int-numeric-term-to-number" "int numeric term expected"
		term))))
   (else (myerror "int-numeric-term-to-number" "int numeric term expected"
		  term))))
  
(define (rat-numeric-term-to-number term)
  (let* ((args (term-in-app-form-to-args term))
	 (k (numeric-term-wrt-pos-to-number (cadr args)))
	 (i (int-numeric-term-to-number (car args))))
    (/ i k)))

(define (is-rat-numeric-term? term)
  (let ((op (term-in-app-form-to-final-op term))
	(args (term-in-app-form-to-args term)))
    (and (term-in-const-form? op)
	 (string=? "RatConstr"
		   (const-to-name (term-in-const-form-to-const op)))
	 (= 2 (length args))
	 (let ((arg1 (car args))
	       (arg2 (cadr args)))
	   (and (is-int-numeric-term? arg1)
		(is-numeric-term-wrt-pos? arg2))))))

(define (pos-term-to-int-term term)
  (mk-term-in-app-form
   (make-term-in-const-form (constr-name-to-constr "IntPos"))
   term))

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

(define (rat-to-rat-term n)
  (mk-term-in-app-form
   (make-term-in-const-form (constr-name-to-constr "RatConstr"))
   (int-to-int-term (numerator n))
   (make-numeric-term-wrt-pos (denominator n))))

(define (rat-term-to-real-term term)
  (let ((natvar (type-to-new-var (py "nat")))
	(intvar (type-to-new-var (py "int"))))
    (mk-term-in-app-form
     (make-term-in-const-form (constr-name-to-constr "RealConstr"))
     (make-term-in-abst-form natvar term) ;constant Cauchy sequence
     (make-term-in-abst-form intvar
			     (make-numeric-term-wrt-nat 1))))) ;one modulus

(define (rat-to-real-term n)
  (rat-term-to-real-term (rat-to-rat-term n)))

;; (pp (rat-to-real-term 2))
;; (pp (rat-to-real-term -2/3))

(define (is-real-numeric-term? term)
  (let ((op (term-in-app-form-to-final-op term))
	(args (term-in-app-form-to-args term)))
    (and (term-in-const-form? op)
	 (string=? "RealConstr"
		   (const-to-name (term-in-const-form-to-const op)))
	 (= 2 (length args))
	 (let ((arg1 (car args)))
	   (and (term-in-abst-form? arg1)
		(is-rat-numeric-term?
		 (term-in-abst-form-to-kernel arg1)))))))

;; 4. Simplification of Real Terms 
;; ===============================

;; General description of the simplification procedure for number
;; terms.  Reals x,y are built from Cauchy sequences v of rationals
;; and moduli M by RealConstr v M.  Rationals a,b,c are built from
;; integers i,j and positive numbers p by pairing i#p (viewed as
;; quotient), und integers are either positive or zero or negative.

;; Positive terms r are built form positive variables p,q and the
;; constant One by the constructors SZero and SOne and the arithmetical
;; functions S, PosPlus, PosTimes, PosMinus, PosExp.

;; Natural terms r0 are built form variables n,m and the constant Zero
;; by the constructor Succ the arithmetical functions NatPlus,
;; NatTimes, NatMinus, NatExp.

;; Integer terms s are built form integer variables i,j and integer
;; constructor terms IntPos r, IntZero, IntNeg r with a positive term r
;; by the arithmetical functions IntS, IntPlus, IntTimes, IntMinus,
;; IntExp.  A positive term r can be lifted to the integer term IntPos
;; r.

;; Rational terms t are built form rational variables a,b and rational
;; constructor terms s#r with an integer term s and a positive term r
;; by the arithmetical functions RatPlus, RatTimes, RatMinus, RatDiv,
;; RatExp.  An integer term s can be lifted to the rational term s#One.

;; Real terms u are built form real variables x,y and real constructor
;; terms RealConstr v w with v a term of type pos=>rat and w a term of
;; type pos=>pos by the arithmetical functions RealPlus, RealTimes,
;; RealMinus, RealDiv, RealExp.  A rational term t can be lifted to
;; the real term RealConstr([n]t)([k]Zero).

;; We abbreviate IntPos by IntP, and IntNeg by IntN.

;; Simplification starts by unfolding exponentials, using the rules 
;; x**IntZero           -> 1, 
;; x**(IntP 1)          -> x, 
;; x**(IntP(SZero p))   -> (x**(IntP p))*(x**(IntP p)), 
;; x**(IntP(SOne p))    -> (x**(IntP p))*(x**(IntP p))*x, 
;; x**(IntP(S p))       -> (x**(IntP p))*x, 
;; x**(IntP(p+q))       -> (x**(IntP p))*(x**(IntP q)),
;; x**(IntP(p*q))       -> (x**(IntP p))**(IntP q).
;; x**(IntN p)          -> 1/x**(IntP p), 
;; x**(IntS a)          -> (x**a)*x, 
;; x**(a+b)             -> (x**a)*(x**b),
;; x**(a*b)             -> exp(x**a)b.

;; Next we want to push the constructors inside, to allow more
;; simplifications.  For the number types pos, nat, int, rat, real the
;; precise meaning is somewhat different.  Notice that the embedding
;; constants PosToNat and NatToInt are ignored.

;; pos.  The constructors are One, SZero, SOne.  If they are part of a
;; numerical term, they are not touched.  Otherwise they are removed, via
;; SZero r -> r*2
;; SOne r  -> r*2+1

;; nat.  The constructors are Zero and Succ.  If they are part of a
;; numerical term, they are not touched.  Otherwise they are removed, via
;; Zero -> 0
;; Succ r0  -> r0+1

;; int.  The constructors are IntN, IntZero, IntP.  IntN is removed using 0-,
;; IntZero is removed using 0, and IntP is pushed inside, through + and *:
;; IntN r -> 0-IntP r
;; IntZero -> 0
;; IntP(r o s) -> IntP r o IntP s for o one of + *

;; rat.  The constructor is RatConstr #.  r#s with s not 1 is replaced
;; using /, and in r#1 the #1 is pushed inside, through + - *:
;; r#s -> (r#1)/(IntP s#1) if s is not 1
;; (r o s)#1 -> r#1 o s#1 for o one of + - *

;; real.  The constructor is RealConstr.  In RealConstr([n]r o s)([k[0)
;; with a constant Cauchy sequence (i.e., n not in r,s) the constructor
;; is pushed inside.
;; RealConstr([n]r o s)([k[0) -> RealConstr([n]r)([k[0) o RealConstr([n]s)([k[0)
;; for o one of + - * /

;; Next we employ an operator term-to-numerator-and-denominator, and
;; then apply some operators to the numerator and denominator
;; separately.  By a monom we mean a product whose factors are neither
;; sums nor differences.  For a single monom, we collect its general
;; numeric terms into a product number and write each factor as a list
;; of a string and its power, for example (27 ("a" 2) ("b" 1) ("c" 3)).
;; Then we sort and join stringpowers as well as summands, to make
;; cancellation possible.  To describe the form of the simplified term,
;; we use the following terminology.  sp (stringpower): a list of two
;; elements, a string and a positive integer (Scheme object).  sps
;; (stringpowers): a list (possibly empty) of stringpowers.  nsps
;; (num-with-stringpowers): a list (num sp1 sp2 ...) containing at
;; least the number.  nsps-list: a list (possibly empty) of nsps.

;; So when given a quotient num1 common-sps1 non-common-nsps-list1 /
;; num2 common-sps2 non-common-nsps-list2, we then produce a product of
;; (/ num1 num2) and the quotient cancelled-common-sps1
;; non-common-nsps-list1 / cancelled-common-sps2 non-common-nsps-list2
;; in case non-common-nsps-list1 and non-common-nsps-list2 differ, and
;; cancelled-common-sps1 / cancelled-common-sps2 in case
;; non-common-nsps-list1 and non-common-nsps-list2 are equal.

(define (num-and-type-to-gen-numeric-term n type)
  (cond
   ((and (integer? n) (positive? n))
    (cond ((equal? (py "pos") type) (make-numeric-term-wrt-pos n))
	  ((equal? (py "nat") type) (make-numeric-term-wrt-nat n))
	  ((equal? (py "int") type) (int-to-int-term n))
	  ((equal? (py "rat") type) (rat-to-rat-term n))
	  ((equal? (py "rea") type) (rat-to-real-term n))
	  (else (myerror "num-and-type-to-gen-numeric-term"
			 "unexpected type" type))))
   ((zero? n)
    (cond ((equal? (py "nat") type) (make-numeric-term-wrt-nat n))
	  ((equal? (py "int") type) (int-to-int-term n))
	  ((equal? (py "rat") type) (rat-to-rat-term n))
	  ((equal? (py "rea") type) (rat-to-real-term n))
	  (else (myerror "num-and-type-to-gen-numeric-term"
			 "unexpected type" type))))
   ((and (integer? n) (negative? n))
    (cond ((equal? (py "int") type) (int-to-int-term n))
	  ((equal? (py "rat") type) (rat-to-rat-term n))
	  ((equal? (py "rea") type) (rat-to-real-term n))
	  (else (myerror "num-and-type-to-gen-numeric-term"
			 "unexpected type" type))))
   (else
    (cond ((equal? (py "rat") type) (rat-to-rat-term n))
	  ((equal? (py "rea") type) (rat-to-real-term n))
	  (else (myerror "num-and-type-to-gen-numeric-term"
			 "unexpected type" type))))))

;; (pp (num-and-type-to-gen-numeric-term 1 (py "pos")))
;; (pp (num-and-type-to-gen-numeric-term 1 (py "nat")))
;; (pp (num-and-type-to-gen-numeric-term 1 (py "int")))
;; (pp (num-and-type-to-gen-numeric-term 1 (py "rat")))
;; (pp (num-and-type-to-gen-numeric-term 1 (py "rea")))

(define (is-gen-numeric-term? term)
  (let ((op (term-in-app-form-to-final-op term))
	(args (term-in-app-form-to-args term)))
    (and
     (term-in-const-form? op)
     (let ((name (const-to-name (term-in-const-form-to-const op))))
      (or
	(member name '("One" "Zero" "IntZero"))
	(and (member name '("SZero" "SOne" "S" "Succ"
			    "IntPos" "IntNeg" "IntS"
			    "PosToNat" "NatToInt"))
	     (= 1 (length args))
	     (is-gen-numeric-term? (car args)))
	(and (member name '("RatConstr" "CpxConstr"))
	     (= 2 (length args))
	     (is-gen-numeric-term? (car args))
	     (is-gen-numeric-term? (cadr args)))
	(and (member name '("RealConstr"))
	     (= 2 (length args))
	     (and (term-in-abst-form? (car args))
		  (is-rat-numeric-term?
		   (term-in-abst-form-to-kernel (car args))))))))))

;; (define (is-gen-numeric-term? term)
;;   (let ((type (term-to-type term)))
;;     (or (and (equal? (py "pos") type) (is-numeric-term-wrt-pos? term))
;; 	(and (equal? (py "nat") type) (is-numeric-term-wrt-nat? term))
;; 	(and (equal? (py "int") type) (is-int-numeric-term? term))
;; 	(and (equal? (py "rat") type) (is-rat-numeric-term? term))
;; 	(and (equal? (py "rea") type) (is-real-numeric-term? term)))))

;; (is-gen-numeric-term? (num-and-type-to-gen-numeric-term 1 (py "pos")))
;; (is-gen-numeric-term? (num-and-type-to-gen-numeric-term 1 (py "nat")))
;; (is-gen-numeric-term? (num-and-type-to-gen-numeric-term 1 (py "int")))
;; (is-gen-numeric-term? (num-and-type-to-gen-numeric-term 1 (py "rat")))
;; (is-gen-numeric-term? (num-and-type-to-gen-numeric-term 1 (py "rea")))
;; (is-gen-numeric-term? (pt "NatToInt Zero"))

(define (gen-numeric-term-to-number term)
  (let ((op (term-in-app-form-to-final-op term))
	(args (term-in-app-form-to-args term)))
    (if (not (term-in-const-form? op))
	(myerror "gen-numeric-term-to-number"
		 "general numeric term expected" term))
    (let ((name (const-to-name (term-in-const-form-to-const op))))
      (cond
       ((string=? name "One") 1)
       ((member name '("Zero" "IntZero")) 0)
       ((member name '("S" "Succ" "IntS"))
	(+ 1 (gen-numeric-term-to-number (car args))))
       ((string=? name "SZero")
	(* 2 (gen-numeric-term-to-number (car args))))
       ((string=? name "SOne")
	(+ 1 (* 2 (gen-numeric-term-to-number (car args)))))
       ((member name '("IntPos" "PosToNat" "NatToInt"))
	(gen-numeric-term-to-number (car args)))
       ((string=? name "IntNeg")
	(- (gen-numeric-term-to-number (car args))))
       ((string=? name "RatConstr")
	(/ (gen-numeric-term-to-number (car args))
	   (gen-numeric-term-to-number (cadr args))))
       ((string=? name "RealConstr")
	(gen-numeric-term-to-number
	 (term-in-abst-form-to-kernel (car args))))
       (else "gen-numeric-term-to-number"
	     "general numeric term expected" term)))))

;; (define (gen-numeric-term-to-number term)
;;   (let ((type (term-to-type term)))
;;     (cond
;;      ((equal? (py "pos") type) (numeric-term-wrt-pos-to-number term))
;;      ((equal? (py "nat") type) (numeric-term-wrt-nat-to-number term))
;;      ((equal? (py "int") type) (int-numeric-term-to-number term))
;;      ((equal? (py "rat") type) (rat-numeric-term-to-number term))
;;      ((equal? (py "rea") type) (real-numeric-term-to-number term))
;;      (else (myerror "gen-numeric-term-to-number"
;; 		    "pos, nat, int, rat or rea expected"
;; 		    type)))))

;; (gen-numeric-term-to-number (num-and-type-to-gen-numeric-term 1 (py "pos")))
;; (gen-numeric-term-to-number (num-and-type-to-gen-numeric-term 1 (py "nat")))
;; (gen-numeric-term-to-number (num-and-type-to-gen-numeric-term 1 (py "int")))
;; (gen-numeric-term-to-number (num-and-type-to-gen-numeric-term 1 (py "rat")))
;; (gen-numeric-term-to-number (num-and-type-to-gen-numeric-term 1 (py "rea")))

(define (term-to-term-with-unfolded-exponents term)
  (case (tag term)
    ((term-in-var-form term-in-const-form)
     term)
    ((term-in-app-form)    
     (let* ((op (term-in-app-form-to-final-op term))
	    (args (term-in-app-form-to-args term))
	    (type (term-to-type term))
	    (string (cond ((equal? (py "pos") type) "Pos")
			  ((equal? (py "nat") type) "Nat")
			  ((equal? (py "int") type) "Int")
			  ((equal? (py "rat") type) "Rat")
			  ((equal? (py "rea") type) "Real")
			  (else (myerror "term-to-term-with-unfolded-exponents"
					 "unexpected type"
					 type)))))
       (if
	(and (term-in-const-form? op)
	     (let* ((name (const-to-name (term-in-const-form-to-const op)))
		    (l (string-length name))
		    (exp-string
		     (substring name (max 0 (- l (string-length "Exp"))) l)))
	       (string=? "Exp" exp-string))
	     (= 2 (length args)))
	(let* ((exp (cadr args))
	       (expop (term-in-app-form-to-final-op exp))
	       (expargs (term-in-app-form-to-args exp)))
	  (cond
	   ((and (term-in-const-form? exp)
		 (string=? "IntZero" (const-to-name
				      (term-in-const-form-to-const exp))))
	    (make-term-in-const-form (constr-name-to-constr "One")))
;; 	    (make-term-in-app-form
;; 	     (make-term-in-const-form (constr-name-to-constr "IntPos"))
;; 	     (make-term-in-const-form (constr-name-to-constr "One"))))
	   ((and (term-in-const-form? expop)
		 (string=? "IntPos" (const-to-name
				     (term-in-const-form-to-const expop)))
		 (< 0 (length expargs)))
	    (let* ((exparg (car expargs))
		   (expargop (term-in-app-form-to-final-op exparg)))
	      (cond
	       ((and (term-in-const-form? expargop)
		     (string=? "One" (const-to-name
				      (term-in-const-form-to-const
				       expargop))))
		(car args))
	       ((and (term-in-const-form? expargop)
		     (string=? "SZero" (const-to-name
					(term-in-const-form-to-const
					 expargop))))
		(let* ((expargarg (term-in-app-form-to-arg exparg))
		       (prev (term-to-term-with-unfolded-exponents
			      (mk-term-in-app-form op (car args) expargarg))))
		  (mk-term-in-app-form
		   (make-term-in-const-form
		    (pconst-name-to-pconst (string-append string "Times")))
		   prev prev)))
	       ((and (term-in-const-form? expargop)
		     (string=? "SOne" (const-to-name
				       (term-in-const-form-to-const
					expargop))))
		(let* ((expargarg (term-in-app-form-to-arg exparg))
		       (prev (term-to-term-with-unfolded-exponents
			      (mk-term-in-app-form op (car args) expargarg)))
		       (timesconst (make-term-in-const-form
				    (pconst-name-to-pconst
				     (string-append string "Times")))))
		  (mk-term-in-app-form
		   timesconst
		   (mk-term-in-app-form timesconst prev prev)
		   (car args))))
	       ((and (term-in-const-form? expargop)
		     (string=? "S" (const-to-name
				    (term-in-const-form-to-const expargop))))
		(let* ((expargarg (term-in-app-form-to-arg exparg))
		       (prev (term-to-term-with-unfolded-exponents
			      (mk-term-in-app-form op (car args) expargarg))))
		  (mk-term-in-app-form
		   (make-term-in-const-form
		    (pconst-name-to-pconst (string-append string "Times")))
		   prev (car args))))
	       ((and (term-in-const-form? expargop)
		     (string=? "PosPlus" (const-to-name
					  (term-in-const-form-to-const
					   expargop))))
		(let* ((expargargs (term-in-app-form-to-args exparg))
		       (expargarg1 (car expargargs))
		       (expargarg2 (cadr expargargs))
		       (prev1 (term-to-term-with-unfolded-exponents
			       (mk-term-in-app-form op (car args) expargarg1)))
		       (prev2 (term-to-term-with-unfolded-exponents
			       (mk-term-in-app-form op (car args)
						    expargarg2))))
		  (mk-term-in-app-form
		   (make-term-in-const-form
		    (pconst-name-to-pconst (string-append string "Times")))
		   prev1 prev2)))
	       ((and (term-in-const-form? expargop)
		     (string=? "PosTimes" (const-to-name
					   (term-in-const-form-to-const
					    expargop))))
		(let* ((expargargs (term-in-app-form-to-args exparg))
		       (expargarg1 (car expargargs))
		       (expargarg2 (cadr expargargs)))
		  (term-to-term-with-unfolded-exponents
		   (mk-term-in-app-form
		    (make-term-in-const-form (pconst-name-to-pconst "RatExp"))
		    (mk-term-in-app-form op (car args) expargarg1)
		    expargarg2))))
	       (else
		(apply mk-term-in-app-form
		       (cons op (map term-to-term-with-unfolded-exponents
				     args)))))))
	   ((and (term-in-const-form? expop)
		 (string=? "IntNeg" (const-to-name
				   (term-in-const-form-to-const expop)))
		 (< 0 (length expargs)))
	    (let ((exparg (car expargs)))
	      (mk-term-in-app-form
	       (make-term-in-const-form (pconst-name-to-pconst "RatDiv"))
	       (make-term-in-const-form (constr-name-to-constr "One"))
	       (term-to-term-with-unfolded-exponents
		(mk-term-in-app-form
		 op (car args)
		 (mk-term-in-app-form
		  (make-term-in-const-form (constr-name-to-constr "IntPos"))
		  exparg))))))
	   ((and (term-in-const-form? expop)
		 (string=? "IntS" (const-to-name
				   (term-in-const-form-to-const expop))))
	    (let* ((exparg (term-in-app-form-to-arg exp))
		   (prev (term-to-term-with-unfolded-exponents
			  (mk-term-in-app-form op (car args) exparg))))
	      (mk-term-in-app-form
	       (make-term-in-const-form
		(pconst-name-to-pconst (string-append string "Times")))
	       prev (car args))))
	   ((and (term-in-const-form? expop)
		 (string=? "IntPlus" (const-to-name
				      (term-in-const-form-to-const expop))))
	    (let* ((expargs (term-in-app-form-to-args exp))
		   (exparg1 (car expargs))
		   (exparg2 (cadr expargs))
		   (prev1 (term-to-term-with-unfolded-exponents
			   (mk-term-in-app-form op (car args) exparg1)))
		   (prev2 (term-to-term-with-unfolded-exponents
			   (mk-term-in-app-form op (car args) exparg2))))
	      (mk-term-in-app-form
	       (make-term-in-const-form
		(pconst-name-to-pconst (string-append string "Times")))
	       prev1 prev2)))
	   ((and (term-in-const-form? expop)
		 (string=? "IntTimes" (const-to-name
				       (term-in-const-form-to-const expop))))
	    (let* ((expargs (term-in-app-form-to-args exp))
		   (exparg1 (car expargs))
		   (exparg2 (cadr expargs)))
	      (term-to-term-with-unfolded-exponents
	       (mk-term-in-app-form
		(make-term-in-const-form (pconst-name-to-pconst "RatExp"))
		(mk-term-in-app-form op (car args) exparg1) exparg2))))
	   (else
	    (apply mk-term-in-app-form
		   (cons op (map term-to-term-with-unfolded-exponents
				 args))))))
	(apply mk-term-in-app-form
	       (cons op (map term-to-term-with-unfolded-exponents args))))))
    ((term-in-abst-form)
     (let ((var (term-in-abst-form-to-var term))
	   (kernel (term-in-abst-form-to-kernel term)))
       (make-term-in-abst-form
	var (term-to-term-with-unfolded-exponents kernel))))
    ((term-in-pair-form)
     (let ((left (term-in-pair-form-to-left term))
	   (right (term-in-pair-form-to-right term)))
       (make-term-in-pair-form
	(term-to-term-with-unfolded-exponents left)
	(term-to-term-with-unfolded-exponents right))))
    ((term-in-lcomp-form)
     (make-term-in-lcomp-form
      (term-to-term-with-unfolded-exponents
       (term-in-lcomp-form-to-kernel term))))
    ((term-in-rcomp-form)
     (make-term-in-rcomp-form
      (term-to-term-with-unfolded-exponents
       (term-in-rcomp-form-to-kernel term))))
    ((term-in-if-form)
     (let* ((test (term-in-if-form-to-test term))
	    (alts (term-in-if-form-to-alts term))
	    (rest (term-in-if-form-to-rest term))
	    (prev (term-to-term-with-unfolded-exponents test))
	    (prevs (map term-to-term-with-unfolded-exponents alts)))
       (apply make-term-in-if-form (cons prev (cons prevs rest)))))
    (else (myerror "term-to-term-with-unfolded-exponents: term expected"
		   term))))

;; (pp (term-to-term-with-unfolded-exponents (pt "(2**(SZero pos))")))
;; (pp (term-to-term-with-unfolded-exponents (pt "(2**(SOne pos))")))
;; (pp (term-to-term-with-unfolded-exponents (pt "(2**2)")))
;; (pp (term-to-term-with-unfolded-exponents (pt "(2**(k+1))")))
;; (pp (term-to-term-with-unfolded-exponents (pt "(2**(k+7))")))
;; (pp (term-to-term-with-unfolded-exponents (pt "(2**(IntS k))")))
;; (pp (term-to-term-with-unfolded-exponents (pt "(2**(k+k1))")))
;; (pp (term-to-term-with-unfolded-exponents (pt "(2**(n*m))")))
;; (pp (term-to-term-with-unfolded-exponents (pt "a**1")))
;; (pp (term-to-term-with-unfolded-exponents (pt "(a**7)+(b**2)")))
;; (pp (term-to-term-with-unfolded-exponents (pt "(a**7)/(b**2)")))

(define (term-to-term-with-constructors-pushed-inside term)
  (if (not (member (term-to-type term)
		   (list (py "pos") (py "nat")  (py "int")
			 (py "rat") (py "rea") (py "cpx"))))
      (myerror "term-to-term-with-constructors-pushed-inside"
	       "term of type pos, nat, int, rat, rea or cpx expected" term))
  (cond
   ((or (term-in-var-form? term)
	(term-in-const-form? term)
	(is-gen-numeric-term? term))
    term)
   ((term-in-app-form? term)    
    (let ((op (term-in-app-form-to-final-op term))
	  (args (term-in-app-form-to-args term)))
      (cond
       ((and
	 (= 2 (length args))
	 (term-in-const-form? op)
	 (member
	  (const-to-name (term-in-const-form-to-const op))
	  '("PosPlus" "NatPlus" "IntPlus" "RatPlus" "RealPlus" "CpxPlus"
	    "PosMinus" "NatMinus" "IntMinus" "RatMinus" "RealMinus" "CpxMinus" 
	    "PosTimes" "NatTimes" "IntTimes" "RatTimes" "RealTimes" "CpxTimes" 
	    "RatDiv" "RealDiv" "CpxDiv")))
	(apply mk-term-in-app-form
	       (cons op (map term-to-term-with-constructors-pushed-inside
			     args))))
       ((and (= 1 (length args))
	     (term-in-const-form? op)
	     (string=? (const-to-name (term-in-const-form-to-const op))
		       "SZero"))
	(mk-term-in-app-form
	 (make-term-in-const-form (pconst-name-to-pconst "PosTimes"))
	 (make-numeric-term-wrt-pos 2)
	 (term-to-term-with-constructors-pushed-inside (car args))))
       ((and (= 1 (length args))
	     (term-in-const-form? op)
	     (string=? (const-to-name (term-in-const-form-to-const op))
		       "SOne"))
	(mk-term-in-app-form
	 (make-term-in-const-form (pconst-name-to-pconst "PosPlus"))
	 (mk-term-in-app-form
	  (make-term-in-const-form (pconst-name-to-pconst "PosTimes"))
	  (make-numeric-term-wrt-pos 2)
	  (term-to-term-with-constructors-pushed-inside (car args)))
	 (make-numeric-term-wrt-pos 1)))
       ((and (= 1 (length args))
	     (term-in-const-form? op)
	     (string=? (const-to-name (term-in-const-form-to-const op))
		       "Succ"))
	(mk-term-in-app-form
	 (make-term-in-const-form (pconst-name-to-pconst "NatPlus"))
	 (make-numeric-term-wrt-nat 1)
	 (term-to-term-with-constructors-pushed-inside (car args))))
       ((and
	 (term-in-const-form? op)
	 (string=? "PosToNat" (const-to-name (term-in-const-form-to-const op)))
	 (= 1 (length args)))
	(let* ((prev (term-to-term-with-constructors-pushed-inside (car args)))
	       (prevop (term-in-app-form-to-final-op prev))
	       (prevargs (term-in-app-form-to-args prev)))
	  (cond
	   ((and (term-in-const-form? prevop)
		 (string=? "PosPlus" (const-to-name
				      (term-in-const-form-to-const prevop))))
	    (mk-term-in-app-form
	     (make-term-in-const-form (pconst-name-to-pconst "NatPlus"))
	     (term-to-term-with-constructors-pushed-inside
	      (mk-term-in-app-form
	       (make-term-in-const-form (pconst-name-to-pconst "PosToNat"))
	       (car prevargs)))
	     (term-to-term-with-constructors-pushed-inside
	      (mk-term-in-app-form
	       (make-term-in-const-form (pconst-name-to-pconst "PosToNat"))
	       (cadr prevargs)))))
	   ((and (term-in-const-form? prevop)
		 (string=? "PosMinus" (const-to-name
				      (term-in-const-form-to-const prevop))))
	    (mk-term-in-app-form
	     (make-term-in-const-form (pconst-name-to-pconst "NatMinus"))
	     (term-to-term-with-constructors-pushed-inside
	      (mk-term-in-app-form
	       (make-term-in-const-form (pconst-name-to-pconst "PosToNat"))
	       (car prevargs)))
	     (term-to-term-with-constructors-pushed-inside
	      (mk-term-in-app-form
	       (make-term-in-const-form (pconst-name-to-pconst "PosToNat"))
	       (cadr prevargs)))))
	   ((and (term-in-const-form? prevop)
		 (string=? "PosTimes" (const-to-name
				      (term-in-const-form-to-const prevop))))
	    (mk-term-in-app-form
	     (make-term-in-const-form (pconst-name-to-pconst "NatTimes"))
	     (term-to-term-with-constructors-pushed-inside
	      (mk-term-in-app-form
	       (make-term-in-const-form (pconst-name-to-pconst "PosToNat"))
	       (car prevargs)))
	     (term-to-term-with-constructors-pushed-inside
	      (mk-term-in-app-form
	       (make-term-in-const-form (pconst-name-to-pconst "PosToNat"))
	       (cadr prevargs)))))
	   ((and (term-in-const-form? prevop)
		 (string=? "One" (const-to-name
				  (term-in-const-form-to-const prevop))))
	    (mk-term-in-app-form
	     (make-term-in-const-form (constr-name-to-constr "Succ"))
	     (make-term-in-const-form (constr-name-to-constr "Zero"))))
	   (else term))))
       ((and
	 (term-in-const-form? op)
	 (string=? "NatToInt" (const-to-name (term-in-const-form-to-const op)))
	 (= 1 (length args)))
	(let* ((prev (term-to-term-with-constructors-pushed-inside (car args)))
	       (prevop (term-in-app-form-to-final-op prev))
	       (prevargs (term-in-app-form-to-args prev)))
	  (cond
	   ((and (term-in-const-form? prevop)
		 (string=? "NatPlus" (const-to-name
				      (term-in-const-form-to-const prevop))))
	    (mk-term-in-app-form
	     (make-term-in-const-form (pconst-name-to-pconst "IntPlus"))
	     (term-to-term-with-constructors-pushed-inside
	      (mk-term-in-app-form
	       (make-term-in-const-form (pconst-name-to-pconst "NatToInt"))
	       (car prevargs)))
	     (term-to-term-with-constructors-pushed-inside
	      (mk-term-in-app-form
	       (make-term-in-const-form (pconst-name-to-pconst "NatToInt"))
	       (cadr prevargs)))))
	   ((and (term-in-const-form? prevop)
		 (string=? "NatMinus" (const-to-name
				      (term-in-const-form-to-const prevop))))
	    (mk-term-in-app-form
	     (make-term-in-const-form (pconst-name-to-pconst "IntMinus"))
	     (term-to-term-with-constructors-pushed-inside
	      (mk-term-in-app-form
	       (make-term-in-const-form (pconst-name-to-pconst "NatToInt"))
	       (car prevargs)))
	     (term-to-term-with-constructors-pushed-inside
	      (mk-term-in-app-form
	       (make-term-in-const-form (pconst-name-to-pconst "NatToInt"))
	       (cadr prevargs)))))
	   ((and (term-in-const-form? prevop)
		 (string=? "NatTimes" (const-to-name
				      (term-in-const-form-to-const prevop))))
	    (mk-term-in-app-form
	     (make-term-in-const-form (pconst-name-to-pconst "IntTimes"))
	     (term-to-term-with-constructors-pushed-inside
	      (mk-term-in-app-form
	       (make-term-in-const-form (pconst-name-to-pconst "NatToInt"))
	       (car prevargs)))
	     (term-to-term-with-constructors-pushed-inside
	      (mk-term-in-app-form
	       (make-term-in-const-form (pconst-name-to-pconst "NatToInt"))
	       (cadr prevargs)))))
	   ((and (term-in-const-form? prevop)
		 (string=? "PosToNat" (const-to-name
				       (term-in-const-form-to-const prevop))))
	    (term-to-term-with-constructors-pushed-inside
	     (mk-term-in-app-form
	      (make-term-in-const-form (constr-name-to-constr "IntPos"))
	      (car prevargs))))
	   ((and (term-in-const-form? prevop)
		 (string=? "Zero" (const-to-name
				   (term-in-const-form-to-const prevop))))
	    (make-term-in-const-form (constr-name-to-constr "IntZero")))
	   (else term))))
       ((and (term-in-const-form? op)
	     (member (const-to-name (term-in-const-form-to-const op))
		     '("PosToNat" "NatToInt"))
	     (= 1 (length args)))
	(make-term-in-app-form
	 op (term-to-term-with-constructors-pushed-inside (car args))))
       ((and (= 1 (length args))
	     (term-in-const-form? op)
	     (string=? (const-to-name (term-in-const-form-to-const op))
		       "IntNeg"))
	(mk-term-in-app-form
	 (make-term-in-const-form (pconst-name-to-pconst "IntMinus"))
	 (make-numeric-term-wrt-pos 0)
	 (term-to-term-with-constructors-pushed-inside (car args))))
       ((and (= 1 (length args))
	     (term-in-const-form? op)
	     (string=? (const-to-name (term-in-const-form-to-const op))
		       "IntPos"))
	(let* ((arg (car args))
	       (mod-arg (term-to-term-with-constructors-pushed-inside arg))
	       (op1 (term-in-app-form-to-final-op mod-arg))
	       (args1 (term-in-app-form-to-args mod-arg)))
	  (cond
	   ((and (term-in-const-form? op1)
		 (string=? "PosPlus" (const-to-name
				      (term-in-const-form-to-const op1)))
		 (= 2 (length args1)))
	    (mk-term-in-app-form
	     (make-term-in-const-form (pconst-name-to-pconst "IntPlus"))
	     (term-to-term-with-constructors-pushed-inside
	      (mk-term-in-app-form op (car args1)))
	     (term-to-term-with-constructors-pushed-inside
	      (mk-term-in-app-form op (cadr args1)))))
	   ((and (term-in-const-form? op1)
		 (string=? "PosTimes" (const-to-name
				       (term-in-const-form-to-const op1)))
		 (= 2 (length args1)))
	    (mk-term-in-app-form
	     (make-term-in-const-form (pconst-name-to-pconst "IntTimes"))
	     (term-to-term-with-constructors-pushed-inside
	      (mk-term-in-app-form op (car args1)))
	     (term-to-term-with-constructors-pushed-inside
	      (mk-term-in-app-form op (cadr args1)))))
	   (else
	    (mk-term-in-app-form
	     op (term-to-term-with-constructors-pushed-inside (car args)))))))
       ((and (= 2 (length args))
	     (term-in-const-form? op)
	     (string=? (const-to-name (term-in-const-form-to-const op))
		       "RatConstr"))
	(let ((left (car args))
	      (right (cadr args)))
	  (if
	   (not (and (is-numeric-term-wrt-pos? right)
		     (= 1 (numeric-term-wrt-pos-to-number right))))
	   (mk-term-in-app-form
	    (make-term-in-const-form (pconst-name-to-pconst "RatDiv"))
	    (term-to-term-with-constructors-pushed-inside
	     (mk-term-in-app-form op left (make-numeric-term-wrt-pos 1)))
	    (term-to-term-with-constructors-pushed-inside
	     (pos-term-to-rat-term right)))
	   (let* ((mod-left
		   (term-to-term-with-constructors-pushed-inside left))
		  (op1 (term-in-app-form-to-final-op mod-left))
		  (args1 (term-in-app-form-to-args mod-left)))
	     (cond
	      ((and (term-in-const-form? op1)
		    (string=? "IntPlus" (const-to-name
					 (term-in-const-form-to-const op1)))
		    (= 2 (length args1)))
	       (mk-term-in-app-form
		(make-term-in-const-form (pconst-name-to-pconst "RatPlus"))
		(term-to-term-with-constructors-pushed-inside
		 (mk-term-in-app-form
		  op (car args1) (make-numeric-term-wrt-pos 1)))
		(term-to-term-with-constructors-pushed-inside
		 (mk-term-in-app-form
		  op (cadr args1) (make-numeric-term-wrt-pos 1)))))
	      ((and (term-in-const-form? op1)
		    (string=? "IntMinus" (const-to-name
					  (term-in-const-form-to-const op1)))
		    (= 2 (length args1)))
	       (mk-term-in-app-form
		(make-term-in-const-form (pconst-name-to-pconst "RatMinus"))
		(term-to-term-with-constructors-pushed-inside
		 (mk-term-in-app-form
		  op (car args1) (make-numeric-term-wrt-pos 1)))
		(term-to-term-with-constructors-pushed-inside
		 (mk-term-in-app-form
		  op (cadr args1) (make-numeric-term-wrt-pos 1)))))
	      ((and (term-in-const-form? op1)
		    (string=? "IntTimes" (const-to-name
					  (term-in-const-form-to-const op1)))
		    (= 2 (length args1)))
	       (mk-term-in-app-form
		(make-term-in-const-form (pconst-name-to-pconst "RatTimes"))
		(term-to-term-with-constructors-pushed-inside
		 (mk-term-in-app-form
		  op (car args1) (make-numeric-term-wrt-pos 1)))
		(term-to-term-with-constructors-pushed-inside
		 (mk-term-in-app-form
		  op (cadr args1) (make-numeric-term-wrt-pos 1)))))
	      (else
	       (mk-term-in-app-form
		op
		(term-to-term-with-constructors-pushed-inside left)
		(term-to-term-with-constructors-pushed-inside right))))))))
       ((and (= 2 (length args))
	     (term-in-const-form? op)
	     (string=? (const-to-name (term-in-const-form-to-const op))
		       "RealConstr")
	     (term-in-abst-form? (car args))
	     (not (member (term-in-abst-form-to-var (car args))
			  (term-to-free
			   (term-in-abst-form-to-kernel (car args))))))
	(let* ((var (term-in-abst-form-to-var (car args)))
	       (kernel (term-in-abst-form-to-kernel (car args)))
	       (op1 (term-in-app-form-to-final-op kernel))
	       (args1 (term-in-app-form-to-args kernel)))
	  (cond
	   ((and (term-in-const-form? op1)
		 (string=? "RatPlus" (const-to-name
				      (term-in-const-form-to-const op1)))
		 (= 2 (length args1)))
	    (mk-term-in-app-form
	     (make-term-in-const-form (pconst-name-to-pconst "RealPlus"))
	     (term-to-term-with-constructors-pushed-inside
	      (mk-term-in-app-form
	       (make-term-in-const-form (constr-name-to-constr "RealConstr"))
	       (make-term-in-abst-form var (car args1))
	       (cadr args)))
	     (term-to-term-with-constructors-pushed-inside
	      (mk-term-in-app-form
	       (make-term-in-const-form (constr-name-to-constr "RealConstr"))
	       (make-term-in-abst-form var (cadr args1))
	       (cadr args)))))
	   ((and (term-in-const-form? op1)
		 (string=? "RatTimes" (const-to-name
				       (term-in-const-form-to-const op1)))
		 (= 2 (length args1)))
	    (mk-term-in-app-form
	     (make-term-in-const-form (pconst-name-to-pconst "RealTimes"))
	     (term-to-term-with-constructors-pushed-inside
	      (mk-term-in-app-form
	       (make-term-in-const-form (constr-name-to-constr "RealConstr"))
	       (make-term-in-abst-form var (car args1))
	       (cadr args)))
	     (term-to-term-with-constructors-pushed-inside
	      (mk-term-in-app-form
	       (make-term-in-const-form (constr-name-to-constr "RealConstr"))
	       (make-term-in-abst-form var (cadr args1))
	       (cadr args)))))
	   ((and (term-in-const-form? op1)
		 (string=? "RatMinus" (const-to-name
				       (term-in-const-form-to-const op1)))
		 (= 2 (length args1)))
	    (mk-term-in-app-form
	     (make-term-in-const-form (pconst-name-to-pconst "RealMinus"))
	     (term-to-term-with-constructors-pushed-inside
	      (mk-term-in-app-form
	       (make-term-in-const-form (constr-name-to-constr "RealConstr"))
	       (make-term-in-abst-form var (car args1))
	       (cadr args)))
	     (term-to-term-with-constructors-pushed-inside
	      (mk-term-in-app-form
	       (make-term-in-const-form (constr-name-to-constr "RealConstr"))
	       (make-term-in-abst-form var (cadr args1))
	       (cadr args)))))
	   ((and (term-in-const-form? op1)
		 (string=? "RatDiv" (const-to-name
				     (term-in-const-form-to-const op1)))
		 (= 2 (length args1)))
	    (mk-term-in-app-form
	     (make-term-in-const-form (pconst-name-to-pconst "RealDiv"))
	     (term-to-term-with-constructors-pushed-inside
	      (mk-term-in-app-form
	       (make-term-in-const-form (constr-name-to-constr "RealConstr"))
	       (make-term-in-abst-form var (car args1))
	       (cadr args)))
	     (term-to-term-with-constructors-pushed-inside
	      (mk-term-in-app-form
	       (make-term-in-const-form (constr-name-to-constr "RealConstr"))
	       (make-term-in-abst-form var (cadr args1))
	       (cadr args)))))
	   (else term))))
       (else term))))
   (else term)))

;; (define tttwepi term-to-term-with-constructors-pushed-inside)
;; (pp (tttwepi (pt "PosToNat(pos1 + pos2)")))
;; (pp (tttwepi (pt "NatToInt Zero")))
;; (pp (tttwepi (pt "IntP(SZero(SOne pos1))#pos2")))
;; (pp (tttwepi (pt "IntP pos1#pos2")))
;; (pp (tttwepi (pt "IntN(pos1+pos2)#pos3")))
;; (pp (tttwepi (pt "IntP(pos1+pos2)#One")))
;; (pp (tttwepi (pt "pos1-pos2#One")))
;; (pp (tttwepi (pt "IntP(pos1*pos2)#One")))
;; (pp (tttwepi (pt "IntP(pos1*pos2)#pos2")))
;; (pp (tttwepi (pt "IntP(pos1+pos2+pos3)#One")))
;; (pp (tttwepi (pt "IntP(pos1+pos2+pos3)#pos2")))
;; (pp (tttwepi (pt "IntP(pos1+pos2+pos3)#pos1+pos2")))
;; (pp (tttwepi (pt "i#One")))
;; (pp (tttwepi (pt "i1+i2-pos#One")))
;; (pp (tttwepi (pt "RealConstr([n]a*b)([k[Zero)")))

;; We now define term-to-numerator-and-denominator
;; ttnd(a1+a2) := let ttnd(a1)=n1/d1, ttnd(a2)=n2/d2 in (n1*d2 + d1*n2)/(d1*d2)
;; ttnd(a1-a2) := let ttnd(a1)=n1/d1, ttnd(a2)=n2/d2 in (n1*d2 - d1*n2)/(d1*d2)
;; ttnd(a1*a2) := let ttnd(a1)=n1/d1, ttnd(a2)=n2/d2 in (n1*n2)/(d1*d2)
;; ttnd(a1/a2) := let ttnd(a1)=n1/d1, ttnd(a2)=n2/d2 in (n1*d2)/(d1*n2)

(define (term-to-numerator-and-denominator term)
  (let* ((type (term-to-type term))
	 (string (cond ((equal? (make-alg "pos") type) "Pos")
		       ((equal? (make-alg "nat") type) "Nat")
		       ((equal? (make-alg "int") type) "Int")
		       ((equal? (make-alg "rat") type) "Rat")
		       ((equal? (make-alg "rea") type) "Real")
		       (else (myerror "term-to-numerator-and-denominator"
				      "unexpected type"
				      type)))))
    (cond
     ((is-gen-numeric-term? term)
      (list term (num-and-type-to-gen-numeric-term 1 type)))
     ((and (term-in-app-form? term)
	   (let* ((op (term-in-app-form-to-final-op term))
		  (args (term-in-app-form-to-args term))
		  (types (map term-to-type args)))
	     (and (term-in-const-form? op)
		  (= 2 (length args))
		  (equal? (car types) (cadr types))
		  (member (car types)
			  (map make-alg
			       (list "pos" "nat" "int" "rat" "rea"))))))
      (let* ((op (term-in-app-form-to-final-op term))
	     (args (term-in-app-form-to-args term))
	     (arg1 (car args))
	     (arg2 (cadr args))
	     (prev1 (term-to-numerator-and-denominator arg1))
	     (n1 (car prev1))
	     (d1 (cadr prev1))
	     (prev2 (term-to-numerator-and-denominator arg2))
	     (n2 (car prev2))
	     (d2 (cadr prev2))
	     (name (const-to-name (term-in-const-form-to-const op)))
	     (l (string-length name))
	     (make-times-term
	      (lambda (arg1 arg2)
		(cond ((and (is-gen-numeric-term? arg1)
			    (= 1 (gen-numeric-term-to-number arg1)))
		       arg2)
		      ((and (is-gen-numeric-term? arg2)
			    (= 1 (gen-numeric-term-to-number arg2)))
		       arg1)
		      (else (mk-term-in-app-form
			     (make-term-in-const-form
			      (pconst-name-to-pconst
			       (string-append string "Times")))
			     arg1 arg2))))))
	(cond
	 ((string=? (substring name (max 0 (- l (string-length "Plus"))) l)
		    "Plus")
	  (list (mk-term-in-app-form
		 (make-term-in-const-form
		  (pconst-name-to-pconst (string-append string "Plus")))
		 (make-times-term n1 d2)
		 (make-times-term d1 n2))
		(make-times-term d1 d2)))
	 ((string=? (substring name (max 0 (- l (string-length "Minus"))) l)
		    "Minus")
	  (list (mk-term-in-app-form
		 (make-term-in-const-form
		  (pconst-name-to-pconst (string-append string "Minus")))
		 (make-times-term n1 d2)
		 (make-times-term d1 n2))
		(make-times-term d1 d2)))
	 ((string=? (substring name (max 0 (- l (string-length "Times"))) l)
		    "Times")
	  (list (make-times-term n1 n2) (make-times-term d1 d2)))
	 ((string=? (substring name (max 0 (- l (string-length "Div"))) l)
		    "Div")
	  (list (make-times-term n1 d2) (make-times-term d1 n2)))
	 ((and (string=? name "RatConstr")  (string=? "Rat" string))
	  (list (int-term-to-rat-term arg1) (pos-term-to-rat-term arg2)))
	 (else (list term (num-and-type-to-gen-numeric-term 1 type))))))
     (else (list term (num-and-type-to-gen-numeric-term 1 type))))))

;; (define ttnad term-to-numerator-and-denominator)
;; (map term-to-string (ttnad (pt "a")))
;; (map term-to-string (ttnad (pt "a/b")))
;; (map term-to-string (ttnad (pt "a*b")))
;; (map term-to-string (ttnad (pt "a+b")))
;; (map term-to-string (ttnad (pt "(a1/b1)/(a2/b2)")))
;; (map term-to-string (ttnad (pt "i#SZero One")))
;; (map term-to-string (ttnad (pt "x/y")))
;; (map term-to-string (ttnad (pt "x*y")))
;; (map term-to-string (ttnad (pt "x+y")))
;; (map term-to-string (ttnad (pt "(x1/y1)/(x2/y2)")))

;; Next, some operators are applied to the numerator and denominator
;; separately: term-to-posmonoms-and-negmonoms needs distribute-prod,
;; which distributes * over two lists.

(define (term-to-posmonoms-and-negmonoms term) ;yields a list of monom-lists
  (let* ((op (term-in-app-form-to-final-op term))
	 (args (term-in-app-form-to-args term))
	 (type (term-to-type term))
	 (string (cond ((equal? (py "pos") type) "Pos")
		       ((equal? (py "nat") type) "Nat")
		       ((equal? (py "int") type) "Int")
		       ((equal? (py "rat") type) "Rat")
		       ((equal? (py "rea") type) "Real")
		       (else (myerror "term-to-posmonoms-and-negmonoms"
				      "unexpected type"
				      type))))
	 (make-times-term
	  (lambda (arg1 arg2)
	    (cond ((and (is-gen-numeric-term? arg1)
			(= 1 (gen-numeric-term-to-number arg1)))
		   arg2)
		  ((and (is-gen-numeric-term? arg2)
			(= 1 (gen-numeric-term-to-number arg2)))
		   arg1)
		  (else (mk-term-in-app-form
			 (make-term-in-const-form
			  (pconst-name-to-pconst
			   (string-append string "Times")))
			 arg1 arg2)))))
	 (distribute-prod
	  (lambda (terms1 terms2)
	    (do ((l terms1 (cdr l))
		 (res '() (append res
				  (map (lambda (y) (make-times-term (car l) y))
				       terms2))))
		((null? l) res)))))
    (cond
     ((and (term-in-const-form? op)
	   (member (const-to-name (term-in-const-form-to-const op))
		   '("Zero" "IntZero")))
      (list '() '()))
     ((and (term-in-const-form? op) (= 1 (length args))
	   (member (const-to-name (term-in-const-form-to-const op))
		   '("S" "Succ" "IntS")))
      (let* ((arg (car args))
	     (prev (term-to-posmonoms-and-negmonoms arg))
	     (posprev (car prev))
	     (negprev (cadr prev)))
	(list (append posprev (list (pt "1"))) negprev)))
     ((and
       (term-in-const-form? op) (= 2 (length args))
       (member
	(const-to-name (term-in-const-form-to-const op))
	'("PosPlus" "NatPlus" "IntPlus" "RatPlus" "RealPlus" "CpxPlus"
	  "PosMinus" "NatMinus" "IntMinus" "RatMinus" "RealMinus" "CpxMinus" 
	  "PosTimes" "NatTimes" "IntTimes" "RatTimes" "RealTimes" "CpxTimes")))
      (let* ((arg1 (car args))
	     (arg2 (cadr args))
	     (prev1 (term-to-posmonoms-and-negmonoms arg1))
	     (prev2 (term-to-posmonoms-and-negmonoms arg2))
	     (posprev1 (car prev1))
	     (negprev1 (cadr prev1))
	     (posprev2 (car prev2))
	     (negprev2 (cadr prev2))
	     (name (const-to-name (term-in-const-form-to-const op)))
	     (l (string-length name)))
	(cond
	 ((string=? (substring name (max 0 (- l (string-length "Plus"))) l)
		    "Plus")
	  (list (append posprev1 posprev2) (append negprev1 negprev2)))
	 ((string=? (substring name (max 0 (- l (string-length "Minus"))) l)
		    "Minus")
	  (list (append posprev1 negprev2) (append negprev1 posprev2)))
	 ((string=? (substring name (max 0 (- l (string-length "Times"))) l)
		    "Times")
	  (list (append (distribute-prod posprev1 posprev2)
			(distribute-prod negprev1 negprev2))
		(append (distribute-prod posprev1 negprev2)
			(distribute-prod negprev1 posprev2))))
	 (else (list (list term) '())))))
     (else (list (list term) '())))))

;; monom-to-num-with-stringpowers collects general numeric terms into a
;; product number and writes each factor as a list of a string and its
;; power: (27 ("a" 2) ("b" 1) ("c" 3))

(define (monom-to-num-with-stringpowers monom)
  (let ((op (term-in-app-form-to-final-op monom)))
    (if
     (and (term-in-const-form? op)
	  (let* ((name (const-to-name (term-in-const-form-to-const op)))
		 (l (string-length name))
		 (times-string
		  (substring name (max 0 (- l (string-length "Times"))) l)))
	    (string=? "Times" times-string)))
     (let* ((args (term-in-app-form-to-args monom))
	    (arg1 (if (= 2 (length args))
		      (car args)
		      (myerror "monom-to-num-with-stringpowers"
			       "2 args expected"
			       (map term-to-string args))))
	    (arg2 (cadr args))
	    (num-with-stringpowers1 (monom-to-num-with-stringpowers arg1))
	    (num1 (car num-with-stringpowers1))
	    (stringpowers1 (cdr num-with-stringpowers1))
	    (num-with-stringpowers2 (monom-to-num-with-stringpowers arg2))
	    (num2 (car num-with-stringpowers2))
	    (stringpowers2 (cdr num-with-stringpowers2)))
       (cons (* num1 num2) (append stringpowers1 stringpowers2)))
     (if (is-gen-numeric-term? monom)
	 (cons (gen-numeric-term-to-number monom) '())
	 (cons 1 (list (list (term-to-string monom) 1)))))))

;; We now aim at term-to-joined-num-joined-stringpowers-list. It sorts
;; and joins stringpowers as well as summands.

(define (stringpowers-to-joined-stringpowers stringpowers)
  (if (<= (length stringpowers) 1)
      stringpowers
      (let* ((fst (car stringpowers))
	     (string1 (car fst))
	     (num1 (cadr fst))
	     (prev (stringpowers-to-joined-stringpowers (cdr stringpowers)))
	     (snd (car prev))
	     (string2 (car snd))
	     (num2 (cadr snd)))
	(if (string=? string1 string2)
	    (cons (list string1 (+ num1 num2)) (cdr prev))
	    (cons fst prev)))))

(define (num-stringpowers-list-to-joined-num-joined-stringpowers-list
	 num-stringpowers-list)
  (if (null? num-stringpowers-list)
      '()
      (let* ((fst (car num-stringpowers-list))
	     (num1 (car fst))
	     (joined-stringpowers1
	      (stringpowers-to-joined-stringpowers (cdr fst)))
	     (prev
	      (num-stringpowers-list-to-joined-num-joined-stringpowers-list
	       (cdr num-stringpowers-list))))
	(if (null? prev)
	    (list (cons num1 joined-stringpowers1))
	    (let* ((snd (car prev))
		   (num2 (car snd))
		   (joined-stringpowers2 (cdr snd)))
	      (if (and (= (length joined-stringpowers1)
			  (length joined-stringpowers2))
		       (apply and-op (map stringpower=?
					  joined-stringpowers1
					  joined-stringpowers2)))
		  (if (zero? (+ num1 num2))
		      (cdr prev)
		      (cons (cons (+ num1 num2) joined-stringpowers1)
			    (cdr prev)))
		  (cons (cons num1 joined-stringpowers1) prev)))))))

(define (stringpower<? stringpower1 stringpower2)
  (string<? (car stringpower1) (car stringpower2)))

(define (stringpower=? stringpower1 stringpower2)
  (and (string=? (car stringpower1) (car stringpower2))
       (= (cadr stringpower1) (cadr stringpower2))))

(define (stringpower-and-type-to-term stringpower type)
  (let* ((type-string
	  (cond ((equal? (py "pos") type) "Pos")
		((equal? (py "nat") type) "Nat")
		((equal? (py "int") type) "Int")
		((equal? (py "rat") type) "Rat")
		((equal? (py "rea") type) "Real")
		(else (myerror "stringpower-and-type-to-term"
			       "unexpected type"
			       type))))
	 (string (car stringpower))
	 (num (cadr stringpower)))
    (if (= 1 num)
	(pt string)
	(mk-term-in-app-form
	 (make-term-in-const-form
	  (pconst-name-to-pconst (string-append type-string "Exp")))
	 (pt string)
	 (make-numeric-term-wrt-pos num)))))

(define (stringpowers-and-type-to-term stringpowers type)
  (if (null? stringpowers)
      (num-and-type-to-gen-numeric-term 1 type)
      (apply mk-* (map (lambda (x) (stringpower-and-type-to-term x type))
		       stringpowers))))

(define (num-stringpowers-and-type-to-term num-stringpowers type)
  (let* ((num (car num-stringpowers))
	 (num-term (num-and-type-to-gen-numeric-term num type))
	 (stringpowers (cdr num-stringpowers)))
    (if (null? stringpowers)
	num-term
	(if (= 1 num)
	    (apply
	     mk-* (map (lambda (x) (stringpower-and-type-to-term x type))
		       stringpowers))
	    (apply
	     mk-* (cons num-term
			(map (lambda (x) (stringpower-and-type-to-term x type))
			     stringpowers)))))))

;; Insertion sort

(define (insert x lt? sorted-list)
  (if (null? sorted-list)
      (list x)
      (let ((fst (car sorted-list)))
	(if (lt? x fst)
	    (cons x sorted-list)
	    (cons fst (insert x lt? (cdr sorted-list)))))))

(define (insertsort lt? l)
  (if (null? l)
      l
      (insert (car l) lt? (insertsort lt? (cdr l)))))

;; Lexicographic extension of an ordering

(define (lex-ext equality? lt?)
  (lambda (l1 l2)
    (and (not (null? l2))
	 (or (null? l1)
	     (let ((fst1 (car l1))
		   (fst2 (car l2)))
	       (or (lt? fst1 fst2)
		   (and (equality? fst1 fst2)
			((lex-ext  equality? lt?) (cdr l1) (cdr l2)))))))))

(define (mk-+ term . terms)
  (if (null? terms)
      term
      (let* ((init-terms (list-head terms (- (length terms) 1)))
	     (y (car (last-pair terms)))
	     (x (apply mk-+ (cons term init-terms)))
	     (type1 (term-to-type x))
	     (type2 (term-to-type y))
	     (type (types-lub type1 type2))
	     (type-string
	      (cond ((equal? (py "pos") type) "Pos")
		    ((equal? (py "nat") type) "Nat")
		    ((equal? (py "int") type) "Int")
		    ((equal? (py "rat") type) "Rat")
		    ((equal? (py "rea") type) "Real")
		    (else (myerror "mk-+" "unexpected type" type))))
	     (internal-name (string-append type-string "Plus")))
	(mk-term-in-app-form
	 (make-term-in-const-form (pconst-name-to-pconst internal-name))
	 x y))))

(define (mk-* term . terms)
  (if (null? terms)
      term
      (let* ((init-terms (list-head terms (- (length terms) 1)))
	     (y (car (last-pair terms)))
	     (x (apply mk-* (cons term init-terms)))
	     (type1 (term-to-type x))
	     (type2 (term-to-type y))
	     (type (types-lub type1 type2))
	     (type-string
	      (cond ((equal? (py "pos") type) "Pos")
		    ((equal? (py "nat") type) "Nat")
		    ((equal? (py "int") type) "Int")
		    ((equal? (py "rat") type) "Rat")
		    ((equal? (py "rea") type) "Real")
		    (else (myerror "mk-*" "unexpected type" type))))
	     (internal-name (string-append type-string "Times")))
	(mk-term-in-app-form
	 (make-term-in-const-form (pconst-name-to-pconst internal-name))
	 x y))))

(define (mk-/ term1 term2)
  (let* ((type1 (term-to-type term1))
	 (type2 (term-to-type term2))
	 (type (types-lub type1 type2 (py "int")))
	 (string (cond ((equal? (py "int") type) "Int")
		       ((equal? (py "rat") type) "Rat")
		       ((equal? (py "rea") type) "Real")
		       (else (myerror "mk-/" "unexpected type" type)))))
    (apply mk-term-in-app-form
	   (cons (make-term-in-const-form
		  (pconst-name-to-pconst (string-append string "Div")))
		 (list term1 term2)))))

;; We use ratnums-to-ratnum-and-intnums to turn a list of Scheme
;; rationals into a Scheme rational and a list of Scheme integers
;; without a common divisor: (n1/d1 n2/d2 n3/d3) -> (n/d (i1 i2 i3))
;; such that (n/d)*i1=n1/d1 etc.

(define (ratnums-to-ratnum-and-intnums ratnum . ratnums)
  (let* ((denoms (cons (denominator ratnum) (map denominator ratnums)))
	 (m (apply lcm denoms))
	 (nums (map (lambda (x) (* m x)) (cons ratnum ratnums)))
	 (g (apply gcd nums))
	 (red-nums (map (lambda (x) (/ x g)) nums)))
    (list (/ g m) red-nums)))

;; (ratnums-to-ratnum-and-intnums (/ 20 3) (/ 16 4))
;; (ratnums-to-ratnum-and-intnums (/ 20 3) (/ 17 4))
;; (ratnums-to-ratnum-and-intnums (/ -1 3) (/ 1 4))
;; (ratnums-to-ratnum-and-intnums 6 4 32)
;; (ratnums-to-ratnum-and-intnums 8 4 32)

(define (nsps-list-to-ratnum-and-nsps-list nsps-list)
  (if (null? nsps-list)
      (list 0 '())
      (let* ((ratnums (map car nsps-list))
	     (sps-list (map cdr nsps-list))
	     (ratnum-and-intnums (apply ratnums-to-ratnum-and-intnums ratnums))
	     (ratnum (car ratnum-and-intnums))
	     (intnums (cadr ratnum-and-intnums)))
	(list ratnum (map (lambda (x y) (cons x y)) intnums sps-list)))))

;; We now simplify a quotient of two joined-num-joined-stringpowers-lists
;; ((27 ("a1" 2) ("a2" 1)) (9 ("a1" 3)) / ((13) (27 ("b1" 1) ("b2" 3)))
;; We turn the numerator and denominator from sums into products, to
;; make cancellation possible.  Apply distributivity backwards.
;; Uses nsps-list-to-common-sps-and-non-common-nsps-list where
;; sps is short for stringpowers, nsps is short for num-stringpowers.
;; It is assumed that nums are integers without a common divisor.
;; Example:
;; (define nspsl '((3 ("a" 1) ("b" 2) ("c" 1)) (4 ("a" 3) ("b" 1) ("c" 1)) (5 ("a" 2) ("b" 2))))
;; (nsps-list-to-common-sps-and-non-common-nsps-list nspsl)
;; ((("a" 1) ("b" 1)) ;common-sps
;;  ((3 ("b" 1) ("c" 1)) (4 ("a" 2) ("c" 1)) (5 ("a" 1) ("b" 1))))
;; ((("a" 1) ("b" 1)) ;common-sps
;;  (3 ("b" 1) ("c" 1))
;;  (4 ("a" 2) ("c" 1))
;;  (5 ("a" 1) ("b" 1)))

(define (nsps-list-to-common-sps-and-non-common-nsps-list nsps-list)
  (if (null? nsps-list)
      (list '() '())
      (let* ((nums (map car nsps-list))
	     (sps-list (map cdr nsps-list))
	     (common-sps-and-non-common-sps-list
	      (sps-list-to-common-sps-and-non-common-sps-list sps-list))
	     (common-sps (car common-sps-and-non-common-sps-list))
	     (non-common-sps-list (cadr common-sps-and-non-common-sps-list))
	     (non-common-nsps-list
	      (map (lambda (num sps) (cons num sps))
		   nums non-common-sps-list))
	     (sorted-non-common-nsps-list
	       (insertsort
		(lambda (x y)
		  ((lex-ext stringpower=? stringpower<?) (cdr x) (cdr y)))
		non-common-nsps-list)))
	(list common-sps sorted-non-common-nsps-list))))

(define (sps-list-to-common-sps-and-non-common-sps-list sps-list)
  (if
   (apply and-op (map pair? sps-list))
   (let* ((sps (map car sps-list))
	  (strings (map car sps)))
     (if
      (string-list=? strings)
      (let* ((string (car strings))
	     (powers (map cadr sps))
	     (m (apply min powers))
	     (rest-powers (map (lambda (x) (- x m)) powers)) ;one is 0
	     (red-sps-list
	      (map (lambda (rest-power sps)
		     (if (zero? rest-power)
			 (cdr sps)
			 (cons (list string rest-power) (cdr sps))))
		   rest-powers sps-list))
	     (prev (sps-list-to-common-sps-and-non-common-sps-list
		    red-sps-list))
	     (prev-common-sps (car prev))
	     (prev-non-common-sps-list (cadr prev)))
	(list (cons (list string m) prev-common-sps) prev-non-common-sps-list))
      (let* ((string (apply string-max strings))
	     (ncsps-list
	      (map (lambda (sps)
		     (list-transform-positive sps
		       (lambda (sp) (string<? (car sp) string))))
		   sps-list))
	     (red-sps-list
	      (map (lambda (sps)
		     (list-transform-positive sps
		       (lambda (sp) (not (string<? (car sp) string)))))
		   sps-list))
	     (prev (sps-list-to-common-sps-and-non-common-sps-list
		    red-sps-list))
	     (prev-common-sps (car prev))
	     (prev-non-common-sps-list (cadr prev)))
	(list prev-common-sps (map (lambda (ncsps x) (append ncsps x))
				   ncsps-list prev-non-common-sps-list)))))
   (list '() sps-list)))

(define (string-max string . strings)
  (do ((l strings (cdr l))
       (res string (if (string<? res (car l)) (car l) res)))
      ((null? l) res)))

;; (define sps-list '((("a" 1) ("b" 2) ("c" 1)) (("a" 3) ("b" 1) ("c" 1)) (("a" 2) ("b" 2))))
;; (sps-list-to-common-sps-and-non-common-sps-list sps-list)

;; ((("a" 1) ("b" 1)) ;common-sps
;;  ((("b" 1) ("c" 1)) (("a" 2) ("c" 1)) (("a" 1) ("b" 1))))

;; Cancellation:  We are given a quotient
;; num1 common-sps1 non-common-nsps-list1 /
;; num2 common-sps2 non-common-nsps-list2
;; and produce a product of (/ num1 num2) and the quotient 
;; cancelled-common-sps1 non-common-nsps-list1 /
;; cancelled-common-sps2 non-common-nsps-list2
;; in case non-common-nsps-list1 and non-common-nsps-list2 differ, and 
;; cancelled-common-sps1 / cancelled-common-sps2
;; in case non-common-nsps-list1 and non-common-nsps-list2 are equal.
;; For this we need cancel-common-sps.

(define (cancel-common-sps sps1 sps2)
  (if
   (or (null? sps1) (null? sps2))
   (list sps1 sps2)
   (let ((s1 (caar sps1))
	 (p1 (cadar sps1))
	 (s2 (caar sps2))
	 (p2 (cadar sps2)))
     (cond
      ((string=? s1 s2)
       (let* ((prev (cancel-common-sps (cdr sps1) (cdr sps2)))
	      (prev-sps1 (car prev))
	      (prev-sps2 (cadr prev)))
	 (cond
	  ((= p1 p2) (list prev-sps1 prev-sps2))
	  ((< p1 p2) (list prev-sps1 (cons (list s2 (- p2 p1)) prev-sps2)))
	  ((> p1 p2) (list (cons (list s1 (- p1 p2)) prev-sps1) prev-sps2)))))
      ((string<? s1 s2)
       (let* ((prev (cancel-common-sps (cdr sps1) sps2))
	      (prev-sps1 (car prev))
	      (prev-sps2 (cadr prev)))
	 (list (cons (car sps1) prev-sps1) prev-sps2)))
      ((string>? s1 s2)
       (let* ((prev (cancel-common-sps sps1 (cdr sps2)))
	      (prev-sps1 (car prev))
	      (prev-sps2 (cadr prev)))
	 (list prev-sps1 (cons (car sps2) prev-sps2))))))))

;; (cancel-common-sps '(("a" 3) ("c" 2)) '(("a" 2) ("b" 5) ("c" 3)))
;; ((("a" 1)) (("b" 5) ("c" 1)))

;; Finally construct the result term: take mk-* for the common-sps and
;; mk-+ with mk-* for the non-common-nsps-list.

;; The general procedure packaging the previous ones together:

(define (term-to-ratnum-and-common-sps-and-non-common-nsps-list term)
  (let* ((posmonoms-and-negmonoms (term-to-posmonoms-and-negmonoms term))
	 (posmonoms (car posmonoms-and-negmonoms))
	 (negmonoms (cadr posmonoms-and-negmonoms))
	 (pos-num-with-stringpowers-list
	  (list-transform-positive (map monom-to-num-with-stringpowers
					posmonoms)
	    (lambda (x) (not (zero? (car x))))))
	 (neg-num-with-stringpowers-list
	  (list-transform-positive (map monom-to-num-with-stringpowers
					negmonoms)
	    (lambda (x) (not (zero? (car x))))))
	 (num-with-stringpowers-list
	  (append pos-num-with-stringpowers-list
		  (map (lambda (nsps) (cons (- (car nsps)) (cdr nsps)))
		       neg-num-with-stringpowers-list)))
	 (num-with-sorted-stringpowers-list
	  (map (lambda (x) (cons (car x) (insertsort stringpower<? (cdr x))))
	       num-with-stringpowers-list))
	 (sorted-num-with-sorted-stringpowers-list
	  (insertsort
	   (lambda (x y)
	     ((lex-ext stringpower=? stringpower<?) (cdr x) (cdr y)))
	   num-with-sorted-stringpowers-list))
	 (joined-num-joined-stringpowers-list
	  (num-stringpowers-list-to-joined-num-joined-stringpowers-list
	   sorted-num-with-sorted-stringpowers-list))
	 (ratnum-and-nsps-list (nsps-list-to-ratnum-and-nsps-list
				joined-num-joined-stringpowers-list))
	 (ratnum (car ratnum-and-nsps-list))
	 (nsps-list (cadr ratnum-and-nsps-list))
	 (common-sps-and-non-common-nsps-list
	  (nsps-list-to-common-sps-and-non-common-nsps-list nsps-list)))
    (cons ratnum common-sps-and-non-common-nsps-list)))
  
(define (equal-nsps-lists-of-different-signs? nsps-list1 nsps-list2)
  (and (pair? nsps-list1)
       (= (length nsps-list1) (length nsps-list2))
       (let ((nums1 (map car nsps-list1))
	     (nums2 (map car nsps-list2)))
	 (apply and-op (map (lambda (n1 n2) (= n1 (- n2))) nums1 nums2)))
       (let ((sps1 (map cdr nsps-list1))
	     (sps2 (map cdr nsps-list2)))
	 (equal? sps1 sps2))))

;(equal-nsps-lists-of-different-signs? '((1) (-7 ("a" 2))) '((-1) (7 ("a" 2))))

(define (term-to-num-and-sps1-and-nsps-list1-and-sps2-and-nsps-list2 term)
  (let* ((term-with-unfolded-exps
	  (term-to-term-with-unfolded-exponents term))
	 (term-with-arith-free-outer-number-constrs
	  (term-to-term-with-constructors-pushed-inside
	   term-with-unfolded-exps))
	 (numer-and-denom (term-to-numerator-and-denominator
			   term-with-arith-free-outer-number-constrs))
	 (numer (car numer-and-denom))
	 (denom (cadr numer-and-denom))
	 (ratnum-and-common-sps-and-non-common-nsps-list1
	  (term-to-ratnum-and-common-sps-and-non-common-nsps-list numer))
	 (ratnum1 (car ratnum-and-common-sps-and-non-common-nsps-list1))
	 (common-sps1 (cadr ratnum-and-common-sps-and-non-common-nsps-list1))
	 (non-common-nsps-list1
	  (caddr ratnum-and-common-sps-and-non-common-nsps-list1))
	 (ratnum-and-common-sps-and-non-common-nsps-list2
	  (term-to-ratnum-and-common-sps-and-non-common-nsps-list denom))
	 (ratnum2 (car ratnum-and-common-sps-and-non-common-nsps-list2))
	 (common-sps2 (cadr ratnum-and-common-sps-and-non-common-nsps-list2))
	 (non-common-nsps-list2
	  (caddr ratnum-and-common-sps-and-non-common-nsps-list2))
	 (ratnum (/ ratnum1 ratnum2))
	 (cancelled-common-sps (cancel-common-sps common-sps1 common-sps2))
	 (cancelled-common-sps1 (car cancelled-common-sps))
	 (cancelled-common-sps2 (cadr cancelled-common-sps))
	 (equal-nsps-lists? (equal? non-common-nsps-list1
				    non-common-nsps-list2))
	 (diff-signs? (equal-nsps-lists-of-different-signs?
		       non-common-nsps-list1 non-common-nsps-list2))
	 (cancelled-nsps-list1 (cond (equal-nsps-lists? '((1)))
				     (diff-signs? '((-1)))
				     (else non-common-nsps-list1)))
	 (cancelled-nsps-list2 (if (or equal-nsps-lists? diff-signs?)
				   '((1))
				   non-common-nsps-list2)))
    (list ratnum
	  cancelled-common-sps1 cancelled-nsps-list1
	  cancelled-common-sps2 cancelled-nsps-list2)))

(define ttnasanl term-to-num-and-sps1-and-nsps-list1-and-sps2-and-nsps-list2)
;; (ttnasanl (pt "(IntN(SOne One)#One)*a*a"))
;; => (3 (("a" 2)) ((-1)) () ((1)))

;; (ttnasanl (pt "(a+b)/((IntN One#One)*a-b)"))
;; => (1 () ((-1)) () ((1)))

(define (nsps-list-and-type-to-term num-stringpowers-list type)
  (if (null? num-stringpowers-list)
      (num-and-type-to-gen-numeric-term 0 type)
      (let ((prod-terms
	     (map (lambda (x) (num-stringpowers-and-type-to-term x type))
		  num-stringpowers-list)))
	(apply mk-+ prod-terms))))

(define (sps-and-nsps-list-and-type-to-pos?-and-term sps nsps-list type)
  (cond
   ((equal? '((1)) nsps-list)
    (list #t (stringpowers-and-type-to-term sps type)))
   ((equal? '((-1)) nsps-list)
    (list #f (stringpowers-and-type-to-term sps type)))
   (else
    (list #t
	  (if (null? sps)
	      (nsps-list-and-type-to-term nsps-list type)
	      (mk-* (apply mk-* (map (lambda (x)
				       (stringpower-and-type-to-term x type))
				     sps))
		    (nsps-list-and-type-to-term nsps-list type)))))))

(define (simp-term term)
  (let* ((x (term-to-num-and-sps1-and-nsps-list1-and-sps2-and-nsps-list2 term))
	 (num (car x))
	 (sps1 (cadr x))
	 (nsps-list1 (caddr x))
	 (sps2 (cadddr x))
	 (nsps-list2 (car (cddddr x)))
	 (type (term-to-type term))
	 (pos1?-and-numer-term
	  (sps-and-nsps-list-and-type-to-pos?-and-term sps1 nsps-list1 type))
	 (pos1? (car pos1?-and-numer-term))
	 (numer-term (cadr pos1?-and-numer-term))
	 (pos2?-and-denom-term
	  (sps-and-nsps-list-and-type-to-pos?-and-term sps2 nsps-list2 type))
	 (pos2? (car pos2?-and-denom-term))
	 (denom-term (cadr pos2?-and-denom-term))
	 (numer-is-1? (and (null? sps1) (equal? '((1)) nsps-list1)))
	 (denom-is-1? (and (null? sps2) (equal? '((1)) nsps-list2)))
	 (pos? (or (and pos1? pos2?) (and (not pos1?) (not pos2?))))
	 (signed-num (if pos? num (- num))))
    (if denom-is-1?
	(if (= 1 signed-num)
	    numer-term
	    (if numer-is-1?
		(num-and-type-to-gen-numeric-term signed-num type)
		(mk-* (num-and-type-to-gen-numeric-term signed-num type)
		      numer-term)))
	(if (= 1 signed-num)
	    (mk-/ numer-term denom-term)
	    (mk-* (num-and-type-to-gen-numeric-term signed-num type)
		  (mk-/ numer-term denom-term))))))

;; Tests
;; (pp (simp-term (pt "(IntP One#SZero One)")))
;; (pp (simp-term (pt "a/b")))
;; (pp (simp-term (pt "(a*a)/b")))
;; (pp (simp-term (pt "(a*a)/(a*b)")))
;; (pp (simp-term (pt "((IntP One#SZero One)*a*a)/(a*b)")))
;; (pp (simp-term (pt "(a*a+a*b)/(a*b)")))
;; (pp (simp-term (pt "a*a+(IntP(SZero One)#One)*a*b+b*b")))
;; (pp (simp-term (pt "(a+b)*(a+b)")))
;; (pp (simp-term (pt "(a+b)**2")))
;; (pp (simp-term (pt "(a+b)/(a+b)")))
;; (pp (simp-term (pt "(a+b)*(a+b)/(a+b)")))
;; (pp (simp-term (pt "(IntP One/2**(k+1))+(IntP One/2**(k+1))")))

;; Tests
;; (pp (simp-term (pt "(2**(k+1))")))
;; (pp (simp-term (pt "(IntP(SZero One)#One)*((IntP One#One)/(IntP(SZero One)#One))")))
;; (pp (simp-term (pt "(IntP(SZero One)#One)*(IntP One/2)")))
;; (pp (simp-term (pt "(IntP(SZero One)#One)*(IntP One/(2*3))")))
;; (pp (simp-term (pt "(IntP One/(2*3))")))
;; (pp (simp-term (pt "(One#SZero One)**(k+1)")))
;; (pp (simp-term (pt "((One#SZero One)**(k+1))+((One#SZero One)**(k+1))")))
;; (pp (simp-term (pt "((One#SZero One)**(k+2))+((One#SZero One)**(k+1))+((One#SZero One)**(k+2))")))

;; (pp (simp-term (pt "(l+l+k)")))
;; (pp (simp-term (pt "One/y")))
;; (pp (simp-term (pt "n/y")))
;; (pp (simp-term (pt "pos/y")))
;; (pp (simp-term (pt "(i*i)/y")))
;; (pp (simp-term (pt "(a*a)/y")))
;; (pp (simp-term (pt "(x*x)/y")))

(define (positive-num-stringpowers-list? nsps-list type)
  (and (pair? nsps-list)
       (= 1 (length (car nsps-list)))
       (number? (caar nsps-list))
       (positive? (caar nsps-list))
       (apply and-op
	      (map (lambda (nsps)
		     (and (positive? (car nsps))
			  (or (equal? (py "pos") type)
			      (apply and-op
				     (map even? (map cadr (cdr nsps)))))))
		   nsps-list))))

(define (negative-num-stringpowers-list? nsps-list type)
  (and (pair? nsps-list)
       (= 1 (length (car nsps-list)))
       (number? (caar nsps-list))
       (negative? (caar nsps-list))
       (apply and-op
	      (map (lambda (nsps)
		     (and (negative? (car nsps))
			  (or (equal? (py "pos") type)
			      (apply and-op
				     (map even? (map cadr (cdr nsps)))))))
		   nsps-list))))

'(
(negative-num-stringpowers-list?
 '((-1) (-3 ("a" 2) ("b" 2) ("c" 6))) (py "rat"))

(positive-num-stringpowers-list?
 '((1) (3 ("a" 2) ("b" 2) ("c" 6)) (4 ("a" 4) ("b" 2))) (py "rat"))
)

;; Consider a term built from variables, constants One, IntZero and
;; reals formed with RealConstr by + - * / and exp.  We assign to the
;; term its non-zero-strings with the property: all must be non-zero
;; for the term to be defined, and its factor-strings with the
;; property: if all factors are non-zero, then the term is non-zero.

(define (term-to-non-zero-strings-and-factor-strings term)
  (cond
   ((and (is-gen-numeric-term? term)
	 (not (= 0 (gen-numeric-term-to-number term))))
    (list '() '()))
   ((term-in-abst-form? term)
    (let* ((kernel (term-in-abst-form-to-kernel term))
	   (prev (term-to-non-zero-strings-and-factor-strings kernel))
	   (non-zero-strings (car prev))
	   (factor-strings (cadr prev)))
      (list non-zero-strings factor-strings)))
   (else
    (let ((op (term-in-app-form-to-final-op term))
	  (args (term-in-app-form-to-args term)))
      (cond
       ((and (term-in-const-form? op)
	     (member (const-to-name (term-in-const-form-to-const op))
		     '("SZero" "SOne" "Succ" "PosToNat" "IntPos" "IntNeg"))
	     (= 1 (length args)))
	(let* ((prev (term-to-non-zero-strings-and-factor-strings (car args)))
	       (non-zero-strings (car prev)))
	  (list non-zero-strings '())))
       ((and (term-in-const-form? op)
	     (member (const-to-name (term-in-const-form-to-const op))
		     '("NatAbs" "IntAbs" "RatAbs" "RealAbs" "CpxAbs"))
	     (= 1 (length args)))
	(let* ((prev (term-to-non-zero-strings-and-factor-strings
		      (term-to-original (car args))))
	       (non-zero-strings (car prev))
	       (factor-strings (cadr prev)))
	  (list non-zero-strings factor-strings)))
       ((and (term-in-const-form? op)
	     (= 2 (length args)))
	(let* ((arg1 (term-to-original (car args)))
	       (arg2 (term-to-original (cadr args)))
	       (prev1 (term-to-non-zero-strings-and-factor-strings arg1))
	       (non-zero-strings1 (car prev1))
	       (factor-strings1 (cadr prev1))
	       (prev2 (term-to-non-zero-strings-and-factor-strings arg2))
	       (non-zero-strings2 (car prev2))
	       (factor-strings2 (cadr prev2))
	       (name (const-to-name (term-in-const-form-to-const op)))
	       (l (string-length name)))
	  (cond
	   ((or
	     (string=? (substring name (max 0 (- l (string-length "Plus"))) l)
		       "Plus")
	     (string=? (substring name (max 0 (- l (string-length "Minus"))) l)
		       "Minus"))
	    (list (union non-zero-strings1 non-zero-strings2)
		  (list (term-to-string term))))
	   ((string=? (substring name (max 0 (- l (string-length "Times"))) l)
		      "Times")
	    (list (union non-zero-strings1 non-zero-strings2)
		  (union factor-strings1 factor-strings2)))
	   ((string=? (substring name (max 0 (- l (string-length "Div"))) l)
		      "Div")
	    (list (union non-zero-strings1 non-zero-strings2 factor-strings2)
		  factor-strings1))
	   ((or
	     (member name '("RatConstr" "RealConstr"))
	     (string=? (substring name (max 0 (- l (string-length "Exp"))) l)
		       "Exp"))
	    (list (union non-zero-strings1 non-zero-strings2)
		  factor-strings1))
	   (else (list '() (list (term-to-string term)))))))
       (else (list '() (list (term-to-string term)))))))))

;; (term-to-non-zero-strings-and-factor-strings (pt "(a+c)/b"))
;; (term-to-non-zero-strings-and-factor-strings (pt "(a/b)/(c1/c2)"))
;; (term-to-non-zero-strings-and-factor-strings (pt "((a+b)*c)/(c1*c2)"))
;; (term-to-non-zero-strings-and-factor-strings (pt "(x+z)/y"))
;; (term-to-non-zero-strings-and-factor-strings (pt "((x+b)*z)/(z1*z2)"))
;; (term-to-non-zero-strings-and-factor-strings (pt "1/2**k"))

(define (term-to-non-zero-strings term)
  (car (term-to-non-zero-strings-and-factor-strings term)))

;; simp-comparison simplifies a comparison (using =, <= or <) of two
;; terms (of type pos, nat, int or rat).  It proceeds as follows.

;; (1) Transform r1=r2 into 0=(r1-r2), and similarly for <= and <. So we
;; can assume that the lhs is 0.

;; (2) Using the field axioms (in particular commutativity and
;; distributivity), bring the rhs in a form number times quotient of two
;; terms (numerator and denominator), each of which is a product of some
;; powers and a polynomial.

;; (3) Simplify, by cancelling equal factors in numerator and
;; denominator, removing the denominator by multiplying with the
;; (positive) square of the denominator, removing non-zero factors from
;; the numerator and reducing power factors to exponent 1 (for =) and 1
;; or 2 (for <, <=)

(define (is-comparison? atom-or-pred)
  (or (and (atom-form? atom-or-pred)
	   (let* ((kernel (atom-form-to-kernel atom-or-pred))
		  (op (term-in-app-form-to-final-op kernel)))
	     (and 
	      (term-in-const-form? op)
	      (member (const-to-name (term-in-const-form-to-const op))
		      '("=" "PosLt" "PosLe" "NatLt" "NatLe" "IntLt" "IntLe"
			"RatEqv" "RatLt" "RatLe"))
	      (= 2 (length (term-in-app-form-to-args kernel))))))
      (and (predicate-form? atom-or-pred)
	   (let ((pred (predicate-form-to-predicate atom-or-pred)))
	     (and (idpredconst-form? pred)
		  (or (member (idpredconst-to-name pred)
			      '("RealEq" "RealLe"))
		      (and (string=? (idpredconst-to-name pred) "EqD")
			   (apply and-op
				  (map synt-total? (predicate-form-to-args
						    atom-or-pred))))))))))

(define (positive-exponential-string? string)
  (let* ((term (pt string))
	 (op (term-in-app-form-to-final-op term))
	 (args (term-in-app-form-to-args term)))
    (and (term-in-const-form? op)
	 (member (const-to-name (term-in-const-form-to-const op))
		 '("PosExp" "NatExp" "IntExp" "RatExp" "RealExp"))
	 (= 2 (length args))
	 (is-gen-numeric-term? (car args))
	 (positive? (gen-numeric-term-to-number (car args))))))

(define (simp-comparison atom-or-pred)
  (if
   (is-comparison? atom-or-pred)
   (let* ((name (if (atom-form? atom-or-pred)
		    (const-to-name (term-in-const-form-to-const
				    (term-in-app-form-to-final-op
				     (atom-form-to-kernel atom-or-pred))))
		    (idpredconst-to-name
		     (predicate-form-to-predicate atom-or-pred))))
	  (op-is-=? (member name '("=" "RatEqv" "RealEq" "EqD")))
	  (op-is-<=? (member name '("PosLe" "NatLe" "IntLe" "RatLe" "RealLe")))
	  (op-is-<? (member name '("PosLt" "NatLt" "IntLt" "RatLt")))
	  (args (if (atom-form? atom-or-pred)
		    (term-in-app-form-to-args
		     (atom-form-to-kernel atom-or-pred))
		    (predicate-form-to-args atom-or-pred)))
	  (arg1 (if (= 2 (length args))
		    (car args)
		    (myerror "simp-comparison" "2 args expected"
			     (map term-to-string args))))
	  (arg2 (cadr args))
	  (type (term-to-type arg1))
	  (minus-const
	   (cond
	    ((equal? (py "pos") type) (pconst-name-to-pconst "PosMinus"))
	    ((equal? (py "nat") type) (pconst-name-to-pconst "NatMinus"))
	    ((equal? (py "int") type) (pconst-name-to-pconst "IntMinus"))
	    ((equal? (py "rat") type) (pconst-name-to-pconst "RatMinus"))
	    ((equal? (py "rea") type) (pconst-name-to-pconst "RealMinus"))
	    (else (myerror "simp-comparison"
			   "unexpected type" type))))
	  (x (term-to-num-and-sps1-and-nsps-list1-and-sps2-and-nsps-list2
	      (mk-term-in-app-form
	       (make-term-in-const-form minus-const) arg2 arg1)))
	  (num (car x))
	  (sps1 (cadr x))
	  (nsps-list1 (caddr x))
	  (sps2 (cadddr x))
	  (nsps-list2 (car (cddddr x)))
	  (sps (stringpowers-to-joined-stringpowers
		(insertsort stringpower<? (append sps1 sps2))))
	  (non-zero-strings (union (term-to-non-zero-strings arg1)
				   (term-to-non-zero-strings arg2)))
	  (reduced-sps ;if = delete pos-exp-strings and non-zero-strings,
					;and reduce exps to 1.  Else delete
					;non-zero-strings with even exps and
					;pos-exp-strings, and red exps mod 2
	   (if 
	    op-is-=? 
	    (map (lambda (sp) (list (car sp) 1))
		 (list-transform-positive sps
		   (lambda (sp)
		     (and (not (member (car sp) non-zero-strings))
			  (not (positive-exponential-string? (car sp)))))))
	    (map (lambda (sp) (list (car sp)
				    (if (= 1 (modulo (cadr sp) 2)) 1 2)))
		 (list-transform-positive sps
		   (lambda (sp)
		     (and (not (and (member (car sp) non-zero-strings)
				    (even? (cadr sp))))
			  (not (positive-exponential-string? (car sp)))))))))
	  (pos1? (positive-num-stringpowers-list? nsps-list1 type))
	  (neg1? (negative-num-stringpowers-list? nsps-list1 type))
	  (pos2? (positive-num-stringpowers-list? nsps-list2 type))
	  (neg2? (negative-num-stringpowers-list? nsps-list2 type))
	  (all-neg1?
	   (apply and-op (map (lambda (nsps) (negative? (car nsps)))
			      nsps-list1)))
	  (all-neg2?
	   (apply and-op (map (lambda (nsps) (negative? (car nsps)))
			      nsps-list2)))
	  (negated-nsps-list1 (map (lambda (nsps)
				     (cons (- (car nsps)) (cdr nsps)))
				   nsps-list1))
	  (negated-nsps-list2 (map (lambda (nsps)
				     (cons (- (car nsps)) (cdr nsps)))
				   nsps-list2))
	  (sign-and-not-all-neg-nsps-lists ;cancel non-zero nsps-lists
	   (cond
	    ((or (and pos1? pos2?) (and neg1? neg2?)) (list #t '()))
	    ((or (and pos1? neg2?) (and neg1? pos2?)) (list #f '()))
	    (pos1? (if all-neg2?
		       (list #f (list negated-nsps-list2))
		       (list #t (list nsps-list2))))
	    (neg1? (if all-neg2?
		       (list #t (list negated-nsps-list2))
		       (list #f (list nsps-list2))))
	    (pos2? (if all-neg1?
		       (list #f (list negated-nsps-list1))
		       (list #t (list nsps-list1))))
	    (neg2? (if all-neg1?
		       (list #t (list negated-nsps-list1))
		       (list #f (list nsps-list1))))
	    ((and all-neg1? all-neg2?)
	     (list #t (list negated-nsps-list1 negated-nsps-list2)))
	    ((and all-neg1? (not all-neg2?))
	     (list #f (list negated-nsps-list1 nsps-list2)))
	    ((and (not all-neg1?) all-neg2?)
	     (list #f (list nsps-list1 negated-nsps-list2)))
	    ((and (not all-neg1?) (not all-neg2?))
	     (list #t (list nsps-list1 nsps-list2)))
	    (else (myerror "simp-comparison" "this should not happen"))))
	  (sign (car sign-and-not-all-neg-nsps-lists))
	  (not-all-neg-nsps-lists (cadr sign-and-not-all-neg-nsps-lists)))
     (cond
      ((null? nsps-list1)
       (if (or op-is-=? op-is-<=?) truth falsity))
      ((and (null? reduced-sps) (null? not-all-neg-nsps-lists))
       (if op-is-=? falsity (if sign truth falsity)))
      ((and (null? reduced-sps) (= 1 (length not-all-neg-nsps-lists)))
	 (let* ((nsps-list (car not-all-neg-nsps-lists))
		(pos-nsps-list (list-transform-positive nsps-list
				 (lambda (nsps) (positive? (car nsps)))))
		(neg-nsps-list (list-transform-positive nsps-list
				 (lambda (nsps) (negative? (car nsps)))))
		(abs-neg-nsps-list
		 (map (lambda (nsps) (cons (- (car nsps)) (cdr nsps)))
		      neg-nsps-list))
		(pos-nsps-list-term
		 (nsps-list-and-type-to-term pos-nsps-list type))
		(abs-neg-nsps-list-term
		 (nsps-list-and-type-to-term abs-neg-nsps-list type))
		(term1 (if sign
			   abs-neg-nsps-list-term
			   pos-nsps-list-term))
		(term2 (if sign
			   pos-nsps-list-term
			   abs-neg-nsps-list-term)))
	   (if (atom-form? atom-or-pred)
	       (make-atomic-formula
		(mk-term-in-app-form (term-in-app-form-to-final-op
				      (atom-form-to-kernel atom-or-pred))
				     term1 term2))
	       (make-predicate-formula
		(predicate-form-to-predicate atom-or-pred) term1 term2))))
      ((and (apply and-op (map (lambda (sp) (even? (cadr sp))) reduced-sps))
	    (null? not-all-neg-nsps-lists)
	    sign op-is-<=?)
       truth)
      ((and (apply and-op (map (lambda (sp) (even? (cadr sp))) reduced-sps))
	    (null? not-all-neg-nsps-lists)
	    (not sign) op-is-<?)
       falsity)
      (else
       (let* ((sps-terms (map (lambda (x)
				(stringpower-and-type-to-term x type))
			      reduced-sps))
	      (nsps-terms (map (lambda (nspsl)
				 (nsps-list-and-type-to-term nspsl type))
			       not-all-neg-nsps-lists))
	      (final-term (apply mk-* (append sps-terms nsps-terms)))
	      (term1 (if sign
			 (num-and-type-to-gen-numeric-term 0 type)
			 final-term))
	      (term2 (if sign
			 final-term
			 (num-and-type-to-gen-numeric-term 0 type))))
	 (if (atom-form? atom-or-pred)
	     (make-atomic-formula
	      (mk-term-in-app-form (term-in-app-form-to-final-op
				    (atom-form-to-kernel atom-or-pred))
				   term1 term2))
	     (make-predicate-formula
	      (predicate-form-to-predicate atom-or-pred) term1 term2))))))
   atom-or-pred))

;; Tests
;; (pp (simp-comparison (pf "a+b==b+a")))
;; (pp (simp-comparison (pf "0<(1+a*a)")))
;; (pp (simp-comparison (pf "0<((IntN 1#One)-a*a)")))

;; (pp (simp-comparison (pf "0==(1-a*a)")))
;; (pp (simp-comparison (pf "0<((IntN 1#One)+a*a)")))

;; (pp (simp-comparison (pf "0<=b*b*(1+a*a)")))

;; (pp (simp-comparison (pf "0<b*b*((IntN 1#One)-a*a)")))

;; (pp (simp-comparison (pf "0<b*b*a*a")))
;; (pp (simp-comparison (pf "0<=(IntN 1#One)*b*b*a*a")))

;; (pp (simp-comparison (pf "j+i+1=i+j")))
;; (pp (simp-comparison (pf "m+n+2=n+m")))
;; (pp (simp-comparison (pf "a*a==(IntN 1#One)")))
;; (pp (simp-comparison (pf "0==(1+a*a)/((IntN 1#One)-a*a)")))

;; (pp (simp-comparison (pf "0<1/(a*a)")))
;; (pp (simp-comparison (pf "0<1/a")))
;; (pp (simp-comparison (pf "0<1/(a*a*(1+b*b+c))")))
;; (pp (simp-comparison (pf "l<=S(l+l+k)")))

;; (pp (simp-comparison (pf "0<2**k")))

;; (pp (simp-comparison (pf "x===x+1")))
;; (pp (simp-comparison (pf "x<<=x+1")))
;; (pp (simp-comparison (pf "0<<=y*y*(1+x*x)")))
;; (pp (simp-comparison (pf "RealLe x(x+1)")))

;; (pp (simp-comparison (pf "c<<=c+1/3*(d-c)")))

;; Test for 1/2**(k+2)+1/2**(k+1)+1/2**(k+2)<=1/2**k
;; (pp (simp-comparison (pf "1/2**(k+1)<=1/2**k")))
;; (pp (simp-comparison (pf "One<=2**1")))
;; (pp (simp-comparison (pf "0<=2**1"))) ;ok
;; (pp (simp-comparison (pf "1<=2**2"))) ;One<=2**2 ??

;; Now: Integration of simp-comparison into interactive proving.

;; Given an atomic goal in the form of a comparison (more precisely, an
;; equality or a le- or lt-inequality in one of the types pos, int,
;; rat or real e.g., a<b), (ord-field-simp-bwd) (1) simplifies the atom
;; to simp-atom, using the field axioms, (2) generates a new global
;; assumption ex k RealLt 0(abs x)k -> ... 0<abs r -> ...-> simp-atom
;; -> atom (with additional hypotheses ex k RealLt 0(abs s)k or 0<abs
;; s for every term s corresponding to one of the non-zero-strings),
;; and (3) uses this new global assumption to create the new goal
;; simp-atom.

;; Given a goal with an atomic hypothesis in the form of a comparison,
;; (ord-field-simp-fwd) (1) simplifies the hypothesis to simp-atom,
;; using the field axioms, (2) generates a new global assumption ex k
;; RealLt 0(abs x)k -> ... 0<abs r -> ... -> atom -> simp-atom, and
;; (3) uses this new global assumption to create the new goal with the
;; simplified hypothesis.

(define (comparison-to-non-zero-strings atom-or-pred)
  (if (is-comparison? atom-or-pred)
      (let* ((args (if (atom-form? atom-or-pred)
		       (term-in-app-form-to-args
			(atom-form-to-kernel atom-or-pred))
		       (predicate-form-to-args atom-or-pred)))
	     (arg1 (car args))
	     (arg2 (cadr args)))
	(union (term-to-non-zero-strings arg1)
	       (term-to-non-zero-strings arg2)))
      '()))
	  
(define (ord-field-simp-bwd)
  (let* ((num-goals (pproof-state-to-num-goals))
	 (num-goal (if (null? num-goals)
		       (myerror "cut: num-goals empty")
		       (car num-goals)))
	 (goal (num-goal-to-goal num-goal))
	 (formula (goal-to-formula goal))
	 (simp-fla (if (is-comparison? formula)
		       (simp-comparison formula)
		       (myerror "ord-field-simp-bwd" "comparison expected"
				(pp formula)))))
    (if (formula=? formula simp-fla)
	(myerror "ord-field-simp-bwd" "formula cannot be simplified"
		 formula))
    (let* ((name (new-global-assumption-name "Simp-GA"))
	   (non-zero-strings (comparison-to-non-zero-strings formula))
	   (args (if (atom-form? formula)
		     (term-in-app-form-to-args
		      (atom-form-to-kernel formula))
		     (predicate-form-to-args formula)))
	   (type (term-to-type (car args)))
	   (string (cond ((equal? (py "pos") type) "Pos")
			 ((equal? (py "pos") type) "Nat")
			 ((equal? (py "int") type) "Int")
			 ((equal? (py "rat") type) "Rat")
			 ((equal? (py "rea") type) "Real")))
	   (abs-name (string-append string "Abs"))
	   (lt-name (string-append string "Lt"))
	   (non-zero-hyps ;list of hyps ex k RealLt 0(abs s)k or 0<abs s
	    (map (lambda (s)
		   (let ((abs-s (make-term-in-app-form
				 (make-term-in-const-form
				  (pconst-name-to-pconst abs-name))
				 (pt s))))
		     (if (string=? "Real" string)
			 (let ((var (type-to-new-var (py "int"))))
			   (make-ex
			    var (make-atomic-formula
				 (mk-term-in-app-form
				  (make-term-in-const-form
				   (pconst-name-to-pconst lt-name))
				  (num-and-type-to-gen-numeric-term 0 type)
				  abs-s (make-term-in-var-form var)))))
			 (make-atomic-formula
			  (mk-term-in-app-form
			   (make-term-in-const-form
			    (pconst-name-to-pconst lt-name))
			   (num-and-type-to-gen-numeric-term 0 type)
			   abs-s)))))
		 non-zero-strings))
	   (real-vars (list-transform-positive (formula-to-free formula)
			(lambda (v) (equal? (py "rea") (var-to-type v)))))
	   (real-hyps ;list of hypotheses Real x
	    (map (lambda (v)
		   (make-predicate-formula
		    (make-idpredconst "Real" '() '())
		    (make-term-in-var-form v)))
		 real-vars)))
      (if (formula=? truth simp-fla)
	  (let* ((imp-formula
		  (apply mk-imp (append real-hyps non-zero-hyps
					(list formula))))
		 (vars (formula-to-free imp-formula))
		 (varterms (map make-term-in-var-form vars)))
	    (add-global-assumption
	     name (apply mk-all (append vars (list imp-formula))))
	    (apply
	     use-with
	     (append (list name)
		     varterms
		     (apply
		      list (map (lambda (x) DEFAULT-GOAL-NAME)
				(append real-hyps non-zero-hyps))))))
	  (let* ((imp-formula
		  (apply mk-imp (append real-hyps non-zero-hyps
					(list simp-fla formula))))
		 (vars (formula-to-free imp-formula))
		 (varterms (map make-term-in-var-form vars)))
	    (add-global-assumption
	     name (apply mk-all (append vars (list imp-formula))))
	    (apply
	     use-with
	     (append (list name)
		     varterms
		     (apply
		      list (map (lambda (x) DEFAULT-GOAL-NAME)
				(append real-hyps non-zero-hyps)))
		     (list DEFAULT-GOAL-NAME))))))))

;; (set-goal "all a,b a+b==b+a")
;; (strip)
;; (ord-field-simp-bwd)

;; (set-goal "all a,b(0<abs a -> 0<abs b ->
;;                    0<=a*b*((IntN 1#One)*a+b) ->
;;                    1/b<=1/a")
;; (strip)
;; (ord-field-simp-bwd)
;; (auto)

;; (display-global-assumptions "Simp-GA1")

;; ord-field-simp-fwd does for forward chaining the same as
;; ord-field-simp-bwd for backward chaining.  It replaces the present
;; goal by a new one, with one additional hypothesis obtained by
;; instantiating a previous one.  In the following definition of
;; ord-field-simp-fwd x is a number or string identifying a hypothesis
;; form the context.

(define (ord-field-simp-fwd x)
  (let* ((num-goals (pproof-state-to-num-goals))
         (num-goal (if (null? num-goals)
		       (myerror "cut: num-goals empty")
		       (car num-goals)))
	 (goal (num-goal-to-goal num-goal))
	 (hypname-info (num-goal-to-hypname-info num-goal))
	 (context (goal-to-context goal))
	 (avars (context-to-avars context))
	 (maxhyp (length avars))
	 (formula (goal-to-formula goal))
	 (x-formula
	  (cond
	   ((and (integer? x) (positive? x))
	    (if (<= x maxhyp)
		(avar-to-formula (list-ref avars (- x 1)))
		(myerror "ord-field-simp-fwd" "assumption number expected" x)))
	   ((and (string? x)
		 (member x (hypname-info-to-names hypname-info)))
	    (let ((i (name-and-hypname-info-to-index x hypname-info)))
	      (if (<= i maxhyp)
		  (avar-to-formula (list-ref avars (- i 1)))
		  (myerror
		   "ord-field-simp-fwd" "assumption number expected" i))))
	   (else (myerror "ord-field-simp-fwd" "illegal first argument" x))))
	 (simp-fla (if (is-comparison? x-formula)
		       (simp-comparison x-formula)
		       (myerror "ord-field-simp-fwd" "comparison expected"
				(formula-to-string x-formula)))))
    (if (formula=? x-formula simp-fla)
	(myerror "ord-field-simp-fwd" "formula cannot be simplified"
		 (formula-to-string x-formula)))
    (let* ((name (new-global-assumption-name "Simp-GA"))
	   (non-zero-strings (comparison-to-non-zero-strings x-formula))
	   (args (if (atom-form? x-formula)
		     (term-in-app-form-to-args
		      (atom-form-to-kernel x-formula))
		     (predicate-form-to-args x-formula)))
	   (type (term-to-type (car args)))
	   (string (cond ((equal? (py "pos") type) "Pos")
			 ((equal? (py "int") type) "Int")
			 ((equal? (py "rat") type) "Rat")
			 ((equal? (py "rea") type) "Real")))
	   (abs-name (string-append string "Abs"))
	   (lt-name (string-append string "Lt"))
	   (non-zero-hyps ;list of hyps ex k RealLt 0(abs s)k or 0<abs s
	    (map (lambda (s)
		   (let ((abs-s (make-term-in-app-form
				 (make-term-in-const-form
				  (pconst-name-to-pconst abs-name))
				 (pt s))))
		     (if (string=? "Real" string)
			 (let ((var (type-to-new-var (py "pos"))))
			   (make-ex
			    var (make-atomic-formula
				 (mk-term-in-app-form
				  (make-term-in-const-form
				   (pconst-name-to-pconst lt-name))
				  (num-and-type-to-gen-numeric-term 0 type)
				  abs-s (make-term-in-var-form var)))))
			 (make-atomic-formula
			  (mk-term-in-app-form
			   (make-term-in-const-form
			    (pconst-name-to-pconst lt-name))
			   (num-and-type-to-gen-numeric-term 0 type)
			   abs-s)))))
		 non-zero-strings))
	   (real-vars (list-transform-positive (formula-to-free x-formula)
			(lambda (v) (equal? (py "rea") (var-to-type v)))))
	   (real-hyps ;list of hypotheses Real x
	    (map (lambda (v)
		   (make-predicate-formula
		    (make-idpredconst "Real" '() '())
		    (make-term-in-var-form v)))
		 real-vars))
	   (imp-formula (apply mk-imp (append real-hyps non-zero-hyps
					      (list x-formula simp-fla))))
	   (vars (formula-to-free imp-formula))
	   (varterms (map make-term-in-var-form vars)))
      (add-global-assumption
       name (apply mk-all (append vars (list imp-formula))))
      (apply inst-with
	     (append (list name)
		     varterms
		     (apply
		      list (map (lambda (x)
				  DEFAULT-GOAL-NAME)
				(append real-hyps non-zero-strings)))
		     (list x))))))
