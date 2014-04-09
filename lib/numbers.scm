;; $Id: numbers.scm 2679 2014-01-08 10:05:44Z schwicht $

'(
(load "~/minlog/init.scm")
(set! COMMENT-FLAG #f)
(libload "nat.scm")
(set! COMMENT-FLAG #t)
)
(if (not (assoc "nat" ALGEBRAS))
    (begin
      (libload "nat.scm")
      (if (not (assoc "nat" ALGEBRAS))
	  (myerror "First execute (libload \"nat.scm\")"))))

(remove-var-name "k")

(display "loading numbers.scm ...") (newline)

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

;; (remove-nat-tokens) removes all tokens added in nat.scm and from
;; DISPLAY-FUNCTIONS all items (nat proc).  The reason is that they
;; will be reintroduced here, with a different assigned procedure.

(remove-nat-tokens)

;; The functions make-numeric-term (used by the parser) and
;; is-numeric-term?, numeric-term-to-number (used by term-to-expr and
;; token-tree-to-string) take pos as default.

(set! NAT-NUMBERS #f)

(define TOKEN-AND-TYPES-TO-NAME-ALIST '())

(define (token-and-types-to-name token types)
  (let ((info (assoc token TOKEN-AND-TYPES-TO-NAME-ALIST)))
    (if info
        (let ((info1 (assoc types (cadr info))))
          (if info1
	      (cadr info1)
	      (apply myerror
		     (append (list "token-and-types-to-name" "token"
				   token "not defined for types")
			     types))))
	(myerror "token-and-types-to-name" "not an overloaded token" token))))

(define (token-and-type-to-name token type)
  (token-and-types-to-name token (list type)))

(define (add-token-and-types-to-name token types name)
  (let ((info (assoc token TOKEN-AND-TYPES-TO-NAME-ALIST)))
    (if info
	(set! TOKEN-AND-TYPES-TO-NAME-ALIST
	      (map (lambda (item)
		     (if (equal? (car item) token)
			 (list token (cons (list types name) (cadr item)))
			 item))
		   TOKEN-AND-TYPES-TO-NAME-ALIST))
	(set! TOKEN-AND-TYPES-TO-NAME-ALIST
	      (cons (list token (list (list types name)))
		    TOKEN-AND-TYPES-TO-NAME-ALIST)))))

(define (add-token-and-type-to-name token type name)
  (add-token-and-types-to-name token (list type) name))


;; 1. Positive, natural, integer, rational, real and complex numbers
;; =================================================================

;; We want to overload operators like +,*,/, <=,<, and automatically
;; raise the type of arguments when reading.  For instance, + should
;; take its arguments, compute the lub rho of their types, raise the
;; type of both arguments to type rho, apply RhoPlus to the results.

;; A special situation occurs with exponentiation **: 2**3 is pos, and
;; 2** -3 is rat.  We need both types to determine the value type.

;; Moreover, a number should be displayed at the lowest possible level.

(add-alg "pos" '("One" "pos") '("SZero" "pos=>pos") '("SOne" "pos=>pos"))
(add-totality "pos")
(add-mr-ids "TotalPos")

;; PosTotalVar
(set-goal "all pos TotalPos pos")
(ind)
(use "TotalPosOne")
(assume "pos" "Tpos")
(use "TotalPosSZero")
(use "Tpos")
(assume "pos" "Tpos")
(use "TotalPosSOne")
(use "Tpos")
;; Proof finished.
(save "PosTotalVar")

;; PosEqToEqD
(set-goal "all pos1,pos2(pos1=pos2 -> pos1 eqd pos2)")
(ind) ;2-4
(cases) ;5-7
(assume "Useless")
(use "InitEqD")
;; 6
(assume "pos1" "1=SZero p1")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "1=SZero p1")
;; 7
(assume "pos1" "1=SOne p1")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "1=SOne p1")
;; 3
(assume "pos1" "IH1")
(cases) ;16-18
(assume "SZero p1=1")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "SZero p1=1")
;; 17
(assume "pos2" "SZero p1=SZero p2")
(assert "pos1 eqd pos2")
 (use "IH1")
 (use "SZero p1=SZero p2")
(assume "pos1 eqd pos2")
(elim "pos1 eqd pos2")
(assume "pos^1")
(use "InitEqD")
;; 18
(assume "pos2" "SZero p1=SOne p2")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "SZero p1=SOne p2")
;; 4
(assume "pos1" "IH1")
(cases) ;33-35
(assume "SOne p1=1")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "SOne p1=1")
;; 34
(assume "pos2" "SOne p1=SZero p2")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "SOne p1=SZero p2")
;; 35
(assume "pos2" "SOne p1=SOne p2")
(assert "pos1 eqd pos2")
 (use "IH1")
 (use "SOne p1=SOne p2")
(assume "pos1 eqd pos2")
(elim "pos1 eqd pos2")
(assume "pos^1")
(use "InitEqD")
;; Proof finished.
(save "PosEqToEqD")

;; PosIfTotal
(set-goal "allnc pos^(TotalPos pos^ ->
 allnc alpha^,(pos=>alpha)^1,(pos=>alpha)^2(
 Total alpha^ ->
 allnc pos^1(TotalPos pos^1 -> Total((pos=>alpha)^1 pos^1)) ->
 allnc pos^1(TotalPos pos^1 -> Total((pos=>alpha)^2 pos^1)) ->
 Total[if pos^ alpha^ (pos=>alpha)^1 (pos=>alpha)^2]))")
(assume "pos^" "Tpos" "alpha^" "(pos=>alpha)^1" "(pos=>alpha)^2"
	"Talpha" "Tf1" "Tf2")
(elim "Tpos")
(use "Talpha")
(assume "pos^1" "Tpos1" "Useless")
(ng #t)
(use "Tf1")
(use "Tpos1")
(assume "pos^1" "Tpos1" "Useless")
(ng #t)
(use "Tf2")
(use "Tpos1")
;; Proof finished.
(save "PosIfTotal")

;; PosRecTotal
(set-goal (rename-variables (term-to-totality-formula (pt "(Rec pos=>alpha)"))))
(assume "pos^" "Tp")
(elim "Tp") ;3-5
(ng #t)
(assume "alpha^" "Talpha")
(strip)
(use "Talpha")
;; 4
(assume "pos^1" "Tp1" "IH" "alpha^" "Talpha"
	"(pos=>alpha=>alpha)^1" "Tf1" "(pos=>alpha=>alpha)^2" "Tf2")
(ng #t)
(use "Tf1")
(use "Tp1")
(use "IH")
(use "Talpha")
(use "Tf1")
(use "Tf2")
;; 5
(assume "pos^1" "Tp1" "IH" "alpha^" "Talpha"
	"(pos=>alpha=>alpha)^1" "Tf1" "(pos=>alpha=>alpha)^2" "Tf2")
(ng #t)
(use "Tf2")
(use "Tp1")
(use "IH")
(use "Talpha")
(use "Tf1")
(use "Tf2")
;; Proof finished.
(save "PosRecTotal")

;; An integer is either positive or zero or negative.

(add-alg
 "int" '("IntPos" "pos=>int") '("IntZero" "int") '("IntNeg" "pos=>int"))
(add-totality "int")
(add-mr-ids "TotalInt")

;; IntTotalVar
(set-goal "all int TotalInt int")
(cases)
(assume "pos")
(use "TotalIntIntPos")
(use "PosTotalVar")
(use "TotalIntIntZero")
(assume "pos")
(use "TotalIntIntNeg")
(use "PosTotalVar")
;; Proof finished.
(save "IntTotalVar")

;; IntEqToEqD
(set-goal "all int1,int2(int1=int2 -> int1 eqd int2)")
(cases) ;2-4
(assume "pos1")
(cases) ;6-8
(assume "pos2")
(ng #t)
(assume "p1=p2")
(assert "pos1=pos2")
 (use "p1=p2")
(assume "pos1=pos2")
(simp "pos1=pos2")
(use "InitEqD")
;; 7
(ng #t)
(use "Efq")
;; 8
(assume "pos2")
(ng #t)
(use "Efq")
;; 3
(cases) ;20-22
(assume "pos2")
(ng #t)
(use "Efq")
;; 21
(assume "Useless")
(use "InitEqD")
;; 22
(assume "pos2")
(ng #t)
(use "Efq")
;; 4
(assume "pos1")
(cases) ;29-31
(assume "pos2")
(ng #t)
(use "Efq")
;; 30
(ng #t)
(use "Efq")
;; 31
(assume "pos2")
(ng #t)
(assume "p1=p2")
(assert "pos1=pos2")
 (use "p1=p2")
(assume "pos1=pos2")
(simp "pos1=pos2")
(use "InitEqD")
;; Proof finished.
(save "IntEqToEqD")

;; IntIfTotal
(set-goal "allnc int^(TotalInt int^ ->
 allnc alpha^,(pos=>alpha)^1,(pos=>alpha)^2(
 Total alpha^ ->
 allnc pos^1(TotalPos pos^1 -> Total((pos=>alpha)^1 pos^1)) ->
 allnc pos^1(TotalPos pos^1 -> Total((pos=>alpha)^2 pos^1)) ->
 Total[if int^ (pos=>alpha)^1 alpha^ (pos=>alpha)^2]))")
(assume "int^" "Tint" "alpha^" "(pos=>alpha)^1" "(pos=>alpha)^2"
	"Talpha" "Tf1" "Tf2")
(elim "Tint")
(assume "pos^1" "Tpos1")
(ng #t)
(use "Tf1")
(use "Tpos1")
(use "Talpha")
(assume "pos^1" "Tpos1")
(ng #t)
(use "Tf2")
(use "Tpos1")
;; Proof finished.
(save "IntIfTotal")

;; make-numeric-term-wrt-pos produces an int object for n <= 0, and a pos
;; object for a positive integer.

(define (make-numeric-term-wrt-pos n)
  (cond ((zero? n) (make-term-in-const-form (constr-name-to-constr "IntZero")))
	((= n 1) (pt "One"))
	((< n 0)  (make-term-in-app-form
		    (make-term-in-const-form (constr-name-to-constr "IntNeg"))
		    (make-numeric-term-wrt-pos (- n))))
	((even? n) (make-term-in-app-form
		    (make-term-in-const-form (constr-name-to-constr "SZero"))
		    (make-numeric-term-wrt-pos (/ n 2))))
	((odd? n) (make-term-in-app-form
		   (make-term-in-const-form (constr-name-to-constr "SOne"))
		   (make-numeric-term-wrt-pos (/ (- n 1) 2))))
	(else
	 (myerror "make-numeric-term-wrt-pos" "integer expected" n))))

(define make-numeric-term
  (if NAT-NUMBERS
      make-numeric-term-wrt-nat
      make-numeric-term-wrt-pos))

(define is-numeric-term?
  (if NAT-NUMBERS
      is-numeric-term-wrt-nat?
      is-numeric-term-wrt-pos?))

(define numeric-term-to-number
  (if NAT-NUMBERS
      numeric-term-wrt-nat-to-number
      numeric-term-wrt-pos-to-number))

;; We postpone introduction of + etc, and first introduce the types rat
;; of rationals, rea of reals and cpx of complex numbers.  A rational
;; is a pair of an integer and a positive number.

;; Comparison with the treatment of constructive analysis in Nijmegen
;; C-CoRN.  They want to be as general as possible, and for instance
;; derive properties of the rationals by instantiation of general field
;; facts.  However, when one wants to use proofs for program extraction
;; and development, it seems better to have a more direct approach,
;; which allows to take care of the underlying data structures.

(add-var-name "p" "q" (py "pos"))
(add-var-name  "k" "l" "i" "j" (py "int"))

(add-token
 "IntN"
 'prefix-op
 (lambda (x) (mk-term-in-app-form (pt "IntNeg") x)))

(add-token
 "IntP"
 'prefix-op
 (lambda (x) (mk-term-in-app-form (pt "IntPos") x)))

(add-display
 (py "int")
 (lambda (x)
   (let ((op (term-in-app-form-to-final-op x))
	 (args (term-in-app-form-to-args x)))
     (if (and (term-in-const-form? op)
	      (= 1 (length args)))
	 (let ((name (const-to-name (term-in-const-form-to-const op))))
	   (cond
	    ((string=? name "IntNeg")
	     (list 'prefix-op "IntN" (term-to-token-tree (car args))))
	    ((string=? name "IntPos")
	     (term-to-token-tree (car args)))
;; added 2007-09-05
	    ((string=? name "NatToInt")
	     (term-to-token-tree (car args)))
	    (else #f)))
	 #f))))

;; 2004-09-03.  To use external code in a pconst, we provide tests for
;; numeral values and conversion operations from numerals values to
;; numbers, for pos, nat and int

(define (pos-numeral-value? value)
  (and (nbe-constr-value? value)
       (let* ((name (nbe-constr-value-to-name value))
	      (args (nbe-constr-value-to-args value))
	      (vals (map nbe-object-to-value args)))
	 (or (string=? "One" name)
	     (and (or (string=? "SZero" name) (string=? "SOne" name))
		  (pair? vals)
		  (pos-numeral-value? (car vals)))))))

(define (pos-numeral-value-to-number value)
  (let* ((name (nbe-constr-value-to-name value))
	 (args (nbe-constr-value-to-args value))
	 (vals (map nbe-object-to-value args)))
    (if (string=? "One" name)
	1
	(let ((prev (pos-numeral-value-to-number (car vals))))
	  (if (string=? "SZero" name) (* 2 prev) (+ (* 2 prev) 1))))))

(define (nat-numeral-value? value)
  (and (nbe-constr-value? value)
       (let* ((name (nbe-constr-value-to-name value))
	      (args (nbe-constr-value-to-args value))
	      (vals (map nbe-object-to-value args)))
	 (or (string=? "Zero" name)
	     (and (string=? "Succ" name)
		  (pair? vals)
		  (nat-numeral-value? (car vals)))))))

(define (nat-numeral-value-to-number value)
  (let* ((name (nbe-constr-value-to-name value))
	 (args (nbe-constr-value-to-args value))
	 (vals (map nbe-object-to-value args)))
    (if (string=? "Zero" name)
	1
	(+ 1 (nat-numeral-value-to-number (car vals))))))

;; Instead of the converse use pt.

(define (int-numeral-value? value)
  (and (nbe-constr-value? value)
       (let* ((name (nbe-constr-value-to-name value))
	      (args (nbe-constr-value-to-args value))
	      (vals (map nbe-object-to-value args)))
	 (or (and (string=? "IntPos" name)
		  (pos-numeral-value? (car vals)))
	     (string=? "IntZero" name)
	     (and (string=? "IntNeg" name)
		  (pos-numeral-value? (car vals)))))))

(define (int-numeral-value-to-number value)
  (let* ((name (nbe-constr-value-to-name value))
	 (args (nbe-constr-value-to-args value))
	 (vals (map nbe-object-to-value args)))
    (cond
     ((string=? "IntNeg" name) (- (pos-numeral-value-to-number (car vals))))
     ((string=? "IntZero" name) 0)
     ((string=? "IntPos" name) (pos-numeral-value-to-number (car vals)))
     (else (myerror "int-numeral-value-to-number" "unexpected arg" value)))))

;; We also introduce the rationals.  A rational is a pair i#p of an
;; integer i and a positive natural number p, interpreted as i/p.

(add-alg "rat" '("RatConstr" "int=>pos=>rat"))
(add-totality "rat")
(add-mr-ids "TotalRat")

;; RatTotalVar
(set-goal "all rat TotalRat rat")
(cases)
(assume "int" "pos")
(use "TotalRatRatConstr")
(use "IntTotalVar")
(use "PosTotalVar")
;; Proof finished.
(save "RatTotalVar")

;; RatEqToEqD
(set-goal "all rat1,rat2(rat1=rat2 -> rat1 eqd rat2)")
(cases)
(assume "int1" "pos1")
(cases)
(assume "int2" "pos2")
(ng #t)
(assume "i1=i2 andb p1=p2")
(assert "int1=int2")
 (use "i1=i2 andb p1=p2")
(assume "int1=int2")
(simp "int1=int2")
(assert "pos1=pos2")
 (use "i1=i2 andb p1=p2")
(assume "pos1=pos2")
(simp "pos1=pos2")
(use "InitEqD")
;; Proof finished.
(save "RatEqToEqD")

;; RatIfTotal
(set-goal "allnc rat^(TotalRat rat^ ->
 allnc (int=>pos=>alpha)^(
  allnc int^,pos^(TotalInt int^ -> TotalPos pos^ ->
                  Total((int=>pos=>alpha)^ int^ pos^)) ->
  Total[if rat^ (int=>pos=>alpha)^]))")
(assume "rat^" "Trat" "(int=>pos=>alpha)^" "Tf")
(elim "Trat")
(assume "int^" "Tint" "pos^" "Tpos")
(ng #t)
(use "Tf")
(use "Tint")
(use "Tpos")
;; Proof finished.
(save "RatIfTotal")

(add-var-name "a" "b" "c" "d" (py "rat"))

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

;; We now introduce the reals.  A real is a pair of a Cauchy sequence
;; of rationals and a modulus.  We view real as a data type (i.e., no
;; properties), and within this data type inductively define the
;; predicate Real x, meaning that x is a (proper) real.

(add-alg "rea" (list "RealConstr" "(nat=>rat)=>(int=>nat)=>rea"))
(add-totality "rea")
(add-mr-ids "TotalRea")

(add-var-name "as" "bs" "cs" "ds" (py "nat=>rat"))
(add-var-name "M" "N" (py "int=>nat"))
(add-var-name "x" "y" (py "rea"))

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

(add-computation-rule (pt "(RealConstr as M)seq") (pt "as"))

;; RealSeqTotal
(set-goal (rename-variables (term-to-totality-formula (pt "RealSeq"))))
(assume "x^" "Tx" "n^" "Tn")
(elim "Tx")
(assume "as^" "Tas" "M^" "TM")
(ng #t)
(use "Tas")
(use "Tn")
;; Proof finished.
(save "RealSeqTotal")

(add-program-constant "RealMod" (py "rea=>int=>nat") t-deg-zero 'const 1)

(add-token
 "mod"
 'postfix-op
 (lambda (x)
   (mk-term-in-app-form
    (make-term-in-const-form (pconst-name-to-pconst "RealMod"))
    x)))

(add-display
 (py "int=>nat")
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

(add-computation-rule (pt "(RealConstr as M)mod") (pt "M"))

;; RealModTotal
(set-goal (rename-variables (term-to-totality-formula (pt "RealMod"))))
(assume "x^" "Tx" "k^" "Tk")
(elim "Tx")
(assume "as^" "Tas" "M^" "TM")
(ng #t)
(use "TM")
(use "Tk")
;; Proof finished.
(save "RealModTotal")

;; (pp (pt "x seq n"))
;; (pp (pt "x mod k"))

;; We also introduce the complex numbers.  A complex number is a pair
;; x##y of two reals, interpreted as x+iy

(add-alg "cpx" '("CpxConstr" "rea=>rea=>cpx"))
(add-totality "cpx")
(add-mr-ids "TotalCpx")

(add-var-name "z" (py "cpx"))

(add-token
 "##"
 'pair-op
 (lambda (x y)
   (mk-term-in-app-form
    (make-term-in-const-form (constr-name-to-constr "CpxConstr"))
    x y)))

(add-display
 (py "cpx")
 (lambda (x)
   (let ((op (term-in-app-form-to-final-op x))
	 (args (term-in-app-form-to-args x)))
     (if (and (term-in-const-form? op)
	      (string=? "CpxConstr"
			(const-to-name (term-in-const-form-to-const op)))
	      (= 2 (length args)))
	 (list 'pair-op "##"
	       (term-to-token-tree (car args))
	       (term-to-token-tree (cadr args)))
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

(add-program-constant "PosToNat" (py "pos=>nat") t-deg-zero)
(add-program-constant "NatToInt" (py "nat=>int") t-deg-zero)

(define (add-item-to-algebra-edge-to-embed-term-alist
         alg1-name alg2-name embed-term)
  (set! ALGEBRA-EDGE-TO-EMBED-TERM-ALIST
        (cons (list (list (make-alg alg1-name) (make-alg alg2-name))
		    embed-term)
              ALGEBRA-EDGE-TO-EMBED-TERM-ALIST)))

;; When later we have proved totality of PosToNat and NatToInt we need
;; to replace their item accordingly.

(define (replace-item-in-algebra-edge-to-embed-term-alist
         alg1-name alg2-name new-embed-term)
  (let* ((alg1 (make-alg alg1-name))
	 (alg2 (make-alg alg2-name))
	 (new-alist (map (lambda (item)
			   (if (equal? (car item) (list alg1 alg2))
			       (list (car item) new-embed-term)
			       item))
			 ALGEBRA-EDGE-TO-EMBED-TERM-ALIST)))
    (set! ALGEBRA-EDGE-TO-EMBED-TERM-ALIST new-alist)))

;; We want the path from "pos" to "int" going through "nat" to be in
;; the association list AFTER the edge from "pos" to "int" because in
;; this case the function "algebras-to-embedding" choose the edge and
;; not the path.

(add-item-to-algebra-edge-to-embed-term-alist
 "pos" "nat"
 (let ((var (make-var (make-alg "pos") -1 t-deg-one "")))
   (make-term-in-abst-form
    var (make-term-in-app-form
         (make-term-in-const-form
          (pconst-name-to-pconst "PosToNat"))
         (make-term-in-var-form var)))))

(add-item-to-algebra-edge-to-embed-term-alist
 "nat" "int"
 (let ((var (make-var (make-alg "nat") -1 t-deg-one "")))
   (make-term-in-abst-form
    var (make-term-in-app-form
         (make-term-in-const-form
          (pconst-name-to-pconst "NatToInt"))
         (make-term-in-var-form var)))))

(add-item-to-algebra-edge-to-embed-term-alist
 "pos" "int"
 (let ((var (make-var (make-alg "pos") -1 t-deg-one "")))
   (make-term-in-abst-form
    var (make-term-in-app-form
         (make-term-in-const-form
          (constr-name-to-constr "IntPos"))
         (make-term-in-var-form var)))))

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

(add-item-to-algebra-edge-to-embed-term-alist
 "rat" "rea"
 (let ((var (make-var (make-alg "rat") -1 t-deg-one ""))
       (n (make-var (make-alg "nat") -1 t-deg-one ""))
       (k (make-var (make-alg "int") -1 t-deg-one "")))
   (make-term-in-abst-form
    var (mk-term-in-app-form
         (make-term-in-const-form
          (constr-name-to-constr "RealConstr"))
         (make-term-in-abst-form ;constant Cauchy sequence
          n (make-term-in-var-form var))
         (make-term-in-abst-form ;Zero modulus
          k (make-term-in-const-form
             (constr-name-to-constr "Zero")))))))

(add-item-to-algebra-edge-to-embed-term-alist
 "rea" "cpx"
 (let ((var (make-var (make-alg "rea") -1 t-deg-one ""))
       (n (make-var (make-alg "nat") -1 t-deg-one ""))
       (k (make-var (make-alg "int") -1 t-deg-one "")))
   (make-term-in-abst-form
    var (mk-term-in-app-form
         (make-term-in-const-form
          (constr-name-to-constr "CpxConstr"))
         (make-term-in-var-form var)
         (mk-term-in-app-form
          (make-term-in-const-form
           (constr-name-to-constr "RealConstr"))
          (make-term-in-abst-form ;Zero Cauchy sequence
           n (mk-term-in-app-form
              (make-term-in-const-form
               (constr-name-to-constr "RatConstr"))
              (make-term-in-const-form
               (constr-name-to-constr "IntZero"))
              (make-term-in-const-form
               (constr-name-to-constr "One"))))
          (make-term-in-abst-form ;Zero modulus
           k (make-term-in-const-form
              (constr-name-to-constr "Zero"))))))))

;; (alg-le? (make-alg "pos") (make-alg "int"))
;; (alg-le? (make-alg "pos") (make-alg "nat"))
;; (alg-le? (make-alg "nat") (make-alg "pos"))
;; (alg-le? (make-alg "nat") (make-alg "int"))
;; (alg-le? (make-alg "pos") (make-alg "rat"))
;; (alg-le? (make-alg "rat") (make-alg "pos"))
;; (alg-le? (make-alg "rat") (make-alg "rea"))
;; (alg-le? (make-alg "rea") (make-alg "cpx"))

(add-program-constant "PosS" (py "pos=>pos") t-deg-zero)

(add-program-constant "PosPred" (py "pos=>pos") t-deg-zero)
(add-program-constant "PosHalf" (py "pos=>pos") t-deg-zero)

;; Added 2007-02-12
(add-program-constant "IntS" (py "int=>int") t-deg-zero)
(add-program-constant "IntPred" (py "int=>int") t-deg-zero)

;; We define an overloaded addition.

(add-program-constant "PosPlus" (py "pos=>pos=>pos") t-deg-zero)
(add-program-constant "IntPlus" (py "int=>int=>int") t-deg-zero)
(add-program-constant "RatPlus" (py "rat=>rat=>rat") t-deg-zero)
(add-program-constant "RealPlus" (py "rea=>rea=>rea") t-deg-zero)
(add-program-constant "CpxPlus" (py "cpx=>cpx=>cpx") t-deg-zero)

;; We define a cut-off subtraction for pos (as we have it for nat).

(add-program-constant "PosMinus" (py "pos=>pos=>pos") t-deg-zero)

;; We define an overloaded subtraction for int, rat, rea and cpx.

(add-program-constant "IntMinus" (py "int=>int=>int") t-deg-zero)
(add-program-constant "RatMinus" (py "rat=>rat=>rat") t-deg-zero)
(add-program-constant "RealMinus" (py "rea=>rea=>rea") t-deg-zero)
(add-program-constant "CpxMinus" (py "cpx=>cpx=>cpx") t-deg-zero)

;; We define an overloaded multiplication.

(add-program-constant "PosTimes" (py "pos=>pos=>pos") t-deg-zero)
(add-program-constant "IntTimes" (py "int=>int=>int") t-deg-zero)
(add-program-constant "RatTimes" (py "rat=>rat=>rat") t-deg-zero)
(add-program-constant "RealTimes" (py "rea=>rea=>rea") t-deg-zero)
(add-program-constant "CpxTimes" (py "cpx=>cpx=>cpx") t-deg-zero)

;; We define an overloaded division for rat, rea and cpx.

(add-program-constant "RatDiv" (py "rat=>rat=>rat") t-deg-zero)
(add-program-constant "RealDiv" (py "rea=>rea=>rea") t-deg-zero)
(add-program-constant "CpxDiv" (py "cpx=>cpx=>cpx") t-deg-zero)

;; We define the absolute value for int, rat, rea and cpx.

(add-program-constant "IntAbs" (py "int=>nat") t-deg-zero)
(add-program-constant "RatAbs" (py "rat=>rat") t-deg-zero)
(add-program-constant "RealAbs" (py "rea=>rea") t-deg-zero)
(add-program-constant "CpxAbs" (py "cpx=>cpx") t-deg-zero)

;; We define the exponential with values in pos, nat, int, rat, rea and cpx.

(add-program-constant "PosExp" (py "pos=>nat=>pos") t-deg-zero)
(add-program-constant "NatExp" (py "nat=>nat=>nat") t-deg-zero)
(add-program-constant "IntExp" (py "int=>nat=>int") t-deg-zero)
(add-program-constant "RatExp" (py "rat=>int=>rat") t-deg-zero)
(add-program-constant "RealExp" (py "rea=>int=>rea") t-deg-zero)
(add-program-constant "CpxExp" (py "cpx=>int=>cpx") t-deg-zero)

;; We define the overloaded maximum function, written infix:

(add-program-constant "PosMax" (py "pos=>pos=>pos") t-deg-zero)
(add-program-constant "IntMax" (py "int=>int=>int") t-deg-zero)
(add-program-constant "RatMax" (py "rat=>rat=>rat") t-deg-zero)
(add-program-constant "RealMax" (py "rea=>rea=>rea") t-deg-zero)

;; We define the overloaded minimum function, written infix:

(add-program-constant "PosMin" (py "pos=>pos=>pos") t-deg-zero)
(add-program-constant "IntMin" (py "int=>int=>int") t-deg-zero)
(add-program-constant "RatMin" (py "rat=>rat=>rat") t-deg-zero)
(add-program-constant "RealMin" (py "rea=>rea=>rea") t-deg-zero)

;; We define the intended equivalence relations on rat.  It is
;; decidable and hence can be introduced by a program constant.  We
;; need an extra token == here, since the standard equality = for
;; finitary algebras is available for rat as well.  Equality for reals
;; is not decidable.  We view it as a defined predicate constant.  For
;; convenience we use the setup of inductively defined predicates,
;; although the "inductive" definition is in fact explicit, i.e., does
;; not contain recursive calls.

(add-program-constant "RatEqv" (py "rat=>rat=>boole") t-deg-zero)

;; We define an overloaded less-than relation.  It can be a program
;; constant for pos, int and rat.

(add-program-constant "PosLt" (py "pos=>pos=>boole") t-deg-zero)
(add-program-constant "IntLt" (py "int=>int=>boole") t-deg-zero)
(add-program-constant "RatLt" (py "rat=>rat=>boole") t-deg-zero)

;; We define an overloaded less-than-or-equal relation.

(add-program-constant "PosLe" (py "pos=>pos=>boole") t-deg-zero)
(add-program-constant "IntLe" (py "int=>int=>boole") t-deg-zero)
(add-program-constant "RatLe" (py "rat=>rat=>boole") t-deg-zero)

;; Program constants used for extraction of program constants to
;; Haskell, where computation rules
;
;;    f (SZero x) = ... x ...
;
;; must be transformed into
;;    f n | even n = ... TranslationPosHalfEven n ...
;
;; etc. Notice that we always know that n is an even number, so that
;; the remainder is zero, and similarly for minus and predecessor. Not
;; meant to be used directly by the user.
;; Maybe give them less understandable names?

(add-program-constant "TranslationPosHalfEven" (py "pos => pos"))
(add-program-constant "TranslationPosNegForInt" (py "pos => pos"))
(add-program-constant "TranslationPosAsInt" (py "int => pos"))
(add-program-constant "TranslationPosPredNonOne" (py "pos => pos"))
(add-program-constant "TranslationNumerator" (py "rat => int"))
(add-program-constant "TranslationDenominator" (py "rat => pos"))

;; We define the tokens that are used by the parser

(define (make-term-creator token min-type-string)
  (lambda (x y)
    (let* ((type1 (term-to-type x))
	   (type2 (term-to-type y))
	   (min-type (py min-type-string))
	   (type (types-lub type1 type2 min-type))
	   (internal-name (token-and-type-to-name token type)))
      (mk-term-in-app-form
       (make-term-in-const-form (pconst-name-to-pconst internal-name))
       x y))))

(define (make-term-creator1 token min-type-string)
  (lambda (x)
    (let* ((min-type (py min-type-string))
           (type (types-lub (term-to-type x) min-type))
	   (internal-name (token-and-type-to-name token type)))
      (mk-term-in-app-form
       (make-term-in-const-form (pconst-name-to-pconst internal-name))
       x))))

(define (make-term-creator-exp token)
  (lambda (x y)
    (let* ((type1 (term-to-type x))
           (type2 (term-to-type y))
	   (internal-name (token-and-types-to-name token (list type1 type2))))
      (mk-term-in-app-form
       (make-term-in-const-form (pconst-name-to-pconst internal-name))
       x y))))

(add-token "+" 'add-op (make-term-creator "+" "pos"))
(add-token-and-type-to-name "+" (py "pos") "PosPlus")
(add-token-and-type-to-name "+" (py "nat") "NatPlus")
(add-token-and-type-to-name "+" (py "int") "IntPlus")
(add-token-and-type-to-name "+" (py "rat") "RatPlus")
(add-token-and-type-to-name "+" (py "rea") "RealPlus")
(add-token-and-type-to-name "+" (py "cpx") "CpxPlus")

(add-token "--" 'add-op (make-term-creator "--" "pos"))
(add-token-and-type-to-name "--" (py "pos") "PosMinus")
(add-token-and-type-to-name "--" (py "nat") "NatMinus")

(add-token "-" 'add-op (make-term-creator "-" "int"))
(add-token-and-type-to-name "-" (py "int") "IntMinus")
(add-token-and-type-to-name "-" (py "rat") "RatMinus")
(add-token-and-type-to-name "-" (py "rea") "RealMinus")
(add-token-and-type-to-name "-" (py "cpx") "CpxMinus")

(add-token "*" 'mul-op (make-term-creator "*" "pos"))
(add-token-and-type-to-name "*" (py "pos") "PosTimes")
(add-token-and-type-to-name "*" (py "nat") "NatTimes")
(add-token-and-type-to-name "*" (py "int") "IntTimes")
(add-token-and-type-to-name "*" (py "rat") "RatTimes")
(add-token-and-type-to-name "*" (py "rea") "RealTimes")
(add-token-and-type-to-name "*" (py "cpx") "CpxTimes")

(add-token "/" 'mul-op (make-term-creator "/" "rat"))
(add-token-and-type-to-name "/" (py "rat") "RatDiv")
(add-token-and-type-to-name "/" (py "rea") "RealDiv")
(add-token-and-type-to-name "/" (py "cpx") "CpxDiv")

(add-token "abs" 'prefix-op (make-term-creator1 "abs" "int"))
(add-token-and-type-to-name "abs" (py "int") "IntAbs")
(add-token-and-type-to-name "abs" (py "rat") "RatAbs")
(add-token-and-type-to-name "abs" (py "rea") "RealAbs")
(add-token-and-type-to-name "abs" (py "cpx") "CpxAbs")

(add-token "**" 'exp-op (make-term-creator-exp "**"))

(add-token-and-types-to-name "**" (list (py "pos") (py "pos")) "PosExp")
(add-token-and-types-to-name "**" (list (py "pos") (py "nat")) "PosExp")

(add-token-and-types-to-name "**" (list (py "nat") (py "pos")) "NatExp")
(add-token-and-types-to-name "**" (list (py "nat") (py "nat")) "NatExp")

(add-token-and-types-to-name "**" (list (py "int") (py "pos")) "IntExp")
(add-token-and-types-to-name "**" (list (py "int") (py "nat")) "IntExp")

(add-token-and-types-to-name "**" (list (py "pos") (py "int")) "RatExp")
(add-token-and-types-to-name "**" (list (py "nat") (py "int")) "RatExp")
(add-token-and-types-to-name "**" (list (py "int") (py "int")) "RatExp")
(add-token-and-types-to-name "**" (list (py "rat") (py "pos")) "RatExp")
(add-token-and-types-to-name "**" (list (py "rat") (py "nat")) "RatExp")
(add-token-and-types-to-name "**" (list (py "rat") (py "int")) "RatExp")

(add-token-and-types-to-name "**" (list (py "rea") (py "pos")) "RealExp")
(add-token-and-types-to-name "**" (list (py "rea") (py "nat")) "RealExp")
(add-token-and-types-to-name "**" (list (py "rea") (py "int")) "RealExp")

(add-token-and-types-to-name "**" (list (py "cpx") (py "pos")) "CpxExp")
(add-token-and-types-to-name "**" (list (py "cpx") (py "nat")) "CpxExp")
(add-token-and-types-to-name "**" (list (py "cpx") (py "int")) "CpxExp")

;; (1#2)**(IntN 1) has type rat, but (IntN 1)**(1#2) as type cpx.
;; Hence generally we will need token-and-types-to-name for Exp.

(add-token "max" 'mul-op (make-term-creator "max" "pos"))
(add-token-and-type-to-name "max" (py "pos") "PosMax")
(add-token-and-type-to-name "max" (py "nat") "NatMax")
(add-token-and-type-to-name "max" (py "int") "IntMax")
(add-token-and-type-to-name "max" (py "rat") "RatMax")
(add-token-and-type-to-name "max" (py "rea") "RealMax")

(add-token "min" 'mul-op (make-term-creator "min" "pos"))
(add-token-and-type-to-name "min" (py "pos") "PosMin")
(add-token-and-type-to-name "min" (py "nat") "NatMin")
(add-token-and-type-to-name "min" (py "int") "IntMin")
(add-token-and-type-to-name "min" (py "rat") "RatMin")
(add-token-and-type-to-name "min" (py "rea") "RealMin")

(add-token "==" 'rel-op (make-term-creator "==" "rat"))
(add-token-and-type-to-name "==" (py "rat") "RatEqv")

(add-token "<" 'rel-op (make-term-creator "<" "pos"))
(add-token-and-type-to-name "<" (py "pos") "PosLt")
(add-token-and-type-to-name "<" (py "nat") "NatLt")
(add-token-and-type-to-name "<" (py "int") "IntLt")
(add-token-and-type-to-name "<" (py "rat") "RatLt")

(add-token "<=" 'rel-op (make-term-creator "<=" "pos"))
(add-token-and-type-to-name "<=" (py "pos") "PosLe")
(add-token-and-type-to-name "<=" (py "nat") "NatLe")
(add-token-and-type-to-name "<=" (py "int") "IntLe")
(add-token-and-type-to-name "<=" (py "rat") "RatLe")

;; (pp (pt "n+z"))
;; (pp (pt "n<a"))
;; (pp (pt "a**k"))

(define (make-display-creator name display-string token-type)
	 (lambda (x)
	   (let ((op (term-in-app-form-to-final-op x))
		 (args (term-in-app-form-to-args x)))
	     (if (and (term-in-const-form? op)
		      (string=? name (const-to-name
				      (term-in-const-form-to-const op)))
		      (= 2 (length args)))
		 (list token-type display-string
		       (term-to-token-tree (term-to-original (car args)))
		       (term-to-token-tree (term-to-original (cadr args))))
		 #f))))
(define (make-display-creator1 name display-string token-type)
	 (lambda (x)
	   (let ((op (term-in-app-form-to-final-op x))
		 (args (term-in-app-form-to-args x)))
	     (if (and (term-in-const-form? op)
		      (string=? name (const-to-name
				      (term-in-const-form-to-const op)))
		      (= 1 (length args)))
		 (list token-type display-string
		       (term-to-token-tree (term-to-original (car args))))
		 #f))))

(add-display (py "pos") (make-display-creator "PosPlus" "+" 'add-op))
(add-display (py "nat") (make-display-creator "NatPlus" "+" 'add-op))
(add-display (py "int") (make-display-creator "IntPlus" "+" 'add-op))
(add-display (py "rat") (make-display-creator "RatPlus" "+" 'add-op))
(add-display (py "rea") (make-display-creator "RealPlus" "+" 'add-op))
(add-display (py "cpx") (make-display-creator "CpxPlus" "+" 'add-op))

(add-display (py "pos") (make-display-creator "PosMinus" "--" 'add-op))
(add-display (py "nat") (make-display-creator "NatMinus" "--" 'add-op))
(add-display (py "int") (make-display-creator "IntMinus" "-" 'add-op))
(add-display (py "rat") (make-display-creator "RatMinus" "-" 'add-op))
(add-display (py "rea") (make-display-creator "RealMinus" "-" 'add-op))
(add-display (py "cpx") (make-display-creator "CpxMinus" "-" 'add-op))

(add-display (py "pos") (make-display-creator "PosTimes" "*" 'mul-op))
(add-display (py "nat") (make-display-creator "NatTimes" "*" 'mul-op))
(add-display (py "int") (make-display-creator "IntTimes" "*" 'mul-op))
(add-display (py "rat") (make-display-creator "RatTimes" "*" 'mul-op))
(add-display (py "rea") (make-display-creator "RealTimes" "*" 'mul-op))
(add-display (py "cpx") (make-display-creator "CpxTimes" "*" 'mul-op))

(add-display (py "rat") (make-display-creator "RatDiv" "/" 'mul-op))
(add-display (py "rea") (make-display-creator "RealDiv" "/" 'mul-op))
(add-display (py "cpx") (make-display-creator "CpxDiv" "/" 'mul-op))

(add-display (py "nat") (make-display-creator1 "IntAbs" "abs" 'prefix-op))
(add-display (py "int") (make-display-creator1 "IntAbs" "abs" 'prefix-op))
(add-display (py "rat") (make-display-creator1 "RatAbs" "abs" 'prefix-op))
(add-display (py "rea") (make-display-creator1 "RealAbs" "abs" 'prefix-op))
(add-display (py "cpx") (make-display-creator1 "CpxAbs" "abs" 'prefix-op))

(add-display (py "pos") (make-display-creator "PosExp" "**" 'exp-op))
(add-display (py "nat") (make-display-creator "NatExp" "**" 'exp-op))
(add-display (py "int") (make-display-creator "IntExp" "**" 'exp-op))
(add-display (py "rat") (make-display-creator "RatExp" "**" 'exp-op))
(add-display (py "rea") (make-display-creator "RealExp" "**" 'exp-op))
(add-display (py "cpx") (make-display-creator "CpxExp" "**" 'exp-op))

(add-display (py "pos") (make-display-creator "PosMax" "max" 'mul-op))
(add-display (py "nat") (make-display-creator "NatMax" "max" 'mul-op))
(add-display (py "int") (make-display-creator "IntMax" "max" 'mul-op))
(add-display (py "rat") (make-display-creator "RatMax" "max" 'mul-op))
(add-display (py "rea") (make-display-creator "RealMax" "max" 'mul-op))

(add-display (py "pos") (make-display-creator "PosMin" "min" 'mul-op))
(add-display (py "nat") (make-display-creator "NatMin" "min" 'mul-op))
(add-display (py "int") (make-display-creator "IntMin" "min" 'mul-op))
(add-display (py "rat") (make-display-creator "RatMin" "min" 'mul-op))
(add-display (py "rea") (make-display-creator "RealMin" "min" 'mul-op))

(add-display (py "boole") (make-display-creator "RatEqv" "==" 'rel-op))

(add-display (py "boole") (make-display-creator "PosLt" "<" 'rel-op))
(add-display (py "boole") (make-display-creator "NatLt" "<" 'rel-op))
(add-display (py "boole") (make-display-creator "IntLt" "<" 'rel-op))
(add-display (py "boole") (make-display-creator "RatLt" "<" 'rel-op))

(add-display (py "boole") (make-display-creator "PosLe" "<=" 'rel-op))
(add-display (py "boole") (make-display-creator "NatLe" "<=" 'rel-op))
(add-display (py "boole") (make-display-creator "IntLe" "<=" 'rel-op))
(add-display (py "boole") (make-display-creator "RatLe" "<=" 'rel-op))

;; (pp (pt "n<=i"))
;; (pp (pt "n<a"))
;; (pp (pt "n<m"))
;; (pp (pt "n==m"))
;; (pp (pt "i==m"))
;; (pp (pt "i==a"))
;; (pp (pt "n min m"))
;; (pp (pt "a max i"))
;; (pp (pt "a**i"))
;; (pp (pt "abs i"))
;; (pp (pt "2/3"))
;; (pp (pt "a/z"))
;; (pp (pt "k/z"))
;; (pp (pt "k*z"))
;; (pp (pt "k-z"))
;; (pp (pt "p-n"))
;; (pp (pt "p--n"))
;; (pp (pt "(IntN p)+q"))
;; (pp (pt "(IntN p)+x"))
;; (pp (pt "(IntN p)+z"))
;; (pp (pt "a+p"))
;; (pp (pt "a+z"))
;; (pp (pt "x+z"))

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

;; (pp (pt "1#2**k"))
;; (pp (pf "abs(x seq(x mod(IntS k))-y seq(y mod(IntS k))) <= 1/2**k"))

(add-ids
 (list (list "RealEq" (make-arity (py "rea") (py "rea"))))
 '("allnc x^,y^(
    allnc k abs(x^ seq(x^ mod(IntS k))-y^ seq(y^ mod(IntS k)))<=1/2**k ->
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

'(
(define idpc
  (idpredconst-name-and-types-and-cterms-to-idpredconst "RealEq" '() '()))
)
;; There are no types, since the clauses do not contain type variables,
;; and no cterms, since the clauses do not contain parameter predicate
;; variables.
'(
(define aconst0 (number-and-idpredconst-to-intro-aconst 0 idpc))
(pp (aconst-to-formula aconst0))
)
'(
allnc x^,y^(
 allnc k abs(x^ seq(x^ mod(IntS k))-y^ seq(y^ mod(IntS k)))<=1/2**k ->
 x^ ===y^)
)

;; RealEqElim
(set-goal
 "allnc x^,y^(x^ ===y^ ->
          allnc k abs(x^ seq(x^ mod(IntS k))-y^ seq(y^ mod(IntS k)))<=1/2**k)")
(assume "x^" "y^" "x=y")
(elim "x=y")
(search)
;; Proof finished.
(save "RealEqElim")

;; The following variant will be more useful, because its head will be
;; more often of the form of a given goal.

;; RealEqElimVariant
(set-goal
 "allnc as^,M^,bs^,N^(RealConstr as^ M^ ===RealConstr bs^ N^ ->
                allnc k abs(as^(M^(IntS k))-bs^(N^(IntS k)))<=1/2**k)")
(strip)
(use-with "RealEqElim"
	  (pt "RealConstr as^ M^") (pt "RealConstr bs^ N^") 1 (pt "k"))
;; Proof finished.
(save "RealEqElimVariant")

;; RealPos is a decidable property and hence can be considered as a
;; program constant.

(add-program-constant "RealPos" (py "rea=>int=>boole") t-deg-zero)

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

(add-computation-rule "RealPos(RealConstr as M)k" "1/2**k<=as(M(k+1))")

;; ;; RealPosTotal
;; (set-goal (rename-variables (term-to-totality-formula (pt "RealPos"))))
;; (assume "x^" "Tx" "k^" "Tk")
;; (elim "Tx")
;; (assume "as^" "Tas" "M^" "TM")
;; (ng #t)
;; (use "RatLeTotal") ;proved only later in this file

;; RealLt is a decidable property and hence can be considered as a
;; program constant.

(add-program-constant "RealLt" (py "rea=>rea=>int=>boole") t-deg-zero)

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

(add-computation-rule
 "RealLt(RealConstr as M)(RealConstr bs N)k"
 "RealPos(RealConstr bs N-RealConstr as M)k")

;; ; RealLtTotal
;; (set-goal (rename-variables (term-to-totality-formula (pt "RealLt"))))
;; (assume "x^" "Tx" "y^" "Ty" "k^" "Tk")
;; (elim "Tx")
;; (assume "as^" "Tas" "M^" "TM")
;; (elim "Ty")
;; (assume "bs^" "Tbs" "N^" "TN")
;; (ng #t)
;; ; ?_7:TotalBoole(RealPos(RealConstr bs^ M^ -RealConstr as^ N^)k^)
;; ; Postponed since RealPosTotal is proved only later in this file.

;; Non-negative reals are defined inductively

(add-ids
 (list (list "RealNNeg" (make-arity (py "rea"))))
 '("allnc x^(allnc k 0<=x^ seq(x^ mod k)+1/2**k -> RealNNeg x^)"
 "RealNNegIntro"))

;; RealNNegElim
(set-goal "allnc x^(RealNNeg x^ -> allnc k 0<=x^ seq(x^ mod k)+1/2**k)")
(assume "x^" "NNegx")
(elim "NNegx")
(search)
;; Proof finished.
(save "RealNNegElim")

;; The following variant will be more useful, because its head will be
;; more often of the form of a given goal.

;; RealNNegElimVariant
(set-goal
 "allnc as^,M^(RealNNeg(RealConstr as^ M^) -> allnc k 0<=as^(M^ k)+1/2**k)")
(strip)
(use-with "RealNNegElim" (pt "RealConstr as^ M^") 1 (pt "k"))
;; Proof finished.
(save "RealNNegElimVariant")

;; For reals less-than-or-equal-to is undecidable and hence must be
;; treated as an inductively defined predicate.

(add-ids
 (list (list "RealLe" (make-arity (py "rea") (py "rea"))))
 '("allnc x^,y^(RealNNeg(y^ -x^) -> RealLe x^ y^)" "RealLeIntro"))

;; Notice that we cannot take <= and use overloading, because the token
;; <= has token type rel-op and hence produces a term, not a predicate.

(add-token
 "<<="
 'pred-infix
 (lambda (x y)
   (make-predicate-formula (make-idpredconst "RealLe" '() '()) x y)))

(add-idpredconst-display "RealLe" 'pred-infix "<<=")
'(
(define idpc
  (idpredconst-name-and-types-and-cterms-to-idpredconst "RealLe" '() '()))
)

;; There are no types, since the clauses do not contain type variables,
;; and no cterms, since the clauses do not contain parameter predicate
;; variables.
'(
(define aconst0 (number-and-idpredconst-to-intro-aconst 0 idpc))
(pp (aconst-to-formula aconst0))
allnc x^,y^(RealNNeg(y^ -x^) -> x^ <<=y^)
)

;; RealLeElim
(set-goal "all x^,y^(x^ <<=y^ -> RealNNeg(y^ -x^))")
(assume "x^" "y^" "x<=y")
(elim "x<=y")
(search)
;; Proof finished.
(save "RealLeElim")

;; The following variant will be useful as well, when its head is of
;; the form of a given goal.  However, the proof below assumes
;;  (add-computation-rule
;;   (pt "RealConstr as M-RealConstr bs N")
;;   (pt "RealConstr([n]as n-bs n)([k]M(k+1)max N(k+1))"))
;; which will only be added later.  Postponed.

'(
(set-goal "allnc as^,M^,bs^,N^(
 RealConstr as^ M^ <<=RealConstr bs^ N^ ->
 RealNNeg(RealConstr([n]bs^ n-as^ n)([k]N^(k+1)max M^(k+1))))")
(strip)
(use-with "RealLeElim" (pt "RealConstr as^ M^") (pt "RealConstr bs^ N^") 1)
(save "RealLeElimVariant")
)


;; 3. Arithmetic
;; =============

;; BooleEqTotal is proved in ets.scm.  NatEqTotal is proved in nat.scm

;; PosEqTotal
(set-goal "allnc p^(
 TotalPos p^ -> allnc q^(TotalPos q^ -> TotalBoole(p^ =q^)))")
(assume "p^" "Tp")
(elim "Tp")
(assume "q^" "Tq")
(elim "Tq")
(use "TotalBooleTrue")
(assume "q^1" "Useless1" "Useless2")
(use "TotalBooleFalse")
(assume "q^1" "Useless1" "Useless2")
(use "TotalBooleFalse")

(assume "p^1" "Tp1" "IHp1" "q^" "Tq")
(elim "Tq")
(use "TotalBooleFalse")
(assume "q^1" "Tq1" "Useless")
(ng #t)
(use "IHp1")
(use "Tq1")
(assume "q^1" "Useless1" "Useless2")
(use "TotalBooleFalse")

(assume "p^1" "Tp1" "IHp1" "q^" "Tq")
(elim "Tq")
(use "TotalBooleFalse")
(assume "q^1" "Useless1" "Useless2")
(use "TotalBooleFalse")
(assume "q^1" "Tq1" "Useless")
(use "IHp1")
(use "Tq1")
;; Proof finished.
(save "PosEqTotal")

(add-mr-ids "TotalBoole")
(display-idpc "TotalBooleMR")

;; PosEqTotalReal
(set-goal (rename-variables
	   (real-and-formula-to-mr-formula
	    (pt "[p,q]p=q")
	    (proof-to-formula (theorem-name-to-proof "PosEqTotal")))))
(assume "p^" "p^0" "TMRp0p")
(elim "TMRp0p")
(assume "q^" "q^0" "TMRq0q")
(elim "TMRq0q")
(use "TotalBooleTrueMR")
(assume "q^1" "q^10" "Useless1" "Useless2")
(use "TotalBooleFalseMR")
(assume "q^1" "q^10" "Useless1" "Useless2")
(use "TotalBooleFalseMR")

(assume "q^" "q^0" "Useless1" "IH" "q^1" "q^10" "TMRq10q1")
(elim "TMRq10q1")
(use "TotalBooleFalseMR")
(assume "q^2" "q^20" "TMRq20q2" "Useless2")
(use "IH")
(use "TMRq20q2")
(assume "q^2" "q^20" "TMRq20q2" "Useless2")
(use "TotalBooleFalseMR")

(assume "q^" "q^0" "Useless1" "IH" "q^1" "q^10" "TMRq10q1")
(elim "TMRq10q1")
(use "TotalBooleFalseMR")
(assume "q^2" "q^20" "TMRq20q2" "Useless2")
(use "TotalBooleFalseMR")
(assume "q^2" "q^20" "TMRq20q2" "Useless2")
(use "IH")
(use "TMRq20q2")
;; Proof finished.
(save "PosEqTotalReal")

(pp (rename-variables (nt (proof-to-extracted-term "PosEqTotal"))))
;; =

;; Hence we are allowed to change the extracted term of PosEqTotal into
;; [n,m]n=m.  Then proof-to-soundness-proof at FinAlgEqTotal looks for
;; FinAlgEqTotalReal and uses it.  An error is raised if
;; FinAlgEqTotalReal does not exist.

;; (pp (theorem-to-extracted-term (theorem-name-to-aconst "PosEqTotal")))
;; [p^,q^]p^ =q^

(add-computation-rules
 "PosS One" "SZero One"
 "PosS(SZero pos)" "SOne pos"
 "PosS(SOne pos)" "SZero(PosS pos)")

;; PosSTotal
(set-goal (rename-variables (term-to-totality-formula (pt "PosS"))))
(assume "p^" "Tp")
(elim "Tp")
;; ?_3:TotalPos(PosS 1)
(ng #t)
(use "TotalPosSZero")
(use "TotalPosOne")
;; ?_4:allnc pos^(
;;      TotalPos pos^ -> TotalPos(PosS pos^) -> TotalPos(PosS(SZero pos^)))
(assume "q^" "Tq" "TSq")
(ng #t)
(use "TotalPosSOne")
(use "Tq")
;; ?_5:allnc pos^(
;;      TotalPos pos^ -> TotalPos(PosS pos^) -> TotalPos(PosS(SOne pos^)))
(assume "q^" "Tq" "TSq")
(ng #t)
(use "TotalPosSZero")
(use "TSq")
;; Proof finished.
(save "PosSTotal")

(define sproof (proof-to-soundness-proof "PosSTotal"))
;; (cdp sproof)
;; (pp (rename-variables (proof-to-formula sproof)))
;; (proof-to-expr-with-formulas sproof)
(define nsproof (np sproof))
;; (proof-to-expr-with-formulas nsproof)
;; (pp (rename-variables (proof-to-formula nsproof)))
'(
allnc p^,p^0(
 TotalPosMR p^0 p^ ->
 TotalPosMR((Rec pos=>pos)p^0 2([p1,p2]SOne p1)([p1]SZero))(PosS p^))
)

;; PosSTotalReal
(set-goal (rename-variables
	   (real-and-formula-to-mr-formula
	    (pt "PosS")
	    (proof-to-formula (theorem-name-to-proof "PosSTotal")))))
(assume "p^" "p^0" "TMRp0p")
(elim "TMRp0p")
(use "TotalPosSZeroMR")
(use "TotalPosOneMR")
(assume "q^" "q^0" "TMRq0q" "IH")
(use "TotalPosSOneMR")
(use "TMRq0q")
(assume "q^" "q^0" "TMRq0q" "IH")
(ng #t)
(use "TotalPosSZeroMR")
(use "IH")
;; Proof finished.
(save "PosSTotalReal")

;; (pp (theorem-to-extracted-term (theorem-name-to-aconst "PosSTotal")))
;; PosS

;; Both PosS and [p^0](Rec pos=>pos)p^0 2([p1,p2]SOne p1)([p1]SZero)
;; are realizers for the formula of the theorem PosSTotal.
;; theorem-to-extracted-term picks PosS, whereas extraction from the
;; proof of PosSTotal gives the latter term with Rec.

(proof-to-expr-with-formulas "PosSTotalReal")
;; simpler than et(nsproof).

(pp (rename-variables
     (proof-to-formula (theorem-name-to-proof "PosSTotalReal"))))
;; allnc p^,p^0(TotalPosMR p^0 p^ --> TotalPosMR(PosS p^0)(PosS p^))
;; Also simpler than the formula of sproof.

;; Correctness of PosS as realizer for PosSTotal is verified by
;; PosSTotalReal.  Therefore proof-to-soundness-proof at theorem
;; PosSTotal should use the theorem PosSTotalReal, and similarly for
;; other pconsts.

(pp (rename-variables (proof-to-extracted-term "PosSTotal")))

(add-computation-rules
 "PosPred One" "One"
 "PosPred(SZero One)" "One"
 "PosPred(SZero(SZero pos))" "SOne(PosPred(SZero pos))"
 "PosPred(SZero(SOne pos))" "SOne(SZero pos)"
 "PosPred(SOne pos)" "SZero pos")

;; (display-pconst "PosPred")

;; PosPredTotal
(set-goal (rename-variables (term-to-totality-formula (pt "PosPred"))))
(assume "p^" "Tp")
(elim "Tp")
;; ?_3:TotalPos(PosPred 1)
(ng #t)
(use "TotalPosOne")
;; ?_4:allnc pos^(
;;      TotalPos pos^ ->
;;      TotalPos(PosPred pos^) -> TotalPos(PosPred(SZero pos^)))
(assume "q^" "Tq" "TPq")
(ng #t)
(elim "Tq")
;; ?_9:TotalPos(PosPred 2)
(ng #t)
(use "TotalPosOne")
;; ?_10:allnc pos^(
;;       TotalPos pos^ ->
;;       TotalPos(PosPred(SZero pos^)) ->
;;       TotalPos(PosPred(SZero(SZero pos^))))
(assume "q^0" "Tq0" "TPSZq0")
(ng #t)
(use "TotalPosSOne")
(use "TPSZq0")
;; ?_11:allnc pos^(
;;       TotalPos pos^ ->
;;       TotalPos(PosPred(SZero pos^)) -> TotalPos(PosPred(SZero(SOne pos^))))
(assume "q^1" "Tq1" "TPSZq1")
(ng #t)
(use "TotalPosSOne")
(use "TotalPosSZero")
(use "Tq1")
;; ?_5:allnc pos^(
;;      TotalPos pos^ ->
;;      TotalPos(PosPred pos^) -> TotalPos(PosPred(SOne pos^)))
(assume "q^" "Tq" "TPq")
(ng #t)
(use "TotalPosSZero")
(use "Tq")
;; Proof finished.
(save "PosPredTotal")

;; PosPredTotalReal
(set-goal (rename-variables
	   (real-and-formula-to-mr-formula
	    (pt "PosPred")
	    (proof-to-formula (theorem-name-to-proof "PosPredTotal")))))
(assume "p^" "p^0" "TMRp0p")
(elim "TMRp0p")
(use "TotalPosOneMR")

(assume "q^" "q^0" "TMRq0q" "IH")
(elim "TMRq0q")
(use "TotalPosOneMR")
(assume "q^2" "q^20" "TMRq20q2" "IH2")
(ng #t)
(use "TotalPosSOneMR")
(use "IH2")
(assume "q^2" "q^20" "TMRq20q2" "Useless")
(ng #t)
(use "TotalPosSOneMR")
(use "TotalPosSZeroMR")
(use "TMRq20q2")

(assume "q^" "q^0" "TMRq0q" "IH")
(ng #t)
(use "TotalPosSZeroMR")
(use "TMRq0q")
;; Proof finished.
(save "PosPredTotalReal")

(add-computation-rules
 "PosHalf One" "One"
 "PosHalf(SZero pos)" "pos"
 "PosHalf(SOne pos)" "pos")

;; PosHalfTotal
(set-goal (rename-variables (term-to-totality-formula (pt "PosHalf"))))
(assume "p^" "Tp")
(elim "Tp")
;; ?_3:TotalPos(PosHalf 1)
(ng #t)
(use "TotalPosOne")
;; ?_4:allnc pos^(
;;      TotalPos pos^ ->
;;      TotalPos(PosHalf pos^) -> TotalPos(PosHalf(SZero pos^)))
(assume "q^" "Tq" "THq")
(ng #t)
(use "Tq")
;; ?_5:allnc pos^(
;;      TotalPos pos^ ->
;;      TotalPos(PosHalf pos^) -> TotalPos(PosHalf(SOne pos^)))
(assume "q^" "Tq" "THq")
(ng #t)
(use "Tq")
;; Proof finished.
(save "PosHalfTotal")

(add-computation-rules
 "PosToNat One" "Succ Zero"
 "PosToNat(SZero pos)" "NatDouble(PosToNat pos)"
 "PosToNat(SOne pos)" "Succ(PosToNat(SZero pos))")

;; PosToNatTotal
(set-goal (rename-variables (term-to-totality-formula (pt "PosToNat"))))
(assume "pos^" "Tpos")
(elim "Tpos") ;3-5
(use "TotalNatSucc")
(use "TotalNatZero")
;; 4
(assume "pos^1" "Tpos1" "IH")
(ng #t)
(use "NatDoubleTotal")
(use "IH")
;; 5
(assume "pos^1" "Tpos1" "IH")
(ng #t)
(use "TotalNatSucc")
(use "NatDoubleTotal")
(use "IH")
;; Proof finished.
(save "PosToNatTotal")

;; PosToNatDefSZero
(set-goal "all pos PosToNat(SZero pos)=NatDouble(PosToNat pos)")
(assume "pos")
(use "Truth")
;; Proof finished.
(save "PosToNatDefSZero")

;; PosToNatDefSOne
(set-goal "all pos PosToNat(SOne pos)=Succ(PosToNat(SZero pos))")
(assume "pos")
(use "Truth")
;; Proof finished.
(save "PosToNatDefSOne")

(replace-item-in-algebra-edge-to-embed-term-alist
         "pos" "nat"
	 (let ((var (make-var (make-alg "pos") -1 t-deg-one "")))
	   (make-term-in-abst-form
	    var (make-term-in-app-form
		 (make-term-in-const-form
		  (pconst-name-to-pconst "PosToNat"))
		 (make-term-in-var-form var)))))

;; We define the inverse NatToPos of PosToNat , using GRec

(add-program-constant "NatToPosStep" (py "nat=>(nat=>pos)=>pos"))

(add-computation-rules
 "NatToPosStep nat(nat=>pos)"
 "[if (NatEven nat)
      (SZero((nat=>pos)(NatHalf nat)))
      [if (nat=Succ Zero) One (SOne((nat=>pos)(NatHalf nat)))]]")

;; NatToPosStepTotal
(set-goal (rename-variables (term-to-totality-formula (pt "NatToPosStep"))))
(assume "nat^" "Tnat" "(nat=>pos)^" "Th")
(ng #t)
(use "BooleIfTotal")
(use "NatEvenTotal")
(use "Tnat")
(use "TotalPosSZero")
(use "Th")
(use "NatHalfTotal")
(use "Tnat")
(use "BooleIfTotal")
(use "NatEqTotal")
(use "Tnat")
(use "TotalNatSucc")
(use "TotalNatZero")
(use "TotalPosOne")
(use "TotalPosSOne")
(use "Th")
(use "NatHalfTotal")
(use "Tnat")
;; Proof finished.
(save "NatToPosStepTotal")

;; NatToPosStepDef
(set-goal "all nat,(nat=>pos)
  NatToPosStep nat(nat=>pos)=
  [if (NatEven nat)
  (SZero((nat=>pos)(NatHalf nat)))
  [if (nat=Succ Zero) 1 (SOne((nat=>pos)(NatHalf nat)))]]")
(assume "nat" "(nat=>pos)")
(use "Truth")
;; Proof finished.
(save "NatToPosStepDef")

(add-program-constant "NatToPos" (py "nat=>pos"))

(add-computation-rules
 "NatToPos nat" "(GRec nat pos)([nat]nat)nat NatToPosStep")

;; NatToPosTotal
(set-goal (term-to-totality-formula (rename-variables (pt "NatToPos"))))
(use "AllTotalElim")
(assume "n")
(ng #t)
(use "BooleIfTotal")
(use "NatEvenTotal")
(use "NatTotalVar")
(use "TotalPosSZero")
(use "PosTotalVar")
(use "BooleIfTotal")
(use "NatEqTotal")
(use "NatTotalVar")
(use "TotalNatSucc")
(use "TotalNatZero")
(use "TotalPosOne")
(use "TotalPosSOne")
(use "PosTotalVar")
;; Proof finished.
(save "NatToPosTotal")

;; NatToPosDef
(set-goal "all nat NatToPos nat=(GRec nat pos)([nat]nat)nat NatToPosStep")
(assume "nat")
(use "Truth")
;; Proof finished
(save "NatToPosDef")

(add-computation-rules
 "NatToInt Zero" "IntZero"
 "NatToInt(Succ nat)" "IntS(NatToInt nat)")

;; (display-pconst "NatToInt")

;; NatToIntTotal
;; (set-goal (rename-variables (term-to-totality-formula (pt "NatToInt"))))
;; (assume "n^" "Tn")
;; (elim "Tn")
;; ; ?_3:TotalInt Zero
;; (use "TotalIntIntZero")
;; ; ?_4:allnc nat^(TotalNat nat^ -> TotalInt nat^ -> TotalInt(Succ nat^))
;; (assume "m^" "Tm" "IH")
;; (ng #t)
;; ?_6:TotalInt(IntS m^)
;; Postponed: we first need totality of IntS

(add-computation-rules
 "pos1+One" "PosS pos1"
 "One+SZero pos1" "SOne pos1"
 "SZero pos1+SZero pos2" "SZero(pos1+pos2)"
 "SOne pos1+SZero pos2" "SOne(pos1+pos2)"
 "One+SOne pos1" "SZero(PosS pos1)"
 "SZero pos1+SOne pos2" "SOne(pos1+pos2)"
 "SOne pos1+SOne pos2" "SZero(PosS(pos1+pos2))")

;; PosPlusTotal
(set-goal (rename-variables (term-to-totality-formula (pt "PosPlus"))))
(assume "p^" "Tp")
(elim "Tp")

;; ?_3:allnc p^(TotalPos p^ -> TotalPos(1+p^))
(assume "q^" "Tq")
(elim "Tq")
(ng #t)
(use "TotalPosSZero")
(use "TotalPosOne")

(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "TotalPosSOne")
(use "Tq1")

(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "TotalPosSZero")
(use "PosSTotal")
(use "Tq1")

;; ?_4:allnc pos^(
;;      TotalPos pos^ ->
;;      allnc p^(TotalPos p^ -> TotalPos(pos^ +p^)) ->
;;      allnc p^(TotalPos p^ -> TotalPos(SZero pos^ +p^)))

(assume "q^" "Tq" "IHq" "q^1" "Tq1")
(elim "Tq1")
(ng #t)
(use "TotalPosSOne")
(use "Tq")

(assume "q^2" "Tq2" "Useless")
(ng #t)
(use "TotalPosSZero")
(use "IHq")
(use "Tq2")

(assume "q^2" "Tq2" "Useless")
(ng #t)
(use "TotalPosSOne")
(use "IHq")
(use "Tq2")

;; ?_5:allnc pos^(
;;      TotalPos pos^ ->
;;      allnc p^(TotalPos p^ -> TotalPos(pos^ +p^)) ->
;;      allnc p^(TotalPos p^ -> TotalPos(SOne pos^ +p^)))

(assume "q^" "Tq" "IHq" "q^1" "Tq1")
(elim "Tq1")
(ng #t)
(use "TotalPosSZero")
(use "PosSTotal")
(use "Tq")

(assume "q^2" "Tq2" "Useless")
(ng #t)
(use "TotalPosSOne")
(use "IHq")
(use "Tq2")

(assume "q^2" "Tq2" "Useless")
(ng #t)
(use "TotalPosSZero")
(use "PosSTotal")
(use "IHq")
(use "Tq2")
;; Proof finished.
(save "PosPlusTotal")

;; PosPlusTotalReal
(set-goal (rename-variables
	   (real-and-formula-to-mr-formula
	    (pt "PosPlus")
	    (proof-to-formula (theorem-name-to-proof "PosPlusTotal")))))
(assume "p^" "p^0" "TMRp0p")
(elim "TMRp0p")
(assume "q^" "q^0" "TMRq0q")
(elim "TMRq0q")
(use "TotalPosSZeroMR")
(use "TotalPosOneMR")
(assume "q^1" "q^10" "TMRq10q1" "IH")
(ng #t)
(use "TotalPosSOneMR")
(use "TMRq10q1")
(assume "q^1" "q^10" "TMRq10q1" "IH")
(ng #t)
(use "TotalPosSZeroMR")
(use "PosSTotalReal")
(use "TMRq10q1")

;; ?_4:allnc pos^,pos^0(
;;      TotalPosMR pos^0 pos^ -->
;;      allnc p^,p^0(TotalPosMR p^0 p^ --> TotalPosMR(pos^0+p^0)(pos^ +p^)) ->
;;      allnc p^,p^0(
;;       TotalPosMR p^0 p^ --> TotalPosMR(SZero pos^0+p^0)(SZero pos^ +p^)))
(assume "p^1" "p^10" "TMRp10p1" "IHp1" "q^" "q^0" "TMRq0q")
(elim "TMRq0q")
(ng #t)
(use "TotalPosSOneMR")
(use "TMRp10p1")

(assume "q^1" "q^10" "TMRq10q1" "IHq1")
(ng #t)
(use "TotalPosSZeroMR")
(use "IHp1")
(use "TMRq10q1")

(assume "q^1" "q^10" "TMRq10q1" "IHq1")
(ng #t)
(use "TotalPosSOneMR")
(use "IHp1")
(use "TMRq10q1")

;; ?_5:allnc pos^,pos^0(
;;      TotalPosMR pos^0 pos^ -->
;;      allnc p^,p^0(TotalPosMR p^0 p^ --> TotalPosMR(pos^0+p^0)(pos^ +p^)) ->
;;      allnc p^,p^0(
;;       TotalPosMR p^0 p^ --> TotalPosMR(SOne pos^0+p^0)(SOne pos^ +p^)))

(assume "p^1" "p^10" "TMRp10p1" "IHp1" "q^" "q^0" "TMRq0q")
(elim "TMRq0q")
(ng #t)
(use "TotalPosSZeroMR")
(use "PosSTotalReal")
(use "TMRp10p1")

(assume "q^1" "q^10" "TMRq10q1" "IHq1")
(ng #t)
(use "TotalPosSOneMR")
(use "IHp1")
(use "TMRq10q1")

(assume "q^1" "q^10" "TMRq10q1" "IHq1")
(ng #t)
(use "TotalPosSZeroMR")
(use "PosSTotalReal")
(use "IHp1")
(use "TMRq10q1")
;; Proof finished.
(save "PosPlusTotalReal")

;; We derive some rewrite rules.  To ensure termination, we (1) decrease
;; the sum of the lengths of summands, where the rhs counts more than
;; the lhs.

(set-goal "all pos PosPred(PosS pos)=pos")
(ind) ;2-4
(ng #t)
(use "Truth")
;; 3
(assume "pos" "IH")
(ng #t)
(use "Truth")
;; 4
(cases) ;8-10
(ng #t)
(strip)
(use "Truth")
(ng #t)
(strip)
(use "Truth")
(ng #t)
(assume "pos" "Hyp")
(use "Hyp")
;; Proof finished.
(add-rewrite-rule "PosPred(PosS pos)" "pos")

(set-goal "all pos One+pos=PosS pos")
(cases)
(auto)
;; Proof finished
(add-rewrite-rule "One+pos" "PosS pos")

(set-goal "all pos1,pos2 PosS pos1+pos2=PosS(pos1+pos2)")
(ind)
  (ind)
  (auto)
(assume "pos" "IHzero")
(ind)
  (auto)
(assume "pos" "IHone")
(ind)
(auto)
;; Proof finished
(add-rewrite-rule "PosS pos1+pos2" "PosS(pos1+pos2)")

(set-goal "all pos1,pos2 pos1+PosS pos2=PosS(pos1+pos2)")
(ind)
  (cases)
(auto)
(assume "p" "IH1")
(cases)
  (auto)
(assume "p" "IH2")
(cases)
(auto)
;; Proof finished
(add-rewrite-rule "pos1+PosS pos2" "PosS(pos1+pos2)")

;; To prove "all pos1,pos2,pos3 pos1+(pos2+pos3)=pos1+pos2+pos3" by
;; pos-induction seems to be difficult.  Solutions: (1) Using the rules
;; just proved one can mimic the proof in nat.  This requires
;; successor-induction for pos, which has to be proven before (see
;; wwwpublic/seminars/prosemss04/sucind.scm).  (2) Another more general
;; way out is to transfer the problem to nat via appropriate functions
;; and then use associativity in nat.  (For an alternative see
;; examples/ordinals/reflection_numbers_thms.scm)

;; GRecDef
(set-goal "all (nat=>nat),nat,(nat=>(nat=>pos)=>pos)
            (GRec nat pos)(nat=>nat)nat(nat=>(nat=>pos)=>pos)=
            (GRecGuard nat pos)(nat=>nat)nat(nat=>(nat=>pos)=>pos)True")
(assume "(nat=>nat)" "nat" "(nat=>(nat=>pos)=>pos)")
(use "Truth")
;; Proof finished.
(save "GRecDef")

;; NatToPosEqSZeroNatToPosHalf
(set-goal "all nat(Zero<nat -> NatEven nat ->
                   NatToPos nat=SZero(NatToPos(NatHalf nat)))")
(assume "nat" "0<nat" "Enat")
(ng #t)
(simp "Enat")
(ng #t)
(assert "NatHalf nat<nat")
 (use "NatHalfLt")
 (use "0<nat")
(assume "NatHalf nat<nat")
(simp "NatHalf nat<nat")
(ng #t)
(use "Truth")
;; Proof finished.
(save "NatToPosEqSZeroNatToPosHalf")

;; NatToPosEqSOneNatToPosHalf
(set-goal "all nat(Zero<nat -> (NatEven nat -> F) -> (nat=Succ Zero -> F) ->
                   NatToPos nat=SOne(NatToPos(NatHalf nat)))")
(assume "nat" "0<nat" "NatEven nat -> F" "nat=Succ Zero -> F")
(ng #t)
(simp "NatEven nat -> F")
(ng #t)
(simp "nat=Succ Zero -> F")
(ng #t)
(assert "NatHalf nat<nat")
 (use "NatHalfLt")
 (use "0<nat")
(assume "NatHalf nat<nat")
(simp "NatHalf nat<nat")
(ng #t)
(use "Truth")
;; Proof finished.
(save "NatToPosEqSOneNatToPosHalf")

;; NatHalfSuccEven
(set-goal "all nat(NatEven nat -> NatHalf(Succ nat)=NatHalf nat)")
(use "CVInd")
(assume "nat" "Prog" "Enat")
(cases (pt "nat"))
(ng #t)
(strip)
(use "Truth")
(assume "nat1" "nat=Sn1")
(cases (pt "nat1"))
(ng #t)
(assume "nat1=0")
(simphyp-with-to "nat=Sn1" "nat1=0" "nat=1")
(simphyp-with-to "Enat" "nat=1" "Absurd")
(use "Absurd")
(assume "nat2" "nat1=Sn2")
(ng #t)
(use "Prog")
(simp "nat=Sn1")
(simp "nat1=Sn2")
(use "NatLtTrans" (pt "Succ nat2"))
(use "Truth")
(use "Truth")
(simphyp-with-to "Enat" "nat=Sn1" "EnatSimp")
(simphyp-with-to "EnatSimp" "nat1=Sn2" "EnatSimpSimp")
(use "EnatSimpSimp")
;; Proof finished.
(save "NatHalfSuccEven")

;; PosToNatToPosId
(set-goal "all nat(Zero<nat -> PosToNat(NatToPos nat)=nat)")
(use "CVInd")
(assume "nat" "Prog" "0<nat")
(cases (pt "NatEven nat")) ;4,5
(assume "Enat")
(assert "NatToPos nat=SZero(NatToPos(NatHalf nat))")
 (use "NatToPosEqSZeroNatToPosHalf")
 (use "0<nat")
 (use "Enat")
(assume "NatToPos nat=SZero(NatToPos(NatHalf nat))")
(simp "NatToPos nat=SZero(NatToPos(NatHalf nat))")
(simp "PosToNatDefSZero")
(simp "Prog")
(use "NatDoubleHalfEven")
(use "Enat")
(use "NatLtZeroHalfEven")
(use "0<nat")
(use "Enat")
(use "NatHalfLt")
(use "0<nat")
;; 5
(assume "NatEven nat -> F")
(cases (pt "nat=Succ Zero"))
(assume "nat=1")
(simp "nat=1")
(ng #t)
(simp "NatEven nat -> F")
(ng #t)
(simp "nat=1")
(use "Truth")
(assume "nat=1 -> F")
(assert "NatToPos nat=SOne(NatToPos(NatHalf nat))")
 (use "NatToPosEqSOneNatToPosHalf")
 (use "0<nat")
 (use "NatEven nat -> F")
 (use "nat=1 -> F")
(assume "NatToPos nat=SOne(NatToPos(NatHalf nat))")
(simp "NatToPos nat=SOne(NatToPos(NatHalf nat))")
(simp "PosToNatDefSOne")
(cases (pt "nat"))
(assume "nat=0")
(use "Efq")
(simphyp-with-to "NatEven nat -> F" "nat=0" "Absurd")
(use "Absurd")
(use "Truth")
(assume "nat1" "nat=Succ nat1")
(simp "PosToNatDefSZero")
(assert "NatEven nat1")
(use "NatOddSuccToEven")
(simp "<-" "nat=Succ nat1")
(use "NatEven nat -> F")
(assume "Enat1")
(simp "NatHalfSuccEven")
(assert "PosToNat(SZero(NatToPos(NatHalf nat1)))=nat1")
 (simp "PosToNatDefSZero")
 (simp "Prog")
 (use "NatDoubleHalfEven")
 (use "Enat1")
 (cases (pt "nat1"))
 (assume "nat1=0")
 (use "nat=1 -> F")
 (simp "nat=Succ nat1")
 (use "nat1=0")
 (cases)
 (ng #t)
 (assume "nat1=1")
 (simphyp-with-to "Enat1" "nat1=1" "Absurd")
 (use "Absurd")
 (ng #t)
 (strip)
 (use "Truth")
 (simp "nat=Succ nat1")
 (use "NatHalfLtSucc")
(assume "PosToNat(SZero(NatToPos(NatHalf nat1)))=nat1")
(simp "Prog")
(simp "NatDoubleHalfEven")
(use "Truth")
(use "Enat1")
(use "NatLtZeroHalfEven")
(cases (pt "nat1"))
(assume "nat1=0")
(use "nat=1 -> F")
(simp "nat=Succ nat1")
(use "nat1=0")
(strip)
(use "Truth")
(use "Enat1")
(simp "nat=Succ nat1")
(use "NatHalfLtSucc")
(use "Enat1")
;; Proof finished.
(save "PosToNatToPosId")

;; NatToPosToNatId
(set-goal "all pos NatToPos(PosToNat pos)=pos")
(ind) ;2-4
(ng #t)
(use "Truth")
;; 3
(assume "pos" "IH")
(ng #t)
(simp "NatEvenDouble")
(ng #t)
(assert "all nat(Zero<nat -> Zero<NatDouble nat)")
 (ind)
 (ng #t)
 (assume "Absurd")
 (use "Absurd")
 (ng #t)
 (strip)
 (use "Truth")
(assume "NatDoublePos")
(assert "Zero<NatDouble(PosToNat pos)")
 (ind (pt "pos"))
 (use "Truth")
 (assume "pos1" "IH1")
 (ng #t)
 (use "NatDoublePos")
 (use "IH1")
 (assume "pos1" "IH1")
 (ng #t)
 (use "Truth")
(assume "Zero<NatDouble(PosToNat pos)")
(assert "NatHalf(NatDouble(PosToNat pos))<NatDouble(PosToNat pos)")
 (use "NatHalfLt")
 (use "Zero<NatDouble(PosToNat pos)")
(assume "NatHalf(NatDouble(PosToNat pos))<NatDouble(PosToNat pos)")
(simp "NatHalf(NatDouble(PosToNat pos))<NatDouble(PosToNat pos)")
(simp "NatHalfDouble")
(simp "IH")
(use "Truth")
;; 4
(assume "pos" "IH")
(ng #t)
(assert "NatEven(Succ(NatDouble(PosToNat pos))) -> F")
 (use "NatEvenSucc")
 (use "NatEvenDouble")
(assume "NatEven(Succ(NatDouble(PosToNat pos))) -> F")
(simp "NatEven(Succ(NatDouble(PosToNat pos))) -> F")
(ng #t)
(assert "all nat(Zero<nat -> Zero<NatDouble nat)")
 (ind)
 (ng #t)
 (assume "Absurd")
 (use "Absurd")
 (ng #t)
 (strip)
 (use "Truth")
(assume "NatDoublePos")
(assert "all pos Zero<PosToNat pos")
 (ind)
 (use "Truth")
 (assume "pos1" "IHpos1")
 (ng #t)
 (use "NatDoublePos")
 (use "IHpos1")
 (assume "pos1" "IHpos1")
 (ng #t)
 (use "Truth")
(assume "PosToNatPos")
(assert "Zero<NatDouble(PosToNat pos)")
 (use "NatDoublePos")
 (use "PosToNatPos")
(assume "Zero<NatDouble(PosToNat pos)")
(assert "NatDouble(PosToNat pos)=Zero -> F")
 (assume "NatDouble(PosToNat pos)=Zero")
 (simphyp-with-to "Zero<NatDouble(PosToNat pos)" "NatDouble(PosToNat pos)=Zero"
		  "Absurd")
 (use "Absurd")
(assume "NatDouble(PosToNat pos)=Zero -> F")
(simp "NatDouble(PosToNat pos)=Zero -> F")
(ng #t)
(assert "NatHalf(Succ(NatDouble(PosToNat pos)))<Succ(NatDouble(PosToNat pos))")
 (use "NatHalfLt")
 (use "Truth")
(assume "NatHalf(Succ(NatDouble(PosToNat pos)))<Succ(NatDouble(PosToNat pos))")
(simp "NatHalf(Succ(NatDouble(PosToNat pos)))<Succ(NatDouble(PosToNat pos))")
(simp "NatHalfSuccDouble")
(simp "IH")
(use "Truth")
;; Proof finished.
(save "NatToPosToNatId")

;; PosSDefSZero
(set-goal "all pos PosS(SZero pos)=SOne pos")
(assume "pos")
(use "Truth")
;; Proof finished
(save "PosSDefSZero")

;; PosSDefSOne
(set-goal "all pos PosS(SOne pos)=SZero(PosS pos)")
(assume "pos")
(use "Truth")
;; Proof finished
(save "PosSDefSOne")

;; SuccPosS
(set-goal "all nat(Zero<nat -> NatToPos(Succ nat)=PosS(NatToPos nat))")
(assert "all nat(Zero<nat -> Succ nat=PosToNat(PosS(NatToPos nat)))")
(use "CVInd")
(assume "nat" "Prog" "0<n")
(cases (pt "NatEven nat")) ;4,5
(assume "En")
(simp "NatToPosEqSZeroNatToPosHalf")
(simp "PosSDefSZero")
(simp "PosToNatDefSOne")
(simp "PosToNatDefSZero")
(simp "PosToNatToPosId")
(simp "NatDoubleHalfEven")
(use "Truth")
(use "En")
(use "NatLtZeroHalfEven")
(use "0<n")
(use "En")
(use "En")
(use "0<n")
;; 5
(assume "On")
(cases (pt "nat=Succ Zero"))
(assume "n=1")
(simp "n=1")
;; simp normalizes the goal, which we do not want.  Why?  Ok if order
;; in simp-with-intern is changed: consider normalized items last.
(ng #t)
(use "Truth")
(assume "n=/=1")
(simp "NatToPosEqSOneNatToPosHalf")
(simp "PosSDefSOne")
(simp "PosToNatDefSZero")
(simp "<-" "Prog")
(simp "NatDoubleDefSucc")
(ng #t)
(simp "NatDoubleHalfOdd")
(use "Truth")
(use "On")
(use "NatLtZeroHalfFinally")
(use "0<n")
(use "n=/=1")
(use "NatHalfLt")
(use "0<n")
(use "n=/=1")
(use "On")
(use "0<n")
;; Assertion proved
(assume "SuccPosSAux" "nat" "0<n")
(simp "SuccPosSAux")
(simp "NatToPosToNatId")
(use "Truth")
(use "0<n")
;; Proof finished.
(save "SuccPosS")

;; NatLt0Double
(set-goal "all nat(Zero<nat -> Zero<NatDouble nat)")
(cases)
(assume "Absurd")
(use "Absurd")
(strip)
(use "Truth")
;; Proof finished
(save "NatLt0Double")

;; NatLt0Pos
(set-goal "all pos Zero<pos")
(ind)
(use "Truth")
(ng #t)
(assume "pos" "0<p")
(use "NatLt0Double")
(use "0<p")
(ng #t)
(strip)
(use "Truth")
;; Proof finished.
(save "NatLt0Pos")

;; PosSSucc
(set-goal "all pos PosToNat(PosS pos)=Succ(PosToNat pos)")
(assume "pos")
(assert "PosToNat(PosS pos)=PosToNat(PosS(NatToPos(PosToNat pos)))")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "EqHyp")
(simp "EqHyp")
(simp "<-" "SuccPosS")
(simp "PosToNatToPosId")
(use "Truth")
(use "Truth")
(use "NatLt0Pos")
;; Proof finished.
(save "PosSSucc")

;; NatPlusDouble
(set-goal "all nat1,nat2 NatDouble nat1+NatDouble nat2=NatDouble(nat1+nat2)")
(assume "nat1")
(ind)
(use "Truth")
(assume "nat2" "IH")
(ng #t)
(use "IH")
;; Proof finished.
(save "NatPlusDouble")

;; We prove that PosToNat is an isomorphism w.r.t. +

;; PosToNatPlus
(set-goal "all pos1,pos2 PosToNat(pos1+pos2)=PosToNat pos1+PosToNat pos2")
(ind) ;2-4
(assume "pos2")
(ng #t)
(use "PosSSucc")
(assume "pos1" "IH1")
(cases) ;8-10
(ng #t)
(use "Truth")
;; 9
(assume "pos2")
(ng #t)
(simp "NatPlusDouble")
(simp "IH1")
(use "Truth")
;; 10
(assume "pos2")
(ng #t)
(simp "NatPlusDouble")
(simp "IH1")
(use "Truth")
;; 4
(assume "pos1" "IH1")
(cases) ;21-23
(ng #t)
(simp "PosSSucc")
(ng #t)
(use "Truth")
;; 22
(assume "pos2")
(ng #t)
(simp "NatPlusDouble")
(simp "IH1")
(use "Truth")
;; 23
(assume "pos2")
(ng #t)
(simp "PosSSucc")
(ng #t)
(simp "NatPlusDouble")
(simp "IH1")
(use "Truth")
;; Proof finished.
(save "PosToNatPlus")

;; NatToPosPlus
(set-goal "all nat1,nat2(Zero<nat1 -> Zero<nat2 ->
  NatToPos(nat1+nat2)=NatToPos nat1+NatToPos nat2)")
(assume "nat1" "nat2" "0<nat1" "0<nat2")
(assert "nat1+nat2=PosToNat(NatToPos nat1)+PosToNat(NatToPos nat2)")
 (simp "PosToNatToPosId")
 (simp "PosToNatToPosId")
 (use "Truth")
 (use "0<nat2")
 (use "0<nat1")
(assume "EqHyp")
(simp "EqHyp")
(simp "<-" "PosToNatPlus")
(simp "NatToPosToNatId")
(use "Truth")
;; Proof finished.
(save "NatToPosPlus")

;; Commutativity of + for pos
;; PosPlusComm
(set-goal "all pos1,pos2 pos1+pos2=pos2+pos1")
(assume "pos1" "pos2")
(assert "pos1+pos2=NatToPos(PosToNat(pos1+pos2))")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "EqHyp1")
(simp "EqHyp1")
(assert "pos2+pos1=NatToPos(PosToNat(pos2+pos1))")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "EqHyp2")
(simp "EqHyp2")
(assert "PosToNat(pos1+pos2)=PosToNat pos1+PosToNat pos2")
 (simp "PosToNatPlus")
 (use "Truth")
(assume "EqHyp3")
(simp "EqHyp3")
(simp "NatPlusComm")
(assert "PosToNat(pos2+pos1)=PosToNat pos2+PosToNat pos1")
 (simp "PosToNatPlus")
 (use "Truth")
(assume "EqHyp4")
(simp "EqHyp4")
(use "Truth")
;; Proof finished.
(save "PosPlusComm")

;; Associativity of + for pos
(set-goal "all pos1,pos2,pos3 pos1+(pos2+pos3)=pos1+pos2+pos3")
(assume "pos1" "pos2" "pos3")
(assert "pos1+(pos2+pos3)=NatToPos(PosToNat(pos1+(pos2+pos3)))")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "EqHyp1")
(simp "EqHyp1")
(assert "PosToNat(pos1+(pos2+pos3))=PosToNat(pos1)+PosToNat(pos2+pos3)")
 (simp "PosToNatPlus")
 (use "Truth")
(assume "EqHyp2")
(simp "EqHyp2")
(assert "PosToNat(pos2+pos3)=PosToNat pos2+PosToNat pos3")
 (simp "PosToNatPlus")
 (use "Truth")
(assume "EqHyp3")
(simp "EqHyp3")
(assert "PosToNat pos1+(NatPlus(PosToNat pos2)(PosToNat pos3))=
         NatPlus(PosToNat pos1+PosToNat pos2)(PosToNat pos3)")
 (use "Truth")
(assume "EqHyp4")
(simp "EqHyp4")
(simp "<-" "PosToNatPlus")
(simp "<-" "PosToNatPlus")
(use "NatToPosToNatId")
;; Proof finished.
(save "PosPlusAssoc")
(add-rewrite-rule "pos1+(pos2+pos3)" "pos1+pos2+pos3")

;; The following (former) rules are not used any more, because they
;; increase the number of +'s.

;; (add-rewrite-rule "pos1+SZero pos2" "pos1+pos2+pos2")
;; (add-rewrite-rule "pos1+SOne pos2" "pos1+pos2+pos2+1")
;; (add-rewrite-rule "SZero pos1+pos2" "pos1+pos1+pos2") ;no term. for 2+m
;; (add-rewrite-rule "SOne pos1+pos2" "pos1+pos1+1+pos2"

;; (display-pconst "PosPlus")

;; Rules for PosMinus:  They give correct results for p--q (only) if q<p.

(add-computation-rules
 "One--pos" "One"
 "SZero pos--One" "PosPred(SZero pos)"
 "SZero pos1--SZero pos2" "SZero(pos1--pos2)"
 "SZero pos1--SOne pos2" "PosPred(SZero(pos1--pos2))"
 "SOne pos--One" "SZero pos"
 "SOne pos1--SZero pos2" "[if (pos1=pos2) One (SOne(pos1--pos2))]"
 "SOne pos1--SOne pos2" "SZero(pos1--pos2)")

;; (display-pconst "PosMinus")

;; (pp (nt (pt "7--4")))
;; (pp (nt (pt "6--4")))
;; (pp (nt (pt "66--44")))

;; PosMinusTotal
(set-goal (rename-variables (term-to-totality-formula (pt "PosMinus"))))
(assume "p^" "Tp")
(elim "Tp")

;; ?_3:allnc p^(TotalPos p^ -> TotalPos(1--p^))
(assume "q^" "Tq")
(elim "Tq")
(ng #t)
(use "TotalPosOne")

(assume "q^1" "Tq1" "Useless")
(ng #t)
(use "TotalPosOne")

(assume "q^1" "Tq1" "Useless")
(ng #t)
(use "TotalPosOne")

;; ?_4:allnc pos^(
;;      TotalPos pos^ ->
;;      allnc p^(TotalPos p^ -> TotalPos(pos^ --p^)) ->
;;      allnc p^(TotalPos p^ -> TotalPos(SZero pos^ --p^)))

(assume "q^" "Tq" "IHq" "q^1" "Tq1")
(elim "Tq1")
(ng #t)
(use "PosPredTotal")
(use "TotalPosSZero")
(use "Tq")

(assume "q^2" "Tq2" "Useless")
(ng #t)
(use "TotalPosSZero")
(use "IHq")
(use "Tq2")

(assume "q^2" "Tq2" "Useless")
(ng #t)
(use "PosPredTotal")
(use "TotalPosSZero")
(use "IHq")
(use "Tq2")

;; ?_5:allnc pos^(
;;      TotalPos pos^ ->
;;      allnc p^(TotalPos p^ -> TotalPos(pos^ --p^)) ->
;;      allnc p^(TotalPos p^ -> TotalPos(SOne pos^ --p^)))

(assume "q^" "Tq" "IHq" "q^1" "Tq1")
(elim "Tq1")
(ng #t)
(use "TotalPosSZero")
(use "Tq")

(assume "q^2" "Tq2" "Useless")
(ng #t)
(use "BooleIfTotal")
(use "PosEqTotal")
(use "Tq")
(use "Tq2")
(use "TotalPosOne")
(use "TotalPosSOne")
(use "IHq")
(use "Tq2")

(assume "q^2" "Tq2" "Useless")
(ng #t)
(use "TotalPosSZero")
(use "IHq")
(use "Tq2")
;; Proof finished.
(save "PosMinusTotal")

;; (display-pconst "PosPlus")
;; (display-pconst "PosMinus")
;; (display-idpc "TotalPosMR")

;; BooleIfTotalReal
(set-goal (rename-variables
	   (real-and-formula-to-mr-formula
	    (proof-to-extracted-term "BooleIfTotal")
	    (proof-to-formula boole-if-total-proof))))
(assume "boole^" "boole^0" "TMRb0b")
(ng #t)
(elim "TMRb0b")
(ng #t)
(assume "alpha^1" "alpha^2" "alpha^10" "TMRa10a1" "alpha^20" "Useless")
(use "TMRa10a1")
(ng #t)
(assume "alpha^1" "alpha^2" "alpha^10" "Useless" "alpha^20" "TMRa20a2")
(use  "TMRa20a2")
;; Proof finished.
(save "BooleIfTotalReal")

;; PosMinusTotalReal
(set-goal (rename-variables
	   (real-and-formula-to-mr-formula
	    (pt "PosMinus")
	    (proof-to-formula (theorem-name-to-proof "PosMinusTotal")))))
(assume "p^" "p^0" "TMRp0p")
(elim "TMRp0p")
(assume "q^" "q^0" "TMRq0q")
(elim "TMRq0q")
(use "TotalPosOneMR")
(assume "q^1" "q^10" "TMRq10q1" "IH")
(ng #t)
(use "TotalPosOneMR")
(assume "q^1" "q^10" "TMRq10q1" "IH")
(ng #t)

(use "TotalPosOneMR")
;; ?_4:allnc pos^,pos^0(
;;      TotalPosMR pos^0 pos^ -->
;;      allnc p^,p^0(TotalPosMR p^0 p^ --> TotalPosMR(pos^0--p^0)(pos^ --p^)) ->
;;      allnc p^,p^0(
;;       TotalPosMR p^0 p^ --> TotalPosMR(SZero pos^0--p^0)(SZero pos^ --p^)))
(assume "p^1" "p^10" "TMRp10p1" "IHp1" "q^" "q^0" "TMRq0q")
(elim "TMRq0q")
(ng #t)
(use "PosPredTotalReal")
(use "TotalPosSZeroMR")
(use "TMRp10p1")

(assume "q^1" "q^10" "TMRq10q1" "IHq1")
(ng #t)
(use "TotalPosSZeroMR")
(use "IHp1")
(use "TMRq10q1")

(assume "q^1" "q^10" "TMRq10q1" "IHq1")
(ng #t)
(use "PosPredTotalReal")
(use "TotalPosSZeroMR")
(use "IHp1")
(use "TMRq10q1")

;; ?_5:allnc pos^,pos^0(
;;      TotalPosMR pos^0 pos^ -->
;;      allnc p^,p^0(TotalPosMR p^0 p^ --> TotalPosMR(pos^0--p^0)(pos^ --p^)) ->
;;      allnc p^,p^0(
;;       TotalPosMR p^0 p^ --> TotalPosMR(SOne pos^0--p^0)(SOne pos^ --p^)))

(assume "p^1" "p^10" "TMRp10p1" "IHp1" "q^" "q^0" "TMRq0q")
(elim "TMRq0q")
(ng #t)
(use "TotalPosSZeroMR")
(use "TMRp10p1")

(assume "q^1" "q^10" "TMRq10q1" "IHq1")
(ng #t)
(use "BooleIfTotalReal")
(use "PosEqTotalReal")
(use "TMRp10p1")
(use "TMRq10q1")
(use "TotalPosOneMR")
(use "TotalPosSOneMR")
(use "IHp1")
(use "TMRq10q1")

(assume "q^1" "q^10" "TMRq10q1" "IHq1")
(ng #t)
(use "TotalPosSZeroMR")
(use "IHp1")
(use "TMRq10q1")
;; Proof finished.
(save "PosMinusTotalReal")

;; Rules for PosTimes:

(add-computation-rules
 "pos*One" "pos"
 "pos1*SZero pos2" "SZero(pos1*pos2)"
 "pos1*SOne pos2" "SZero(pos1*pos2)+pos1")

;; PosTimesTotal
(set-goal (rename-variables (term-to-totality-formula (pt "PosTimes"))))
(assume "p^" "Tp" "q^" "Tq")
(elim "Tq")

(ng #t)
(use "Tp")

(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "TotalPosSZero")
(use "IHq1")

(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "PosPlusTotal")
(use "TotalPosSZero")
(use "IHq1")
(use "Tp")
;; Proof finished.
(save "PosTimesTotal")

;; PosTimesTotalReal
(set-goal (rename-variables
	   (real-and-formula-to-mr-formula
	    (pt "PosTimes")
	    (proof-to-formula (theorem-name-to-proof "PosTimesTotal")))))
(assume "p^" "p^0" "TMRp0p" "q^" "q^0" "TMRq0q")
(elim "TMRq0q")
(use "TMRp0p")
(assume "q^1" "q^10" "Useless" "IHq1")
(ng #t)
(use "TotalPosSZeroMR")
(use "IHq1")
(assume "q^1" "q^10" "Useless" "IHq1")
(ng #t)
(use "PosPlusTotalReal")
(use "TotalPosSZeroMR")
(use "IHq1")
(use "TMRp0p")
;; Proof finished.
(save "PosTimesTotalReal")

(set-goal "all pos One*pos=pos")
(ind)
(auto)
;; Proof finished.
(add-rewrite-rule "One*pos" "pos")

(set-goal "all pos1,pos2 SZero pos1*pos2=SZero(pos1*pos2)")
(assume "pos1")
(ind)
(auto)
(assume "pos2" "IHone")
(ng)
(simp "IHone")
(use "Truth-Axiom")
;; Proof finished.
(add-rewrite-rule "SZero pos1*pos2" "SZero(pos1*pos2)")

;; We prove that NatToPos is an isomorphism w.r.t. *

;; NatDoublePlus
(set-goal "all nat1,nat2 NatDouble(nat1+nat2)=NatDouble nat1+NatDouble nat2")
(assume "nat1")
(ind)
(use "Truth")
(assume "nat2" "IH")
(ng #t)
(use "IH")
;; Proof finished.
(save "NatDoublePlus")

;; NatDoublePlusEq
(set-goal "all nat nat+nat=NatDouble nat")
(ind)
(use "Truth")
(assume "nat" "IH")
(ng #t)
(use "IH")
;; Proof finished.
(save "NatDoublePlusEq")

;; NatTimesDouble
(set-goal "all nat1,nat2 NatDouble nat1*NatDouble nat2=
                         NatDouble(NatDouble(nat1*nat2))")
(assume "nat1")
(ind)
(use "Truth")
(assume "nat2" "IH")
(ng #t)
(simp "IH")
(assert "NatDouble(nat1*nat2+nat1)=NatDouble(nat1*nat2)+NatDouble nat1")
 (use "NatDoublePlus")
(assume "EqHyp1")
(simp "EqHyp1")
(assert "NatDouble(NatDouble(nat1*nat2)+NatDouble nat1)=
         NatDouble(NatDouble(nat1*nat2))+NatDouble(NatDouble(nat1))")
 (use "NatDoublePlus")
(assume "EqHyp2")
(simp "EqHyp2")
(assert "NatDouble(NatDouble nat1)=NatDouble nat1+NatDouble nat1")
 (simp "NatDoublePlusEq")
 (use "Truth")
(assume "EqHyp3")
(simp "EqHyp3")
(use "Truth")
;; Proof finished.
(save "NatTimesDouble")

;; NatDoubleTimes2
(set-goal "all nat1,nat2 NatDouble(nat1*nat2)=nat1*NatDouble nat2")
(assume "nat1")
(ind)
(use "Truth")
(assume "nat2" "IH")
(ng #t)
(simp "NatDoublePlus")
(simp "IH")
(assert "NatDouble nat1=nat1+nat1")
 (simp "NatDoublePlusEq")
 (use "Truth")
(assume "EqHyp1")
(simp "EqHyp1")
(use "Truth")
;; Proof finished.
(save "NatDoubleTimes2")

;; PosToNatTimes
(set-goal "all pos1,pos2 PosToNat(pos1*pos2)=PosToNat pos1*PosToNat pos2")
(assume "pos1")
(ind) ;3-5
(ng #t)
(use "Truth")
;; 4
(assume "pos2" "IH")
(ng #t)
(simp "IH")
(simp "NatDoubleTimes2")
(use "Truth")
;; 5
(assume "pos2" "IH")
(ng #t)
(simp "PosToNatPlus")
(ng #t)
(simp "IH")
(simp "NatDoubleTimes2")
(use "Truth")
;; Proof finished.
(save "PosToNatTimes")

;; NatToPosTimes
(set-goal "all nat1,nat2(Zero<nat1 -> Zero<nat2 ->
  NatToPos(nat1*nat2)=NatToPos nat1*NatToPos nat2)")
(assume "nat1" "nat2" "0<nat1" "0<nat2")
(assert "nat1*nat2=PosToNat(NatToPos nat1)*PosToNat(NatToPos nat2)")
 (simp "PosToNatToPosId")
 (simp "PosToNatToPosId")
 (use "Truth")
 (use "0<nat2")
 (use "0<nat1")
(assume "EqHyp")
(simp "EqHyp")
(simp "<-" "PosToNatTimes")
(simp "NatToPosToNatId")
(use "Truth")
;; Proof finished.
(save "NatToPosTimes")

;; Commutativity of * for pos
;; PosTimesComm
(set-goal "all pos1,pos2 pos1*pos2=pos2*pos1")
(assume "pos1" "pos2")
(assert "pos1*pos2=NatToPos(PosToNat(pos1*pos2))")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "EqHyp1")
(simp "EqHyp1")
(assert "pos2*pos1=NatToPos(PosToNat(pos2*pos1))")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "EqHyp2")
(simp "EqHyp2")
(assert "PosToNat(pos1*pos2)=PosToNat pos1*PosToNat pos2")
 (simp "PosToNatTimes")
 (use "Truth")
(assume "EqHyp3")
(simp "EqHyp3")
(simp "NatTimesComm")
(assert "PosToNat(pos2*pos1)=PosToNat pos2*PosToNat pos1")
 (simp "PosToNatTimes")
 (use "Truth")
(assume "EqHyp4")
(simp "EqHyp4")
(use "Truth")
;; Proof finished.
(save "PosTimesComm")

;; Associativity of * for pos
(set-goal "all pos1,pos2,pos3 pos1*(pos2*pos3)=pos1*pos2*pos3")
(assume "pos1" "pos2" "pos3")
(assert "pos1*(pos2*pos3)=NatToPos(PosToNat(pos1*(pos2*pos3)))")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "EqHyp1")
(simp "EqHyp1")
(assert "PosToNat(pos1*(pos2*pos3))=PosToNat(pos1)*PosToNat(pos2*pos3)")
 (simp "PosToNatTimes")
 (use "Truth")
(assume "EqHyp2")
(simp "EqHyp2")
(assert "PosToNat(pos2*pos3)=PosToNat pos2*PosToNat pos3")
 (simp "PosToNatTimes")
 (use "Truth")
(assume "EqHyp3")
(simp "EqHyp3")
(assert "PosToNat pos1*(NatTimes(PosToNat pos2)(PosToNat pos3))=
         NatTimes(PosToNat pos1*PosToNat pos2)(PosToNat pos3)")
 (use "Truth")
(assume "EqHyp4")
(simp "EqHyp4")
(simp "<-" "PosToNatTimes")
(simp "<-" "PosToNatTimes")
(use "NatToPosToNatId")
;; Proof finished.
(save "PosTimesAssoc")
(add-rewrite-rule "pos1*(pos2*pos3)" "pos1*pos2*pos3")

(set-goal "all pos1,pos2 SOne pos1*pos2=SZero(pos1*pos2)+pos2")
(assume "pos1")
(ind)
(ng #t)
(use "Truth")
;; 4
(assume "pos2" "IH")
(ng #t)
(use "IH")
;; 5
(assume "pos2" "IH")
(ng #t)
(simp "IH")
(assert "SZero(pos1*pos2)+pos2+pos1=SZero(pos1*pos2)+(pos2+pos1)")
 (use "Truth")
(assume "EqHyp1")
(simp "EqHyp1")
(assert "SZero(pos1*pos2)+pos1+pos2=SZero(pos1*pos2)+(pos1+pos2)")
 (use "Truth")
(assume "EqHyp2")
(simp "EqHyp2")
(assert "pos1+pos2=pos2+pos1")
 (use "PosPlusComm")
(assume "pos1+pos2=pos2+pos1")
(simp "pos1+pos2=pos2+pos1")
(use "Truth")
;; Proof finished.
(save "PosTimesSOne")
(add-rewrite-rule "SOne pos1*pos2" "SZero(pos1*pos2)+pos2")

;; Rules for PosExp : pos=>nat=>pos

(add-computation-rules
 "pos**Zero" "One"
 "pos1**Succ nat2" "pos1**nat2*pos1")

;; PosExpTotal
(set-goal (rename-variables (term-to-totality-formula (pt "PosExp"))))
(assume "p^" "Tp" "n^" "Tn")
(elim "Tn")

(ng #t)
(use "TotalPosOne")

(assume "n^1" "Tn1" "IHn1")
(ng #t)
(use "PosTimesTotal")
(use "IHn1")
(use "Tp")
;; Proof finished.
(save "PosExpTotal")

;; PosExpOne
(set-goal "all n 1**n=1")
(ind)
(use "Truth")
(assume "n" "IH")
(ng #t)
(use "IH")
;; Proof finished.
(save "PosExpOne")
(add-rewrite-rules "1**n" "1")

;; Rules for PosLt, PosLe

(add-computation-rules
 "pos<One" "False"
 "One<SZero pos" "True"
 "One<SOne pos" "True"
 "SZero pos1<SZero pos2" "pos1<pos2"
 "SZero pos1<SOne pos2" "pos1<=pos2"
 "SOne pos1<SZero pos2" "pos1<pos2"
 "SOne pos1<SOne pos2" "pos1<pos2")

(add-computation-rules
 "One<=pos" "True"
 "SZero pos<=One" "False"
 "SOne pos<=One" "False"
 "SZero pos1<=SZero pos2" "pos1<=pos2"
 "SZero pos1<=SOne pos2" "pos1<=pos2"
 "SOne pos1<=SZero pos2" "pos1<pos2"
 "SOne pos1<=SOne pos2" "pos1<=pos2")

;; PosLtPosLeTotalLemma
(set-goal "allnc p^(TotalPos p^ -> allnc q^(TotalPos q^ ->
 TotalBoole(p^ <q^) andd TotalBoole(p^ <=q^)))")
(assume "p^" "Tp")
(elim "Tp")

(assume "q^" "Tq")
(split)
(elim "Tq")
(use "TotalBooleFalse")

(assume "q^1" "Tq1" "Useless")
(ng #t)
(use "TotalBooleTrue")

(assume "q^1" "Tq1" "Useless")
(ng #t)
(use "TotalBooleTrue")

(ng #t)
(use "TotalBooleTrue")

;; ?_4:allnc pos^(
;;      TotalPos pos^ ->
;;      allnc q^(
;;       TotalPos q^ -> TotalBoole(pos^ <q^) andd TotalBoole(pos^ <=q^)) ->
;;      allnc q^(
;;       TotalPos q^ ->
;;       TotalBoole(SZero pos^ <q^) andd TotalBoole(SZero pos^ <=q^)))

(assume "p^1" "Tp1" "IHp1" "q^" "Tq")
(elim "Tq")

(split)
(ng #t)
(use "TotalBooleFalse")
(ng #t)
(use "TotalBooleFalse")

(assume "q^1" "Tq1" "Useless")
(inst-with-to "IHp1" (pt "q^1") "Tq1" "AndHyp")
(drop "IHp1")
(split)
(ng #t)
(elim "AndHyp")
(assume "Hyp1" "Hyp2")
(use "Hyp1")

(ng #t)
(elim "AndHyp")
(assume "Hyp1" "Hyp2")
(use "Hyp2")

(assume "q^1" "Tq1" "Useless")
(ng #t)
(inst-with-to "IHp1" (pt "q^1") "Tq1" "AndHyp")
(drop "IHp1")
(split)
(elim "AndHyp")
(assume "Hyp1" "Hyp2")
(use "Hyp2")
(elim "AndHyp")
(assume "Hyp1" "Hyp2")
(use "Hyp2")

;; ?_5:allnc pos^(
;;      TotalPos pos^ ->
;;      allnc q^(
;;       TotalPos q^ -> TotalBoole(pos^ <q^) andd TotalBoole(pos^ <=q^)) ->
;;      allnc q^(
;;       TotalPos q^ ->
;;       TotalBoole(SOne pos^ <q^) andd TotalBoole(SOne pos^ <=q^)))

(assume "p^1" "Tp1" "IHp1" "q^" "Tq")
(elim "Tq")

(split)
(ng #t)
(use "TotalBooleFalse")
(ng #t)
(use "TotalBooleFalse")

(assume "q^1" "Tq1" "Useless")
(inst-with-to "IHp1" (pt "q^1") "Tq1" "AndHyp")
(drop "IHp1")
(split)
(ng #t)
(elim "AndHyp")
(assume "Hyp1" "Hyp2")
(use "Hyp1")

(ng #t)
(elim "AndHyp")
(assume "Hyp1" "Hyp2")
(use "Hyp1")

(assume "q^1" "Tq1" "Useless")
(ng #t)
(use "IHp1")
(use "Tq1")
;; Proof finished.
(save "PosLtPosLeTotalLemma")

;; PosLtTotal
(set-goal (rename-variables (term-to-totality-formula (pt "PosLt"))))
(assume "p^" "Tp" "q^" "Tq")
(assert "TotalBoole(p^ <q^) andd TotalBoole(p^ <=q^)")
(use "PosLtPosLeTotalLemma")
(use "Tp")
(use "Tq")
(assume "AndHyp")
(elim "AndHyp")
(assume "Hyp1" "Hyp2")
(use "Hyp1")
;; Proof finished.
(save "PosLtTotal")

;; PosLeTotal
(set-goal (rename-variables (term-to-totality-formula (pt "PosLe"))))
(assume "p^" "Tp" "q^" "Tq")
(assert "TotalBoole(p^ <q^) andd TotalBoole(p^ <=q^)")
(use "PosLtPosLeTotalLemma")
(use "Tp")
(use "Tq")
(assume "AndHyp")
(elim "AndHyp")
(assume "Hyp1" "Hyp2")
(use "Hyp2")
;; Proof finished.
(save "PosLeTotal")

;; PosLtPosLeTotalRealLemma
(set-goal "allnc p^,p^0(
 TotalPosMR p^0 p^ -->
 allnc q^,q^0(
  TotalPosMR q^0 q^ -->
  TotalBooleMR(p^0<q^0)(p^ <q^) andu TotalBooleMR(p^0<=q^0)(p^ <=q^)))")
(assume "p^" "p^0" "TMRp0p")
(elim "TMRp0p")
(assume "q^" "q^0" "TMRq0q")
(elim "TMRq0q")
(split)
(use "TotalBooleFalseMR")
(use "TotalBooleTrueMR")
(assume "q^1" "q^10" "TMRq10q1" "IHq1")
(split)
(use "TotalBooleTrueMR")
(use "TotalBooleTrueMR")
(assume "q^1" "q^10" "TMRq10q1" "IHq1")
(split)
(use "TotalBooleTrueMR")
(use "TotalBooleTrueMR")

(assume "p^1" "p^10" "TMRp10p1" "IHp1" "q^" "q^0" "TMRq0q")
(elim "TMRq0q")
(split)
(use "TotalBooleFalseMR")
(use "TotalBooleFalseMR")
(assume "q^1" "q^10" "TMRq10q1" "IHq1")
(ng #t)
(use "IHp1")
(use "TMRq10q1")
(assume "q^1" "q^10" "TMRq10q1" "IHq1")
(ng #t)
(split)
(use "IHp1")
(use "TMRq10q1")
(use "IHp1")
(use "TMRq10q1")

;; ?_5:allnc pos^,pos^0(
;;      TotalPosMR pos^0 pos^ -->
;;      allnc q^,q^0(
;;       TotalPosMR q^0 q^ -->
;;       TotalBooleMR(pos^0<q^0)(pos^ <q^) andu
;;       TotalBooleMR(pos^0<=q^0)(pos^ <=q^)) ->
;;      allnc q^,q^0(
;;       TotalPosMR q^0 q^ -->
;;       TotalBooleMR(SOne pos^0<q^0)(SOne pos^ <q^) andu
;;       TotalBooleMR(SOne pos^0<=q^0)(SOne pos^ <=q^)))
(assume "p^1" "p^10" "TMRp10p1" "IHp1" "q^" "q^0" "TMRq0q")
(elim "TMRq0q")
(split)
(use "TotalBooleFalseMR")
(use "TotalBooleFalseMR")
(assume "q^1" "q^10" "TMRq10q1" "IHq1")
(ng #t)
(split)
(use "IHp1")
(use "TMRq10q1")
(use "IHp1")
(use "TMRq10q1")
(assume "q^1" "q^10" "TMRq10q1" "IHq1")
(ng #t)
(use "IHp1")
(use "TMRq10q1")
;; Proof finished.
(save "PosLtPosLeTotalRealLemma")

;; (display-pconst "PosLt")
;; (display-pconst "PosLe")

;; PosLtTotalReal
(set-goal (rename-variables
	   (real-and-formula-to-mr-formula
	    (pt "PosLt")
	    (proof-to-formula (theorem-name-to-proof "PosLtTotal")))))
(assume "p^" "p^0" "TMRp0p" "q^" "q^0" "TMRq0q")
(use "PosLtPosLeTotalRealLemma")
(use "TMRp0p")
(use "TMRq0q")
;; Proof finished.
(save "PosLtTotalReal")

;; PosLeTotalReal
(set-goal (rename-variables
	   (real-and-formula-to-mr-formula
	    (pt "PosLe")
	    (proof-to-formula (theorem-name-to-proof "PosLeTotal")))))
(assume "p^" "p^0" "TMRp0p" "q^" "q^0" "TMRq0q")
(use "PosLtPosLeTotalRealLemma")
(use "TMRp0p")
(use "TMRq0q")
;; Proof finished.
(save "PosLeTotalReal")

;; PosLtToLe
(set-goal "all pos1,pos2(pos1<pos2 -> pos1<=pos2)")
(ind)
(ng #t)
(strip)
(use "Truth")
(assume "pos1" "IH1")
(cases)
(ng #t)
(assume "Absurd")
(use "Absurd")
(assume "pos2")
(ng #t)
(use "IH1")
(assume "pos2")
(ng #t)
(assume "pos1<=pos1")
(use "pos1<=pos1")
;; 4
(assume "pos1" "IH1")
(cases)
(ng #t)
(assume "Absurd")
(use "Absurd")
(assume "pos2")
(ng #t)
(assume "pos1<pos1")
(use "pos1<pos1")
(assume "pos2")
(ng #t)
(use "IH1")
;; Proof finished.
(save "PosLtToLe")

;; PosLTrans
(set-goal "all pos1,pos2,pos3((pos1<pos2 -> pos2<=pos3 -> pos1<pos3)
                             &(pos1<=pos2 -> pos2<pos3 -> pos1<pos3)
                             &(pos1<=pos2 -> pos2<=pos3 -> pos1<=pos3))")
(ind) ;2-4
(cases) ;5-7
(assume "pos3")
(ng #t)
(split)
(use "Efq")
(split)
(assume "Useless" "1<p3")
(use "1<p3")
(strip)
(use "Truth")
;; 6
(assume "pos2")
(ng #t)
(cases)
(ng #t)
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(strip)
(use "Truth")
(assume "pos3")
(ng #t)
(split)
(strip)
(use "Truth")
(split)
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "pos3")
(split)
(ng #t)
(strip)
(use "Truth")
(split)
(ng #t)
(strip)
(use "Truth")
(strip)
(use "Truth")
;; 7
(assume "pos2")
(cases)
(ng #t)
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(strip)
(use "Truth")
(assume "pos3")
(ng #t)
(split)
(strip)
(use "Truth")
(split)
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "pos3")
(ng #t)
(split)
(strip)
(use "Truth")
(split)
(strip)
(use "Truth")
(strip)
(use "Truth")
;; 3
(assume "pos1" "IH1")
(cases) ;79-81
(assume "pos2")
(ng #t)
(split)
(use "Efq")
(split)
(use "Efq")
(use "Efq")
;; 80
(assume "pos2")
(cases) ;89-91
(ng #t)
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(assume "Useless" "Absurd")
(use "Absurd")
;; 90
(assume "pos3")
(ng #t)
(split)
(use "IH1")
(split)
(use "IH1")
(use "IH1")
;; 91
(assume "pos3")
(ng #t)
(split)
(assume "p1<p2" "p2<=p3")
(use "PosLtToLe")
(use-with "IH1" (pt "pos2") (pt "pos3") 'left "p1<p2" "p2<=p3")
(split)
(use "IH1")
(use "IH1")
;; 81
(assume "pos2")
(cases) ;115-117
(ng #t)
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(assume "Useless" "Absurd")
(use "Absurd")
;; 116
(assume "pos3")
(ng #t)
(split)
(use "IH1")
(split)
(use "IH1")
(assume "p1<=p2" "p2<p3")
(use "PosLtToLe")
(use-with "IH1" (pt "pos2") (pt "pos3") 'right 'left "p1<=p2" "p2<p3")
;; 117
(assume "pos3")
(ng #t)
(split)
(use "IH1")
(split)
(assume "p1<=p2" "p2<p3")
(use "PosLtToLe")
(use-with "IH1" (pt "pos2") (pt "pos3") 'right 'left "p1<=p2" "p2<p3")
(use "IH1")
;; 4
(assume "pos1" "IH1")
(cases) ;143-145
(assume "pos2")
(ng #t)
(split)
(use "Efq")
(split)
(use "Efq")
(use "Efq")
;; 144
(assume "pos2")
(cases) ;153-155
(ng #t)
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(assume "Useless" "Absurd")
(use "Absurd")
;; 154
(assume "pos3")
(ng #t)
(split)
(use "IH1")
(split)
(assume "p1<p2" "p2<p3")
(use-with "IH1" (pt "pos2") (pt "pos3") 'left "p1<p2" "?")
(use "PosLtToLe")
(use "p2<p3")
(use "IH1")
;; 155
(assume "pos3")
(ng #t)
(split)
(use "IH1")
(split)
(use "IH1")
(assume "p1<p2" "p2<=p3")
(use "PosLtToLe")
(use-with "IH1" (pt "pos2") (pt "pos3") 'left "p1<p2" "p2<=p3")
;; 145
(assume "pos2")
(cases) ;182-184
(ng #t)
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(split)
(assume "Useless" "Absurd")
(use "Absurd")
(assume "Useless" "Absurd")
(use "Absurd")
;; 183
(assume "pos3")
(ng #t)
(split)
(assume "p1<p2" "p2<p3")
(use-with "IH1" (pt "pos2") (pt "pos3") 'left "p1<p2" "?")
(use "PosLtToLe")
(use "p2<p3")
(split)
(use "IH1")
(use "IH1")
;; 184
(assume "pos3")
(ng #t)
(split)
(use "IH1")
(split)
(use "IH1")
(use "IH1")
;; Proof finished.
(save "PosLTrans")

;; Using this and PosLtToLe we can easily derive PosLeLtTrans
;; PosLtLeTrans PosLeTrans PosLtTrans.

;; PosLtLeTrans
(set-goal "all pos1,pos2,pos3(pos1<pos2 -> pos2<=pos3 -> pos1<pos3)")
(assume "pos1" "pos2" "pos3")
(use "PosLTrans")
;; Proof finished.
(save "PosLtLeTrans")

;; PosLeLtTrans
(set-goal "all pos1,pos2,pos3(pos1<=pos2 -> pos2<pos3 -> pos1<pos3)")
(assume "pos1" "pos2" "pos3")
(use "PosLTrans")
;; Proof finished.
(save "PosLeLtTrans")

;; (remove-global-assumption "PosLeTrans")
;; PosLeTrans
(set-goal "all pos1,pos2,pos3(pos1<=pos2 -> pos2<=pos3 -> pos1<=pos3)")
(assume "pos1" "pos2" "pos3")
(use "PosLTrans")
;; Proof finished.
(save "PosLeTrans")

;; PosLtTrans
(set-goal "all pos1,pos2,pos3(pos1<pos2 -> pos2<pos3 -> pos1<pos3)")
(assume "pos1" "pos2" "pos3" "p1<p2")
(use "PosLeLtTrans")
(use "PosLtToLe")
(use "p1<p2")
;; Proof finished.
(save "PosLtTrans")

;; We add some useful rewrite rules.

(set-goal "all pos (pos<pos)=False")
(ind)
(use "Truth")
(assume "pos" "IH")
(use "IH")
(assume "pos" "IH")
(use "IH")
;; Proof finished.
(add-rewrite-rule "pos<pos" "False")

(set-goal "all pos pos<=pos")
(ind)
(use "Truth")
(assume "pos" "IH")
(use "IH")
(assume "pos" "IH")
(use "IH")
;; Proof finished.
(add-rewrite-rule "pos<=pos" "True")

(set-goal "all pos pos<PosS pos")
(ind)
(use "Truth")
(ng #t)
(strip)
(use "Truth")
;; 4
(assume "pos" "IH")
(ng #t)
(use "IH")
;; Proof finished.
(add-rewrite-rule "pos<PosS pos" "True")

(set-goal "all pos pos<=PosS pos")
(cases)
(use "Truth")
(ng #t)
(strip)
(use "Truth")
;; 4
(assume "pos")
(ng #t)
(use "Truth")
;; Proof finished.
(add-rewrite-rule "pos<=PosS pos" "True")

(set-goal "all pos (PosS pos<=pos)=False")
(ind)
(use "Truth")
(assume "pos" "IH")
(ng #t)
(use "Truth")
(assume "pos" "IH")
(ng #t)
(use "IH")
;; Proof finished.
(add-rewrite-rule "PosS pos<=pos" "False")

(set-goal "all pos (PosS pos<pos)=False")
(ind)
(use "Truth")
(assume "pos" "IH")
(ng #t)
(use "Truth")
(assume "pos" "IH")
(ng #t)
(use "Truth")
;; Proof finished.
(add-rewrite-rule "PosS pos<pos" "False")

(set-goal "all pos1,pos2 pos1<=pos1+pos2")
(ind)
(ind)
(use "Truth")
(assume "pos2" "IH2")
(ng #t)
(use "Truth")
(assume "pos2" "IH2")
(ng #t)
(use "Truth")
;; 3
(assume "pos1" "IH1")
(ind)
(ng #t)
(use "Truth")
(assume "pos2" "IH2")
(ng #t)
(use "IH1")
(assume "pos2" "IH2")
(ng #t)
(use "IH1")
;; 4
(assume "pos1" "IH1")
(ind)
(ng #t)
(use "Truth")
(assume "pos2" "IH2")
(ng #t)
(use "IH1")
(assume "pos2" "IH2")
(ng #t)
(use "PosLeLtTrans" (pt "pos1+pos2"))
(use "IH1")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "pos1<=pos1+pos2" "True")

(set-goal "all pos1,pos2 pos1<pos1+pos2")
(ind)
(ind)
(use "Truth")
(assume "pos2" "IH2")
(ng #t)
(use "Truth")
(assume "pos2" "IH2")
(ng #t)
(use "Truth")
;; 3
(assume "pos1" "IH1")
(ind)
(ng #t)
(use "Truth")
(assume "pos2" "IH2")
(ng #t)
(use "IH1")
(assume "pos2" "IH2")
(ng #t)
(use "Truth")
;; 4
(assume "pos1" "IH1")
(ind)
(ng #t)
(use "Truth")
(assume "pos2" "IH2")
(ng #t)
(use "IH1")
(assume "pos2" "IH2")
(ng #t)
(use "PosLtTrans" (pt "pos1+pos2"))
(use "IH1")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "pos1<pos1+pos2" "True")

(set-goal "all pos1,pos2 pos1<=pos2+pos1")
(assume "pos1" "pos2")
(simp "PosPlusComm")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "pos1<=pos2+pos1" "True")

(set-goal "all pos1,pos2 pos1<pos2+pos1")
(assume "pos1" "pos2")
(simp "PosPlusComm")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "pos1<pos2+pos1" "True")

(set-goal "all pos (PosS pos<=One)=False")
(assert "all pos(PosS pos<=One -> F)")
 (cases)
 (ng #t)
 (assume "Absurd")
 (use "Absurd")
 (ng #t)
 (assume "pos" "Absurd")
 (use "Absurd")
 (ng #t)
 (assume "pos" "Absurd")
 (use "Absurd")
;; Assertion proved.
(assume "Assertion" "pos")
(use "AtomFalse")
(use "Assertion")
;; Proof finished.
(add-rewrite-rule "PosS pos<=One" "False")

(set-goal "all pos1,pos2 (pos1+pos2<=pos1)=False")
(assert "all pos1,pos2(pos1+pos2<=pos1 -> F)")
 (ind) ;4-6
 (ng #t)
 (assume "pos1" "Absurd")
 (use "Absurd")
;; 5
 (assume "pos1" "IH1")
 (ind)
 (ng #t)
 (assume "Absurd")
 (use "Absurd")
 (assume "pos2" "IH2")
 (ng #t)
 (use "IH1")
 (assume "pos2" "IH2")
 (ng #t)
 (assume "p1+p2<p1")
 (use "IH1" (pt "pos2"))
 (use "PosLtToLe")
 (use "p1+p2<p1")
;; 6
 (assume "pos1" "IH1")
 (ind)
 (ng #t)
 (assume "Absurd")
 (use "Absurd")
 (assume "pos2" "IH2")
 (ng #t)
 (use "IH1")
 (assume "pos2" "IH2")
 (ng #t)
 (assume "S(p1+p2)<=p1")
 (use "IH1" (pt "pos2"))
 (use "PosLeTrans" (pt "PosS(pos1+pos2)"))
 (use "Truth")
 (use "S(p1+p2)<=p1")
;; Assertion proved.
(assume "Assertion" "pos1" "pos2")
(use "AtomFalse")
(use "Assertion")
;; Proof finished.
(add-rewrite-rule "pos1+pos2<=pos1" "False")

(set-goal "all pos1,pos2 (pos1+pos2<=pos2)=False")
(assume "pos1" "pos2")
(simp "PosPlusComm")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "pos1+pos2<=pos2" "False")

(set-goal "all pos1,pos2 (pos1+pos2<pos1)=False")
(assert "all pos1,pos2(pos1+pos2<pos1 -> F)")
 (ind) ;4-6
 (ng #t)
 (assume "pos1" "Absurd")
 (use "Absurd")
;; 5
 (assume "pos1" "IH1")
 (ind)
 (ng #t)
 (assume "Absurd")
 (use "Absurd")
 (assume "pos2" "IH2")
 (ng #t)
 (use "IH1")
 (assume "pos2" "IH2")
 (ng #t)
 (assume "p1+p2<p1")
 (use "IH1" (pt "pos2"))
 (use "p1+p2<p1")
;; 6
 (assume "pos1" "IH1")
 (ind)
 (ng #t)
 (assume "Absurd")
 (use "Absurd")
 (assume "pos2" "IH2")
 (ng #t)
 (use "IH1")
 (assume "pos2" "IH2")
 (ng #t)
 (assume "S(p1+p2)<=p1")
 (use "IH1" (pt "pos2"))
 (use "PosLtLeTrans" (pt "PosS(pos1+pos2)"))
 (use "Truth")
 (use "S(p1+p2)<=p1")
;; Assertion proved.
(assume "Assertion" "pos1" "pos2")
(use "AtomFalse")
(use "Assertion")
;; Proof finished.
(add-rewrite-rule "pos1+pos2<pos1" "False")

(set-goal "all pos1,pos2 (pos1+pos2<pos2)=False")
(assume "pos1" "pos2")
(simp "PosPlusComm")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "pos1+pos2<pos2" "False")

(set-goal "all pos One<PosS pos")
(ind)
(use "Truth")
(assume "pos" "IH")
(ng #t)
(use "Truth")
(assume "pos" "IH")
(ng #t)
(use "Truth")
;; Proof finished.
(add-rewrite-rule "One<PosS pos" "True")

;; PosLtPosS
(set-goal "all pos1,pos2 (pos1<PosS pos2)=(pos1<=pos2)")
(ind)
(cases)
(ng #t)
(use "Truth")
(assume "pos2")
(ng #t)
(use "Truth")
(assume "pos2")
(ng #t)
(use "Truth")
;; 3
(assume "pos1" "IH1")
(cases)
(ng #t)
(use "Truth")
(assume "pos2")
(ng #t)
(use "Truth")
(assume "pos2")
(ng #t)
(use "IH1")
;; 4
(assume "pos1" "IH1")
(cases)
(ng #t)
(use "Truth")
(assume "pos2")
(ng #t)
(use "Truth")
(assume "pos2")
(ng #t)
(use "IH1")
;; Proof finished
(save "PosLtPosS")

;; PosLePosS
(set-goal "all pos1,pos2 (PosS pos1<=pos2)=(pos1<pos2)")
(ind)
(cases)
(ng #t)
(use "Truth")
(assume "pos2")
(ng #t)
(use "Truth")
(assume "pos2")
(ng #t)
(use "Truth")
;; 3
(assume "pos1" "IH1")
(cases)
(ng #t)
(use "Truth")
(assume "pos2")
(ng #t)
(use "Truth")
(assume "pos2")
(ng #t)
(use "Truth")
;; 4
(assume "pos1" "IH1")
(cases)
(ng #t)
(use "Truth")
(assume "pos2")
(ng #t)
(use "IH1")
(assume "pos2")
(ng #t)
(use "IH1")
;; Proof finished.
(save "PosLePosS")

(set-goal "all pos1,pos2 (PosS pos1<PosS pos2)=(pos1<pos2)")
(ind)
(cases)
(ng #t)
(use "Truth")
(assume "pos2")
(ng #t)
(use "Truth")
(assume "pos2")
(ng #t)
(use "Truth")
;; 3
(assume "pos1" "IH1")
(cases)
(ng #t)
(use "Truth")
(assume "pos2")
(ng #t)
(use "Truth")
(assume "pos2")
(ng #t)
(use "PosLtPosS")
;; 4
(assume "pos1" "IH1")
(cases)
(ng #t)
(use "Truth")
(assume "pos2")
(ng #t)
(use "PosLePosS")
(assume "pos2")
(ng #t)
(use "IH1")
;; Proof finished.
(add-rewrite-rule "PosS pos1<PosS pos2" "pos1<pos2")

(set-goal "all pos1,pos2 (PosS pos1<=PosS pos2)=(pos1<=pos2)")
(ind)
(cases)
(ng #t)
(use "Truth")
(assume "pos2")
(ng #t)
(use "Truth")
(assume "pos2")
(ng #t)
(use "Truth")
;; 3
(assume "pos1" "IH1")
(cases)
(ng #t)
(use "Truth")
(assume "pos2")
(ng #t)
(use "Truth")
(assume "pos2")
(ng #t)
(use "PosLtPosS")
;; 4
(assume "pos1" "IH1")
(cases)
(ng #t)
(use "Truth")
(assume "pos2")
(ng #t)
(use "PosLePosS")
(assume "pos2")
(ng #t)
(use "IH1")
;; Proof finished.
(add-rewrite-rule "PosS pos1<=PosS pos2" "pos1<=pos2")

;; PosNotLeToLt and PosNotLtToLe should be best proved using the
;; isomorphic embedding PosToNat of pos into nat.

(add-global-assumption
 "PosNotLeToLt"
 "all pos1,pos2((pos1<=pos2 -> F) -> pos2<pos1)")

(add-global-assumption
 "PosNotLtToLe"
 "all pos1,pos2((pos1<pos2 -> F) -> pos2<=pos1)")

;; Code discarded 2014-01-08
;; ;; PosNotLtToLe
;; (set-goal "all pos1,pos2((pos1<pos2 -> F) -> pos2<=pos1)")
;; (assume "pos1" "pos2" "p1<p2 -> F")
;; (use "Stab-Atom")
;; (assume "p2<=p1 -> F")
;; (use "p1<p2 -> F")
;; (use "PosNotLeToLt")
;; (use "p2<=p1 -> F")
;; ;; Proof finished.
;; (save "PosNotLtToLe")

;; Rules for PosMax

(add-computation-rules
 "One max pos" "pos"
 "SZero pos max One" "SZero pos"
 "SZero pos1 max SZero pos2" "SZero(pos1 max pos2)"
 "SZero pos1 max SOne pos2" "[if (pos1<=pos2) (SOne pos2) (SZero pos1)]"
 "SOne pos max One" "SOne pos"
 "SOne pos1 max SZero pos2" "[if (pos2<=pos1) (SOne pos1) (SZero pos2)]"
 "SOne pos1 max SOne pos2" "SOne(pos1 max pos2)")

;; PosMaxTotal
(set-goal (rename-variables (term-to-totality-formula (pt "PosMax"))))
(assume "p^" "Tp")
(elim "Tp")
(ng #t)
(assume "q^" "Tq")
(use "Tq")

(assume "p^1" "Tp1" "IHp1" "q^" "Tq")
(elim "Tq")
(ng #t)
(use "TotalPosSZero")
(use "Tp1")
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "TotalPosSZero")
(use "IHp1")
(use "Tq1")
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "BooleIfTotal")
(use "PosLeTotal")
(use "Tp1")
(use "Tq1")
(use "TotalPosSOne")
(use "Tq1")
(use "TotalPosSZero")
(use "Tp1")

(assume "p^1" "Tp1" "IHp1" "q^" "Tq")
(elim "Tq")
(ng #t)
(use "TotalPosSOne")
(use "Tp1")
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "BooleIfTotal")
(use "PosLeTotal")
(use "Tq1")
(use "Tp1")
(use "TotalPosSOne")
(use "Tp1")
(use "TotalPosSZero")
(use "Tq1")
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "TotalPosSOne")
(use "IHp1")
(use "Tq1")
;; Proof finished.
(save "PosMaxTotal")

(set-goal "all pos pos max One=pos")
(cases)
(use "Truth")
(assume "pos")
(ng #t)
(use "Truth")
(assume "pos")
(ng #t)
(use "Truth")
;; Proof finished.
(add-rewrite-rule "pos max One" "pos")

(set-goal "all pos pos max pos=pos")
(ind)
(use "Truth")
(assume "pos" "IH")
(ng #t)
(use "IH")
(assume "pos" "IH")
(ng #t)
(use "IH")
;; Proof finished.
(add-rewrite-rule "pos max pos" "pos")

;; Rules for PosMin

(add-computation-rules
 "One min pos" "One"
 "SZero pos min One" "One"
 "SZero pos1 min SZero pos2" "SZero(pos1 min pos2)"
 "SZero pos1 min SOne pos2" "[if (pos1<=pos2) (SZero pos1) (SOne pos2)]"
 "SOne pos min One" "One"
 "SOne pos1 min SZero pos2" "[if (pos1<=pos2) (SZero pos2) (SOne pos1)]"
 "SOne pos1 min SOne pos2" "SOne(pos1 min pos2)")

;; PosMinTotal
(set-goal (rename-variables (term-to-totality-formula (pt "PosMin"))))
(assume "p^" "Tp")
(elim "Tp")
(ng #t)
(assume "q^" "Tq")
(use "TotalPosOne")

(assume "p^1" "Tp1" "IHp1" "q^" "Tq")
(elim "Tq")
(ng #t)
(use "TotalPosOne")
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "TotalPosSZero")
(use "IHp1")
(use "Tq1")
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "BooleIfTotal")
(use "PosLeTotal")
(use "Tp1")
(use "Tq1")
(use "TotalPosSZero")
(use "Tp1")
(use "TotalPosSOne")
(use "Tq1")

(assume "p^1" "Tp1" "IHp1" "q^" "Tq")
(elim "Tq")
(ng #t)
(use "TotalPosOne")
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "BooleIfTotal")
(use "PosLeTotal")
(use "Tp1")
(use "Tq1")
(use "TotalPosSZero")
(use "Tq1")
(use "TotalPosSOne")
(use "Tp1")
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "TotalPosSOne")
(use "IHp1")
(use "Tq1")
;; Proof finished.
(save "PosMinTotal")

;; Rules for NatExp : nat=>nat=>nat

(add-computation-rules
 "nat**Zero" "Succ Zero"
 "nat1**Succ nat2" "nat1**nat2*nat1")

;; NatExpTotal
(set-goal (rename-variables (term-to-totality-formula (pt "NatExp"))))
(assume "n^" "Tn" "m^" "Tm")
(elim "Tm")
(ng #t)
(use "TotalNatSucc")
(use "TotalNatZero")

(assume "m^1" "Tm1" "IHm1")
(ng #t)
(use "NatTimesTotal")
(use "IHm1")
(use "Tn")
;; Proof finished.
(save "NatExpTotal")

(set-goal "all pos,nat (PosToNat pos**nat)=PosToNat(pos**nat)")
(assume "pos")
(ind)
(ng #t)
(use "Truth")
(assume "nat" "IH")
(ng #t)
(simp "IH")
(simp "PosToNatTimes")
(use "Truth")
;; Proof finished.
(add-rewrite-rules
 "(PosToNat pos)**nat" "PosToNat(pos**nat)")

;; Now for the integers.

;; IntEqTotal
(set-goal "allnc i^(
 TotalInt i^ -> allnc j^(TotalInt j^ -> TotalBoole(i^ =j^)))")
(assume "i^" "Ti")
(elim "Ti") ;3-5
(assume "p^" "Tp" "j^" "Tj")
(elim "Tj") ;7-9
(assume "q^" "Tq")
(use "PosEqTotal")
(use "Tp")
(use "Tq")
;; 8
(ng #t)
(use "TotalBooleFalse")
;; 9
(ng #t)
(strip)
(use "TotalBooleFalse")
;; 4
(assume "j^" "Tj")
(elim "Tj")
(ng #t)
(strip)
(use "TotalBooleFalse")
(ng #t)
(use "TotalBooleTrue")
(ng #t)
(strip)
(use "TotalBooleFalse")
;; 5
(assume "p^" "Tp" "j^" "Tj")
(elim "Tj")
(ng #t)
(strip)
(use "TotalBooleFalse")
(ng #t)
(use "TotalBooleFalse")
(assume "q^" "Tq")
(ng #t)
(use "PosEqTotal")
(use "Tp")
(use "Tq")
;; Proof finished.
(save "IntEqTotal")

;; Rules for IntS, IntPred

(add-computation-rules
 "IntS IntZero" "IntP One"
 "IntS(IntP pos)" "IntP(PosS pos)"
 "IntS(IntN One)" "IntZero"
 "IntS(IntN(SZero pos))" "IntN(PosPred(SZero pos))"
 "IntS(IntN(SOne pos))" "IntN(SZero pos)")

;; IntSTotal
(set-goal (rename-variables (term-to-totality-formula (pt "IntS"))))
(assume "k^" "Tk")
(elim "Tk")

(assume "p^" "Tp")
(elim "Tp")
(ng #t)
(use "TotalIntIntPos")
(use "TotalPosSZero")
(use "TotalPosOne")

(assume "p^1" "Tp1" "Useless")
(ng #t)
(use "TotalIntIntPos")
(use "TotalPosSOne")
(use "Tp1")

(assume "p^1" "Tp1" "Useless")
(ng #t)
(use "TotalIntIntPos")
(use "TotalPosSZero")
(use "PosSTotal")
(use "Tp1")

(ng #t)
(use "TotalIntIntPos")
(use "TotalPosOne")

(assume "p^1" "Tp1")
(elim "Tp1")
(ng #t)
(use "TotalIntIntZero")

(assume "p^2" "Tp2" "Useless")
(ng #t)
(use "TotalIntIntNeg")
(use "PosPredTotal")
(use "TotalPosSZero")
(use "Tp2")

(assume "p^2" "Tp2" "Useless")
(ng #t)
(use "TotalIntIntNeg")
(use "TotalPosSZero")
(use "Tp2")
;; Proof finished.
(save "IntSTotal")

;; Using IntSTotal we can now prove the postponed NatToIntTotal.

(set-goal (rename-variables (term-to-totality-formula (pt "NatToInt"))))
(assume "n^" "Tn")
(elim "Tn")
;; ?_3:TotalInt Zero
(use "TotalIntIntZero")
;; ?_4:allnc nat^(TotalNat nat^ -> TotalInt nat^ -> TotalInt(Succ nat^))
(assume "m^" "Tm" "IH")
(ng #t)
;; ?_6:TotalInt(IntS m^)
(use "IntSTotal")
(use "IH")
;; Proof finished.
(save "NatToIntTotal")

(replace-item-in-algebra-edge-to-embed-term-alist
         "nat" "int"
	 (let ((var (make-var (make-alg "nat") -1 t-deg-one "")))
	   (make-term-in-abst-form
	    var (make-term-in-app-form
		 (make-term-in-const-form
		  (pconst-name-to-pconst "NatToInt"))
		 (make-term-in-var-form var)))))

;; (add-rewrite-rule "IntS(int+IntN One)" "int")
;; Postponed, since we do not yet have rules for IntPos

(add-computation-rules
 "IntPred IntZero" "IntN One"
 "IntPred(IntN pos)" "IntN(PosS pos)"
 "IntPred(IntP One)" "IntZero"
 "IntPred(IntP(SZero pos))" "IntP(PosPred(SZero pos))"
 "IntPred(IntP(SOne pos))" "IntP(SZero pos)")

;; IntPredTotal
(set-goal (rename-variables (term-to-totality-formula (pt "IntPred"))))
(assume "k^" "Tk")
(elim "Tk")

(assume "p^" "Tp")
(elim "Tp")
(ng #t)
(use "TotalIntIntZero")

(assume "p^1" "Tp1" "Useless")
(elim "Tp1")

(ng #t)
(use "TotalIntIntPos")
(use "TotalPosOne")

(assume "p^2" "Tp2" "Useless2")
(ng #t)
(use "TotalIntIntPos")
(use "TotalPosSOne")
(use "PosPredTotal")
(use "TotalPosSZero")
(use "Tp2")

(assume "p^2" "Tp2" "Useless2")
(ng #t)
(use "TotalIntIntPos")
(use "TotalPosSOne")
(use "TotalPosSZero")
(use "Tp2")

(assume "p^1" "Tp1" "Useless")
(ng #t)
(use "TotalIntIntPos")
(use "TotalPosSZero")
(use "Tp1")

(ng #t)
(use "TotalIntIntNeg")
(use "TotalPosOne")

(assume "p^1" "Tp1")
(ng #t)
(use "TotalIntIntNeg")
(use "PosSTotal")
(use "Tp1")
;; Proof finished.
(save "IntPredTotal")

;; Move up to PosPred
(set-goal "all pos PosPred(SZero(PosS pos))=SOne pos")
(ind)
(use "Truth")
(assume "pos" "IH")
(ng #t)
(use "Truth")
(assume "pos" "IH")
(ng #t)
(use "IH")
;; Proof finished.
(add-rewrite-rule "PosPred(SZero(PosS pos))" "SOne pos")

(set-goal "all pos IntPred(PosS pos)=pos")
(ind)
(ng #t)
(use "Truth")
(assume "pos" "IH")
(ng #t)
(use "Truth")
(assume "pos" "IH")
(ng #t)
(use "Truth")
;; Proof finished.
(add-rewrite-rule "IntPred(PosS pos)" "IntPos pos")

;; Move up to PosS
(set-goal "all pos PosS(PosPred(SZero pos))=SZero pos")
(ind)
(use "Truth")
(assume "pos" "IH")
(ng #t)
(use "IH")
(assume "pos" "IH")
(ng #t)
(use "Truth")
;; Proof finished.
(add-rewrite-rule "PosS(PosPred(SZero pos))" "SZero pos")

(set-goal "all int IntPred(IntS int)=int")
(ind)
(assume "pos")
(ng #t)
(use "Truth")
(use "Truth")
(cases)
(ng #t)
(use "Truth")
(assume "pos")
(ng #t)
(use "Truth")
(assume "pos")
(ng #t)
(use "Truth")
;; Proof finished.
(add-rewrite-rule "IntPred(IntS int)" "int")

(set-goal "all pos IntS(IntPred pos)=pos")
(ind)
(use "Truth")
(ng #t)
(strip)
(use "Truth")
(ng #t)
(strip)
(use "Truth")
;; Proof finished.
(add-rewrite-rule "IntS(IntPred pos)" "IntPos pos")

(set-goal "all int IntS(IntPred int)=int")
(ind)
(ng #t)
(strip)
(use "Truth")
(use "Truth")
(cases)
(use "Truth")
(assume "pos")
(ng #t)
(use "Truth")
(assume "pos")
(ng #t)
(use "Truth")
;; Proof finished.
(add-rewrite-rule "IntS(IntPred int)" "int")

;; Rules for IntPlus

(add-computation-rules
 "IntZero+int" "int"
 "IntP pos+IntZero" "IntP pos"
 "IntP pos1+IntP pos2" "IntP(pos1+pos2)"

 "IntP pos1+IntN pos2"
 "[if (pos1=pos2)
      IntZero
      [if (pos1<pos2) (IntN(pos2--pos1)) (IntP(pos1--pos2))]]"

 "IntN pos+IntZero" "IntN pos"

 "IntN pos1+IntP pos2"
 "[if (pos1=pos2)
      IntZero
      [if (pos1<pos2) (IntP(pos2--pos1)) (IntN(pos1--pos2))]]"

 "IntN pos1+IntN pos2" "IntN(pos1+pos2)")

;; IntPlusTotal
(set-goal (rename-variables (term-to-totality-formula (pt "IntPlus"))))
(assume "k^" "Tk" "l^" "Tl")
(elim "Tk")

;; ?_3:allnc pos^(TotalPos pos^ -> TotalInt(pos^ +l^))
(assume "p^" "Tp")
(elim "Tl")

(assume "q^" "Tq")
(use "TotalIntIntPos")
(use "PosPlusTotal")
(use "Tp")
(use "Tq")

(ng #t)
(use "TotalIntIntPos")
(use "Tp")

(assume "q^" "Tq")
(ng #t)
(use "BooleIfTotal")
(use "PosEqTotal")
(use "Tp")
(use "Tq")

(use "TotalIntIntZero")

(use "BooleIfTotal")
(use "PosLtTotal")
(use "Tp")
(use "Tq")

(use "TotalIntIntNeg")
(use "PosMinusTotal")
(use "Tq")
(use "Tp")

(use "TotalIntIntPos")
(use "PosMinusTotal")
(use "Tp")
(use "Tq")

;; ?_4:TotalInt(0+l^)
(ng #t)
(use "Tl")

;; ?_5:allnc pos^(TotalPos pos^ -> TotalInt(IntN pos^ +l^))
(assume "p^" "Tp")
(elim "Tl")

(assume "q^" "Tq")
(ng #t)
(use "BooleIfTotal")
(use "PosEqTotal")
(use "Tp")
(use "Tq")

(use "TotalIntIntZero")

(use "BooleIfTotal")
(use "PosLtTotal")
(use "Tp")
(use "Tq")

(use "TotalIntIntPos")
(use "PosMinusTotal")
(use "Tq")
(use "Tp")

(use "TotalIntIntNeg")
(use "PosMinusTotal")
(use "Tp")
(use "Tq")

(ng #t)
(use "TotalIntIntNeg")
(use "Tp")

(assume "q^" "Tq")
(ng #t)
(use "TotalIntIntNeg")
(use "PosPlusTotal")
(use "Tp")
(use "Tq")
;; Proof finished.
(save "IntPlusTotal")

;; IntPlusTotalReal
(set-goal (rename-variables
	   (real-and-formula-to-mr-formula
	    (pt "IntPlus")
	    (proof-to-formula (theorem-name-to-proof "IntPlusTotal")))))
(assume "k^" "k^0" "TMRk0k" "l^" "l^0" "TMRl0l")
(elim "TMRk0k")

;; ?_3:allnc pos^,pos^0(
;;      TotalPosMR pos^0 pos^ --> TotalIntMR(pos^0+l^0)(pos^ +l^))
(assume "p^" "p^0" "TMRp0p")
(elim "TMRl0l")

;; ?_7:allnc pos^,pos^0(
;;      TotalPosMR pos^0 pos^ --> TotalIntMR(p^0+pos^0)(p^ +pos^))
(assume "q^1" "q^10" "TMRq10q1")
(use "TotalIntIntPosMR")
(use "PosPlusTotalReal")
(use "TMRp0p")
(use "TMRq10q1")

;; ?_8:TotalIntMR(p^0+0)(p^ +0)
(ng #t)
(use "TotalIntIntPosMR")
(use "TMRp0p")

;; ?_9:allnc pos^,pos^0(
;;      TotalPosMR pos^0 pos^ --> TotalIntMR(p^0+IntN pos^0)(p^ +IntN pos^))
(assume "q^1" "q^10" "TMRq10q1")
(ng #t)
;; ?_17:TotalIntMR
;;      [if (p^0=q^10) 0 [if (p^0<q^10) (IntN(q^10--p^0)) (p^0--q^10)]]
;;      [if (p^ =q^1) 0 [if (p^ <q^1) (IntN(q^1--p^)) (p^ --q^1)]]
(use "BooleIfTotalReal")
(use "PosEqTotalReal")
(use "TMRp0p")
(use "TMRq10q1")
(use "TotalIntIntZeroMR")
;; ?_20:TotalIntMR[if (p^0<q^10) (IntN(q^10--p^0)) (p^0--q^10)]
;;      [if (p^ <q^1) (IntN(q^1--p^)) (p^ --q^1)]
(use "BooleIfTotalReal")
(use "PosLtTotalReal")
(use "TMRp0p")
(use "TMRq10q1")
(use "TotalIntIntNegMR")
(use "PosMinusTotalReal")
(use "TMRq10q1")
(use "TMRp0p")
(use "TotalIntIntPosMR")
(use "PosMinusTotalReal")
(use "TMRp0p")
(use "TMRq10q1")

;; ?_4:TotalIntMR(0+l^0)(0+l^)
(ng #t)
(use "TMRl0l")

;; ?_5:allnc pos^,pos^0(
;;      TotalPosMR pos^0 pos^ --> TotalIntMR(IntN pos^0+l^0)(IntN pos^ +l^))
(assume "p^" "p^0" "TMRp0p")
(elim "TMRl0l")

;; ?_36:allnc pos^,pos^0(
;;       TotalPosMR pos^0 pos^ --> TotalIntMR(IntN p^0+pos^0)(IntN p^ +pos^))
(assume "q^1" "q^10" "TMRq10q1")
(ng #t)
(use "BooleIfTotalReal")
(use "PosEqTotalReal")
(use "TMRp0p")
(use "TMRq10q1")
(use "TotalIntIntZeroMR")
;; ?_43:TotalIntMR[if (p^0<q^10) (q^10--p^0) (IntN(p^0--q^10))]
;;      [if (p^ <q^1) (q^1--p^) (IntN(p^ --q^1))]
(use "BooleIfTotalReal")
(use "PosLtTotalReal")
(use "TMRp0p")
(use "TMRq10q1")
(use "TotalIntIntPosMR")
(use "PosMinusTotalReal")
(use "TMRq10q1")
(use "TMRp0p")
(use "TotalIntIntNegMR")
(use "PosMinusTotalReal")
(use "TMRp0p")
(use "TMRq10q1")

;; ?_37:TotalIntMR(IntN p^0+0)(IntN p^ +0)
(ng #t)
(use "TotalIntIntNegMR")
(use "TMRp0p")

;; ?_38:allnc pos^,pos^0(
;;       TotalPosMR pos^0 pos^ -->
;;       TotalIntMR(IntN p^0+IntN pos^0)(IntN p^ +IntN pos^))
(assume "q^1" "q^10" "TMRq10q1")
(ng #t)
(use "TotalIntIntNegMR")
(use "PosPlusTotalReal")
(use "TMRp0p")
(use "TMRq10q1")
;; Proof finished.
(save "IntPlusTotalReal")

(set-goal "all int int+IntZero=int")
(cases)
(ng #t)
(assume "pos")
(use "Truth")
(use "Truth")
(assume "pos")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "int+IntZero" "int")

;; SZeroPosPlus
(set-goal "all pos SZero pos=pos+pos")
(ind)
(use "Truth")
(assume "pos" "IH")
(ng #t)
(use "IH")
(assume "pos" "IH")
(ng #t)
(simp "<-" "IH")
(ng #t)
(use "Truth")
;; Proof finished.
(save "SZeroPosPlus")

;; PosPlusIntPlus
(set-goal "all pos1,pos2 pos1+pos2=IntPlus pos1 pos2")
(assume "pos1" "pos2")
(use "Truth")
;; Proof finished.
(save "PosPlusIntPlus")

;; Commutativity and associativity of + for int require many case
;; distinctions and hence are very tedious.  Postponed.

;; ;; Commutativity of + for int
;; ;; IntPlusComm
;; (set-goal "all int1,int2 int1+int2=int2+int1")
;; (cases) ;2-4
;; (ind) ;5-7
;; (cases) ;8-10
;; (ng #t)
;; (assume "pos")
;; (use "Truth")
;; ;; 9
;; (use "Truth")
;; (cases) ;13-15
;; (ng #t)
;; (use "Truth")
;; (ind)
;; (ng #t)
;; (strip)
;; (use "Truth")
;; (ng #t)
;; (strip)
;; (use "Truth")
;; (ng #t)
;; (strip)
;; (use "Truth")
;; (ng #t)
;; (strip)
;; (use "Truth")
;; ;; 6
;; (ind) ;28-30
;; (assume  "IH")
;; (cases) ;32-34
;; (ind) ;35-37
;; (use "Truth")
;; (ng #t)
;; (strip)
;; (use "Truth")
;; (ng #t)
;; (strip)
;; (use "Truth")
;; ;; 33
;; (use "Truth")
;; ;; 34
;; (ind) ;42-44
;; (use "Truth")
;; (ng #t)
;; (assume "pos" "IHpos")
;; (cases (pt "One=pos"))
;; (assume "1=p")
;; (simp "<-" "1=p")
;; (ng #t)
;; (use "Truth")
;; (assume "1=p -> F")
;; (ng #t)
;; (cases (pt "pos"))
;; (ng #t)
;; (assume "p=1")
;; (use "1=p -> F")
;; (simp "p=1")
;; (use "Truth")
;; (assume "pos1" "p=SZero p1")
;; (ng #t)
;; (use "Truth")
;; (assume "pos1" "p=SOne p1")
;; (ng #t)
;; (use "Truth")
;; ;; 44
;; (ng #t)
;; (strip)
;; (use "Truth")
;; ;; 29
;; (assume "pos" "IHpos" "IH")
;; (cases)
;; (ng #t)
;; (use "PosPlusComm")
;; (use "Truth")
;; (ind)
;; (ng #t)
;; (use "Truth")
;; (assume "pos1" "IHpos1")
;; (ng #t)
;; (cases (pt "SZero pos=pos1"))
;; (assume "SZero pos=pos1")
;; (ng #t)
;; (simp "SZero pos=pos1")
;; (use "Truth")
;; (assume "SZero pos=pos1 -> F")
;; (ng #t)
;; (cases (pt "pos1"))
;; (assume "p1=1")
;; (ng #t)
;; (use "Truth")
;; (assume "pos2" "p1=SZero p2")
;; (ng #t)
;; (cases (pt "pos<pos2"))
;; (assume "pos<pos2")
;; (ng #t)
;; (assert "pos2=pos -> F")
;;  (assume "pos2=pos")
;;  (simphyp-with-to "pos<pos2" "pos2=pos" "Absurd")
;;  (use "Absurd")
;; (assume "pos2=pos -> F")
;; (simp "pos2=pos -> F")
;; (ng #t)
;; (assert "pos2<pos -> F")
;;  (assume "pos2<pos")
;;  (assert "pos<pos")
;;   (use "PosLtTrans" (pt "pos2"))
;;   (use "pos<pos2")
;;   (use "pos2<pos")
;;  (assume "pos<pos")
;;  (use "pos<pos")
;; (assume "pos2<pos -> F")
;; (simp "pos2<pos -> F")
;; (ng #t)
;; (use "Truth")
;; (assume "pos<pos2 -> F")
;; (ng #t)
;; (assert "pos2=pos -> F")
;;  (assume "pos2=pos")
;;  (use "SZero pos=pos1 -> F")
;;  (simp "p1=SZero p2")
;;  (simp "pos2=pos")
;;  (use "Truth")
;; (assume "pos2=pos -> F")
;; (simp "pos2=pos -> F")
;; (ng #t)
;; (assert "pos2<pos")
;; ;;   int5308  p5312  p5328  pos  IHpos:
;; ;;     all int0 pos+int0=int0+pos -> all int0 SZero pos+int0=int0+SZero pos
;; ;;   IH:all int0 SZero pos+int0=int0+SZero pos
;; ;;   int5368  p5397  pos1  IHpos1:
;; ;;     SZero(SZero pos)+IntN pos1=IntN pos1+SZero(SZero pos)
;; ;;   SZero pos=pos1 -> F:SZero pos=pos1 -> F
;; ;;   pos2  p1=SZero p2:pos1=SZero pos2
;; ;;   pos<pos2 -> F:pos<pos2 -> F
;; ;;   pos2=pos -> F:pos2=pos -> F
;; ;; -----------------------------------------------------------------------------
;; ;; ?_127:pos2<pos
;; ;; Here we would need PosLtLeCases.  Postponed.

;; ;; Intplusassoc
;; (set-goal "all int1,int2,int3 int1+(int2+int3)=int1+int2+int3")
;; (ind)
;; (assume "pos1")
;; (ind)
;; (assume "pos2")
;; (ind)
;; (assume "pos3")
;; (ng #t)
;; (use "Truth")
;; (ng #t)
;; (use "Truth")
;; (assume "pos3")
;; (ng #t)
;; (cases (pt "pos2=pos3"))
;; (ng #t)
;; (assume "pos2=pos3")
;; (simp "pos2=pos3")
;; (ng #t)
;; (cases (pt "pos1+pos3=pos3"))
;; ;; stuck

;; The following rewrite rules still need to be proved; postponed.
;; They require many case distinctions.

;; Added 2007-02-12
(add-rewrite-rule "i+One" "IntS i")
(add-rewrite-rule "i+IntP(SZero pos)" "i+IntP pos+IntP pos")
(add-rewrite-rule "i+IntP(SOne pos)" "IntS(i+IntP(SZero pos))")
(add-rewrite-rule "i+IntN(SZero pos)" "i+IntN pos+IntN pos")
(add-rewrite-rule "i+IntN(SOne pos)" "IntPred(i+IntN(SZero pos))")

(add-rewrite-rule "One+i" "IntS i")
(add-rewrite-rule "IntP(SZero pos)+i" "i+IntP pos+IntP pos")
(add-rewrite-rule "IntP(SOne pos)+i" "IntS(i+IntP(SZero pos))")
(add-rewrite-rule "IntN(SZero pos)+i" "i+IntN pos+IntN pos")
(add-rewrite-rule "IntN(SOne pos)+i" "IntPred(i+IntN(SZero pos))")

;; Added 2007-02-13
(add-rewrite-rule "i1+(i2+i3)" "i1+i2+i3")
(add-rewrite-rule "IntS i+j" "IntS(i+j)")
(add-rewrite-rule "i+IntS j" "IntS(i+j)")

;; We prove PosToNatToInt : NatToInt(PosToNat pos)=IntP pos and some
;; auxiliary propositions.

;; NatToIntDouble
(set-goal "all nat NatToInt(NatDouble nat)=NatToInt nat + NatToInt nat")
(ind)
(ng #t)
(use "Truth")
(assume "nat" "IH")
(ng #t)
(simp "IH")
(use "Truth")
;; Proof finished.
(save "NatToIntDouble")

;; IntPSZero
(set-goal "all pos IntP(SZero pos)=IntP pos + IntP pos")
(ind)
(use "Truth")
(assume "pos" "IH")
(ng #t)
(use "IH")
;; 4
(assume "pos" "IH")
(ng #t)
(simp "<-" "IH")
(ng #t)
(use "Truth")
;; Proof finished.
(save "IntPSZero")

;; IntPSOne
(set-goal "all pos IntP(SOne pos)=IntS(IntP pos + IntP pos)")
(ind)
(use "Truth")
(assume "pos" "IH")
(ng #t)
(use "IntPSZero")
;; 4
(assume "pos" "IH")
(ng #t)
(simp "<-" "IH")
(use "Truth")
;; Proof finished.
(save "IntPSOne")

;; PosToNatToInt
(set-goal "all pos NatToInt(PosToNat pos)=IntP pos")
(ind)
(use "Truth")
(assume "pos" "IH")
(ng #t)
(simp "NatToIntDouble")
(simp "IntPSZero")
(simp "IH")
(use "Truth")
;; 4
(assume "pos" "IH")
(ng #t)
(simp "NatToIntDouble")
(simp "IntPSOne")
(simp "IH")
(use "Truth")
;; Proof finished.
(save "PosToNatToInt")

;; Rules for IntMinus

(add-computation-rules
 "i-IntZero" "i"

 "IntP pos1-IntP pos2"
 "[if (pos1=pos2)
      IntZero
      [if (pos1<pos2) (IntN(pos2--pos1)) (IntP(pos1--pos2))]]"

 "IntP pos1-IntN pos2" "IntP(pos1+pos2)"
 "IntN pos1-IntP pos2" "IntN(pos1+pos2)"

 "IntN pos1-IntN pos2"
 "[if (pos1=pos2)
      IntZero
      [if (pos1<pos2) (IntP(pos2--pos1)) (IntN(pos1--pos2))]]"

 "IntZero-IntN pos" "IntP pos"
 "IntZero-IntP pos" "IntN pos")

;; IntMinusTotal
(set-goal (rename-variables (term-to-totality-formula (pt "IntMinus"))))
(assume "k^" "Tk" "l^" "Tl")
(elim "Tk")

;; ?_3:allnc pos^(TotalPos pos^ -> TotalInt(pos^ -l^))
(assume "p^" "Tp")
(elim "Tl")

;; ?_7:allnc pos^(TotalPos pos^ -> TotalInt(p^ -pos^))

(assume "q^" "Tq")
(ng #t)
(use "BooleIfTotal")
(use "PosEqTotal")
(use "Tp")
(use "Tq")

(use "TotalIntIntZero")

(use "BooleIfTotal")
(use "PosLtTotal")
(use "Tp")
(use "Tq")

(use "TotalIntIntNeg")
(use "PosMinusTotal")
(use "Tq")
(use "Tp")

(use "TotalIntIntPos")
(use "PosMinusTotal")
(use "Tp")
(use "Tq")

;; ?_8:TotalInt(p^ -0)
(ng #t)
(use "TotalIntIntPos")
(use "Tp")

;; ?_9:allnc pos^(TotalPos pos^ -> TotalInt(p^ -IntN pos^))

(assume "q^" "Tq")
(ng #t)
(use "TotalIntIntPos")
(use "PosPlusTotal")
(use "Tp")
(use "Tq")

;; ?_4:TotalInt(0-l^)
(elim "Tl")

(assume "p^" "Tp")
(ng #t)
(use "TotalIntIntNeg")
(use "Tp")

(ng #t)
(use "TotalIntIntZero")

(assume "p^" "Tp")
(ng #t)
(use "TotalIntIntPos")
(use "Tp")

;; ?_5:allnc pos^(TotalPos pos^ -> TotalInt(IntN pos^ -l^))
(assume "p^" "Tp")
(elim "Tl")

;; ?_46:allnc pos^(TotalPos pos^ -> TotalInt(IntN p^ -pos^))

(assume "q^" "Tq")
(ng #t)
(use "TotalIntIntNeg")
(use "PosPlusTotal")
(use "Tp")
(use "Tq")

;; ?_47:TotalInt(IntN p^ -0)

(ng #t)
(use "TotalIntIntNeg")
(use "Tp")

(assume "q^" "Tq")
(ng #t)
(use "BooleIfTotal")
(use "PosEqTotal")
(use "Tp")
(use "Tq")

(use "TotalIntIntZero")

(use "BooleIfTotal")
(use "PosLtTotal")
(use "Tp")
(use "Tq")

(use "TotalIntIntPos")
(use "PosMinusTotal")
(use "Tq")
(use "Tp")

(use "TotalIntIntNeg")
(use "PosMinusTotal")
(use "Tp")
(use "Tq")
;; Proof finished.
(save "IntMinusTotal")

;; IntMinusTotalReal
(set-goal (rename-variables
	   (real-and-formula-to-mr-formula
	    (pt "IntMinus")
	    (proof-to-formula (theorem-name-to-proof "IntMinusTotal")))))
(assume "k^" "k^0" "TMRk0k" "l^" "l^0" "TMRl0l")
(elim "TMRk0k")

;; ?_3:allnc pos^,pos^0(
;;      TotalPosMR pos^0 pos^ --> TotalIntMR(pos^0-l^0)(pos^ -l^))
(assume "p^" "p^0" "TMRp0p")
(elim "TMRl0l")

;; ?_7:allnc pos^,pos^0(
;;      TotalPosMR pos^0 pos^ --> TotalIntMR(p^0-pos^0)(p^ -pos^))
(assume "q^1" "q^10" "TMRq10q1")
(ng #t)
;; ?_11:TotalIntMR
;;      [if (p^0=q^10) 0 [if (p^0<q^10) (IntN(q^10--p^0)) (p^0--q^10)]]
;;      [if (p^ =q^1) 0 [if (p^ <q^1) (IntN(q^1--p^)) (p^ --q^1)]]
(use "BooleIfTotalReal")
(use "PosEqTotalReal")
(use "TMRp0p")
(use "TMRq10q1")
(use "TotalIntIntZeroMR")
(use "BooleIfTotalReal")
(use "PosLtTotalReal")
(use "TMRp0p")
(use "TMRq10q1")
(use "TotalIntIntNegMR")
(use "PosMinusTotalReal")
(use "TMRq10q1")
(use "TMRp0p")
(use "TotalIntIntPosMR")
(use "PosMinusTotalReal")
(use "TMRp0p")
(use "TMRq10q1")

;; ?_8:TotalIntMR(p^0-0)(p^ -0)
(ng #t)
(use "TotalIntIntPosMR")
(use "TMRp0p")

;; ?_9:allnc pos^,pos^0(
;;      TotalPosMR pos^0 pos^ --> TotalIntMR(p^0-IntN pos^0)(p^ -IntN pos^))
(assume "q^1" "q^10" "TMRq10q1")
(ng #t)
(use "TotalIntIntPosMR")
(use "PosPlusTotalReal")
(use "TMRp0p")
(use "TMRq10q1")

;; ?_4:TotalIntMR(0-l^0)(0-l^)
(elim "TMRl0l")
(assume "q^1" "q^10" "TMRq10q1")
(ng #t)
(use "TotalIntIntNegMR")
(use "TMRq10q1")
(use "TotalIntIntZeroMR")
(assume "q^1" "q^10" "TMRq10q1")
(ng #t)
(use "TotalIntIntPosMR")
(use "TMRq10q1")

;; ?_5:allnc pos^,pos^0(
;;      TotalPosMR pos^0 pos^ --> TotalIntMR(IntN pos^0-l^0)(IntN pos^ -l^))
(assume "p^" "p^0" "TMRp0p")
(elim "TMRl0l")

;; ?_45:allnc pos^,pos^0(
;;       TotalPosMR pos^0 pos^ --> TotalIntMR(IntN p^0-pos^0)(IntN p^ -pos^))
(assume "q^1" "q^10" "TMRq10q1")
(ng #t)
(use "TotalIntIntNegMR")
(use "PosPlusTotalReal")
(use "TMRp0p")
(use "TMRq10q1")

;; ?_46:TotalIntMR(IntN p^0-0)(IntN p^ -0)
(ng #t)
(use "TotalIntIntNegMR")
(use "TMRp0p")

;; ?_47:allnc pos^,pos^0(
;;       TotalPosMR pos^0 pos^ -->
;;       TotalIntMR(IntN p^0-IntN pos^0)(IntN p^ -IntN pos^))
(assume "q^1" "q^10" "TMRq10q1")
(ng #t)
;; ?_56:TotalIntMR
;;      [if (p^0=q^10) 0 [if (p^0<q^10) (q^10--p^0) (IntN(p^0--q^10))]]
;;      [if (p^ =q^1) 0 [if (p^ <q^1) (q^1--p^) (IntN(p^ --q^1))]]
(use "BooleIfTotalReal")
(use "PosEqTotalReal")
(use "TMRp0p")
(use "TMRq10q1")
(use "TotalIntIntZeroMR")
(use "BooleIfTotalReal")
(use "PosLtTotalReal")
(use "TMRp0p")
(use "TMRq10q1")
(use "TotalIntIntPosMR")
(use "PosMinusTotalReal")
(use "TMRq10q1")
(use "TMRp0p")
(use "TotalIntIntNegMR")
(use "PosMinusTotalReal")
(use "TMRp0p")
(use "TMRq10q1")
;; Proof finished.
(save "IntMinusTotalReal")

;; Rules for IntTimes

(add-computation-rules
 "IntZero*i" "IntZero"
 "IntP pos*IntZero" "IntZero"
 "IntP pos1*IntP pos2" "IntP(pos1*pos2)"
 "IntP pos1*IntN pos2" "IntN(pos1*pos2)"
 "IntN pos*IntZero" "IntZero"
 "IntN pos1*IntP pos2" "IntN(pos1*pos2)"
 "IntN pos1*IntN pos2" "IntP(pos1*pos2)")

;; IntTimesTotal
(set-goal (rename-variables (term-to-totality-formula (pt "IntTimes"))))
(assume "k^" "Tk" "l^" "Tl")
(elim "Tk")

;; ?_3:allnc pos^(TotalPos pos^ -> TotalInt(pos^ *l^))
(elim "Tl")

(assume "p^" "Tp" "q^" "Tq")
(use "TotalIntIntPos")
(use "PosTimesTotal")
(use "Tq")
(use "Tp")

(assume "p^" "Tp")
(ng #t)
(use "TotalIntIntZero")

(assume "p^" "Tp" "q^" "Tq")
(use "TotalIntIntNeg")
(use "PosTimesTotal")
(use "Tq")
(use "Tp")

(ng #t)
(use "TotalIntIntZero")

;; ?_5:allnc pos^(TotalPos pos^ -> TotalInt(IntN pos^ *l^))
(elim "Tl")

(assume "p^" "Tp" "q^" "Tq")
(use "TotalIntIntNeg")
(use "PosTimesTotal")
(use "Tq")
(use "Tp")

(assume "p^" "Tp")
(ng #t)
(use "TotalIntIntZero")

(assume "p^" "Tp" "q^" "Tq")
(use "TotalIntIntPos")
(use "PosTimesTotal")
(use "Tq")
(use "Tp")
;; Proof finished.
(save "IntTimesTotal")

;; IntTimesTotalReal
(set-goal (rename-variables
	   (real-and-formula-to-mr-formula
	    (pt "IntTimes")
	    (proof-to-formula (theorem-name-to-proof "IntTimesTotal")))))
(assume "k^" "k^0" "TMRk0k" "l^" "l^0" "TMRl0l")
(elim "TMRk0k")

;; ?_3:allnc pos^,pos^0(
;;      TotalPosMR pos^0 pos^ --> TotalIntMR(pos^0*l^0)(pos^ *l^))
(assume "p^" "p^0" "TMRp0p")
(elim "TMRl0l")

;; ?_7:allnc pos^,pos^0(
;;      TotalPosMR pos^0 pos^ --> TotalIntMR(p^0*pos^0)(p^ *pos^))
(assume "q^1" "q^10" "TMRq10q1")
(use "TotalIntIntPosMR")
(use "PosTimesTotalReal")
(use "TMRp0p")
(use "TMRq10q1")

;; ?_8:TotalIntMR(p^0*0)(p^ *0)
(ng #t)
(use "TotalIntIntZeroMR")

;; ?_9:allnc pos^,pos^0(
;;      TotalPosMR pos^0 pos^ --> TotalIntMR(p^0*IntN pos^0)(p^ *IntN pos^))
(assume "q^1" "q^10" "TMRq10q1")
(ng #t)
(use "TotalIntIntNegMR")
(use "PosTimesTotalReal")
(use "TMRp0p")
(use "TMRq10q1")

;; ?_4:TotalIntMR(0*l^0)(0*l^)
(ng #t)
(use "TotalIntIntZeroMR")

;; ?_5:allnc pos^,pos^0(
;;      TotalPosMR pos^0 pos^ --> TotalIntMR(IntN pos^0*l^0)(IntN pos^ *l^))
(assume "p^" "p^0" "TMRp0p")
(elim "TMRl0l")

;; ?_22:allnc pos^,pos^0(
;;       TotalPosMR pos^0 pos^ --> TotalIntMR(IntN p^0*pos^0)(IntN p^ *pos^))
(assume "q^1" "q^10" "TMRq10q1")
(use "TotalIntIntNegMR")
(use "PosTimesTotalReal")
(use "TMRp0p")
(use "TMRq10q1")

;; ?_23:TotalIntMR(IntN p^0*0)(IntN p^ *0)
(ng #t)
(use "TotalIntIntZeroMR")

;; ?_24:allnc pos^,pos^0(
;;       TotalPosMR pos^0 pos^ -->
;;       TotalIntMR(IntN p^0*IntN pos^0)(IntN p^ *IntN pos^))
(assume "q^1" "q^10" "TMRq10q1")
(ng #t)
(use "TotalIntIntPosMR")
(use "PosTimesTotalReal")
(use "TMRp0p")
(use "TMRq10q1")
;; Proof finished.
(save "IntTimesTotalReal")

;; The following rewrite rules should be proved.

(add-rewrite-rule "i*IntZero" "IntZero")
(add-rewrite-rule "i*IntP One" "i")
(add-rewrite-rule "IntP One*i" "i")
(add-rewrite-rule "int1*(int2*int3)" "int1*int2*int3")

;; (pp (nt (pt "i+0")))
;; So for integers we can use 0.  But beware:
;; (pp (pf "i**0"))       ;i**0
;; (pp (pf "i**IntZero")) ;i**IntZero

;; Rules for IntAbs

(add-computation-rules
 "abs IntZero" "Zero"
 "abs IntP pos" "PosToNat pos"
 "abs IntN pos" "PosToNat pos")

;; IntAbsTotal
(set-goal (rename-variables (term-to-totality-formula (pt "IntAbs"))))
(assume "k^" "Tk")
(elim "Tk")

(assume "p^" "Tp")
(use "PosToNatTotal")
(use "Tp")

(ng #t)
(use "TotalNatZero")

(assume "p^" "Tp")
(use "PosToNatTotal")
(use "Tp")
;; Proof finished.
(save "IntAbsTotal")

;; Rules for IntExp : int=>nat=>int

(add-computation-rules
 "int**Zero" "IntP One"
 "int1**Succ nat2" "int1**nat2*int1")

;; IntExpTotal
(set-goal (rename-variables (term-to-totality-formula (pt "IntExp"))))
(assume "k^" "Tk" "n^" "Tn")
(elim "Tn")
(ng #t)
(use "TotalIntIntPos")
(use "TotalPosOne")
(assume "n^1" "Tn1" "IHn1")
(ng #t)
(use "IntTimesTotal")
(use "IHn1")
(use "Tk")
;; Proof finished.
(save "IntExpTotal")

;; Strategy: do computations at the lowest possible level.  Raise outside.

;; We may assume that the given term is an original; otherwise use
;; term-to-original first.  If it is say a sum, take the original of
;; both components.  Let alg be the lub of their types.  If it is below
;; the type of the given term, do the addition at level alg already
;; (after embedding both components into alg via algebras-to-embedding)
;; and then embed the result into the type of the given term.

(add-rewrite-rule "(IntP pos1)**nat2" "IntP(pos1**nat2)")

;; Rules for IntMax

(add-computation-rules
 "IntZero max IntZero" "IntZero"
 "IntZero max IntP pos" "IntP pos"
 "IntZero max IntN pos" "IntZero"
 "IntP pos max IntZero" "IntP pos"
 "IntP pos1 max IntP pos2" "IntP(pos1 max pos2)"
 "IntP pos1 max IntN pos2" "IntP pos1"
 "IntN pos max IntZero" "IntZero"
 "IntN pos1 max IntP pos2" "IntP pos2"
 "IntN pos1 max IntN pos2" "IntN(pos1 min pos2)")

;; IntMaxTotal
(set-goal (rename-variables (term-to-totality-formula (pt "IntMax"))))
(assume "k^" "Tk")
(elim "Tk") ;3-5
(assume "p^" "Tp")
(elim "Tp") ;7-9
(assume "l^" "Tl")
(elim "Tl") ;11-13
(assume "q^" "Tq")
(ng #t)
(use "TotalIntIntPos")
(use "Tq")
;; 12
(ng #t)
(use "TotalIntIntPos")
(use "TotalPosOne")
;; 13
(assume "q^" "Tq")
(ng #t)
(use "TotalIntIntPos")
(use "TotalPosOne")
;; 8
(assume "p^1" "Tp1" "IHp1" "l^" "Tl")
(elim "Tl") ;23-25
(assume "q^" "Tq")
(elim "Tq") ;27-29
(ng #t)
(use "TotalIntIntPos")
(use "TotalPosSZero")
(use "Tp1")
;; 28
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "TotalIntIntPos")
(use "TotalPosSZero")
(use "PosMaxTotal")
(use "Tp1")
(use "Tq1")
;; 29
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "TotalIntIntPos")
(use "BooleIfTotal")
(use "PosLeTotal")
(use "Tp1")
(use "Tq1")
(use "TotalPosSOne")
(use "Tq1")
(use "TotalPosSZero")
(use "Tp1")
;; 24
(ng #t)
(use "TotalIntIntPos")
(use "TotalPosSZero")
(use "Tp1")
;; 25
(assume "q^1" "Tq1")
(ng #t)
(use "TotalIntIntPos")
(use "TotalPosSZero")
(use "Tp1")

;; ?_9:allnc pos^(
;;      TotalPos pos^ ->
;;      allnc k^(TotalInt k^ -> TotalInt(pos^ max k^)) ->
;;      allnc k^(TotalInt k^ -> TotalInt(SOne pos^ max k^)))

(assume "p^1" "Tp1" "IHp1" "l^" "Tl")
(elim "Tl") ;57-59
(assume "q^" "Tq")
(elim "Tq") ;61-63
(ng #t)
(use "TotalIntIntPos")
(use "TotalPosSOne")
(use "Tp1")
;; 62
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "TotalIntIntPos")
(use "BooleIfTotal")
(use "PosLeTotal")
(use "Tq1")
(use "Tp1")
(use "TotalPosSOne")
(use "Tp1")
(use "TotalPosSZero")
(use "Tq1")
;; 63
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "TotalIntIntPos")
(use "TotalPosSOne")
(use "PosMaxTotal")
(use "Tp1")
(use "Tq1")
;; 58
(ng #t)
(use "TotalIntIntPos")
(use "TotalPosSOne")
(use "Tp1")
;; 59
(assume "q^" "Tq")
(ng #t)
(use "TotalIntIntPos")
(use "TotalPosSOne")
(use "Tp1")

;; ?_4:allnc k^(TotalInt k^ -> TotalInt(0 max k^))
(assume "l^" "Tl")
(elim "Tl")
(assume "q^" "Tq")
(ng #t)
(use "TotalIntIntPos")
(use "Tq")
(ng #t)
(use "TotalIntIntZero")
(assume "q^" "Tq")
(ng #t)
(use "TotalIntIntZero")

;; 5
(assume "p^" "Tp")
(elim "Tp") ;101-103
(assume "l^" "Tl")
(elim "Tl") ;105-107
(assume "q^" "Tq")
(ng #t)
(use "TotalIntIntPos")
(use "Tq")
;; 106
(ng #t)
(use "TotalIntIntZero")
;; 107
(assume "q^" "Tq")
(ng #t)
(use "TotalIntIntNeg")
(use "TotalPosOne")
;; 102
(assume "p^1" "Tp1" "IHp1" "l^" "Tl")
(elim "Tl") ;116-118
(assume "q^" "Tq")
(elim "Tq") ;120-122
(ng #t)
(use "TotalIntIntPos")
(use "TotalPosOne")
;; 121
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "TotalIntIntPos")
(use "TotalPosSZero")
(use "Tq1")
;; 122
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "TotalIntIntPos")
(use "TotalPosSOne")
(use "Tq1")
;; 117
(ng #t)
(use "TotalIntIntZero")
;; 118
(assume "q^1" "Tq1")
(ng #t)
(use "TotalIntIntNeg")
(use "PosMinTotal")
(use "TotalPosSZero")
(use "Tp1")
(use "Tq1")

;; ?_103:allnc pos^(
;;        TotalPos pos^ ->
;;        allnc k^(TotalInt k^ -> TotalInt(IntN pos^ max k^)) ->
;;        allnc k^(TotalInt k^ -> TotalInt(IntN(SOne pos^)max k^)))

(assume "p^1" "Tp1" "IHp1" "l^" "Tl")
(elim "Tl") ;141-143
(assume "q^" "Tq")
(elim "Tq") ;145-147
(ng #t)
(use "TotalIntIntPos")
(use "TotalPosOne")
;; 146
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "TotalIntIntPos")
(use "TotalPosSZero")
(use "Tq1")
;; 147
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "TotalIntIntPos")
(use "TotalPosSOne")
(use "Tq1")
;; 142
(ng #t)
(use "TotalIntIntZero")
;; 143
(assume "q^" "Tq")
(ng #t)
(use "TotalIntIntNeg")
(use "PosMinTotal")
(use "TotalPosSOne")
(use "Tp1")
(use "Tq")
;; Proof finished.
(save "IntMaxTotal")

;; Rules for IntMin

(add-computation-rules
 "IntZero min IntZero" "IntZero"
 "IntZero min IntP pos" "IntZero"
 "IntZero min IntN pos" "IntN pos"
 "IntP pos min IntZero" "IntZero"
 "IntP pos1 min IntP pos2" "IntP(pos1 min pos2)"
 "IntP pos1 min IntN pos2" "IntN pos2"
 "IntN pos min IntZero" "IntN pos"
 "IntN pos1 min IntP pos2" "IntN pos1"
 "IntN pos1 min IntN pos2" "IntN(pos1 max pos2)")

;; IntMinTotal
(set-goal (rename-variables (term-to-totality-formula (pt "IntMin"))))
(assume "k^" "Tk")
(elim "Tk") ;3-5
(assume "p^" "Tp")
(elim "Tp") ;7-9
(assume "l^" "Tl")
(elim "Tl") ;11-13
(assume "q^" "Tq")
(ng #t)
(use "TotalIntIntPos")
(use "TotalPosOne")
;; 12
(ng #t)
(use "TotalIntIntZero")
;; 13
(assume "q^" "Tq")
(ng #t)
(use "TotalIntIntNeg")
(use "Tq")
;; 8
(assume "p^1" "Tp1" "IHp1" "l^" "Tl")
(elim "Tl") ;22-24
(assume "q^" "Tq")
(elim "Tq") ;26-28
(ng #t)
(use "TotalIntIntPos")
(use "TotalPosOne")
;; 27
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "TotalIntIntPos")
(use "TotalPosSZero")
(use "PosMinTotal")
(use "Tp1")
(use "Tq1")
;; 28
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "TotalIntIntPos")
(use "BooleIfTotal")
(use "PosLeTotal")
(use "Tp1")
(use "Tq1")
(use "TotalPosSZero")
(use "Tp1")
(use "TotalPosSOne")
(use "Tq1")
;; 23
(ng #t)
(use "TotalIntIntZero")
;; 24
(assume "q^1" "Tq1")
(ng #t)
(use "TotalIntIntNeg")
(use "Tq1")

;; ?_9:allnc pos^(
;;      TotalPos pos^ ->
;;      allnc k^(TotalInt k^ -> TotalInt(pos^ min k^)) ->
;;      allnc k^(TotalInt k^ -> TotalInt(SOne pos^ min k^)))

(assume "p^1" "Tp1" "IHp1" "l^" "Tl")
(elim "Tl") ;52-54
(assume "q^" "Tq")
(elim "Tq") ;56-58
(ng #t)
(use "TotalIntIntPos")
(use "TotalPosOne")
;; 57
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "TotalIntIntPos")
(use "BooleIfTotal")
(use "PosLeTotal")
(use "Tp1")
(use "Tq1")
(use "TotalPosSZero")
(use "Tq1")
(use "TotalPosSOne")
(use "Tp1")
;; 58
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "TotalIntIntPos")
(use "TotalPosSOne")
(use "PosMinTotal")
(use "Tp1")
(use "Tq1")
;; 53
(ng #t)
(use "TotalIntIntZero")
;; 54
(assume "q^" "Tq")
(ng #t)
(use "TotalIntIntNeg")
(use "Tq")

;; ?_4:allnc k^(TotalInt k^ -> TotalInt(0 min k^))
(assume "l^" "Tl")
(elim "Tl")
(assume "q^" "Tq")
(ng #t)
(use "TotalIntIntZero")
(ng #t)
(use "TotalIntIntZero")
(assume "q^" "Tq")
(ng #t)
(use "TotalIntIntNeg")
(use "Tq")

;; 5
(assume "p^" "Tp")
(elim "Tp") ;92-94
(assume "l^" "Tl")
(elim "Tl") ;96-98
(assume "q^" "Tq")
(ng #t)
(use "TotalIntIntNeg")
(use "TotalPosOne")
;; 97
(ng #t)
(use "TotalIntIntNeg")
(use "TotalPosOne")
;; 98
(assume "q^" "Tq")
(ng #t)
(use "TotalIntIntNeg")
(use "Tq")
;; 93
(assume "p^1" "Tp1" "IHp1" "l^" "Tl")
(elim "Tl") ;108-110
(assume "q^" "Tq")
(elim "Tq") ;112-114
(ng #t)
(use "TotalIntIntNeg")
(use "TotalPosSZero")
(use "Tp1")
;; 113
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "TotalIntIntNeg")
(use "TotalPosSZero")
(use "Tp1")
;; 114
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "TotalIntIntNeg")
(use "TotalPosSZero")
(use "Tp1")
;; 109
(ng #t)
(use "TotalIntIntNeg")
(use "TotalPosSZero")
(use "Tp1")
;; 110
(assume "q^1" "Tq1")
(ng #t)
(use "TotalIntIntNeg")
(use "PosMaxTotal")
(use "TotalPosSZero")
(use "Tp1")
(use "Tq1")

;; ?_94:allnc pos^(
;;        TotalPos pos^ ->
;;        allnc k^(TotalInt k^ -> TotalInt(IntN pos^ min k^)) ->
;;        allnc k^(TotalInt k^ -> TotalInt(IntN(SOne pos^)min k^)))

(assume "p^1" "Tp1" "IHp1" "l^" "Tl")
(elim "Tl") ;136-138
(assume "q^" "Tq")
(elim "Tq") ;140-142
(ng #t)
(use "TotalIntIntNeg")
(use "TotalPosSOne")
(use "Tp1")
;; 141
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "TotalIntIntNeg")
(use "TotalPosSOne")
(use "Tp1")
;; 142
(assume "q^1" "Tq1" "IHq1")
(ng #t)
(use "TotalIntIntNeg")
(use "TotalPosSOne")
(use "Tp1")
;; 137
(ng #t)
(use "TotalIntIntNeg")
(use "TotalPosSOne")
(use "Tp1")
;; 138
(assume "q^" "Tq")
(ng #t)
(use "TotalIntIntNeg")
(use "PosMaxTotal")
(use "TotalPosSOne")
(use "Tp1")
(use "Tq")
;; Proof finished.
(save "IntMinTotal")

;; Rules for IntLt

(add-computation-rules
 "IntZero<IntZero" "False"
 "IntZero<IntP pos" "True"
 "IntZero<IntN pos" "False"
 "IntP pos<IntZero" "False"
 "IntP pos1<IntP pos2" "pos1<pos2"
 "IntP pos1<IntN pos2" "False"
 "IntN pos<IntZero" "True"
 "IntN pos1<IntP pos2" "True"
 "IntN pos1<IntN pos2" "pos2<pos1")

;; IntLtTotal
(set-goal (rename-variables (term-to-totality-formula (pt "IntLt"))))
(assume "k^" "Tk" "l^" "Tl")
(elim "Tk")

;; ?_3:allnc pos^(TotalPos pos^ -> TotalBoole(pos^ <l^))

(assume  "p^" "Tp")

(elim "Tl")

(assume "q^" "Tq")
(use "PosLtTotal")
(use "Tp")
(use "Tq")

(use "TotalBooleFalse")

(assume "q^" "Tq")
(use "TotalBooleFalse")

;; ?_4:TotalBoole(0<l^)

(elim "Tl")

(assume "q^" "Tq")
(use "TotalBooleTrue")

(use "TotalBooleFalse")

(assume "q^" "Tq")
(use "TotalBooleFalse")

;; ?_5:allnc pos^(TotalPos pos^ -> TotalBoole(IntN pos^ <l^))

(assume  "p^" "Tp")

(elim "Tl")

(assume "q^" "Tq")
(use "TotalBooleTrue")

(use "TotalBooleTrue")

(assume "q^" "Tq")
(ng #t)
(use "PosLtTotal")
(use "Tq")
(use "Tp")
;; Proof finished.
(save "IntLtTotal")

;; Rules for IntLe

(add-computation-rules
 "IntZero<=IntZero" "True"
 "IntZero<=IntP pos" "True"
 "IntZero<=IntN pos" "False"
 "IntP pos<=IntZero" "False"
 "IntP pos1<=IntP pos2" "pos1<=pos2"
 "IntP pos1<=IntN pos2" "False"
 "IntN pos<=IntZero" "True"
 "IntN pos1<=IntP pos2" "True"
 "IntN pos1<=IntN pos2" "pos2<=pos1")

;; IntLeTotal
(set-goal (rename-variables (term-to-totality-formula (pt "IntLe"))))
(assume "k^" "Tk" "l^" "Tl")
(elim "Tk")

;; ?_3:allnc pos^(TotalPos pos^ -> TotalBoole(pos^ <=l^))

(assume  "p^" "Tp")

(elim "Tl")

(assume "q^" "Tq")
(use "PosLeTotal")
(use "Tp")
(use "Tq")

(use "TotalBooleFalse")

(assume "q^" "Tq")
(use "TotalBooleFalse")

;; ?_4:TotalBoole(0<=l^)

(elim "Tl")

(assume "q^" "Tq")
(use "TotalBooleTrue")

(use "TotalBooleTrue")

(assume "q^" "Tq")
(use "TotalBooleFalse")

;; ?_5:allnc pos^(TotalPos pos^ -> TotalBoole(IntN pos^ <=l^))

(assume  "p^" "Tp")

(elim "Tl")

(assume "q^" "Tq")
(use "TotalBooleTrue")

(use "TotalBooleTrue")

(assume "q^" "Tq")
(ng #t)
(use "PosLeTotal")
(use "Tq")
(use "Tp")
;; Proof finished.
(save "IntLeTotal")

(add-rewrite-rule "i<i" "False")
(add-rewrite-rule "i<i+pos" "True")

(add-rewrite-rule "i<=i" "True")
(add-rewrite-rule "i<=i+nat" "True")
(add-rewrite-rule "i<=i+pos" "True")
(add-rewrite-rule "i<=IntS i" "True")
(add-rewrite-rule "IntS i<=i" "False")

;; Now for the rationals.

;; RatEqTotal
(set-goal "allnc a^(
 TotalRat a^ -> allnc b^(TotalRat b^ -> TotalBoole(a^ =b^)))")
(assume "a^" "Ta")
(elim "Ta")
(assume "i^" "Ti" "p^" "Tp" "b^" "Tb")
(elim "Tb")
(assume "j^" "Tj" "q^" "Tq")
(ng #t)
(use "AndConstTotal")
(use "IntEqTotal")
(use "Ti")
(use "Tj")
(use "PosEqTotal")
(use "Tp")
(use "Tq")
;; Proof finished.
(save "RatEqTotal")

;; Rules for RatPlus

(add-computation-rules
 "(i1#pos1)+(i2#pos2)" "i1*pos2+i2*pos1#pos1*pos2")

;; RatPlusTotal
(set-goal (rename-variables (term-to-totality-formula (pt "RatPlus"))))
(assume "a^" "Ta" "b^" "Tb")
(elim "Ta")
(assume "k^" "Tk" "p^" "Tp")
(elim "Tb")
(assume "l^" "Tl" "q^" "Tq")
(ng #t)
(use "TotalRatRatConstr")
(use "IntPlusTotal")
(use "IntTimesTotal")
(use "Tk")
(use "TotalIntIntPos")
(use "Tq")

(use "IntTimesTotal")
(use "Tl")
(use "TotalIntIntPos")
(use "Tp")

(use "PosTimesTotal")
(use "Tp")
(use "Tq")
;; Proof finished.
(save "RatPlusTotal")

;; RatPlusTotalReal
(set-goal (rename-variables
	   (real-and-formula-to-mr-formula
	    (pt "RatPlus")
	    (proof-to-formula (theorem-name-to-proof "RatPlusTotal")))))
(assume "a^" "a^0" "TMRa0a" "b^" "b^0" "TMRb0b")
(elim "TMRa0a")
(assume "k^" "k^0" "TMRk0k" "p^" "p^0" "TMRp0p")
(elim "TMRb0b")
(assume "l^" "l^0" "TMRl0l" "q^" "q^0" "TMRq0q")
(ng #t)
(use "TotalRatRatConstrMR")
(use "IntPlusTotalReal")
(use "IntTimesTotalReal")
(use "TMRk0k")
(use "TotalIntIntPosMR")
(use "TMRq0q")
(use "IntTimesTotalReal")
(use "TMRl0l")
(use "TotalIntIntPosMR")
(use "TMRp0p")
(use "PosTimesTotalReal")
(use "TMRp0p")
(use "TMRq0q")
;; Proof finished.
(save "RatPlusTotalReal")

;; (display-pconst "RatPlus")
;; (display-idpc "TotalIntMR")

;; 2007-02-13
;; Added rules for RatPlus.  Goal: {1} Bring / out.  (2) Delete /.

(add-rewrite-rule "(a1/b1)+(a2/b2)" "(a1*b2+a2*b1)/(b1*b2)")
(add-rewrite-rule "a1+a2/b2" "(a1*b2+a2)/b2")
(add-rewrite-rule "a1/b1+a2" "(a1+a2*b1)/b1")

(add-rewrite-rule "(a1/b1)+(i2#pos2)" "(a1*pos2+i2*b1)/(b1*pos2)")
(add-rewrite-rule "(i1#pos1)+(a2/b2)" "(i1*b2+a2*pos1)/(pos1*b2)")
;; The following leads to non-termination for a*b+1
;; (add-rewrite-rule "a1+(i2#pos2)" "(a1*pos2+i2)/pos2")
;; (add-rewrite-rule "(i1#pos1)+a2" "(i1+a2*pos1)/pos1")

;; Added 2007-08-28

(add-rewrite-rule "a+(RatConstr IntZero One)" "a")
(add-rewrite-rule "(RatConstr IntZero One)+a" "a")
(add-rewrite-rule "a1+(a2+a3)" "a1+a2+a3")

;; Rules for RatMinus

(add-computation-rules
 "(i1#pos1)-(i2#pos2)" "i1*pos2-i2*pos1#pos1*pos2")

;; RatMinusTotal
(set-goal (rename-variables (term-to-totality-formula (pt "RatMinus"))))
(assume "a^" "Ta" "b^" "Tb")
(elim "Ta")
(assume "k^" "Tk" "p^" "Tp")
(elim "Tb")
(assume "l^" "Tl" "q^" "Tq")
(ng #t)
(use "TotalRatRatConstr")
(use "IntMinusTotal")
(use "IntTimesTotal")
(use "Tk")
(use "TotalIntIntPos")
(use "Tq")
(use "IntTimesTotal")
(use "Tl")
(use "TotalIntIntPos")
(use "Tp")
(use "PosTimesTotal")
(use "Tp")
(use "Tq")
;; Proof finished.
(save "RatMinusTotal")

;; RatMinusTotalReal
(set-goal (rename-variables
	   (real-and-formula-to-mr-formula
	    (pt "RatMinus")
	    (proof-to-formula (theorem-name-to-proof "RatMinusTotal")))))
(assume "a^" "a^0" "TMRa0a" "b^" "b^0" "TMRb0b")
(elim "TMRa0a")
(assume "k^" "k^0" "TMRk0k" "p^" "p^0" "TMRp0p")
(elim "TMRb0b")
(assume "l^" "l^0" "TMRl0l" "q^" "q^0" "TMRq0q")
(ng #t)
(use "TotalRatRatConstrMR")
(use "IntMinusTotalReal")
(use "IntTimesTotalReal")
(use "TMRk0k")
(use "TotalIntIntPosMR")
(use "TMRq0q")
(use "IntTimesTotalReal")
(use "TMRl0l")
(use "TotalIntIntPosMR")
(use "TMRp0p")
(use "PosTimesTotalReal")
(use "TMRp0p")
(use "TMRq0q")
;; Proof finished.
(save "RatMinusTotalReal")

(add-rewrite-rule "(a1/b1)-(a2/b2)" "(a1*b2-a2*b1)/(b1*b2)")
(add-rewrite-rule "a1-a2/b2" "(a1*b2-a2)/b2")
(add-rewrite-rule "a1/b1-a2" "(a1-a2*b1)/b1")

(add-rewrite-rule "(a1/b1)-(i2#pos2)" "(a1*pos2-i2*b1)/(b1*pos2)")
(add-rewrite-rule "(i1#pos1)-(a2/b2)" "(i1*b2-a2*pos1)/(pos1*b2)")
;; (add-rewrite-rule "a1-(i2#pos2)" "(a1*pos2-i2)/pos2")
;; (add-rewrite-rule "(i1#pos1)-a2" "(i1-a2*pos1)/pos1")

;; Added 2007-08-28

(add-rewrite-rule "a-(RatConstr IntZero One)" "a")
(add-rewrite-rule "a-a" "RatConstr IntZero One")

;; Rules for RatTimes

(add-computation-rules
 "(i1#pos1)*(i2#pos2)" "i1*i2#pos1*pos2")

;; RatTimesTotal
(set-goal (rename-variables (term-to-totality-formula (pt "RatTimes"))))
(assume "a^" "Ta" "b^" "Tb")
(elim "Ta")
(assume "k^" "Tk" "p^" "Tp")
(elim "Tb")
(assume "l^" "Tl" "q^" "Tq")
(ng #t)
(use "TotalRatRatConstr")
(use "IntTimesTotal")
(use "Tk")
(use "Tl")

(use "PosTimesTotal")
(use "Tp")
(use "Tq")
;; Proof finished.
(save "RatTimesTotal")

;; RatTimesTotalReal
(set-goal (rename-variables
	   (real-and-formula-to-mr-formula
	    (pt "RatTimes")
	    (proof-to-formula (theorem-name-to-proof "RatTimesTotal")))))
(assume "a^" "a^0" "TMRa0a" "b^" "b^0" "TMRb0b")
(elim "TMRa0a")
(assume "k^" "k^0" "TMRk0k" "p^" "p^0" "TMRp0p")
(elim "TMRb0b")
(assume "l^" "l^0" "TMRl0l" "q^" "q^0" "TMRq0q")
(ng #t)
(use "TotalRatRatConstrMR")
(use "IntTimesTotalReal")
(use "TMRk0k")
(use "TMRl0l")
(use "PosTimesTotalReal")
(use "TMRp0p")
(use "TMRq0q")
;; Proof finished.
(save "RatTimesTotalReal")

(add-rewrite-rule "(a1/b1)*(a2/b2)" "(a1*a2)/(b1*b2)")
;; (add-rewrite-rule "a1*(a2/b2)" "(a1*a2)/b2")
;; (add-rewrite-rule "(a1/b1)*a2" "(a1*a2)/b1")

(add-rewrite-rule "(a1/b1)*(i2#pos2)" "(a1*i2)/(b1*pos2)")
(add-rewrite-rule "(i1#pos1)*(a2/b2)" "(i1*a2)/(pos1*b2)")
;; (add-rewrite-rule "a1*(i2#pos2)" "(a1*i2)/pos2")
;; (add-rewrite-rule "(i1#pos1)*a2" "(i1*a2)/pos1")

;; Added 2007-02-26
(add-rewrite-rule "RatConstr(IntP One)One*a" "a")
(add-rewrite-rule "a*RatConstr(IntP One)One" "a")

;; Added 2007-08-28

(add-rewrite-rule "a*(RatConstr IntZero One)" "RatConstr IntZero One")
(add-rewrite-rule "(RatConstr IntZero One)*a" "RatConstr IntZero One")
(add-rewrite-rule "a1*(a2*a3)" "a1*a2*a3")

;; Changed 2013-03-30

;; Rules for RatDiv.  They give correct results for a/b (only) if b not 0.

(add-computation-rules
 "(i1#pos1)/(IntP pos#pos2)" "(i1*pos2#pos*pos1)"
 "(i1#pos1)/(IntZero#pos2)" "RatConstr IntZero One"
 "(i1#pos1)/(IntN pos#pos2)" "((IntZero-i1)*pos2#pos*pos1)")

;; RatDivTotal
(set-goal (rename-variables (term-to-totality-formula (pt "RatDiv"))))
(assume "a^" "Ta" "b^" "Tb")
(elim "Ta")
(assume "k^" "Tk" "p^" "Tp")
(elim "Tb")
(assume "l^" "Tl" "q^" "Tq")
(elim "Tl")
(assume "p^1" "Tp1")
(use "TotalRatRatConstr")
(use "IntTimesTotal")
(use "Tk")
(use "TotalIntIntPos")
(use "Tq")
(use "PosTimesTotal")
(use "Tp1")
(use "Tp")
(ng #t)
(use "TotalRatRatConstr")
(use "TotalIntIntZero")
(use "TotalPosOne")
(assume "p^1" "Tp1")
(use "TotalRatRatConstr")
(use "IntTimesTotal")
(use "IntMinusTotal")
(use "TotalIntIntZero")
(use "Tk")
(use "TotalIntIntPos")
(use "Tq")
(use "PosTimesTotal")
(use "Tp1")
(use "Tp")
;; Proof finished.
(save "RatDivTotal")

(add-rewrite-rule "(a1/b1)/(a2/b2)" "(a1*b2)/(b1*a2)")

;; Rules for RatAbs

(add-computation-rules
 "abs(IntZero#pos)" "IntZero#pos"
 "abs(IntP pos1#pos2)" "IntP pos1#pos2"
 "abs(IntN pos1#pos2)" "IntP pos1#pos2")

;; RatAbsTotal
(set-goal (rename-variables (term-to-totality-formula (pt "RatAbs"))))
(assume "a^" "Ta")
(elim "Ta")
(assume "k^" "Tk" "p^" "Tp")
(elim "Tk")

;; ?_5:allnc pos^(TotalPos pos^ -> TotalRat(abs(pos^ #p^)))
(assume "q^" "Tq")
(elim "Tq")

(use "TotalRatRatConstr")
(use "TotalIntIntPos")
(use "TotalPosOne")
(use "Tp")

(assume "q^1" "Tq1" "Useless")
(ng #t)
(use "TotalRatRatConstr")
(use "TotalIntIntPos")
(use "TotalPosSZero")
(use "Tq1")
(use "Tp")

(assume "q^1" "Tq1" "Useless")
(ng #t)
(use "TotalRatRatConstr")
(use "TotalIntIntPos")
(use "TotalPosSOne")
(use "Tq1")
(use "Tp")

;; ?_6:TotalRat(abs(0#p^))
(ng #t)
(use "TotalRatRatConstr")
(use "TotalIntIntZero")
(use "Tp")

;; ?_7:allnc pos^(TotalPos pos^ -> TotalRat(abs(IntN pos^ #p^)))
(assume "q^" "Tq")
(elim "Tq")

(use "TotalRatRatConstr")
(use "TotalIntIntPos")
(use "TotalPosOne")
(use "Tp")

(assume "q^1" "Tq1" "Useless")
(ng #t)
(use "TotalRatRatConstr")
(use "TotalIntIntPos")
(use "TotalPosSZero")
(use "Tq1")
(use "Tp")

(assume "q^1" "Tq1" "Useless")
(ng #t)
(use "TotalRatRatConstr")
(use "TotalIntIntPos")
(use "TotalPosSOne")
(use "Tq1")
(use "Tp")
;; Proof finished.
(save "RatAbsTotal")

;; Rules for RatExp : rat=>int=>rat

(add-computation-rules
 "(int1#pos2)**(IntP pos3)" "(int1**pos3)#(pos2**pos3)"
 "rat**IntZero" "IntP One#One"
 "(IntZero#pos2)**(IntN pos3)" "IntZero#pos2"
 "((IntP pos1)#pos2)**(IntN pos3)" "IntP(pos2**pos3)#(pos1**pos3)"
 "((IntN pos1)#pos2)**(IntN pos3)" "((IntN pos2)**pos3)#(pos1**pos3)")

;; RatExpTotal
(set-goal (rename-variables (term-to-totality-formula (pt "RatExp"))))
(assume "a^" "Ta" "k^" "Tk")
(elim "Ta")
(assume "k^1" "Tk1" "p^2" "Tp2")
(elim "Tk")
(assume "p^3" "Tp3")
(use "TotalRatRatConstr")
(use "IntExpTotal")
(use "Tk1")
(use "PosToNatTotal")
(use "Tp3")
(use "PosExpTotal")
(use "Tp2")
(use "PosToNatTotal")
(use "Tp3")
(use "TotalRatRatConstr")
(use "TotalIntIntPos")
(use "TotalPosOne")
(use "TotalPosOne")
(assume "p^3" "Tp3")
(elim "Tk1")
(assume "p^1" "Tp1")
(ng #t)
(use "TotalRatRatConstr")
(use "TotalIntIntPos")
(use "PosExpTotal")
(use "Tp2")
(use "PosToNatTotal")
(use "Tp3")
(use "PosExpTotal")
(use "Tp1")
(use "PosToNatTotal")
(use "Tp3")
(ng #t)
(use "TotalRatRatConstr")
(use "TotalIntIntZero")
(use "Tp2")
(assume "p^1" "Tp1")
(ng #t)
(use "TotalRatRatConstr")
(use "IntExpTotal")
(use "TotalIntIntNeg")
(use "Tp2")
(use "PosToNatTotal")
(use "Tp3")
(use "PosExpTotal")
(use "Tp1")
(use "PosToNatTotal")
(use "Tp3")
;; Proof finished.
(save "RatExpTotal")

;; Normal forms, which makes equally displayed terms equal.  Strategy:
;; do computations at the lowest possible level.  Raise the type outside.

(add-rewrite-rules
 "rat**(IntP One)" "rat"
 "rat1**(IntS int2)" "rat1**int2*rat1"

 "((IntP pos1)#One)**(IntP pos2)" "IntP(pos1**pos2)#One"
 "((IntP pos1)#One)**(IntN pos2)" "IntP One#(pos1**pos2)"
 "((IntP pos1)#One)**(NatToInt nat2)" "IntP(pos1**nat2)#One"

 "((NatToInt nat1)#One)**(IntP pos2)" "NatToInt(nat1**pos2)#One"
 "((NatToInt nat1)#One)**(NatToInt nat2)" "NatToInt(nat1**nat2)#One"

 "((IntN pos1)#One)**(IntP pos2)" "IntN(pos1**pos2)#One"
 "((IntN pos1)#One)**(IntN pos2)" "IntN One#(pos1**pos2)"
 "((IntN pos1)#One)**(NatToInt nat2)" "IntN(pos1**nat2)#One"

 "(int1#One)**(IntP pos2)" "(int1**pos2)#One")

;; Rules for RatMax

(add-computation-rules
 "(i1#pos1)max(i2#pos2)"
 "[if (i1*pos2<=i2*pos1) (i2#pos2) (i1#pos1)]")

;; RatMaxTotal
(set-goal (rename-variables (term-to-totality-formula (pt "RatMax"))))
(assume "a^" "Ta" "b^" "Tb")
(elim "Ta")
(assume "i^" "Ti" "p^" "Tp")
(elim "Tb")
(assume "k^" "Tk" "q^" "Tq")
(ng #t)
(use "BooleIfTotal")
(use "IntLeTotal")
(use "IntTimesTotal")
(use "Ti")
(use "TotalIntIntPos")
(use "Tq")
(use "IntTimesTotal")
(use "Tk")
(use "TotalIntIntPos")
(use "Tp")
(use "TotalRatRatConstr")
(use "Tk")
(use "Tq")
(use "TotalRatRatConstr")
(use "Ti")
(use "Tp")
;; Proof finished.
(save "RatMaxTotal")

;; Rules for RatMin

(add-computation-rules
 "(i1#pos1)min(i2#pos2)"
 "[if (i1*pos2<=i2*pos1) (i1#pos1) (i2#pos2)]")

;; RatMinTotal
(set-goal (rename-variables (term-to-totality-formula (pt "RatMin"))))
(assume "a^" "Ta" "b^" "Tb")
(elim "Ta")
(assume "i^" "Ti" "p^" "Tp")
(elim "Tb")
(assume "k^" "Tk" "q^" "Tq")
(ng #t)
(use "BooleIfTotal")
(use "IntLeTotal")
(use "IntTimesTotal")
(use "Ti")
(use "TotalIntIntPos")
(use "Tq")
(use "IntTimesTotal")
(use "Tk")
(use "TotalIntIntPos")
(use "Tp")
(use "TotalRatRatConstr")
(use "Ti")
(use "Tp")
(use "TotalRatRatConstr")
(use "Tk")
(use "Tq")
;; Proof finished.
(save "RatMinTotal")

;; Rules for RatLt

(add-computation-rules
 "(i1#pos1)<(i2#pos2)" "i1*pos2<i2*pos1")

;; RatLtTotal
(set-goal (rename-variables (term-to-totality-formula (pt "RatLt"))))
(assume "a^" "Ta" "b^" "Tb")
(elim "Ta")
(assume "k^" "Tk" "p^" "Tp")
(elim "Tb")
(assume "l^" "Tl" "q^" "Tq")
(ng #t)
(use "IntLtTotal")
(use "IntTimesTotal")
(use "Tk")
(use "TotalIntIntPos")
(use "Tq")
(use "IntTimesTotal")
(use "Tl")
(use "TotalIntIntPos")
(use "Tp")
;; Proof finished.
(save "RatLtTotal")

;; Rules for RatLe

(add-computation-rules
 "(i1#pos1)<=(i2#pos2)" "i1*pos2<=i2*pos1")

;; RatLeTotal
(set-goal (rename-variables (term-to-totality-formula (pt "RatLe"))))
(assume "a^" "Ta" "b^" "Tb")
(elim "Ta")
(assume "k^" "Tk" "p^" "Tp")
(elim "Tb")
(assume "l^" "Tl" "q^" "Tq")
(ng #t)
(use "IntLeTotal")
(use "IntTimesTotal")
(use "Tk")
(use "TotalIntIntPos")
(use "Tq")
(use "IntTimesTotal")
(use "Tl")
(use "TotalIntIntPos")
(use "Tp")
;; Proof finished.
(save "RatLeTotal")

;; RealPosTotal
(set-goal (rename-variables (term-to-totality-formula (pt "RealPos"))))
(assume "x^" "Tx" "k^" "Tk")
(elim "Tx")
(assume "as^" "Tas" "M^" "TM")
(ng #t)
(use "RatLeTotal")
(use "RatDivTotal")
(use "TotalRatRatConstr")
(use "TotalIntIntPos")
(use "TotalPosOne")
(use "TotalPosOne")
(use "RatExpTotal")
(use "TotalRatRatConstr")
(use "TotalIntIntPos")
(use "TotalPosSZero")
(use "TotalPosOne")
(use "TotalPosOne")
(use "Tk")
(use "Tas")
(use "TM")
(use "IntPlusTotal")
(use "Tk")
(use "TotalIntIntPos")
(use "TotalPosOne")
;; Proof finished.
(save "RealPosTotal")

(add-rewrite-rule "a<a" "False")
(add-rewrite-rule "a<a+pos" "True")

(add-rewrite-rule "a<=a" "True")
(add-rewrite-rule "a<=a+pos" "True")
(add-rewrite-rule "a<=a+nat" "True")
(add-rewrite-rule "IntZero<=(IntN pos1#pos2)" "False")

;; Rules for RatEqv

(add-computation-rules
 "(i1#pos1)==(i2#pos2)" "i1*pos2=i2*pos1")

(add-rewrite-rule "a==a" "True")

;; RatEqvTotal
(set-goal (rename-variables (term-to-totality-formula (pt "RatEqv"))))
(assume "a^" "Ta")
(elim "Ta")
(assume "i^" "Ti" "p^" "Tp" "b^" "Tb")
(elim "Tb")
(assume "j^" "Tj" "q^" "Tq")
(ng #t)
(use "IntEqTotal")
(use "IntTimesTotal")
(use "Ti")
(use "TotalIntIntPos")
(use "Tq")
(use "IntTimesTotal")
(use "Tj")
(use "TotalIntIntPos")
(use "Tp")
;; Proof finished.
(save "RatEqvTotal")

;; Rules for RealPlus

(add-computation-rule
 "RealConstr as M+RealConstr bs N"
 "RealConstr([n]as n+bs n)([k]M(k+1)max N(k+1))")

;: RealPlusTotal
(set-goal (rename-variables (term-to-totality-formula (pt "RealPlus"))))
(use "All-AllPartial")
(ind)
(use "AllPartial-All")
(assume "as^" "Tas")
(use "AllPartial-All")
(assume "M^" "TM")
(use "All-AllPartial")
(ind)
(use "AllPartial-All")
(assume "bs^" "Tbs")
(use "AllPartial-All")
(assume "N^" "TN")
(ng #t)
(use "TotalReaRealConstr")
(assume "n^" "Tn")
(use "RatPlusTotal")
(use "Tas")
(use "Tn")
(use "Tbs")
(use "Tn")
(assume "k^" "Tk")
(use "NatMaxTotal")
(use "TM")
(use "IntSTotal")
(use "Tk")
(use "TN")
(use "IntSTotal")
(use "Tk")
;; Proof finished.
(save "RealPlusTotal")

;; Added 2007-08-29
(add-rewrite-rule
 "x+(RealConstr([n](RatConstr IntZero One))([k]Zero))" "x")
(add-rewrite-rule
 "(RealConstr([n](RatConstr IntZero One))([k]Zero))+x" "x")
(add-rewrite-rule "x1+(x2+x3)" "x1+x2+x3")

;; Rules for RealMinus

(add-computation-rule
 "RealConstr as M-RealConstr bs N"
 "RealConstr([n]as n-bs n)([k]M(k+1)max N(k+1))")

;; RealMinusTotal
(set-goal (rename-variables (term-to-totality-formula (pt "RealMinus"))))
(use "All-AllPartial")
(ind)
(use "AllPartial-All")
(assume "as^" "Tas")
(use "AllPartial-All")
(assume "M^" "TM")
(use "All-AllPartial")
(ind)
(use "AllPartial-All")
(assume "bs^" "Tbs")
(use "AllPartial-All")
(assume "N^" "TN")
(ng #t)
(use "TotalReaRealConstr")
(assume "n^" "Tn")
(use "RatMinusTotal")
(use "Tas")
(use "Tn")
(use "Tbs")
(use "Tn")
(assume "k^" "Tk")
(use "NatMaxTotal")
(use "TM")
(use "IntSTotal")
(use "Tk")
(use "TN")
(use "IntSTotal")
(use "Tk")
;; Proof finished.
(save "RealMinusTotal")

;; RealLtTotal
(set-goal (rename-variables (term-to-totality-formula (pt "RealLt"))))
(assume "x^" "Tx" "y^" "Ty" "k^" "Tk")
(elim "Tx")
(assume "as^" "Tas" "M^" "TM")
(elim "Ty")
(assume "bs^" "Tbs" "N^" "TN")
(ng #t)
;; ?_7:TotalBoole
;;     (1/2**k^ <=
;;      bs^(N^(k^ +1+1)max M^(k^ +1+1))-as^(N^(k^ +1+1)max M^(k^ +1+1)))
(use "RatLeTotal")
(use "RatDivTotal")
(use "TotalRatRatConstr")
(use "TotalIntIntPos")
(use "TotalPosOne")
(use "TotalPosOne")
(use "RatExpTotal")
(use "TotalRatRatConstr")
(use "TotalIntIntPos")
(use "TotalPosSZero")
(use "TotalPosOne")
(use "TotalPosOne")
(use "Tk")
(use "RatMinusTotal")
(use "Tbs")
(use "NatMaxTotal")
(use "TN")
(use "IntPlusTotal")
(use "IntPlusTotal")
(use "Tk")
(use "TotalIntIntPos")
(use "TotalPosOne")
(use "TotalIntIntPos")
(use "TotalPosOne")
(use "TM")
(use "IntPlusTotal")
(use "IntPlusTotal")
(use "Tk")
(use "TotalIntIntPos")
(use "TotalPosOne")
(use "TotalIntIntPos")
(use "TotalPosOne")

(use "Tas")
(use "NatMaxTotal")
(use "TN")
(use "IntPlusTotal")
(use "IntPlusTotal")
(use "Tk")
(use "TotalIntIntPos")
(use "TotalPosOne")
(use "TotalIntIntPos")
(use "TotalPosOne")
(use "TM")
(use "IntPlusTotal")
(use "IntPlusTotal")
(use "Tk")
(use "TotalIntIntPos")
(use "TotalPosOne")
(use "TotalIntIntPos")
(use "TotalPosOne")
;; Proof finished.
(save "RealLtTotal")

;; Added 2007-08-29
(add-rewrite-rule "x-(RealConstr([n](RatConstr IntZero One))([k]Zero))" "x")
(add-rewrite-rule "x-x" "RealConstr([n](RatConstr IntZero One))([k]Zero)")

;; Rules for RealAbs

(add-computation-rule
 "abs(RealConstr as M)" "RealConstr([n]abs(as n))M")

;; RealAbsTotal
(set-goal (rename-variables (term-to-totality-formula (pt "RealAbs"))))
(assume "x^" "Tx")
(elim "Tx")
(assume "as^" "Tas" "M^" "TM")
(ng #t)
(use "TotalReaRealConstr")
(assume "n^" "Tn")
(ng #t)
(use "RatAbsTotal")
(use "Tas")
(use "Tn")
(use "TM")
;; Proof finished.
(save "RealAbsTotal")

(add-program-constant "RealInv" (py "rea=>int=>rea") t-deg-zero)

(add-computation-rules
 "RealInv(RealConstr as M)l"
 "RealConstr([n]1/as n)([k]M(2*IntS l+k)max M(IntS l))")

;; RealInvTotal
(set-goal (rename-variables (term-to-totality-formula (pt "RealInv"))))
(assume "x^" "Tx")
(elim "Tx")
(drop "Tx")
(assume "as^" "Tas" "M^" "TM" "k^" "Tk")
(ng #t)
(use "TotalReaRealConstr") ;7-8
(assume "n^" "Tn")
(ng #t)
(use "RatDivTotal")
(use "TotalRatRatConstr")
(use "TotalIntIntPos")
(use "TotalPosOne")
(use "TotalPosOne")
(use "Tas")
(use "Tn")
;; 8
(assume "k^1" "Tk1")
(ng #t)
(use "NatMaxTotal")
(use "TM")
(use "IntPlusTotal")
(use "IntTimesTotal")
(use "TotalIntIntPos")
(use "TotalPosSZero")
(use "TotalPosOne")
(use "IntSTotal")
(use "Tk")
(use "Tk1")
(use "TM")
(use "IntSTotal")
(use "Tk")
;; Proof finished.
(save "RealInvTotal")

;; We prove that NatToPos is an isomorphism w.r.t. <= and <.  Main
;; idea: Translate the computation rules for PosLe, PosLt into
;; equational lemmas for NatLe, NatLt with NatDouble nat for SZero pos
;; and Succ(NatDouble nat) for SOne pos.

;; NatLeSZeroSZero
(set-goal "all nat1,nat2 (NatDouble nat1<=NatDouble nat2)=(nat1<=nat2)")
(ind) ;2-3
(assume "nat2")
(ng #t)
(use "Truth")
;; 3
(assume "nat1" "IH1")
(cases)
(ng #t)
(use "Truth")
(assume "nat2")
(ng #t)
(use "IH1")
;; Proof finished.
(save "NatLeSZeroSZero")

;; NatLeSZeroSOne
(set-goal "all nat1,nat2 (NatDouble nat1<=Succ(NatDouble nat2))=(nat1<=nat2)")
(ind) ;2-3
(assume "nat2")
(ng #t)
(use "Truth")
;; 3
(assume "nat1" "IH1")
(cases)
(ng #t)
(use "Truth")
(assume "nat2")
(ng #t)
(use "IH1")
;; Proof finished.
(save "NatLeSZeroSOne")

;; NatLeSOneSZero
(set-goal "all nat1,nat2 (Succ(NatDouble nat1)<=NatDouble nat2)=(nat1<nat2)")
(ind) ;2-3
(cases)
(ng #t)
(use "Truth")
(assume "nat2")
(ng #t)
(use "Truth")
;; 3
(assume "nat1" "IH1")
(cases)
(ng #t)
(use "Truth")
(assume "nat2")
(ng #t)
(use "IH1")
;; Proof finished.
(save "NatLeSOneSZero")

;; NatLeSOneSOne
(set-goal "all nat1,nat2
 (Succ(NatDouble nat1)<=Succ(NatDouble nat2))=(nat1<=nat2)")
(ind) ;2-3
(ng #t)
(strip)
(use "Truth")
;; 3
(assume "nat1" "IH1")
(cases)
(ng #t)
(use "Truth")
(assume "nat2")
(ng #t)
(use "IH1")
;; Proof finished.
(save "NatLeSOneSOne")

;; NatLtSZeroSZero
(set-goal "all nat1,nat2 (NatDouble nat1<NatDouble nat2)=(nat1<nat2)")
(ind) ;2-3
(cases)
(use "Truth")
(assume "nat2")
(ng #t)
(use "Truth")
;; 3
(assume "nat1" "IH1")
(cases)
(ng #t)
(use "Truth")
(assume "nat2")
(ng #t)
(use "IH1")
;; Proof finished.
(save "NatLtSZeroSZero")

;; NatLtSZeroSOne
(set-goal "all nat1,nat2 (NatDouble nat1<Succ(NatDouble nat2))=(nat1<=nat2)")
(ind) ;2-3
(assume "nat2")
(ng #t)
(use "Truth")
;; 3
(assume "nat1" "IH1")
(cases)
(ng #t)
(use "Truth")
(assume "nat2")
(ng #t)
(use "IH1")
;; Proof finished.
(save "NatLtSZeroSOne")

;; NatLtSOneSZero
(set-goal "all nat1,nat2 (Succ(NatDouble nat1)<NatDouble nat2)=(nat1<nat2)")
(ind) ;2-3
(cases)
(ng #t)
(use "Truth")
(assume "nat2")
(ng #t)
(use "Truth")
;; 3
(assume "nat1" "IH1")
(cases)
(ng #t)
(use "Truth")
(assume "nat2")
(ng #t)
(use "IH1")
;; Proof finished.
(save "NatLtSOneSZero")

(display-pconst "PosLe" "PosLt")
;; NatLtSOneSOne
(set-goal "all nat1,nat2
 (Succ(NatDouble nat1)<Succ(NatDouble nat2))=(nat1<nat2)")
(ind) ;2-3
(cases)
(ng #t)
(strip)
(use "Truth")
(assume "nat2")
(ng #t)
(use "Truth")
;; 3
(assume "nat1" "IH1")
(cases)
(ng #t)
(use "Truth")
(assume "nat2")
(ng #t)
(use "IH1")
;; Proof finished.
(save "NatLtSOneSOne")

;; NatLtOneSZero
(set-goal "all nat(Zero<nat -> Succ Zero<NatDouble nat)")
(cases)
(assume "Absurd")
(use "Absurd")
(ng #t)
(strip)
(use "Truth")
;; Proof finished.
(save "NatLtOneSZero")

;; NatLtOneSOne
(set-goal "all nat(Zero<nat -> Succ Zero<Succ(NatDouble nat))")
(assume "nat" "0<n")
(use "NatLtTrans" (pt "NatDouble nat"))
(use "NatLtOneSZero")
(use "0<n")
(use "Truth")
;; Proof finished.
(save "NatLtOneSOne")

;; NatLeSZeroOne
(set-goal "all nat(Zero<nat -> NatDouble nat<=Succ Zero -> F)")
(cases)
(assume "Absurd" "Useless")
(use "Absurd")
(ng #t)
(assume "nat" "Useless" "Absurd")
(use "Absurd")
;; Proof finished.
(save "NatLeSZeroOne")

;; NatLtOneFalse
(set-goal "all nat(Zero<nat -> NatDouble nat<Succ Zero -> F)")
(cases)
(assume "Absurd" "Useless")
(use "Absurd")
(ng #t)
(assume "nat" "Useless" "Absurd")
(use "Absurd")
;; Proof finished.
(save "NatLtOneFalse")

;; NatLeSOneOne
;; (remove-theorem "NatLeSOneOne")
(set-goal "all nat(Zero<nat -> NatDouble nat<=Zero -> F)")
(cases)
(assume "Absurd" "Useless")
(use "Absurd")
(ng #t)
(assume "nat" "Useless" "Absurd")
(use "Absurd")
;; Proof finished.
(save "NatLeSOneOne")

;; PosToNatLeLt
(set-goal "all pos1,pos2((PosToNat pos1<=PosToNat pos2)=(pos1<=pos2) &
                         (PosToNat pos1<PosToNat pos2)=(pos1<pos2))")
(ind) ;2-4
(cases) ;5-7
(ng #t)
(split)
(use "Truth")
(use "Truth")
;; 6
(assume "pos")
(ng #t)
(split)
(assert "Succ Zero<=NatDouble(PosToNat pos)")
 (use "NatLtToLe")
 (use "NatLtOneSZero")
 (use "NatLt0Pos")
(assume "Succ Zero<=NatDouble(PosToNat pos)")
(simp "Succ Zero<=NatDouble(PosToNat pos)")
(use "Truth")
(assert "Succ Zero<NatDouble(PosToNat pos)")
 (use "NatLtOneSZero")
 (use "NatLt0Pos")
(assume "Succ Zero<NatDouble(PosToNat pos)")
(simp "Succ Zero<NatDouble(PosToNat pos)")
(use "Truth")
;; 7
(assume "pos")
(ng #t)
(split)
(use "Truth")
(assert "Zero<NatDouble(PosToNat pos)")
 (use "NatLtOneSOne")
 (use "NatLt0Pos")
(assume "Zero<NatDouble(PosToNat pos)")
(simp "Zero<NatDouble(PosToNat pos)")
(use "Truth")
;; 3
(assume "pos1" "IH1")
(cases) ;36-38
(ng #t)
(split)
(assert "NatDouble(PosToNat pos1)<=Succ Zero -> F")
 (use "NatLeSZeroOne")
 (use "NatLt0Pos")
(assume "NatDouble(PosToNat pos1)<=Succ Zero -> F")
(simp "NatDouble(PosToNat pos1)<=Succ Zero -> F")
(use "Truth")
(assert "NatDouble(PosToNat pos1)<Succ Zero -> F")
 (use "NatLtOneFalse")
 (use "NatLt0Pos")
(assume "NatDouble(PosToNat pos1)<Succ Zero -> F")
(simp "NatDouble(PosToNat pos1)<Succ Zero -> F")
(use "Truth")
;; 37
(assume "pos2")
(ng #t)
(split)
(simp "NatLeSZeroSZero")
(use "IH1")
(simp "NatLtSZeroSZero")
(use "IH1")
;; 38
(assume "pos2")
(ng #t)
(split)
(simp "NatLeSZeroSOne")
(use "IH1")
(simp "NatLtSZeroSOne")
(use "IH1")
;; 4
(assume "pos1" "IH1")
(cases) ;65-67
(ng #t)
(split)
(assert "NatDouble(PosToNat pos1)<=Zero -> F")
 (use "NatLeSOneOne")
 (use "NatLt0Pos")
(assume "NatDouble(PosToNat pos1)<=Zero -> F")
(simp "NatDouble(PosToNat pos1)<=Zero -> F")
(use "Truth")
(use "Truth")
;; 66
(assume "pos2")
(ng #t)
(split)
(simp "NatLeSOneSZero")
(use "IH1")
(simp "NatLtSOneSZero")
(use "IH1")
;; 67
(assume "pos2")
(ng #t)
(split)
(simp "NatLeSOneSOne")
(use "IH1")
(simp "NatLtSOneSOne")
(use "IH1")
;; Proof finished.
(save "PosToNatLeLt")

;; Easy consequences

;; PosToNatLe
(set-goal "all pos1,pos2 (PosToNat pos1<=PosToNat pos2)=(pos1<=pos2)")
(assume "pos1" "pos2")
(use "PosToNatLeLt")
;; Proof finished.
(save "PosToNatLe")

;; NatToPosLe
(set-goal "all nat1,nat2(Zero<nat1 -> Zero<nat2 ->
  (NatToPos nat1<=NatToPos nat2)=(nat1<=nat2))")
(assume "nat1" "nat2" "0<n1" "0<n2")
(simp "<-" "PosToNatLe")
(simp "PosToNatToPosId")
(simp "PosToNatToPosId")
(use "Truth")
(use "0<n2")
(use "0<n1")
;; Proof finished.
(save "NatToPosLe")

;; PosLeMonPlus
(set-goal
 "all pos1,pos2,pos3,pos4(pos1<=pos2 -> pos3<=pos4 -> pos1+pos3<=pos2+pos4)")
(assume "pos1" "pos2" "pos3" "pos4" "p1<=p2" "p3<=p4")
(assert "pos1=NatToPos(PosToNat pos1)")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "pos1=NatToPos(PosToNat pos1)")
(simp "pos1=NatToPos(PosToNat pos1)")
(drop "pos1=NatToPos(PosToNat pos1)")
(assert "pos2=NatToPos(PosToNat pos2)")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "pos2=NatToPos(PosToNat pos2)")
(simp "pos2=NatToPos(PosToNat pos2)")
(drop "pos2=NatToPos(PosToNat pos2)")
(assert "pos3=NatToPos(PosToNat pos3)")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "pos3=NatToPos(PosToNat pos3)")
(simp "pos3=NatToPos(PosToNat pos3)")
(drop "pos3=NatToPos(PosToNat pos3)")
(assert "pos4=NatToPos(PosToNat pos4)")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "pos4=NatToPos(PosToNat pos4)")
(simp "pos4=NatToPos(PosToNat pos4)")
(drop "pos4=NatToPos(PosToNat pos4)")
(simp "<-" "NatToPosPlus")
(simp "<-" "NatToPosPlus")
(simp "NatToPosLe")
(use "NatLeMonPlus")
(simp "PosToNatLe")
(use "p1<=p2")
(simp "PosToNatLe")
(use "p3<=p4")
;; ?_35:Zero<NatPlus(PosToNat pos2)(PosToNat pos4)
(simp "<-" "PosToNatPlus")
(use "NatLt0Pos")
(simp "<-" "PosToNatPlus")
(use "NatLt0Pos")
(use "NatLt0Pos")
(use "NatLt0Pos")
(use "NatLt0Pos")
(use "NatLt0Pos")
;; Proof finished.
(save "PosLeMonPlus")

;; PosLeMonTimes
(set-goal
 "all pos1,pos2,pos3,pos4(pos1<=pos2 -> pos3<=pos4 -> pos1*pos3<=pos2*pos4)")
(assume "pos1" "pos2" "pos3" "pos4" "p1<=p2" "p3<=p4")
(assert "pos1=NatToPos(PosToNat pos1)")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "pos1=NatToPos(PosToNat pos1)")
(simp "pos1=NatToPos(PosToNat pos1)")
(drop "pos1=NatToPos(PosToNat pos1)")
(assert "pos2=NatToPos(PosToNat pos2)")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "pos2=NatToPos(PosToNat pos2)")
(simp "pos2=NatToPos(PosToNat pos2)")
(drop "pos2=NatToPos(PosToNat pos2)")
(assert "pos3=NatToPos(PosToNat pos3)")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "pos3=NatToPos(PosToNat pos3)")
(simp "pos3=NatToPos(PosToNat pos3)")
(drop "pos3=NatToPos(PosToNat pos3)")
(assert "pos4=NatToPos(PosToNat pos4)")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "pos4=NatToPos(PosToNat pos4)")
(simp "pos4=NatToPos(PosToNat pos4)")
(drop "pos4=NatToPos(PosToNat pos4)")
(simp "<-" "NatToPosTimes")
(simp "<-" "NatToPosTimes")
(simp "NatToPosLe")
(use "NatLeMonTimes")
(simp "PosToNatLe")
(use "p1<=p2")
(simp "PosToNatLe")
(use "p3<=p4")
;; ?_35:Zero<NatTimes(PosToNat pos2)(PosToNat pos4)
(simp "<-" "PosToNatTimes")
(use "NatLt0Pos")
(simp "<-" "PosToNatTimes")
(use "NatLt0Pos")
(use "NatLt0Pos")
(use "NatLt0Pos")
(use "NatLt0Pos")
(use "NatLt0Pos")
;; Proof finished.
(save "PosLeMonTimes")

;; We now aim at defining RealTimes by computation rules and proving
;; RealTimesTotal.  This however requires much of the development of
;; constructive reals (and also the function ord-field-simp-bwd) and
;; hence is done in real.scm.  Here we collect some auxiliary program
;; constants and theorems which seem to fit in this file.

(add-program-constant "PosLog" (py "pos=>nat") t-deg-zero)

(add-computation-rules
 "PosLog One" "Zero"
 "PosLog(SZero pos)" "Succ(PosLog pos)"
 "PosLog(SOne pos)" "Succ(PosLog pos)")

;; (pp (nt (pt "PosLog(SZero(SZero(SZero One)))")))
;; (pp (nt (pt "PosLog(SZero(SOne(SZero One)))")))

;; PosLogTotal
(set-goal (rename-variables (term-to-totality-formula (pt "PosLog"))))
(assume "pos^" "Tp")
(elim "Tp")
(ng #t)
(use "TotalNatZero")
;; 4
(assume "pos^1" "Tp1" "IH")
(ng #t)
(use "TotalNatSucc")
(use "IH")
;; 5
(assume "pos^1" "Tp1" "IH")
(ng #t)
(use "TotalNatSucc")
(use "IH")
;; Proof finished.
(save "PosLogTotal")

;; (pp (nt (pt "PosLog 32")))

;; PosLeExpTwoLog
(set-goal "all pos 2**PosLog pos<=pos")
(ind)
(use "Truth")
(assume "pos" "IH")
(ng #t)
(use "IH")
(assume "pos" "IH")
(ng #t)
(use "IH")
;; Proof finished.
(save "PosLeExpTwoLog")

;; PosLtExpTwoSuccLog
(set-goal "all pos pos<2**Succ(PosLog pos)")
(ind)
(use "Truth")
(assume "pos")
(ng #t)
(assume "IH")
(use "IH")
(assume "pos")
(ng #t)
(assume "IH")
(use "IH")
;; Proof finished.
(save "PosLtExpTwoSuccLog")

;; RatLeCritPos
(set-goal "all pos1,pos2,pos3,pos4(pos1<=pos2 -> pos3<=pos4 ->
 (pos1#pos4)<=pos2/pos3)")
(ng #t)
(use "PosLeMonTimes")
;; Proof finished.
(save "RatLeCritPos")

;; RatLeBoundPos
(set-goal "all pos1,pos2(
 (pos1#pos2)<=(2**Succ(PosLog pos1))/(2**PosLog pos2))")
(assume "pos1" "pos2")
(use "RatLeCritPos")
(use "PosLtToLe")
(use "PosLtExpTwoSuccLog")
(use "PosLeExpTwoLog")
;; Proof finished.
(save "RatLeBoundPos")

(add-global-assumption
 "RatTimesTwoExp"
 "all int1,int2 2**int1*2**int2=2**(int1+int2)")

(add-global-assumption
 "RatDivTwoExp"
 "all nat1,nat2 2**nat1/2**nat2=2**(nat1-nat2)")

;; RatLeBound
(set-goal "all pos1,pos2 ex int (pos1#pos2)<=2**int")
(assume "pos1" "pos2")
(assert "(pos1#pos2)<=(2**Succ(PosLog pos1))/(2**PosLog pos2)")
 (use "RatLeCritPos")
 (use "PosLtToLe")
 (use "PosLtExpTwoSuccLog")
 (use "PosLeExpTwoLog")
 (simp "RatDivTwoExp")
(assume "Assertion")
(ex-intro (pt "Succ(PosLog pos1)-PosLog pos2"))
(use "Assertion")
;; Proof finished.
(save "RatLeBound")

;; (pp (nt (proof-to-extracted-term (theorem-name-to-proof "RatLeBound"))))
;; [p0,p1]IntS(PosLog p0)-PosLog p1

;; RatLeAbsBound
(set-goal "all rat ex int abs rat<=2**int")
(cases)
(cases) ;3-5
(ng #t)
(use "RatLeBound")
;; 4
(assume "pos")
(ex-intro (pt "0"))
(use "Truth")
;; 5
(ng #t)
(use "RatLeBound")
;; Proof finished.
(save "RatLeAbsBound")

;; (pp (nt (proof-to-extracted-term (theorem-name-to-proof "RatLeAbsBound"))))
;;[a0][if a0 ([k1,p2][if k1 ([p3]cRatLeBound p3 p2) 0 ([p3]cRatLeBound p3 p2)])]

;; Rules for RealExp : rea=>int=>rea

(add-computation-rules
 "rea**(IntP One)" "rea"
 "rea1**(IntP(SZero pos2))" "(rea1**(IntP pos2))*(rea1**(IntP pos2))"
 "rea1**(IntP(SOne pos2))" "(rea1**(IntP(SZero pos2)))*rea1"
 "rea**IntZero" "RealConstr([n](RatConstr(IntPos One)One))([k]Zero)")

(add-rewrite-rules
 "(RealConstr([n]rat1)([k]Zero))**int2" "RealConstr([n]rat1**int2)([k]Zero)")


;; 4.  Adding external code
;; ========================

;; We want to view RatPlus, RatMinus, RatTimes, RatDiv, RatLt, RatLe as
;; program constants with external code, using add-external-code.  The
;; external code - after evaluation and application to tsubst and the
;; arguments - should give either the final value (e.g., the numeral
;; for the sum) or else #f, in which case the rules are tried next on
;; the arguments.

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
