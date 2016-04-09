;; 2016-04-02.  pos.scm.  Based on the former numbers.scm.

;; (load "~/git/minlog/init.scm")
;; (set! COMMENT-FLAG #f)
;; (libload "nat.scm")
;; (libload "pos.scm")
;; (set! COMMENT-FLAG #t)

(if (not (assoc "nat" ALGEBRAS))
    (myerror "First execute (libload \"nat.scm\")"))

(display "loading pos.scm ...") (newline)

(remove-var-name "k")

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

;; 1.  Positive numbers
;; ====================

;; We want to overload operators like +,*,/,<=,<, and automatically
;; raise the type of arguments when reading.  For instance, + should
;; take its arguments, compute the lub rho of their types, raise the
;; type of both arguments to type rho, apply RhoPlus to the results.
;; Moreover, a number should be displayed at the lowest possible level.

(add-algs "pos" '("One" "pos") '("SZero" "pos=>pos") '("SOne" "pos=>pos"))
(add-totality "pos")
(add-mr-ids "TotalPos")

;; PosTotalVar
(set-goal "all pos TotalPos pos")
(use "AllTotalIntro")
(assume "pos^" "Tpos")
(use "Tpos")
;; Proof finished.
(save "PosTotalVar")

;; (cdp (proof-to-soundness-proof))
;; Uses the axiom AllTotalIntroSound.

;; Alternative proof:
;; (set-goal "all pos TotalPos pos")
;; (ind)
;; (use "TotalPosOne")
;; (assume "pos" "Tpos")
;; (use "TotalPosSZero")
;; (use "Tpos")
;; (assume "pos" "Tpos")
;; (use "TotalPosSOne")
;; (use "Tpos")

;; PosEqToEqD
(set-goal "all pos1,pos2(pos1=pos2 -> pos1 eqd pos2)")
(ind) ;2-4
(cases) ;5-7
(assume "Useless")
(use "InitEqD")
;; 6
(assume "pos1" "1=SZero p1")
(use "EfqEqD")
(use "1=SZero p1")
;; 7
(assume "pos1" "1=SOne p1")
(use "EfqEqD")
(use "1=SOne p1")
;; 3
(assume "pos1" "IH1")
(cases) ;14-16
(assume "SZero p1=1")
(use "EfqEqD")
(use "SZero p1=1")
;; 15
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
(use "EfqEqD")
(use "SZero p1=SOne p2")
;; 4
(assume "pos1" "IH1")
(cases) ;29-31
(assume "SOne p1=1")
(use "EfqEqD")
(use "SOne p1=1")
;; 30
(assume "pos2" "SOne p1=SZero p2")
(use "EfqEqD")
(use "SOne p1=SZero p2")
;; 31
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

;; make-numeric-term-wrt-pos produces a pos object for a positive
;; integer.

(define (make-numeric-term-wrt-pos n)
  (cond ((= n 1) (pt "One"))
	((even? n) (make-term-in-app-form
		    (make-term-in-const-form (constr-name-to-constr "SZero"))
		    (make-numeric-term-wrt-pos (/ n 2))))
	((odd? n) (make-term-in-app-form
		   (make-term-in-const-form (constr-name-to-constr "SOne"))
		   (make-numeric-term-wrt-pos (/ (- n 1) 2))))
	(else
	 (myerror "make-numeric-term-wrt-pos" "positive integer expected" n))))

(define (make-numeric-term n)
  (if NAT-NUMBERS
      (make-numeric-term-wrt-nat n)
      (make-numeric-term-wrt-pos n)))

;; (define (make-numeric-term n)
;;   (if (not (and (integer? n) (positive? n)))
;;       (myerror "make-numeric-term" "positive integer expected" n)
;;       (make-numeric-term-wrt-pos n)))
(define is-numeric-term? is-numeric-term-wrt-pos?)
(define numeric-term-to-number numeric-term-wrt-pos-to-number)

;; To use external code in a pconst, we provide tests for numeral
;; values and conversion operations from numerals values to numbers,
;; for pos and nat.

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

;; 2. Parsing and display for arithmetical operations
;; ==================================================

;; We have the subtype relation pos < nat.

(add-program-constant "PosToNat" (py "pos=>nat"))

(define (add-item-to-algebra-edge-to-embed-term-alist
         alg1-name alg2-name embed-term)
  (set! ALGEBRA-EDGE-TO-EMBED-TERM-ALIST
        (cons (list (list (make-alg alg1-name) (make-alg alg2-name))
		    embed-term)
              ALGEBRA-EDGE-TO-EMBED-TERM-ALIST)))

(add-item-to-algebra-edge-to-embed-term-alist
 "pos" "nat"
 (let ((var (make-var (make-alg "pos") -1 t-deg-one "")))
   (make-term-in-abst-form
    var (make-term-in-app-form
         (make-term-in-const-form
          (pconst-name-to-pconst "PosToNat"))
         (make-term-in-var-form var)))))

;; (alg-le? (make-alg "pos") (make-alg "nat"))
;; (alg-le? (make-alg "nat") (make-alg "pos"))

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

(replace-item-in-algebra-edge-to-embed-term-alist
 "pos" "nat"
 (let ((var (make-var (make-alg "pos") -1 t-deg-one "")))
   (make-term-in-abst-form
    var (make-term-in-app-form
	 (make-term-in-const-form
	  (pconst-name-to-pconst "PosToNat"))
	 (make-term-in-var-form var)))))

(add-program-constant "PosS" (py "pos=>pos"))
(add-program-constant "PosPred" (py "pos=>pos"))
(add-program-constant "PosHalf" (py "pos=>pos"))

;; We define an overloaded addition.

(add-program-constant "PosPlus" (py "pos=>pos=>pos"))

;; We define a cut-off subtraction for pos (as we have it for nat).

(add-program-constant "PosMinus" (py "pos=>pos=>pos"))

;; We define an overloaded multiplication.

(add-program-constant "PosTimes" (py "pos=>pos=>pos"))

;; We define the exponential with values in pos and nat

(add-program-constant "PosExp" (py "pos=>nat=>pos"))
(add-program-constant "NatExp" (py "nat=>nat=>nat"))

;; We define the overloaded maximum function, written infix:

(add-program-constant "PosMax" (py "pos=>pos=>pos"))

;; We define the overloaded minimum function, written infix:

(add-program-constant "PosMin" (py "pos=>pos=>pos"))

;; We define an overloaded less-than relation.

(add-program-constant "PosLt" (py "pos=>pos=>boole"))

;; We define an overloaded less-than-or-equal relation.

(add-program-constant "PosLe" (py "pos=>pos=>boole"))

;; Program constants used for extraction of program constants to
;; Haskell, where computation rules
;;
;;    f (SZero x) = ... x ...
;
;; must be transformed into
;;    f n | even n = ... TranslationPosHalfEven n ...
;;
;; etc.  Notice that we always know that n is an even number, so that
;; the remainder is zero, and similarly for minus and predecessor. Not
;; meant to be used directly by the user.

(add-program-constant "TranslationPosHalfEven" (py "pos=>pos"))
(add-program-constant "TranslationPosNegForInt" (py "pos=>pos"))
(add-program-constant "TranslationPosPredNonOne" (py "pos=>pos"))

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

(add-token "--" 'add-op (make-term-creator "--" "pos"))
(add-token-and-type-to-name "--" (py "pos") "PosMinus")
(add-token-and-type-to-name "--" (py "nat") "NatMinus")

(add-token "*" 'mul-op (make-term-creator "*" "pos"))
(add-token-and-type-to-name "*" (py "pos") "PosTimes")
(add-token-and-type-to-name "*" (py "nat") "NatTimes")

(add-token "**" 'exp-op (make-term-creator-exp "**"))

(add-token-and-types-to-name "**" (list (py "pos") (py "pos")) "PosExp")
(add-token-and-types-to-name "**" (list (py "pos") (py "nat")) "PosExp")

(add-token-and-types-to-name "**" (list (py "nat") (py "pos")) "NatExp")
(add-token-and-types-to-name "**" (list (py "nat") (py "nat")) "NatExp")

(add-token "max" 'mul-op (make-term-creator "max" "pos"))
(add-token-and-type-to-name "max" (py "pos") "PosMax")
(add-token-and-type-to-name "max" (py "nat") "NatMax")

(add-token "min" 'mul-op (make-term-creator "min" "pos"))
(add-token-and-type-to-name "min" (py "pos") "PosMin")
(add-token-and-type-to-name "min" (py "nat") "NatMin")

(add-token "<" 'rel-op (make-term-creator "<" "pos"))
(add-token-and-type-to-name "<" (py "pos") "PosLt")
(add-token-and-type-to-name "<" (py "nat") "NatLt")

(add-token "<=" 'rel-op (make-term-creator "<=" "pos"))
(add-token-and-type-to-name "<=" (py "pos") "PosLe")
(add-token-and-type-to-name "<=" (py "nat") "NatLe")

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

(add-display (py "pos") (make-display-creator "PosMinus" "--" 'add-op))
(add-display (py "nat") (make-display-creator "NatMinus" "--" 'add-op))

(add-display (py "pos") (make-display-creator "PosTimes" "*" 'mul-op))
(add-display (py "nat") (make-display-creator "NatTimes" "*" 'mul-op))

(add-display (py "pos") (make-display-creator "PosExp" "**" 'exp-op))
(add-display (py "nat") (make-display-creator "NatExp" "**" 'exp-op))

(add-display (py "pos") (make-display-creator "PosMax" "max" 'mul-op))
(add-display (py "nat") (make-display-creator "NatMax" "max" 'mul-op))

(add-display (py "pos") (make-display-creator "PosMin" "min" 'mul-op))
(add-display (py "nat") (make-display-creator "NatMin" "min" 'mul-op))

(add-display (py "boole") (make-display-creator "PosLt" "<" 'rel-op))
(add-display (py "boole") (make-display-creator "NatLt" "<" 'rel-op))

(add-display (py "boole") (make-display-creator "PosLe" "<=" 'rel-op))
(add-display (py "boole") (make-display-creator "NatLe" "<=" 'rel-op))

;; 3. Arithmetic for positive numbers
;; ==================================

(add-var-name "p" "q" (py "pos"))

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

;; (cdp (proof-to-soundness-proof))
;; (proof-to-expr-with-formulas (np (proof-to-soundness-proof)))

;; Code discarded 2016-04-02.
;; Theorems like PosEqTotalReal PosPlusTotalReal removed.  They were
;; designed for use in proof-to-soundness-proof at theorem like
;; PosEqTotal PosPlusTotal.  But proof-to-soundness-proof should not
;; use soundness proofs for theorems of the form Pconst+Total and
;; AlgEqTotal: these proofs have terms involving Rec as content, but
;; proof-to-extracted-term assigns Pconst or identities to them.

;; (display-idpc "TotalBooleMR")

;; ;; PosEqTotalReal
;; (set-goal (rename-variables
;; 	   (real-and-formula-to-mr-formula
;; 	    (pt "[p,q]p=q")
;; 	    (proof-to-formula (theorem-name-to-proof "PosEqTotal")))))
;; (assume "p^" "p^0" "TMRp0p")
;; (elim "TMRp0p")
;; (assume "q^" "q^0" "TMRq0q")
;; (elim "TMRq0q")
;; (use "TotalBooleTrueMR")
;; (assume "q^1" "q^10" "Useless1" "Useless2")
;; (use "TotalBooleFalseMR")
;; (assume "q^1" "q^10" "Useless1" "Useless2")
;; (use "TotalBooleFalseMR")

;; (assume "q^" "q^0" "Useless1" "IH" "q^1" "q^10" "TMRq10q1")
;; (elim "TMRq10q1")
;; (use "TotalBooleFalseMR")
;; (assume "q^2" "q^20" "TMRq20q2" "Useless2")
;; (use "IH")
;; (use "TMRq20q2")
;; (assume "q^2" "q^20" "TMRq20q2" "Useless2")
;; (use "TotalBooleFalseMR")

;; (assume "q^" "q^0" "Useless1" "IH" "q^1" "q^10" "TMRq10q1")
;; (elim "TMRq10q1")
;; (use "TotalBooleFalseMR")
;; (assume "q^2" "q^20" "TMRq20q2" "Useless2")
;; (use "TotalBooleFalseMR")
;; (assume "q^2" "q^20" "TMRq20q2" "Useless2")
;; (use "IH")
;; (use "TMRq20q2")
;; ;; Proof finished.
;; (save "PosEqTotalReal")

;; (pp (rename-variables (nt (proof-to-extracted-term "PosEqTotal"))))
;; ;; =

;; ;; Hence we are allowed to change the extracted term of PosEqTotal into
;; ;; [n,m]n=m.  Then proof-to-soundness-proof at FinAlgEqTotal looks for
;; ;; FinAlgEqTotalReal and uses it.  An error is raised if
;; ;; FinAlgEqTotalReal does not exist.

;; (pp (theorem-to-extracted-term (theorem-name-to-aconst "PosEqTotal")))
;; [p^,q^]p^ =q^

;; Rules for PosS

(add-computation-rules
 "PosS One" "SZero One"
 "PosS(SZero pos)" "SOne pos"
 "PosS(SOne pos)" "SZero(PosS pos)")

;; PosSTotal
(set-totality-goal "PosS")
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
(save-totality)

;; (define sproof (proof-to-soundness-proof "PosSTotal"))
;; (cdp sproof)
;; (pp (rename-variables (proof-to-formula sproof)))
;; (proof-to-expr-with-formulas sproof)
;; (define nsproof (np sproof))
;; (proof-to-expr-with-formulas nsproof)
;; (pp (rename-variables (proof-to-formula nsproof)))
;; (pp (rename-variables (nf (proof-to-formula nsproof))))

;; all p^,p^0(TotalPosMR p^0 p^ -> TotalPosMR(PosS p^0)(PosS p^))

;; Code discarded 2016-04-02
;; ;; PosSTotalReal
;; (set-goal (rename-variables
;; 	   (real-and-formula-to-mr-formula
;; 	    (pt "PosS")
;; 	    (proof-to-formula (theorem-name-to-proof "PosSTotal")))))
;; (assume "p^" "p^0" "TMRp0p")
;; (elim "TMRp0p")
;; (use "TotalPosSZeroMR")
;; (use "TotalPosOneMR")
;; (assume "q^" "q^0" "TMRq0q" "IH")
;; (use "TotalPosSOneMR")
;; (use "TMRq0q")
;; (assume "q^" "q^0" "TMRq0q" "IH")
;; (ng #t)
;; (use "TotalPosSZeroMR")
;; (use "IH")
;; ;; Proof finished.
;; (save "PosSTotalReal")

;; ;; (pp (theorem-to-extracted-term (theorem-name-to-aconst "PosSTotal")))
;; ;; PosS

;; ;; Both PosS and [p^0](Rec pos=>pos)p^0 2([p1,p2]SOne p1)([p1]SZero)
;; ;; are realizers for the formula of the theorem PosSTotal.
;; ;; theorem-to-extracted-term picks PosS, whereas extraction from the
;; ;; proof of PosSTotal gives the latter term with Rec.

;; (proof-to-expr-with-formulas "PosSTotalReal")
;; ;; simpler than et(nsproof).

;; (pp (rename-variables
;;      (proof-to-formula (theorem-name-to-proof "PosSTotalReal"))))
;; ;; allnc p^,p^0(TotalPosMR p^0 p^ --> TotalPosMR(PosS p^0)(PosS p^))
;; ;; Also simpler than the formula of sproof.

;; ;; Correctness of PosS as realizer for PosSTotal is verified by
;; ;; PosSTotalReal.  Therefore proof-to-soundness-proof at theorem
;; ;; PosSTotal should use the theorem PosSTotalReal, and similarly for
;; ;; other pconsts.

;; (pp (rename-variables (proof-to-extracted-term "PosSTotal")))

;; Rules for PosPred

(add-computation-rules
 "PosPred One" "One"
 "PosPred(SZero One)" "One"
 "PosPred(SZero(SZero pos))" "SOne(PosPred(SZero pos))"
 "PosPred(SZero(SOne pos))" "SOne(SZero pos)"
 "PosPred(SOne pos)" "SZero pos")

;; PosPredTotal
(set-totality-goal "PosPred")
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
(save-totality)

;; Code discarded 2016-04-02
;; ;; PosPredTotalReal
;; (set-goal (rename-variables
;; 	   (real-and-formula-to-mr-formula
;; 	    (pt "PosPred")
;; 	    (proof-to-formula (theorem-name-to-proof "PosPredTotal")))))
;; (assume "p^" "p^0" "TMRp0p")
;; (elim "TMRp0p")
;; (use "TotalPosOneMR")

;; (assume "q^" "q^0" "TMRq0q" "IH")
;; (elim "TMRq0q")
;; (use "TotalPosOneMR")
;; (assume "q^2" "q^20" "TMRq20q2" "IH2")
;; (ng #t)
;; (use "TotalPosSOneMR")
;; (use "IH2")
;; (assume "q^2" "q^20" "TMRq20q2" "Useless")
;; (ng #t)
;; (use "TotalPosSOneMR")
;; (use "TotalPosSZeroMR")
;; (use "TMRq20q2")

;; (assume "q^" "q^0" "TMRq0q" "IH")
;; (ng #t)
;; (use "TotalPosSZeroMR")
;; (use "TMRq0q")
;; ;; Proof finished.
;; (save "PosPredTotalReal")

;; Rules for PosHalf

(add-computation-rules
 "PosHalf One" "One"
 "PosHalf(SZero pos)" "pos"
 "PosHalf(SOne pos)" "pos")

;; PosHalfTotal
(set-totality-goal "PosHalf")
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
(save-totality)

;; Rules for PosToNat

(add-computation-rules
 "PosToNat One" "Succ Zero"
 "PosToNat(SZero pos)" "NatDouble(PosToNat pos)"
 "PosToNat(SOne pos)" "Succ(PosToNat(SZero pos))")

;; PosToNatTotal
(set-totality-goal "PosToNat")
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
(save-totality)

;; PosToNatDefSZero is obsolete.  Use PosToNat1CompRule instead.
;; (set-goal "all pos PosToNat(SZero pos)=NatDouble(PosToNat pos)")
;; (assume "pos")
;; (use "Truth")
;; ;; Proof finished.
;; (save "PosToNatDefSZero")

;; PosToNatDefSOne is obsolete.  Use PosToNat2CompRule instead.
;; (set-goal "all pos PosToNat(SOne pos)=Succ(PosToNat(SZero pos))")
;; (assume "pos")
;; (use "Truth")
;; ;; Proof finished.
;; (save "PosToNatDefSOne")

;; We define the inverse NatToPos of PosToNat , using GRec

(add-program-constant "NatToPosStep" (py "nat=>(nat=>pos)=>pos"))

;; Rules for NatToPosStep

(add-computation-rules
 "NatToPosStep nat(nat=>pos)"
 "[if (NatEven nat)
      (SZero((nat=>pos)(NatHalf nat)))
      [if (nat=Succ Zero) One (SOne((nat=>pos)(NatHalf nat)))]]")

;; NatToPosStepTotal
(set-totality-goal "NatToPosStep")
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
(save-totality)

(add-program-constant "NatToPos" (py "nat=>pos"))

;; Rules for NatToPos

(add-computation-rules
 "NatToPos nat" "(GRec nat pos)([nat]nat)nat NatToPosStep")

;; NatToPosTotal
(set-totality-goal  "NatToPos")
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
(save-totality)

;; NatToPosDef
(set-goal "all nat NatToPos nat=(GRec nat pos)([nat]nat)nat NatToPosStep")
(assume "nat")
(use "Truth")
;; Proof finished
(save "NatToPosDef")

;; Rules for PosPlus

(add-computation-rules
 "pos1+One" "PosS pos1"
 "One+SZero pos1" "SOne pos1"
 "SZero pos1+SZero pos2" "SZero(pos1+pos2)"
 "SOne pos1+SZero pos2" "SOne(pos1+pos2)"
 "One+SOne pos1" "SZero(PosS pos1)"
 "SZero pos1+SOne pos2" "SOne(pos1+pos2)"
 "SOne pos1+SOne pos2" "SZero(PosS(pos1+pos2))")

;; PosPlusTotal
(set-totality-goal "PosPlus")
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
(save-totality)

;; Code discarded 2016-04-02
;; ;; PosPlusTotalReal
;; (set-goal (rename-variables
;; 	   (real-and-formula-to-mr-formula
;; 	    (pt "PosPlus")
;; 	    (proof-to-formula (theorem-name-to-proof "PosPlusTotal")))))
;; (assume "p^" "p^0" "TMRp0p")
;; (elim "TMRp0p")
;; (assume "q^" "q^0" "TMRq0q")
;; (elim "TMRq0q")
;; (use "TotalPosSZeroMR")
;; (use "TotalPosOneMR")
;; (assume "q^1" "q^10" "TMRq10q1" "IH")
;; (ng #t)
;; (use "TotalPosSOneMR")
;; (use "TMRq10q1")
;; (assume "q^1" "q^10" "TMRq10q1" "IH")
;; (ng #t)
;; (use "TotalPosSZeroMR")
;; (use "PosSTotalReal")
;; (use "TMRq10q1")

;; ;; ?_4:allnc pos^,pos^0(
;; ;;      TotalPosMR pos^0 pos^ -->
;; ;;      allnc p^,p^0(TotalPosMR p^0 p^ --> TotalPosMR(pos^0+p^0)(pos^ +p^)) ->
;; ;;      allnc p^,p^0(
;; ;;       TotalPosMR p^0 p^ --> TotalPosMR(SZero pos^0+p^0)(SZero pos^ +p^)))
;; (assume "p^1" "p^10" "TMRp10p1" "IHp1" "q^" "q^0" "TMRq0q")
;; (elim "TMRq0q")
;; (ng #t)
;; (use "TotalPosSOneMR")
;; (use "TMRp10p1")

;; (assume "q^1" "q^10" "TMRq10q1" "IHq1")
;; (ng #t)
;; (use "TotalPosSZeroMR")
;; (use "IHp1")
;; (use "TMRq10q1")

;; (assume "q^1" "q^10" "TMRq10q1" "IHq1")
;; (ng #t)
;; (use "TotalPosSOneMR")
;; (use "IHp1")
;; (use "TMRq10q1")

;; ;; ?_5:allnc pos^,pos^0(
;; ;;      TotalPosMR pos^0 pos^ -->
;; ;;      allnc p^,p^0(TotalPosMR p^0 p^ --> TotalPosMR(pos^0+p^0)(pos^ +p^)) ->
;; ;;      allnc p^,p^0(
;; ;;       TotalPosMR p^0 p^ --> TotalPosMR(SOne pos^0+p^0)(SOne pos^ +p^)))

;; (assume "p^1" "p^10" "TMRp10p1" "IHp1" "q^" "q^0" "TMRq0q")
;; (elim "TMRq0q")
;; (ng #t)
;; (use "TotalPosSZeroMR")
;; (use "PosSTotalReal")
;; (use "TMRp10p1")

;; (assume "q^1" "q^10" "TMRq10q1" "IHq1")
;; (ng #t)
;; (use "TotalPosSOneMR")
;; (use "IHp1")
;; (use "TMRq10q1")

;; (assume "q^1" "q^10" "TMRq10q1" "IHq1")
;; (ng #t)
;; (use "TotalPosSZeroMR")
;; (use "PosSTotalReal")
;; (use "IHp1")
;; (use "TMRq10q1")
;; ;; Proof finished.
;; (save "PosPlusTotalReal")

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
(use "CVIndPvar")
(assume "Absurd")
(strip)
(use "EfqAtom")
(use "Absurd")
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
(use "CVIndPvar")
(assume "Absurd")
(strip)
(use "EfqAtom")
(use "Absurd")
(assume "nat" "Prog" "0<nat")
(cases (pt "NatEven nat")) ;8,9
(assume "Enat")
(assert "NatToPos nat=SZero(NatToPos(NatHalf nat))")
 (use "NatToPosEqSZeroNatToPosHalf")
 (use "0<nat")
 (use "Enat")
(assume "NatToPos nat=SZero(NatToPos(NatHalf nat))")
(simp "NatToPos nat=SZero(NatToPos(NatHalf nat))")
(simp "PosToNat1CompRule")
(simp "Prog")
(use "NatDoubleHalfEven")
(use "Enat")
(use "NatLtZeroHalfEven")
(use "0<nat")
(use "Enat")
(use "NatHalfLt")
(use "0<nat")
;; 9
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
(simp "PosToNat2CompRule")
(cases (pt "nat"))
(assume "nat=0")
(use "EfqAtom")
(simphyp-with-to "NatEven nat -> F" "nat=0" "Absurd")
(use "Absurd")
(use "Truth")
(assume "nat1" "nat=Succ nat1")
(simp "PosToNat1CompRule")
(assert "NatEven nat1")
(use "NatOddSuccToEven")
(simp "<-" "nat=Succ nat1")
(use "NatEven nat -> F")
(assume "Enat1")
(simp "NatHalfSuccEven")
(assert "PosToNat(SZero(NatToPos(NatHalf nat1)))=nat1")
 (simp "PosToNat1CompRule")
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
(ind) 
;; 2-4
(ng #t)
(use "Truth")
;; 3
(assume "pos" "IH")
(ng #t)
(simp "NatEvenDouble")
(ng #t)
(assert "Zero<NatDouble(PosToNat pos)")
 (ind (pt "pos"))
 (use "Truth")
 (assume "pos1" "IH1")
 (ng #t)
 (use "NatLt0Double")
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
(assert "Zero<NatDouble(PosToNat pos)")
 (use "NatLt0Double")
 (use "NatLt0Pos")
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

;; PosToNatInj
(set-goal "all pos1,pos2(PosToNat pos1=PosToNat pos2 -> pos1=pos2)")
(assume "pos1" "pos2" "EqHyp")
(assert "NatToPos(PosToNat pos1)=NatToPos(PosToNat pos2)")
 (simp "EqHyp")
 (use "Truth")
 (simp "NatToPosToNatId")
 (simp "NatToPosToNatId")
(assume "p1=p2")
(use "p1=p2")
;; Proof finished.
(save "PosToNatInj")

;; NatLt0PosToNat
(set-goal "all pos Zero<PosToNat pos")
(ind)
;; 2-4
(use "Truth")
;; 3
(assume "pos" "IH")
(ng)
(use "NatLt0Double")
(use "IH")
;; 4
(assume "pos" "IH")
(use "Truth")
;; Proof finished.
(save "NatLt0PosToNat")

;; SuccPosS
(set-goal "all nat(Zero<nat -> NatToPos(Succ nat)=PosS(NatToPos nat))")
(assert "all nat(Zero<nat -> Succ nat=PosToNat(PosS(NatToPos nat)))")
(use "CVIndPvar")
(assume "Absurd")
(strip)
(use "EfqAtom")
(use "Absurd")
(assume "nat" "Prog" "0<n")
(cases (pt "NatEven nat")) ;10,11
(assume "En")
(simp "NatToPosEqSZeroNatToPosHalf")
(simp "PosS1CompRule")
(simp "PosToNat2CompRule")
(simp "PosToNat1CompRule")
(simp "PosToNatToPosId")
(simp "NatDoubleHalfEven")
(use "Truth")
(use "En")
(use "NatLtZeroHalfEven")
(use "0<n")
(use "En")
(use "En")
(use "0<n")
;; 11
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
(simp "PosS2CompRule")
(simp "PosToNat1CompRule")
(simp "<-" "Prog")
(simp "NatDouble1CompRule")
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

;; We prove that PosToNat is an isomorphism w.r.t. +

;; PosToNatPlus
(set-goal "all pos1,pos2 PosToNat(pos1+pos2)=PosToNat pos1+PosToNat pos2")
(ind) 
;; 2-4
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

;; The rules for PosMinus will give correct results for p--q (only) if
;; q<p.  To be able to formulate appropriate assumptions we postpone
;; the treatment of PosMinus until after PosLe and PosLt.

;; Rules for PosTimes:

(add-computation-rules
 "pos*One" "pos"
 "pos1*SZero pos2" "SZero(pos1*pos2)"
 "pos1*SOne pos2" "SZero(pos1*pos2)+pos1")

;; PosTimesTotal
(set-totality-goal "PosTimes")
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
(save-totality)

;; Code discarded 2016-04-02
;; ;; PosTimesTotalReal
;; (set-goal (rename-variables
;; 	   (real-and-formula-to-mr-formula
;; 	    (pt "PosTimes")
;; 	    (proof-to-formula (theorem-name-to-proof "PosTimesTotal")))))
;; (assume "p^" "p^0" "TMRp0p" "q^" "q^0" "TMRq0q")
;; (elim "TMRq0q")
;; (use "TMRp0p")
;; (assume "q^1" "q^10" "Useless" "IHq1")
;; (ng #t)
;; (use "TotalPosSZeroMR")
;; (use "IHq1")
;; (assume "q^1" "q^10" "Useless" "IHq1")
;; (ng #t)
;; (use "PosPlusTotalReal")
;; (use "TotalPosSZeroMR")
;; (use "IHq1")
;; (use "TMRp0p")
;; ;; Proof finished.
;; (save "PosTimesTotalReal")

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
(use "Truth")
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

;; PosTimesPlusDistr
(set-goal "all pos1,pos2,pos3 pos1*(pos2+pos3)=pos1*pos2+pos1*pos3")
(assume "pos1" "pos2" "pos3")
(assert "pos1*(pos2+pos3)=NatToPos(PosToNat(pos1*(pos2+pos3)))")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "EqHyp1")
(simp "EqHyp1")
(assert "pos1*pos2+pos1*pos3=NatToPos(PosToNat(pos1*pos2+pos1*pos3))")
 (simp "NatToPosToNatId")
 (use "Truth")
(assume "EqHyp2")
(simp "EqHyp2")
(simp "PosToNatTimes")
(simp "PosToNatPlus")
(simp "PosToNatPlus")
(simp "PosToNatTimes")
(simp "PosToNatTimes")
(simp "NatTimesPlusDistr")
(use "Truth")
;; Proof finished.
(save "PosTimesPlusDistr")
(add-rewrite-rule "pos1*(pos2+pos3)" "pos1*pos2+pos1*pos3")

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

;; PosTimesPlusDistrLeft
(set-goal "all pos1,pos2,pos3 (pos1+pos2)*pos3=(pos1*pos3)+(pos2*pos3)")
(assume "pos1" "pos2" "pos3")
(simp-with "PosTimesComm" (pt "pos1+pos2") (pt "pos3"))
(ng)
(simp-with "PosTimesComm" (pt "pos1") (pt "pos3"))
(simp-with "PosTimesComm" (pt "pos2") (pt "pos3"))
(use "Truth")
;; Proof finished.
(save "PosTimesPlusDistrLeft")
(add-rewrite-rule "(pos1+pos2)*pos3" "pos1*pos3+pos2*pos3")

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
(set-totality-goal "PosExp")
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
(save-totality)

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
(set-totality-goal "PosLt")
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
(save-totality)

;; PosLeTotal
(set-totality-goal "PosLe")
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

;; Code discarded 2016-04-02
;; ;; PosLtPosLeTotalRealLemma
;; (set-goal "allnc p^,p^0(
;;  TotalPosMR p^0 p^ -->
;;  allnc q^,q^0(
;;   TotalPosMR q^0 q^ -->
;;   TotalBooleMR(p^0<q^0)(p^ <q^) andu TotalBooleMR(p^0<=q^0)(p^ <=q^)))")
;; (assume "p^" "p^0" "TMRp0p")
;; (elim "TMRp0p")
;; (assume "q^" "q^0" "TMRq0q")
;; (elim "TMRq0q")
;; (split)
;; (use "TotalBooleFalseMR")
;; (use "TotalBooleTrueMR")
;; (assume "q^1" "q^10" "TMRq10q1" "IHq1")
;; (split)
;; (use "TotalBooleTrueMR")
;; (use "TotalBooleTrueMR")
;; (assume "q^1" "q^10" "TMRq10q1" "IHq1")
;; (split)
;; (use "TotalBooleTrueMR")
;; (use "TotalBooleTrueMR")

;; (assume "p^1" "p^10" "TMRp10p1" "IHp1" "q^" "q^0" "TMRq0q")
;; (elim "TMRq0q")
;; (split)
;; (use "TotalBooleFalseMR")
;; (use "TotalBooleFalseMR")
;; (assume "q^1" "q^10" "TMRq10q1" "IHq1")
;; (ng #t)
;; (use "IHp1")
;; (use "TMRq10q1")
;; (assume "q^1" "q^10" "TMRq10q1" "IHq1")
;; (ng #t)
;; (split)
;; (use "IHp1")
;; (use "TMRq10q1")
;; (use "IHp1")
;; (use "TMRq10q1")

;; ;; ?_5:allnc pos^,pos^0(
;; ;;      TotalPosMR pos^0 pos^ -->
;; ;;      allnc q^,q^0(
;; ;;       TotalPosMR q^0 q^ -->
;; ;;       TotalBooleMR(pos^0<q^0)(pos^ <q^) andu
;; ;;       TotalBooleMR(pos^0<=q^0)(pos^ <=q^)) ->
;; ;;      allnc q^,q^0(
;; ;;       TotalPosMR q^0 q^ -->
;; ;;       TotalBooleMR(SOne pos^0<q^0)(SOne pos^ <q^) andu
;; ;;       TotalBooleMR(SOne pos^0<=q^0)(SOne pos^ <=q^)))
;; (assume "p^1" "p^10" "TMRp10p1" "IHp1" "q^" "q^0" "TMRq0q")
;; (elim "TMRq0q")
;; (split)
;; (use "TotalBooleFalseMR")
;; (use "TotalBooleFalseMR")
;; (assume "q^1" "q^10" "TMRq10q1" "IHq1")
;; (ng #t)
;; (split)
;; (use "IHp1")
;; (use "TMRq10q1")
;; (use "IHp1")
;; (use "TMRq10q1")
;; (assume "q^1" "q^10" "TMRq10q1" "IHq1")
;; (ng #t)
;; (use "IHp1")
;; (use "TMRq10q1")
;; ;; Proof finished.
;; (save "PosLtPosLeTotalRealLemma")

;; ;; (display-pconst "PosLt")
;; ;; (display-pconst "PosLe")

;; ;; PosLtTotalReal
;; (set-goal (rename-variables
;; 	   (real-and-formula-to-mr-formula
;; 	    (pt "PosLt")
;; 	    (proof-to-formula (theorem-name-to-proof "PosLtTotal")))))
;; (assume "p^" "p^0" "TMRp0p" "q^" "q^0" "TMRq0q")
;; (use "PosLtPosLeTotalRealLemma")
;; (use "TMRp0p")
;; (use "TMRq0q")
;; ;; Proof finished.
;; (save "PosLtTotalReal")

;; ;; PosLeTotalReal
;; (set-goal (rename-variables
;; 	   (real-and-formula-to-mr-formula
;; 	    (pt "PosLe")
;; 	    (proof-to-formula (theorem-name-to-proof "PosLeTotal")))))
;; (assume "p^" "p^0" "TMRp0p" "q^" "q^0" "TMRq0q")
;; (use "PosLtPosLeTotalRealLemma")
;; (use "TMRp0p")
;; (use "TMRq0q")
;; ;; Proof finished.
;; (save "PosLeTotalReal")

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

;; PosLeToEq
(set-goal "all pos (pos<=1)=(pos=1)")
(cases)
(use "Truth")
(assume "pos")
(use "Truth")
(assume "pos")
(use "Truth")
;; Proof finished.
(save "PosLeToEq")
(add-rewrite-rule "pos<=1" "pos=1")

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
(cases)
(use "Truth")
(assume "pos")
(ng)
(use "Truth")
(assume "pos")
(ng)
(use "Truth")
;; Proof finished.
(add-rewrite-rule "PosS pos<pos" "False")

(set-goal "all pos1,pos2 pos1<=pos1+pos2")
(ind)
(cases)
(use "Truth")
(assume "pos2")
(ng)
(use "Truth")
(assume "pos2")
(ng)
(use "Truth")
;; 3
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
(use "PosLeLtTrans" (pt "pos1+pos2"))
(use "IH1")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "pos1<=pos1+pos2" "True")

(set-goal "all pos1,pos2 pos1<pos1+pos2")
(ind)
(cases)
(use "Truth")
(assume "pos2")
(ng)
(use "Truth")
(assume "pos2")
(ng)
(use "Truth")
;; 3
(assume "pos1" "IH1")
(cases)
(ng #t)
(use "Truth")
(assume "pos2")
(ng #t)
(use "IH1")
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

(set-goal "all pos (PosS pos<=1)=False")
(cases)
(use "Truth")
(strip)
(use "Truth")
(strip)
(use "Truth")
;; Proof finished.
(add-rewrite-rule "PosS pos<=1" "False")

(set-goal "all pos1,pos2 (pos1+pos2<=pos1)=False")
(assert "all pos1,pos2(pos1+pos2<=pos1 -> F)")
 (ind) ;4-6
 (ng)
 (cases)
 (assume "Absurd")
 (use "Absurd")
 (assume "pos" "Absurd")
 (use "Absurd")
 (assume "pos" "Absurd")
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
(ng)
(cases)
(use "Truth")
(assume "pos2")
(use "Truth")
(assume "pos2")
(use "Truth")
;; 3
(assume "pos1" "IH1")
(cases)
(ng)
(use "Truth")
(assume "pos2")
(use "Truth")
(assume "pos2")
(use "PosLtPosS")
;; 4
(assume "pos1" "IH1")
(cases)
(ng)
(cases (pt "pos1"))
(strip)
(use "Truth")
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "pos2")
(ng #t)
(use "PosLePosS")
(assume "pos2")
(ng #t)
(use "IH1")
;; Proof finished.
(add-rewrite-rule "PosS pos1<=PosS pos2" "pos1<=pos2")

;; PosSPosPredId
(set-goal "all pos(One<pos -> PosS(PosPred pos)=pos)")
(cases)
;; 2-4
(assume "Absurd")
(use "Absurd")
;; 3
(assume "pos" "Useless")
(ng)
(use "Truth")
;; 4
(assume "pos" "Useless")
(ng)
(use "Truth")
;; Proof finished.
(save "PosSPosPredId")

;; PosLtMonPred
(set-goal "all pos1,pos2(One<pos1 -> pos1<pos2 -> PosPred pos1<PosPred pos2)")
(assume "pos1" "pos2" "1<p1" "p1<p2")
(assert "One<pos2")
 (use "PosLtTrans" (pt "pos1"))
 (use "1<p1")
 (use "p1<p2")
(assume "1<p2")
(simp "<-" "PosLt8RewRule")
(simp "PosSPosPredId")
(simp "PosSPosPredId")
(use "p1<p2")
(use "1<p2")
(use "1<p1")
;; Proof finished.
(save "PosLtMonPred")

;; PosNotLeToLt and PosNotLtToLe are proved using the isomorphic
;; embedding PosToNat of pos into nat.

;; We prove that NatToPos is an isomorphism w.r.t. <= and <.  Main
;; idea: Translate the computation rules for PosLe, PosLt into
;; equational lemmas for NatLe, NatLt with NatDouble nat for SZero pos
;; and Succ(NatDouble nat) for SOne pos.

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
 (use "NatLtOneDouble")
 (use "NatLt0Pos")
(assume "Succ Zero<=NatDouble(PosToNat pos)")
(simp "Succ Zero<=NatDouble(PosToNat pos)")
(use "Truth")
(assert "Succ Zero<NatDouble(PosToNat pos)")
 (use "NatLtOneDouble")
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
 (use "NatLtOneSuccDouble")
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
 (use "NatLeDoubleOne")
 (use "NatLt0Pos")
(assume "NatDouble(PosToNat pos1)<=Succ Zero -> F")
(simp "NatDouble(PosToNat pos1)<=Succ Zero -> F")
(use "Truth")
(assert "NatDouble(PosToNat pos1)<Succ Zero -> F")
 (use "NatLtDoubleOne")
 (use "NatLt0Pos")
(assume "NatDouble(PosToNat pos1)<Succ Zero -> F")
(simp "NatDouble(PosToNat pos1)<Succ Zero -> F")
(use "Truth")
;; 37
(assume "pos2")
(ng #t)
(split)
(simp "NatDoubleLe")
(use "IH1")
(simp "NatDoubleLt")
(use "IH1")
;; 38
(assume "pos2")
(ng #t)
(split)
(simp "NatLeDoubleSuccDouble")
(use "IH1")
(simp "NatLtDoubleSuccDouble")
(use "IH1")
;; 4
(assume "pos1" "IH1")
(cases) ;65-67
(ng #t)
(split)
(assert "NatDouble(PosToNat pos1)=Zero -> F")
 (assume "NatDouble(PosToNat pos1)=Zero")
 (assert "Zero<PosToNat pos1")
  (use "NatLt0Pos")
 (assume "0<pos1")
 (inst-with-to "NatLt0Double" (pt "PosToNat pos1") "0<pos1" "NatLt0DoubleInst")
 (simphyp-with-to "NatLt0DoubleInst" "NatDouble(PosToNat pos1)=Zero" "Absurd")
 (use "Absurd")
(assume "NatDouble(PosToNat pos1)=Zero -> F")
(simp "NatDouble(PosToNat pos1)=Zero -> F")
(use "Truth")
(use "Truth")
;; 66
(assume "pos2")
(ng #t)
(split)
(simp "NatLeSuccDoubleDouble")
(use "IH1")
(simp "NatLtSuccDoubleDouble")
(use "IH1")
;; 67
(assume "pos2")
(ng #t)
(split)
(simp "NatLeSuccDoubleSuccDouble")
(use "IH1")
(simp "NatLtSuccDoubleSuccDouble")
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

;; PosToNatLt
(set-goal "all pos1,pos2 (PosToNat pos1<PosToNat pos2)=(pos1<pos2)")
(assume "pos1" "pos2")
(use "PosToNatLeLt")
;; Proof finished.
(save "PosToNatLt")

;; NatToPosLt
(set-goal "all nat1,nat2(Zero<nat1 -> Zero<nat2 ->
  (NatToPos nat1<NatToPos nat2)=(nat1<nat2))")
(assume "nat1" "nat2" "0<n1" "0<n2")
(simp "<-" "PosToNatLt")
(simp "PosToNatToPosId")
(simp "PosToNatToPosId")
(use "Truth")
(use "0<n2")
(use "0<n1")
;; Proof finished.
(save "NatToPosLt")

;; PosNotLeToLt
(set-goal "all pos1,pos2((pos1<=pos2 -> F) -> pos2<pos1)")
(assume "pos1" "pos2")
(simp "<-" "NatToPosToNatId")
(assert "NatToPos(PosToNat pos2)=pos2")
 (use "NatToPosToNatId")
(assume "NatToPos(PosToNat pos2)=pos2")
(simp "<-" "NatToPos(PosToNat pos2)=pos2")
(simp "NatToPosLe")
(simp "NatToPosLt")
(simp "PosToNatToPosId")
(simp "PosToNatToPosId")
(use "NatNotLeToLt")
(use "NatLt0Pos")
(use "NatLt0Pos")
(use "NatLt0Pos")
(use "NatLt0Pos")
;; Proof finished.
(save "PosNotLeToLt")

;; PosNotLtToLe
(set-goal "all pos1,pos2((pos1<pos2 -> F) -> pos2<=pos1)")
(assume "pos1" "pos2")
(simp "<-" "NatToPosToNatId")
(assert "NatToPos(PosToNat pos2)=pos2")
 (use "NatToPosToNatId")
(assume "NatToPos(PosToNat pos2)=pos2")
(simp "<-" "NatToPos(PosToNat pos2)=pos2")
(simp "NatToPosLe")
(simp "NatToPosLt")
(simp "PosToNatToPosId")
(simp "PosToNatToPosId")
(use "NatNotLtToLe")
(use "NatLt0Pos")
(use "NatLt0Pos")
(use "NatLt0Pos")
(use "NatLt0Pos")
;; Proof finished.
(save "PosNotLtToLe")

;; PosLeAntiSym
(set-goal "all pos1,pos2(pos1<=pos2 -> pos2<=pos1 -> pos1=pos2)")
(assume "pos1" "pos2")
(simp "<-" "PosToNatLe")
(simp "<-" "PosToNatLe")
(assume "NatLeHyp1" "NatLeHyp2")
(assert "PosToNat pos1=PosToNat pos2")
(use "NatLeAntiSym")
(use "NatLeHyp1")
(use "NatLeHyp2")
(use "PosToNatInj")
;; Proof finished.
(save "PosLeAntiSym")

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

;; Since many properties involving PosMinus depend on <-hypotheses
;; we provide PosLtLeMonTimes and PosLeLtMonTimes

;; PosLtLeMonTimes
(set-goal "all pos1,pos2,pos3,pos4(
 pos1<pos2 -> pos3<=pos4 -> pos1*pos3<pos2*pos4)")
(assume "pos1" "pos2" "pos3" "pos4")
(simp "<-" "PosLePosS")
(simp "<-" "PosPlus0CompRule")
(assume "Sp1<=p2" "p3<=p4")
(assert "(pos1+1)*pos3<=pos2*pos4")
 (use "PosLeMonTimes")
 (use "Sp1<=p2")
 (use "p3<=p4")
(assume "(p1+1)p3<=p2p3")
(use "PosLtLeTrans" (pt "(pos1+1)*pos3"))
(simp "PosTimesPlusDistrLeft")
(ng)
(use "Truth")
(use "(p1+1)p3<=p2p3")
;; Proof finished.
(save "PosLtLeMonTimes")

;; PosLeLtMonTimes
(set-goal "all pos1,pos2,pos3,pos4(
 pos1<=pos2 -> pos3<pos4 -> pos1*pos3<pos2*pos4)")
(assume "pos1" "pos2" "pos3" "pos4" "p1<=p2")
(simp "<-" "PosLePosS")
(simp "<-" "PosPlus0CompRule")
(assume "Sp3<=p4")
(assert "pos1*(pos3+1)<=pos2*pos4")
 (use "PosLeMonTimes")
 (use "p1<=p2")
 (use "Sp3<=p4")
(assume "p1*(p3+1)<=p2p4")
(use "PosLtLeTrans" (pt "pos1*(pos3+1)"))
(simp "PosTimesPlusDistr")
(ng)
(use "Truth")
(use "p1*(p3+1)<=p2p4")
;; Proof finished.
(save "PosLeLtMonTimes")

(set-goal "all pos1,pos2,pos3 (pos1*pos3<=pos2*pos3)=(pos1<=pos2)")
(assume "pos1" "pos2" "pos3")
(use "BooleAeqToEq")
;; 3,4
(assume "p1p3<=p2p3")
(use "PosNotLtToLe")
(assume "p2<p1")
(assert "pos2*pos3<pos1*pos3")
 (use "PosLtLeMonTimes")
 (use "p2<p1")
 (use "Truth")
(assume "p2p3<p1p3")
(assert "pos1*pos3<pos1*pos3")
 (use "PosLeLtTrans" (pt "pos2*pos3"))
 (use "p1p3<=p2p3")
 (use "p2p3<p1p3")
(assume "Absurd")
(use "Absurd")
;; 4
(assume "p1<=p2")
(use "PosLeMonTimes")
(use "p1<=p2")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "pos1*pos3<=pos2*pos3" "pos1<=pos2")

;; PosTimesInj
(set-goal "all pos1,pos2,pos3(pos1*pos2=pos1*pos3 -> pos2=pos3)")
(assume "pos1" "pos2" "pos3" "p1p2=p1p3")
(use "PosLeAntiSym")
;; 3,4
(use "PosNotLtToLe")
(assume "p3<p2")
(assert "pos1*pos3<pos1*pos2")
 (use "PosLeLtMonTimes")
 (use "Truth")
 (use "p3<p2")
(simp "p1p2=p1p3")
(assume "Absurd")
(use "Absurd")
;; 4 
(use "PosNotLtToLe")
(assume "p2<p3")
(assert "pos1*pos2<pos1*pos3")
 (use "PosLeLtMonTimes")
 (use "Truth")
 (use "p2<p3")
(simp "p1p2=p1p3")
(assume "Absurd")
(use "Absurd")
;; Proof finished.
(save "PosTimesInj")

;; PosTimesInjLeft
(set-goal "all pos1,pos2,pos3(pos1*pos3=pos2*pos3 -> pos1=pos2)")
(assume "pos1" "pos2" "pos3" "p1p3=p2p3")
(use "PosTimesInj" (pt "pos3"))
(simp "PosTimesComm")
(simp "p1p3=p2p3")
(use "PosTimesComm")
;; Proof finished.
(save "PosTimesInjLeft")

;; PosLtMonTimesInv
(set-goal  "all pos1,pos2,pos3(pos1*pos2<pos1*pos3 -> pos2<pos3)")
(assume "pos1" "pos2" "pos3" "p1p2<p1p3")
(use "PosNotLeToLt")
(assume "p3<=p2")
(assert "pos1*pos3<=pos1*pos2")
 (use "PosLeMonTimes")
 (use "Truth")
 (use "p3<=p2")
(assume "p1p3<=p1p2")
(assert "pos1*pos2<pos1*pos2")
 (use "PosLtLeTrans" (pt "pos1*pos3"))
 (use "p1p2<p1p3")
 (use "p1p3<=p1p2")
(assume "Absurd")
(use "Absurd")
;; Proof finished.
(save "PosLtMonTimesInv")

;; PosLeLtCases
(set-goal "all pos1,pos2((pos1<=pos2 -> Pvar) -> (pos2<pos1 -> Pvar) -> Pvar)")
(assume "pos1" "pos2" "LeHyp" "LtHyp")
(use "NatLeLtCases" (pt "PosToNat pos1") (pt "PosToNat pos2") "?" "?")
;; 3,4
(assume "NatLeHyp")
(use "LeHyp")
(simp "<-" "PosToNatLe")
(use "NatLeHyp")
;; 4
(assume "NatLtHyp")
(use "LtHyp")
(simp "<-" "PosToNatLt")
(use "NatLtHyp")
;; Proof finished.
(save "PosLeLtCases")

;; PosLeCases
(set-goal "all pos1,pos2(
 pos1<=pos2 -> (pos1<pos2 -> Pvar) -> (pos1=pos2 -> Pvar) -> Pvar)")
(assume "pos1" "pos2" "pos1<=pos2" "LtHyp" "EqHyp")
(use "NatLeCases" (pt "PosToNat pos1") (pt "PosToNat pos2") "?" "?" "?")
;; 3-5
(simp "PosToNatLe")
(use "pos1<=pos2")
;; 4
(simp "PosToNatLt")
(use "LtHyp")
;; 5
(assume "EqPosToNatHyp")
(use "EqHyp")
(simp "<-" "NatToPosToNatId")
(simp "EqPosToNatHyp")
(use "NatToPosToNatId")
;; Proof finished.
(save "PosLeCases")

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
(set-totality-goal "PosMinus")
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
(save-totality)

(set-goal "all pos PosS pos--1=pos")
(cases)
(use "Truth")
(assume "pos")
(ng)
(use "Truth")
(assume "pos")
;; PosS(SOne pos)--1=SOne pos
(ng)
;; ?_8:PosPred(SZero(PosS pos))=SOne pos
(use "Truth")
;; Proof finished.
(add-rewrite-rule "PosS pos--1" "pos")

;; We consider the rules for NatMinus.  Do they hold for PosMinus?

;; PosMinusOneEqPosPred
(set-goal "all pos pos--1=PosPred pos")
(cases)
;; 2-4
(use "Truth")
;; 3
(assume "pos")
(use "Truth")
;; 4
(assume "pos")
(use "Truth")
;; Proof finished.
(save "PosMinusOneEqPosPred")

;; The remaining rewrite rules for NatMinus are

;; (set-goal "all nat1,nat2 Pred(Succ nat1--nat2)=nat1--nat2")
;; (set-goal "all nat nat--nat=0")
;; (set-goal "all nat Succ nat--nat=1")
;; (set-goal "all nat 0--nat=0")
;; (set-goal "all nat1,nat2 nat1--nat2<=nat1")
;; (set-goal "all nat1,nat2 nat1+nat2--nat2=nat1")
;; (set-goal "all nat1,nat2 nat2+nat1--nat2=nat1")

;; The second computation rule pos1--PosS pos2=PosPred(pos1--pos2) is
;; wrong for pos1=2 and pos2=1.

;; (pp (nt (pt "2--PosS 1"))) ;2
;; (pp (nt (pt "PosPred(2--1)"))) ;1

;; We need a premise PosS pos2<pos1.  Since the proof is easiest with
;; an ordinary successor induction, we postpone the proof until we
;; have seen the NatToPos and PosToNat are isomorphisms w.r.t. -

;; We prove that PosToNat is an isomorphism w.r.t. -

;; Need that PosToNat is an isomorphism w.r.t. NatDouble and Pred.

;; SuccPosPred
(set-goal "all pos(1<pos -> PosToNat pos=Succ(PosToNat(PosPred pos)))")
(ind)
(assume "Absurd")
(use "Absurd")
;; 3
(cases)
;; 6-8
(ng)
(strip)
(use "Truth")
;; 7
(assume "pos" "IH" "Useless")
(ng)
(simp "IH")
(ng)
(use "Truth")
(use "Truth")
; 8
(assume "pos" "IH" "Useless")
(ng)
(use "Truth")
;; 4
(ng)
(strip)
(use "Truth")
;; Proof finished.
(save "SuccPosPred")

;; PredPosPred
(set-goal "all pos(1<pos -> Pred(PosToNat pos)=PosToNat(PosPred pos))")
(assume "pos" "1<pos")
(simp "SuccPosPred")
(use "Truth")
(use "1<pos")
;; Proof finished.
(save "PredPosPred")

(set-goal "all pos PosPred pos<=pos")
(assume "pos")
(use "PosLeCases" (pt "1") (pt "pos"))
(use "Truth")
(assume "1<pos")
(simp "<-" "PosToNatLe")
(simp "<-" "PredPosPred")
(ng)
(use "Truth")
(use "1<pos")
(assume "1=pos")
(simp "<-" "1=pos")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "PosPred pos<=pos" "True")

;; NatDoubleSZero
(set-goal "NatDouble(PosToNat pos)=PosToNat(SZero pos)")
(ind)
(ng)
(use "Truth")
(assume "pos" "IH")
(ng)
(use "Truth")
(assume "pos" "IH")
(ng)
(use "Truth")
;; Proof finished.
(save "NatDoubleSZero")

;; Now we can prove that PosToNat is an isomorphism w.r.t. -

;; PosToNatMinus
(set-goal "all pos1,pos2(
 pos2<pos1 -> PosToNat(pos1--pos2)=PosToNat pos1--PosToNat pos2)")
(ind)
;; 2-4
(assume "pos2")
(ng #t)
(use "Efq")
;; 3
(assume "pos1" "IH1")
(ind)
;; 8-10
(ng)
;; ?_11:T -> PosToNat(PosPred(SZero pos1))=Pred(NatDouble(PosToNat pos1))
(simp "NatDoubleSZero")
(simp "PredPosPred")
(assume "Useless")
(use "Truth")
(ng)
(use "Truth")
;; 9
(assume "pos2" "IH2" "pos2<pos1")
(ng)
(simp "IH1")
(simp "NatDoubleMinus")
(use "Truth")
(use "pos2<pos1")
;; 10
(ng)
(assume "pos2" "IH2")
(assume "pos2<pos1")
(simp "<-" "NatDoubleMinus")
(simp "<-" "PredPosPred")
(simp "<-" "NatDoubleSZero")
(simp "IH1")
(use "Truth")
(use "pos2<pos1")
(ng)
(use "Truth")
;; 4
(assume "pos1" "IH1")
(ind)
;; 33-35
(ng)
(strip)
(use "Truth")
;; 34
(assume "pos2" "IH2")
(ng)
(assume "pos2<=pos1")
(use "PosLeCases" (pt "pos2") (pt "pos1"))
(use "pos2<=pos1")
(assume "pos2<pos1")
(assert "pos1=pos2 -> pos2<pos2")
 (assume "pos1=pos2")
 (simphyp-with-to "pos2<pos1" "pos1=pos2" "Absurd")
 (use "Absurd")
(assume "pos1=pos2 -> F")
(simp "pos1=pos2 -> F")
(ng #t)
(simp "<-" "SuccNatMinus")
(simp "<-" "NatDoubleMinus")
(ng)
(simp "IH1")
(ng)
(use "Truth")
(use "pos2<pos1")
(simp "NatDoubleLt")
(simp "PosToNatLt")
(use "pos2<pos1")
;; 43
(assume "pos2=pos1")
(simp "pos2=pos1")
(ng)
(use "Truth")
;; 35
(assume "pos2" "IH2" "pos2<pos1")
(ng #t)
(simp "IH1")
(simp "NatDoubleMinus")
(use "Truth")
(use "pos2<pos1")
;; Proof finished.
(save "PosToNatMinus")

;; NatToPosMinus
(set-goal "all nat1,nat2(
 Zero<nat2 -> nat2<nat1 -> NatToPos(nat1--nat2)=NatToPos nat1--NatToPos nat2)")
(assume "nat1" "nat2" "0<nat2" "nat2<nat1")
(assert "Zero<nat1")
 (use "NatLtTrans" (pt "nat2"))
 (use "0<nat2")
 (use "nat2<nat1")
(assume "0<nat1") 
(assert "nat1--nat2=PosToNat(NatToPos nat1)--PosToNat(NatToPos nat2)")
 (simp "PosToNatToPosId")
 (simp "PosToNatToPosId")
 (use "Truth")
 (use "0<nat2")
 (use "0<nat1")
(assume "EqHyp")
(simp "EqHyp")
(simp "<-" "PosToNatMinus")
(simp "NatToPosToNatId")
(use "Truth")
(simp "NatToPosLt")
(use "nat2<nat1")
(use "0<nat1")
(use "0<nat2")
;; Proof finished.
;; Proof finished.
(save "NatToPosMinus")

;; Now we can continue proving the nat rewrite rules for pos

(set-goal "all pos1,pos2 pos1+pos2--pos2=pos1")
(assume "pos1" "pos2")
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
(simp "<-" "NatToPosPlus")
(simp "<-" "NatToPosMinus")
(ng #t)
(use "Truth")
(simp "<-" "PosToNatPlus")
(simp "PosToNatLt")
(ng #t)
(use "Truth")
(use "NatLt0Pos")
(use "NatLt0Pos")
(use "NatLt0Pos")
;; Proof finished.
(add-rewrite-rule "pos1+pos2--pos2" "pos1")

(set-goal "all pos1,pos2 pos2+pos1--pos2=pos1")
(assume "pos1" "pos2")
(simp "PosPlusComm")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "pos2+pos1--pos2" "pos1")

;; PosLtMonMinusLeft
(set-goal "all pos1,pos2,pos3(
 pos2<pos3 -> pos1<pos2 -> pos2--pos1<pos3--pos1)")
(assume "pos1" "pos2" "pos3" "p2<p3" "p1<p2")
(inst-with-to "NatToPosToNatId" (pt "pos2--pos1") "IdInstLeft")
(simp "<-" "IdInstLeft")
(drop "IdInstLeft")
(inst-with-to "NatToPosToNatId" (pt "pos3--pos1") "IdInstRight")
(simp "<-" "IdInstRight")
(drop "IdInstRight")
(simp "NatToPosLt")
(simp "PosToNatMinus")
(simp "PosToNatMinus")
(use "NatLtMonMinusLeft")
(simp "PosToNatLt")
(use "p2<p3")
(use "NatLtToLe")
(simp "PosToNatLt")
(use "p1<p2")
(use "PosLtTrans" (pt "pos2"))
(use "p1<p2")
(use "p2<p3")
(use "p1<p2")
(use "NatLt0Pos")
(use "NatLt0Pos")
;; Proof finished.
(save "PosLtMonMinusLeft")

;; From NatPlusMinus we obtain PosPlusMinus using the isomorphisms
;; PosToNat and NatToPos.

;; PosPlusMinus
(set-goal "all pos1,pos2,pos3(pos3<pos2 -> pos1+(pos2--pos3)=pos1+pos2--pos3)")
(assume "pos1" "pos2" "pos3" "p3<p2")
(assert
 "NatToPos(PosToNat(pos1+(pos2--pos3)))=NatToPos(PosToNat(pos1+pos2--pos3))")
 (simp "PosToNatPlus")
 (simp "PosToNatMinus")
 (simp "PosToNatMinus")
 (simp "PosToNatPlus")
 (simp "NatPlusMinus")
 (use "Truth")
 (use "NatLtToLe")
 (simp "PosToNatLt")
 (use "p3<p2")
 (use "PosLtTrans" (pt "pos2"))
 (use "p3<p2")
 (use "Truth")
 (use "p3<p2")
 (simp "NatToPosToNatId")
 (simp "NatToPosToNatId")
(assume "Assertion")
(use "Assertion")
;; Proof finished.
(save "PosPlusMinus")

;; PosMinusPlus
(set-goal "all pos1,pos2,pos3(pos3<pos1 -> pos1--pos3+pos2=pos1+pos2--pos3)")
(assume "pos1" "pos2" "pos3" "p3<p1")
(inst-with-to "PosPlusMinus" (pt "pos2") (pt "pos1") (pt "pos3") "p3<p1"
	      "PosPlusMinusInst")
(simp "PosPlusComm")
(simp "PosPlusMinusInst")
(simp "PosPlusComm")
(use "Truth")
;; Proof finished.
(save "PosMinusPlus")

;; PosMinusPlusEq
(set-goal "all pos1,pos2(pos2<pos1 -> pos1--pos2+pos2=pos1)")
(assume "pos1" "pos2" "p2<p1")
(simp "PosMinusPlus")
(use "Truth")
(use "p2<p1")
;; Proof finished.
(save "PosMinusPlusEq")

;; From NatMinusMinus we obtain PosMinusMinus using the isomorphisms
;; PosToNat and NatToPos.

;; PosMinusMinus
(set-goal "all pos1,pos2,pos3(
 pos3<pos2 -> pos2<pos1+pos3 -> pos1--(pos2--pos3)=pos1+pos3--pos2)")
(assume "pos1" "pos2" "pos3" "p3<p2" "p2<p1+p3")
(assert "pos2--pos3<pos1")
 (assert "pos1=pos1+pos3--pos3")
  (use "Truth")
 (assume "p1=p1+p3-p3")
 (simp "p1=p1+p3-p3")
 (drop "p1=p1+p3-p3")
 (use "PosLtMonMinusLeft")
 (use "p2<p1+p3")
 (use "p3<p2")
(assume "p2-p3<p1")
(assert
 "NatToPos(PosToNat(pos1--(pos2--pos3)))=NatToPos(PosToNat(pos1+pos3--pos2))")
 (simp "PosToNatMinus")
 (simp "PosToNatMinus")
 (simp "PosToNatMinus")
 (simp "PosToNatPlus")
 (simp "NatMinusMinus")
 (use "Truth")
 (use "NatLtToLe")
 (simp "<-" "PosToNatPlus")
 (simp "PosToNatLt")
 (use "p2<p1+p3")
 (use "NatLtToLe")
 (simp "PosToNatLt")
 (use "p3<p2")
 (use "p2<p1+p3")
 (use "p3<p2")
 (use "p2-p3<p1")
 (simp "NatToPosToNatId")
 (simp "NatToPosToNatId")
(assume "Hyp")
(use "Hyp")
;; Proof finished.
(save "PosMinusMinus")

;; Similarly to NatMinus5RewRule we have
;; pos2+pos3<pos1 -> pos1--pos2--pos3=pos1--(pos2+pos3)
;; The assumption pos2+pos3<pos1 is necessary since PosMinus does not
;; behave well for equal arguments.

;; Idea of the proof: Apply PosToNat o NatToPos outside.  Move
;; PosToNat inside (this needs pos2+pos3<pos1), use NatMinus5RewRule
;; Notice that the display is not helpful for this level of detail.

;; PosMinusMinusLeft
(set-goal "all pos1,pos2,pos3(
 pos2+pos3<pos1 -> pos1--pos2--pos3=pos1--(pos2+pos3))")
(assume "pos1" "pos2" "pos3" "p2+p3<p1")
(assert "pos2<pos1")
 (use "PosLtTrans" (pt "pos2+pos3"))
 (use "Truth")
 (use "p2+p3<p1")
(assume "p2<p1")
(inst-with-to "NatToPosToNatId" (pt "pos1--pos2--pos3") "IdInstLeft")
(simp "<-" "IdInstLeft")
(drop "IdInstLeft")
(inst-with-to "NatToPosToNatId" (pt "pos1--(pos2+pos3)") "IdInstRight")
(simp "<-" "IdInstRight")
(drop "IdInstRight")
(simp "PosToNatMinus")
(simp "PosToNatMinus")
(simp "PosToNatMinus")
(simp "PosToNatPlus")
(simp "<-" "NatMinus5RewRule")
(use "Truth")
(use "p2+p3<p1")
(use "p2<p1")
;; ?_17:pos3<pos1--pos2
(assert "pos3=pos2+pos3--pos2")
 (use "Truth")
(assume "pos3=pos2+pos3--pos2")
(simp "pos3=pos2+pos3--pos2")
(drop "pos3=pos2+pos3--pos2")
(use "PosLtMonMinusLeft")
(use "p2+p3<p1")
(use "Truth")
;; Proof finished.
(save "PosMinusMinusLeft")

;; PosTimesMinusDistr
(set-goal "all pos1,pos2,pos3(
 pos3<pos2 ->  pos1*(pos2--pos3)=pos1*pos2--pos1*pos3)")
(assume "pos1" "pos2" "pos3" "p3<p2")
(inst-with-to "NatToPosToNatId" (pt "pos1*(pos2--pos3)") "IdInstLeft")
(simp "<-" "IdInstLeft")
(drop "IdInstLeft")
(inst-with-to "NatToPosToNatId" (pt "pos1*pos2--pos1*pos3") "IdInstRight")
(simp "<-" "IdInstRight")
(drop "IdInstRight")
(simp "PosToNatTimes")
(simp "PosToNatMinus")
(simp "PosToNatMinus")
(simp "PosToNatTimes")
(simp "PosToNatTimes")
(ng)
(use "Truth")
(use "PosLeLtMonTimes")
(use "Truth")
(use "p3<p2")
(use "p3<p2")
;; Proof finished.
(save "PosTimesMinusDistr")

;; PosTimesMinusDistrLeft
(set-goal "all pos1,pos2,pos3(
 pos2<pos1 ->  (pos1--pos2)*pos3=pos1*pos3--pos2*pos3)")
(assume "pos1" "pos2" "pos3" "p2<p1")
(inst-with-to "NatToPosToNatId" (pt "(pos1--pos2)*pos3") "IdInstLeft")
(simp "<-" "IdInstLeft")
(drop "IdInstLeft")
(inst-with-to "NatToPosToNatId" (pt "pos1*pos3--pos2*pos3") "IdInstRight")
(simp "<-" "IdInstRight")
(drop "IdInstRight")
(simp "PosToNatTimes")
(simp "PosToNatMinus")
(simp "PosToNatMinus")
(simp "PosToNatTimes")
(simp "PosToNatTimes")
(ng)
(use "Truth")
(use "PosLtLeMonTimes")
(use "p2<p1")
(use "Truth")
(use "p2<p1")
;; Proof finished.
(save "PosTimesMinusDistrLeft")

;; Code discarded 2016-04-02
;; ;; BooleIfTotalReal
;; (set-goal (rename-variables
;; 	   (real-and-formula-to-mr-formula
;; 	    (proof-to-extracted-term "BooleIfTotal")
;; 	    (proof-to-formula boole-if-total-proof))))
;; (assume "boole^" "boole^0" "TMRb0b")
;; (ng #t)
;; (elim "TMRb0b")
;; (ng #t)
;; (assume "alpha^1" "alpha^2" "alpha^10" "TMRa10a1" "alpha^20" "Useless")
;; (use "TMRa10a1")
;; (ng #t)
;; (assume "alpha^1" "alpha^2" "alpha^10" "Useless" "alpha^20" "TMRa20a2")
;; (use  "TMRa20a2")
;; ;; Proof finished.
;; (save "BooleIfTotalReal")

;; ;; PosMinusTotalReal
;; (set-goal (rename-variables
;; 	   (real-and-formula-to-mr-formula
;; 	    (pt "PosMinus")
;; 	    (proof-to-formula (theorem-name-to-proof "PosMinusTotal")))))
;; (assume "p^" "p^0" "TMRp0p")
;; (elim "TMRp0p")
;; (assume "q^" "q^0" "TMRq0q")
;; (elim "TMRq0q")
;; (use "TotalPosOneMR")
;; (assume "q^1" "q^10" "TMRq10q1" "IH")
;; (ng #t)
;; (use "TotalPosOneMR")
;; (assume "q^1" "q^10" "TMRq10q1" "IH")
;; (ng #t)

;; (use "TotalPosOneMR")
;; ;; ?_4:allnc pos^,pos^0(
;; ;;      TotalPosMR pos^0 pos^ -->
;; ;;      allnc p^,p^0(TotalPosMR p^0 p^ --> TotalPosMR(pos^0--p^0)(pos^ --p^)) ->
;; ;;      allnc p^,p^0(
;; ;;       TotalPosMR p^0 p^ --> TotalPosMR(SZero pos^0--p^0)(SZero pos^ --p^)))
;; (assume "p^1" "p^10" "TMRp10p1" "IHp1" "q^" "q^0" "TMRq0q")
;; (elim "TMRq0q")
;; (ng #t)
;; (use "PosPredTotalReal")
;; (use "TotalPosSZeroMR")
;; (use "TMRp10p1")

;; (assume "q^1" "q^10" "TMRq10q1" "IHq1")
;; (ng #t)
;; (use "TotalPosSZeroMR")
;; (use "IHp1")
;; (use "TMRq10q1")

;; (assume "q^1" "q^10" "TMRq10q1" "IHq1")
;; (ng #t)
;; (use "PosPredTotalReal")
;; (use "TotalPosSZeroMR")
;; (use "IHp1")
;; (use "TMRq10q1")

;; ;; ?_5:allnc pos^,pos^0(
;; ;;      TotalPosMR pos^0 pos^ -->
;; ;;      allnc p^,p^0(TotalPosMR p^0 p^ --> TotalPosMR(pos^0--p^0)(pos^ --p^)) ->
;; ;;      allnc p^,p^0(
;; ;;       TotalPosMR p^0 p^ --> TotalPosMR(SOne pos^0--p^0)(SOne pos^ --p^)))

;; (assume "p^1" "p^10" "TMRp10p1" "IHp1" "q^" "q^0" "TMRq0q")
;; (elim "TMRq0q")
;; (ng #t)
;; (use "TotalPosSZeroMR")
;; (use "TMRp10p1")

;; (assume "q^1" "q^10" "TMRq10q1" "IHq1")
;; (ng #t)
;; (use "BooleIfTotalReal")
;; (use "PosEqTotalReal")
;; (use "TMRp10p1")
;; (use "TMRq10q1")
;; (use "TotalPosOneMR")
;; (use "TotalPosSOneMR")
;; (use "IHp1")
;; (use "TMRq10q1")

;; (assume "q^1" "q^10" "TMRq10q1" "IHq1")
;; (ng #t)
;; (use "TotalPosSZeroMR")
;; (use "IHp1")
;; (use "TMRq10q1")
;; ;; Proof finished.
;; (save "PosMinusTotalReal")

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
(set-totality-goal "PosMax")
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
(save-totality)

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
(set-totality-goal "PosMin")
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
(save-totality)

;; Rules for NatExp : nat=>nat=>nat

(add-computation-rules
 "nat**Zero" "Succ Zero"
 "nat1**Succ nat2" "nat1**nat2*nat1")

;; NatExpTotal
(set-totality-goal "NatExp")
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
(save-totality)

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


