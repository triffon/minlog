;; 2016-04-02.  int.scm.  Based on the former numbers.scm.

;; (load "~/git/minlog/init.scm")
;; (set! COMMENT-FLAG #f)
;; (libload "nat.scm")
;; (libload "pos.scm")
;; (set! COMMENT-FLAG #t)

(if (not (assoc "nat" ALGEBRAS))
    (myerror "First execute (libload \"nat.scm\")")
    (if (not (assoc "pos" ALGEBRAS))
	(myerror "First execute (libload \"pos.scm\")")))

(display "loading int.scm ...") (newline)

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
	  ((member name '("NatPlus" "IntPlus"))
	   (or (and (synt-pos? (car args)) (synt-nneg? (cadr args)))
	       (and (synt-nneg? (car args)) (synt-pos? (cadr args)))))
	  ((member name '("NatTimes" "IntTimes"))
	   (and (synt-non-zero? (car args)) (synt-non-zero? (cadr args))))
	  ((member name '("NatExp" "IntExp"))
	   (synt-non-zero? (car args)))
	  ((member name '("NatToInt"))
	   (synt-non-zero? (car args)))
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
	  ((member name '("NatPlus" "IntPlus"))
	   (or (and (synt-pos? (car args)) (synt-nneg? (cadr args)))
	       (and (synt-nneg? (car args)) (synt-pos? (cadr args)))))
	  ((member name '("NatTimes" "IntTimes"))
	   (or (and (synt-pos? (car args)) (synt-pos? (cadr args)))
	       (and (synt-neg? (car args)) (synt-neg? (cadr args)))))
	  ((member name '("NatExp" "IntExp"))
	   (synt-pos? (car args)))
	  ((member name '("NatToInt"))
	   (synt-pos? (car args)))
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
	  ((member name '("IntPlus"))
	   (and (synt-nneg? (car args) (synt-nneg? (cadr args)))))
	  ((member name '("IntTimes"))
	   (or (and (synt-nneg? (car args)) (synt-nneg? (cadr args)))
	       (and (synt-neg? (car args)) (synt-neg? (cadr args)))))
	  ((member name '("IntExp"))
	   (synt-nneg? (car args)))
	  ((member name '("NatToInt"))
	   (synt-nneg? (car args)))
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
	((member name '("NatPlus" "IntPlus"))
	 (or (and (synt-neg? (car args)) (synt-npos? (cadr args)))
	     (and (synt-npos? (car args)) (synt-neg? (cadr args)))))
	((member name '("NatTimes" "IntTimes"))
	 (or (and (synt-pos? (car args)) (synt-neg? (cadr args)))
	     (and (synt-neg? (car args)) (synt-pos? (cadr args)))))
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
	((member name '("NatPlus" "IntPlus"))
	 (and (synt-npos? (car args)) (synt-npos? (cadr args))))
	((member name '("IntTimes"))
	 (or (and (synt-npos? (car args) (synt-nneg? (cadr args))))
	     (and (synt-nneg? (car args) (synt-npos? (cadr args))))))
	(else #f))))))

;; 1.  Integers
;; ============

;; An integer is either positive or zero or negative.

(add-algs
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

;; make-numeric-term-wrt-pos produces an int object for n<=0, and a pos
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

(define (make-numeric-term n)
  (if NAT-NUMBERS
      (make-numeric-term-wrt-nat n)
      (make-numeric-term-wrt-pos n)))

;; (define make-numeric-term make-numeric-term-wrt-pos)

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

;; 2. Parsing and display for arithmetical operations
;; ==================================================

(add-program-constant "NatToInt" (py "nat=>int"))

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

;; (alg-le? (make-alg "pos") (make-alg "int"))
;; (alg-le? (make-alg "pos") (make-alg "nat"))
;; (alg-le? (make-alg "nat") (make-alg "pos"))
;; (alg-le? (make-alg "nat") (make-alg "int"))

(add-program-constant "IntS" (py "int=>int"))
(add-program-constant "IntPred" (py "int=>int"))
(add-program-constant "IntPlus" (py "int=>int=>int"))
(add-program-constant "IntMinus" (py "int=>int=>int"))
(add-program-constant "IntUMinus" (py "int=>int"))
(add-program-constant "IntTimes" (py "int=>int=>int"))
(add-program-constant "IntAbs" (py "int=>nat"))
(add-program-constant "IntExp" (py "int=>nat=>int"))
(add-program-constant "IntMax" (py "int=>int=>int"))
(add-program-constant "IntMin" (py "int=>int=>int"))
(add-program-constant "IntLt" (py "int=>int=>boole"))
(add-program-constant "IntLe" (py "int=>int=>boole"))

;; Program constants used for extraction of program constants to
;; Haskell, where computation rules
;;
;;    f (SZero x) = ... x ...
;;
;; must be transformed into e.g.
;;    f n | even n = ... TranslationPosHalfEven n ...

(add-program-constant "TranslationPosAsInt" (py "int=>pos"))

(add-token-and-type-to-name "+" (py "int") "IntPlus")

(add-token "-" 'add-op (make-term-creator "-" "int"))
(add-token-and-type-to-name "-" (py "int") "IntMinus")

(add-token "~" 'prefix-op (make-term-creator1 "~" "int"))
(add-token-and-type-to-name "~" (py "int") "IntUMinus")

(add-token-and-type-to-name "*" (py "int") "IntTimes")

(add-token "abs" 'prefix-op (make-term-creator1 "abs" "int"))
(add-token-and-type-to-name "abs" (py "int") "IntAbs")

(add-token-and-types-to-name "**" (list (py "int") (py "pos")) "IntExp")
(add-token-and-types-to-name "**" (list (py "int") (py "nat")) "IntExp")

(add-token-and-type-to-name "max" (py "int") "IntMax")
(add-token-and-type-to-name "min" (py "int") "IntMin")
(add-token-and-type-to-name "<" (py "int") "IntLt")
(add-token-and-type-to-name "<=" (py "int") "IntLe")

(add-display (py "int") (make-display-creator "IntPlus" "+" 'add-op))
(add-display (py "int") (make-display-creator "IntMinus" "-" 'add-op))
(add-display (py "int") (make-display-creator1 "IntUMinus" "~" 'prefix-op))
(add-display (py "int") (make-display-creator "IntTimes" "*" 'mul-op))
(add-display (py "nat") (make-display-creator1 "IntAbs" "abs" 'prefix-op))
(add-display (py "int") (make-display-creator1 "IntAbs" "abs" 'prefix-op))
(add-display (py "int") (make-display-creator "IntExp" "**" 'exp-op))
(add-display (py "int") (make-display-creator "IntMax" "max" 'mul-op))
(add-display (py "int") (make-display-creator "IntMin" "min" 'mul-op))
(add-display (py "boole") (make-display-creator "IntLt" "<" 'rel-op))
(add-display (py "boole") (make-display-creator "IntLe" "<=" 'rel-op))

;; 3. Arithmetic for integers
;; ==========================

(add-var-name  "k" "l" "i" "j" (py "int"))

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
(set-totality-goal "IntS")
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
(save-totality)

;; Rules for NatToInt

(add-computation-rules
 "NatToInt Zero" "IntZero"
 "NatToInt(Succ nat)" "IntS(NatToInt nat)")

(set-totality-goal "NatToInt")
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

;; ;; NatToIntInj
;; (set-goal "all nat1,nat2(NatToInt nat1=NatToInt nat2 -> nat1=nat2)")
;; (cases)
;; ;; 2-3
;; (cases)
;; ;; 4-5
;; (ng)
;; (strip)
;; (use "Truth")
;; (ng)
;; ;; ?_8:all n(0=IntS n -> F)
;; (assume "nat")
;; (simp "<-" "NatToInt1CompRule")

;; (goal-to-formula (current-goal))

;; (set-goal "all nat (0=NatToInt(Succ nat))=False")
;; (ind)
;; (use "Truth")
;; ;; 3
;; (assume "nat" "IH")
;; (ng)

;; (search-about "Succ")
;; (search-about "Mon")
;; (search-about "Inj")
;; (display-pconst "NatToInt")
;; (search-about "NatToInt")

;; Rules for IntPred

(add-computation-rules
 "IntPred IntZero" "IntN One"
 "IntPred(IntN pos)" "IntN(PosS pos)"
 "IntPred(IntP One)" "IntZero"
 "IntPred(IntP(SZero pos))" "IntP(PosPred(SZero pos))"
 "IntPred(IntP(SOne pos))" "IntP(SZero pos)")

;; IntPredTotal
(set-totality-goal "IntPred")
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
(save-totality)

(set-goal "all pos IntPred(PosS pos)=pos")
(cases)
;; 2-4
(ng)
(use "Truth")
;; 3
(assume "pos")
(ng)
(use "Truth")
;; 4
(assume "pos")
(ng)
(use "Truth")
;; Proof finished.
(add-rewrite-rule "IntPred(PosS pos)" "IntPos pos")

(set-goal "all int IntPred(IntS int)=int")
(cases)
;; 2-4
(cases)
(ng)
(use "Truth")
(assume "pos")
(ng #t)
(use "Truth")
(assume "pos")
(ng)
(use "Truth")
;; 3
(use "Truth")
;; 4
(cases)
(ng)
(use "Truth")
(assume "pos")
(ng)
(use "Truth")
(assume "pos")
(ng)
(use "Truth")
;; Proof finished.
(add-rewrite-rule "IntPred(IntS int)" "int")

(set-goal "all int IntS(IntPred int)=int")
(cases)
(cases)
(use "Truth")
(ng)
(strip)
(use "Truth")
(ng)
(strip)
(use "Truth")
(use "Truth")
(cases)
(use "Truth")
(assume "pos")
(ng)
(use "Truth")
(assume "pos")
(ng)
(use "Truth")
;; Proof finished.
(add-rewrite-rule "IntS(IntPred int)" "int")

;; IntSInj
(set-goal "all int1,int2(IntS int1=IntS int2 -> int1=int2)")
(assume "int1" "int2" "Si1=Si2")
(assert "IntPred(IntS int1)=IntPred(IntS int2)")
 (simp "Si1=Si2")
 (use "Truth")
(ng)
(assume "i1=i2")
(use "i1=i2")
;; Proof finished.
(save "IntSInj")

;; IntPredInj
(set-goal "all int1,int2(IntPred int1=IntPred int2 -> int1=int2)")
(assume "int1" "int2" "Pi1=Pi2")
(assert "IntS(IntPred int1)=IntS(IntPred int2)")
 (simp "Pi1=Pi2")
 (use "Truth")
(ng)
(assume "i1=i2")
(use "i1=i2")
;; Proof finished.
(save "IntPredInj")

;; (display-pconst "IntPred")
;; (display-pconst "IntS")

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
(set-totality-goal "IntPlus")
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
(save-totality)

;; Code discarded 2016-04-02
;; ;; IntPlusTotalReal
;; (set-goal (rename-variables
;; 	   (real-and-formula-to-mr-formula
;; 	    (pt "IntPlus")
;; 	    (proof-to-formula (theorem-name-to-proof "IntPlusTotal")))))
;; (assume "k^" "k^0" "TMRk0k" "l^" "l^0" "TMRl0l")
;; (elim "TMRk0k")

;; ;; ?_3:allnc pos^,pos^0(
;; ;;      TotalPosMR pos^0 pos^ --> TotalIntMR(pos^0+l^0)(pos^ +l^))
;; (assume "p^" "p^0" "TMRp0p")
;; (elim "TMRl0l")

;; ;; ?_7:allnc pos^,pos^0(
;; ;;      TotalPosMR pos^0 pos^ --> TotalIntMR(p^0+pos^0)(p^ +pos^))
;; (assume "q^1" "q^10" "TMRq10q1")
;; (use "TotalIntIntPosMR")
;; (use "PosPlusTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")

;; ;; ?_8:TotalIntMR(p^0+0)(p^ +0)
;; (ng #t)
;; (use "TotalIntIntPosMR")
;; (use "TMRp0p")

;; ;; ?_9:allnc pos^,pos^0(
;; ;;      TotalPosMR pos^0 pos^ --> TotalIntMR(p^0+IntN pos^0)(p^ +IntN pos^))
;; (assume "q^1" "q^10" "TMRq10q1")
;; (ng #t)
;; ;; ?_17:TotalIntMR
;; ;;      [if (p^0=q^10) 0 [if (p^0<q^10) (IntN(q^10--p^0)) (p^0--q^10)]]
;; ;;      [if (p^ =q^1) 0 [if (p^ <q^1) (IntN(q^1--p^)) (p^ --q^1)]]
;; (use "BooleIfTotalReal")
;; (use "PosEqTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")
;; (use "TotalIntIntZeroMR")
;; ;; ?_20:TotalIntMR[if (p^0<q^10) (IntN(q^10--p^0)) (p^0--q^10)]
;; ;;      [if (p^ <q^1) (IntN(q^1--p^)) (p^ --q^1)]
;; (use "BooleIfTotalReal")
;; (use "PosLtTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")
;; (use "TotalIntIntNegMR")
;; (use "PosMinusTotalReal")
;; (use "TMRq10q1")
;; (use "TMRp0p")
;; (use "TotalIntIntPosMR")
;; (use "PosMinusTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")

;; ;; ?_4:TotalIntMR(0+l^0)(0+l^)
;; (ng #t)
;; (use "TMRl0l")

;; ;; ?_5:allnc pos^,pos^0(
;; ;;      TotalPosMR pos^0 pos^ --> TotalIntMR(IntN pos^0+l^0)(IntN pos^ +l^))
;; (assume "p^" "p^0" "TMRp0p")
;; (elim "TMRl0l")

;; ;; ?_36:allnc pos^,pos^0(
;; ;;       TotalPosMR pos^0 pos^ --> TotalIntMR(IntN p^0+pos^0)(IntN p^ +pos^))
;; (assume "q^1" "q^10" "TMRq10q1")
;; (ng #t)
;; (use "BooleIfTotalReal")
;; (use "PosEqTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")
;; (use "TotalIntIntZeroMR")
;; ;; ?_43:TotalIntMR[if (p^0<q^10) (q^10--p^0) (IntN(p^0--q^10))]
;; ;;      [if (p^ <q^1) (q^1--p^) (IntN(p^ --q^1))]
;; (use "BooleIfTotalReal")
;; (use "PosLtTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")
;; (use "TotalIntIntPosMR")
;; (use "PosMinusTotalReal")
;; (use "TMRq10q1")
;; (use "TMRp0p")
;; (use "TotalIntIntNegMR")
;; (use "PosMinusTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")

;; ;; ?_37:TotalIntMR(IntN p^0+0)(IntN p^ +0)
;; (ng #t)
;; (use "TotalIntIntNegMR")
;; (use "TMRp0p")

;; ;; ?_38:allnc pos^,pos^0(
;; ;;       TotalPosMR pos^0 pos^ -->
;; ;;       TotalIntMR(IntN p^0+IntN pos^0)(IntN p^ +IntN pos^))
;; (assume "q^1" "q^10" "TMRq10q1")
;; (ng #t)
;; (use "TotalIntIntNegMR")
;; (use "PosPlusTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")
;; ;; Proof finished.
;; (save "IntPlusTotalReal")

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

;; The computation rules for IntPlus involve case distinctions, which
;; makes it unpleasant to work with normalization.  As a substitute we
;; provide some lemmas expressing conditional equations.

;; IntPlusPNN
(set-goal "all pos1,pos2(pos1<pos2 -> pos1+IntN pos2=IntN(pos2--pos1))")
(assume "pos1" "pos2" "p1<p2")
(ng)
(simp "p1<p2")
(ng)
(assert "pos1=pos2 -> F")
 (assume "p1=p2")
 (simphyp-with-to "p1<p2" "p1=p2" "Absurd")
 (use "Absurd")
(assume "p1=p2 -> F")
(simp "p1=p2 -> F")
(use "Truth")
;; Proof finished.
(save "IntPlusPNN")

;; IntPlusPNP
(set-goal "all pos1,pos2(pos2<pos1 -> pos1+IntN pos2=pos1--pos2)")
(assume "pos1" "pos2" "p2<p1")
(assert "pos1=pos2 -> F")
 (assume "p1=p2")
 (simphyp-with-to "p2<p1" "p1=p2" "Absurd")
 (use "Absurd")
(assume "p1=p2 -> F")
(ng)
(simp "p1=p2 -> F")
(ng)
(drop "p1=p2 -> F")
(assert "pos1<pos2 -> F")
 (assume "p1<p2")
 (assert "pos1<pos1")
  (use "PosLtTrans" (pt "pos2"))
  (use "p1<p2")
  (use "p2<p1")
 (assume "Absurd")
 (use "Absurd")
(assume "p1<p2 -> F")
(simp "p1<p2 -> F")
(use "Truth")
;; Proof finished.
(save "IntPlusPNP")

;; IntPlusNPP
(set-goal "all pos1,pos2(pos1<pos2 -> IntN pos1+pos2=pos2--pos1)")
(assume "pos1" "pos2" "p1<p2")
(ng)
(simp "p1<p2")
(ng)
(assert "pos1=pos2 -> F")
 (assume "p1=p2")
 (simphyp-with-to "p1<p2" "p1=p2" "Absurd")
 (use "Absurd")
(assume "p1=p2 -> F")
(simp "p1=p2 -> F")
(use "Truth")
;; Proof finished.
(save "IntPlusNPP")

;; IntPlusNPN
(set-goal "all pos1,pos2(pos2<pos1 -> IntN pos1+pos2=IntN(pos1--pos2))")
(assume "pos1" "pos2" "p2<p1")
(assert "pos1=pos2 -> F")
 (assume "p1=p2")
 (simphyp-with-to "p2<p1" "p1=p2" "Absurd")
 (use "Absurd")
(assume "p1=p2 -> F")
(ng)
(simp "p1=p2 -> F")
(ng)
(drop "p1=p2 -> F")
(assert "pos1<pos2 -> F")
 (assume "p1<p2")
 (assert "pos1<pos1")
  (use "PosLtTrans" (pt "pos2"))
  (use "p1<p2")
  (use "p2<p1")
 (assume "Absurd")
 (use "Absurd")
(assume "p1<p2 -> F")
(simp "p1<p2 -> F")
(use "Truth")
;; Proof finished.
(save "IntPlusNPN")

;; IntPlusComm
(set-goal "all int1,int2 int1+int2=int2+int1")
;; We need an auxiliary lemma
(assert "all pos1,pos2 pos1+IntN pos2=IntN pos2+pos1")
(assume "pos1" "pos2")
(use "PosLeLtCases" (pt "pos1") (pt "pos2"))
;; 3,4
(assume "pos1<=pos2")
(use "PosLeCases" (pt "pos1") (pt "pos2"))
;; 6-8
(use "pos1<=pos2")
;; 7
(assume "pos1<pos2")
(ng #t)
(simp "pos1<pos2")
(assert "pos2<pos1 -> pos1<pos1")
 (use "PosLeLtTrans")
 (use "pos1<=pos2")
(assume "pos2<pos1 -> F")
(ng)
(simp "pos2<pos1 -> F")
(ng)
(cases (pt "pos1=pos2"))
;; 19-20
(assume "pos1=pos2")
(simp "pos1=pos2")
(use "Truth")
;; 20
(assume "pos1=pos2 -> F")
(assert "pos2=pos1 -> F")
 (assume "pos2=pos1")
 (use "pos1=pos2 -> F")
 (simp "pos2=pos1")
 (use "Truth")
(assume "pos2=pos1 -> F")
(simp "pos2=pos1 -> F")
(use "Truth")
;; 8
(assume "pos1=pos2")
(simp "pos1=pos2")
(use "Truth")
;; 4
(assume "pos2<pos1")
(ng)
(simp "pos2<pos1")
(assert "pos1<pos2 -> pos2<pos2")
 (use "PosLtTrans")
 (use "pos2<pos1")
(assume "pos1<pos2 -> F")
(ng)
(simp "pos1<pos2 -> F")
(ng)
(cases (pt "pos1=pos2"))
;; 43-44
(assume "pos1=pos2")
(simp "pos1=pos2")
(use "Truth")
;; 44
(assume "pos1=pos2 -> F")
(assert "pos2=pos1 -> F")
 (assume "pos2=pos1")
 (use "pos1=pos2 -> F")
 (simp "pos2=pos1")
 (use "Truth")
(assume "pos2=pos1 -> F")
(simp "pos2=pos1 -> F")
(use "Truth")
;; Assertion proved
(assume "IntPlusCommAux")
;; Now the proof of IntPlusComm starts properly.
(cases)
;; 2-4
(assume "pos1")
(cases)
;; 6-8
(assume "pos2")
(ng)
(use "PosPlusComm")
;; 7
(ng)
(use "Truth")
;; 8
(assume "pos2")
(use "IntPlusCommAux")
;; 3
(assume "int")
(ng)
(use "Truth")
;; 4
(assume "pos2")
(cases)
;; 16-18
(assume "pos1")
(simp "IntPlusCommAux")
(use "Truth")
;; 17
(ng)
(use "Truth")
;; 18
(assume "pos1")
(ng)
(use "PosPlusComm")
;; Proof finished.
(save "IntPlusComm")

;; To prove IntPlusAssoc (from IntPlusAssocPPN) we use IntUMinus.
;; Therefore we postpone this until we get to IntUMinus.

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

;; IntPNatToPosEqNatToInt
(set-goal "all nat(Zero<nat -> IntP(NatToPos nat)=NatToInt nat)")
(ind)
(assume "Absurd")
(use "Efq")
(use "Absurd")
;; 3
(cases)
(assume "Useless1" "Useless2")
(use "Truth")
(assume "nat" "IH" "Useless")
(simp "SuccPosS")
(simp "NatToInt1CompRule")
(simp "<-" "IntS1CompRule")
(simp "IH")
(use "Truth")
(use "Truth")
(use "Truth")
;; Proof finished.
(save "IntPNatToPosEqNatToInt")

;; PosToNatToIntId
(set-goal "all pos NatToInt(PosToNat pos)=IntP pos")
(assume "pos")
(simp "<-" "IntPNatToPosEqNatToInt")
(use "NatToPosToNatId")
(use "NatLt0PosToNat")
;; Proof finished.
(save "PosToNatToIntId")

;; The following is not used any more:
;; NatToIntDouble
;; (set-goal "all nat NatToInt(NatDouble nat)=NatToInt nat + NatToInt nat")
;; (ind)
;; (ng #t)
;; (use "Truth")
;; (assume "nat" "IH")
;; (ng #t)
;; (simp "IH")
;; ;; ?_7:IntS(IntS(IntPlus nat nat))=IntS nat+IntS nat
;; (use "Truth")
;; ;; Proof finished.
;; (save "NatToIntDouble")

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
(set-totality-goal "IntMinus")
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

;; Code discarded 2016-04-02
;; ;; IntMinusTotalReal
;; (set-goal (rename-variables
;; 	   (real-and-formula-to-mr-formula
;; 	    (pt "IntMinus")
;; 	    (proof-to-formula (theorem-name-to-proof "IntMinusTotal")))))
;; (assume "k^" "k^0" "TMRk0k" "l^" "l^0" "TMRl0l")
;; (elim "TMRk0k")

;; ;; ?_3:allnc pos^,pos^0(
;; ;;      TotalPosMR pos^0 pos^ --> TotalIntMR(pos^0-l^0)(pos^ -l^))
;; (assume "p^" "p^0" "TMRp0p")
;; (elim "TMRl0l")

;; ;; ?_7:allnc pos^,pos^0(
;; ;;      TotalPosMR pos^0 pos^ --> TotalIntMR(p^0-pos^0)(p^ -pos^))
;; (assume "q^1" "q^10" "TMRq10q1")
;; (ng #t)
;; ;; ?_11:TotalIntMR
;; ;;      [if (p^0=q^10) 0 [if (p^0<q^10) (IntN(q^10--p^0)) (p^0--q^10)]]
;; ;;      [if (p^ =q^1) 0 [if (p^ <q^1) (IntN(q^1--p^)) (p^ --q^1)]]
;; (use "BooleIfTotalReal")
;; (use "PosEqTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")
;; (use "TotalIntIntZeroMR")
;; (use "BooleIfTotalReal")
;; (use "PosLtTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")
;; (use "TotalIntIntNegMR")
;; (use "PosMinusTotalReal")
;; (use "TMRq10q1")
;; (use "TMRp0p")
;; (use "TotalIntIntPosMR")
;; (use "PosMinusTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")

;; ;; ?_8:TotalIntMR(p^0-0)(p^ -0)
;; (ng #t)
;; (use "TotalIntIntPosMR")
;; (use "TMRp0p")

;; ;; ?_9:allnc pos^,pos^0(
;; ;;      TotalPosMR pos^0 pos^ --> TotalIntMR(p^0-IntN pos^0)(p^ -IntN pos^))
;; (assume "q^1" "q^10" "TMRq10q1")
;; (ng #t)
;; (use "TotalIntIntPosMR")
;; (use "PosPlusTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")

;; ;; ?_4:TotalIntMR(0-l^0)(0-l^)
;; (elim "TMRl0l")
;; (assume "q^1" "q^10" "TMRq10q1")
;; (ng #t)
;; (use "TotalIntIntNegMR")
;; (use "TMRq10q1")
;; (use "TotalIntIntZeroMR")
;; (assume "q^1" "q^10" "TMRq10q1")
;; (ng #t)
;; (use "TotalIntIntPosMR")
;; (use "TMRq10q1")

;; ;; ?_5:allnc pos^,pos^0(
;; ;;      TotalPosMR pos^0 pos^ --> TotalIntMR(IntN pos^0-l^0)(IntN pos^ -l^))
;; (assume "p^" "p^0" "TMRp0p")
;; (elim "TMRl0l")

;; ;; ?_45:allnc pos^,pos^0(
;; ;;       TotalPosMR pos^0 pos^ --> TotalIntMR(IntN p^0-pos^0)(IntN p^ -pos^))
;; (assume "q^1" "q^10" "TMRq10q1")
;; (ng #t)
;; (use "TotalIntIntNegMR")
;; (use "PosPlusTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")

;; ;; ?_46:TotalIntMR(IntN p^0-0)(IntN p^ -0)
;; (ng #t)
;; (use "TotalIntIntNegMR")
;; (use "TMRp0p")

;; ;; ?_47:allnc pos^,pos^0(
;; ;;       TotalPosMR pos^0 pos^ -->
;; ;;       TotalIntMR(IntN p^0-IntN pos^0)(IntN p^ -IntN pos^))
;; (assume "q^1" "q^10" "TMRq10q1")
;; (ng #t)
;; ;; ?_56:TotalIntMR
;; ;;      [if (p^0=q^10) 0 [if (p^0<q^10) (q^10--p^0) (IntN(p^0--q^10))]]
;; ;;      [if (p^ =q^1) 0 [if (p^ <q^1) (q^1--p^) (IntN(p^ --q^1))]]
;; (use "BooleIfTotalReal")
;; (use "PosEqTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")
;; (use "TotalIntIntZeroMR")
;; (use "BooleIfTotalReal")
;; (use "PosLtTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")
;; (use "TotalIntIntPosMR")
;; (use "PosMinusTotalReal")
;; (use "TMRq10q1")
;; (use "TMRp0p")
;; (use "TotalIntIntNegMR")
;; (use "PosMinusTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")
;; ;; Proof finished.
;; (save "IntMinusTotalReal")

;; Rules for IntUMinus

(add-computation-rules
 "~IntZero" "IntZero"
 "~IntP pos" "IntN pos"
 "~IntN pos" "IntP pos")

;; IntUMinusTotal
(set-totality-goal "IntUMinus")
(assume "k^" "Tk")
(elim "Tk")
;; 3-5
(assume "p^" "Tp")
(use "TotalIntIntNeg")
(use "Tp")
;; 4
(use "TotalIntIntZero")
;; 5
(assume "p^" "Tp")
(use "TotalIntIntPos")
(use "Tp")
;; Proof finished.
(save-totality)

(set-goal "all int ~ ~int=int")
(cases)
;; 2-4
(assume "pos")
(use "Truth")
;; 3
(use "Truth")
;; 4
(assume "pos")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "~ ~int" "int")

(set-goal "all int1,int2 ~(int1+int2)= ~int1+ ~int2")
(cases)
;; 2-4
(assume "pos1")
(cases)
;; 6-8
(assume "pos2")
(use "Truth")
;; 7
(use "Truth")
;; 8
(assume "pos2")
(ng)
(cases (pt "pos1=pos2"))
(assume "p1=p2")
(use "Truth")
(assume "p1=p2 -> F")
(ng)
(cases (pt "pos1<pos2"))
(assume "p1<p2")
(use "Truth")
(assume "p1<p2 -> F")
(use "Truth")
;; 3
(assume "int")
(use "Truth")
;; 4
(assume "pos1")
(cases)
;; 23-25
(assume "pos2")
(ng)
(cases (pt "pos1=pos2"))
(assume "p1=p2")
(use "Truth")
(assume "p1=p2 -> F")
(ng)
(cases (pt "pos1<pos2"))
(assume "p1<p2")
(use "Truth")
(assume "p1<p2 -> F")
(use "Truth")
;; 24
(use "Truth")
;; 25
(assume "pos2")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "~(int1+int2)" "~int1+ ~int2")

;; IntUMinusMinus
(set-goal "all int1,int2 ~(int1-int2)= ~int1+int2")
(cases)
;; 2-4
(assume "pos1")
(cases)
;; 6-8
(assume "pos2")
(ng)
(cases (pt "pos1=pos2"))
(assume "p1=p2")
(use "Truth")
(assume "p1=p2 -> F")
(ng)
(cases (pt "pos1<pos2"))
(assume "p1<p2")
(use "Truth")
(assume "p1<p2 -> F")
(use "Truth")
;; 7
(use "Truth")
;; 8
(assume "pos2")
(use "Truth")
;; 3
(cases)
(assume "pos2")
(use "Truth")
(use "Truth")
(assume "pos2")
(use "Truth")
;; 4
(assume "pos1")
(cases)
;; 27-29
(assume "pos2")
(use "Truth")
;; 28
(use "Truth")
;; 29
(assume "pos2")
(ng)
(cases (pt "pos1=pos2"))
(assume "p1=p2")
(use "Truth")
(assume "p1=p2 -> F")
(ng)
(cases (pt "pos1<pos2"))
(assume "p1<p2")
(use "Truth")
(assume "p1<p2 -> F")
(use "Truth")
;; Proof finished.
(save "IntUMinusMinus")

;; IntUMinusInj
(set-goal "all int1,int2(~int1= ~int2 -> int1=int2)")
(cases)
;; 2-4
(assume "pos1")
(cases)
;; 6-8
(assume "pos2")
(ng)
(assume "p1=p2")
(use "p1=p2")
;; 7
(assume "Absurd")
(use "Absurd")
;; 8
(assume "pos2")
(ng)
(assume "Absurd")
(use "Absurd")
;; 3
(cases)
(assume "pos2")
(ng)
(assume "Absurd")
(use "Absurd")
(assume "Useless")
(use "Truth")
(assume "pos2")
(ng)
(assume "Absurd")
(use "Absurd")
;; 4
(assume "pos1")
(cases)
;; 27-29
(assume "pos2")
(ng)
(assume "Absurd")
(use "Absurd")
;; 28
(ng)
(assume "Absurd")
(use "Absurd")
;; 29
(assume "pos2")
(ng)
(assume "p1=p2")
(use "p1=p2")
;; Proof finished.
(save "IntUMinusInj")

(set-goal "all int ~(IntS int)=IntPred~int")
(cases)
;; 2-4
(assume "pos")
(use "Truth")
;; 3
(ng)
(use "Truth")
;; 4
(ng)
(cases)
(ng)
(use "Truth")
(assume "pos")
(ng)
(use "Truth")
(assume "pos")
(ng)
(use "Truth")
;; Proof finished.
(add-rewrite-rule "~(IntS int)" "IntPred~int")

(set-goal "all int ~(IntPred int)=IntS~int")
(assume "int")
(use "IntUMinusInj")
(ng)
(use "Truth")
;; Proof finished.
(add-rewrite-rule "~(IntPred int)" "IntS~int")

;; (display-pconst "IntUMinus")

;; The following can only be done after IntTimes IntMax IntMin
;; IntTimesUMinusId
;; all int1,int2 ~int1*int2= ~(int1*int2)
;; IntTimesIdUMinus
;; all int1,int2 int1* ~int2= ~(int1*int2)
;; IntUMinusMax
;; IntUMinusMin

;; Next: IntPlusAssoc.  It suffices to prove IntPlusAssocPPN:
;; pos1+(pos2+IntN pos3)=pos1+pos2+IntN pos3.  This requires
;; comparison of p3 with p2<p1+p2, i.e., consideration of 5 cases:
;; p3<p2 p3=p2 p2<p3<p1+p2 p3=p1+p2 p1+p2<p3

;; IntPlusAssoc
(set-goal "all int1,int2,int3 int1+(int2+int3)=int1+int2+int3")
;; IntPlusAssocPPN
(assert "all pos1,pos2,pos3
 pos1+(pos2+IntN pos3)=IntP pos1+IntP pos2+IntN pos3")
(assume "pos1" "pos2" "pos3")
(use "PosLeLtCases" (pt "pos3") (pt "pos2"))
(assume "p3<=p2")
(use "PosLeCases"  (pt "pos3") (pt "pos2"))
(use "p3<=p2")
(drop "p3<=p2")
(assume "p3<p2")
;; Case p3<p2
(assert "pos3<pos1+pos2")
 (use "PosLtTrans" (pt "pos2"))
 (use "p3<p2")
 (use "Truth")
(assume "p3<p1+p2")
;; ?_15:pos1+(pos2+IntN pos3)=IntPlus pos1 pos2+IntN pos3
(simp "IntPlus2CompRule")
;; ?_16:pos1+(pos2+IntN pos3)=pos1+pos2+IntN pos3
(simp "IntPlusPNP")
;; ?_17:IntPlus pos1(pos2--pos3)=pos1+pos2+IntN pos3
(simp "IntPlusPNP")
;; ?_19:IntPlus pos1(pos2--pos3)=pos1+pos2--pos3
(simp "IntPlus2CompRule")
;; ?_21:=(pos1+(pos2--pos3))(pos1+pos2--pos3)
(simp "PosPlusMinus")
(use "Truth")
(use "p3<p2")
(use "p3<p1+p2")
(use "p3<p2")
;; Case p3=p2
(assume "p3=p2")
(assert "IntP pos2+IntN pos3=0")
 (ng #t)
 (simp "p3=p2")
 (use "Truth")
(assume "p2-p3=0")
(simp "p2-p3=0")
(drop "p2-p3=0")
(simp "IntPlus2CompRule")
(simp "IntPlusPNP")
(simp "p3=p2")
(use "Truth")
(simp "p3=p2")
(use "Truth")
;; Case p2<p3.  Need further case distinction on p3 with p1+p2
(use "PosLeLtCases" (pt "pos3") (pt "pos1+pos2"))
(assume "p3<=p1+p2")
(use "PosLeCases"  (pt "pos3") (pt "pos1+pos2"))
(use "p3<=p1+p2")
(drop "p3<=p1+p2")
(assume "p3<p1+p2")
;; Case p2<p3<p1+p2
(assume "p2<p3")
(assert "pos3--pos2<pos1")
 (assert "pos1=pos1+pos2--pos2")
  (use "Truth")
 (assume "p1=p1+p2-p2")
 (simp "p1=p1+p2-p2")
 (drop "p1=p1+p2-p2")
 (use "PosLtMonMinusLeft")
 (use "p3<p1+p2")
 (use "p2<p3")
(assume "p3-p2<p1")
(simp "IntPlusPNN")
(simp "IntPlusPNP")
(simp "IntPlus2CompRule")
(simp "IntPlusPNP")
(simp "PosMinusMinus")
(use "Truth")
(use "p3<p1+p2")
(use "p2<p3")
(use "p3<p1+p2")
(use "p3-p2<p1")
(use "p2<p3")
;; Case p3=p1+p2
(drop "p3<=p1+p2")
(assume "p3=p1+p2" "p2<p3")
(simp "p3=p1+p2")
(ng #t)
(assert "pos2=pos1+pos2 -> F")
 (assume "p2=p1+p2")
 (assert "pos2<pos1+pos2 -> F")
  (simp "<-" "p2=p1+p2")
  (assume "p2<p2")
  (use "p2<p2")
 (assume "p2<p1+p2 -> F")
 (use "p2<p1+p2 -> F")
 (use "Truth")
(assume "p2=p1+p2 -> F")
(simp "p2=p1+p2 -> F")
(use "Truth")
;; Case p1+p2<p3
(assume "p1+p2<p3" "p2<p3")
(simp "IntPlus2CompRule")
(simp "IntPlusPNN")
(simp "IntPlusPNN")
(simp "IntPlusPNN")
(simp "PosPlusComm")
(simp "PosMinusMinusLeft")
(use "Truth")
(simp "PosPlusComm")
(use "p1+p2<p3")
(use "p1+p2<p3")
(assert "pos1+pos2--pos2<pos3--pos2")
 (use "PosLtMonMinusLeft")
 (use "p1+p2<p3")
 (use "Truth")
 (ng #t)
(assume "Hyp")
(use "Hyp")
(use "p2<p3")
;; Proof of assertion finished.
(assume "IntPlusAssocPPN")
;; Now we can tackle IntPlusAssoc.
(cases)
;; 2-4
(assume "pos1")
(cases)
;; 6-8
(assume "pos2")
(cases)
;; 10-12
(assume "pos3")
(use "PosPlusAssoc" (pt "pos1") (pt "pos2") (pt "pos3"))
;; 11
(use "Truth")
;; 12
(assume "pos3")
(use "IntPlusAssocPPN")
;; 7
(assume "int3")
(use "Truth")
;; 8
(assume "pos2")
(cases)
;; 17-19
(assume "pos3")
;; ?_20:pos1+(IntN pos2+pos3)=pos1+IntN pos2+pos3
(assert "IntN pos2+pos3=pos3+IntN pos2")
 (use "IntPlusComm")
(assume "IntN pos2+pos3=pos3+IntN pos2")
(simp "IntN pos2+pos3=pos3+IntN pos2")
(drop "IntN pos2+pos3=pos3+IntN pos2")
(simp "IntPlusAssocPPN")
(assert "IntPlus pos1 pos3=IntPlus pos3 pos1")
 (use "IntPlusComm")
(assume "IntPlus pos1 pos3=IntPlus pos3 pos1")
(simp "IntPlus pos1 pos3=IntPlus pos3 pos1")
(drop "IntPlus pos1 pos3=IntPlus pos3 pos1")
(simp "<-" "IntPlusAssocPPN")
(use "IntPlusComm")
;; 18
(use "Truth")
;; 19
(assume "pos3")
;; ?_33:pos1+(IntN pos2+IntN pos3)=pos1+IntN pos2+IntN pos3
(use "IntUMinusInj")
(assert "IntN pos2= ~pos2")
 (use "Truth")
(assume "IntN pos2= ~pos2")
(simp "IntN pos2= ~pos2")
(assert "IntN pos3= ~pos3")
 (use "Truth")
(assume "IntN pos3= ~pos3")
(simp "IntN pos3= ~pos3")
;; ?_42:~(pos1+(~pos2+ ~pos3))= ~(pos1+ ~pos2+ ~pos3)
(simp "IntUMinus1RewRule")
(simp "IntUMinus1RewRule")
(simp "IntUMinus0RewRule")
(simp "IntUMinus0RewRule")
(simp "IntUMinus1RewRule")
(simp "IntUMinus0RewRule")
(simp "IntUMinus1RewRule")
(simp "IntUMinus0RewRule")
;; ?_50:~pos1+IntPlus pos2 pos3= ~pos1+pos2+pos3
(assert "~pos1+pos2+pos3=pos3+(~pos1+pos2)")
 (use "IntPlusComm")
(assume "~pos1+pos2+pos3=pos3+(~pos1+pos2)")
(simp "~pos1+pos2+pos3=pos3+(~pos1+pos2)")
(drop "~pos1+pos2+pos3=pos3+(~pos1+pos2)")
;; ?_55:~pos1+IntPlus pos2 pos3=pos3+(~pos1+pos2)
(assert "~pos1+pos2=pos2+ ~pos1")
 (use "IntPlusComm")
(assume "~pos1+pos2=pos2+ ~pos1")
(simp "~pos1+pos2=pos2+ ~pos1")
(drop "~pos1+pos2=pos2+ ~pos1")
;; ?_60:~pos1+IntPlus pos2 pos3=pos3+(pos2+ ~pos1)
(simp "IntPlusComm")
;; ?_61:IntPlus pos2 pos3+ ~pos1=pos3+(pos2+ ~pos1)
(assert "IntN pos1= ~pos1")
 (use "Truth")
(assume "IntN pos1= ~pos1")
(simp "<-" "IntN pos1= ~pos1")
;; ?_65:IntPlus pos2 pos3+IntN pos1=pos3+(pos2+IntN pos1)
(assert "IntPlus pos2 pos3=IntPlus pos3 pos2")
 (use "IntPlusComm")
(assume "IntPlus pos2 pos3=IntPlus pos3 pos2")
(simp "IntPlus pos2 pos3=IntPlus pos3 pos2")
(drop "IntPlus pos2 pos3=IntPlus pos3 pos2")
(simp "<-" "IntPlusAssocPPN")
(use "Truth")
;; 3
(assume "int1" "int2")
(use "Truth")
;; 4
(assume "pos1")
(cases)
;; 74-76
(assume "pos2")
(cases)
;; 78-80
(assume "pos3")
;; ?_81:IntN pos1+IntPlus pos2 pos3=IntN pos1+pos2+pos3
(assert "IntPlus pos2 pos3=IntPlus pos3 pos2")
 (use "IntPlusComm")
(assume "IntPlus pos2 pos3=IntPlus pos3 pos2")
(simp "IntPlus pos2 pos3=IntPlus pos3 pos2")
(drop "IntPlus pos2 pos3=IntPlus pos3 pos2")
;; ?_86:IntN pos1+IntPlus pos3 pos2=IntN pos1+pos2+pos3
(simp "IntPlusComm")
;; ?_87:IntPlus pos3 pos2+IntN pos1=IntN pos1+pos2+pos3
(assert "IntN pos1+pos2+pos3=pos3+(IntN pos1+pos2)")
 (use "IntPlusComm")
(assume "IntN pos1+pos2+pos3=pos3+(IntN pos1+pos2)")
(simp "IntN pos1+pos2+pos3=pos3+(IntN pos1+pos2)")
(drop "IntN pos1+pos2+pos3=pos3+(IntN pos1+pos2)")
;; ?_92:IntPlus pos3 pos2+IntN pos1=pos3+(IntN pos1+pos2)
(assert "IntN pos1+pos2=pos2+IntN pos1")
 (use "IntPlusComm")
(assume "IntN pos1+pos2=pos2+IntN pos1")
(simp "IntN pos1+pos2=pos2+IntN pos1")
(drop "IntN pos1+pos2=pos2+IntN pos1")
(simp "<-" "IntPlusAssocPPN")
(use "Truth")
;; 79
(use "Truth")
;; 80
(assume "pos3")
;; ?_99:IntN pos1+(pos2+IntN pos3)=IntN pos1+pos2+IntN pos3
(use "IntUMinusInj")
(assert "IntN pos1= ~pos1")
 (use "Truth")
(assume "IntN pos1= ~pos1")
(simp "IntN pos1= ~pos1")
(assert "IntN pos3= ~pos3")
 (use "Truth")
(assume "IntN pos3= ~pos3")
(simp "IntN pos3= ~pos3")
;; ?_108:~(~pos1+(pos2+ ~pos3))= ~(~pos1+pos2+ ~pos3)
(simp "IntUMinus1RewRule")
(simp "IntUMinus0RewRule")
(simp "IntUMinus1RewRule")
(simp "IntUMinus0RewRule")
(simp "IntUMinus1RewRule")
(simp "IntUMinus0RewRule")
(simp "IntUMinus1RewRule")
(simp "IntUMinus0RewRule")
;; ?_116:pos1+(~pos2+pos3)=pos1+ ~pos2+pos3
(assert "~pos2+pos3=pos3+ ~pos2")
 (use "IntPlusComm")
(assume "~pos2+pos3=pos3+ ~pos2")
(simp "~pos2+pos3=pos3+ ~pos2")
(drop "~pos2+pos3=pos3+ ~pos2")
;; ?_121:pos1+(pos3+ ~pos2)=pos1+ ~pos2+pos3
(assert "IntN pos2= ~pos2")
 (use "Truth")
(assume "IntN pos2= ~pos2")
(simp "<-" "IntN pos2= ~pos2")
(simp "IntPlusAssocPPN")
;; ?_126:IntPlus pos1 pos3+IntN pos2=pos1+IntN pos2+pos3
(assert "pos1+IntN pos2+pos3=pos3+(pos1+IntN pos2)")
 (use "IntPlusComm")
(assume "pos1+IntN pos2+pos3=pos3+(pos1+IntN pos2)")
(simp "pos1+IntN pos2+pos3=pos3+(pos1+IntN pos2)")
(drop "pos1+IntN pos2+pos3=pos3+(pos1+IntN pos2)")
(simp "IntPlusAssocPPN")
(assert "IntPlus pos1 pos3=IntPlus pos3 pos1")
 (use "IntPlusComm")
(assume "IntPlus pos1 pos3=IntPlus pos3 pos1")
(simp "IntPlus pos1 pos3=IntPlus pos3 pos1")
(use "Truth")
;; 75
(assume "int3")
(use "Truth")
;; 76
(assume "pos2")
(cases)
;; 139-141
(assume "pos3")
;; ?_142:IntN pos1+(IntN pos2+pos3)=IntN pos1+IntN pos2+pos3
(use "IntUMinusInj")
(assert "IntN pos1= ~pos1")
 (use "Truth")
(assume "IntN pos1= ~pos1")
(simp "IntN pos1= ~pos1")
(assert "IntN pos2= ~pos2")
 (use "Truth")
(assume "IntN pos2= ~pos2")
(simp "IntN pos2= ~pos2")
;; ?_151:~(~pos1+(~pos2+pos3))= ~(~pos1+ ~pos2+pos3)
(simp "IntUMinus1RewRule")
(simp "IntUMinus0RewRule")
(simp "IntUMinus1RewRule")
(simp "IntUMinus0RewRule")
(simp "IntUMinus1RewRule")
(simp "IntUMinus1RewRule")
(simp "IntUMinus0RewRule")
(simp "IntUMinus0RewRule")
(assert "IntN pos3= ~pos3")
 (use "Truth")
(assume "IntN pos3= ~pos3")
(simp "<-" "IntN pos3= ~pos3")
(use "IntPlusAssocPPN")
;; 140
(use "Truth")
;; 141
(assume "pos3")
;; ?_164:IntN pos1+(IntN pos2+IntN pos3)=IntN pos1+IntN pos2+IntN pos3
(use "Truth")
;; Proof finished.
(save "IntPlusAssoc")
;; We also add IntPlusAssoc as rewrite rule
(add-rewrite-rule "int1+(int2+int3)" "int1+int2+int3")

;; IntPlusIdOne
(set-goal "all int int+1=IntS int")
(cases)
;; 2-4
(assume "pos")
(use "Truth")
;; 3
(use "Truth")
;; 4
(cases)
;; 6-8
(use "Truth")
;; 7
(assume "pos")
(use "Truth")
;; 8
(assume "pos")
(use "Truth")
;; Proof finished.
(save "IntPlusIdOne")
;; (add-rewrite-rule "i+One" "IntS i")

;; IntPlusIdIntPSZero
(set-goal "all int,pos int+IntP(SZero pos)=int+IntP pos+IntP pos")
(assume "int" "pos")
(simp "SZeroPosPlus")
(simp "PosPlusIntPlus")
(use "IntPlusAssoc")
;; Proof finished.
(save "IntPlusIdIntPSZero")
;; (add-rewrite-rule "int+IntP(SZero pos)" "int+IntP pos+IntP pos")

;; IntPlusIdIntPSOne
(set-goal "all int,pos int+IntP(SOne pos)=IntS(int+IntP(SZero pos))")
(assume "int" "pos")
(simp "IntPSOne")
(simp "SZeroPosPlus")
(simp "<-" "IntPlusIdOne")
(simp "<-" "IntPlusIdOne")
(simp "PosPlusIntPlus")
(simp "IntPlusAssoc")
(use "Truth")
;; Proof finished.
(save "IntPlusIdIntPSOne")
;; (add-rewrite-rule "i+IntP(SOne pos)" "IntS(i+IntP(SZero pos))")

;; IntPlusIdIntNSZero
(set-goal "all int,pos int+IntN(SZero pos)=int+IntN pos+IntN pos")
(assume "int" "pos")
(use "IntUMinusInj")
(ng)
(use "IntPlusIdIntPSZero")
;; Proof finished.
(save "IntPlusIdIntNSZero")
;; (add-rewrite-rule "i+IntN(SZero pos)" "i+IntN pos+IntN pos")

;; IntPlusIdIntNSOne
(set-goal "all int,pos int+IntN(SOne pos)=IntPred(int+IntN(SZero pos))")
(assume "int" "pos")
(use "IntUMinusInj")
(ng)
(use "IntPlusIdIntPSOne")
;; Proof finished.
(save "IntPlusIdIntNSOne")
;; (add-rewrite-rule "i+IntN(SOne pos)" "IntPred(i+IntN(SZero pos))")

;; IntPlusOneId
(set-goal "all int 1+int=IntS int")
(assume "int")
(simp "IntPlusComm")
(use "IntPlusIdOne")
;; Proof finished.
(save "IntPlusOneId")
;; (add-rewrite-rule "One+i" "IntS i")

;; IntPlusIntPSZeroId
(set-goal "all int,pos IntP(SZero pos)+int=int+IntP pos+IntP pos")
(assume "int" "pos")
(simp "IntPlusComm")
(use "IntPlusIdIntPSZero")
;; Proof finished.
;; (add-rewrite-rule "IntP(SZero pos)+int" "int+IntP pos+IntP pos")

;; IntPlusIntPSOneId
(set-goal "all int,pos IntP(SOne pos)+int=IntS(int+IntP(SZero pos))")
(assume "int" "pos")
(simp "IntPlusComm")
(use "IntPlusIdIntPSOne")
;; Proof finished.
;; (add-rewrite-rule "IntP(SOne pos)+i" "IntS(i+IntP(SZero pos))")

;; IntPlusIntNSZeroId
(set-goal "all int,pos IntN(SZero pos)+int=int+IntN pos+IntN pos")
(assume "int" "pos")
(simp "IntPlusComm")
(use "IntPlusIdIntNSZero")
;; Proof finished.
;; (add-rewrite-rule "IntN(SZero pos)+i" "i+IntN pos+IntN pos")

;; IntPlusIdIntNSOne
(set-goal "all int,pos IntN(SOne pos)+int=IntPred(int+IntN(SZero pos))")
(assume "int" "pos")
(simp "IntPlusComm")
(use "IntPlusIdIntNSOne")
;; Proof finished.
;; (add-rewrite-rule "IntN(SOne pos)+i" "IntPred(i+IntN(SZero pos))")

;; IntPlusIntSId
(set-goal "all int1,int2 IntS int1+int2=IntS(int1+int2)")
(assume "int1" "int2")
(simp "<-" "IntPlusOneId")
(simp "<-" "IntPlusOneId")
(simp "IntPlusAssoc")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "IntS int1+int2" "IntS(int1+int2)")

;; IntPlusIdIntS
(set-goal "all int1,int2 int1+IntS int2=IntS(int1+int2)")
(assume "int1" "int2")
(simp "<-" "IntPlusIdOne")
(simp "<-" "IntPlusIdOne")
(simp "IntPlusAssoc")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "int1+IntS int2" "IntS(int1+int2)")

;; (display-pconst "IntPlus")
;; (search-about "IntPlus")
;; (display-pconst "IntS")
;; (search-about "IntS")

;; In numbers.scm we had unproven rewrite rules
;; (add-rewrite-rule "i+One" "IntS i")
;; (add-rewrite-rule "i+IntP(SZero pos)" "i+IntP pos+IntP pos")
;; (add-rewrite-rule "i+IntP(SOne pos)" "IntS(i+IntP(SZero pos))")
;; (add-rewrite-rule "i+IntN(SZero pos)" "i+IntN pos+IntN pos")
;; (add-rewrite-rule "i+IntN(SOne pos)" "IntPred(i+IntN(SZero pos))")

;; (add-rewrite-rule "One+i" "IntS i")
;; (add-rewrite-rule "IntP(SZero pos)+i" "i+IntP pos+IntP pos")
;; (add-rewrite-rule "IntP(SOne pos)+i" "IntS(i+IntP(SZero pos))")
;; (add-rewrite-rule "IntN(SZero pos)+i" "i+IntN pos+IntN pos")
;; (add-rewrite-rule "IntN(SOne pos)+i" "IntPred(i+IntN(SZero pos))")

;; ;; Added 2007-02-13
;; (add-rewrite-rule "i1+(i2+i3)" "i1+i2+i3")
;; (add-rewrite-rule "IntS i+j" "IntS(i+j)")
;; (add-rewrite-rule "i+IntS j" "IntS(i+j)")

;; Rules for IntTimes

(add-computation-rules
 "IntZero*int" "IntZero"
 "IntP pos*IntZero" "IntZero"
 "IntP pos1*IntP pos2" "IntP(pos1*pos2)"
 "IntP pos1*IntN pos2" "IntN(pos1*pos2)"
 "IntN pos*IntZero" "IntZero"
 "IntN pos1*IntP pos2" "IntN(pos1*pos2)"
 "IntN pos1*IntN pos2" "IntP(pos1*pos2)")

;; IntTimesTotal
(set-totality-goal "IntTimes")
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
(save-totality)

;; Code discarded 2016-04-02
;; ;; IntTimesTotalReal
;; (set-goal (rename-variables
;; 	   (real-and-formula-to-mr-formula
;; 	    (pt "IntTimes")
;; 	    (proof-to-formula (theorem-name-to-proof "IntTimesTotal")))))
;; (assume "k^" "k^0" "TMRk0k" "l^" "l^0" "TMRl0l")
;; (elim "TMRk0k")

;; ;; ?_3:allnc pos^,pos^0(
;; ;;      TotalPosMR pos^0 pos^ --> TotalIntMR(pos^0*l^0)(pos^ *l^))
;; (assume "p^" "p^0" "TMRp0p")
;; (elim "TMRl0l")

;; ;; ?_7:allnc pos^,pos^0(
;; ;;      TotalPosMR pos^0 pos^ --> TotalIntMR(p^0*pos^0)(p^ *pos^))
;; (assume "q^1" "q^10" "TMRq10q1")
;; (use "TotalIntIntPosMR")
;; (use "PosTimesTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")

;; ;; ?_8:TotalIntMR(p^0*0)(p^ *0)
;; (ng #t)
;; (use "TotalIntIntZeroMR")

;; ;; ?_9:allnc pos^,pos^0(
;; ;;      TotalPosMR pos^0 pos^ --> TotalIntMR(p^0*IntN pos^0)(p^ *IntN pos^))
;; (assume "q^1" "q^10" "TMRq10q1")
;; (ng #t)
;; (use "TotalIntIntNegMR")
;; (use "PosTimesTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")

;; ;; ?_4:TotalIntMR(0*l^0)(0*l^)
;; (ng #t)
;; (use "TotalIntIntZeroMR")

;; ;; ?_5:allnc pos^,pos^0(
;; ;;      TotalPosMR pos^0 pos^ --> TotalIntMR(IntN pos^0*l^0)(IntN pos^ *l^))
;; (assume "p^" "p^0" "TMRp0p")
;; (elim "TMRl0l")

;; ;; ?_22:allnc pos^,pos^0(
;; ;;       TotalPosMR pos^0 pos^ --> TotalIntMR(IntN p^0*pos^0)(IntN p^ *pos^))
;; (assume "q^1" "q^10" "TMRq10q1")
;; (use "TotalIntIntNegMR")
;; (use "PosTimesTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")

;; ;; ?_23:TotalIntMR(IntN p^0*0)(IntN p^ *0)
;; (ng #t)
;; (use "TotalIntIntZeroMR")

;; ;; ?_24:allnc pos^,pos^0(
;; ;;       TotalPosMR pos^0 pos^ -->
;; ;;       TotalIntMR(IntN p^0*IntN pos^0)(IntN p^ *IntN pos^))
;; (assume "q^1" "q^10" "TMRq10q1")
;; (ng #t)
;; (use "TotalIntIntPosMR")
;; (use "PosTimesTotalReal")
;; (use "TMRp0p")
;; (use "TMRq10q1")
;; ;; Proof finished.
;; (save "IntTimesTotalReal")

(set-goal "all int int*IntZero=IntZero")
(cases)
(assume "pos")
(use "Truth")
(use "Truth")
(assume "pos")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "int*IntZero" "IntZero")

(set-goal "all int int*IntP One=int")
(cases)
;; 2-4
(assume "pos")
(use "Truth")
;; 3
(use "Truth")
;; 4
(assume "pos")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "int*IntP One" "int")

(set-goal "all int IntP One*int=int")
(cases)
;; 2-4
(assume "pos")
(use "Truth")
;; 3
(use "Truth")
;; 4
(assume "pos")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "IntP One*int" "int")

;; IntTimesComm
(set-goal "all int1,int2 int1*int2=int2*int1")
(cases)
;; 2-4
(assume "pos1")
(cases)
;; 6-8
(assume "pos2")
(ng)
(use "PosTimesComm")
;; 7
(ng)
(use "Truth")
;; 8
(assume "pos2")
(ng)
(use "PosTimesComm")
;; 3
(assume "int2")
(use "Truth")
;; 4
(assume "pos1")
(cases)
;; 16-18
(assume "pos2")
(ng)
(use "PosTimesComm")
;; 17
(ng)
(use "Truth")
;; 18
(assume "pos2")
(ng)
(use "PosTimesComm")
;; Proof finished.
(save "IntTimesComm")

;; IntTimesAssoc
(set-goal "all int1,int2,int3 int1*(int2*int3)=int1*int2*int3")
(cases)
;; 2-4
(assume "pos1")
(cases)
;; 6-8
(assume "pos2")
(cases)
;; 10-12
(assume "pos3")
(use "Truth")
;; 11
(use "Truth")
;; 12
(assume "pos3")
(use "Truth")
;; 7
(assume "int")
(use "Truth")
;; 8
(assume "pos2")
(cases)
;; 17-19
(assume "pos3")
(use "Truth")
;; 18
(use "Truth")
;; 19
(assume "pos3")
(use "Truth")
;; 3
(strip)
(use "Truth")
;; 4
(assume "pos1")
(cases)
;; 24-26
(assume "pos2")
(cases)
;; 28-30
(assume "pos3")
(use "Truth")
;; 29
(use "Truth")
;; 30
(assume "pos3")
(use "Truth")
;; 25
(assume "int")
(use "Truth")
;; 26
(assume "pos2")
(cases)
;; 35-37
(assume "pos3")
(use "Truth")
;; 36
(use "Truth")
;; 37
(assume "pos3")
(use "Truth")
;; Proof finished.
(save "IntTimesAssoc")
(add-rewrite-rule "int1*(int2*int3)" "int1*int2*int3")

;; We show that one IntUMinus can be moved out of a product.

;; IntTimesIdUMinus
(set-goal "all int1,int2 int1* ~int2= ~(int1*int2)")
(cases)
;; 2-4
(assume "pos1")
(cases)
;; 6-8
(assume "pos2")
(ng)
(use "Truth")
;; 7
(use "Truth")
;; 8
(assume "pos2")
(ng)
(use "Truth")
;; 3
(assume "int1")
(use "Truth")
;; 4
(assume "pos1")
(cases)
;; 15-17
(assume "pos2")
(ng)
(use "Truth")
;; 16
(use "Truth")
;; 17
(assume "pos2")
(ng)
(use "Truth")
;; Proof finished.
(save "IntTimesIdUMinus")

;; IntTimesUMinusId
(set-goal "all int1,int2 ~int1*int2= ~(int1*int2)")
(assume "int1" "int2")
(simp "IntTimesComm")
(simp "IntTimesIdUMinus")
(simp "IntTimesComm")
(use "Truth")
;; Proof finished.
(save "IntTimesUMinusId")

;; IntTimesPlusDistr.  It suffices to prove IntTimesPlusDistrPPN:
;; pos1*(pos2+IntN pos3)=pos1*pos2+pos1*IntN pos3.  This requires
;; comparison of p3 with p2, i.e., the consideration of the 3 cases
;; p3<p2 p3=p2 p2<p3.

;; IntTimesPlusDistr
(set-goal "all int1,int2,int3 int1*(int2+int3)=int1*int2+int1*int3")
;; IntTimesPlusDistrPPN
(assert "all pos1,pos2,pos3 pos1*(pos2+IntN pos3)=pos1*pos2+pos1*IntN pos3")
(assume "pos1" "pos2" "pos3")
(use "PosLeLtCases" (pt "pos3") (pt "pos2"))
(assume "p3<=p2")
(use "PosLeCases"  (pt "pos3") (pt "pos2"))
(use "p3<=p2")
(drop "p3<=p2")
(assume "p3<p2")
;; Case p3<p2
(simp "IntPlusPNP")
(simp "IntTimes3CompRule")
(simp "IntTimes2CompRule")
(simp "IntPlusPNP")
(use "PosTimesMinusDistr")
(use "p3<p2")
(use "PosLeLtMonTimes")
(use "Truth")
(use "p3<p2")
(use "p3<p2")
(assume "p3=p2")
;; Case p3=p2
(simp "p3=p2")
(ng #t)
(use "Truth")
(assume "p2<p3")
;; Case p2<p3
(simp "IntPlusPNN")
(simp "IntTimes3CompRule")
(simp "IntTimes3CompRule")
(simp "IntPlusPNN")
(use "PosTimesMinusDistr")
(use "p2<p3")
(use "PosLeLtMonTimes")
(use "Truth")
(use "p2<p3")
(use "p2<p3")
;; Proof of assertion finished.
(assume "IntTimesPlusDistrPPN")
;; Now we can tackle IntTimesPlusDistr
(cases)
;; 2-4
(assume "pos1")
(cases)
;; 6-8
(assume "pos2")
(cases)
;; 10-12
(assume "pos3")
(use "PosTimesPlusDistr" (pt "pos1") (pt "pos2") (pt "pos3"))
;; 11
(use "Truth")
;; 12
(assume "pos3")
(use "IntTimesPlusDistrPPN")
;; 7
(assume "int")
(use "Truth")
;; 8
(assume "pos2")
(cases)
;; 17-19
(assume "pos3")
(simp "IntPlusComm")
(simp "IntTimesPlusDistrPPN")
(simp "IntPlusComm")
(use "Truth")
;; 18
(use "Truth")
;; 19
(assume "pos3")
(ng)
(use "Truth")
;; 3
(strip)
(use "Truth")
;; 4
(assume "pos1")
(cases)
;; 28-30
(assume "pos2")
(cases)
;; 32-34
(assume "pos3")
(simp "IntPlus2CompRule")
(ng)
(use "Truth")
;; 33
(use "Truth")
;; 34
(assume "pos3")
(use "IntUMinusInj")
(simp "<-" "IntTimesUMinusId")
(simp "IntUMinus2CompRule")
(simp "IntUMinus1RewRule")
(simp "<-" "IntTimesUMinusId")
(simp "<-" "IntTimesUMinusId")
(simp "IntUMinus2CompRule")
(simp "IntUMinus2CompRule")
(simp "IntTimes2CompRule")
(simp "IntTimesPlusDistrPPN")
(use "Truth")
;; 29
(assume "int3")
(use "Truth")
;; 30
(assume "pos2")
(cases)
;; 51-53
(assume "pos3")
(use "IntUMinusInj")
(simp "<-" "IntTimesUMinusId")
(simp "IntUMinus2CompRule")
(simp "IntUMinus1RewRule")
(simp "<-" "IntTimesUMinusId")
(simp "<-" "IntTimesUMinusId")
(simp "IntUMinus2CompRule")
(simp "IntUMinus2CompRule")
(simp "IntTimes2CompRule")
(simp "IntPlusComm")
(simp "IntTimesPlusDistrPPN")
(simp "IntPlusComm")
(use "Truth")
;; 52
(use "Truth")
;; 53
(assume "pos3")
(ng)
(use "Truth")
;; Proof finished.
(save "IntTimesPlusDistr")
(add-rewrite-rule "int1*(int2+int3)" "int1*int2+int1*int3")

;; IntTimesPlusDistrLeft
(set-goal "all int1,int2,int3 (int1+int2)*int3=(int1*int3)+(int2*int3)")
(assume "int1" "int2" "int3")
(simp "IntTimesComm")
(simp "IntTimesPlusDistr")
(simp "IntTimesComm")
(assert "int3*int2=int2*int3")
 (use "IntTimesComm")
(assume "i3i2=i2i3")
(simp "i3i2=i2i3")
(use "Truth")
;; Proof finished.
(save "IntTimesPlusDistrLeft")
(add-rewrite-rule "(int1+int2)*int3" "(int1*int3)+(int2*int3)")

;; Rules for IntAbs

(add-computation-rules
 "abs IntZero" "Zero"
 "abs IntP pos" "PosToNat pos"
 "abs IntN pos" "PosToNat pos")

;; IntAbsTotal
(set-totality-goal "IntAbs")
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
(save-totality)

;; Rules for IntExp : int=>nat=>int

(add-computation-rules
 "int**Zero" "IntP One"
 "int1**Succ nat2" "int1**nat2*int1")

;; IntExpTotal
(set-totality-goal "IntExp")
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
(save-totality)

;; Strategy: do computations at the lowest possible level.  Raise outside.

;; We may assume that the given term is an original; otherwise use
;; term-to-original first.  If it is say a sum, take the original of
;; both components.  Let alg be the lub of their types.  If it is below
;; the type of the given term, do the addition at level alg already
;; (after embedding both components into alg via algebras-to-embedding)
;; and then embed the result into the type of the given term.

(set-goal "all pos1,nat2 (IntP pos1)**nat2=IntP(pos1**nat2)")
(assume "pos1")
(ind)
(use "Truth")
(assume "nat" "IH")
(ng #t)
(simp "IH")
(ng)
(use "Truth")
;; Proof finished.
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
(set-totality-goal "IntMax")
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
(save-totality)

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
(set-totality-goal "IntMin")
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
(save-totality)

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
(set-totality-goal "IntLt")
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
(save-totality)

;; IntTimesInj
(set-goal "all int1,int2,int3(0<abs int1 -> int1*int2=int1*int3 -> int2=int3)")
(cases)
;; 2-4
(assume "pos1")
(cases)
;; 6-8
(assume "pos2")
(cases)
;; 10-12
(assume "pos3" "Useless")
(ng)
(use "PosTimesInj")
;; 11
(ng)
(assume "Useless" "Absurd")
(use "Absurd")
;; 12
(assume "pos3")
(ng)
(assume "Useless" "Absurd")
(use "Absurd")
;; 7
(cases)
(ng)
(assume "pos3" "Useless" "Absurd")
(use "Absurd")
;; 21
(ng)
(strip)
(use "Truth")
;; 22
(ng)
(assume "pos2" "Useless" "Absurd")
(use "Absurd")
;; 8
(assume "pos2")
(cases)
;; 30-32
(ng)
(assume "pos3" "Useless" "Absurd")
(use "Absurd")
;; 31
(ng)
(assume "Useless" "Absurd")
(use "Absurd")
;; 32
(assume "pos3" "Useless")
(ng)
(use "PosTimesInj")
;; 3
(ng)
(assume "int2" "int3")
(use "Efq")
;; 4
(ng)
(assume "pos1")
(cases)
;; 43-45
(assume "pos2")
(cases)
;; 47-49
(assume "pos3" "Useless")
(ng)
(use "PosTimesInj")
;; 48
(ng)
(assume "Useless" "Absurd")
(use "Absurd")
;; 49
(assume "pos3" "Useless")
(ng)
(assume "Absurd")
(use "Absurd")
;; 44
(cases)
;; 57-59
(ng)
(assume "pos3" "Useless" "Absurd")
(use "Absurd")
;; 58
(strip)
(use "Truth")
;; 59
(ng)
(assume "pos3" "Useless" "Absurd")
(use "Absurd")
;; 45
(assume "pos2")
(cases)
;; 66-68
(ng)
(assume "pos3" "Useless" "Absurd")
(use "Absurd")
;; 67
(ng)
(assume "Useless" "Absurd")
(use "Absurd")
;; 68
(ng)
(assume "pos3" "Useless")
(use "PosTimesInj")
;; Proof finished.
(save "IntTimesInj")

;; IntTimesInjLeft
(set-goal "all int1,int2,int3(0<abs int3 -> int1*int3=int2*int3 -> int1=int2)")
(assume "int1" "int2" "int3" "PosHyp" "i1i3=i2i3")
(use "IntTimesInj" (pt "int3"))
(use "PosHyp")
(simp "IntTimesComm")
(simp "i1i3=i2i3")
(use "IntTimesComm")
;; Proof finished.
(save "IntTimesInjLeft")

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
(set-totality-goal "IntLe")
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
(save-totality)

;; IntLtToLe
(set-goal "all int1,int2(int1<int2 -> int1<=int2)")
(cases)
;; 2-4
(assume "pos1")
(cases)
;; 6-8
(assume "pos2")
(ng)
(use "PosLtToLe")
;; 7
(ng)
(assume "Absurd")
(use "Absurd")
;; 8
(assume "pos2")
(ng)
(assume "Absurd")
(use "Absurd")
;; 3
(cases)
(assume "pos2")
(ng)
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "pos2")
(ng)
(assume "Absurd")
(use "Absurd")
;; 4
(assume "pos1")
(cases)
(assume "pos2")
(ng)
(strip)
(use "Truth")
(ng)
(strip)
(use "Truth")
(assume "pos2")
(ng)
(use "PosLtToLe")
;; Proof finished.
(save "IntLtToLe")

(set-goal "all int (int<int)=False")
(cases)
;; 2-4
(assume "pos")
(use "Truth")
;; 3
(use "Truth")
;; 4
(assume "pos")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "int<int" "False")

(set-goal "all int,pos int<int+pos")
(cases)
;; 2-4
(assume "pos1" "pos2")
(use "Truth")
;; 3
(assume "pos1")
(use "Truth")
;; 4
(assume "pos1" "pos2")
(ng)
(cases (pt "pos1=pos2"))
(assume "p1=p2")
(ng)
(use "Truth")
(assume "p1=p2->F")
(ng)
(cases (pt "pos1<pos2"))
(assume "p1<p2")
(ng)
(use "Truth")
(assume "p1<p2->F")
(ng)
(assert "pos2<pos1")
 (use "PosNotLeToLt")
 (assume "p1<=p2") 
 (use "PosLeCases" (pt "pos1") (pt "pos2"))
 (use "p1<=p2")
 (use "p1<p2->F")
 (use "p1=p2->F")
(assume "p2<p1")
(inst-with-to "PosMinusPlusEq" (pt "pos1") (pt "pos2") "p2<p1"
	      "PosMinusPlusEqInst")
(simp "<-" "PosMinusPlusEqInst")
(ng)
(use "Truth")
;; Proof finished.
(add-rewrite-rule "int<int+pos" "True")

(set-goal "all int int<IntS int")
(assume "int")
(simp "<-" "IntPlusIdOne")
(ng)
(use "Truth")
;; Proof finished.
(add-rewrite-rule "int<IntS int" "True") 

(set-goal "all int int<=int")
(cases)
;; 2-4
(assume "pos")
(use "Truth")
;; 3
(use "Truth")
(assume "pos")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "int<=int" "True")

(set-goal "all int,pos int<=int+pos")
(assume "int" "pos")
(use "IntLtToLe")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "int<=int+pos" "True")

(set-goal "all int int<=IntS int")
(assume "int")
(simp "<-" "IntPlusIdOne")
(ng)
(use "Truth")
;; Proof finished.
(add-rewrite-rule "int<=IntS int" "True")

;; (set-goal "all nat,int int<=int+nat")
;; (cases)
;; (assume "int")
;; (use "Truth")
;; (assume "nat" "int")
;; (simp "NatToInt1CompRule")
;; (ng)
;; (simp "<-" "IntPlusIdOne")
;; (simp "<-" "IntPlusAssoc")
;; stuck, but probably non needed.

(set-goal "all pos IntS IntN pos<1")
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
(add-rewrite-rule "IntS IntN pos<1" "True")

(set-goal "all pos IntS IntN pos<=0")
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
(add-rewrite-rule "IntS IntN pos<=0" "True")

(set-goal "all pos (0<IntS IntN pos)=False")
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
(add-rewrite-rule "0<IntS IntN pos" "False")

(set-goal "all pos (1<=IntS IntN pos)=False")
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
(add-rewrite-rule "1<=IntS IntN pos" "False")

;; IntLtTrans
(set-goal "all int1,int2,int3(int1<int2 -> int2<int3 -> int1<int3)")
(cases)
;; 2-4
(assume "pos1")
(cases)
(assume "pos2")
(cases)
(assume "pos3")
(use "PosLtTrans")
(assume "Useless" "Absurd")
(use "Absurd")
(assume "pos3" "Useless" "Absurd")
(use "Absurd")
;; 7
(assume "int" "Absurd")
(use "Efq")
(use "Absurd")
;; 8
(assume "pos2" "int3" "Absurd")
(use "Efq")
(use "Absurd")
;; 3
(cases)
(assume "pos2")
(cases)
(strip)
(use "Truth")
(assume "Useless" "Absurd")
(use "Absurd")
(assume "pos3" "Useless" "Absurd")
(use "Absurd")
(assume "int" "Absurd")
(use "Efq")
(use "Absurd")
(assume "pos2" "int" "Absurd")
(use "Efq")
(use "Absurd")
;; 4
(assume "pos1")
(cases)
(assume "pos2")
(cases)
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "pos3" "Useless" "Absurd")
(use "Efq")
(use "Absurd")
(cases)
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "pos3" "Useless" "Absurd")
(use "Efq")
(use "Absurd")
(assume "pos2")
(cases)
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "pos3")
(ng)
(assume "p2<p1" "p3<p2")
(use "PosLtTrans" (pt "pos2"))
(use "p3<p2")
(use "p2<p1")
;; Proof finished.
(save "IntLtTrans")

;; The following theorems can be proved similarly from the
;; corresponding ones for pos.

;; IntLeTrans
(set-goal "all int1,int2,int3(int1<=int2 -> int2<=int3 -> int1<=int3)")
(cases)
;; 2-4
(assume "pos1")
(cases)
(assume "pos2")
(cases)
(assume "pos3")
(use "PosLeTrans")
(assume "Useless" "Absurd")
(use "Absurd")
(assume "pos3" "Useless" "Absurd")
(use "Absurd")
;; 7
(assume "int" "Absurd")
(use "Efq")
(use "Absurd")
;; 8
(assume "pos2" "int3" "Absurd")
(use "Efq")
(use "Absurd")
;; 3
(cases)
(assume "pos2")
(cases)
(strip)
(use "Truth")
(assume "Useless" "Absurd")
(use "Truth")
(assume "pos3" "Useless" "Absurd")
(use "Absurd")
(assume "int" "Useless" "0<=int")
(use "0<=int")
(assume "pos2" "int" "Absurd")
(use "Efq")
(use "Absurd")
;; 4
(assume "pos1")
(cases)
(assume "pos2")
(cases)
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "pos3" "Useless" "Absurd")
(use "Efq")
(use "Absurd")
(cases)
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "pos3" "Useless" "Absurd")
(use "Efq")
(use "Absurd")
(assume "pos2")
(cases)
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "pos3")
(ng)
(assume "p2<=p1" "p3<=p2")
(use "PosLeTrans" (pt "pos2"))
(use "p3<=p2")
(use "p2<=p1")
;; Proof finished.
(save "IntLeTrans")

;; IntLeLtTrans
(set-goal "all int1,int2,int3(int1<=int2 -> int2<int3 -> int1<int3)")
(cases)
;; 2-4
(assume "pos1")
(cases)
(assume "pos2")
(cases)
(assume "pos3")
(use "PosLeLtTrans")
(assume "Useless" "Absurd")
(use "Absurd")
(assume "pos3" "Useless" "Absurd")
(use "Absurd")
;; 7
(assume "int" "Absurd")
(use "Efq")
(use "Absurd")
;; 8
(assume "pos2" "int3" "Absurd")
(use "Efq")
(use "Absurd")
;; 3
(cases)
(assume "pos2")
(cases)
(strip)
(use "Truth")
(assume "Useless" "Absurd")
(use "Absurd")
(assume "pos3" "Useless" "Absurd")
(use "Absurd")
(assume "int" "Useless" "0<int")
(use "0<int")
(assume "pos2" "int" "Absurd")
(use "Efq")
(use "Absurd")
;; 4
(assume "pos1")
(cases)
(assume "pos2")
(cases)
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "pos3" "Useless" "Absurd")
(use "Efq")
(use "Absurd")
(cases)
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "pos3" "Useless" "Absurd")
(use "Efq")
(use "Absurd")
(assume "pos2")
(cases)
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "pos3")
(ng)
(assume "p2<=p1" "p3<p2")
(use "PosLtLeTrans" (pt "pos2"))
(use "p3<p2")
(use "p2<=p1")
;; Proof finished.
(save "IntLeLtTrans")

;; IntLtLeTrans
(set-goal "all int1,int2,int3(int1<int2 -> int2<=int3 -> int1<int3)")
(cases)
;; 2-4
(assume "pos1")
(cases)
(assume "pos2")
(cases)
(assume "pos3")
(use "PosLtLeTrans")
(assume "Useless" "Absurd")
(use "Absurd")
(assume "pos3" "Useless" "Absurd")
(use "Absurd")
;; 7
(assume "int" "Absurd")
(use "Efq")
(use "Absurd")
;; 8
(assume "pos2" "int3" "Absurd")
(use "Efq")
(use "Absurd")
;; 3
(cases)
(assume "pos2")
(cases)
(strip)
(use "Truth")
(assume "Useless" "Absurd")
(use "Absurd")
(assume "pos3" "Useless" "Absurd")
(use "Absurd")
(assume "int" "Absurd")
(use "Efq")
(use "Absurd")
(assume "pos2" "int" "Absurd")
(use "Efq")
(use "Absurd")
;; 4
(assume "pos1")
(cases)
(assume "pos2")
(cases)
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "pos3" "Useless" "Absurd")
(use "Efq")
(use "Absurd")
(cases)
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "pos3" "Useless" "Absurd")
(use "Efq")
(use "Absurd")
(assume "pos2")
(cases)
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "pos3")
(ng)
(assume "p2<p1" "p3<=p2")
(use "PosLeLtTrans" (pt "pos2"))
(use "p3<=p2")
(use "p2<p1")
;; Proof finished.
(save "IntLtLeTrans")

;; IntNotLeToLt
(set-goal "all int1,int2((int1<=int2 -> F) -> int2<int1)")
(cases)
;; 2-4
(assume "pos1")
(cases)
;; 6-8
(assume "pos")
(ng)
(use "PosNotLeToLt")
;; 7
(strip)
(use "Truth")
;; 8
(strip)
(use "Truth")
;; 3
(cases)
(assume "pos2" "Absurd")
(use "Absurd")
(use "Truth")
(assume "Absurd")
(use "Absurd")
(use "Truth")
(strip)
(use "Truth")
;; 4
(assume "pos1")
(cases)
;; 22-24
(assume "pos2" "Absurd")
(use "Absurd")
(use "Truth")
;; 23
(assume "Absurd")
(use "Absurd")
(use "Truth")
;; 24
(assume "pos2")
(ng)
(use "PosNotLeToLt")
;; Proof finished.
(save "IntNotLeToLt")

;; IntNotLtToLe
(set-goal "all int1,int2((int1<int2 -> F) -> int2<=int1)")
(cases)
;; 2-4
(assume "pos1")
(cases)
;; 6-8
(assume "pos")
(ng)
(use "PosNotLtToLe")
;; 7
(strip)
(use "Truth")
;; 8
(strip)
(use "Truth")
;; 3
(cases)
(assume "pos2" "Absurd")
(use "Absurd")
(use "Truth")
(assume "Useless")
(use "Truth")
(assume "pos2" "Useless")
(use "Truth")
;; 4
(assume "pos1")
(cases)
;; 21-23
(assume "pos2" "Absurd")
(use "Absurd")
(use "Truth")
;; 22
(assume "Absurd")
(use "Absurd")
(use "Truth")
;; 23
(assume "pos2")
(ng)
(use "PosNotLtToLe")
;; Proof finished.
(save "IntNotLtToLe")

;; IntLeAntiSym
(set-goal "all int1,int2(int1<=int2 -> int2<=int1 -> int1=int2)")
(cases)
;; 2-4
(assume "pos1")
(cases)
;; 6-8
(assume "pos2")
(use "PosLeAntiSym")
;; 7
(ng)
(assume "Absurd" "Useless")
(use "Absurd")
;; 8
(assume "pos2")
(ng)
(assume "Absurd" "Useless")
(use "Absurd")
;; 3
(cases)
;; 15-17
(assume "pos2")
(ng)
(assume "Useless" "Absurd")
(use "Absurd")
;; 16
(strip)
(use "Truth")
;; 17
(assume "pos2")
(ng)
(assume "Absurd" "Useless")
(use "Absurd")
;; 4
(assume "pos1")
(cases)
;; 26-28
(assume "pos2")
(ng)
(assume "Useless" "Absurd")
(use "Absurd")
;; 27
(ng)
(assume "Useless" "Absurd")
(use "Absurd")
;; 28
(assume "pos2" "p2<=p1" "p1<=p2")
(use "PosLeAntiSym")
(use "p1<=p2")
(use "p2<=p1")
;; Proof finished.
(save "IntLeAntiSym")

;; Next relations of IntLt, IntLe with IntUMinus

;; IntLtUMinus
(set-goal "all int1,int2 (~int2< ~int1)=(int1<int2)")
(cases)
;; 2-4
(assume "pos1")
(cases)
;; 6-8
(assume "pos2")
(ng)
(use "Truth")
;; 7
(ng)
(use "Truth")
;; 8
(assume "pos2")
(ng)
(use "Truth")
;; 3
(cases)
;; 14-16
(assume "pos1")
(ng)
(use "Truth")
;; 15
(ng)
(use "Truth")
;; 16
(assume "pos2")
(ng)
(use "Truth")
;; 4
(assume "pos1")
(cases)
;; 23025
(assume "pos2")
(ng)
(use "Truth")
;; 24
(ng)
(use "Truth")
;; 25
(assume "pos2")
(ng)
(use "Truth")
;; Proof finished.
(save "IntLtUMinus")
(add-rewrite-rule "~int2< ~int1" "int1<int2")

;; IntLeUMinus
(set-goal "all int1,int2 (~int2<= ~int1)=(int1<=int2)")
(cases)
;; 2-4
(assume "pos1")
(cases)
;; 6-8
(assume "pos2")
(ng)
(use "Truth")
;; 7
(ng)
(use "Truth")
;; 8
(assume "pos2")
(ng)
(use "Truth")
;; 3
(cases)
;; 14-16
(assume "pos1")
(ng)
(use "Truth")
;; 15
(ng)
(use "Truth")
;; 16
(assume "pos2")
(ng)
(use "Truth")
;; 4
(assume "pos1")
(cases)
;; 23-25
(assume "pos2")
(ng)
(use "Truth")
;; 24
(ng)
(use "Truth")
;; 31
(assume "pos2")
(ng)
(use "Truth")
;; Proof finished.
(save "IntLeUMinus")
(add-rewrite-rule "~int2<= ~int1" "int1<=int2")

;; IntLtMonPredIntP
(set-goal "all pos1,pos2(pos1<pos2 -> IntPred pos1<IntPred pos2)")
(assume "pos1" "pos2" "p1<p2")
(use "PosLeCases" (pt "One") (pt "pos1"))
(use "Truth")
(assume "1<p1")
(assert "1<pos2")
(use "PosLtTrans" (pt "pos1"))
(use "1<p1")
(use "p1<p2")
(assume "1<p2")
(assert "PosS(PosPred pos1)=pos1")
 (use "PosSPosPredId")
 (use "1<p1")
(assume "PosS(PosPred pos1)=pos1")
(simp "<-" "PosS(PosPred pos1)=pos1")
(drop "PosS(PosPred pos1)=pos1")
(assert "PosS(PosPred pos2)=pos2")
 (use "PosSPosPredId")
 (use "1<p2")
(assume "PosS(PosPred pos2)=pos2")
(simp "<-" "PosS(PosPred pos2)=pos2")
(drop "PosS(PosPred pos2)=pos2")
(ng)
(use "PosLtMonPred")
(use "1<p1")
(use "p1<p2")
;; 5
(assume "1=pos1")
(assert "1<pos2")
 (simp "1=pos1")
 (use "p1<p2")
(assume "1<p2")
(simp "<-" "1=pos1")
(ng)
(assert "PosS(PosPred pos2)=pos2")
 (use "PosSPosPredId")
 (use "1<p2")
(assume "PosS(PosPred pos2)=pos2")
(simp "<-" "PosS(PosPred pos2)=pos2")
(drop "PosS(PosPred pos2)=pos2")
(ng)
(use "Truth")
;; Proof finished.
(save "IntLtMonPredIntP")

;; IntLtMonIntS
(set-goal "all int1,int2(int1<int2 -> IntS int1<IntS int2)")
(cases)
;; 2-4
(assume "pos1")
(cases)
;; 6-8
(assume "pos2")
(ng)
(assume "p1<p2")
(use "p1<p2")
;; 7
(ng)
(assume "Absurd")
(use "Absurd")
;; 8
(assume "pos2")
(ng)
(use "Efq")
;; 3
(cases)
(assume "pos2")
(ng)
(strip)
(use "Truth")
;; 17
(ng)
(assume "Absurd")
(use "Absurd")
;; 18
(assume "pos2")
(ng)
(use "Efq")
;; 4
(assume "pos1")
(cases)
;; 27-29
(assume "pos2")
(ng)
(assume "Useless")
;; ?_32:IntS IntN pos1<PosS pos2
(use "IntLtLeTrans" (pt "IntP 1"))
(use "Truth")
(use "Truth")
;; 28
(ng)
(strip)
(use "Truth")
;; 29
(assume "pos2")
;; ?_37:IntN pos1<IntN pos2 -> IntS IntN pos1<IntS IntN pos2
(ng)
;; ?_38:pos2<pos1 -> IntS IntN pos1<IntS IntN pos2
(simp "<-" "IntUMinus1CompRule")
(simp "<-" "IntUMinus1CompRule")
(simp "<-" "IntUMinus3RewRule")
(simp "<-" "IntUMinus3RewRule")
(simp "IntLtUMinus")
;; ?_43:pos2<pos1 -> IntPred pos2<IntPred pos1
(use "IntLtMonPredIntP")
;; Proof finished.
(save "IntLtMonIntS")

;; IntLtMonIntPred
(set-goal "all int1,int2(int1<int2 -> IntPred int1<IntPred int2)")
(cases)
;; 2-4
(assume "pos1")
(cases)
;; 6-8
(assume "pos2")
(ng)
(use "IntLtMonPredIntP")
;; 7
(ng)
(use "Efq")
;; 8
(assume "pos2")
(ng)
(use "Efq")
;; 3
(cases)
; 14-16
(assume "pos2" "Useless")
(simp "<-" "IntLtUMinus")
(ng)
(use "Truth")
;; 15
(assume "Absurd")
(use "Absurd")
;; 16
(assume "pos2")
(ng)
(assume "Absurd")
(use "Absurd")
;; 4
(assume "pos1")
(cases)
;; 25-27
(assume "pos2" "Useless")
(simp "<-" "IntLtUMinus")
(ng)
(use "IntLtTrans" (pt "IntP 1"))
(use "Truth")
(use "Truth")
;; 26
(ng)
(strip)
(use "Truth")
;; 27
(assume "pos2")
(ng)
(assume "p2<p1")
(use "p2<p1")
;; Proof finished.
(save "IntLtMonIntPred")

;; We turn this into a rewrite rule
(set-goal "all int1,int2 (IntS int1<IntS int2)=(int1<int2)")
(assume "int1" "int2")
(use "BooleAeqToEq")
;; 3,4
(assume "IntS int1<IntS int2")
(assert "IntPred(IntS int1)=int1")
 (use "Truth")
(assume "IntPred(IntS int1)=int1")
(simp "<-" "IntPred(IntS int1)=int1")
(drop "IntPred(IntS int1)=int1")
(assert "IntPred(IntS int2)=int2")
 (use "Truth")
(assume "IntPred(IntS int2)=int2")
(simp "<-" "IntPred(IntS int2)=int2")
(drop "IntPred(IntS int2)=int2")
(use "IntLtMonIntPred")
(use "IntS int1<IntS int2")
;; 4
(use "IntLtMonIntS")
;; Proof finished.
(add-rewrite-rule "IntS int1<IntS int2" "int1<int2")

;; Same for IntLe
(set-goal "all int1,int2 (IntS int1<=IntS int2)=(int1<=int2)")
(assume "int1" "int2")
(use "BooleAeqToEq")
;; 3,4
(assume "Si1<=Si2")
(use "IntNotLtToLe")
(assume "i2<i1")
(assert "IntS int2<IntS int1 -> IntS int1<IntS int1")
 (use "IntLeLtTrans")
 (use "Si1<=Si2")
(assume "Assertion")
(ng)
(use "Assertion")
(use "i2<i1")
;; 4
(assume "i1<=i2")
(use "IntNotLtToLe")
(assume "i2<i1")
(assert "int2<int1 -> int1<int1")
 (use "IntLeLtTrans")
 (use "i1<=i2")
(assume "Assertion")
(ng)
(use "Assertion")
(use "i2<i1")
;; Proof finished.
(add-rewrite-rule "IntS int1<=IntS int2" "int1<=int2")

(set-goal "all int1,int2,pos (int1*pos<=int2*pos)=(int1<=int2)")
(cases)
;; 2-4
(assume "pos1")
(cases)
;; 6-8
(assume "pos2" "pos")
(use "Truth")
;; 7
(assume "pos2")
(use "Truth")
;; 8
(assume "pos2" "pos")
(use "Truth")
;; 3
(cases)
;; 12-14
(strip)
(use "Truth")
;; 13
(strip)
(use "Truth")
;; 14
(strip)
(use "Truth")
;; 4
(assume "pos1")
(cases)
;; 19-21
(strip)
(use "Truth")
;; 20
(strip)
(use "Truth")
;; 21
(strip)
(use "Truth")
;; Proof finished
(add-rewrite-rule "int1*pos<=int2*pos" "int1<=int2")

;; IntLeMonTimes
(set-goal "all int1,int2,int3(0<=int1 -> int2<=int3 -> int2*int1<=int3*int1)")
(cases)
;; 2-4
(assume "pos1")
(cases)
;; 6-8
(assume "pos2")
(cases)
;; 10-12
(assume "pos3" "Useless" "p2<=p3")
(ng)
(use "p2<=p3")
;; 11
(ng)
(assume "Useless" "Absurd")
(use "Absurd")
;; 12
(assume "pos3" "Useless" "Absurd")
(use "Efq")
(use "Absurd")
;; 7
(cases)
(strip)
(use "Truth")
(ng)
(strip)
(use "Truth")
(assume "pos3" "Useless" "Absurd")
(use "Efq")
(use "Absurd")
;; 8
(assume "pos2")
(cases)
(strip)
(use "Truth")
(strip)
(use "Truth")
(assume "pos3" "Useless")
(ng)
(assume "p3<=p2")
(use "p3<=p2")
;; 3
(strip)
(use "Truth")
;; 4
(assume "pos1" "int2" "int3" "Absurd")
(use "Efq")
(use "Absurd")
;; Proof finished.
(save "IntLeMonTimes")

;; (search-about "IntS" "Mon")
;; For IntLeMonPlus : int1<=int2 -> int3<=int4 -> int1+int3<=int2+int4
;; it suffices to prove int1<=int2 -> int1+int3<=int2+int3

;; Plan for not saving some theorems immediate from IntLeMonPlus:
;; IntLtPlusIntN int+IntN pos<int  
;; IntLePlusIntN int+IntN pos<=int uses IntLtPlusIntN

;; IntLtPlusIntP int<int+pos  uses IntLtPlusIntN
;; IntLePlusIntP int<=int+pos  uses IntLePlusIntN

;; IntLeMonPlusIntN pos3<=pos2 -> int1+IntN pos2<=int1+IntN pos3
;; IntLeMonPlusIntP pos2<=pos3 -> int1+pos2<=int1+pos3 uses IntLeMonPlusIntN

;; IntLeMonPlusAux int2<=int3 -> int1+int2<=int1+int3 uses
;;   IntLePlusIntN IntLeMonPlusIntN IntLeMonPlusIntP IntLePlusIntP

;; IntLeMonPlus int1<=int2 -> int3<=int4 -> int1+int3<=int2+int4
;; uses IntLeMonPlusAux

;; IntLeMonPlus
(set-goal
 "all int1,int2,int3,int4(int1<=int2 -> int3<=int4 -> int1+int3<=int2+int4)")

;; We will need (in this order) theorems we do not want to save:
;; IntLtPlusIntN
;; IntLePlusIntN
;; IntLePlusIntP
;; IntLeMonPlusIntN
;; IntLeMonPlusIntP 
;; IntLeMonPlusAux

;; IntLtPlusIntN
(assert "all int,pos int+IntN pos<int")
(cases)
;; 2-4
(assume "pos1" "pos2")
(ng)
(cases (pt "pos1=pos2"))
(assume "p1=p2")
(ng)
(use "Truth")
(assume "p1=p2->F")
(ng)
(cases (pt "pos1<pos2"))
(assume "p1<p2")
(ng)
(use "Truth")
(assume "p1<p2->F")
(ng)
(assert "pos2<pos1")
 (use "PosNotLeToLt")
 (assume "p1<=p2") 
 (use "PosLeCases" (pt "pos1") (pt "pos2"))
 (use "p1<=p2")
 (use "p1<p2->F")
 (use "p1=p2->F")
(assume "p2<p1")
(inst-with-to "PosMinusPlusEq" (pt "pos1") (pt "pos2") "p2<p1"
	      "PosMinusPlusEqInst")
(simp "<-" "PosMinusPlusEqInst")
(ng)
(use "Truth")
;; 3
(ng)
(strip)
(use "Truth")
;; 4
(ng)
(strip)
(use "Truth")
;; Subproof finished.
(assume  "IntLtPlusIntN")

;; IntLePlusIntN
(assert "all int,pos int+IntN pos<=int")
(assume "int" "pos")
(use "IntLtToLe")
(use "IntLtPlusIntN")
;; Subproof finished.
(assume "IntLePlusIntN")

;; IntLtPlusIntP
(assert "all int,pos int<int+pos")
(assume "int" "pos")
(simp "<-" "IntLtUMinus")
(ng)
(use "IntLtPlusIntN")
;; Subproof finished.
(assume "IntLtPlusIntP")

;; IntLePlusIntP
(assert "all int,pos int<=int+pos")
(assume "int" "pos")
(simp "<-" "IntLeUMinus")
(ng)
(use "IntLePlusIntN")
;; Subproof finished.
(assume "IntLePlusIntP")

;; IntLeMonPlusIntN
(assert "all int1,pos2,pos3(pos3<=pos2 -> int1+IntN pos2<=int1+IntN pos3)")
(cases)
;; 2-4
(assume "pos1" "pos2" "pos3" "p3<=p2")
(ng)
(cases (pt "pos1=pos2"))
(assume "p1=p2")
(ng)
(simp "p1=p2")
(cases (pt "pos2=pos3"))
(strip)
(ng)
(use "Truth")
(assume "p2=p3 -> F")
(ng)
(assert "pos2<pos3 -> F")
 (assume "p2<p3")
 (assert "pos2<pos2")
  (use "PosLtLeTrans" (pt "pos3"))
  (use "p2<p3")
  (use "p3<=p2")
 (assume "p2<p2")
 (use "p2<p2")
(assume "p2<p3 -> F")
(simp "p2<p3 -> F")
(use "Truth")
;; 8
(assume "p1=p2 -> F")
(ng)
(cases (pt "pos1<pos2"))
;; 30,31
(assume "p1<p2")
(ng)
(cases (pt "pos1=pos3"))
(assume "p1=p3")
(ng)
(use "Truth")
(assume "p1=p3 -> F")
(ng)
(cases (pt "pos1<pos3"))
(assume "p1<p3")
(ng)
(use "PosLeCases" (pt "pos3") (pt "pos2"))
(use "p3<=p2")
(assume "p3<p2")
(use "PosLtToLe")
(use "PosLtMonMinusLeft")
(use "p3<p2")
(use "p1<p3")
(assume "p3=p2")
(simp "p3=p2")
(use "Truth")
;; 41
(assume "p1<p3 -> F")
(ng)
(use "Truth")
;; 31
(assume "p1<p2 -> F")
(ng)
(assert "pos1=pos3 -> F")
 (assume "p1=p3")
 (use "PosLeCases" (pt "pos2") (pt "pos1"))
 (use "PosNotLtToLe")
 (use "p1<p2 -> F")
 (assume "p2<p1")
 (assert "pos3<pos3")
  (use "PosLeLtTrans" (pt "pos2"))
  (use "p3<=p2")
  (simp "<-" "p1=p3")
  (use "p2<p1")
 (assume "p3<p3")
 (use "p3<p3")
 (assume "p2=p1")
 (use "p1=p2 -> F")
 (simp "p2=p1")
 (use "Truth")
(assume "p1=p3 -> F")
(simp "p1=p3 -> F")
(ng)
(assert "pos1<pos3 -> F")
 (assume "p1<p3")
 (use "p1<p2 -> F")
 (use "PosLtLeTrans" (pt "pos3"))
 (use "p1<p3")
 (use "p3<=p2")
(assume "p1<p3 -> F")
(simp "p1<p3 -> F")
(ng)
(assert "NatToPos(PosToNat(pos1--pos2))<=NatToPos(PosToNat(pos1--pos3))") 
 (simp "NatToPosLe")
 (simp "PosToNatMinus")
 (simp "PosToNatMinus")
 (use "NatLeMonMinus")
 (use "Truth")
 (simp "PosToNatLe")
 (use "p3<=p2")

 (use "PosLeCases" (pt "pos3") (pt "pos1"))
 (use "PosNotLtToLe")
 (use "p1<p3 -> F")
 (assume "p3<p1")
 (use "p3<p1")
 (assume "p3=p1")
 (simp "p3=p1")
 (use "p1=p3 -> F")
 (simp "p3=p1")
 (use "Truth")
 
 (use "PosLeCases" (pt "pos2") (pt "pos1"))
 (use "PosNotLtToLe")
 (use "p1<p2 -> F")
 (assume "p2<p1")
 (use "p2<p1")
 (assume "p2=p1")
 (simp "p2=p1")
 (use "p1=p2 -> F")
 (simp "p2=p1")
 (use "Truth")

 (use "NatLt0Pos")
 (use "NatLt0Pos")
;; Assertion proved.
(simp "NatToPosToNatId")
(simp "NatToPosToNatId")
(assume "Hyp")
(use "Hyp")
;; 3
(ng)
(assume "pos2" "pos3" "p3<=p2")
(use "p3<=p2")
;; 4
(ng)
(assume "pos1" "pos2" "pos3" "p3<=p2")
(use "PosLeMonPlus")
(use "Truth")
(use "p3<=p2")
;; Subproof finished.
(assume "IntLeMonPlusIntN")

;; IntLeMonPlusIntP
(assert "all int1,pos2,pos3(pos2<=pos3 -> int1+pos2<=int1+pos3)")
(assume "int1" "pos2" "pos3" "p2<=p3")
(simp "<-" "IntLeUMinus")
(ng)
(use "IntLeMonPlusIntN")
(use "p2<=p3")
;; Subproof finished
(assume "IntLeMonPlusIntP")

;; IntLeMonPlusAux
(assert "all int1,int2,int3(int2<=int3 -> int1+int2<=int1+int3)")
(cases)
;; 2-4
(assume "pos1")
(cases)
;; 6-8
(assume "pos2")
(cases)
;; 10-12
(assume "pos3" "p2<=p3")
(use "PosLeMonPlus")
(use "Truth")
(use "p2<=p3")
;; 11
(ng)
(assume "Absurd")
(use "Absurd")
;; 12
(assume "pos3" "Absurd")
(use "Efq")
(use "Absurd")
;; 7
(cases)
(strip)
(use "Truth")
(ng)
(strip)
(use "Truth")
(assume "pos3" "Absurd")
(use "Efq")
(use "Absurd")
;; 8
(assume "pos2")
(cases)
(assume "pos3" "Useless")
(use "IntLeTrans" (pt "IntP pos1"))
;; ?_33:pos1+IntN pos2<=pos1
(use "IntLePlusIntN")
(ng)
(use "Truth")
(assume "Useless")
(use "IntLeTrans" (pt "IntP pos1"))
(use "IntLePlusIntN")
(use "Truth")
;; 31
(assume "pos3")
;; ?_39:IntN pos2<=IntN pos3 -> pos1+IntN pos2<=pos1+IntN pos3
(assume "p3<=p2")
(ng "p3<=p2")
(use "IntLeMonPlusIntN")
(use "p3<=p2")
;; 3
(assume "int2" "int3" "i2<=i3")
(use "i2<=i3")
;; 4
(assume "pos1")
(cases)
;; 45-47
(assume "pos2")
(cases)
;; 49-51
(assume "pos3" "p2<=p3")
(ng "p2<=p3")
(use "IntLeMonPlusIntP")
(use "p2<=p3")
;; 50
(assume "Absurd")
(use "Efq")
(use "Absurd")
;; 51
(assume "pos3" "Absurd")
(use "Efq")
(use "Absurd")
; 46
(cases)
;; 59-61
(assume "pos3" "Useless")
;; ?_62:IntN pos1+0<=IntN pos1+pos3
(assert "IntN pos1+0=IntN pos1")
 (use "Truth")
(assume "IntN pos1+0=IntN pos1")
(simp "IntN pos1+0=IntN pos1")
(drop "IntN pos1+0=IntN pos1")
(use "IntLePlusIntP")
;; 60
(strip)
(use "Truth")
;; 61
(assume "pos3" "Absurd")
(use "Efq")
(use "Absurd")
;; 47
(assume "pos2")
(cases)
;; 72-74
(assume "pos3" "Useless")
(use "IntLeTrans" (pt "IntN pos1"))
(use "IntLePlusIntN")
(use "IntLePlusIntP")
;; 73
(assume "Useless")
(assert "IntN pos1+0=IntN pos1")
 (use "Truth")
(assume "IntN pos1+0=IntN pos1")
(simp "IntN pos1+0=IntN pos1")
(drop "IntN pos1+0=IntN pos1")
(use "IntLePlusIntN")
;; 74
(assume "pos3" "p3<=p2")
(ng "p3<=p2")
(use "IntLeMonPlusIntN")
(use "p3<=p2")
;; Subproof finished.
(assume "IntLeMonPlusAux")

;; Now for the main goal.
(assume "int1" "int2" "int3" "int4" "i1<=i2" "i3<=i4")
(use "IntLeTrans" (pt "int1+int4"))
(use "IntLeMonPlusAux")
(use "i3<=i4")
(simp "IntPlusComm")
(use "IntLeTrans" (pt "int4+int2"))
(use "IntLeMonPlusAux")
(use "i1<=i2")
(simp "IntPlusComm")
(use "Truth")
;; Proof finished.
(save "IntLeMonPlus")

;; IntLtIntS
(set-goal "all int1,int2 (int1<IntS int2)=(int1<=int2)")
(cases)
;; 2-4
(assume "pos1")
(cases)
;; 6-8
(assume "pos2")
(ng)
(simp "PosLtPosS")
(use "Truth")
;; 7
(ng)
(use "Truth")
;; 8
(assume "pos2")
(ng)
(use "BooleAeqToEq")
(assume "p1<S~p1")
(assert "0<IntS IntN pos2")
 (use "IntLtTrans" (pt "IntP pos1"))
 (use "Truth")
 (use "p1<S~p1")
(ng)
(assume "Absurd")
(use "Absurd")
(use "Efq")
;; 3
(cases)
(strip)
(use "Truth")
(ng)
(strip)
(use "Truth")
(ng)
(strip)
(use "Truth")
;; 4
(assume "pos1")
(cases)
;; 33-35
(assume "pos2")
(ng)
(use "Truth")
(ng)
(use "Truth")
(assume "pos2")
(ng)
;; ?_40:(IntN pos1<IntS IntN pos2)=(pos2<=pos1)
(simp "<-" "IntUMinus1CompRule")
(simp "<-" "IntUMinus1CompRule")
(simp "<-" "IntUMinus3RewRule")
(simp "IntLtUMinus")
;; ?_44:(IntPred pos2<pos1)=(pos2<=pos1)
(use "PosLeCases" (pt "1") (pt "pos2"))
(use "Truth")
(assume "1<p2")
(assert "all pos(1<pos -> IntP(PosPred pos)=IntPred pos)")
 (assume "pos" "1<p")
 (assert "PosS(PosPred pos)=pos")
  (use "PosSPosPredId")
  (use "1<p")
 (assume "PosS(PosPred pos)=pos")
 (simp "<-" "PosS(PosPred pos)=pos")
 (drop "PosS(PosPred pos)=pos")
 (ng)
 (use "Truth")
(assume "PosPredIntPredId")
(inst-with-to "PosPredIntPredId" (pt "pos2") "1<p2" "PosPredIntPredIdInst")
(simp "<-" "PosPredIntPredIdInst")
(ng)
(simp "<-" "PosLtPosS")
(assert "PosS(PosPred pos2)=pos2")
 (use "PosSPosPredId")
 (use "1<p2")
(assume "PosS(PosPred pos2)=pos2")
(simp "<-" "PosS(PosPred pos2)=pos2")
(drop "PosS(PosPred pos2)=pos2")
(ng)
(use "Truth")
;; 47
(assume "1=pos2")
(simp "<-" "1=pos2")
(ng)
(use "Truth")
;; Proof finished.
(save "IntLtIntS")

;; IntLeIntS
(set-goal "all int1,int2 (IntS int1<=int2)=(int1<int2)")
(assume "int1" "int2")
(inst-with-to "IntLtIntS" (pt "IntS int1") (pt "int2") "IntLtIntSInst")
(ng "IntLtIntSInst")
(simp "IntLtIntSInst")
(use "Truth")
;; Proof finished.
(save "IntLeIntS")

