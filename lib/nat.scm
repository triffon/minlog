;; 2017-04-01.  nat.scm

;; (load "~/git/minlog/init.scm")

(display "loading nat.scm ...") (newline)

(add-algs "nat" '("Zero" "nat") '("Succ" "nat=>nat"))
(add-var-name "n" "m" "l" (py "nat")) ;l instead of k, which will be an int

(add-totality "nat")

;; This adds the c.r. predicate TotalNat with clauses
;; TotalNatZero:	TotalNat Zero
;; TotalNatSucc:	allnc nat^(TotalNat nat^ -> TotalNat(Succ nat^))

(add-totalnc "nat")
(add-co "TotalNat")
(add-co "TotalNatNc")

(add-eqp "nat")
(add-co "EqPNat")
(add-eqpnc "nat")
(add-co "EqPNatNc")

;; NatTotalVar
(set-goal "all n TotalNat n")
(use "AllTotalIntro")
(assume "n^" "Tn")
(use "Tn")
;; Proof finished
(save "NatTotalVar")

;; (cdp (proof-to-soundness-proof))
;; Uses the axiom AllTotalIntroSound.

(define (make-numeric-term-wrt-nat n)
  (if (= n 0)
      (pt "Zero")
      (make-term-in-app-form
       (pt "Succ")
       (make-numeric-term-wrt-nat (- n 1)))))

;; The following is in term.scm, because it is used for term-to-expr
;; (define (is-numeric-term-wrt-nat? term)
;;   (or
;;    (and (term-in-const-form? term)
;; 	(string=? "Zero" (const-to-name (term-in-const-form-to-const term))))
;;    (and (term-in-app-form? term)
;; 	(let ((op (term-in-app-form-to-op term)))
;; 	  (and (term-in-const-form? op)
;; 	       (string=? "Succ" (const-to-name
;; 				 (term-in-const-form-to-const op)))
;; 	       (is-numeric-term-wrt-nat? (term-in-app-form-to-arg term)))))))

;; (define (numeric-term-wrt-nat-to-number term)
;;   (if (equal? term (pt "Zero"))
;;       0
;;       (+ 1 (numeric-term-wrt-nat-to-number (term-in-app-form-to-arg term)))))

;; The functions make-numeric-term (used by the parser) and
;; is-numeric-term?, numeric-term-to-number (used by term-to-expr and
;; token-tree-to-string) take either pos or nat as default.

(define NAT-NUMBERS #t)

(define (make-numeric-term x)
  (if NAT-NUMBERS
      (make-numeric-term-wrt-nat x)
      (make-numeric-term-wrt-pos x)))

(define (is-numeric-term? x)
  (if NAT-NUMBERS
      (is-numeric-term-wrt-nat? x)
      (is-numeric-term-wrt-pos? x)))

(define (numeric-term-to-number x)
  (if NAT-NUMBERS
      (numeric-term-wrt-nat-to-number x)
      (numeric-term-wrt-pos-to-number x)))

;; Program constants.

(add-program-constant "NatPlus" (py "nat=>nat=>nat"))
(add-program-constant "NatTimes" (py "nat=>nat=>nat"))
(add-program-constant "NatLt" (py "nat=>nat=>boole"))
(add-program-constant "NatLe" (py "nat=>nat=>boole"))
(add-program-constant "Pred" (py "nat=>nat"))
(add-program-constant "NatMinus" (py "nat=>nat=>nat"))
(add-program-constant "NatMax" (py "nat=>nat=>nat"))
(add-program-constant "NatMin" (py "nat=>nat=>nat"))
(add-program-constant "AllBNat" (py "nat=>(nat=>boole)=>boole"))
(add-program-constant "ExBNat" (py "nat=>(nat=>boole)=>boole"))
(add-program-constant "NatLeast" (py "nat=>(nat=>boole)=>nat"))
(add-program-constant "NatLeastUp" (py "nat=>nat=>(nat=>boole)=>nat"))

;; Tokens used by the parser.

(define (add-nat-tokens)
  (let* ((make-type-string
	  (lambda (type op-string type-strings)
	    (let* ((string (type-to-string type))
		   (l (string->list string)))
	      (if (member string type-strings)
		  (list->string (cons (char-upcase (car l)) (cdr l)))
		  (myerror op-string "unexpected type" type)))))
	 (tc ;term-creator
	  (lambda (op-string . type-strings)
	    (lambda (x y)
	      (let* ((type (term-to-type x))
		     (type-string
		      (make-type-string type op-string type-strings))
		     (internal-name (string-append type-string op-string)))
		(mk-term-in-app-form
		 (make-term-in-const-form
		  (pconst-name-to-pconst internal-name))
		 x y))))))
    (add-token "+" 'add-op (tc "Plus" "nat"))
    (add-token "*" 'mul-op (tc "Times" "nat"))
    (add-token "<" 'rel-op (tc "Lt" "nat"))
    (add-token "<=" 'rel-op (tc "Le" "nat"))
    (add-token "--" 'add-op (tc "Minus" "nat"))
    (add-token "max" 'mul-op (tc "Max" "nat"))
    (add-token "min" 'mul-op (tc "Min" "nat"))))

(add-nat-tokens)

;; (add-nat-display) updates DISPLAY-FUNCTIONS, so that it uses the
;; tokens introduced by (add-nat-tokens).

(define (add-nat-display)
  (let ((dc ;display-creator
	 (lambda (name display-string token-type)
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
		   #f))))))
    (add-display (py "nat") (dc "NatPlus" "+" 'add-op))
    (add-display (py "nat") (dc "NatTimes" "*" 'mul-op))
    (add-display (py "boole") (dc "NatLt" "<" 'rel-op))
    (add-display (py "boole") (dc "NatLe" "<=" 'rel-op))
    (add-display (py "nat") (dc "NatMinus" "--" 'add-op))
    (add-display (py "nat") (dc "NatMax" "max" 'mul-op))
    (add-display (py "nat") (dc "NatMin" "min" 'mul-op))))

(add-nat-display)

;; (remove-nat-tokens) removes all tokens and from DISPLAY-FUNCTIONS
;; all items (nat proc).

(define (remove-nat-tokens)
  (remove-token "+")
  (remove-token "*")
  (remove-token "<")
  (remove-token "<=")
  (remove-token "--")
  (remove-token "max")
  (remove-token "min")
  (set! DISPLAY-FUNCTIONS
	(list-transform-positive DISPLAY-FUNCTIONS
	  (lambda (item)
	    (not (equal? (car item) (py "nat")))))))

;; NatEqToEqD
(set-goal "all n,m(n=m -> n eqd m)")
(ind)
(cases)
(assume "Useless")
(use "InitEqD")
(assume "n" "0=Sn")
(use "EfqEqD")
(use "0=Sn")
(assume "n" "IH")
(cases)
(assume "Sn=0")
(use "EfqEqD")
(use "Sn=0")
(assume "m" "Sn=Sm")
(assert "n eqd m")
 (use "IH")
 (use "Sn=Sm")
(assume "n=m")
(elim "n=m")
(strip)
(use "InitEqD")
;; Proof finished.
(save "NatEqToEqD")

;; BooleEqToEqD
(set-goal "all boole1,boole2(boole1=boole2 -> boole1 eqd boole2)")
(cases)
(cases)
(assume "Useless")
(use "InitEqD")
(assume "T=F")
(use "EfqEqD")
(use "T=F")
(cases)
(assume "F=T")
(use "EfqEqD")
(use "F=T")
(assume "Useless")
(use "InitEqD")
;; Proof finished.
(save "BooleEqToEqD")

;; Computation rules for the program constants.

;; For NatPlus
(add-computation-rules
 "n+0" "n"
 "n+Succ m" "Succ(n+m)")

;; For NatTimes
(add-computation-rules
 "n*0" "0"
 "n*Succ m" "(n*m)+n")

;; For NatLt
(add-computation-rules
 "n<0" "False"
 "0<Succ n" "True"
 "Succ n<Succ m" "n<m")

;; For NatLe
(add-computation-rules
 "0<=n" "True"
 "Succ n<=0" "False"
 "Succ n<=Succ m" "n<=m")

;; For Pred
(add-computation-rules
 "Pred 0" "0"
 "Pred(Succ n)" "n")

;; For NatMinus
(add-computation-rules
 "n--0" "n"
 "n--Succ m" "Pred(n--m)")

;; For NatMax
(add-computation-rules
 "n max 0" "n"
 "0 max Succ n" "Succ n"
 "Succ n max Succ m" "Succ(n max m)")

;; For NatMin
(add-computation-rules
 "n min 0" "0"
 "0 min Succ n" "0"
 "Succ n min Succ m" "Succ(n min m)")

;; For AllBNat
(add-computation-rules
 "AllBNat 0 nat=>boole" "True"
 "AllBNat(Succ n)nat=>boole"
 "[if (AllBNat n nat=>boole) ((nat=>boole)n) False]")

;; (add-computation-rules
;;  "AllBNat 0 nat=>boole" "True"
;;  "AllBNat(Succ n)nat=>boole" "AllBNat n nat=>boole andb (nat=>boole)n")

;; For ExBNat
(add-computation-rules
 "ExBNat 0 nat=>boole" "False"
 "ExBNat(Succ n)nat=>boole" "[if ((nat=>boole)n)
                                   True
                                   (ExBNat n nat=>boole)]")

;; For efficiency reasons if is preferred over orb (i.e., over the
;; term (ExBNat n nat=>boole orb (nat=>boole)n), since it computes
;; its arguments only when necessary.

;; For NatLeast
(add-computation-rules
 "NatLeast 0(nat=>boole)" "0"
 "NatLeast(Succ n)(nat=>boole)"
 "[if ((nat=>boole)0) 0 (Succ(NatLeast n([m](nat=>boole)(Succ m))))]")

;; For NatLeastUp
(add-computation-rules
 "NatLeastUp n0 n(nat=>boole)"
 "[if (n0<=n) (NatLeast(n--n0)([m](nat=>boole)(m+n0))+n0) 0]")

;; We prove and add some properties of the program constants introduced,
;; either as rewrite rules or as theorems.

;; Properties of NatPlus

(set-totality-goal "NatPlus")
(assume "n^" "Tn" "m^" "Tm")
(elim "Tm")
(ng #t)
(use "Tn")
(assume "l^" "Tl" "IH")
(ng #t)
(use "TotalNatSucc")
(use "IH")
;; Proof finished.
(save-totality)

;; (cdp (proof-to-soundness-proof))
;; (proof-to-expr-with-formulas (np (proof-to-soundness-proof)))

;; Alternative, with AllTotalElim
;; (set-totality-goal "NatPlus")
;; (use "AllTotalElim")
;; (assume "n")
;; (use "AllTotalElim")
;; (ind)
;; (use "NatTotalVar")
;; (assume "m" "IH")
;; (ng #t)
;; (use "TotalNatSucc")
;; (use "IH")
;; ;; Proof finished.
;; (save-totality)

(set-goal "all n 0+n=n")
(ind)
(use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
(add-rewrite-rule "0+n" "n")

(set-goal "all n,m Succ n+m=Succ(n+m)")
(assume "n")
(ind)
(use "Truth")
(assume "m" "IH")
(use "IH")
;; Proof finished.
(add-rewrite-rule "Succ n+m" "Succ(n+m)")

(set-goal "all n,m,l n+(m+l)=n+m+l")
(assume "n" "m")
(ind)
(use "Truth")
(assume "l" "IH")
(use "IH")
;; Proof finished.
(add-rewrite-rule "n+(m+l)" "n+m+l")

;; NatPlusComm
(set-goal "all n,m n+m=m+n")
(assume "n")
(ind)
(use "Truth")
(assume "m" "IH")
(use "IH")
;; Proof finished.
(save "NatPlusComm")

;; Properties of NatTimes

(set-totality-goal "NatTimes")
(assume "n^" "Tn" "m^" "Tm")
(elim "Tm")
(ng #t)
(use "TotalNatZero")
(assume "l^" "Tl" "IH")
(ng #t)
(use "NatPlusTotal")
(use "IH")
(use "Tn")
;; Proof finished
(save-totality)

;; (cdp (proof-to-soundness-proof))
;; (proof-to-expr-with-formulas (np (proof-to-soundness-proof)))

;; Alternative, with AllTotalElim
;; (set-totality-goal "NatTimes")
;; (use "AllTotalElim")
;; (assume "n")
;; (use "AllTotalElim")
;; (ind)
;; (use "NatTotalVar")
;; (assume "m" "IH")
;; (ng #t)
;; (use "NatPlusTotal")
;; (use "IH")
;; (use "NatTotalVar")
;; ;; Proof finished.
;; (save-totality)

(set-goal "all n 0*n=0")
(ind)
(use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
(add-rewrite-rule "0*n" "0")

;; NatCompat
(set-goal "all n,m(n=m -> all (nat=>boole)^((nat=>boole)^n -> (nat=>boole)^m))")
(ind)
  (cases)
    (assume "0=0" "(nat=>boole)^" "H1")
    (use "H1")
  (assume "nat" "Absurd" "(nat=>boole)^" "H1")
  (use "EfqAtom")
  (use "Absurd")
(assume "n" "IH")
(cases)
  (assume "Absurd" "(nat=>boole)^" "H1")
  (use "EfqAtom")
  (use "Absurd")
(assume "m" "n=m" "(nat=>boole)^")
(use-with "IH" (pt "m") "n=m" (pt "[nat](nat=>boole)^(Succ nat)"))
;; Proof finished.
(save "NatCompat")

;; NatEqCompat
(set-goal "all n,m(n=m -> all (nat=>nat)((nat=>nat) n=(nat=>nat) m))")
(ind)
  (cases)
    (assume "Useless" "(nat=>nat)")
    (use "Truth")
  (assume "m" "Absurd" "(nat=>nat)")
  (use "EfqAtom")
  (use "Absurd")
(assume "n" "IH")
(cases)
  (assume "Absurd" "(nat=>nat)")
  (use "EfqAtom")
  (use "Absurd")
(assume "m" "n=m" "(nat=>nat)")
(use-with "IH" (pt "m") "n=m" (pt "[nat](nat=>nat)(Succ nat)"))
;; Proof finished.
(save "NatEqCompat")

;; NatEqSym
(set-goal "all n,m(n=m -> m=n)")
(ind)
  (cases)
    (assume "H")
    (use "H")
  (assume "m" "Absurd")
  (use "Absurd")
(assume "n" "IH")
(cases)
  (assume "H")
  (use "H")
(use "IH")
;; Proof finished.
(save "NatEqSym")

;; NatEqTrans
(set-goal "all n,m,l(n=m -> m=l -> n=l)")
(ind)
  (cases)
    (assume "l" "Useless" "0=l")
    (use "0=l")
  (assume "m" "l" "Absurd" "H1")
  (use "EfqAtom")
  (use "Absurd")
(assume "n" "IH")
(cases)
  (assume "l" "Absurd" "H1")
  (use "EfqAtom")
  (use "Absurd")
(assume "m")
(cases)
  (assume "H1" "H2")
  (use "H2")
(use "IH")
;; Proof finished.
(save "NatEqTrans")

(set-goal "all n,m Succ n*m=(n*m)+m")
(assume "n")
(ind)
  (use "Truth")
(assume "m" "IH")
(ng)
(use "NatEqTrans" (pt "n*m+m+n"))
(use-with "NatEqCompat" (pt "Succ n*m") (pt "n*m+m")
	  "IH" (pt "[nat]nat+n"))
(use-with "NatEqCompat" (pt "m+n") (pt "n+m") "?"
	  (pt "[nat]n*m+nat"))
(use "NatPlusComm")
;; Proof finished.
(add-rewrite-rule "Succ n*m" "(n*m)+m")

;; NatTimesPlusDistr
(set-goal "all n,m,l n*(m+l)=(n*m)+(n*l)")
(assume "n" "m")
(ind)
(use "Truth")
(assume "l" "IH")
(ng #t)
(simp "IH")
(use "Truth")
;; Proof finished.
(save "NatTimesPlusDistr")
(add-rewrite-rule "n*(m+l)" "n*m+n*l")

;; NatTimesComm
(set-goal "all n,m n*m=m*n")
(assume "n")
(ind)
  (use "Truth")
(assume "m" "IH")
(ng)
(use "NatEqTrans" (pt "m*n+n"))
(use-with "NatEqCompat" (pt "n*m") (pt "m*n") "IH"
	  (pt "[nat]nat+n"))
(use "Truth")
;; Proof finished.
(save "NatTimesComm")

;; NatTimesPlusDistrLeft
(set-goal "all n,m,l (n+m)*l=(n*l)+(m*l)")
(assume "n" "m" "l")
(simp-with "NatTimesComm" (pt "n+m") (pt "l"))
(ng #t)
(simp-with "NatTimesComm" (pt "n") (pt "l"))
(simp-with "NatTimesComm" (pt "m") (pt "l"))
(use-with "Truth")
;; Proof finished.
(save "NatTimesPlusDistrLeft")
(add-rewrite-rule "(n+m)*l" "n*l+m*l")

(set-goal "all n,m,l n*(m*l)=(n*m)*l")
(ind)
  (strip)
  (use "Truth")
(assume "n" "IH1" "m" "l")
(ng)
(simp-with "IH1" (pt "m") (pt "l"))
(use "Truth")
;; Proof finished.
(add-rewrite-rule "n*(m*l)" "n*m*l")

;; Properties of NatLt

;; (add-totality "boole") ;moved to boole.scm
;; (pp "TotalBooleTrue")
;; (pp "TotalBooleFalse")

(set-totality-goal "NatLt")
(assume "n^" "Tn")
(elim "Tn")
(assume "m^" "Tm")
(elim "Tm")
(ng #t)
(use "TotalBooleFalse")
(assume "l^" "Tl" "Useless")
(ng #t)
(use "TotalBooleTrue")
(assume "m^" "Tm" "IH" "l^" "Tl")
(elim "Tl")
(ng #t)
(use "TotalBooleFalse")
(assume "l^0" "Tl0" "Useless")
(ng #t)
(use "IH")
(use "Tl0")
;; Proof finished.
(save-totality)

;; (cdp (proof-to-soundness-proof))
;; (proof-to-expr-with-formulas (np (proof-to-soundness-proof)))

;; ;; Alternative, with AllTotalElim
;; (set-totality-goal "NatLt")
;; (assert "allnc nat^(
;;   TotalNat nat^ -> allnc nat^0(TotalNat nat^0 -> TotalBoole(nat^0 <nat^)))")
;; (use "AllTotalElim")
;; (ind)
;; (assume "nat^2" "Useless")
;; (use "BooleTotalVar")
;; (assume "n" "IH")
;; (use "AllTotalElim")
;; (cases)
;; (use "BooleTotalVar")
;; (use "AllTotalIntro")
;; (use "IH")
;; ;; Assertion proved.
;; (assume "Assertion" "nat^1" "Tn" "nat^2" "Tm")
;; (use "Assertion")
;; (use "Tm")
;; (use "Tn")
;; ;; Proof finished.
;; (save-totality)

(set-goal "all n n<Succ n")
(ind)
  (use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
(add-rewrite-rule "n<Succ n" "True")

(set-goal "all n (n<n)=False")
(ind)
  (use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
(add-rewrite-rule "n<n" "False")

(set-goal "all n(Succ n<n)=False")
(ind)
  (use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
(add-rewrite-rule "Succ n<n" "False")

;; NatLtTrans
(set-goal "all n,m,l(n<m -> m<l -> n<l)")
(ind)
  (cases)
    (assume "l" "Absurd" "0<l")
    (use "0<l")
  (assume "m")
  (cases)
    (assume "Useless" "Absurd")
    (use "Absurd")
  (assume "l" "Useless" "H1")
  (use "Truth")
(assume "n" "IH1")
(cases)
  (assume "l" "Absurd" "0<l")
  (use "EfqAtom")
  (use "Absurd")
(assume "m")
(cases)
(assume "H1" "Absurd")
(use "Absurd")
(use "IH1")
;; Proof finished
(save "NatLtTrans")

;; NatNotLeToLt
(set-goal "all n,m((n<=m -> F) -> m<n)")
(ind)
(assume "m" "H1")
(use-with "H1" "Truth")
(assume "n" "IH")
(cases)
(assume "Useless")
(use "Truth")
(use "IH")
;; Proof finished.
(save "NatNotLeToLt")

;; NatNotLtToLe
(set-goal "all n,m((n<m -> F) -> m<=n)")
(ind)
(cases)
(assume "Useless")
(use "Truth")
(assume "m" "H1")
(use-with "H1" "Truth")
(assume "n" "IH")
(cases)
(assume "Useless")
(use "Truth")
(use "IH")
;; Proof finished.
(save "NatNotLtToLe")

;; NatLtToLe
(set-goal "all n,m(n<m -> n<=m)")
(ind)
(assume "m" "Useless")
(use "Truth")
(assume "nat" "IH")
(cases)
(assume "Absurd")
(use "Absurd")
(use "IH")
;; Proof finished.
(save "NatLtToLe")

;; NatLeAntiSym
(set-goal "all n,m(n<=m -> m<=n -> n=m)")
(ind)
(cases)
(assume "Useless1" "Useless2")
(use "Truth")
(assume "n" "Useless" "Absurd")
(use "EfqAtom")
(use "Absurd")
(assume "n" "IHn")
(cases)
(assume "Absurd" "Useless")
(use "EfqAtom")
(use "Absurd")
(assume "m")
(use "IHn")
;; Proof finished.
(save "NatLeAntiSym")

;; Properties of NatLe

(set-totality-goal "NatLe")
(assume "n^" "Tn")
(elim "Tn")
(assume "m^" "Tm")
(elim "Tm")
(ng #t)
(use "TotalBooleTrue")
(assume "l^" "Tl" "Useless")
(ng #t)
(use "TotalBooleTrue")
(assume "m^" "Tm" "IH" "l^" "Tl")
(elim "Tl")
(ng #t)
(use "TotalBooleFalse")
(assume "l^0" "Tl0" "Useless")
(ng #t)
(use "IH")
(use "Tl0")
;; Proof finished.
(save-totality)

;; (cdp (proof-to-soundness-proof))
;; (proof-to-expr-with-formulas (np (proof-to-soundness-proof)))

;; ;; Alternative, with AllTotalElim
;; (set-totality-goal "NatLe")
;; (use "AllTotalElim")
;; (ind)
;; (assume "nat^2" "Useless")
;; (use "BooleTotalVar")
;; (assume "n" "IH")
;; (use "AllTotalElim")
;; (cases)
;; (use "BooleTotalVar")
;; (use "AllTotalIntro")
;; (use "IH")
;; ;; Proof finished.
;; (save-totality)

;; NatLeToEq
(set-goal "all n (n<=0)=(n=0)")
(cases)
(use "Truth")
(assume "n")
(use "Truth")
;; Proof finished.
(save "NatLeToEq")
(add-rewrite-rule "n<=0" "n=0")

(set-goal "all n n<=n")
(ind)
  (use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
(add-rewrite-rule "n<=n" "True")

(set-goal "all n,m n<=n+m")
(ind)
  (assume "m")
  (use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
(add-rewrite-rule "n<=n+m" "True")

(set-goal "all n(Succ n<=n)=False")
(ind)
  (use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
(add-rewrite-rule "Succ n<=n" "False")

(set-goal "all n n<=Succ n")
(ind)
  (use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
(add-rewrite-rule "n<=Succ n" "True")

;; NatLeTrans
(set-goal "all n,m,l(n<=m -> m<=l -> n<=l)")
(ind)
  (strip)
  (use "Truth")
(assume "n" "IH")
(cases)
  (assume "l" "Absurd" "H1")
  (use "EfqAtom")
  (use "Absurd")
(assume "m")
(cases)
  (assume "H1" "Absurd")
  (use "Absurd")
(use "IH")
;; Proof finished.
(save "NatLeTrans")

;; NatLtLeTrans
(set-goal "all n,m,l(n<m -> m<=l -> n<l)")
(ind)
(cases)
  (assume "l" "Absurd" "H1")
  (use "EfqAtom")
  (use "Absurd")
(assume "m")
(cases)
  (assume "H1" "Absurd")
  (use "Absurd")
(strip)
(use "Truth")
(assume "n" "IH")
(cases)
  (assume "l" "Absurd" "H1")
  (use "EfqAtom")
  (use "Absurd")
(assume "m")
(cases)
  (assume "H1" "Absurd")
  (use "Absurd")
(use "IH")
;; Proof finished.
(save "NatLtLeTrans")

;; NatLeLtTrans
(set-goal "all n,m,l(n<=m -> m<l -> n<l)")
(ind)
(cases)
  (assume "l" "Useless" "0<l")
  (use "0<l")
(assume "m")
(cases)
  (prop)
(assume "l")
(prop)
(assume "n" "IH")
(cases)
  (assume "l" "Absurd" "H1")
  (use "EfqAtom")
  (use "Absurd")
(assume "m")
(cases)
  (assume "H1" "Absurd")
  (use "Absurd")
(use "IH")
;; Proof finished.
(save "NatLeLtTrans")

;; NatLtSuccToLe
(set-goal "all n,m(n<Succ m -> n<=m)")
(ind)
  (strip)
  (use "Truth")
(assume "n" "IH")
(cases)
  (assume "Absurd")
  (use "Absurd")
(use "IH")
;; Proof finished.
(save "NatLtSuccToLe")

;; NatLtLtSuccTrans
(set-goal "all n,m,l(n<m -> m<Succ l -> n<l)")
(assume "n" "m" "l" "n<m" "m<Succ l")
(use "NatLtLeTrans" (pt "m"))
(use "n<m")
(use "NatLtSuccToLe")
(use "m<Succ l")
;; Proof finished.
(save "NatLtLtSuccTrans")

;; NatLeToLtSucc
(set-goal "all n,m(n<=m -> n<Succ m)")
(ind)
  (strip)
  (use "Truth")
(assume "n" "IH")
(cases)
  (assume "Absurd")
  (use "Absurd")
(use "IH")
;; Proof finished.
(save "NatLeToLtSucc")

;; NatLtToSuccLe
(set-goal "all n,m(n<m -> Succ n<=m)")
(ind)
  (cases)
  (assume "Absurd")
  (use "EfqAtom")
  (use "Absurd")
  (assume "m" "Useless")
  (use "Truth")
(assume "n" "IH")
  (cases)
  (assume "Absurd")
  (use "EfqAtom")
  (use "Absurd")
(use "IH")
;; Proof finished.
(save "NatLtToSuccLe")

;; NatSuccLeToLt
(set-goal "all n,m(Succ n<=m -> n<m)")
(ind)
  (cases)
  (assume "Absurd")
  (use "EfqAtom")
  (use "Absurd")
  (assume "m" "Useless")
  (use "Truth")
(assume "n" "IH")
  (cases)
  (assume "Absurd")
  (use "EfqAtom")
  (use "Absurd")
(use "IH")
;; Proof finished.
(save "NatSuccLeToLt")

;; NatLtSuccCases
(set-goal "all n,m(n<Succ m -> (n<m -> Pvar) -> (n=m -> Pvar) -> Pvar)")
(assume "n" "m" "LtSuccHyp")
(cases (pt "n<m"))
;; Case n<m
(assume "n<m" "THyp" "FHyp")
(use-with "THyp" "Truth")
;; Case n<m -> F
(assume "n<m -> F" "THyp" "FHyp")
(use "FHyp")
(use "NatLeAntiSym")
(use "NatLtSuccToLe")
(use "LtSuccHyp")
(use "NatNotLtToLe")
(use "n<m -> F")
;; Proof finished.
(save "NatLtSuccCases")

;; (define eterm (proof-to-extracted-term))
;; (define neterm (rename-variables (nt eterm)))
;; (pp neterm)
;; [n,n0,alpha34,alpha34_0][if (n<n0) alpha34 alpha34_0]

(animate "NatLtSuccCases")

(define sproof (proof-to-soundness-proof))
;; (cdp sproof)
;; (pp (rename-variables (nf (proof-to-formula sproof))))

;; all n,m(
;;  n<Succ m -> 
;;  all alpha34^(
;;   (n<m -> (Pvar alpha34)^49 alpha34^) -> 
;;   all alpha34^0(
;;    (n=m -> (Pvar alpha34)^49 alpha34^0) -> 
;;    (Pvar alpha34)^49[if (n<m) alpha34^ alpha34^0])))

;; (define nsproof (np sproof))
;; (cdp nsproof)
;; (proof-to-expr-with-formulas nsproof)

(set-goal (rename-variables (nf (proof-to-formula sproof))))
(use-with sproof)
;; Proof finished.
(save "NatLtSuccCasesSound")

;; (pp "NatLtSuccCasesSound")

;; all n,m(
;;  n<Succ m -> 
;;  all alpha34^(
;;   (n<m -> (Pvar alpha34)^49 alpha34^) -> 
;;   all alpha34^0(
;;    (n=m -> (Pvar alpha34)^49 alpha34^0) -> 
;;    (Pvar alpha34)^49[if (n<m) alpha34^ alpha34^0])))

;; Remark.  (use sproof) does not work:
;; use2-closed-proof-intern
;; more terms expected, to be substituted for
;; n
;; m
;; alpha185^1340
;; alpha185^1341

;; NatLeCases
(set-goal "all n,m(n<=m -> (n<m -> Pvar) -> (n=m -> Pvar) -> Pvar)")
(assume "n" "m" "n<=m")
(cases (pt "n<m"))
;; Case n<m
(assume "n<m" "THyp" "FHyp")
(use-with "THyp" "Truth")
;; Case n<m -> F
(assume "n<m -> F" "THyp" "FHyp")
(use "FHyp")
(use "NatLeAntiSym")
(use "n<=m")
(use "NatNotLtToLe")
(use "n<m -> F")
;; Proof finished.
(save "NatLeCases")

;; (define eterm (proof-to-extracted-term))
;; (define neterm (rename-variables (nt eterm)))
;; (pp neterm)
;; [n,n0,alpha34,alpha34_0][if (n<n0) alpha34 alpha34_0]

(animate "NatLeCases")

;; (define sproof (proof-to-soundness-proof))
;; (cdp sproof)
;; (pp (rename-variables (proof-to-formula sproof)))
;; (pp (rename-variables (nf (proof-to-formula sproof))))

;; all n,m(
;;  n<=m -> 
;;  all alpha34^(
;;   (n<m -> (Pvar alpha34)^49 alpha34^) -> 
;;   all alpha34^0(
;;    (n=m -> (Pvar alpha34)^49 alpha34^0) -> 
;;    (Pvar alpha34)^49[if (n<m) alpha34^ alpha34^0])))

;; NatLeLtCases
(set-goal "all n,m((n<=m -> Pvar) -> (m<n -> Pvar) -> Pvar)")
(assume "n" "m")
(cases (pt "n<=m"))
;; Case n<=m
(assume "n<=m" "THyp" "FHyp")
(use-with "THyp" "Truth")
;; Case n<=m -> F
(assume "n<=m -> F" "THyp" "FHyp")
(use "FHyp")
(use "NatNotLeToLt")
(use "n<=m -> F")
;; Proof finished.
(save "NatLeLtCases")

;; (define eterm (proof-to-extracted-term))
;; (define neterm (rename-variables (nt eterm)))
;; (pp neterm)
;; [n,n0,alpha34,alpha34_0][if (n<=n0) alpha34 alpha34_0]

(animate "NatLeLtCases")

;; (define sproof (proof-to-soundness-proof))
;; (cdp sproof)
;; (pp (rename-variables (nf (proof-to-formula sproof))))

;; all n,m,alpha34^(
;;  (n<=m -> (Pvar alpha34)^49 alpha34^) -> 
;;  all alpha34^0(
;;   (m<n -> (Pvar alpha34)^49 alpha34^0) -> 
;;   (Pvar alpha34)^49[if (n<=m) alpha34^ alpha34^0]))

;; (define nsproof (np sproof))
;; (cdp nsproof)
;; (proof-to-expr-with-formulas nsproof)

;; NatLeLin
(set-goal "all n,m((n<=m -> Pvar) -> (m<=n -> Pvar) -> Pvar)")
(assume "n" "m")
(cases (pt "n<=m"))
;; Case n<=m
(assume "n<=m" "THyp" "FHyp")
(use-with "THyp" "Truth")
;; Case n<=m -> F
(assume "n<=m -> F" "THyp" "FHyp")
(use "FHyp")
(use "NatLtToLe")
(use "NatNotLeToLt")
(use "n<=m -> F")
;; Proof finished.
(save "NatLeLin")

;; (define eterm (proof-to-extracted-term))
;; (define neterm (rename-variables (nt eterm)))
;; (pp neterm)
;; [n,n0,alpha34,alpha34_0][if (n<=n0) alpha34 alpha34_0]

(animate "NatLeLin")

;; (define sproof (proof-to-soundness-proof))
;; (cdp sproof)
;; (pp (rename-variables (nf (proof-to-formula sproof))))

;; all n,m,alpha34^(
;;  (n<=m -> (Pvar alpha34)^49 alpha34^) -> 
;;  all alpha34^0(
;;   (m<=n -> (Pvar alpha34)^49 alpha34^0) -> 
;;   (Pvar alpha34)^49[if (n<=m) alpha34^ alpha34^0]))

;; (define nsproof (np sproof))
;; (cdp nsproof)
;; (proof-to-expr-with-formulas nsproof)

;; NatLtToLePred
(set-goal "all n,m(n<m -> n<=Pred m)")
(assume "n")
(cases)
(assume "Absurd")
(use "EfqAtom")
(use "Absurd")
(assume "m" "n<Succ m")
(use "NatLtSuccToLe")
(use "n<Succ m")
;; Proof finished.
(save "NatLtToLePred")

;; NatLePred
(set-goal "all n,m (Pred n<=m)=(n<=Succ m)")
(cases)
(strip)
(use "Truth")
(strip)
(use "Truth")
;; Proof finished.
(save "NatLePred")

;; NatLtMonPred
(set-goal "all n,m(0<n -> n<m -> Pred n<Pred m)")
(cases)
(assume "m" "Absurd" "Useless")
(use "EfqAtom")
(use "Absurd")
(assume "n")
(cases)
(assume "Useless" "Absurd")
(use "EfqAtom")
(use "Absurd")
(assume "m" "Useless" "n<m")
(use "n<m")
;; Proof finished.
(save "NatLtMonPred")

;; Properties of NatMinus and Pred

(set-totality-goal "Pred")
(assume "n^" "Tn")
(elim "Tn")
(ng #t)
(use "TotalNatZero")
(assume "m^" "Tm" "Useless")
(ng #t)
(use "Tm")
;; Proof finished.
(save-totality)

;; (cdp (proof-to-soundness-proof))
;; (proof-to-expr-with-formulas (np (proof-to-soundness-proof)))

;; ;; Alternative, with AllTotalElim
;; (set-totality-goal "Pred")
;; (use "AllTotalElim")
;; (cases)
;; (use "NatTotalVar")
;; (assume "nat")
;; (use "NatTotalVar")
;; ;; Proof finished.
;; (save-totality)

(set-totality-goal "NatMinus")
(assume "n^" "Tn" "m^" "Tm")
(elim "Tm")
(ng #t)
(use "Tn")
(assume "l^" "Tl" "IH")
(ng #t)
(use "PredTotal")
(use "IH")
;; Proof finished.
(save-totality)

;; (cdp (proof-to-soundness-proof))
;; (proof-to-expr-with-formulas (np (proof-to-soundness-proof)))

;; ;; Alternative, with AllTotalElim
;; (set-totality-goal "NatMinus")
;; (use "AllTotalElim")
;; (assume "n")
;; (use "AllTotalElim")
;; (ind)
;; (use "NatTotalVar")
;; (assume "m" "IH")
;; (ng #t)
;; (use "PredTotal")
;; (use "IH")
;; ;; Proof finished.
;; (save-totality)

(set-goal "all n,m Pred(Succ n--m)=n--m")
(assume "n")
(ind)
  (use "Truth")
(assume "m" "IH")
(ng)
(simp-with "IH")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "Pred(Succ n--m)" "n--m")

(set-goal "all n n--n=0")
(ind)
  (use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
(add-rewrite-rule "n--n" "0")

(set-goal "all n Succ n--n=1")
(ind)
  (use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
(add-rewrite-rule "Succ n--n" "1")

;; Properties of NatMax

(set-totality-goal "NatMax")
(assume "n^" "Tn")
(elim "Tn")
(assume "m^" "Tm")
(elim "Tm")
(ng #t)
(use "TotalNatZero")
(assume "l^" "Tl" "Useless")
(ng #t)
(use "TotalNatSucc")
(use "Tl")
(assume "m^" "Tm" "IH" "l^" "Tl")
(elim "Tl")
(ng #t)
(use "TotalNatSucc")
(use "Tm")
(assume "l^0" "Tl0" "Useless")
(ng #t)
(use "TotalNatSucc")
(use "IH")
(use "Tl0")
;; Proof finished.
(save-totality)

;; (cdp (proof-to-soundness-proof))
;; (proof-to-expr-with-formulas (np (proof-to-soundness-proof)))

;; ;; Alternative, with AllTotalElim
;; (set-totality-goal "NatMax")
;; (assert "allnc nat^(
;;   TotalNat nat^ -> allnc nat^0(TotalNat nat^0 -> TotalNat(nat^0 max nat^)))")
;; (use "AllTotalElim")
;; (ind)
;; (assume "nat^2" "Tm")
;; (use "Tm")
;; (assume "n" "IH")
;; (use "AllTotalElim")
;; (cases)
;; (use "NatTotalVar")
;; (use "AllTotalIntro")
;; (assume "nat^2" "Tm")
;; (ng #t)
;; (use "TotalNatSucc")
;; (use "IH")
;; (use "Tm")
;; ;; Assertion proved.
;; (assume "Assertion" "nat^1" "Tn" "nat^2" "Tm")
;; (use "Assertion")
;; (use "Tm")
;; (use "Tn")
;; ;; Proof finished.
;; (save-totality)

(set-goal "all n 0 max n=n")
(cases)
  (use "Truth")
(strip)
(use "Truth")
;; Proof finished.
(add-rewrite-rule "0 max n" "n")

(set-goal "all n n max n = n")
(ind)
  (use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
(add-rewrite-rule "n max n" "n")

(set-goal "all n,m,l(n max (m max l)=n max m max l)")
(ind)
  (strip)
  (use "Truth")
(assume "n" "IH")
(cases)
  (strip)
  (use "Truth")
(assume "m")
(cases)
  (use "Truth")
(use "IH")
;; Proof finished.
(add-rewrite-rule
 "n max (m max l)" "n max m max l")

;; NatMaxComm
(set-goal "all n,m n max m = m max n")
(ind)
  (strip)
  (use "Truth")
(assume "n" "IH")
(cases)
  (use "Truth")
(use "IH")
;; Proof finished.
(save "NatMaxComm")

;; NatMaxUB1
(set-goal "all n,m n<=n max m")
(ind)
  (assume "m")
  (use "Truth")
(assume "n" "IH")
(cases)
  (use "Truth")
(use "IH")
;; Proof finished.
(save "NatMaxUB1")

;; NatMaxUB2
(set-goal "all n,m m<=n max m")
(ind)
  (assume "m")
  (use "Truth")
(assume "n" "IH")
(cases)
  (use "Truth")
(use "IH")
;; Proof finished.
(save "NatMaxUB2")

;; NatMaxLUB
(set-goal "all n,m,l(n<=l -> m<=l -> n max m<=l)")
(ind)
(cases)
(strip)
(use "Truth")
(assume "m" "l" "Useless1" "Hyp")
(use "Hyp")
(assume "n" "IHn")
(cases)
(cases)
(assume "Absurd" "Useless")
(use "Absurd")
(assume "l" "Hyp" "Useless")
(use "Hyp")
(assume "m")
(cases)
(assume "Absurd" "Useless")
(use "Absurd")
(assume "l")
(ng #t)
(use "IHn")
;; Proof finished
(save "NatMaxLUB")

;; NatMaxEq1
(set-goal "all n,m(m<=n -> n max m=n)")
(assume "n" "m" "m<=n")
(use "NatLeAntiSym")
(use "NatMaxLUB")
(use "Truth")
(use "m<=n")
(use "NatMaxUB1")
;; Proof finished.
(save "NatMaxEq1")

;; NatMaxEq2
(set-goal "all n,m(n<=m -> n max m=m)")
(assume "n" "m" "n<=m")
(use "NatLeAntiSym")
(use "NatMaxLUB")
(use "n<=m")
(use "Truth")
(use "NatMaxUB2")
;; Proof finished.
(save "NatMaxEq2")

;; Properties of NatMin

(set-totality-goal "NatMin")
(assume "n^" "Tn")
(elim "Tn")
(assume "m^" "Tm")
(elim "Tm")
(ng #t)
(use "TotalNatZero")
(assume "l^" "Tl" "Useless")
(ng #t)
(use "TotalNatZero")
(assume "m^" "Tm" "IH" "l^" "Tl")
(elim "Tl")
(ng #t)
(use "TotalNatZero")
(assume "l^0" "Tl0" "Useless")
(ng #t)
(use "TotalNatSucc")
(use "IH")
(use "Tl0")
;; Proof finished.
(save-totality)

;; (cdp (proof-to-soundness-proof))
;; (proof-to-expr-with-formulas (np (proof-to-soundness-proof)))

;; ;; Alternative, with AllTotalElim
;; (set-totality-goal "NatMin")
;; (assert "allnc nat^(
;;   TotalNat nat^ -> allnc nat^0(TotalNat nat^0 -> TotalNat(nat^0 min nat^)))")
;; (use "AllTotalElim")
;; (ind)
;; (assume "m^" "Tm")
;; (use "NatTotalVar")
;; (assume "n" "IH")
;; (use "AllTotalElim")
;; (cases)
;; (use "NatTotalVar")
;; (use "AllTotalIntro")
;; (assume "m^" "Tm")
;; (ng #t)
;; (use "TotalNatSucc")
;; (use "IH")
;; (use "Tm")
;; ;; Assertion proved.
;; (assume "Assertion" "nat^1" "Tn" "m^" "Tm")
;; (use "Assertion")
;; (use "Tm")
;; (use "Tn")
;; ;; Proof finished.
;; (save-totality)nat
 
(set-goal "all n 0 min n=0")
(cases)
  (use "Truth")
(strip)
(use "Truth")
;; Proof finished.
(add-rewrite-rule "0 min n" "0")

(set-goal "all n n min n = n")
(ind)
  (use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
(add-rewrite-rule "n min n" "n")

(set-goal "all n,m,l(n min (m min l)=n min m min l)")
(ind)
  (strip)
  (use "Truth")
(assume "n" "IH")
(cases)
  (strip)
  (use "Truth")
(assume "m")
(cases)
  (use "Truth")
(use "IH")
;; Proof finished.
(add-rewrite-rule "n min (m min l)" "n min m min l")

;; NatMinComm
(set-goal "all n,m n min m = m min n")
(ind)
  (strip)
  (use "Truth")
(assume "n" "IH")
(cases)
  (use "Truth")
(use "IH")
;; Proof finished.
(save "NatMinComm")

;; NatMinLB1
(set-goal "all n,m n min m<=n")
(ind)
  (assume "m")
  (use "Truth")
(assume "n" "IH")
(cases)
  (use "Truth")
(use "IH")
;; Proof finished.
(save "NatMinLB1")

;; NatMinLB2
(set-goal "all n,m n min m<=m")
(ind)
  (assume "m")
  (use "Truth")
(assume "n" "IH")
(cases)
  (use "Truth")
(use "IH")
;; Proof finished.
(save "NatMinLB2")

;; NatMinGLB
(set-goal "all n,m,l(l<=n -> l<=m -> l<=n min m)")
(ind)
(assume "m" "l" "Hyp" "Useless")
(use "Hyp")
(assume "n" "IH")
(cases)
(assume "l" "Useless1" "Hyp")
(use "Hyp")
(assume "m")
(cases)
(strip)
(use "Truth")
(use "IH")
;; Proof finished
(save "NatMinGLB")

;; NatMinEq1
(set-goal "all n,m(n<=m -> n min m=n)")
(assume "n" "m" "n<=m")
(use "NatLeAntiSym")
(use "NatMinLB1")
(use "NatMinGLB")
(use "Truth")
(use "n<=m")
;; Proof finished.
(save "NatMinEq1")

;; NatMinEq2
(set-goal "all n,m(m<=n -> n min m=m)")
(assume "n" "m" "m<=n")
(use "NatLeAntiSym")
(use "NatMinLB2")
(use "NatMinGLB")
(use "m<=n")
(use "Truth")
;; Proof finished.
(save "NatMinEq2")

;; NatIfTotal
(set-goal "allnc n^(TotalNat n^ ->
 allnc alpha^,(nat=>alpha)^(Total alpha^ ->
 allnc m^(TotalNat m^ -> Total((nat=>alpha)^ m^)) ->
 Total[if n^ alpha^ (nat=>alpha)^]))")
(assume "n^" "Tn" "alpha^" "(nat=>alpha)^" "Talpha" "Tf")
(elim "Tn")
(use "Talpha")
(assume "m^" "Tm" "Useless")
(ng #t)
(use "Tf")
(use "Tm")
;; Proof finished.
(save "NatIfTotal")

;; (define sproof (proof-to-soundness-proof))
;; (cdp sproof)
;; (pp (rename-variables (nf (proof-to-formula sproof))))

;; all n^,n^0(
;;  TotalNatMR n^0 n^ -> 
;;  all alpha^,(nat=>alpha)^0,alpha^1(
;;   TotalMR alpha^1 alpha^ -> 
;;   all (nat=>alpha)^2(
;;    all m^,n^1(
;;     TotalNatMR n^1 m^ -> TotalMR((nat=>alpha)^2 n^1)((nat=>alpha)^0 m^)) -> 
;;    TotalMR[if n^0 alpha^1 (nat=>alpha)^2][if n^ alpha^ (nat=>alpha)^0])))

;; (define nsproof (np sproof))
;; (cdp nsproof)
;; (proof-to-expr-with-formulas nsproof)

;; NatEqTotal
(set-goal "allnc n^(
 TotalNat n^ -> allnc m^(TotalNat m^ -> TotalBoole(n^ =m^)))")
(assume "n^" "Tn")
(elim "Tn")
(assume "m^" "Tm")
(elim "Tm")
(use "TotalBooleTrue")
(assume "l^" "Useless1" "Useless2")
(use "TotalBooleFalse")
(assume "l^" "Tl" "IHl" "l^0" "Tl0")
(elim "Tl0")
(use "TotalBooleFalse")
(assume "l^1" "Tl1" "Useless")
(use "IHl")
(use "Tl1")
;; Proof finished.
(save "NatEqTotal")

;; (cdp (proof-to-soundness-proof))
;; (proof-to-expr-with-formulas (np (proof-to-soundness-proof)))

;; ;; Alternative, with AllTotalElim
;; (set-goal "allnc n^(
;;  TotalNat n^ -> allnc m^(TotalNat m^ -> TotalBoole(n^ =m^)))")
;; (use "AllTotalElim")
;; (ind)
;; ;; 3,4
;; (use "AllTotalElim")
;; (cases)
;; (use "BooleTotalVar")
;; (assume "m")
;; (use "BooleTotalVar")
;; ;; 4
;; (assume "n" "IH")
;; (use "AllTotalElim")
;; (cases)
;; (use "BooleTotalVar")
;; (assume "m")
;; (use "IH")
;; (use "NatTotalVar")
;; ;; Proof finished.
;; (save "NatEqTotal")

;; The following would fit better into a file lib/boole.scm

;; EqFalseToNeg
(set-goal "all boole(boole=False -> boole -> F)")
(cases)
(assume "Absurd" "Useless")
(use "Absurd")
(assume "Useless" "Absurd")
(use "Absurd")
;; Proof finished.
(save "EqFalseToNeg")

;; NegToEqFalse
(set-goal "all boole((boole -> F) -> boole=False)")
(cases)
(assume "Absurd")
(use-with "Absurd" "Truth")
(assume "Useless")
(use "Truth")
;; Proof finished.
(save "NegToEqFalse")

;; BooleAeqToEq
(set-goal "all boole1,boole2(
 (boole1 -> boole2) -> (boole2 -> boole1) -> boole1=boole2)")
(cases)
(cases)
(strip)
(use "Truth")
(assume "Absurd" "Useless")
(use-with "Absurd" "Truth")
(cases)
(assume "Useless" "Absurd")
(use-with "Absurd" "Truth")
(strip)
(use "Truth")
;; Proof finished.
(save "BooleAeqToEq")

;; BooleEqToAeqLeft
(set-goal "all boole1,boole2(boole1=boole2 -> boole1 -> boole2)")
(cases)
(cases)
(strip)
(use "Truth")
(assume "Absurd" "Useless")
(use "Absurd")
(cases)
(strip)
(use "Truth")
(assume "Useless" "Absurd")
(use "Absurd")
;; Proof finished.
(save "BooleEqToAeqLeft")

;; BooleEqToAeqRight
(set-goal "all boole1,boole2(boole1=boole2 -> boole2 -> boole1)")
(cases)
(strip)
(use "Truth")
(cases)
(assume "Absurd" "Useless")
(use "Absurd")
(assume "Useless" "Absurd")
(use "Absurd")
;; Proof finished.
(save "BooleEqToAeqRight")

;; OrIntroLeft
(set-goal "all boole1,boole2(boole1 -> boole1 orb boole2)")
(cases)
(strip)
(use "Truth")
(cases)
(strip)
(use "Truth")
(assume "Absurd")
(use "Absurd")
;; Proof finished.
(save "OrIntroLeft")

;; OrIntroRight
(set-goal "all boole1,boole2(boole2 -> boole1 orb boole2)")
(cases)
(strip)
(use "Truth")
(cases)
(strip)
(use "Truth")
(assume "Absurd")
(use "Absurd")
;; Proof finished.
(save "OrIntroRight")

;; OrElim
(set-goal "all boole1,boole2(
 boole1 orb boole2 -> (boole1 -> Pvar) -> (boole2 -> Pvar) -> Pvar)")
(cases)
(assume "boole1" "Useless1" "Hyp" "Useless2")
(use-with "Hyp" "Truth")
(cases)
(assume "Useless1" "Useless2" "Hyp")
(use-with "Hyp" "Truth")
(ng #t)
(assume "Absurd" "Hyp1" "Hyp2")
(use-with "Hyp1" "Absurd")
;; Proof finished.
(save "OrElim")

(define sproof (proof-to-soundness-proof))
;; (cdp sproof)
;; (proof-to-expr-with-formulas sproof)
;; (define nsproof (np sproof))
;; (proof-to-expr-with-formulas nsproof)

(set-goal (rename-variables (nf (proof-to-formula sproof))))
(use-with sproof)
;; Proof finished.
(save "OrElimSound")

;; IfAndb
(set-goal "all boole1,boole2 [if boole1 boole2 False]=(boole1 andb boole2)")
(cases)
(assume "boole1")
(use "Truth")
(assume "boole1")
(use "Truth")
;; Proof finished.
(save "IfAndb")

;; IfOrb
(set-goal "all boole1,boole2 [if boole1 True boole2]=(boole1 orb boole2)")
(cases)
(assume "boole1")
(use "Truth")
(assume "boole1")
(use "Truth")
;; Proof finished.
(save "IfOrb")

;; Properties of AllBNat

(set-totality-goal "AllBNat")
(assume "n^" "Tn")
(elim "Tn")
(assume "(nat=>boole)^" "Useless")
(ng #t)
(use "TotalBooleTrue")
(assume "m^" "Tm" "IH" "(nat=>boole)^" "Hyp")
(ng #t)
(use "BooleIfTotal")
(use "IH")
(use "Hyp")
(use "Hyp")
(use "Tm")
(use "TotalBooleFalse")
;; Proof finished.
(save-totality)

;; (define sproof (proof-to-soundness-proof))
;; (cdp sproof)
;; (pp (rename-variables (nf (proof-to-formula sproof))))

;; all n^,n^0(
;;  TotalNatMR n^0 n^ -> 
;;  all (nat=>boole)^,(nat=>boole)^0(
;;   all n^1,n^2(
;;    TotalNatMR n^2 n^1 -> TotalBooleMR((nat=>boole)^0 n^2)((nat=>boole)^ n^1)) -> 
;;   TotalBooleMR
;;   ((Rec nat=>(nat=>boole)=>boole)n^0([(nat=>boole)]True)
;;    ([n,((nat=>boole)=>boole),(nat=>boole)]
;;      [if (((nat=>boole)=>boole)(nat=>boole)) ((nat=>boole)n) False])
;;    (nat=>boole)^0)
;;   (AllBNat n^(nat=>boole)^)))

;; (define nsproof (np sproof))
;; (cdp nsproof)
;; (proof-to-expr-with-formulas nsproof)

;; Here is the reason why the rules for AllBNat were changed.
;; Problem: [if t r False] and (t andb r) are not considered equal if
;; t,r are not total.  Hence we change the computation rules for
;; AllBNat using [if (AllBNat nat nat=>boole) ((nat=>boole)nat) False]
;; instead of andb.  if arises via rec-to-if when normalizing Rec for
;; a boolean.  fan/fanwklu then needs to be adapted.

;; AllBNatIntro
(set-goal "all (nat=>boole),m(
      all n(n<m -> (nat=>boole)n) ->
      AllBNat m([n](nat=>boole)n))")
(assume "(nat=>boole)")
(ind)
  (strip)
  (use "Truth")
(assume "m" "IH" "H")
(ng)
(inst-with-to "H" (pt "m") "Truth" "HInst")
(simp "HInst")
(ng #t)
(use "IH")
(assume "n" "n1<n2")
(use "H")
(use "NatLtTrans" (pt "m"))
(use "n1<n2")
(use "Truth")
;; Proof finished.
(save "AllBNatIntro")

;; AllBNatElim
(set-goal "all (nat=>boole),m(
      AllBNat m(nat=>boole) ->
      all n(n<m -> (nat=>boole)n))")
(assume "(nat=>boole)")
(ind)
  (assume "H1" "n" "Absurd")
  (use "EfqAtom")
  (use "Absurd")
(assume "m" "IH")
(ng)
(assume "AllBHyp" "n" "n<Succ m")
(assert "AllBNat m(nat=>boole)andb(nat=>boole)m")
 (simp "<-" "IfAndb")
 (use "AllBHyp")
(assume "Conj")
(use "NatLtSuccCases" (pt "n") (pt "m"))
;; 14-16
(use "n<Succ m")
;; 16
(use "IH")
(use "Conj")
;; 16
(assume "n=m")
(simp "n=m")
(use "Conj")
;; Proof finished.
(save "AllBNatElim")

;; Properties of ExBNat

(set-totality-goal "ExBNat")
(assume "n^" "Tn")
(elim "Tn")
(assume "(nat=>boole)^" "Useless")
(ng #t)
(use "TotalBooleFalse")
(assume "m^" "Tm" "IH" "(nat=>boole)^" "Hyp")
(ng #t)
(use "BooleIfTotal")
(use "Hyp")
(use "Tm")
(use "TotalBooleTrue")
(use "IH")
(use "Hyp")
;; Proof finished.
(save-totality)

;; ExBNatIntro
(set-goal "all (nat=>boole),m,n(n<m -> (nat=>boole)n ->
      ExBNat m([n](nat=>boole)n))")
(assume "(nat=>boole)")
(ind)
;; 3,4
(ng)
(assume "n" "Absurd" "Useless")
(use "Absurd")
;; 4
(assume "m" "IH" "n" "n<Sm")
(use "NatLtSuccCases" (pt "n") (pt "m"))
(use "n<Sm")
(assume "n<m" "fn1")
(ng #t)
(cases (pt "(nat=>boole)m"))
(strip)
(use "Truth")
(assume "Useless")
(ng #t)
(use "IH" (pt "n"))
(use "n<m")
(use "fn1")
;; 10
(assume "n=m")
(simp "n=m")
(assume "fn2")
(simp "fn2")
(use "Truth")
;; Proof finished.
(save "ExBNatIntro")

;; ExBNatElim
(set-goal "all (nat=>boole),m(
      ExBNat m(nat=>boole) ->
      exu n(n<m andu (nat=>boole)n))")
(assume "(nat=>boole)")
(ind)
(ng)
;; (use "Efq")
;; use2-closed-proof-intern
;; unusable formula
;; F -> all boole^325 boole^325
;; for goal formula
;; F -> exu n(F andu (nat=>boole)n)
(assume "Absurd")
(intro 0 (pt "0"))
(split)
(use "Absurd")
(use "EfqAtom")
(use "Absurd")
(assume "m" "IH")
(ng)
(cases (pt "(nat=>boole)m"))
(assume "(nat=>boole)m" "Useless")
(intro 0 (pt "m"))
(split)
(use "Truth")
(use "(nat=>boole)m")
(ng)
(assume "Useless" "ExBNatHyp")
(inst-with-to "IH" "ExBNatHyp" "IHInst")
(drop "IH")
(by-assume "IHInst" "n" "nProp")
(intro 0 (pt "n"))
(split)
(use "NatLtTrans" (pt "m"))
(use "nProp")
(use "Truth")
(use "nProp")
;; Proof finished.
(save "ExBNatElim")

;; AllBNatExBNat
(set-goal "all nat=>boole,n(
 negb(ExBNat n([m](nat=>boole)m))=
 AllBNat n([m]negb((nat=>boole)m)))")
(assume "nat=>boole")
(ind)
(ng)
(use "Truth")
(assume "n" "IH")
(ng)
(simp "<-" "IH")
(cases (pt "(nat=>boole)n"))
(ng)
(strip)
(use "Truth")
(ng)
(strip)
(use "Truth")
;; Proof finished.
(save "AllBNatExBNat")

(set-totality-goal "NatLeast")
(assume "n^" "Tn")
(elim "Tn")
(ng #t)
(strip)
(use "TotalNatZero")
(assume "m^" "Tm" "IH" "nat=>boole^" "Tg")
(ng #t)
(use "BooleIfTotal")
(use "Tg")
(use "TotalNatZero")
(use "TotalNatZero")
(use "TotalNatSucc")
(use "IH")
(ng #t)
(assume "l^" "Tl")
(use "Tg")
(use "TotalNatSucc")
(use "Tl")
;; Proof finished.
(save-totality)

;; NatLeastBound
(set-goal "all n,(nat=>boole) NatLeast n(nat=>boole)<=n")
(ind)
(ng #t)
(strip)
(use "Truth")
(assume "n" "IH" "(nat=>boole)")
(ng #t)
(cases (pt "(nat=>boole)0"))
(assume "(nat=>boole)0")
(ng #t)
(use "Truth")
(assume "(nat=>boole)0 -> F")
(ng #t)
(use "IH")
;; Proof finished.
(save "NatLeastBound")

;; NatLeastLeIntro
(set-goal "all n,m,(nat=>boole)((nat=>boole)m -> (NatLeast n nat=>boole)<=m)")
(ind)
(strip)
(use "Truth")
(assume "n" "IH")
(cases)
(assume "(nat=>boole)" "g0")
(ng #t)
(simp "g0")
(use "Truth")
(assume "m" "(nat=>boole)" "g(Sn)")
(ng #t)
(cases 'auto)
(strip)
(use "Truth")
(strip)
(ng #t)
(use-with "IH" (pt "m") (pt "[nat]((nat=>boole)(Succ nat))") "?")
(ng #t)
(use "g(Sn)")
;; Proof finished.
(save "NatLeastLeIntro")

;; NatLeastLtElim
(set-goal "all n,(nat=>boole)(
 NatLeast n(nat=>boole)<n -> (nat=>boole)(NatLeast n(nat=>boole)))")
(ind)
(assume "(nat=>boole)")
(ng #t)
(use "Efq")
(assume "n" "IH" "(nat=>boole)")
(ng #t)
(cases (pt "(nat=>boole)0"))
(assume "g0" "Useless")
(use "g0")
(assume "(nat=>boole)0 -> F")
(ng #t)
(use "IH")
;; Proof finished.
(save "NatLeastLtElim")

(set-totality-goal "NatLeastUp")
(assume "n^0" "Tn0" "n^" "Tn" "nat=>boole^" "Tg")
(ng #t)
(use "BooleIfTotal")
(use "NatLeTotal")
(use "Tn0")
(use "Tn")
(use "NatPlusTotal")
(use "NatLeastTotal")
(use "NatMinusTotal")
(use "Tn")
(use "Tn0")
(assume "n^1" "Tn1")
(ng #t)
(use "Tg")
(use "NatPlusTotal")
(use "Tn1")
(use "Tn0")
(use "Tn0")
(use "TotalNatZero")
;; Proof finished.
(save-totality)

;; We postpone proofs of the NatLeastUpBound NatLeastUpLBound
;; NatLeastUpLeIntro NatLeastUpLtElim NatLeastUpZero since they use
;; monotonicity properties of NatLt which are only proved later.

;; We add some further rewrite rules and theorems.  The order is
;; somewhat delicate, since the proofs can depend on which rewrite
;; rules are present, and also which program constants have been proved
;; to be total.

(set-goal "all n,m n<=m+n")
(ind)
  (assume "n")
  (use "Truth")
(assume "n" "IH")
(use "IH")
;; Proof finished.
(add-rewrite-rule "n<=m+n" "True")

(set-goal "all n,m (n+m<n)=False")
(assert "all l,l0(l+l0<l -> F)")
 (ind)
 (assume "l" "Absurd")
 (use "Absurd")
 (assume "l" "IH")
 (cases)
 (assume "Absurd")
 (use "Absurd")
 (assume "l0")
 (ng #t)
 (assume "Succ(l+l0)<l")
 (use "IH" (pt "l0"))
 (use "NatLtTrans" (pt "Succ(l+l0)"))
 (use "Truth")
 (use "Succ(l+l0)<l")
(assume "Prop" "n" "m")
(use "AtomFalse")
(use "Prop")
;; Proof finished.
(add-rewrite-rule "n+m<n" "False")

(set-goal "all n Pred n<=n")
(cases)
(use "Truth")
(assume "n")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "Pred n<=n" "True")

(set-goal "all n 0--n=0")
(ind)
  (use "Truth")
(assume "n" "IH")
(ng #t)
(simp "IH")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "0--n" "0")

(set-goal "all n,m n--m<=n")
(assume "n")
(ind)
  (use "Truth")
(assume "m" "IH")
(ng #t)
(use "NatLeTrans" (pt "n--m"))
(use "Truth")
(use "IH")
;; Proof finished.
(add-rewrite-rule "n--m<=n" "True")

(set-goal "all n,m n+m--m=n")
(assume "n")
(ind)
  (use "Truth")
(assume "m" "IH")
(ng #t)
(use "IH")
;; Proof finished.
(add-rewrite-rule "n+m--m" "n")

(set-goal "all n,m m+n--m=n")
(assume "n")
(ind)
  (use "Truth")
(assume "m" "IH")
(ng #t)
(use "IH")
;; Proof finished.
(add-rewrite-rule "m+n--m" "n")

(set-goal "all n,m n*Pred m=n*m--n")
(assume "n")
(ind)
  (use "Truth")
(assume "m" "IH")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "n*Pred m" "n*m--n")

(set-goal "all n,m Pred m*n=m*n--n")
(assume "n")
(ind)
  (use "Truth")
(assume "m" "IH")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "Pred m*n" "m*n--n")

(set-goal "all n,m,l n--m--l=n--(m+l)")
(assume "n" "m")
(ind)
  (use "Truth")
(assume "l" "IH")
(ng #t)
(simp "IH")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "n--m--l" "n--(m+l)")

(set-goal "all n,m,l n*(m--l)=n*m--n*l")
(assume "n" "m")
(ind)
  (use "Truth")
(assume "l" "IH")
(ng #t)
(simp "IH")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "n*(m--l)" "n*m--n*l")

(set-goal "all n,m,l (m--l)*n=m*n--l*n")
(assume "n" "m")
(ind)
  (use "Truth")
(assume "l" "IH")
(ng #t)
(simp "IH")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "(m--l)*n" "m*n--l*n")

;; SuccNatMinus
(set-goal "all m,n(m<n -> Succ(n--m)=Succ(n)--m)")
(ind)
(ng)
(strip)
(use "Truth")
(assume "m" "IH")
(cases)
(ng)
(assume "Absurd")
(use "Absurd")
(assume "n")
(use "IH")
;; Proof finished.
(save "SuccNatMinus")

;; NatLeMonPlus
(set-goal "all n,m,l,l0(n<=m -> l<=l0 -> n+l<=m+l0)")
(assume "n" "m")
(ind)
(ind)
(assume "n<=m" "Useless")
(use "n<=m")
(assume "l0" "IHl0")
(assume "n<=m" "Useless")
(use "NatLeTrans" (pt "m+l0"))
(use "IHl0")
(use "n<=m")
(use "Truth")
(use "Truth")
(assume "l" "IHl")
(cases)
(assume "Useless" "Absurd")
(use "Efq")
(use "Absurd")
(use "IHl")
;; Proof finished.
(save "NatLeMonPlus")

;; NatLeMonTimes
(set-goal "all n,m,l,l0(n<=m -> l<=l0 -> n*l<=m*l0)")
(assume "n" "m")
(ind)
(ind)
(assume "Useless1" "Useless2")
(use "Truth")
(assume "l0" "IHl0")
(assume "Useless1" "Useless2")
(use "Truth")
(assume "l" "IHl")
(cases)
(assume "Useless" "Absurd")
(use "Efq")
(use "Absurd")
(assume "l0" "n<=m" "l<=l0")
(ng)
(use "NatLeMonPlus")
(use "IHl")
(use "n<=m")
(use "l<=l0")
(use "n<=m")
;; Proof finished.
(save "NatLeMonTimes")

;; NatLeMonPred
(set-goal "all n,m(n<=m -> Pred n<=Pred m)")
(cases)
(assume "m" "Useless")
(use "Truth")
(assume "n")
(cases)
(assume "Absurd")
(use "Efq")
(use "Absurd")
(assume "m" "n<=m")
(use "n<=m")
;; Proof finished.
(save "NatLeMonPred")

;; NatLeMonMinus
(set-goal "all n,m,l,l0(n<=m -> l<=l0 -> n--l0<=m--l)")
(assume "n" "m" "l" "l0" "n<=m" "l<=l0")
(use "NatLeTrans" (pt "m--l0"))
;; ?_3: n--l0<=m--l0
(ind (pt "l0"))
(use "n<=m")
(assume "nat" "IH")
(ng #t)
(use "NatLeMonPred")
(use "IH")
;; ?_4: m--l0<=m--l
(assert "all nat5,nat6,nat7(nat5<=nat6 -> nat7--nat6<=nat7--nat5)")
 (ind)
 (assume "nat5" "nat6" "Useless")
 (use "Truth")
 (assume "nat5" "IH5")
 (cases)
 (assume "nat6" "Absurd")
 (use "Efq")
 (use "Absurd")
 (assume "nat6")
 (cases)
 (assume "Useless")
 (use "Truth")
 (assume "nat7")
 (ng)
 (use "IH5")
(assume "NatLeMonMinusRight")
(use "NatLeMonMinusRight")
(use "l<=l0")
;; Proof finished.
(save "NatLeMonMinus")

;; NatPlusMinus
(set-goal "all n,m,l(l<=m -> n+(m--l)=n+m--l)")
(assume "n" "m")
(ind)
(assume "Useless")
(use "Truth")
(assume "l" "IH" "l+1<=m")
(ng #t)
(assert "all l0,l1(0<l1 -> l0+Pred l1=Pred(l0+l1))")
 (assume "l0")
 (cases)
 (assume "Absurd")
 (use "Efq")
 (use "Absurd")
 (assume "l1" "Useless")
 (use "Truth")
(assume "NatPlusPred")
(simp "<-" "IH")
(use "NatPlusPred")
(drop "IH" "NatPlusPred")
(use "NatLtLeTrans" (pt "Succ l--l"))
(use "Truth")
(use "NatLeMonMinus")
(use "l+1<=m")
(use "Truth")
(use "NatLeTrans" (pt "Succ l"))
(use "Truth")
(use "l+1<=m")
;; Proof finished.
(save "NatPlusMinus")

;; NatMinusPlus
(set-goal "all n,m,l(l<=n -> n--l+m=n+m--l)")
(assume "n" "m")
(ind)
(assume "Useless")
(use "Truth")
(assume "l" "IH" "l+1<=n")
(ng #t)
(assert "all l1,l0(0<l0 -> Pred l0+l1=Pred(l0+l1))")
 (assume "l1")
 (cases)
 (assume "Absurd")
 (use "Efq")
 (use "Absurd")
 (assume "l0" "Useless")
 (use "Truth")
(assume "NatPlusPred")
(simp "<-" "IH")
(use "NatPlusPred")
(drop "IH" "NatPlusPred")
(use "NatLtLeTrans" (pt "Succ l--l"))
(use "Truth")
(use "NatLeMonMinus")
(use "l+1<=n")
(use "Truth")
(use "NatLeTrans" (pt "Succ l"))
(use "Truth")
(use "l+1<=n")
;; Proof finished.
(save "NatMinusPlus")

;; NatMinusPlusEq
(set-goal "all n,m(m<=n -> n--m+m=n)")
(assume "n" "m" "m<=n")
(simp "NatMinusPlus")
(use "Truth")
(use "m<=n")
;; Proof finished.
(save "NatMinusPlusEq")

;; NatMinusMinus
(set-goal  "all n,m,l(l<=m -> m<=n+l -> n--(m--l)=n+l--m)")
(assume "n")
(ind)
(cases)
(assume "Useless1" "Useless2")
(use "Truth")
(assume "m" "Absurd" "Useless")
(use "Efq")
(use "Absurd")
(assume "m" "IHm")
(cases)
(assume "Useless1" "Useless2")
(use "Truth")
(assume "l" "l<=m" "m<=n+l")
(ng)
(use "IHm")
(use "l<=m")
(use "m<=n+l")
;; Proof finished.
(save "NatMinusMinus")

;; NatLtMonPlus1
(set-goal "all n,m,l,l0(n<m -> l<=l0 -> n+l<m+l0)")
(ind)
(cases)
(assume "l" "l0")
(ng #t)
(use "Efq")
(assume "m" "l" "l0" "Useless" "l<=l0")
(ng #t)
(use "NatLeToLtSucc")
(use "NatLeTrans" (pt "l0"))
(use "l<=l0")
(ng #t)
(use "Truth")
(assume "n" "IH")
(ng #t)
(cases)
(assume "l" "l0")
(ng #t)
(use "Efq")
(ng #t)
(use "IH")
;; Proof finished.
(save "NatLtMonPlus1")

;; NatLtMonPlus2
(set-goal "all n,m,l,l0(n<=m -> l<l0 -> n+l<m+l0)")
(assume "n" "m")
(ind)
(cases)
(ng #t)
(assume "Useless")
(use "Efq")
(assume "l" "n<=m" "Useless")
(ng #t)
(use "NatLeToLtSucc")
(use "NatLeTrans" (pt "m"))
(use "n<=m")
(ng #t)
(use "Truth")
(assume "l" "IH")
(ng #t)
(cases)
(assume "n<=m")
(ng #t)
(use "Efq")
(ng #t)
(use "IH")
;; Proof finished.
(save "NatLtMonPlus2")

;; NatLtMonMinusLeft
(set-goal "all n,m,l(m<l -> n<=m -> m--n<l--n)")
(ind)
(ng #t)
(assume "m" "l" "m<l" "Useless")
(use "m<l")
(assume "n" "IH")
(cases)
(ng #t)
(assume "l" "Useless")
(use "Efq")
(assume "m")
(cases)
(ng #t)
(assume "Absurd" "Useless")
(use "Absurd")
(assume "l")
(ng #t)
(use "IH")
;; Proof finished.
(save "NatLtMonMinusLeft")

;; NatLtMonMinus
(set-goal "all n,m,l,l0(n<m -> l<=l0 -> l0<n -> n--l0<m--l)")
(assume "n" "m" "l" "l0" "n<m" "l<=l0" "l0<n")
(use "NatLtLeTrans" (pt "m--l0"))
;; n--l0<m--l0
(use "NatLtMonMinusLeft")
(use "n<m")
(use "NatLtToLe")
(use "l0<n")
;; m--l0<=m--l
(assert "all nat5,nat6,nat7(nat5<=nat6 -> nat7--nat6<=nat7--nat5)")
 (ind)
 (assume "nat5" "nat6" "Useless")
 (use "Truth")
 (assume "nat5" "IH5")
 (cases)
 (assume "nat6" "Absurd")
 (use "Efq")
 (use "Absurd")
 (assume "nat6")
 (cases)
 (assume "Useless")
 (use "Truth")
 (assume "nat7")
 (ng)
 (use "IH5")
(assume "NatLeMonMinusRight")
(use "NatLeMonMinusRight")
(use "l<=l0")
;; Proof finished.
(save "NatLtMonMinus")

;;  NatLeastUpBound
(set-goal "all n0,n,(nat=>boole) NatLeastUp n0 n(nat=>boole)<=n")
(assume "n0" "n" "(nat=>boole)")
(ng #t)
(cases (pt "n0<=n"))
(assume "n0<=n")
(ng #t)
(use "NatLeTrans" (pt "n--n0+n0"))
(use "NatLeMonPlus")
(use "NatLeastBound")
(use "Truth")
(simp "NatMinusPlusEq")
(use "Truth")
(use "n0<=n")
(strip)
(use "Truth")
;; Proof finished.
(save "NatLeastUpBound")

;; NatLeastUpLBound
(set-goal "all n0,n,(nat=>boole)(n0<=n -> n0<=NatLeastUp n0 n(nat=>boole))")
(assume "n0" "n" "(nat=>boole)" "n0<=n")
(ng #t)
(simp "n0<=n")
(ng #t)
(use "Truth")
;; Proof finished.
(save "NatLeastUpLBound")

;; NatLeastUpLeIntro
(set-goal "all n0,n,m,(nat=>boole)(
 n0<=m -> (nat=>boole)m -> NatLeastUp n0 n(nat=>boole)<=m)")
(assume "n0" "n" "m" "(nat=>boole)" "n0<=m" "(nat=>boole)m")
(ng #t)
(cases (pt "n0<=n"))
(assume "n0<=n")
(ng #t)
(assert "NatLeast(n--n0)([nat](nat=>boole)(nat+n0))<=m--n0")
 (use "NatLeastLeIntro")
 (ng #t)
 (simp "NatMinusPlusEq")
 (use "(nat=>boole)m")
 (use "n0<=m")
(assume "Assertion")
(assert
 "NatLeast(n--n0)([nat](nat=>boole)(nat+n0))+n0<=m--n0+n0")
 (use "NatLeMonPlus")
 (use "Assertion")
 (use "Truth")
 (simp "NatMinusPlusEq")
(assume "Hyp")
(use "Hyp")
(use "n0<=m")
(strip)
(use "Truth")
;; Proof finished.
(save "NatLeastUpLeIntro")

;; NatLeastUpLtElim
(set-goal "all n0,n,(nat=>boole)(
 n0<=NatLeastUp n0 n(nat=>boole) ->
 NatLeastUp n0 n(nat=>boole)<n ->
 (nat=>boole)(NatLeastUp n0 n(nat=>boole)))")
(assume "n0" "n" "(nat=>boole)" "n0<=m" "m<n")
(ng #t)
(assert "n0<=n")
 (use "NatLeTrans" (pt "NatLeastUp n0 n(nat=>boole)"))
 (use "n0<=m")
 (use "NatLtToLe")
 (use "m<n")
(assume "n0<=n")
(simp "n0<=n")
(ng #t)
(use-with "NatLeastLtElim"
	  (pt "n--n0")
	  (pt "[nat]((nat=>boole)(nat+n0))") "?")
(ng "m<n")
(simphyp-with-to "m<n" "n0<=n" "SimpHyp")
(ng "SimpHyp")
(assert
 "NatLeast(n--n0)([nat](nat=>boole)(nat+n0))+n0--n0<n--n0")
 (use "NatLtMonMinusLeft")
 (use "SimpHyp")
 (ng #t)
 (use "Truth")
(ng #t)
(assume "Hyp")
(use "Hyp")
;; Proof finished.
(save "NatLeastUpLtElim")

;; NatLeastUpZero
(set-goal "all n,(nat=>boole)
 NatLeastUp Zero n(nat=>boole)=NatLeast n(nat=>boole)")
(assume "n" "nat=>boole")
(use "Truth")
;; Proof finished.
(save "NatLeastUpZero")
(add-rewrite-rule "NatLeastUp Zero n(nat=>boole)" "NatLeast n(nat=>boole)")

;; NatRecTotal
(set-goal (rename-variables (term-to-totality-formula (pt "(Rec nat=>alpha)"))))
(assume "n^" "Tn")
(elim "Tn")
(ng #t)
(assume "alpha^" "Talpha")
(strip)
(use "Talpha")
(assume "m^" "Tm" "IH" "alpha^" "Talpha" "(nat=>alpha=>alpha)^" "Tf")
(ng #t)
(use "Tf")
(use "Tm")
(use "IH")
(use "Talpha")
(use "Tf")
;; Proof finished.
(save "NatRecTotal")

;; (define sproof (proof-to-soundness-proof))
;; (cdp sproof)
;; (pp (rename-variables (nf (proof-to-formula sproof))))

;; all n^,n^0(
;;  TotalNatMR n^0 n^ -> 
;;  all alpha^,alpha^0(
;;   TotalMR alpha^0 alpha^ -> 
;;   all (nat=>alpha=>alpha)^1,(nat=>alpha=>alpha)^2(
;;    all n^1,n^2(
;;     TotalNatMR n^2 n^1 -> 
;;     all alpha^3,alpha^4(
;;      TotalMR alpha^4 alpha^3 -> 
;;      TotalMR((nat=>alpha=>alpha)^2 n^2 alpha^4)
;;      ((nat=>alpha=>alpha)^1 n^1 alpha^3))) -> 
;;    TotalMR
;;    ((Rec nat=>alpha=>(nat=>alpha=>alpha)=>alpha)n^0
;;     ([alpha,(nat=>alpha=>alpha)]alpha)
;;     ([n,(alpha=>(nat=>alpha=>alpha)=>alpha),alpha,(nat=>alpha=>alpha)]
;;       (nat=>alpha=>alpha)n
;;       ((alpha=>(nat=>alpha=>alpha)=>alpha)alpha(nat=>alpha=>alpha)))
;;     alpha^0
;;     (nat=>alpha=>alpha)^2)
;;    ((Rec nat=>alpha)n^ alpha^(nat=>alpha=>alpha)^1))))

;; (define nsproof (np sproof))
;; (cdp nsproof)
;; (proof-to-expr-with-formulas nsproof)

;; NatDouble
(add-program-constant "NatDouble" (py "nat=>nat"))

(add-computation-rules
 "NatDouble Zero" "Zero"
 "NatDouble(Succ n)" "Succ(Succ(NatDouble n))")

(set-totality-goal "NatDouble")
(assume "n^" "Tn")
(elim "Tn")
(use "TotalNatZero")
(assume "m^" "Tm" "IH")
(ng #t)
(use "TotalNatSucc")
(use "TotalNatSucc")
(use "IH")
;; Proof finished.
(save-totality)

;; NatMaxDouble
(set-goal "all n,m NatDouble n max NatDouble m=NatDouble(n max m)")
(ind)
(assume "m")
(ng)
(use "Truth")
(assume "n" "IH")
(cases)
(ng)
(use "Truth")
(ng)
(use "IH")
;; Proof finished.
(save "NatMaxDouble")

;; NatMinDouble
(set-goal "all n,m NatDouble n min NatDouble m=NatDouble(n min m)")
(ind)
(assume "m")
(ng)
(use "Truth")
(assume "n" "IH")
(cases)
(ng)
(use "Truth")
(ng)
(use "IH")
;; Proof finished.
(save "NatMinDouble")

(add-program-constant "NatEven" (py "nat=>boole"))

(add-computation-rules
 "NatEven Zero" "True"
 "NatEven(Succ Zero)" "False"
 "NatEven(Succ(Succ n))" "NatEven n")

(set-totality-goal "NatEven")
(assert "allnc n^(TotalNat n^ ->
         TotalBoole(NatEven(Succ n^)) &
         TotalBoole(NatEven(Succ(Succ n^))))")
 (assume "n^" "Tn")
 (elim "Tn")
 (ng #t)
 (split)
 (use "TotalBooleFalse")
 (use "TotalBooleTrue")
 (assume "m^" "Tm" "IH")
 (ng)
 (split)
 (use "IH")
 (use "IH")
(assume "NatEvenTotalAux")
(ng)
(assume "n^" "Tn")
(use "NatEvenTotalAux")
(use "Tn")
;; Proof finished.
(save-totality)

;; NatEvenDouble
(set-goal "all n NatEven(NatDouble n)")
(ind)
(ng #t)
(use "Truth")
(assume "n" "IH")
(ng #t)
(use "IH")
;; Proof finished.
(save "NatEvenDouble")

;; NatEvenSucc
(set-goal "all n(NatEven n -> NatEven(Succ n) -> F)")
(ind)
(ng #t)
(assume "Useless" "Absurd")
(use "Absurd")
(assume "n" "IH" "ESn" "ESSn")
(ng "ESSn")
(use "IH")
(use "ESSn")
(use "ESn")
;; Proof finished.
(save "NatEvenSucc")

;; NatOddSuccToEven
(set-goal "all n((NatEven(Succ n) -> F) ->NatEven n)")
(ind)
(ng #t)
(strip)
(use "Truth")
(assume "n" "IH" "OSSn")
(cases (pt "NatEven(Succ n)"))
(strip)
(use "Truth")
(assume "OSn")
(use "OSSn")
(ng #t)
(use "IH")
(use "OSn")
;; Proof finished
(save "NatOddSuccToEven")

(add-program-constant "NatHalf" (py "nat=>nat"))

(add-computation-rules
 "NatHalf Zero" "Zero"
 "NatHalf(Succ Zero)" "Zero"
 "NatHalf(Succ(Succ n))" "Succ(NatHalf n)")

(set-totality-goal "NatHalf")
(assert "allnc n^(TotalNat n^ -> TotalNat(NatHalf n^) &
                                 TotalNat(NatHalf(Succ n^)))")
 (assume "n^" "Tn")
 (elim "Tn")
 (ng #t)
 (split)
 (use "TotalNatZero")
 (use "TotalNatZero")
 (assume "m^" "Tm" "IH")
 (split)
 (use "IH")
 (ng #t)
 (use "TotalNatSucc")
 (use "IH")
(assume "NatHalfTotalAux")
(assume "n^" "Tn")
(use "NatHalfTotalAux")
(use "Tn")
;; Proof finished.
(save-totality)

;; NatHalfDouble
(set-goal "all n NatHalf(NatDouble n)=n")
(ind)
(ng #t)
(use "Truth")
(assume "n" "IH")
(ng #t)
(use "IH")
;; Proof finished.
(save "NatHalfDouble")

;; NatHalfSuccDouble
(set-goal "all n NatHalf(Succ(NatDouble n))=n")
(ind)
(ng #t)
(use "Truth")
(assume "n" "IH")
(ng #t)
(use "IH")
;; Proof finished.
(save "NatHalfSuccDouble")

;; NatPlusDouble
(set-goal "all n,m NatDouble n+NatDouble m=NatDouble(n+m)")
(assume "n")
(ind)
(use "Truth")
(assume "m" "IH")
(ng #t)
(use "IH")
;; Proof finished.
(save "NatPlusDouble")

;; NatDoubleLt
(set-goal "all n,m (NatDouble n<NatDouble m)=(n<m)")
(ind)
(ng)
(cases)
(use "Truth")
(strip)
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
(ng)
(use "Truth")
(ng)
(use "IH")
;; Proof finished.
(save "NatDoubleLt")

;; NatDoubleLe
(set-goal "all n,m (NatDouble n<=NatDouble m)=(n<=m)")
(ind)
(ng)
(strip)
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
(ng)
(use "Truth")
(ng)
(use "IH")
;; Proof finished.
(save "NatDoubleLe")

;; NatLt0Double
(set-goal "all n(Zero<n -> Zero<NatDouble n)")
(cases)
(assume "Absurd")
(use "Absurd")
(strip)
(use "Truth")
;; Proof finished
(save "NatLt0Double")

;; NatLeDouble
(set-goal "all n n<=NatDouble n")
(ind)
(use "Truth")
(assume "n" "IH")
(ng)
(use "NatLeTrans" (pt "NatDouble n"))
(use "IH")
(use "Truth")
;; Proof finished.
(save "NatLeDouble")

;; NatLtDouble
(set-goal "all n(Zero<n -> n<NatDouble n)")
(ind)
(assume "Absurd")
(use "Absurd")
;; Step
(assume "n" "IH" "Useless")
(ng)
(use "NatLeLtTrans" (pt "NatDouble n"))
(use "NatLeDouble")
(use "Truth")
;; Proof finished.
(save "NatLtDouble")

;; NatDoubleMinus
(set-goal "all n,m NatDouble(n--m)=NatDouble n--NatDouble m")
(ind)
;; 2-3
(ng)
(strip)
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
;; 7,8
(ng)
(use "Truth")
;; 8
(ng)
(use "IH")
;; Proof finished.
(save "NatDoubleMinus")

;; NatLtSZeroSOne 
;; NatLtSOneSZero
;; NatLtSOneSOne

;; NatLeSZeroSOne
;; NatLeSOneSZero
;; NatLeSOneSOne

;; NatLtOneSZero
;; NatLtOneSOne

;; NatLeSZeroOne
;; NatLtSZeroOne

;; moved here from numbers.scm.  The terminology comes from pos: Double
;; for NatDouble, SOne for Succ(NatDouble)

;; NatLtDoubleSuccDouble
(set-goal "all n,m (NatDouble n<Succ(NatDouble m))=(n<=m)")
(ind) ;2-3
(assume "m")
(ng #t)
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
(ng #t)
(use "Truth")
(assume "m")
(ng #t)
(use "IH")
;; Proof finished.
(save "NatLtDoubleSuccDouble")

;; NatLtSuccDoubleDouble
(set-goal "all n,m (Succ(NatDouble n)<NatDouble m)=(n<m)")
(ind) ;2-3
(cases)
(ng #t)
(use "Truth")
(assume "m")
(ng #t)
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
(ng #t)
(use "Truth")
(assume "m")
(ng #t)
(use "IH")
;; Proof finished.
(save "NatLtSuccDoubleDouble")

;; NatLtSuccDoubleSuccDouble
(set-goal "all n,m
 (Succ(NatDouble n)<Succ(NatDouble m))=(n<m)")
(ind) ;2-3
(cases)
(ng #t)
(strip)
(use "Truth")
(assume "m")
(ng #t)
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
(ng #t)
(use "Truth")
(assume "m")
(ng #t)
(use "IH")
;; Proof finished.
(save "NatLtSuccDoubleSuccDouble")

;; NatLeDoubleSuccDouble
(set-goal "all n,m (NatDouble n<=Succ(NatDouble m))=(n<=m)")
(ind) ;2-3
(assume "m")
(ng #t)
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
(ng #t)
(use "Truth")
(assume "m")
(ng #t)
(use "IH")
;; Proof finished.
(save "NatLeDoubleSuccDouble")

;; NatLeSuccDoubleDouble
(set-goal "all n,m (Succ(NatDouble n)<=NatDouble m)=(n<m)")
(ind) ;2-3
(cases)
(ng #t)
(use "Truth")
(assume "m")
(ng #t)
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
(ng #t)
(use "Truth")
(assume "m")
(ng #t)
(use "IH")
;; Proof finished.
(save "NatLeSuccDoubleDouble")

;; NatLeSuccDoubleSuccDouble
(set-goal "all n,m
 (Succ(NatDouble n)<=Succ(NatDouble m))=(n<=m)")
(ind) ;2-3
(ng #t)
(strip)
(use "Truth")
;; 3
(assume "n" "IH")
(cases)
(ng #t)
(use "Truth")
(assume "m")
(ng #t)
(use "IH")
;; Proof finished.
(save "NatLeSuccDoubleSuccDouble")

;; NatLtOneDouble
(set-goal "all n(Zero<n -> Succ Zero<NatDouble n)")
(cases)
(assume "Absurd")
(use "Absurd")
(ng #t)
(strip)
(use "Truth")
;; Proof finished.
(save "NatLtOneDouble")

;; NatLtOneSuccDouble
(set-goal "all n(Zero<n -> Succ Zero<Succ(NatDouble n))")
(assume "n" "0<n")
(use "NatLtTrans" (pt "NatDouble n"))
(use "NatLtOneDouble")
(use "0<n")
(use "Truth")
;; Proof finished.
(save "NatLtOneSuccDouble")

;; NatLeDoubleOne
(set-goal "all n(Zero<n -> NatDouble n<=Succ Zero -> F)")
(cases)
(assume "Absurd" "Useless")
(use "Absurd")
(ng #t)
(assume "n" "Useless" "Absurd")
(use "Absurd")
;; Proof finished.
(save "NatLeDoubleOne")

;; NatLtDoubleOne
(set-goal "all n(Zero<n -> NatDouble n<Succ Zero -> F)")
(cases)
(assume "Absurd" "Useless")
(use "Absurd")
(ng #t)
(assume "n" "Useless" "Absurd")
(use "Absurd")
;; Proof finished.
(save "NatLtDoubleOne")

;; Reason to have a local efq assumption in CVIndPvar: soundness proof
;; does not normalize for Efq a global assumption.  Check

;; CVIndPvar
(set-goal "(F -> all n^(Pvar nat)n^) ->
  all n(all m(m<n -> (Pvar nat)m) -> (Pvar nat)n) ->
  all n (Pvar nat)n")
(assume "efq" "Prog")
(assert "all n,m(m<n -> (Pvar nat)m)")
 (ind)
 (assume "m" "Absurd")
 (use "efq")
 (use "Absurd")
 (assume "n" "IHn" "m" "m<Succ n")
 (use "NatLtSuccCases" (pt "m") (pt "n"))
 (use "m<Succ n")
 (use "IHn")
 (assume "m=n")
 (simp "m=n")
 (use "Prog")
 (use "IHn")
(assume "Assertion" "n")
(use "Assertion" (pt "Succ n"))
(use "Truth")
;; Proof finished.
(save "CVIndPvar")

;; (define sproof (proof-to-soundness-proof))
;; (define nsproof (np sproof))
;; (cdp nsproof)
;; (proof-to-expr-with-formulas nsproof)

;; In CVInd we do not need an Efq assumption since EfqEqD is avaiable
;; (pp "EfqEqD")
;; F -> all alpha^,alpha^0 alpha^ eqd alpha^0

;; CVInd
(set-goal "all nat=>boole(
 all n(all m(m<n -> (nat=>boole)m) -> (nat=>boole)n) ->
 all n (nat=>boole)n)")
(assume "nat=>boole" "Prog")
(assert "all n,m(m<n -> (nat=>boole)m)")
 (ind)
 (assume "m" "Absurd")
 (use "EfqAtom")
 (use "Absurd")
 (assume "n" "IHn" "m" "m<Succ n")
 (use "NatLtSuccCases" (pt "m") (pt "n"))
 (use "m<Succ n")
 (use "IHn")
 (assume "m=n")
 (simp "m=n")
 (use "Prog")
 (use "IHn")
(assume "Assertion" "n")
(use "Assertion" (pt "Succ n"))
(use "Truth")
;; Proof finished.
(save "CVInd")

;; NatHalfLt
(set-goal "all n(Zero<n -> NatHalf n<n)")
(assert "all n((Zero<n -> NatHalf n<n) &
                  NatHalf(Succ n)<Succ n)")
(use "CVIndPvar")
(use "Efq")
(assume "n" "Prog")
(split)
(cases (pt "n"))
(assume "Useless" "Absurd")
(use "Absurd")
(assume "l" "n=Sl" "Useless")
(use-with "Prog" (pt "l") "?" 'right)
(simp "n=Sl")
(use "Truth")
;; 7
(cases (pt "n"))
(ng #t)
(strip)
(use "Truth")
(assume "l" "n=Sl")
(ng #t)
(cases (pt "l"))
(ng #t)
(strip)
(use "Truth")
(assume "m" "l=Sm")
(simp "<-" "l=Sm")
(use "NatLtTrans" (pt "l"))
(use "Prog")
(simp "n=Sl")
(use "Truth")
(simp "l=Sm")
(use "Truth")
(use "Truth")
;; Assertion proved.
(assume "NatHalfLtAux" "n")
(use "NatHalfLtAux")
;; Proof finished.
(save "NatHalfLt")

;; NatHalfLtSucc
(set-goal "all n NatHalf n<Succ n")
(use "CVInd")
(assume "n" "Prog")
(cases (pt "n"))
(ng #t)
(strip)
(use "Truth")
(assume "m" "n=Sm")
(cases (pt "m"))
(ng #t)
(strip)
(use "Truth")
(assume "l" "m=Sl")
(ng #t)
(use "NatLtTrans" (pt "Succ l"))
(use "Prog")
(use "NatLtTrans" (pt "m"))
(simp "m=Sl")
(use "Truth")
(simp "n=Sm")
(use "Truth")
(use "Truth")
;; Proof finished.
(save "NatHalfLtSucc")

;; NatDoubleHalfEven
(set-goal "all n(NatEven n -> NatDouble(NatHalf n)=n)")
(assert "all n((NatEven n -> NatDouble(NatHalf n)=n) &
               (NatEven(Succ n) -> NatDouble(NatHalf(Succ n))=Succ n))")
(ind)
(split)
(ng #t)
(strip)
(use "Truth")
(ng #t)
(assume "Absurd")
(use "Absurd")
(assume "n" "IHn")
(split)
(use "IHn")
(ng #t)
(use "IHn")
;; Assertion proved.
(assume "NatDoubleHalfEvenAux" "n")
(use "NatDoubleHalfEvenAux")
;; Proof finished.
(save "NatDoubleHalfEven")

;; NatDoubleHalfOdd
(set-goal "all n((NatEven n -> F) -> Succ(NatDouble(NatHalf n))=n)")
(assert "all n(
   ((NatEven n -> F) -> Succ(NatDouble(NatHalf n))=n) &
   ((NatEven(Succ n) -> F) -> Succ(NatDouble(NatHalf(Succ n)))=Succ n))")
(ind)
(split)
(ng #t)
(assume "Absurd")
(use "Absurd")
(use "Truth")
(ng #t)
(strip)
(use "Truth")
(assume "n" "IHn")
(split)
(use "IHn")
(ng #t)
(use "IHn")
;; Assertion proved.
(assume "NatDoubleHalfOddAux" "n")
(use "NatDoubleHalfOddAux")
;; Proof finished.
(save "NatDoubleHalfOdd")

;; NatLtZeroHalfEven
(set-goal "all n(Zero<n -> NatEven n -> Zero<NatHalf n)")
(cases)
(assume "Absurd" "Useless")
(use "Absurd")
(cases)
(assume "Useless" "Absurd")
(use "Absurd")
(assume "n" "Useless1" "Useless2")
(use "Truth")
;; Proof finished.
(save "NatLtZeroHalfEven")

;; NatLtZeroHalfFinally
(set-goal "all n(Zero<n -> (n=Succ Zero -> F) -> Zero<NatHalf n)")
(cases)
(ng #t)
(assume "Absurd" "Useless")
(use "Absurd")
(cases)
(ng #t)
(assume "Useless" "Absurd")
(use "Absurd")
(use "Truth")
(ng #t)
(strip)
(use "Truth")
;; Proof finished.
(save "NatLtZeroHalfFinally")

;; For use with grec we add

(define natlt-obj (nbe-term-to-object (pt "NatLt") '()))

;; For the translation to Haskell we add

(add-program-constant "TranslationNatMinusPosDiff" (py "nat=>nat=>nat"))

