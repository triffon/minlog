;; $Id: nat.scm 2677 2014-01-08 10:03:39Z schwicht $
(display "loading nat.scm ...") (newline)

;; (load "~/minlog/init.scm")

(add-algs "nat" '("Zero" "nat") '("Succ" "nat=>nat"))
(add-totality "nat")

;; NatTotalVar
(set-goal "all nat TotalNat nat")
(use "AllTotalIntro")
(assume "nat^" "Tnat")
(use "Tnat")
;; Proof finished
(save "NatTotalVar")

(add-mr-ids "TotalNat")

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

(add-program-constant "NatPlus" (py "nat=>nat=>nat") t-deg-zero)
(add-program-constant "NatTimes" (py "nat=>nat=>nat") t-deg-zero)
(add-program-constant "NatLt" (py "nat=>nat=>boole") t-deg-zero)
(add-program-constant "NatLe" (py "nat=>nat=>boole") t-deg-zero)
(add-program-constant "Pred" (py "nat=>nat") t-deg-zero)
(add-program-constant "NatMinus" (py "nat=>nat=>nat") t-deg-zero)
(add-program-constant "NatMax" (py "nat=>nat=>nat") t-deg-zero)
(add-program-constant "NatMin" (py "nat=>nat=>nat") t-deg-zero)
(add-program-constant "AllBNat" (py "nat=>(nat=>boole)=>boole") t-deg-zero)
(add-program-constant "NatLeast" (py "nat=>(nat=>boole)=>nat") t-deg-zero)
(add-program-constant "NatLeastUp" (py "nat=>nat=>(nat=>boole)=>nat")
		      t-deg-zero)

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
(set-goal "all nat1,nat2(nat1=nat2 -> nat1 eqd nat2)")
(ind)
(cases)
(assume "Useless")
(use "InitEqD")
(assume "nat1" "0=Snat1")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "0=Snat1")
(assume "nat1" "IH1")
(cases)
(assume "Snat1=0")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "Snat1=0")
(assume "nat2" "Snat1=Snat2")
(assert "nat1 eqd nat2")
 (use "IH1")
 (use "Snat1=Snat2")
(assume "nat1=nat2")
(elim "nat1=nat2")
(assume "nat^1")
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
(use "EFEqD")
(use "AtomToEqDTrue")
(use "T=F")
(cases)
(assume "F=T")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "F=T")
(assume "Useless")
(use "InitEqD")
;; Proof finished.
(save "BooleEqToEqD")

;; Computation rules for the program constants.

;; For NatPlus
(add-computation-rules
 "nat+0" "nat"
 "nat1+Succ nat2" "Succ(nat1+nat2)")

;; For NatTimes
(add-computation-rules
 "nat*0" "0"
 "nat1*Succ nat2" "(nat1*nat2)+nat1")

;; For NatLt
(add-computation-rules
 "nat<0" "False"
 "0<Succ nat" "True"
 "Succ nat1<Succ nat2" "nat1<nat2")

;; For NatLe
(add-computation-rules
 "0<=nat" "True"
 "Succ nat<=0" "False"
 "Succ nat1<=Succ nat2" "nat1<=nat2")

;; For Pred
(add-computation-rules
 "Pred 0" "0"
 "Pred(Succ nat)" "nat")

;; For NatMinus
(add-computation-rules
 "nat--0" "nat"
 "nat1--Succ nat2" "Pred(nat1--nat2)")

;; For NatMax
(add-computation-rules
 "nat max 0" "nat"
 "0 max Succ nat" "Succ nat"
 "Succ nat1 max Succ nat2" "Succ(nat1 max nat2)")

;; For NatMin
(add-computation-rules
 "nat min 0" "0"
 "0 min Succ nat" "0"
 "Succ nat1 min Succ nat2" "Succ(nat1 min nat2)")

;; For AllBNat
(add-computation-rules
 "AllBNat 0 nat=>boole" "True"
 "AllBNat(Succ nat)nat=>boole" "AllBNat nat nat=>boole andb (nat=>boole)nat")

;; For NatLeast

(add-computation-rules
 "NatLeast 0(nat=>boole)" "0"
 "NatLeast(Succ nat)(nat=>boole)"
 "[if ((nat=>boole)0) 0 (Succ(NatLeast nat([nat1](nat=>boole)(Succ nat1))))]")

;; For NatLeastUp

(add-computation-rules
 "NatLeastUp nat0 nat(nat=>boole)"
 "[if (nat0<=nat) (NatLeast(nat--nat0)([nat1](nat=>boole)(nat1+nat0))+nat0) 0]")

;; We prove and add some properties of the program constants introduced,
;; either as rewrite rules or as theorems

;; Properties of NatPlus

(pp (rename-variables (term-to-totality-formula (pt "NatPlus"))))
;; allnc nat^(
;;  TotalNat nat^ -> allnc nat^0(TotalNat nat^0 -> TotalNat(nat^ +nat^0)))

;; NatPlusTotal
(set-goal (term-to-totality-formula (pt "NatPlus")))
(assume "nat^1" "Tnat1" "nat^2" "Tnat2")
(elim "Tnat2")
(ng #t)
(use "Tnat1")
(assume "nat^" "Tnat" "IH")
(ng #t)
(use "TotalNatSucc")
(use "IH")
;; Proof finished.
(save "NatPlusTotal")

(set-goal "all nat 0+nat=nat")
(ind)
  (use "Truth")
(assume "nat" "IH")
(use "IH")
;; Proof finished.
(add-rewrite-rule "0+nat" "nat")

(set-goal "all nat1,nat2 Succ nat1+nat2=Succ(nat1+nat2)")
(assume "nat1")
(ind)
  (use "Truth")
(assume "nat2" "IH")
(use "IH")
;; Proof finished.
(add-rewrite-rule "Succ nat1+nat2" "Succ(nat1+nat2)")

(set-goal "all nat1,nat2,nat3 nat1+(nat2+nat3)=nat1+nat2+nat3")
(assume "nat1" "nat2")
(ind)
  (use "Truth")
(assume "nat3" "IH")
(use "IH")
;; Proof finished.
(add-rewrite-rule "nat1+(nat2+nat3)" "nat1+nat2+nat3")

;; NatPlusComm
(set-goal "all nat1,nat2 nat1+nat2=nat2+nat1")
(assume "nat1")
(ind)
  (use "Truth")
(assume "nat2" "IH")
(use "IH")
;; Proof finished.
(save "NatPlusComm")

;; Properties of NatTimes

(pp (rename-variables (term-to-totality-formula (pt "NatTimes"))))
;; allnc nat^(
;;  TotalNat nat^ -> allnc nat^0(TotalNat nat^0 -> TotalNat(nat^ *nat^0)))

;; NatTimesTotal
(set-goal (term-to-totality-formula (pt "NatTimes")))
(assume "nat^1" "Tnat1" "nat^2" "Tnat2")
(elim "Tnat2")
(ng #t)
(use "TotalNatZero")
(assume "nat^" "Tnat" "IH")
(ng #t)
(use "NatPlusTotal")
(use "IH")
(use "Tnat1")
;; Proof finished
(save "NatTimesTotal")

(set-goal "all nat 0*nat=0")
(ind)
  (use "Truth")
(assume "nat" "IH")
(use "IH")
;; Proof finished.
(add-rewrite-rule "0*nat" "0")

;; NatCompat
(set-goal
 "all nat1,nat2(nat1=nat2 ->
                all nat=>boole^(nat=>boole^nat1 -> nat=>boole^nat2))")
(ind)
  (cases)
    (assume "0=0" "nat=>boole^" "H1")
    (use "H1")
  (assume "nat" "Absurd" "nat=>boole^" "H1")
  (use "Efq")
  (use "Absurd")
(assume "nat1" "IH")
(cases)
  (assume "Absurd" "nat=>boole^" "H1")
  (use "Efq")
  (use "Absurd")
(assume "nat2" "nat1=nat2" "nat=>boole^")
(use-with "IH" (pt "nat2") "nat1=nat2" (pt "[nat]nat=>boole^(Succ nat)"))
;; Proof finished.
(save "NatCompat")

;; NatEqCompat
(set-goal
 "all nat1,nat2(nat1=nat2 -> all nat=>nat(nat=>nat nat1=nat=>nat nat2))")
(ind)
  (cases)
    (assume "Trivial" "nat=>nat")
    (use "Truth")
  (assume "nat2" "Absurd" "nat=>nat")
  (use "Efq")
  (use "Absurd")
(assume "nat1" "IH")
(cases)
  (assume "Absurd" "nat=>nat")
  (use "Efq")
  (use "Absurd")
(assume "nat2" "nat1=nat2" "nat=>nat")
(use-with "IH" (pt "nat2") "nat1=nat2" (pt "[nat]nat=>nat(Succ nat)"))
;; Proof finished.
(save "NatEqCompat")

;; NatEqSym
(set-goal "all nat1,nat2(nat1=nat2 -> nat2=nat1)")
(ind)
  (cases)
    (assume "H")
    (use "H")
  (assume "nat2" "Absurd")
  (use "Absurd")
(assume "nat1" "IH")
(cases)
  (assume "H")
  (use "H")
(use "IH")
;; Proof finished.
(save "NatEqSym")

;; NatEqTrans
(set-goal "all nat1,nat2,nat3(nat1=nat2 -> nat2=nat3 -> nat1=nat3)")
(ind)
  (cases)
    (assume "nat3" "Trivial" "0=nat3")
    (use "0=nat3")
  (assume "nat2" "nat3" "Absurd" "H1")
  (use "Efq-Atom")
  (use "Absurd")
(assume "nat1" "IH")
(cases)
  (assume "nat3" "Absurd" "H1")
  (use "Efq-Atom")
  (use "Absurd")
(assume "nat2")
(cases)
  (assume "H1" "H2")
  (use "H2")
(use "IH")
;; Proof finished.
(save "NatEqTrans")

(set-goal "all nat1,nat2 Succ nat1*nat2=(nat1*nat2)+nat2")
(assume "nat1")
(ind)
  (use "Truth")
(assume "nat2" "IH")
(ng)
(use "NatEqTrans" (pt "nat1*nat2+nat2+nat1"))
(use-with "NatEqCompat" (pt "Succ nat1*nat2") (pt "nat1*nat2+nat2")
	  "IH" (pt "[nat]nat+nat1"))
(use-with "NatEqCompat" (pt "nat2+nat1") (pt "nat1+nat2") "?"
	  (pt "[nat]nat1*nat2+nat"))
(use "NatPlusComm")
;; Proof finished.
(add-rewrite-rule "Succ nat1*nat2" "(nat1*nat2)+nat2")

;; NatTimesPlusDistr
(set-goal "all nat1,nat2,nat3 nat1*(nat2+nat3)=(nat1*nat2)+(nat1*nat3)")
(assume "nat1" "nat2")
(ind)
(use "Truth")
(assume "nat3" "IH")
(ng #t)
(simp "IH")
(use "Truth")
;; Proof finished.
(save "NatTimesPlusDistr")
(add-rewrite-rule "nat1*(nat2+nat3)" "nat1*nat2+nat1*nat3")

;; NatTimesComm
(set-goal "all nat1,nat2 nat1*nat2=nat2*nat1")
(assume "nat1")
(ind)
  (use "Truth")
(assume "nat2" "IH")
(ng)
(use "NatEqTrans" (pt "nat2*nat1+nat1"))
(use-with "NatEqCompat" (pt "nat1*nat2") (pt "nat2*nat1") "IH"
	  (pt "[nat]nat+nat1"))
(use "Truth")
;; Proof finished.
(save "NatTimesComm")

;; NatTimesPlusDistrLeft
(set-goal "all nat1,nat2,nat3 (nat1+nat2)*nat3=(nat1*nat3)+(nat2*nat3)")
(assume "nat1" "nat2" "nat3")
(simp-with "NatTimesComm" (pt "nat1+nat2") (pt "nat3"))
(ng #t)
(simp-with "NatTimesComm" (pt "nat1") (pt "nat3"))
(simp-with "NatTimesComm" (pt "nat2") (pt "nat3"))
(use-with "Truth")
;; Proof finished.
(save "NatTimesPlusDistrLeft")
(add-rewrite-rule "(nat1+nat2)*nat3" "nat1*nat3+nat2*nat3")

(set-goal "all nat1,nat2,nat3 nat1*(nat2*nat3)=(nat1*nat2)*nat3")
(ind)
  (strip)
  (use "Truth")
(assume "nat1" "IH1" "nat2" "nat3")
(ng)
(simp-with "IH1" (pt "nat2") (pt "nat3"))
(use "Truth")
;; Proof finished.
(add-rewrite-rule "nat1*(nat2*nat3)" "nat1*nat2*nat3")

;; Properties of NatLt

;; (add-totality "boole") ;moved to boole.scm
;; (pp "TotalBooleTrue")
;; (pp "TotalBooleFalse")

(pp (rename-variables (term-to-totality-formula (pt "NatLt"))))
;; allnc nat^(
;;  TotalNat nat^ -> allnc nat^0(TotalNat nat^0 -> TotalBoole(nat^ <nat^0)))

;; NatLtTotal
(set-goal (term-to-totality-formula (pt "NatLt")))
(assume "nat^1" "Tnat1")
(elim "Tnat1")
(assume "nat^2" "Tnat2")
(elim "Tnat2")
(ng #t)
(use "TotalBooleFalse")
(assume "nat^3" "Tnat3" "Useless")
(ng #t)
(use "TotalBooleTrue")
(assume "nat^2" "Tnat2" "IH" "nat^3" "Tnat3")
(elim "Tnat3")
(ng #t)
(use "TotalBooleFalse")
(assume "nat^4" "Tnat4" "Useless")
(ng #t)
(use "IH")
(use "Tnat4")
;; Proof finished.
(save "NatLtTotal")

(set-goal "all nat nat<Succ nat")
(ind)
  (use "Truth")
(assume "nat" "IH")
(use "IH")
;; Proof finished.
(add-rewrite-rule "nat<Succ nat" "True")

(set-goal "all nat (nat<nat)=False")
(ind)
  (use "Truth")
(assume "nat" "IH")
(use "IH")
;; Proof finished.
(add-rewrite-rule "nat<nat" "False")

(set-goal "all nat(Succ nat<nat)=False")
(ind)
  (use "Truth")
(assume "nat" "IH")
(use "IH")
;; Proof finished.
(add-rewrite-rule "Succ nat<nat" "False")

;; NatLtTrans
(set-goal "all nat1,nat2,nat3(nat1<nat2 -> nat2<nat3 -> nat1<nat3)")
(ind)
  (cases)
    (assume "nat3" "Absurd" "0<nat3")
    (use "0<nat3")
  (assume "nat2")
  (cases)
    (assume "Trivial" "Absurd")
    (use "Absurd")
  (assume "nat3" "Trivial" "H1")
  (use "Truth")
(assume "nat1" "IH1")
(cases)
  (assume "nat3" "Absurd" "0<nat3")
  (use "Efq-Atom")
  (use "Absurd")
(assume "nat2")
(cases)
(assume "H1" "Absurd")
(use "Absurd")
(use "IH1")
;; Proof finished
(save "NatLtTrans")

;; NatLtSuccCases
(set-goal "all nat2,nat1(nat1<Succ nat2 -> (nat1<nat2 -> Pvar) ->
                                           (nat1=nat2 -> Pvar) -> Pvar)")
(ind)
  (cases)
    (assume "H1" "H2" "H3")
    (use "H3")
  (use "Truth")
  (assume "nat1" "Absurd" "H2" "H3")
  (use "Efq")
  (use "Absurd")
(assume "nat1" "IH")
(cases)
  (assume "H1" "H2" "H3")
  (use "H2")
  (use "Truth")
(use "IH")
;; Proof finished.
(save "NatLtSuccCases")

;; Properties of NatLe

(pp (rename-variables (term-to-totality-formula (pt "NatLe"))))
;; allnc nat^(
;;  TotalNat nat^ -> allnc nat^0(TotalNat nat^0 -> TotalBoole(nat^ <=nat^0)))

;; NatLeTotal
(set-goal (term-to-totality-formula (pt "NatLe")))
(assume "nat^1" "Tnat1")
(elim "Tnat1")
(assume "nat^2" "Tnat2")
(elim "Tnat2")
(ng #t)
(use "TotalBooleTrue")
(assume "nat^3" "Tnat3" "Useless")
(ng #t)
(use "TotalBooleTrue")
(assume "nat^2" "Tnat2" "IH" "nat^3" "Tnat3")
(elim "Tnat3")
(ng #t)
(use "TotalBooleFalse")
(assume "nat^4" "Tnat4" "Useless")
(ng #t)
(use "IH")
(use "Tnat4")
;; Proof finished.
(save "NatLeTotal")

(set-goal "all nat nat<=nat")
(ind)
  (use "Truth")
(assume "nat" "IH")
(use "IH")
;; Proof finished.
(add-rewrite-rule "nat<=nat" "True")

(set-goal "all nat1,nat2 nat1<=nat1+nat2")
(ind)
  (assume "nat2")
  (use "Truth")
(assume "nat" "IH")
(use "IH")
;; Proof finished.
(add-rewrite-rule "nat1<=nat1+nat2" "True")

(set-goal "all nat(Succ nat<=nat)=False")
(ind)
  (use "Truth")
(assume "nat" "IH")
(use "IH")
;; Proof finished.
(add-rewrite-rule "Succ nat<=nat" "False")

(set-goal "all nat nat<=Succ nat")
(ind)
  (use "Truth")
(assume "nat" "IH")
(use "IH")
;; Proof finished.
(add-rewrite-rule "nat<=Succ nat" "True")

;; NatLeTrans
(set-goal "all nat1,nat2,nat3(nat1<=nat2 -> nat2<=nat3 -> nat1<=nat3)")
(ind)
  (strip)
  (use "Truth")
(assume "nat1" "IH1")
(cases)
  (assume "nat3" "Absurd" "H1")
  (use "Efq-Atom")
  (use "Absurd")
(assume "nat2")
(cases)
  (assume "H1" "Absurd")
  (use "Absurd")
(use "IH1")
;; Proof finished.
(save "NatLeTrans")

;; NatLtLeTrans
(set-goal "all nat1,nat2,nat3(nat1<nat2 -> nat2<=nat3 -> nat1<nat3)")
(ind)
(cases)
  (assume "nat3" "Absurd" "H1")
  (use "Efq-Atom")
  (use "Absurd")
(assume "nat2")
(cases)
  (assume "H1" "Absurd")
  (use "Absurd")
(strip)
(use "Truth")
(assume "nat1" "IH1")
(cases)
  (assume "nat3" "Absurd" "H1")
  (use "Efq-Atom")
  (use "Absurd")
(assume "nat2")
(cases)
  (assume "H1" "Absurd")
  (use "Absurd")
(use "IH1")
;; Proof finished.
(save "NatLtLeTrans")

;; NatLeLtTrans
(set-goal "all nat1,nat2,nat3(nat1<=nat2 -> nat2<nat3 -> nat1<nat3)")
(ind)
(cases)
  (assume "nat3" "Trivial" "0<nat3")
  (use "0<nat3")
(assume "nat2")
(cases)
  (prop)
(assume "nat3")
(prop)
(assume "nat1" "IH1")
(cases)
  (assume "nat3" "Absurd" "H1")
  (use "Efq-Atom")
  (use "Absurd")
(assume "nat2")
(cases)
  (assume "H1" "Absurd")
  (use "Absurd")
(use "IH1")
;; Proof finished.
(save "NatLeLtTrans")

;; NatLtSuccToLe
(set-goal "all nat1,nat2(nat1<Succ nat2 -> nat1<=nat2)")
(ind)
  (strip)
  (use "Truth")
(assume "nat1" "IH1")
(cases)
  (assume "Absurd")
  (use "Absurd")
(use "IH1")
;; Proof finished.
(save "NatLtSuccToLe")

;; NatLtLtSuccTrans
(set-goal "all nat1,nat2,nat3(nat1<nat2 -> nat2<Succ nat3 -> nat1<nat3)")
(assume "nat1" "nat2" "nat3" "nat1<nat2" "nat2<Succ nat3")
(use "NatLtLeTrans" (pt "nat2"))
(use "nat1<nat2")
(use "NatLtSuccToLe")
(use "nat2<Succ nat3")
;; Proof finished.
(save "NatLtLtSuccTrans")

;; NatLeToLtSucc
(set-goal "all nat1,nat2(nat1<=nat2 -> nat1<Succ nat2)")
(ind)
  (strip)
  (use "Truth")
(assume "nat1" "IH1")
(cases)
  (assume "Absurd")
  (use "Absurd")
(use "IH1")
;; Proof finished.
(save "NatLeToLtSucc")

;; NatLtToSuccLe
(set-goal "all nat1,nat2(nat1<nat2 -> Succ nat1<=nat2)")
(ind)
  (cases)
  (assume "Absurd")
  (use "Efq")
  (use "Absurd")
  (assume "nat2" "Trivial")
  (use "Truth")
(assume "nat1" "IH1")
  (cases)
  (assume "Absurd")
  (use "Efq")
  (use "Absurd")
(use "IH1")
;; Proof finished.
(save "NatLtToSuccLe")

;; NatSuccLeToLt
(set-goal "all nat1,nat2(Succ nat1<=nat2 -> nat1<nat2)")
(ind)
  (cases)
  (assume "Absurd")
  (use "Efq")
  (use "Absurd")
  (assume "nat2" "Trivial")
  (use "Truth")
(assume "nat1" "IH1")
  (cases)
  (assume "Absurd")
  (use "Efq")
  (use "Absurd")
(use "IH1")
;; Proof finished.
(save "NatSuccLeToLt")

;; NatLeCases
(set-goal "all nat2,nat1(nat1<=nat2 -> (nat1<nat2 -> Pvar) ->
                        (nat1=nat2 -> Pvar) -> Pvar)")
(ind)
  (cases)
  (assume "H1" "H2" "H3")
  (use "H3")
  (use "Truth")
(assume "nat1" "Absurd" "H2" "H3")
(use "H2")
(use "Absurd")
(assume "nat1" "IH")
(cases)
  (assume "H1" "H2" "H3")
  (use "H2")
  (use "Truth")
(use "IH")
;; Proof finished.
(save "NatLeCases")

;; NatLeLtCases
(set-goal
 "all nat1,nat2((nat1<=nat2 -> Pvar) -> (nat2<nat1 -> Pvar) -> Pvar)")
(ind)
  (cases)
    (assume "H1" "H2")
    (use "H1")
    (use "Truth")
  (assume "nat1" "H1" "H2")
  (use "H1")
  (use "Truth")
(assume "nat1" "IH1")
(cases)
  (assume "H1" "H2")
  (use "H2")
  (use "Truth")
(assume "nat2" "H1" "H2")
(use "IH1" (pt "nat2"))
(use "H1")
(use "H2")
;; Proof finished.
(save "NatLeLtCases")

;; NatLeLin
(set-goal
 "all nat1,nat2((nat1<=nat2 -> Pvar) -> (nat2<=nat1 -> Pvar) -> Pvar)")
(ind)
  (cases)
    (assume "H1" "H2")
    (use "H1")
    (use "Truth")
  (assume "nat1" "H1" "H2")
  (use "H1")
  (use "Truth")
(assume "nat1" "IH1")
(cases)
  (assume "H1" "H2")
  (use "H2")
  (use "Truth")
(assume "nat2" "H1" "H2")
(use "IH1" (pt "nat2"))
(use "H1")
(use "H2")
;; Proof finished.
(save "NatLeLin")

;; NatNotLeToLt
(set-goal "all nat1,nat2((nat1<=nat2 -> F) -> nat2<nat1)")
(ind)
(assume "nat2" "H1")
(use-with "H1" "Truth")
(assume "nat1" "IH1")
(cases)
(assume "Trivial")
(use "Truth")
(use "IH1")
;; Proof finished.
(save "NatNotLeToLt")

;; NatNotLtToLe
(set-goal "all nat1,nat2((nat1<nat2 -> F) -> nat2<=nat1)")
(ind)
(cases)
(assume "Trivial")
(use "Truth")
(assume "nat2" "H1")
(use-with "H1" "Truth")
(assume "nat1" "IH1")
(cases)
(assume "Trivial")
(use "Truth")
(use "IH1")
;; Proof finished.
(save "NatNotLtToLe")

;; NatLtToLe
(set-goal "all nat1,nat2(nat1<nat2 -> nat1<=nat2)")
(ind)
(assume "nat2" "Useless")
(use "Truth")
(assume "nat" "IH")
(cases)
(assume "Absurd")
(use "Absurd")
(use "IH")
;; Proof finished.
(save "NatLtToLe")

;; NatLeAntiSym
(set-goal "all nat1,nat2(nat1<=nat2 -> nat2<=nat1 -> nat1=nat2)")
(ind)
(cases)
(assume "Useless1" "Useless2")
(use "Truth")
(assume "nat1" "Useless" "Absurd")
(use "Efq")
(use "Absurd")
(assume "nat1" "IHnat1")
(cases)
(assume "Absurd" "Useless")
(use "Efq")
(use "Absurd")
(assume "nat2")
(use "IHnat1")
;; Proof finished.
(save "NatLeAntiSym")

;; NatLtToLePred
(set-goal "all nat1,nat2(nat1<nat2 -> nat1<=Pred nat2)")
(assume "nat1")
(cases)
(assume "Absurd")
(use "Efq")
(use "Absurd")
(assume "nat2" "nat1<Succ nat2")
(use "NatLtSuccToLe")
(use "nat1<Succ nat2")
;; Proof finite
(save "NatLtToLePred")

;; NatLtMonPred
(set-goal "all nat1,nat2(0<nat1 -> nat1<nat2 -> Pred nat1<Pred nat2)")
(cases)
(assume "nat2" "Absurd" "Useless")
(use "Efq")
(use "Absurd")
(assume "nat1")
(cases)
(assume "Useless" "Absurd")
(use "Efq")
(use "Absurd")
(assume "nat2" "Useless" "nat1<nat2")
(use "nat1<nat2")
;; Proof finished.
(save "NatLtMonPred")

;; Properties of NatMinus and Pred

(pp (term-to-totality-formula (pt "Pred")))
;; allnc nat^612(TotalNat nat^612 -> TotalNat(Pred nat^612))

;; PredTotal
(set-goal (term-to-totality-formula (pt "Pred")))
(assume "nat^" "Tnat")
(elim "Tnat")
(ng #t)
(use "TotalNatZero")
(assume "nat^1" "Tnat1" "Useless")
(ng #t)
(use "Tnat1")
;; Proof finished.
(save "PredTotal")

(pp (term-to-totality-formula (pt "NatMinus")))
;; allnc nat^622(
;;  TotalNat nat^622 ->
;;  allnc nat^623(TotalNat nat^623 -> TotalNat(nat^622--nat^623)))

;; NatMinusTotal
(set-goal (term-to-totality-formula (pt "NatMinus")))
(assume "nat^1" "Tnat1" "nat^2" "Tnat2")
(elim "Tnat2")
(ng #t)
(use "Tnat1")
(assume "nat^" "Tnat" "IH")
(ng #t)
(use "PredTotal")
(use "IH")
;; Proof finished.
(save "NatMinusTotal")

(set-goal "all nat1,nat2 Pred(Succ nat1--nat2)=nat1--nat2")
(assume "nat1")
(ind)
  (use "Truth")
(assume "nat2" "IH")
(ng)
(simp-with "IH")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "Pred(Succ nat1--nat2)" "nat1--nat2")

(set-goal "all nat nat--nat=0")
(ind)
  (use "Truth")
(assume "nat" "IH")
(use "IH")
;; Proof finished.
(add-rewrite-rule "nat--nat" "0")

(set-goal "all nat Succ nat--nat=1")
(ind)
  (use "Truth")
(assume "nat" "IH")
(use "IH")
;; Proof finished.
(add-rewrite-rule "Succ nat--nat" "1")

;; Properties of NatMax

(pp (rename-variables (term-to-totality-formula (pt "NatMax"))))
;; allnc nat^(
;;  TotalNat nat^ -> allnc nat^0(TotalNat nat^0 -> TotalBoole(nat^ max nat^0)))

;; NatMaxTotal
(set-goal (term-to-totality-formula (pt "NatMax")))
(assume "nat^1" "Tnat1")
(elim "Tnat1")
(assume "nat^2" "Tnat2")
(elim "Tnat2")
(ng #t)
(use "TotalNatZero")
(assume "nat^3" "Tnat3" "Useless")
(ng #t)
(use "TotalNatSucc")
(use "Tnat3")
(assume "nat^2" "Tnat2" "IH" "nat^3" "Tnat3")
(elim "Tnat3")
(ng #t)
(use "TotalNatSucc")
(use "Tnat2")
(assume "nat^4" "Tnat4" "Useless")
(ng #t)
(use "TotalNatSucc")
(use "IH")
(use "Tnat4")
;; Proof finished.
(save "NatMaxTotal")

(set-goal "all nat 0 max nat=nat")
(cases)
  (use "Truth")
(strip)
(use "Truth")
;; Proof finished.
(add-rewrite-rule "0 max nat" "nat")

(set-goal "all nat nat max nat = nat")
(ind)
  (use "Truth")
(assume "nat" "IH")
(use "IH")
;; Proof finished.
(add-rewrite-rule "nat max nat" "nat")

(set-goal "all nat1,nat2,nat3(
            nat1 max (nat2 max nat3)=nat1 max nat2 max nat3)")
(ind)
  (strip)
  (use "Truth")
(assume "nat1" "IH1")
(cases)
  (strip)
  (use "Truth")
(assume "nat2")
(cases)
  (use "Truth")
(use "IH1")
;; Proof finished.
(add-rewrite-rule
 "nat1 max (nat2 max nat3)" "nat1 max nat2 max nat3")

;; NatMaxComm
(set-goal "all nat1,nat2 nat1 max nat2 = nat2 max nat1")
(ind)
  (strip)
  (use "Truth")
(assume "nat1" "IH")
(cases)
  (use "Truth")
(use "IH")
;; Proof finished.
(save "NatMaxComm")

;; NatMaxUB1
(set-goal "all nat1,nat2 nat1<=nat1 max nat2")
(ind)
  (assume "nat2")
  (use "Truth")
(assume "nat1" "IH1")
(cases)
  (use "Truth")
(use "IH1")
;; Proof finished.
(save "NatMaxUB1")

;; NatMaxUB2
(set-goal "all nat1,nat2 nat2<=nat1 max nat2")
(ind)
  (assume "nat2")
  (use "Truth")
(assume "nat1" "IH1")
(cases)
  (use "Truth")
(use "IH1")
;; Proof finished.
(save "NatMaxUB2")

;; NatMaxLUB
(set-goal "all nat1,nat2,nat3(nat1<=nat3 -> nat2<=nat3 -> nat1 max nat2<=nat3)")
(ind)
(cases)
(strip)
(use "Truth")
(assume "nat2" "nat3" "Useless1" "Hyp")
(use "Hyp")
(assume "nat1" "IHnat1")
(cases)
(cases)
(assume "Absurd" "Useless")
(use "Absurd")
(assume "nat3" "Hyp" "Useless")
(use "Hyp")
(assume "nat2")
(cases)
(assume "Absurd" "Useless")
(use "Absurd")
(assume "nat3")
(ng #t)
(use "IHnat1")
;; Proof finished
(save "NatMaxLUB")

;; Properties of NatMin

(pp (rename-variables (term-to-totality-formula (pt "NatMin"))))
;; allnc nat^(
;;  TotalNat nat^ -> allnc nat^0(TotalNat nat^0 -> TotalBoole(nat^ min nat^0)))

;; NatMinTotal
(set-goal (term-to-totality-formula (pt "NatMin")))
(assume "nat^1" "Tnat1")
(elim "Tnat1")
(assume "nat^2" "Tnat2")
(elim "Tnat2")
(ng #t)
(use "TotalNatZero")
(assume "nat^3" "Tnat3" "Useless")
(ng #t)
(use "TotalNatZero")
(assume "nat^2" "Tnat2" "IH" "nat^3" "Tnat3")
(elim "Tnat3")
(ng #t)
(use "TotalNatZero")
(assume "nat^4" "Tnat4" "Useless")
(ng #t)
(use "TotalNatSucc")
(use "IH")
(use "Tnat4")
;; Proof finished.
(save "NatMinTotal")

(set-goal "all nat 0 min nat=0")
(cases)
  (use "Truth")
(strip)
(use "Truth")
;; Proof finished.
(add-rewrite-rule "0 min nat" "0")

(set-goal "all nat nat min nat = nat")
(ind)
  (use "Truth")
(assume "nat" "IH")
(use "IH")
;; Proof finished.
(add-rewrite-rule "nat min nat" "nat")

(set-goal "all nat1,nat2,nat3(
            nat1 min (nat2 min nat3)=nat1 min nat2 min nat3)")
(ind)
  (strip)
  (use "Truth")
(assume "nat1" "IH1")
(cases)
  (strip)
  (use "Truth")
(assume "nat2")
(cases)
  (use "Truth")
(use "IH1")
;; Proof finished.
(add-rewrite-rule "nat1 min (nat2 min nat3)" "nat1 min nat2 min nat3")

;; NatMinComm
(set-goal "all nat1,nat2 nat1 min nat2 = nat2 min nat1")
(ind)
  (strip)
  (use "Truth")
(assume "nat1" "IH")
(cases)
  (use "Truth")
(use "IH")
;; Proof finished.
(save "NatMinComm")

;; NatMinLB1
(set-goal "all nat1,nat2 nat1 min nat2<=nat1")
(ind)
  (assume "nat2")
  (use "Truth")
(assume "nat1" "IH1")
(cases)
  (use "Truth")
(use "IH1")
;; Proof finished.
(save "NatMinLB1")

;; NatMinLB2
(set-goal "all nat1,nat2 nat1 min nat2<=nat2")
(ind)
  (assume "nat2")
  (use "Truth")
(assume "nat1" "IH1")
(cases)
  (use "Truth")
(use "IH1")
;; Proof finished.
(save "NatMinLB2")

;; NatIfTotal
(set-goal "allnc nat^(TotalNat nat^ ->
 allnc alpha^,(nat=>alpha)^(Total alpha^ ->
 allnc nat^1(TotalNat nat^1 -> Total((nat=>alpha)^ nat^1)) ->
 Total[if nat^ alpha^ (nat=>alpha)^]))")
(assume "nat^" "Tnat" "alpha^" "(nat=>alpha)^" "Talpha" "Tf")
(elim "Tnat")
(use "Talpha")
(assume "nat^1" "Tnat1" "Useless")
(ng #t)
(use "Tf")
(use "Tnat1")
;; Proof finished.
(save "NatIfTotal")

;; NatEqTotal
(set-goal "allnc nat^1(
 TotalNat nat^1 -> allnc nat^2(TotalNat nat^2 -> TotalBoole(nat^1 =nat^2)))")
(assume "nat^1" "Tnat1")
(elim "Tnat1")
(assume "nat^2" "Tnat2")
(elim "Tnat2")
(use "TotalBooleTrue")
(assume "nat^3" "Useless1" "Useless2")
(use "TotalBooleFalse")
(assume "nat^3" "Tnat3" "IHn3" "nat^4" "Tnat4")
(elim "Tnat4")
(use "TotalBooleFalse")
(assume "nat^5" "Tnat5" "Useless")
(use "IHn3")
(use "Tnat5")
;; Proof finished.
(save "NatEqTotal")

;; Properties of AllBNat

(pp (rename-variables (term-to-totality-formula (pt "AndConst"))))
;; allnc boole^(
;;  TotalBoole boole^ ->
;;  allnc boole^0(TotalBoole boole^0 -> TotalBoole(boole^ andb boole^0)))

(pp (term-to-totality-formula (pt "AllBNat")))
;; allnc nat^805(
;;  TotalNat nat^805 ->
;;  allnc (nat=>boole)^806(
;;   allnc nat^807(TotalNat nat^807 -> TotalBoole((nat=>boole)^806 nat^807)) ->
;;   TotalBoole(AllBNat nat^805(nat=>boole)^806)))

;; AllBNatTotal
(set-goal (term-to-totality-formula (pt "AllBNat")))
(assume "nat^" "Tnat")
(elim "Tnat")
(assume "(nat=>boole)^" "Useless")
(ng #t)
(use "TotalBooleTrue")
(assume "nat^1" "Tnat1" "IH" "(nat=>boole)^" "Hyp")
(ng #t)
(use "AndConstTotal")
(use "IH")
(use "Hyp")
(use "Hyp")
(use "Tnat1")
;; Proof finished.
(save "AllBNatTotal")

;; AllBNatIntro
(set-goal "all (nat=>boole),nat2(
      all nat1(nat1<nat2 -> (nat=>boole)nat1) ->
      AllBNat nat2([nat1](nat=>boole)nat1))")
(assume "(nat=>boole)")
(ind)
  (strip)
  (use "Truth")
(assume "nat2" "IH" "H")
(ng)
(split)
  (use "IH")
  (assume "nat1" "nat1<nat2")
  (use "H")
  (use "NatLtTrans" (pt "nat2"))
  (use "nat1<nat2")
  (use "Truth")
(use "H")
(use "Truth")
;; Proof finished.
(save "AllBNatIntro")

;; AllBNatElim
(set-goal "all (nat=>boole),nat2(
      AllBNat nat2(nat=>boole) ->
      all nat1(nat1<nat2 -> (nat=>boole)nat1))")
(assume "(nat=>boole)")
(ind)
  (assume "H1" "nat1" "Absurd")
  (use "Efq")
  (use "Absurd")
(assume "nat2" "IH")
(ng)
(assume "AllBHyp" "nat1" "nat1<Succ nat2")
(use "NatLtSuccCases" (pt "nat2") (pt "nat1"))
(use "nat1<Succ nat2")
(use "IH")
(use "AllBHyp")
(assume "nat1=nat2")
(simp "nat1=nat2")
(use "AllBHyp")
;; Proof finished.
(save "AllBNatElim")

;; NatLeastTotal
(set-goal (rename-variables (term-to-totality-formula (pt "NatLeast"))))
(assume "nat^" "Tnat")
(elim "Tnat")
(ng #t)
(strip)
(use "TotalNatZero")
(assume "nat^1" "Tnat1" "IH" "nat=>boole^" "Tg")
(ng #t)
(use "BooleIfTotal")
(use "Tg")
(use "TotalNatZero")
(use "TotalNatZero")
(use "TotalNatSucc")
(use "IH")
(ng #t)
(assume "nat^2" "Tnat2")
(use "Tg")
(use "TotalNatSucc")
(use "Tnat2")
;; Proof finished.
(save "NatLeastTotal")

;; NatLeastBound
(set-goal "all nat1,(nat=>boole) NatLeast nat1(nat=>boole)<=nat1")
(ind)
(ng #t)
(strip)
(use "Truth")
(assume "nat1" "IH" "(nat=>boole)")
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
(set-goal "all nat1,nat2,(nat=>boole)(
 (nat=>boole)nat2 -> (NatLeast nat1 nat=>boole)<=nat2)")
(ind)
(strip)
(use "Truth")
(assume "nat1" "IH")
(cases)
(assume "(nat=>boole)" "g0")
(ng #t)
(simp "g0")
(use "Truth")
(assume "nat2" "(nat=>boole)" "g(Sn)")
(ng #t)
(cases 'auto)
(strip)
(use "Truth")
(strip)
(ng #t)
(use-with "IH" (pt "nat2") (pt "[nat]((nat=>boole)(Succ nat))") "?")
(ng #t)
(use "g(Sn)")
;; Proof finished.
(save "NatLeastLeIntro")

;; NatLeastLtElim
(set-goal "all nat,(nat=>boole)(
 NatLeast nat(nat=>boole)<nat -> (nat=>boole)(NatLeast nat(nat=>boole)))")
(ind)
(assume "(nat=>boole)")
(ng #t)
(use "Efq")
(assume "nat" "IH" "(nat=>boole)")
(ng #t)
(cases (pt "(nat=>boole)0"))
(assume "g0" "Useless")
(use "g0")
(assume "(nat=>boole)0 -> F")
(ng #t)
(use "IH")
;; Proof finished.
(save "NatLeastLtElim")

;; NatLeastUpTotal
(set-goal (rename-variables (term-to-totality-formula (pt "NatLeastUp"))))
(assume "nat^0" "Tnat0" "nat^" "Tnat" "nat=>boole^" "Tg")
(ng #t)
(use "BooleIfTotal")
(use "NatLeTotal")
(use "Tnat0")
(use "Tnat")
(use "NatPlusTotal")
(use "NatLeastTotal")
(use "NatMinusTotal")
(use "Tnat")
(use "Tnat0")
(assume "nat^1" "Tnat1")
(ng #t)
(use "Tg")
(use "NatPlusTotal")
(use "Tnat1")
(use "Tnat0")
(use "Tnat0")
(use "TotalNatZero")
;; Proof finished.
(save "NatLeastUpTotal")

;; We postpone proofs of the NatLeastUpBound NatLeastUpLBound
;; NatLeastUpLeIntro NatLeastUpLtElim NatLeastUpZero since they use
;; monotonicity properties of NatLt which are only proved later.

;; We add some further rewrite rules and theorems.  The order is
;; somewhat delicate, since the proofs can depend on which rewrite
;; rules are present, and also which program constants have been proved
;; to be total.

(set-goal "all nat1,nat2 nat1<=nat2+nat1")
(ind)
  (assume "nat1")
  (use "Truth")
(assume "nat1" "IH")
(use "IH")
;; Proof finished.
(add-rewrite-rule "nat1<=nat2+nat1" "True")

(set-goal "all nat1,nat2 (nat1+nat2<nat1)=False")
(assert "all nat3,nat4(nat3+nat4<nat3 -> F)")
 (ind)
 (assume "nat3" "Absurd")
 (use "Absurd")
 (assume "nat3" "IH")
 (cases)
 (assume "Absurd")
 (use "Absurd")
 (assume "nat4")
 (ng #t)
 (assume "Succ(nat3+nat4)<nat3")
 (use "IH" (pt "nat4"))
 (use "NatLtTrans" (pt "Succ(nat3+nat4)"))
 (use "Truth")
 (use "Succ(nat3+nat4)<nat3")
(assume "Prop" "nat1" "nat2")
(use "AtomFalse")
(use "Prop")
;; Proof finished.
(add-rewrite-rule "nat1+nat2<nat1" "False")

(set-goal "all nat Pred nat<=nat")
(cases)
(use "Truth")
(assume "nat")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "Pred nat<=nat" "True")

(set-goal "all nat 0--nat=0")
(ind)
  (use "Truth")
(assume "nat" "IH")
(ng #t)
(simp "IH")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "0--nat" "0")

(set-goal "all nat1,nat2 nat1--nat2<=nat1")
(assume "nat1")
(ind)
  (use "Truth")
(assume "nat2" "IH")
(ng #t)
(use "NatLeTrans" (pt "nat1--nat2"))
(use "Truth")
(use "IH")
;; Proof finished.
(add-rewrite-rule "nat1--nat2<=nat1" "True")

(set-goal "all nat1,nat2 nat1+nat2--nat2=nat1")
(assume "nat1")
(ind)
  (use "Truth")
(assume "nat2" "IH")
(ng #t)
(use "IH")
(add-rewrite-rule "nat1+nat2--nat2" "nat1")

(set-goal "all nat1,nat2 nat2+nat1--nat2=nat1")
(assume "nat1")
(ind)
  (use "Truth")
(assume "nat2" "IH")
(ng #t)
(use "IH")
(add-rewrite-rule "nat2+nat1--nat2" "nat1")

(set-goal "all nat1,nat2 nat1*Pred nat2=nat1*nat2--nat1")
(assume "nat1")
(ind)
  (use "Truth")
(assume "nat2" "IH")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "nat1*Pred nat2" "nat1*nat2--nat1")

(set-goal "all nat1,nat2 Pred nat2*nat1=nat2*nat1--nat1")
(assume "nat1")
(ind)
  (use "Truth")
(assume "nat2" "IH")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "Pred nat2*nat1" "nat2*nat1--nat1")

(set-goal "all nat1,nat2,nat3 nat1--nat2--nat3=nat1--(nat2+nat3)")
(assume "nat1" "nat2")
(ind)
  (use "Truth")
(assume "nat3" "IH")
(ng #t)
(simp "IH")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "nat1--nat2--nat3" "nat1--(nat2+nat3)")

(set-goal "all nat1,nat2,nat3 nat1*(nat2--nat3)=nat1*nat2--nat1*nat3")
(assume "nat1" "nat2")
(ind)
  (use "Truth")
(assume "nat3" "IH")
(ng #t)
(simp "IH")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "nat1*(nat2--nat3)" "nat1*nat2--nat1*nat3")

(set-goal "all nat1,nat2,nat3 (nat2--nat3)*nat1=nat2*nat1--nat3*nat1")
(assume "nat1" "nat2")
(ind)
  (use "Truth")
(assume "nat3" "IH")
(ng #t)
(simp "IH")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "(nat2--nat3)*nat1" "nat2*nat1--nat3*nat1")

;; NatLeMonPlus
(set-goal
 "all nat1,nat2,nat3,nat4(nat1<=nat2 -> nat3<=nat4 -> nat1+nat3<=nat2+nat4)")
(assume "nat1" "nat2")
(ind)
(ind)
(assume "nat1<=nat2" "Useless")
(use "nat1<=nat2")
(assume "nat4" "IH4")
(assume "nat1<=nat2" "Useless")
(use "NatLeTrans" (pt "nat2+nat4"))
(use "IH4")
(use "nat1<=nat2")
(use "Truth")
(use "Truth")
(assume "nat3" "IH3")
(cases)
(assume "Useless" "Absurd")
(use "Efq")
(use "Absurd")
(use "IH3")
;; Proof finished.
(save "NatLeMonPlus")

;; NatLeMonTimes
(set-goal
 "all nat1,nat2,nat3,nat4(nat1<=nat2 -> nat3<=nat4 -> nat1*nat3<=nat2*nat4)")
(assume "nat1" "nat2")
(ind)
(ind)
(assume "Useless1" "Useless2")
(use "Truth")
(assume "nat4" "IH4")
(assume "Useless1" "Useless2")
(use "Truth")
(assume "nat3" "IH3")
(cases)
(assume "Useless" "Absurd")
(use "Efq")
(use "Absurd")
(assume "nat4" "nat1<=nat2" "nat3<=nat4")
(ng)
(use "NatLeMonPlus")
(use "IH3")
(use "nat1<=nat2")
(use "nat3<=nat4")
(use "nat1<=nat2")
;; Proof finished.
(save "NatLeMonTimes")

;; NatLeMonPred
(set-goal "all nat1,nat2(nat1<=nat2 -> Pred nat1<=Pred nat2)")
(cases)
(assume "nat2" "Useless")
(use "Truth")
(assume "nat1")
(cases)
(assume "Absurd")
(use "Efq")
(use "Absurd")
(assume "nat2" "nat1<=nat2")
(use "nat1<=nat2")
;; Proof finished.
(save "NatLeMonPred")

;; NatLeMonMinus
(set-goal
 "all nat1,nat2,nat3,nat4(nat1<=nat2 -> nat3<=nat4 -> nat1--nat4<=nat2--nat3)")
(assume "nat1" "nat2" "nat3" "nat4" "nat1<=nat2" "nat3<=nat4")
(use "NatLeTrans" (pt "nat2--nat4"))
;; ?_3: nat1--nat4<=nat2--nat4
(ind (pt "nat4"))
(use "nat1<=nat2")
(assume "nat" "IH")
(ng #t)
(use "NatLeMonPred")
(use "IH")
;; ?_4: nat2--nat4<=nat2--nat3
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
(use "nat3<=nat4")
;; Proof finished.
(save "NatLeMonMinus")


;; NatPlusMinus
(set-goal
 "all nat1,nat2,nat3(nat3<=nat2 -> nat1+(nat2--nat3)=nat1+nat2--nat3)")
(assume "nat1" "nat2")
(ind)
(assume "Useless")
(use "Truth")
(assume "nat3" "IH" "n3+1<=n2")
(ng #t)
(assert "all nat4,nat5(0<nat5 -> nat4+Pred nat5=Pred(nat4+nat5))")
 (assume "nat4")
 (cases)
 (assume "Absurd")
 (use "Efq")
 (use "Absurd")
 (assume "nat5" "Useless")
 (use "Truth")
(assume "NatPlusPred")
(simp "<-" "IH")
(use "NatPlusPred")
(drop "IH" "NatPlusPred")
(use "NatLtLeTrans" (pt "Succ nat3--nat3"))
(use "Truth")
(use "NatLeMonMinus")
(use "n3+1<=n2")
(use "Truth")
(use "NatLeTrans" (pt "Succ nat3"))
(use "Truth")
(use "n3+1<=n2")
;; Proof finished.
(save "NatPlusMinus")

;; NatMinusPlus
(set-goal
 "all nat1,nat2,nat3(nat3<=nat1 -> nat1--nat3+nat2=nat1+nat2--nat3)")
(assume "nat1" "nat2")
(ind)
(assume "Useless")
(use "Truth")
(assume "nat3" "IH" "n3+1<=n1")
(ng #t)
(assert "all nat5,nat4(0<nat4 -> Pred nat4+nat5=Pred(nat4+nat5))")
 (assume "nat5")
 (cases)
 (assume "Absurd")
 (use "Efq")
 (use "Absurd")
 (assume "nat4" "Useless")
 (use "Truth")
(assume "NatPlusPred")
(simp "<-" "IH")
(use "NatPlusPred")
(drop "IH" "NatPlusPred")
(use "NatLtLeTrans" (pt "Succ nat3--nat3"))
(use "Truth")
(use "NatLeMonMinus")
(use "n3+1<=n1")
(use "Truth")
(use "NatLeTrans" (pt "Succ nat3"))
(use "Truth")
(use "n3+1<=n1")
;; Proof finished.
(save "NatMinusPlus")

;; NatMinusPlusEq
(set-goal "all nat1,nat2(nat2<=nat1 -> nat1--nat2+nat2=nat1)")
(assume "nat1" "nat2" "nat2<=nat1")
(simp "NatMinusPlus")
(use "Truth")
(use "nat2<=nat1")
;; Proof finished.
(save "NatMinusPlusEq")

;; NatMinusMinus
(set-goal  "all nat1,nat2,nat3(
  nat3<=nat2 -> nat2<=nat1+nat3 -> nat1--(nat2--nat3)=nat1+nat3--nat2)")
(assume "nat1")
(ind)
(cases)
(assume "Useless1" "Useless2")
(use "Truth")
(assume "nat2" "Absurd" "Useless")
(use "Efq")
(use "Absurd")
(assume "nat2" "IH2")
(cases)
(assume "Useless1" "Useless2")
(use "Truth")
(assume "nat3" "nat3<=nat2" "nat2<=nat1+nat3")
(ng)
(use "IH2")
(use "nat3<=nat2")
(use "nat2<=nat1+nat3")
;; Proof finished.
(save "NatMinusMinus")

;; NatLtMonPlus1
(set-goal "all nat1,nat2,nat3,nat4(
 nat1<nat2 -> nat3<=nat4 -> nat1+nat3<nat2+nat4)")
(ind)
(cases)
(assume "nat3" "nat4")
(ng #t)
(use "Efq")
(assume "nat2" "nat3" "nat4" "Useless" "nat3<=nat4")
(ng #t)
(use "NatLeToLtSucc")
(use "NatLeTrans" (pt "nat4"))
(use "nat3<=nat4")
(ng #t)
(use "Truth")
(assume "nat1" "IH")
(ng #t)
(cases)
(assume "nat3" "nat4")
(ng #t)
(use "Efq")
(ng #t)
(use "IH")
;; Proof finished.
(save "NatLtMonPlus1")

;; NatLtMonPlus2
(set-goal "all nat1,nat2,nat3,nat4(
 nat1<=nat2 -> nat3<nat4 -> nat1+nat3<nat2+nat4)")
(assume "nat1" "nat2")
(ind)
(cases)
(ng #t)
(assume "Useless")
(use "Efq")
(assume "nat3" "nat1<=nat2" "Useless")
(ng #t)
(use "NatLeToLtSucc")
(use "NatLeTrans" (pt "nat2"))
(use "nat1<=nat2")
(ng #t)
(use "Truth")
(assume "nat3" "IH")
(ng #t)
(cases)
(assume "nat1<=nat2")
(ng #t)
(use "Efq")
(ng #t)
(use "IH")
;; Proof finished.
(save "NatLtMonPlus2")

;; NatLtMonMinusLeft
(set-goal "all nat1,nat2,nat3(
 nat2<nat3 -> nat1<=nat2 -> nat2--nat1<nat3--nat1)")
(ind)
(ng #t)
(assume "nat2" "nat3" "nat2<nat3" "Useless")
(use "nat2<nat3")
(assume "nat1" "IH")
(cases)
(ng #t)
(assume "nat3" "Useless")
(use "Efq")
(assume "nat2")
(cases)
(ng #t)
(assume "Absurd" "Useless")
(use "Absurd")
(assume "nat3")
(ng #t)
(use "IH")
(save "NatLtMonMinusLeft")

;; NatLtMonMinus
(set-goal
 "all nat1,nat2,nat3,nat4(nat1<nat2 -> nat3<=nat4 -> nat4<nat1 ->
                          nat1--nat4<nat2--nat3)")
(assume "nat1" "nat2" "nat3" "nat4" "nat1<nat2" "nat3<=nat4" "nat4<nat1")
(use "NatLtLeTrans" (pt "nat2--nat4"))
;; nat1--nat4<nat2--nat4
(use "NatLtMonMinusLeft")
(use "nat1<nat2")
(use "NatLtToLe")
(use "nat4<nat1")
;; nat2--nat4<=nat2--nat3
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
(use "nat3<=nat4")
;; Proof finished.
(save "NatLtMonMinus")


;;  NatLeastUpBound
(set-goal "all nat0,nat1,(nat=>boole) NatLeastUp nat0 nat1(nat=>boole)<=nat1")
(assume "nat0" "nat1" "(nat=>boole)")
(ng #t)
(cases (pt "nat0<=nat1"))
(assume "nat0<=nat1")
(ng #t)
(use "NatLeTrans" (pt "nat1--nat0+nat0"))
(use "NatLeMonPlus")
(use "NatLeastBound")
(use "Truth")
(simp "NatMinusPlusEq")
(use "Truth")
(use "nat0<=nat1")
(strip)
(use "Truth")
;; Proof finished.
(save "NatLeastUpBound")

;; NatLeastUpLBound
(set-goal "all nat0,nat1,(nat=>boole)(
 nat0<=nat1 -> nat0<=NatLeastUp nat0 nat1(nat=>boole))")
(assume "nat0" "nat1" "(nat=>boole)" "nat0<=nat1")
(ng #t)
(simp "nat0<=nat1")
(ng #t)
(use "Truth")
;; Proof finished.
(save "NatLeastUpLBound")

;; NatLeastUpLeIntro
(set-goal "all nat0,nat1,nat2,(nat=>boole)(
 nat0<=nat2 -> (nat=>boole)nat2 -> NatLeastUp nat0 nat1(nat=>boole)<=nat2)")
(assume "nat0" "nat1" "nat2" "(nat=>boole)" "nat0<=nat2" "(nat=>boole)nat2")
(ng #t)
(cases (pt "nat0<=nat1"))
(assume "nat0<=nat1")
(ng #t)
(assert "NatLeast(nat1--nat0)([nat](nat=>boole)(nat+nat0))<=nat2--nat0")
 (use "NatLeastLeIntro")
 (ng #t)
 (simp "NatMinusPlusEq")
 (use "(nat=>boole)nat2")
 (use "nat0<=nat2")
(assume "Assertion")
(assert
 "NatLeast(nat1--nat0)([nat](nat=>boole)(nat+nat0))+nat0<=nat2--nat0+nat0")
 (use "NatLeMonPlus")
 (use "Assertion")
 (use "Truth")
 (simp "NatMinusPlusEq")
(assume "Hyp")
(use "Hyp")
(use "nat0<=nat2")
(strip)
(use "Truth")
;; Proof finished.
(save "NatLeastUpLeIntro")

;; NatLeastUpLtElim
(set-goal "all nat0,nat1,(nat=>boole)(
 nat0<=NatLeastUp nat0 nat1(nat=>boole) ->
 NatLeastUp nat0 nat1(nat=>boole)<nat1 ->
 (nat=>boole)(NatLeastUp nat0 nat1(nat=>boole)))")
(assume "nat0" "nat1" "(nat=>boole)" "nat0<=m" "m<nat1")
(ng #t)
(assert "nat0<=nat1")
 (use "NatLeTrans" (pt "NatLeastUp nat0 nat1(nat=>boole)"))
 (use "nat0<=m")
 (use "NatLtToLe")
 (use "m<nat1")
(assume "nat0<=nat1")
(simp "nat0<=nat1")
(ng #t)
(use-with "NatLeastLtElim"
	  (pt "nat1--nat0")
	  (pt "[nat]((nat=>boole)(nat+nat0))") "?")
(ng "m<nat1")
(simphyp-with-to "m<nat1" "nat0<=nat1" "SimpHyp")
(ng "SimpHyp")
(assert
 "NatLeast(nat1--nat0)([nat](nat=>boole)(nat+nat0))+nat0--nat0<nat1--nat0")
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
(set-goal "all nat,(nat=>boole)
 NatLeastUp Zero nat(nat=>boole)=NatLeast nat(nat=>boole)")
(assume "nat" "nat=>boole")
(use "Truth")
;; Proof finished.
(save "NatLeastUpZero")
(add-rewrite-rule "NatLeastUp Zero nat(nat=>boole)" "NatLeast nat(nat=>boole)")

;; NatRecTotal
(set-goal (rename-variables (term-to-totality-formula (pt "(Rec nat=>alpha)"))))
(assume "nat^" "Tn")
(elim "Tn")
(ng #t)
(assume "alpha^" "Talpha")
(strip)
(use "Talpha")
(assume "nat^1" "Tn1" "IH" "alpha^" "Talpha" "(nat=>alpha=>alpha)^" "Tf")
(ng #t)
(use "Tf")
(use "Tn1")
(use "IH")
(use "Talpha")
(use "Tf")
;; Proof finished.
(save "NatRecTotal")

;; NatDouble
(add-program-constant "NatDouble" (py "nat=>nat"))

(add-computation-rules
 "NatDouble Zero" "Zero"
 "NatDouble(Succ nat)" "Succ(Succ(NatDouble nat))")

;; NatDoubleTotal
(set-goal (rename-variables (term-to-totality-formula (pt "NatDouble"))))
(assume "nat^" "Tnat")
(elim "Tnat")
(use "TotalNatZero")
(assume "nat^1" "Tnat1" "IH")
(ng #t)
(use "TotalNatSucc")
(use "TotalNatSucc")
(use "IH")
;; Proof finished.
(save "NatDoubleTotal")

;; NatDoubleDefSucc
(set-goal "all nat NatDouble(Succ nat)=Succ(Succ(NatDouble nat))")
(assume "nat")
(use "Truth")
;; Proof finished.
(save "NatDoubleDefSucc")

(add-program-constant "NatEven" (py "nat=>boole"))

(add-computation-rules
 "NatEven Zero" "True"
 "NatEven(Succ Zero)" "False"
 "NatEven(Succ(Succ nat))" "NatEven nat")

;; NatEvenTotal
(set-goal (rename-variables (term-to-totality-formula (pt "NatEven"))))
(assert "allnc nat^(TotalNat nat^ ->
         TotalBoole(NatEven(Succ nat^)) &
         TotalBoole(NatEven(Succ(Succ nat^))))")
 (assume "nat^" "Tnat")
 (elim "Tnat")
 (ng #t)
 (split)
 (use "TotalBooleFalse")
 (use "TotalBooleTrue")
 (assume "nat^1" "Tnat1" "IH")
 (ng)
 (split)
 (use "IH")
 (use "IH")
(assume "NatEvenTotalAux")
(ng)
(assume "nat^" "Tnat")
(use "NatEvenTotalAux")
(use "Tnat")
;; Proof finished.
(save "NatEvenTotal")

;; NatEvenDouble
(set-goal "all nat NatEven(NatDouble nat)")
(ind)
(ng #t)
(use "Truth")
(assume "nat" "IH")
(ng #t)
(use "IH")
;; Proof finished.
(save "NatEvenDouble")

;; NatEvenSucc
(set-goal "all nat(NatEven nat -> NatEven(Succ nat) -> F)")
(ind)
(ng #t)
(assume "Useless" "Absurd")
(use "Absurd")
(assume "nat" "IH" "ESn" "ESSn")
(ng "ESSn")
(use "IH")
(use "ESSn")
(use "ESn")
;; Proof finished.
(save "NatEvenSucc")

;; NatOddSuccToEven
(set-goal "all nat((NatEven(Succ nat) -> F) ->NatEven nat)")
(ind)
(ng #t)
(strip)
(use "Truth")
(assume "nat" "IH" "OSSn")
(cases (pt "NatEven(Succ nat)"))
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
 "NatHalf(Succ(Succ nat))" "Succ(NatHalf nat)")

;; NatHalfTotal
(set-goal (rename-variables (term-to-totality-formula (pt "NatHalf"))))
(assert "allnc nat^(TotalNat nat^ -> TotalNat(NatHalf nat^) &
                                     TotalNat(NatHalf(Succ nat^)))")
 (assume "nat^" "Tnat")
 (elim "Tnat")
 (ng #t)
 (split)
 (use "TotalNatZero")
 (use "TotalNatZero")
 (assume "nat^1" "Tnat1" "IH")
 (split)
 (use "IH")
 (ng #t)
 (use "TotalNatSucc")
 (use "IH")
(assume "NatHalfTotalAux")
(assume "nat^" "Tnat")
(use "NatHalfTotalAux")
(use "Tnat")
;; Proof finished.
(save "NatHalfTotal")

;; NatHalfDouble
(set-goal "all nat NatHalf(NatDouble nat)=nat")
(ind)
(ng #t)
(use "Truth")
(assume "nat" "IH")
(ng #t)
(use "IH")
;; Proof finished.
(save "NatHalfDouble")

;; NatHalfSuccDouble
(set-goal "all nat NatHalf(Succ(NatDouble nat))=nat")
(ind)
(ng #t)
(use "Truth")
(assume "nat" "IH")
(ng #t)
(use "IH")
;; Proof finished.
(save "NatHalfSuccDouble")

;; "CVInd"
(set-goal "all nat(all nat1(nat1<nat -> (Pvar nat)nat1) ->
                   (Pvar nat)nat) -> all nat (Pvar nat)nat")
(assume "Prog")
(assert "all nat,nat1(nat1<nat -> (Pvar nat)nat1)")
 (ind)
 (assume "nat1" "Absurd")
 (use "Efq")
 (use "Absurd")
 (assume "nat" "IHnat" "nat1" "nat1<Succ nat")
 (use "NatLtSuccCases" (pt "nat") (pt "nat1"))
 (use "nat1<Succ nat")
 (use "IHnat")
 (assume "nat1=nat")
 (simp "nat1=nat")
 (use "Prog")
 (use "IHnat")
(assume "Assertion" "nat")
(use "Assertion" (pt "Succ nat"))
(use "Truth")
;; Proof finished.
(save "CVInd")

;; NatHalfLt
(set-goal "all nat(Zero<nat -> NatHalf nat<nat)")
(assert "all nat((Zero<nat -> NatHalf nat<nat) &
                  NatHalf(Succ nat)<Succ nat)")
(use "CVInd")
(assume "nat" "Prog")
(split)
(cases (pt "nat"))
(assume "Useless" "Absurd")
(use "Absurd")
(assume "nat1" "nat=Snat1" "Useless")
(use-with "Prog" (pt "nat1") "?" 'right)
(simp "nat=Snat1")
(use "Truth")
;; 7
(cases (pt "nat"))
(ng #t)
(strip)
(use "Truth")
(assume "nat1" "nat=Snat1")
(ng #t)
(cases (pt "nat1"))
(ng #t)
(strip)
(use "Truth")
(assume "nat2" "nat1=Snat2")
(simp "<-" "nat1=Snat2")
(use "NatLtTrans" (pt "nat1"))
(use "Prog")
(simp "nat=Snat1")
(use "Truth")
(simp "nat1=Snat2")
(use "Truth")
(use "Truth")
;; Assertion proved.
(assume "NatHalfLtAux" "nat")
(use "NatHalfLtAux")
;; Proof finished.
(save "NatHalfLt")

;; NatHalfLtSucc
(set-goal "all nat NatHalf nat<Succ nat")
(use "CVInd")
(assume "nat" "Prog")
(cases (pt "nat"))
(ng #t)
(strip)
(use "Truth")
(assume "nat1" "nat=Sn1")
(cases (pt "nat1"))
(ng #t)
(strip)
(use "Truth")
(assume "nat2" "nat1=Sn2")
(ng #t)
(use "NatLtTrans" (pt "Succ nat2"))
(use "Prog")
(use "NatLtTrans" (pt "nat1"))
(simp "nat1=Sn2")
(use "Truth")
(simp "nat=Sn1")
(use "Truth")
(use "Truth")
;; Proof finished.
(save "NatHalfLtSucc")

;; NatDoubleHalfEven
(set-goal "all nat(NatEven nat -> NatDouble(NatHalf nat)=nat)")
(assert
 "all nat((NatEven nat -> NatDouble(NatHalf nat)=nat) &
          (NatEven(Succ nat) -> NatDouble(NatHalf(Succ nat))=Succ nat))")
(ind)
(split)
(ng #t)
(strip)
(use "Truth")
(ng #t)
(assume "Absurd")
(use "Absurd")
(assume "nat" "IHnat")
(split)
(use "IHnat")
(ng #t)
(use "IHnat")
;; Assertion proved.
(assume "NatDoubleHalfEvenAux" "nat")
(use "NatDoubleHalfEvenAux")
;; Proof finished.
(save "NatDoubleHalfEven")

;; NatDoubleHalfOdd
(set-goal "all nat((NatEven nat -> F) -> Succ(NatDouble(NatHalf nat))=nat)")
(assert "all nat(
   ((NatEven nat -> F) -> Succ(NatDouble(NatHalf nat))=nat) &
   ((NatEven(Succ nat) -> F) -> Succ(NatDouble(NatHalf(Succ nat)))=Succ nat))")
(ind)
(split)
(ng #t)
(assume "Absurd")
(use "Absurd")
(use "Truth")
(ng #t)
(strip)
(use "Truth")
(assume "nat" "IHnat")
(split)
(use "IHnat")
(ng #t)
(use "IHnat")
;; Assertion proved.
(assume "NatDoubleHalfOddAux" "nat")
(use "NatDoubleHalfOddAux")
;; Proof finished.
(save "NatDoubleHalfOdd")

;; NatLtZeroHalfEven
(set-goal "all nat(Zero<nat -> NatEven nat -> Zero<NatHalf nat)")
(cases)
(assume "Absurd" "Useless")
(use "Absurd")
(cases)
(assume "Useless" "Absurd")
(use "Absurd")
(assume "nat" "Useless1" "Useless2")
(use "Truth")
;; Proof finished.
(save "NatLtZeroHalfEven")

;; NatLtZeroHalfFinally
(set-goal "all nat(Zero<nat -> (nat=Succ Zero -> F) -> Zero<NatHalf nat)")
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

(add-var-name "n" "m" "k" (py "nat"))

