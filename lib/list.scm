;; $Id: list.scm 2678 2014-01-08 10:04:13Z schwicht $

;; (load "~/git/minlog/init.scm")
;; (set! COMMENT-FLAG #f)
;; (libload "nat.scm")
;; (set! COMMENT-FLAG #t)

(if (not (assoc "nat" ALGEBRAS))
    (myerror "First execute (libload \"nat.scm\")"))

(display "loading list.scm ...") (newline)

(add-algs "list" 'prefix-typeop
	  '("list" "Nil")
	  '("alpha=>list=>list" "Cons"))
(add-rtotality "list")
(add-totality "list")
(add-mr-ids "TotalList")

;; Infix notation allowed (and type parameters omitted) for binary
;; constructors, as follows.  This would also work for prefix notation.
;; Example: :: for Cons.  x::y::z:
;; Here : is postfix for z

(add-infix-display-string "Cons" "::" 'pair-op) ;right associative

;; The postfix-op ":" with "x:" for "x::(Nil rho)" needs a special
;; treatment with explicit uses of add-token and add-display.

(add-token
 ":" 'postfix-op
 (lambda (x)
   (mk-term-in-app-form
    (make-term-in-const-form
     (let* ((constr (constr-name-to-constr "Cons"))
	    (tvars (const-to-tvars constr))
	    (subst (make-substitution tvars (list (term-to-type x)))))
       (const-substitute constr subst #f)))
    x
    (make-term-in-const-form
     (let* ((constr (constr-name-to-constr "Nil"))
	    (tvars (const-to-tvars constr))
	    (subst (make-substitution tvars (list (term-to-type x)))))
       (const-substitute constr subst #f))))))

(add-display
 (py "list alpha")
 (lambda (x)
   (if (term-in-app-form? x)
       (let ((op (term-in-app-form-to-final-op x))
	     (args (term-in-app-form-to-args x)))
	 (if (and (term-in-const-form? op)
		  (string=? "Cons" (const-to-name
				    (term-in-const-form-to-const op)))
		  (= 2 (length args))
		  (term-in-const-form? (cadr args))
		  (string=? "Nil" (const-to-name
				   (term-in-const-form-to-const (cadr args)))))
	     (list 'postfix-op ":" (term-to-token-tree (car args)))
	     #f))
       #f)))

(add-var-name "x" (py "alpha"))
(add-var-name "xs" (py "list alpha"))

;; ListTotalVar
(set-goal "all xs TotalList xs")
(use "AllTotalIntro")
(assume "xs^" "Txs")
(use "Txs")
;; Proof finished.
(save "ListTotalVar")

(add-ids (list (list "STotalList" (make-arity (py "list alpha")) "nat"))
	 '("STotalList(Nil alpha)" "STotalListNil")
	 '("allnc x^,xs^(
             STotalList xs^ -> STotalList(x^ ::xs^))" "STotalListCons"))

;; We could use (RTotalList (cterm (x^) T))xs^ for STotalList xs^.
;; However, STotalList is just convenient.

(add-mr-ids "STotalList")

(display-idpc "STotalListMR")

;; STotalListMR
;; 	STotalListNilMR:	STotalListMR 0(Nil alpha)
;; 	STotalListConsMR:
;; allnc x^,xs^,n^(STotalListMR n^ xs^ --> STotalListMR(Succ n^)(x^ ::xs^))

(add-program-constant
 "ListAppend" (py "list alpha=>list alpha=>list alpha") t-deg-zero 'const 1)

(add-infix-display-string "ListAppend" ":+:" 'mul-op)

(add-computation-rules
 "(ListAppend alpha)(Nil alpha)" "[xs]xs"
 "(ListAppend alpha)(x::xs1)" "[xs2](x::xs1:+:xs2)")

;; (pp (rename-variables (term-to-totality-formula (pt "(ListAppend alpha)"))))

;; allnc xs^(
;;  TotalList xs^ -> allnc xs^0(TotalList xs^0 -> TotalList(xs^ :+:xs^0)))

;; ListAppendTotal
(set-goal (term-to-totality-formula (pt "(ListAppend alpha)")))
(assume "xs^1" "Txs1" "xs^2" "Txs2")
(elim "Txs1")
(ng #t)
(use "Txs2")
(assume "x^" "Tx" "xs^3" "Txs3" "IH")
(ng #t)
(use "TotalListCons")
(use "Tx")
(use "IH")
;; Proof finished.
(save "ListAppendTotal")

;; ListAppendTotalSound
(set-goal (real-and-formula-to-mr-formula
	   (pt "(ListAppend alpha)")
	   (proof-to-formula (theorem-name-to-proof "ListAppendTotal"))))
(assume "xs^1" "xs^10" "TMRxs10xs1" "xs^2" "xs^20" "TMRxs20xs2")
(elim "TMRxs10xs1")
(use "TMRxs20xs2")
(assume "x^" "x^0" "TMRx0x" "xs^" "xs^0" "TMRxs0xs" "IH")
(ng #t)
(use "TotalListConsMR")
(use "TMRx0x")
(use "IH")
;; Proof finished.
(save "ListAppendTotalReal")

;; (pp (rename-variables (term-to-stotality-formula (pt "(ListAppend alpha)"))))

;; allnc xs^(
;;  STotalList xs^ -> allnc xs^0(STotalList xs^0 -> STotalList(xs^ :+:xs^0)))

;; ListAppendSTotal
(set-goal (term-to-stotality-formula (pt "(ListAppend alpha)")))
(assume "xs^1" "STxs1" "xs^2" "STxs2")
(elim "STxs1")
(ng #t)
(use "STxs2")
(assume "x^" "xs^3" "STxs3" "IH")
(ng #t)
(use "STotalListCons")
(use "IH")
;; Proof finished.
(save "ListAppendSTotal")

;; (pp (rename-variables (proof-to-extracted-term "ListAppendSTotal")))
;; [n,n0](Rec nat=>nat)n n0([n1,n2]Succ n2)

;; ListAppendSTotalSound
(set-goal (real-and-formula-to-mr-formula
	   (nt (proof-to-extracted-term "ListAppendSTotal"))
	   (proof-to-formula (theorem-name-to-proof "ListAppendSTotal"))))
(assume "xs^1" "n^1" "STMRn1xs1" "xs^2" "n^2" "TMRn2xs2")
(elim "STMRn1xs1")
(use "TMRn2xs2")
(assume "x^" "xs^" "n^" "STMRnxs" "IH")
(ng #t)
(use "STotalListConsMR")
(use "IH")
;; Proof finished.
(save "ListAppendSTotalSound")

;; ListAppendNil
(set-goal "all xs xs:+:(Nil alpha)eqd xs")
(ind)
(use "InitEqD")
(assume "x" "xs" "IH")
(ng)
(simp "IH")
(use "InitEqD")
;; Proof finished.
(save "ListAppendNil")

;; ListAppendNilPartial
(set-goal "all xs^(STotalList xs^ -> xs^ :+:(Nil alpha)eqd xs^)")
(assume "xs^" "STxs")
(elim "STxs")
(use "InitEqD")
(assume "x^" "xs^1" "STxs1" "IH")
(ng #t)
(simp "IH")
(use "InitEqD")
;; Proof finished.
(save "ListAppendNilPartial")

;; This is not added as a rewrite rule, because ListAppend is defined
;; by recursion over the first argument and expects rules of arity 1.

;; ListAppendNilPartialSound
(set-goal (real-and-formula-to-mr-formula
	   'eps
	   (proof-to-formula (theorem-name-to-proof "ListAppendNilPartial"))))
(assume "xs^" "n^" "STMRnxs")
(elim "STMRnxs")
(use "InitEqD")
(assume "x^1" "xs^1" "n^1" "STMRn1xs1" "IH")
(ng #t)
(simp "IH")
(use "InitEqD")
;; Proof finished.
(save "ListAppendNilPartialSound")

;; We also provide a variant ListAppd of ListAppend (with display ++),
;; which allows rewrite rules with two arguments.

(add-program-constant
 "ListAppd" (py "list alpha=>list alpha=>list alpha") t-deg-zero)

(add-infix-display-string "ListAppd" "++" 'mul-op)

(add-computation-rules
 "(Nil alpha)++xs2" "xs2"
 "(x1::xs1)++xs2" "x1::xs1++xs2")

;; (pp (rename-variables (term-to-totality-formula (pt "(ListAppd alpha)"))))

;; allnc xs^(
;;  TotalList xs^ -> allnc xs^0(TotalList xs^0 -> TotalList(xs^ ++xs^0)))

;; ListAppdTotal
(set-goal (term-to-totality-formula (pt "(ListAppd alpha)")))
(assume "xs^1" "Txs1" "xs^2" "Txs2")
(elim "Txs1")
(ng #t)
(use "Txs2")
(assume "x^" "Tx" "xs^3" "Txs3" "IH")
(ng #t)
(use "TotalListCons")
(use "Tx")
(use "IH")
;; Proof finished.
(save "ListAppdTotal")

;; (pp (rename-variables (term-to-stotality-formula (pt "(ListAppd alpha)"))))

;; allnc xs^(
;;  STotalList xs^ -> allnc xs^0(STotalList xs^0 -> STotalList(xs^ ++xs^0)))

;; ListAppdTotalSound
(set-goal (real-and-formula-to-mr-formula
	   (pt "(ListAppd alpha)")
	   (proof-to-formula (theorem-name-to-proof "ListAppdTotal"))))
(assume "xs^1" "xs^10" "TMRxs10xs1" "xs^2" "xs^20" "TMRxs20xs2")
(elim "TMRxs10xs1")
(use "TMRxs20xs2")
(assume "x^" "x^0" "TMRx0x" "xs^" "xs^0" "TMRxs0xs" "IH")
(ng #t)
(use "TotalListConsMR")
(use "TMRx0x")
(use "IH")
;; Proof finished.
(save "ListAppdTotalReal")

;; ListAppdSTotal
(set-goal (term-to-stotality-formula (pt "(ListAppd alpha)")))
(assume "xs^1" "STxs1" "xs^2" "STxs2")
(elim "STxs1")
(ng #t)
(use "STxs2")
(assume "x^" "xs^3" "STxs3" "IH")
(ng #t)
(use "STotalListCons")
(use "IH")
;; Proof finished.
(save "ListAppdSTotal")

;; ListAppdSTotalSound
(set-goal (real-and-formula-to-mr-formula
	   (nt (proof-to-extracted-term "ListAppdSTotal"))
	   (proof-to-formula (theorem-name-to-proof "ListAppdSTotal"))))
(assume "xs^1" "n^1" "STMRn1xs1" "xs^2" "n^2" "TMRn2xs2")
(elim "STMRn1xs1")
(use "TMRn2xs2")
(assume "x^" "xs^" "n^" "STMRnxs" "IH")
(ng #t)
(use "STotalListConsMR")
(use "IH")
;; Proof finished.
(save "ListAppdSTotalSound")

;; ListAppdNil
(set-goal "all xs xs++(Nil alpha)eqd xs")
(ind)
(use "InitEqD")
(assume "x" "xs" "IH")
(ng)
(simp "IH")
(use "InitEqD")
;; Proof finished.
(add-rewrite-rule "xs++(Nil alpha)" "xs")

;; ListAppdNilPartial
(set-goal "all xs^(STotalList xs^ -> xs^ ++(Nil alpha)eqd xs^)")
(assume "xs^" "STxs")
(elim "STxs")
(use "InitEqD")
(assume "x^" "xs^1" "STxs1" "IH")
(ng #t)
(simp "IH")
(use "InitEqD")
;; Proof finished.
(save "ListAppdNilPartial")

;; ListAppdNilPartialSound
(set-goal (real-and-formula-to-mr-formula
	   'eps
	   (proof-to-formula (theorem-name-to-proof "ListAppdNilPartial"))))
(assume "xs^" "n^" "STMRnxs")
(elim "STMRnxs")
(use "InitEqD")
(assume "x^1" "xs^1" "n^1" "STMRn1xs1" "IH")
(ng #t)
(simp "IH")
(use "InitEqD")
;; Proof finished.
(save "ListAppdNilPartialSound")

;; ListAppdAssoc
(set-goal "all xs1,xs2,xs3 xs1++(xs2++xs3)eqd xs1++xs2++xs3")
(ind)
(assume "xs2" "xs3")
(use "InitEqD")
(assume "x1" "xs1" "IH")
(ng)
(assume "xs2" "xs3")
(simp "IH")
(use "InitEqD")
;; Proof finished.
(save "ListAppdAssoc")

;; We could add associativity as a rewrite rule by executing
;; (add-rewrite-rule "xs1++(xs2++xs3)" "xs1++xs2++xs3")

;; However, this will block other rewriting rules in long appends.
;; Example: consider (pt "s++(L::t++R:)") and (pt "s++(L::t)++R:").
;; Both are normal, since rewriting (pt "(L::t)++R:") into (pt
;; "L::t++R:") is blocked by the leading s++ and the fact that ++
;; associates to the left.

;; x: ++xs converts into x::xs.  However, xs1++x2: ++xs2 does not rewrite,
;; because ++ associates to the left.  But we can add the corresponding
;; rule:

(set-goal "all xs1,x2,xs2 xs1++x2: ++xs2 eqd xs1++(x2::xs2)")
(ind)
(assume "x2" "xs2")
(use "InitEqD")
(assume "x" "xs1" "IHxs1" "x2" "xs2")
(ng)
(simp "IHxs1")
(use "InitEqD")
;; Proof finished.
(add-rewrite-rule "xs1++x2: ++xs2" "xs1++(x2::xs2)")

;; In the other direction this rule would lead to non-termination, if
;; we also had associativity as a rewrite rule.  x2: is x2::(Nil par),
;; and this again is a redex for associativity.

(add-program-constant "ListLength" (py "list alpha=>nat") t-deg-zero)
(add-prefix-display-string "ListLength" "Lh")

(add-computation-rules
 "Lh(Nil alpha)" "Zero"
 "Lh(x::xs)" "Succ Lh xs")

;; (pp (rename-variables (term-to-totality-formula (pt "(ListLength alpha)"))))
;; allnc xs^(TotalList xs^ -> TotalNat(Lh xs^))

;; ListLengthTotal
(set-goal (term-to-totality-formula (pt "(ListLength alpha)")))
(assume "xs^" "Txs")
(elim "Txs")
(ng #t)
(use "TotalNatZero")
(assume "x^" "Tx" "xs^1" "Txs1" "IH")
(ng #t)
(use "TotalNatSucc")
(use "IH")
;; Proof finished.
(save "ListLengthTotal")

;; ListLengthTotalSound
(set-goal (real-and-formula-to-mr-formula
	   (pt "(ListLength alpha)")
	   (proof-to-formula (theorem-name-to-proof "ListLengthTotal"))))
(assume "xs^1" "xs^10" "TMRxs10xs1")
(elim "TMRxs10xs1")
(use "TotalNatZeroMR")
(assume "x^" "x^0" "TMRx0x" "xs^" "xs^0" "TMRxs0xs" "IH")
(ng #t)
(use "TotalNatSuccMR")
(use "IH")
;; Proof finished.
(save "ListLengthTotalReal")

;; ListLengthSTotal
(set-goal (term-to-stotality-formula (pt "(ListLength alpha)")))
(assume "xs^" "STxs")
(elim "STxs")
(ng #t)
(use "TotalNatZero")
(assume "x^" "xs^1" "STxs1" "IH")
(ng #t)
(use "TotalNatSucc")
(use "IH")
;; Proof finished.
(save "ListLengthSTotal")

(pp (rename-variables (proof-to-extracted-term "ListLengthSTotal")))
;; [n](Rec nat=>nat)n 0([n0,n1]Succ n1)

;; ListLengthSTotalSound
(set-goal (real-and-formula-to-mr-formula
	   (proof-to-extracted-term "ListLengthSTotal")
	   (proof-to-formula (theorem-name-to-proof "ListLengthSTotal"))))
(assume "xs^1" "n^1" "STMRn1xs1")
(elim "STMRn1xs1")
(ng #t)
(use "TotalNatZeroMR")
(assume "x^" "xs^" "n^" "STMRnxs" "IH")
(ng #t)
(use "TotalNatSuccMR")
(use "IH")
;; Proof finished.
(save "ListLengthSTotalSound")

;; LhZeroImpNil
(set-goal "all xs(Lh xs=0 -> xs eqd(Nil alpha))")
(cases)
(assume "Useless")
(use "InitEqD")
(assume "x" "xs" "Absurd")
(use "Efq")
(use "Absurd")
;; Proof finished.
(save "LhZeroImpNil")

;; LhAppend
(set-goal "all xs1,xs2 Lh(xs1:+:xs2)=Lh xs1+Lh xs2")
(ind)
(assume "xs2")
(use "Truth")
(assume "x" "xs1" "IH")
(use "IH")
;; Proof finished.
(save "LhAppend")

(add-rewrite-rule "Lh(xs1:+:xs2)" "Lh xs1+Lh xs2")

;; LhAppd
(set-goal "all xs1,xs2 Lh(xs1++xs2)=Lh xs1+Lh xs2")
(ind)
(assume "xs2")
(use "Truth")
(assume "x" "xs1" "IH")
(use "IH")
;; Proof finished.
(save "LhAppd")

(add-rewrite-rule "Lh(xs1++xs2)" "Lh xs1+Lh xs2")

;; Now for projection ListProj.  We use the rule (n thof (Nil alpha)) ->
;; (Inhab alpha)

(add-program-constant "ListProj" (py "nat=>list alpha=>alpha") t-deg-zero)

(add-infix-display-string "ListProj" "thof" 'pair-op) ;right associative

(add-token
 "__" 'mul-op ;hence left associative
 (lambda (xs y)
   (mk-term-in-app-form
    (make-term-in-const-form
     (let* ((const (pconst-name-to-pconst "ListProj"))
	    (tvars (const-to-tvars const))
	    (listtype (term-to-type xs))
	    (type (car (alg-form-to-types listtype)))
	    (subst (make-substitution tvars (list type))))
       (const-substitute const subst #f)))
    y xs)))

;; Not used (reason: occurrences of "thof" examples/tait)
;; (add-display
;;  (py "alpha")
;;  (lambda (x)
;;    (if (term-in-app-form? x)
;;        (let ((op (term-in-app-form-to-final-op x))
;; 	     (args (term-in-app-form-to-args x)))
;; 	 (if (and (term-in-const-form? op)
;; 		  (string=? "ListProj"
;; 			    (const-to-name (term-in-const-form-to-const op)))
;; 		  (= 2 (length args)))
;; 	     (list 'mul-op "__"
;; 		   (term-to-token-tree (car args))
;; 		   (term-to-token-tree (cadr args)))
;; 	     #f))
;;        #f)))

(add-computation-rules
 "nat thof(Nil alpha)" "(Inhab alpha)"
 "0 thof x::xs1" "x"
 "Succ nat1 thof x::xs1" "nat1 thof xs1")

;; (pp (nt (pt "0 thof 3::2::1::0:")))
;; 3
;; (pp (nt (pt "1 thof 3::2::1::0:")))
;; 2
;; (pp (nt (pt "3 thof 3::2::1::0:")))
;; 0
;; (pp (nt (pt "4 thof 3::2::1::0:")))
;; (Inhab nat)
;; (pp (nt (pt "(3::2::1::0:)__1")))
;; 2
;; (pp (nt (pt "(3::2::1::0:)__4")))
;; (Inhab nat)

;; (pp (rename-variables (term-to-totality-formula (pt "(ListProj alpha)"))))
;; allnc n^(TotalNat n^ -> allnc xs^(TotalList xs^ -> Total(n^ thof xs^)))

;; ListProjTotal
(set-goal (term-to-totality-formula (pt "(ListProj alpha)")))
(assume "n^" "Tn")
(elim "Tn")
(assume "xs^" "Txs")
(elim "Txs")
(ng #t)
(use "InhabTotal")
(assume "x^" "Tx" "xs^1" "Txs1" "IH")
(ng #t)
(use "Tx")
(assume "n^1" "Tn1" "IHn1" "xs^1" "Txs1")
(elim "Txs1")
(ng #t)
(use "InhabTotal")
(assume "x^" "Tx" "xs^2" "Txs2" "IHxs2")
(ng #t)
(use "IHn1")
(use "Txs2")
;; Proof finished.
(save "ListProjTotal")

;; ListProjTotalSound
(set-goal (real-and-formula-to-mr-formula
	   (pt "(ListProj alpha)")
	   (proof-to-formula (theorem-name-to-proof "ListProjTotal"))))
(assume "n^" "n^0" "TMRn0n")
(elim "TMRn0n")
(assume "xs^" "xs^0" "TMRxs0xs")
(elim "TMRxs0xs")
(ng #t)
(use "InhabTotalMR")
(assume "x^" "x^0" "TMRx0x" "xs^1" "xs^10" "TMRxs10xs1" "IH")
(ng #t)
(use "TMRx0x")
(assume "n^1" "n^10" "TMRn10n1" "IHn1" "xs^1" "xs^10" "TMRxs10xs1")
(elim  "TMRxs10xs1")
(ng #t)
(use "InhabTotalMR")
(assume "x^" "x^0" "TMRx0x" "xs^2" "xs^20" "TMRx20x2" "IHxs2")
(ng #t)
(use "IHn1")
(use "TMRx20x2")
;; Proof finished.
(save "ListProjTotalReal")

(add-program-constant
 "ListFBar" (py "(nat=>alpha)=>nat=>list alpha") t-deg-zero)

(add-infix-display-string "ListFBar" "fbar" 'pair-op) ;right associative

(add-computation-rules
 "(nat=>alpha)fbar 0" "(Nil alpha)"
 "(nat=>alpha)fbar Succ n" "(nat=>alpha)0::([n1](nat=>alpha)(Succ n1))fbar n")

;; (pp (nt (pt "Succ fbar 4")))
;; 1::2::3::4:
;; (pp (nt (pt "([n]n+3)fbar 4")))
;; 3::4::5::6:

;; (pp (rename-variables (term-to-totality-formula (pt "(ListFBar alpha)"))))

;; allnc (nat=>alpha)^(
;;  allnc n^(TotalNat n^ -> Total((nat=>alpha)^ n^)) ->
;;  allnc n^(TotalNat n^ -> TotalList((nat=>alpha)^ fbar n^)))

;; ListFBarTotal
(set-goal (term-to-totality-formula (pt "(ListFBar alpha)")))
(assert "allnc n^(TotalNat n^ ->
  allnc (nat=>alpha)^(
  allnc n^(TotalNat n^ -> Total((nat=>alpha)^ n^)) ->
  TotalList((nat=>alpha)^ fbar n^)))")
 (assume "n^" "Tn")
 (elim "Tn")
 (assume "(nat=>alpha)^" "Tf")
 (ng #t)
 (use "TotalListNil")
 (assume "n^1" "Tn1" "IH")
 (assume "(nat=>alpha)^" "Tf")
 (ng #t)
 (use "TotalListCons")
 (use "Tf")
 (use "TotalNatZero")
 (use "IH")
 (assume "n^2" "Tn2")
 (use "Tf")
 (use "TotalNatSucc")
 (use "Tn2")
(assume "Assertion" "(nat=>alpha)^" "Tf"  "n^" "Tn")
(use "Assertion")
(use "Tn")
(use "Tf")
;; Proof finished.
(save "ListFBarTotal")

(set-goal "all n,(nat=>alpha)^ Lh((nat=>alpha)^ fbar n)=n")
(ind)
(assume "(nat=>alpha)^")
(ng #t)
(use "Truth")
(assume "n" "IHn")
(assume "(nat=>alpha)^")
(ng #t)
(use "IHn")
;; Proof finished.

(add-rewrite-rule "Lh((nat=>alpha)^ fbar n)" "n")

(add-program-constant "ListBar" (py "list alpha=>nat=>list alpha") t-deg-zero)

(add-infix-display-string "ListBar" "bar" 'add-op) ;left associative

(add-computation-rules
 "xs bar 0" "(Nil alpha)"
 "(Nil alpha)bar(Succ n)" "(Inhab alpha)::(Nil alpha) bar n"
 "(x::xs)bar Succ n" "x::xs bar n")

;; (pp (nt (pt "(0::1::2::3::4:)bar 2")))
;; 0::1:
;; (pp (nt (pt "(0::1::2::3::4:)bar 7")))
;; 0::1::2::3::4::(Inhab nat)::(Inhab nat):

;; (add-computation-rule "(Inhab nat)" "0")

;; (pp (nt (pt "(0::1::2::3::4:)bar 7")))
;; 0::1::2::3::4::0::0:

;; (pp (rename-variables (term-to-totality-formula (pt "(ListBar alpha)"))))
;; allnc xs^(TotalList xs^ -> allnc n^(TotalNat n^ -> TotalList(xs^ bar n^)))

;; ListBarTotal
(set-goal (term-to-totality-formula (pt "(ListBar alpha)")))
(assume "xs^" "Txs")
(elim "Txs")
(assume "n^" "Tn")
(elim "Tn")
(ng #t)
(use "TotalListNil")
(assume "n^0" "Tn0" "IHn0")
(ng #t)
(use "TotalListCons")
(use "InhabTotal")
(use "IHn0")
;; Step
(assume "x^" "Tx" "xs^1" "Txs1" "IH" "n^1" "Tn1")
(elim "Tn1")
(ng #t)
(use "TotalListNil")
(assume "n^2" "Tn2" "Useless")
(ng #t)
(use "TotalListCons")
(use "Tx")
(use "IH")
(use "Tn2")
;; Proof finished.
(save "ListBarTotal")

(set-goal "all xs,n Lh(xs bar n)=n")
(ind)
(ind)
(ng #t)
(use "Truth")
(assume "n" "IHn")
(ng #t)
(use "IHn")
(assume "x" "xs" "IHxs")
(cases)
(ng #t)
(use "Truth")
(assume "n")
(ng #t)
(use "IHxs")
;; Proof finished.

(add-rewrite-rule "Lh(xs bar n)" "n")

;; A list of length n+1 can be seen as the result of appending to its
;; initial segment of length n its final element.

;; BarAppdLast
(set-goal "all n,xs(Lh xs=Succ n -> (xs bar n)++(n thof xs):eqd xs)")
(ind)
;; Base
(cases)
(assume "Absurd")
(use "Efq")
(use "Absurd")
(assume "x" "xs" "Lh xs=0")
(ng #t)
(assert "xs eqd(Nil alpha)")
 (use "LhZeroImpNil")
 (use "Lh xs=0")
(assume "xs=Nil")
(simp "xs=Nil")
(use "InitEqD")
;; Step
(assume "n" "IHn")
(cases)
(assume "Absurd")
(use "Efq")
(use "Absurd")
(assume "x" "xs" "Lh xs=Succ n")
(ng #t)
(simp "IHn")
(use "InitEqD")
(use "Lh xs=Succ n")
;; Proof finished.
(save "BarAppdLast")

;; FBarAppdLast
(set-goal "all n,(nat=>alpha)(
       (nat=>alpha)fbar(Succ n) eqd
       ((nat=>alpha)fbar n)++((nat=>alpha)n):)")
(ind)
(assume "nat=>alpha")
(ng #t)
(use "InitEqD")
;; Step
(assume "n" "IHn" "nat=>alpha")
(assert "((nat=>alpha)fbar Succ(Succ n))eqd
         (nat=>alpha)0::([n](nat=>alpha)(Succ n))fbar Succ n")
 (ng #t)
 (use "InitEqD")
(assume "Equality")
(simp "Equality")
(simp "IHn")
(ng #t)
(use "InitEqD")
;; Proof finished.
(save "FBarAppdLast")

;; Now the relation between ListBar and ListFBar

;; ListBarFBar
(set-goal "all n,xs xs bar n eqd(([m]m thof xs)fbar n)")
(ind)
(assume "xs")
(ng #t)
(use "InitEqD")
(assume "n" "IHn")
(cases)
(ng #t)
(simp "IHn")
(ng #t)
(use "InitEqD")
(assume "x" "xs")
(ng #t)
(simp "IHn")
(use "InitEqD")
;; Proof finished.
(save "ListBarFBar")

(add-var-name "psi" (py "alpha1=>list alpha1=>alpha2"))
(add-var-name "y" (py "alpha1"))
(add-var-name "ys" (py "list alpha1"))
(add-var-name "z" (py "alpha2"))
(add-var-name "zs" (py "list alpha2"))

;; "ListIfTotal"
(set-goal "allnc ys^(TotalList ys^ ->
 allnc z^,psi^(Total z^ ->
 allnc y^,ys^(Total y^ -> TotalList ys^ -> Total(psi^ y^ ys^)) ->
 Total[if ys^ z^ psi^]))")
(assume "ys^" "Tys" "z^" "psi^" "Tz" "Tpsi")
(elim "Tys")
(use "Tz")
(assume "y^1" "Ty1" "ys^1" "Tys1" "Useless")
(ng #t)
(use "Tpsi")
(use "Ty1")
(use "Tys1")
;; Proof finished.
(save "ListIfTotal")

;; "ListIfSTotal"
(set-goal "allnc ys^(STotalList ys^ ->
 allnc z^,psi^(Total z^ ->
 allnc y^,ys^(STotalList ys^ -> Total(psi^ y^ ys^)) ->
 Total[if ys^ z^ psi^]))")
(assume "ys^" "STys" "z^" "psi^" "Tz" "STpsi")
(elim "STys")
(use "Tz")
(assume "y^1" "ys^1" "STys1" "Useless")
(ng #t)
(use "STpsi")
(use "STys1")
;; Proof finished.
(save "ListIfSTotal")

(add-program-constant
 "ListMap" (py "(alpha1=>alpha2)=>list alpha1=>list alpha2") t-deg-zero)

(add-infix-display-string "ListMap" "map" 'pair-op) ;right associative

(add-var-name "phi" (py "alpha1=>alpha2"))

(add-computation-rules
 "phi map(Nil alpha1)" "(Nil alpha2)"
 "phi map y::ys" "phi y::phi map ys")

;; (pp (nt (pt "Pred map 2::3::4:")))
;; 1::2::3:

;; (pp (rename-variables
;;      (term-to-totality-formula (pt "(ListMap alpha1 alpha2)"))))

;; allnc phi^(
;;  allnc y^(Total y^ -> Total(phi^ y^)) ->
;;  allnc ys^(TotalList ys^ -> TotalList(phi^ map ys^)))

;; ListMapTotal
(set-goal (term-to-totality-formula (pt "(ListMap alpha1 alpha2)")))
(assume "phi^" "Tphi" "ys^" "Tys")
(elim "Tys")
(ng #t)
(use "TotalListNil")
(assume "y^1" "Ty1" "ys^1" "Tys1" "IH")
(ng #t)
(use "TotalListCons")
(use "Tphi")
(use "Ty1")
(use "IH")
;; Proof finished.
(save "ListMapTotal")

;; (pp (rename-variables
;;      (term-to-stotality-formula (pt "(ListMap alpha1 alpha2)"))))

;; allnc phi^(
;;  allnc y^(Total y^ -> Total(phi^ y^)) ->
;;  allnc ys^(STotalList ys^ -> STotalList(phi^ map ys^)))

;; ListMapSTotal
(set-goal (term-to-stotality-formula (pt "(ListMap alpha1 alpha2)")))
(assume "phi^" "Tphi" "ys^" "STys")
(elim "STys")
(ng #t)
(use "STotalListNil")
(assume "y^1" "ys^1" "STys1" "IH")
(ng #t)
(use "STotalListCons")
(use "IH")
;; Proof finished.
(save "ListMapSTotal")

;; LhMap
(set-goal "all phi,ys Lh(phi map ys)=Lh ys")
(assume "phi")
(ind)
(use "Truth")
(assume "y" "ys" "IH")
(use "IH")
;; Proof finished.
(save "LhMap")

;; LhMapPartial
(set-goal "all phi^,ys^(STotalList ys^ -> Lh(phi^ map ys^)=Lh ys^)")
(assume "phi^" "ys^" "STys")
(elim "STys")
(ng #t)
(use "Truth")
(assume "y^" "ys^1" "STys1" "IH")
(ng #t)
(use "IH")
;; Proof finished.
(save "LhMapPartial")

;; MapAppend
(set-goal "all phi,ys2,ys1 (phi map ys1:+:ys2)eqd(phi map ys1):+:(phi map ys2)")
(assume "phi" "ys2")
(ind)
(ng)
(use "InitEqD")
(assume "y" "ys" "IH")
(ng)
(simp "IH")
(use "InitEqD")
;; Proof finished.
(save "MapAppend")

;; MapAppendPartial
(set-goal "all phi^,ys^2,ys^1(
       STotalList ys^1 ->
       (phi^ map ys^1:+:ys^2)eqd(phi^ map ys^1):+:(phi^ map ys^2))")
(assume "phi^" "ys^2" "ys^1" "STys1")
(elim "STys1")
(ng #t)
(use "InitEqD")
(assume "y^" "ys^" "STys" "IH")
(ng #t)
(simp "IH")
(use "InitEqD")
;; Proof finished.
(save "MapAppendPartial")

;; MapAppd
(set-goal "all phi,ys2,ys1 (phi map ys1++ys2)eqd(phi map ys1)++(phi map ys2)")
(assume "phi" "ys2")
(ind)
(ng)
(use "InitEqD")
(assume "y" "ys" "IH")
(ng)
(simp "IH")
(use "InitEqD")
;; Proof finished.
(save "MapAppd")

;; MapAppdPartial
(set-goal "all phi^,ys^2,ys^1(
       STotalList ys^1 ->
       (phi^ map ys^1++ys^2)eqd(phi^ map ys^1)++(phi^ map ys^2))")
(assume "phi^" "ys^2" "ys^1" "STys1")
(elim "STys1")
(ng #t)
(use "InitEqD")
(assume "y^" "ys^" "STys" "IH")
(ng #t)
(simp "IH")
(use "InitEqD")
;; Proof finished.
(save "MapAppdPartial")

;; ListProjMap
(set-goal "all phi^,ys,n(n<Lh ys -> (n thof phi^ map ys)eqd phi^(n thof ys))")
(assume "phi^")
(ind)
(assume "n" "Absurd")
(use "Efq")
(use "Absurd")
(assume "y" "ys" "IH")
(cases)
(assume "Trivial")
(ng)
(use "InitEqD")
(assume "n" "n<Lh ys")
(ng)
(use "IH")
(use "n<Lh ys")
;; Proof finished.
(save "ListProjMap")

;; MapFbar
(set-goal "all phi^,n,(nat=>alpha1)^(
       phi^ map (nat=>alpha1)^ fbar n)eqd
            (([n]phi^((nat=>alpha1)^ n))fbar n)")
(assume "phi^")
(ind)
(assume "(nat=>alpha1)^")
(ng #t)
(use "InitEqD")
(assume "n" "IHn" "(nat=>alpha1)^")
(ng #t)
(simp "IHn")
(ng #t)
(use "InitEqD")
;; Proof finished.
(save "MapFbar")

(add-rewrite-rule
 "phi^ map (nat=>alpha1)^ fbar n" "([n]phi^((nat=>alpha1)^ n))fbar n")

(add-program-constant
 "Consn" (py "alpha=>nat=>list alpha=>list alpha") t-deg-zero)

(add-computation-rules
 "(Consn alpha)x 0 xs" "x::xs"
 "(Consn alpha)x(Succ n)(Nil alpha)" "x::(Consn alpha)x n(Nil alpha)"
 "(Consn alpha)x(Succ n)(x1::xs)" "x1::(Consn alpha)x n(xs)")

;; (pp (nt (pt "(Consn nat)n 7(0::1::2:)")))
;; => 0::1::2::n::n::n::n::n:

;; (pp (rename-variables (term-to-totality-formula (pt "(Consn alpha)"))))

;; allnc x^(
;;  Total x^ ->
;;  allnc n^(
;;   TotalNat n^ ->
;;   allnc xs^(TotalList xs^ -> TotalList((Consn alpha)x^ n^ xs^))))

;; ConsnTotal
(set-goal (term-to-totality-formula (pt "(Consn alpha)")))
(assume "x^" "Tx" "n^" "Tn")
(elim "Tn")
;; Base
(assume "xs^" "Txs")
(elim "Txs")
(ng #t)
(use "TotalListCons")
(use "Tx")
(use "TotalListNil")
(assume "x^1" "Tx1" "xs^1" "Txs1" "Useless")
(ng #t)
(use "TotalListCons")
(use "Tx")
(use "TotalListCons")
(use "Tx1")
(use "Txs1")
;; Step
(assume "n^1" "Tn1" "IHn1" "xs^" "Txs")
(elim "Txs")
(ng #t)
(use "TotalListCons")
(use "Tx")
(use "IHn1")
(use "TotalListNil")
(assume "x^1" "Tx1" "xs^1" "Txs1" "Useless")
(ng #t)
(use "TotalListCons")
(use "Tx1")
(use "IHn1")
(use "Txs1")
;; Proof finished.
(save "ConsnTotal")

;; (pp (rename-variables (term-to-stotality-formula (pt "(Consn alpha)"))))

;; allnc x^(
;;  Total x^ ->
;;  allnc n^(
;;   TotalNat n^ ->
;;   allnc xs^(STotalList xs^ -> STotalList((Consn alpha)x^ n^ xs^))))

;; ConsnSTotal
(set-goal (term-to-stotality-formula (pt "(Consn alpha)")))
(assume "x^" "Tx" "n^" "Tn")
(elim "Tn")
;; Base
(assume "xs^" "Txs")
(elim "Txs")
(ng #t)
(use "STotalListCons")
(use "STotalListNil")
(assume "x^1" "xs^1" "Txs1" "Useless")
(ng #t)
(use "STotalListCons")
(use "STotalListCons")
(use "Txs1")
;; Step
(assume "n^1" "Tn1" "IHn1" "xs^" "STxs")
(elim "STxs")
(ng #t)
(use "STotalListCons")
(use "IHn1")
(use "STotalListNil")
(assume "x^1" "xs^1" "STxs1" "Useless")
(ng #t)
(use "STotalListCons")
(use "IHn1")
(use "STxs1")
;; Proof finished.
(save "ConsnSTotal")

;; LhConsn
(set-goal "all x^1,xs^(
        STotalList xs^ ->
        all n(
         Lh xs^ <=n ->
         Lh(xs^ :+:(Consn alpha)x^1(n--Lh xs^)(Nil alpha))=Succ n))")
(assume "x^1" "xs^" "STxs")
(elim "STxs")
(ind)
(assume "Useless")
(ng #t)
(use  "Truth")
(assume "n" "IHn" "Useless")
(ng #t)
(use "IHn")
(use "Truth")
(assume "x^2" "xs^1" "STxs1" "IHl")
(cases)
(assume "Absurd")
(use "Efq")
(use "Absurd")
(assume "n" "Lh xs^1 <=n")
(ng #t)
(assert "all n1,n^2(TotalNat n^2 -> Pred(Succ n1--n^2)=n1--n^2)")
 (assume "n1")
 (use-with (make-proof-in-aconst-form all-allpartial-aconst)
	   (py "nat")
	   (make-cterm (pv "n^2") (pf "Pred(Succ n1--n^2)=n1--n^2"))
	   "?")
 (assume "n2")
 (ng #t)
 (use "Truth")
(assume "H")
(simp "H")
(use "IHl")
(use "Lh xs^1 <=n")
(use "ListLengthSTotal")
(use "STxs1")
;; Proof finished.
(save "LhConsn")

;; LhConsnAppd
(set-goal "all x^1,xs^(
        STotalList xs^ ->
        all n(
         Lh xs^ <=n ->
         Lh(xs^ ++(Consn alpha)x^1(n--Lh xs^)(Nil alpha))=Succ n))")
(assume "x^1" "xs^" "STxs")
(elim "STxs")
(ind)
(assume "Useless")
(ng #t)
(use "Truth")
(assume "n" "IHn" "Useless")
(use "IHn")
(ng #t)
(use "Truth")
(assume "x^2" "xs^2" "STxs2" "IHl")
(cases)
(assume "Absurd")
(use "Efq")
(use "Absurd")
(assume "n" "Lh xs^ <=n")
(ng #t)
(assert "all n1,n^2(TotalNat n^2 -> Pred(Succ n1--n^2)=n1--n^2)")
 (assume "n1")
 (use-with (make-proof-in-aconst-form all-allpartial-aconst)
	   (py "nat")
	   (make-cterm (pv "n^2") (pf "Pred(Succ n1--n^2)=n1--n^2"))
	   "?")
 (assume "n2")
 (ng #t)
 (use "Truth")
(assume "H")
(simp "H")
(use "IHl")
(use "Lh xs^ <=n")
(use "ListLengthSTotal")
(use "STxs2")
;; Proof finished.
(save "LhConsnAppd")

;; We add a bounded universal quantifier.  AllBList n P means that for
;; all lists of length n of booleans the property P holds.

(add-program-constant
 "AllBList" (py "nat=>(list boole=>boole)=>boole") t-deg-zero)

(add-computation-rules
 "AllBList 0 list boole=>boole" "(list boole=>boole)(Nil boole)"

 "AllBList(Succ n)list boole=>boole"

 "(AllBList n([list boole]list boole=>boole(True::list boole)))andb
  (AllBList n([list boole]list boole=>boole(False::list boole)))")

;; (pp (rename-variables (term-to-totality-formula (pt "AllBList"))))

;; allnc n^(
;;  TotalNat n^ ->
;;  allnc (list boole=>boole)^(
;;   allnc (list boole)^0(
;;    TotalList(list boole)^0 ->
;;    TotalBoole((list boole=>boole)^(list boole)^0)) ->
;;   TotalBoole(AllBList n^(list boole=>boole)^)))

;; AllBListTotal
(set-goal (term-to-totality-formula (pt "AllBList")))
(assume "nat^" "Tnat")
(elim "Tnat")
;; Base
(assume "(list boole=>boole)^" "Hyp")
(ng #t)
(use "Hyp")
(use "TotalListNil")
;; Step
(assume "n^" "Tn" "IHn" "(list boole=>boole)^" "TLBToB")
(ng #t)
(use "AndConstTotal")
(use "IHn")
(ng #t)
(assume "(list boole)^" "TLB")
(use "TLBToB")
(use "TotalListCons")
(use "TotalBooleTrue")
(use "TLB")
(use "IHn")
(ng #t)
(assume "(list boole)^" "TLB")
(use "TLBToB")
(use "TotalListCons")
(use "TotalBooleFalse")
(use "TLB")
;; Proof finished.
(save "AllBListTotal")

;; ListLhZero
(set-goal "all xs^(STotalList xs^ -> Lh xs^ =0 -> xs^ eqd(Nil alpha))")
(assume "xs^" "STxs")
(elim "STxs")
(assume "Useless")
(use "InitEqD")
(assume "x^" "xs^1" "STxs1" "IH" "Absurd")
(use "Efq")
(use "Absurd")
;; Proof finished.
(save "ListLhZero")

;; AllBListIntro
(set-goal "all n,(list boole=>boole)^(
        all (list boole)^(
         Lh(list boole)^ =n -> (list boole=>boole)^(list boole)^) ->
        AllBList n(list boole=>boole)^)")
(ind)
;; Base
(assume "(list boole=>boole)^" "Hyp")
(ng #t)
(use "Hyp")
(ng #t)
(use "Truth")
;; Step
(assume "n" "IH" "(list boole=>boole)^" "Hyp")
(ng #t)
(split)
(use "IH")
(assume "(list boole)^" "Lhn")
(ng #t)
(use "Hyp")
(ng #t)
(use "Lhn")
(use "IH")
(assume "(list boole)^" "Lhn")
(ng #t)
(use "Hyp")
(ng #t)
(use "Lhn")
;; Proof finished.
(save "AllBListIntro")

;; AllBListElim
(set-goal "all n,(list boole=>boole)(
        AllBList n(list boole=>boole) ->
        all (list boole)(
         Lh(list boole)=n -> (list boole=>boole)(list boole)))")
(ind)
;; Base
(assume "list boole=>boole" "H1")
(cases)
(assume "Useless")
(use "H1")
(assume "boole" "list boole" "Absurd")
(use "Efq")
(use "Absurd")
;; Step
(assume "n" "IH" "list boole=>boole" "H1")
(cases)
(assume "Absurd")
(use "Efq")
(use "Absurd")
(cases)
(assume "list boole" "Lhn")
(use-with "IH" (pt "[list boole1]list boole=>boole(True::list boole1)")
	  "?" (pt "list boole") "?")
(ng "H1")
(use "H1")
(use "Lhn")
(assume "list boole" "Lhn")
(use-with "IH" (pt "[list boole1]list boole=>boole(False::list boole1)")
	  "?" (pt "list boole") "?")
(ng "H1")
(use "H1")
(use "Lhn")
;; Proof finished.
(save "AllBListElim")

;; ListNatEqToEqD
(set-goal "all (list nat)_1,(list nat)_2(
  (list nat)_1=(list nat)_2 -> (list nat)_1 eqd (list nat)_2)")
(ind)
(cases)
(assume "Useless")
(use "InitEqD")
(assume "nat1" "(list nat)_1" "Nil=n::ns")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "Nil=n::ns")
(assume "nat1" "(list nat)_1" "IH")
(cases)
(assume "n::ns=Nil")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "n::ns=Nil")
(assume "nat2" "(list nat)_2" "n::ns=m::ms")
(ng "n::ns=m::ms")
(assert "(list nat)_1=(list nat)_2")
 (use "n::ns=m::ms")
(assume "ns=ms")
(assert "nat1=nat2")
 (use "n::ns=m::ms")
(assume "n=m")
(drop "n::ns=m::ms")
(assert "(list nat)_1 eqd (list nat)_2")
 (use "IH")
 (use "ns=ms")
(assume "ns eqd ms")
(assert "nat1 eqd nat2")
 (use "NatEqToEqD")
 (use "n=m")
(assume "n eqd m")
(elim "ns eqd ms")
(assume "(list nat)^1")
(elim "n eqd m")
(assume "nat^")
(use "InitEqD")
;; Proof finished.
(save "ListNatEqToEqD")

;; ListNatEqTotal
(set-goal "allnc (list nat)^1(
 TotalList (list nat)^1 -> allnc (list nat)^2(TotalList (list nat)^2 ->
 TotalBoole((list nat)^1 =(list nat)^2)))")
(assume "(list nat)^1" "Tns1")
(elim "Tns1")
(assume "(list nat)^2" "Tns2")
(elim "Tns2")
(use "TotalBooleTrue")
(strip)
(use "TotalBooleFalse")
(assume "nat^3" "Tn3" "(list nat)^3" "Tns3" "IHns3" "(list nat)^4" "Tns4")
(elim "Tns4")
(use "TotalBooleFalse")
(assume "nat^5" "Tn5" "(list nat)^5" "Tns5" "Useless")
(ng #t)
(use "AndConstTotal")
(use "NatEqTotal")
(use "Tn3")
(use "Tn5")
(use "IHns3")
(use "Tns5")
;; Proof finished.
(save "ListNatEqTotal")

;; ListBooleEqToEqD
(set-goal "all (list boole)_1,(list boole)_2(
  (list boole)_1=(list boole)_2 -> (list boole)_1 eqd (list boole)_2)")
(ind)
(cases)
(assume "Useless")
(use "InitEqD")
(assume "boole1" "(list boole)_1" "Nil=p::ps")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "Nil=p::ps")
(assume "boole1" "(list boole)_1" "IH")
(cases)
(assume "p::ps=Nil")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "p::ps=Nil")
(assume "boole2" "(list boole)_2" "p::ps=q::qs")
(ng "p::ps=q::qs")
(assert "(list boole)_1=(list boole)_2")
 (use "p::ps=q::qs")
(assume "ps=qs")
(assert "boole1=boole2")
 (use "p::ps=q::qs")
(assume "p=q")
(drop "p::ps=q::qs")
(assert "(list boole)_1 eqd (list boole)_2")
 (use "IH")
 (use "ps=qs")
(assume "ps eqd qs")
(assert "boole1 eqd boole2")
 (use "BooleEqToEqD")
 (use "p=q")
(assume "p eqd q")
(elim "ps eqd qs")
(assume "(list boole)^1")
(elim "p eqd q")
(assume "boole^")
(use "InitEqD")
;; Proof finished.
(save "ListBooleEqToEqD")

;; ListBooleEqTotal
(set-goal "allnc (list boole)^1(
 TotalList (list boole)^1 -> allnc (list boole)^2(TotalList (list boole)^2 ->
 TotalBoole((list boole)^1 =(list boole)^2)))")
(assume "(list boole)^1" "Tps1")
(elim "Tps1")
(assume "(list boole)^2" "Tps2")
(elim "Tps2")
(use "TotalBooleTrue")
(strip)
(use "TotalBooleFalse")
(assume "boole^3" "Tp3" "(list boole)^3" "Tps3" "IHps3" "(list boole)^4" "Tps4")
(elim "Tps4")
(use "TotalBooleFalse")
(assume "boole^5" "Tp5" "(list boole)^5" "Tps5" "Useless")
(ng #t)
(use "AndConstTotal")
(use "BooleEqTotal")
(use "Tp3")
(use "Tp5")
(use "IHps3")
(use "Tps5")
;; Proof finished.
(save "ListBooleEqTotal")

(remove-var-name "x" "xs" "phi" "psi" "y" "ys" "z" "zs")
