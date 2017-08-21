;; 2017-08-21

;; (load "~/git/minlog/init.scm")
;; (set! COMMENT-FLAG #f)
;; (libload "nat.scm")
;; (set! COMMENT-FLAG #t)

(if (not (assoc "nat" ALGEBRAS))
    (myerror "First execute (libload \"nat.scm\")"))

(display "loading list.scm ...") (newline)

(add-rtotalnc "yprod")

(add-algs "list" 'prefix-typeop
	  '("list" "Nil")
	  '("alpha=>list=>list" "Cons"))
(add-totality "list")
(add-rtotality "list")
(add-totalnc "list")
(add-rtotalnc "list")
(add-co "TotalList")
(add-co "TotalListNc")

(add-eqp "list")
(add-eqpnc "list")
(add-co "EqPList")
;; (pp "CoEqPListClause")
(add-co "EqPListNc")

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

;; RTotalListMon
(set-goal "allnc x^((Pvar alpha)_1 x^ -> (Pvar alpha)_2 x^) ->
 allnc xs^((RTotalList (cterm (x^) (Pvar alpha)_1 x^))xs^ ->
           (RTotalList (cterm (x^) (Pvar alpha)_2 x^))xs^)")
(assume "MonHyp" "xs^")
(elim)
(intro 0)
(assume "x^" "Yx" "xs^1" "RTYxs1" "RTZxs1")
(intro 1)
(use "MonHyp")
(use "Yx")
(use "RTZxs1")
;; Proof finished.
(save "RTotalListMon")

;; RTotalListToTotalList
(set-goal "allnc xs^((RTotalList (cterm (x^) Total x^)) xs^ -> TotalList xs^)")
(assume "xs^" "RTxs")
(elim "RTxs")
(use "TotalListNil")
(assume "x^" "Tx" "xs^1" "Txs1" "IH")
(use "TotalListCons")
(use "Tx")
(use "IH")
;; Proof finished.
(save "RTotalListToTotalList")

;; TotalListToRTotalList
(set-goal "allnc xs^(TotalList xs^ -> (RTotalList (cterm (x^) Total x^)) xs^)")
(assume "xs^" "Txs")
(elim "Txs")
(use "RTotalListNil")
(assume "x^" "Tx" "xs^1" "Txs1" "IH")
(use "RTotalListCons")
(use "Tx")
(use "IH")
;; Proof finished.
(save "TotalListToRTotalList")

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

;; ListSTotalVar
(set-goal "all xs STotalList xs")
(use "AllTotalIntro")
(assume "xs^" "Txs")
(elim "Txs")
(use "STotalListNil")
(assume "x^" "Tx" "xs^0" "Txs0" "STxs0")
(use "STotalListCons")
(use "STxs0")
;; Proof finished.
(save "ListSTotalVar")

(add-program-constant
 "ListAppend" (py "list alpha=>list alpha=>list alpha") t-deg-zero 'const 1)

(add-infix-display-string "ListAppend" ":+:" 'mul-op)

(add-computation-rules
 "(ListAppend alpha)(Nil alpha)" "[xs]xs"
 "(ListAppend alpha)(x::xs1)" "[xs2](x::xs1:+:xs2)")

(set-totality-goal "ListAppend")
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
(save-totality)

;; 2017-04-01.  Code preliminarily discarded.
;; ;; ListAppendTotalReal
;; (set-goal (real-and-formula-to-mr-formula
;; 	   (pt "(ListAppend alpha)")
;; 	   (proof-to-formula (theorem-name-to-proof "ListAppendTotal"))))
;; (assume "xs^1" "xs^10" "TMRxs10xs1" "xs^2" "xs^20" "TMRxs20xs2")
;; (elim "TMRxs10xs1")
;; (use "TMRxs20xs2")
;; (assume "x^" "x^0" "TMRx0x" "xs^" "xs^0" "TMRxs0xs" "IH")
;; (ng #t)
;; (use "TotalListConsMR")
;; (use "TMRx0x")
;; (use "IH")
;; ;; Proof finished.
;; (save "ListAppendTotalReal")

;; (pp (rename-variables (term-to-stotality-formula (pt "(ListAppend alpha)"))))

;; allnc xs^(
;;  STotalList xs^ -> allnc xs^0(STotalList xs^0 -> STotalList(xs^ :+:xs^0)))

;; ListAppendSTotal
(set-goal
 (rename-variables (term-to-stotality-formula (pt "(ListAppend alpha)"))))
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

;; ListAppendSTotalReal
(set-goal (rename-variables
	   (real-and-formula-to-mr-formula
	    (nt (proof-to-extracted-term "ListAppendSTotal"))
	    (proof-to-formula (theorem-name-to-proof "ListAppendSTotal")))))
(assume "xs^1" "n^1" "STMRn1xs1" "xs^2" "n^2" "TMRn2xs2")
(elim "STMRn1xs1")
(use "TMRn2xs2")
(assume "x^" "xs^" "n^" "STMRnxs" "IH")
(ng #t)
(use "STotalListConsMR")
(use "IH")
;; Proof finished.
(save "ListAppendSTotalReal")

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

;; We also provide a variant ListAppd of ListAppend (with display ++),
;; which allows rewrite rules with two arguments.

(add-program-constant
 "ListAppd" (py "list alpha=>list alpha=>list alpha") t-deg-zero)

(add-infix-display-string "ListAppd" "++" 'mul-op)

(add-computation-rules
 "(Nil alpha)++xs2" "xs2"
 "(x1::xs1)++xs2" "x1::xs1++xs2")

(set-totality-goal "ListAppd")
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
(save-totality)

;; (pp (rename-variables (term-to-stotality-formula (pt "(ListAppd alpha)"))))

;; allnc xs^(
;;  STotalList xs^ -> allnc xs^0(STotalList xs^0 -> STotalList(xs^ ++xs^0)))

;; 2017-04-01.  Code preliminarily discarded.
;; ;; ListAppdTotalSound
;; (set-goal (rename-variables
;; 	   (real-and-formula-to-mr-formula
;; 	    (pt "(ListAppd alpha)")
;; 	    (proof-to-formula (theorem-name-to-proof "ListAppdTotal")))))
;; (assume "xs^1" "xs^10" "TMRxs10xs1" "xs^2" "xs^20" "TMRxs20xs2")
;; (elim "TMRxs10xs1")
;; (use "TMRxs20xs2")
;; (assume "x^" "x^0" "TMRx0x" "xs^" "xs^0" "TMRxs0xs" "IH")
;; (ng #t)
;; (use "TotalListConsMR")
;; (use "TMRx0x")
;; (use "IH")
;; ;; Proof finished.
;; (save "ListAppdTotalSound")

;; ListAppdSTotal
(set-goal (rename-variables
	   (term-to-stotality-formula (pt "(ListAppd alpha)"))))
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
(set-goal (rename-variables
	   (real-and-formula-to-mr-formula
	    (nt (proof-to-extracted-term "ListAppdSTotal"))
	    (proof-to-formula (theorem-name-to-proof "ListAppdSTotal")))))
(assume "xs^1" "n^1" "STMRn1xs1" "xs^2" "n^2" "TMRn2xs2")
(elim "STMRn1xs1")
(use "TMRn2xs2")
(assume "x^" "xs^" "n^" "STMRnxs" "IH")
(ng #t)
(use "STotalListConsMR")
(use "IH")
;; Proof finished.
(save "ListAppdSTotalSound")

;; x: ++xs converts into x::xs.  However, xs1++x2: ++xs2 does not rewrite,
;; because ++ associates to the left.  But we can add the corresponding
;; rule:

(set-goal "all xs1,x^2,xs^2 xs1++x^2: ++xs^2 eqd xs1++(x^2::xs^2)")
(ind)
(assume "x^2" "xs^2")
(use "InitEqD")
(assume "x" "xs1" "IHxs1" "x^2" "xs^2")
(ng)
(simp "IHxs1")
(use "InitEqD")
;; Proof finished.
(add-rewrite-rule "xs1++x^2: ++xs^2" "xs1++(x^2::xs^2)")

;; In the other direction this rule would lead to non-termination, if
;; we also had associativity as a rewrite rule.  x2: is x2::(Nil par),
;; and this again is a redex for associativity.

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

;; ListAppdAssocPartial
(set-goal "all xs^1(STotalList xs^1 ->
  all xs^2,xs^3 xs^1++(xs^2++xs^3)eqd xs^1++xs^2++xs^3)")
(assume "xs^1" "STxs1")
(elim "STxs1")
(assume "xs^2" "xs^3")
(use "InitEqD")
(assume "x^" "xs^" "STxs" "IH")
(ng #t)
(assume "xs^2" "xs^3")
(simp "IH")
(use "InitEqD")
;; Proof finished.
(save "ListAppdAssocPartial")

;; We could add associativity as a rewrite rule by executing
;; (add-rewrite-rule "xs1++(xs2++xs3)" "xs1++xs2++xs3")

;; However, this will block other rewriting rules in long appends.
;; Example: consider (pt "s++(L::t++R:)") and (pt "s++(L::t)++R:").
;; Both are normal, since rewriting (pt "(L::t)++R:") into (pt
;; "L::t++R:") is blocked by the leading s++ and the fact that ++
;; associates to the left.

(add-program-constant "ListLength" (py "list alpha=>nat") t-deg-zero)
(add-prefix-display-string "ListLength" "Lh")

(add-computation-rules
 "Lh(Nil alpha)" "Zero"
 "Lh(x::xs)" "Succ Lh xs")

(set-totality-goal "ListLength")
(assume "xs^" "Txs")
(elim "Txs")
(ng #t)
(use "TotalNatZero")
(assume "x^" "Tx" "xs^1" "Txs1" "IH")
(ng #t)
(use "TotalNatSucc")
(use "IH")
;; Proof finished.
(save-totality)

;; 2017-04-01.  Code preliminarily discarded.
;; ;; ListLengthTotalSound
;; (set-goal (rename-variables
;; 	   (real-and-formula-to-mr-formula
;; 	    (pt "(ListLength alpha)")
;; 	    (proof-to-formula (theorem-name-to-proof "ListLengthTotal")))))
;; (assume "xs^1" "xs^10" "TMRxs10xs1")
;; (elim "TMRxs10xs1")
;; (use "TotalNatZeroMR")
;; (assume "x^" "x^0" "TMRx0x" "xs^" "xs^0" "TMRxs0xs" "IH")
;; (ng #t)
;; (use "TotalNatSuccMR")
;; (use "IH")
;; ;; Proof finished.
;; (save "ListLengthTotalSound")

;; ListLengthSTotal
(set-goal (rename-variables
	   (term-to-stotality-formula (pt "(ListLength alpha)"))))
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

;; 2017-04-01.  Code preliminarily discarded.
;; ;; ListLengthSTotalSound
;; (set-goal (rename-variables
;; 	   (real-and-formula-to-mr-formula
;; 	    (proof-to-extracted-term "ListLengthSTotal")
;; 	    (proof-to-formula (theorem-name-to-proof "ListLengthSTotal")))))
;; (assume "xs^1" "n^1" "STMRn1xs1")
;; (elim "STMRn1xs1")
;; (ng #t)
;; (use "TotalNatZeroMR")
;; (assume "x^" "xs^" "n^" "STMRnxs" "IH")
;; (ng #t)
;; (use "TotalNatSuccMR")
;; (use "IH")
;; ;; Proof finished.
;; (save "ListLengthSTotalSound")

;; LhZeroToEqNil
(set-goal "all xs(Lh xs=0 -> xs eqd(Nil alpha))")
(cases)
(assume "Useless")
(use "InitEqD")
(assume "x" "xs" "Absurd")
(use "Efq")
(use "Absurd")
;; Proof finished.
(save "LhZeroToEqNil")

;; LhZeroToEqNilPartial
(set-goal "all xs^(STotalList xs^ -> Lh xs^ =0 -> xs^ eqd(Nil alpha))")
(assume "xs^" "STxs")
(elim "STxs")
(assume "Useless")
(use "InitEqD")
(assume "x^" "xs^1" "STxs1" "IH" "Absurd")
(use "Efq")
(use "Absurd")
;; Proof finished.
(save "LhZeroToEqNilPartial")

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

(set-totality-goal "ListProj")
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
(save-totality)

;; 2017-04-01.  Code preliminarily discarded.
;; ;; ListProjTotalSound
;; (set-goal (rename-variables
;; 	   (real-and-formula-to-mr-formula
;; 	    (pt "(ListProj alpha)")
;; 	    (proof-to-formula (theorem-name-to-proof "ListProjTotal")))))
;; (assume "n^" "n^0" "TMRn0n")
;; (elim "TMRn0n")
;; (assume "xs^" "xs^0" "TMRxs0xs")
;; (elim "TMRxs0xs")
;; (ng #t)
;; (use "InhabTotalMR")
;; (assume "x^" "x^0" "TMRx0x" "xs^1" "xs^10" "TMRxs10xs1" "IH")
;; (ng #t)
;; (use "TMRx0x")
;; (assume "n^1" "n^10" "TMRn10n1" "IHn1" "xs^1" "xs^10" "TMRxs10xs1")
;; (elim  "TMRxs10xs1")
;; (ng #t)
;; (use "InhabTotalMR")
;; (assume "x^" "x^0" "TMRx0x" "xs^2" "xs^20" "TMRx20x2" "IHxs2")
;; (ng #t)
;; (use "IHn1")
;; (use "TMRx20x2")
;; ;; Proof finished.
;; (save "ListProjTotalSound")

;; ListProjAppdLeft
(set-goal "all xs1,n,xs2(n<Lh xs1 -> (n thof(xs1++xs2))eqd(n thof xs1))")
(ind)
(assume "n" "xs2" "Absurd")
(use "Efq")
(use "Absurd")
(assume "x1" "xs1" "IHxs1")
(ng)
(cases)
(ng)
(strip)
(use "InitEqD")
(ng)
(use "IHxs1")
;; Proof finished.
(save "ListProjAppdLeft")

;; ListProjAppdRight
(set-goal "all xs1,xs2,n(n<Lh xs2 -> (Lh xs1+n thof(xs1++xs2))eqd(n thof xs2))")
(ind)
(ng)
(strip)
(use "InitEqD")
(assume "x1" "xs1" "IHxs1")
(ng)
(use "IHxs1")
;; Proof finished.
(save "ListProjAppdRight")

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

(set-totality-goal "ListFBar")
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
(save-totality)

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

(set-totality-goal "ListBar")
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
(save-totality)

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
 (use "LhZeroToEqNil")
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
(set-goal "all n,(nat=>alpha)^(
       (nat=>alpha)^ fbar(Succ n)eqd
       ((nat=>alpha)^ fbar n)++((nat=>alpha)^ n):)")
(ind)
(assume "(nat=>alpha)^")
(ng #t)
(use "InitEqD")
;; Step
(assume "n" "IHn" "(nat=>alpha)^")
(assert "((nat=>alpha)^ fbar Succ(Succ n))eqd
         (nat=>alpha)^ 0::([n](nat=>alpha)^ (Succ n))fbar Succ n")
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

;; ListBarFBarPlus
(set-goal "all n,m,(nat=>alpha)^(
     ((nat=>alpha)^ fbar(n+m))bar n eqd((nat=>alpha)^ fbar n))")
(ind)
(assume "m" "(nat=>alpha)^")
(ng)
(use "InitEqD")
(assume "n" "IH"  "m" "(nat=>alpha)^")
(ng #t)
(simp "IH")
(use "InitEqD")
;; Proof finished.
(save "ListBarFBarPlus")

;; ListProjFBarSucc
(set-goal
 "all n,(nat=>alpha)^ (n thof(nat=>alpha)^ fbar Succ n)eqd(nat=>alpha)^ n")
(ind)
(assume "(nat=>alpha)^")
(ng)
(use "InitEqD")
(assume "n" "IH" "(nat=>alpha)^")
(inst-with-to "IH" (pt "[n0](nat=>alpha)^(Succ n0)") "IHInst")
(ng)
(use "IHInst")
;; Proof finished.
(save "ListProjFBarSucc")

(add-var-name "psi" (py "alpha1=>list alpha1=>alpha2"))
(add-var-name "y" (py "alpha1"))
(add-var-name "ys" (py "list alpha1"))
(add-var-name "z" (py "alpha2"))
(add-var-name "zs" (py "list alpha2"))

;; ListIfTotal
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

;; ListIfSTotal
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

(set-totality-goal "ListMap")
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
(save-totality)

;; (pp (rename-variables
;;      (term-to-stotality-formula (pt "(ListMap alpha1 alpha2)"))))

;; allnc phi^(
;;  allnc y^(Total y^ -> Total(phi^ y^)) ->
;;  allnc ys^(STotalList ys^ -> STotalList(phi^ map ys^)))

;; ListMapSTotal
(set-goal (rename-variables
	   (term-to-stotality-formula (pt "(ListMap alpha1 alpha2)"))))
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

(set-totality-goal "Consn")
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
(save-totality)

;; (pp (rename-variables (term-to-stotality-formula (pt "(Consn alpha)"))))

;; allnc x^(
;;  Total x^ ->
;;  allnc n^(
;;   TotalNat n^ ->
;;   allnc xs^(STotalList xs^ -> STotalList((Consn alpha)x^ n^ xs^))))

;; ConsnSTotal
(set-goal (rename-variables (term-to-stotality-formula (pt "(Consn alpha)"))))
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
 (use-with (make-proof-in-aconst-form alltotal-elim-aconst)
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
 (use-with (make-proof-in-aconst-form alltotal-elim-aconst)
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

(set-totality-goal "AllBList")
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
(save-totality)

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
(use "EfqEqD")
(use "Nil=n::ns")
(assume "nat1" "(list nat)_1" "IH")
(cases)
(assume "n::ns=Nil")
(use "EfqEqD")
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
(use "EfqEqD")
(use "Nil=p::ps")
(assume "boole1" "(list boole)_1" "IH")
(cases)
(assume "p::ps=Nil")
(use "EfqEqD")
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

(add-program-constant "ListRev" (py "list alpha=>list alpha") t-deg-zero)
(add-prefix-display-string "ListRev" "Rev")
(add-computation-rules
 "Rev(Nil alpha)" "(Nil alpha)"
 "Rev(x::xs)" "Rev xs++x:")

(set-totality-goal "ListRev")
(use "AllTotalElim")
(ind)
(use "TotalListNil")
(assume "x" "xs" "IH")
(ng #t)
(use "ListAppdTotal")
(use "IH")
(use "ListTotalVar")
;; Proof finished.
(save-totality)

;; ListRevSTotal
(set-goal (rename-variables (term-to-stotality-formula (pt "(ListRev alpha)"))))
(assume "xs^" "STxs")
(elim "STxs")
(use "STotalListNil")
(assume "x^1" "xs^1" "STxs1" "IH")
(ng #t)
(use "ListAppdSTotal")
(use "IH")
(use "STotalListCons")
(use "STotalListNil")
;; Proof finished.
(save "ListRevSTotal")

;; ListLengthRev
(set-goal "all xs Lh Rev xs eqd Lh xs")
(ind)
(use "InitEqD")
(assume "x" "xs" "IH")
(ng)
(simp "IH")
(use "InitEqD")
;; Proof finished.
(save "ListLengthRev")

;; ListRevAppd
(set-goal "all xs1,xs2 Rev(xs1++xs2)eqd Rev xs2++Rev xs1")
(ind)
(ng #t)
(strip)
(use "InitEqD")
(assume "x" "xs" "IH")
(ng #t)
(assume "xs2")
(simp "IH")
(simp "ListAppdAssoc")
(use "InitEqD")
;; Proof finished.
(save "ListRevAppd")

;; ListRevAppdPartial
(set-goal "all xs^1(STotalList xs^1 -> all xs^2(STotalList xs^2 ->
                   Rev(xs^1 ++xs^2)eqd Rev xs^2 ++Rev xs^1))")
(assume "xs^1" "STxs1")
(elim "STxs1")
(ng #t)
(assume "xs^2" "STxs2")
(simp "ListAppdNilPartial")
(use "InitEqD")
(use "ListRevSTotal")
(use "STxs2")
(assume "x^" "xs^" "STxs" "IH")
(ng #t)
(assume "xs^2" "STxs2")
(simp "IH")
(simp "ListAppdAssocPartial")
(use "InitEqD")
(use "ListRevSTotal")
(use "STxs2")
(use "STxs2")
;; Proof finished.
(save "ListRevAppdPartial")

;; ListRevInvol
(set-goal "all xs Rev(Rev xs)eqd xs")
(ind)
(use "InitEqD")
(assume "x" "xs" "IH")
(ng #t)
(simp "ListRevAppd")
(simp "IH")
(ng #t)
(use "InitEqD")
;; Proof finished.
(save "ListRevInvol")

;; ListRevInvolPartial
(set-goal "all xs^(STotalList xs^ -> Rev(Rev xs^)eqd xs^)")
(assume "xs^" "STxs")
(elim "STxs")
(ng #t)
(use "InitEqD")
(assume "x^1" "xs^1" "STxs1" "IH")
(ng #t)
(simp "ListRevAppdPartial")
(simp "IH")
(ng #t)
(use "InitEqD")
(use "STotalListCons")
(use "STotalListNil")
(use "ListRevSTotal")
(use "STxs1")
;; Proof finished.
(save "ListRevInvolPartial")

;; ListProjRev
(set-goal "all xs,n(n<Lh xs -> (n thof Rev xs)eqd(Pred(Lh xs--n)thof xs))")
(assert "all xs,n(n<Lh xs -> (n thof xs)eqd(Pred(Lh xs--n)thof Rev xs))")
 (ind)
 (ng)
 (assume "n" "Absurd")
 (use "InitEqD")
 (assume "x" "xs" "IH")
 (ng #t)
 (cases)
 (ng #t)
 (assume "Useless")
 (assert "Lh xs eqd Lh Rev xs+0")
  (simp "ListLengthRev")
  (use "InitEqD")
 (assume "EqHyp")
 (simp "EqHyp")
 (simp "ListProjAppdRight")
 (use "InitEqD")
 (use "Truth")
;; Case Succ n
 (ng #t)
 (assume "n" "n<Lh xs")
 (simp "ListProjAppdLeft")
 (use "IH")
 (use "n<Lh xs")
;; ?_22:Pred(Lh xs--n)<Lh Rev xs
 (simp "ListLengthRev")
 (cases (pt "Lh xs"))
 (assume "Lh xs=0")
 (simphyp-with-to "n<Lh xs" "Lh xs=0" "Absurd")
 (use "Efq")
 (use "Absurd")
 (assume "n0" "Lh xs=Sn0")
 (ng #t)
 (use "NatLeLtTrans" (pt "n0"))
 (use "Truth")
 (use "Truth")
(assume "ListProjRevAux" "xs" "n" "n<Lh xs")
(inst-with-to "ListProjRevAux" (pt "Rev xs") (pt "n") "Aux")
(assert "Rev Rev xs eqd xs")
 (use "ListRevInvol")
(assume "Assertion")
(simphyp-with-to "Aux" "Assertion" "SimpAux")
(assert "Lh Rev xs eqd Lh xs")
 (use "ListLengthRev")
(assume "Lh Rev xs eqd Lh xs")
(simphyp-with-to "SimpAux" "Lh Rev xs eqd Lh xs" "SimpSimpAux")
(use "SimpSimpAux")
(use "n<Lh xs")
;; Proof finished.
(save "ListProjRev")

;; ListRevFBarSucc
(set-goal "all n,(nat=>alpha) 
   Rev((nat=>alpha)fbar Succ n)eqd((nat=>alpha)n::Rev((nat=>alpha)fbar n))")
(assume "n" "(nat=>alpha)")
(simp "FBarAppdLast")
(simp "ListRevAppd")
(ng)
(use "InitEqD")
;; Proof finished.
(save "ListRevFBarSucc")

;; Similar to Pred in nat.scm we define Head and Tail.  They are
;; easier to handle than the general (Destr list alpha).

(add-program-constant "ListHead" (py "list alpha=>alpha") t-deg-zero)
(add-prefix-display-string "ListHead" "Head")
(add-computation-rules
 "Head(Nil alpha)" "(Inhab alpha)"
 "Head(x::xs)" "x")

(set-totality-goal "ListHead")
(assume "xs^" "Txs")
(elim "Txs")
(ng #t)
(use "InhabTotal")
(assume "x^" "Tx" "xs^1" "Txs1" "IH")
(ng #t)
(use "Tx")
;; Proof finished.
(save-totality)

(add-program-constant "ListTail" (py "list alpha=>list alpha") t-deg-zero)
(add-prefix-display-string "ListTail" "Tail")
(add-computation-rules
 "Tail(Nil alpha)" "(Inhab list alpha)"
 "Tail(x::xs)" "xs")

(set-totality-goal "ListTail")
(assume "xs^" "Txs")
(elim "Txs")
(ng #t)
(use "InhabTotal")
(assume "x^" "Tx" "xs^1" "Txs1" "IH")
(ng #t)
(use "Txs1")
;; Proof finished.
(save-totality)

;; ZeroLtLhToHeadTailId
(set-goal "all xs(0<Lh xs -> (Head xs::Tail xs)eqd xs)")
(cases)
(ng)
(use "Efq")
(assume "x" "xs" "Useless")
(use "InitEqD")
;; Proof finished.
(save "ZeroLtLhToHeadTailId")

(add-program-constant "ListLast" (py "list alpha=>alpha") t-deg-zero)
(add-prefix-display-string "ListLast" "Last")
(add-computation-rules
 "Last(Nil alpha)" "(Inhab alpha)"
 "Last(x::xs)" "[if (Lh xs=0) x (Last xs)]")

(set-totality-goal "ListLast")
(assume "xs^" "Txs")
(elim "Txs")
(ng #t)
(use "InhabTotal")
(assume "x^" "Tx" "xs^1" "Txs1" "IH")
(ng #t)
(use "BooleIfTotal")
(use "NatEqTotal")
(use "ListLengthTotal")
(use "Txs1")
(use "TotalNatZero")
(use "Tx")
(use "IH")
;; Proof finished.
(save-totality)

(add-program-constant "ListMain" (py "list alpha=>list alpha") t-deg-zero)
(add-prefix-display-string "ListMain" "Main")
(add-computation-rules
 "Main(Nil alpha)" "(Inhab list alpha)"
 "Main(x::xs)" "[if (Lh xs=0) (Nil alpha) (x::Main xs)]")

(set-totality-goal "ListMain")
(assume "xs^" "Txs")
(elim "Txs")
(ng #t)
(use "InhabTotal")
(assume "x^" "Tx" "xs^1" "Txs1" "IH")
(ng #t)
(use "BooleIfTotal")
(use "NatEqTotal")
(use "ListLengthTotal")
(use "Txs1")
(use "TotalNatZero")
(use "TotalListNil")
(use "TotalListCons")
(use "Tx")
(use "IH")
;; Proof finished.
(save-totality)

;; ZeroLtLhToMainLastId
(set-goal "all xs(0<Lh xs -> Main xs++(Last xs):eqd xs)")
(assert "all n,xs(Lh xs<=n -> 0<Lh xs -> Main xs++(Last xs):eqd xs)")
(ind)
(assume "xs")
(ng)
(assume "Lh xs=0")
(simp "Lh xs=0")
(ng)
(use "Efq")
(assume "n" "IHn")
(cases)
(ng)
(assume "Useless")
(use "Efq")
(assume "x" "xs" "LhBound" "Useless")
(ng)
(cases (pt "Lh xs=0"))
(assume "Lh xs=0")
(assert "xs eqd(Nil alpha)")
 (use "LhZeroToEqNilPartial")
 (use "ListSTotalVar")
 (use "Lh xs=0")
(assume "xs eqd(Nil alpha)")
(simp "xs eqd(Nil alpha)")
(ng)
(use "InitEqD")
(assume "0=Lh xs -> F")
(ng)
(simp "IHn")
(use "InitEqD")
(cases (pt "Lh xs"))
(assume "Lh xs=0")
(use "0=Lh xs -> F")
(use "Lh xs=0")
(strip)
(use "Truth")
(use "LhBound")
;; Now the assrtion is proved.
(assume "Assertion" "xs")
(use "Assertion" (pt "Lh xs"))
(use "Truth")
;; Proof finished.
(save "ZeroLtLhToMainLastId")

(add-program-constant "ListHeads" (py "list list alpha=>list alpha") t-deg-zero)
(add-prefix-display-string "ListHeads" "Heads")
(add-computation-rules
 "Heads(Nil list alpha)" "(Nil alpha)"
 "Heads(xs::(list list alpha))" "Head xs::Heads(list list alpha)")

(set-totality-goal "ListHeads")
(assume "(list list alpha)^" "Txss")
(elim "Txss")
(use "TotalListNil")
(assume "xs^" "Txs" "(list list alpha)^1" "Txss1" "IH")
(ng #t)
(use "TotalListCons")
(use "ListHeadTotal")
(use "Txs")
(use "IH")
;; Proof finished.
(save-totality)

;; We also define ListPHeads (p for proper), which ignores heads of
;; empty lists.

(add-program-constant
 "ListPHeads" (py "list list alpha=>list alpha") t-deg-zero)
(add-prefix-display-string "ListPHeads" "PHeads")
(add-computation-rules
 "PHeads(Nil list alpha)" "(Nil alpha)"
 "PHeads((Nil alpha)::(list list alpha))" "PHeads(list list alpha)"
 "PHeads((x::xs)::(list list alpha))" "x::PHeads(list list alpha)")

(set-totality-goal "ListPHeads")
(assume "(list list alpha)^" "Txss")
(elim "Txss")
(use "TotalListNil")
(assume "xs^" "Txs")
(elim "Txs")
(assume "(list list alpha)^1" "Txss1" "IH")
(ng #t)
(use "IH")
(assume "x^" "Tx" "xs^1" "Txs1" "Useless" "(list list alpha)^1" "Txss1" "IH")
(ng #t)
(use "TotalListCons")
(use "Tx")
(use "IH")
;; Proof finished.
(save-totality)

(add-program-constant "ListInit" (py "nat=>list alpha=>list alpha") t-deg-zero)
(add-infix-display-string "ListInit" "init" 'mul-op)
(add-computation-rules
 "0 init xs" "(Nil alpha)"
 "Succ n init(Nil alpha)" "(Nil alpha)"
 "Succ n init(x::xs)" "x::n init xs")

;; In lib/list.scm there is a similar ListBar.  Difference: in case
;; the number n is larger than the length, ListInit returns the
;; original list whereas ListBar appends Inhab's.

;; (pp (nt (pt "7 init(0::1::2::3::4:)")))
;; 0::1::2::3::4:

;; (pp (nt (pt "(0::1::2::3::4:)bar 7")))
;; 0::1::2::3::4::(Inhab nat)::(Inhab nat):

(set-totality-goal "ListInit")
(use "AllTotalElim")
(ind)
(ng)
(strip)
(use "TotalListNil")
(assume "n" "IHn" "xs^" "Txs")
(elim "Txs")
(ng)
(use "TotalListNil")
(assume "x^" "Tx" "xs^1" "Txs1" "Useless")
(ng)
(use "TotalListCons")
(use "Tx")
(use "IHn")
(use "Txs1")
;; Proof finished.
(save "ListInitTotal")

(add-program-constant "ListRest" (py "nat=>list alpha=>list alpha") t-deg-zero)
(add-infix-display-string "ListRest" "rest" 'mul-op)
(add-computation-rules
 "0 rest xs" "xs"
 "Succ n rest(Nil alpha)" "(Nil alpha)"
 "Succ n rest(x::xs)" "n rest xs")

(set-totality-goal "ListRest")
(use "AllTotalElim")
(ind)
(ng)
(assume "xs^" "Txs")
(use "Txs")
(assume "n" "IHn" "xs^" "Txs")
(elim "Txs")
(ng)
(use "TotalListNil")
(assume "x^" "Tx" "xs^1" "Txs1" "Useless")
(ng)
(use "IHn")
(use "Txs1")
;; Proof finished.
(save-totality)

;; (pp (nt (pt "1 init(5::6::7::8::9:)")))
;; 5:
;; (pp (nt (pt "1 rest(5::6::7::8::9:)")))
;; 6::7::8::9:

;; (pp (nt (pt "7 init(5::6::7::8::9:)")))
;; (pp (nt (pt "7 rest(5::6::7::8::9:)")))
;; (pp (nt (pt "0 init(5::6::7::8::9:)")))
;; (pp (nt (pt "0 rest(5::6::7::8::9:)")))

;; ListAppdInitRest
(set-goal "all n,xs xs eqd n init xs++(n rest xs)")
(ind)
(ng)
(assume "xs")
(use "InitEqD")
(assume "n" "IHn")
(ind)
(ng)
(use "InitEqD")
(assume "x" "xs" "IHxs")
(ng)
(simp "<-" "IHn")
(use "InitEqD")
;; Proof finished
(save "ListAppdInitRest")

;; ListAppdInitRestPartial
(set-goal "all n,xs^(STotalList xs^ -> xs^ eqd n init xs^ ++(n rest xs^))")
(ind)
(ng)
(assume "xs^" "STxs")
(elim "STxs")
(use "InitEqD")
(strip)
(use "InitEqD")
(assume "n" "IHn" "xs^" "STxs")
(elim "STxs")
(ng)
(use "InitEqD")
(assume "x^1" "xs^1" "STxs1" "IH")
(ng)
(simp "<-" "IHn")
(use "InitEqD")
(use "STxs1")
;; Proof finished
(save "ListAppdInitRestPartial")

;; ListInitLh
(set-goal "all xs Lh xs init xs eqd xs")
(ind)
(use "InitEqD")
(assume "x" "xs" "IHxs")
(ng)
(simp "IHxs")
(use "InitEqD")
;; Proof finished.
(save "ListInitLh")
(add-rewrite-rule "Lh xs init xs" "xs")

;; ListRestLh
(set-goal "all xs Lh xs rest xs eqd(Nil alpha)")
(ind)
(use "InitEqD")
(assume "x" "xs" "IHxs")
(ng)
(simp "IHxs")
(use "InitEqD")
;; Proof finished.
(save "ListRestLh")
(add-rewrite-rule "Lh xs rest xs" "(Nil alpha)")

;; ListLhInit
(set-goal "all xs,n(n<=Lh xs -> Lh(n init xs)=n)")
(ind)
(ng)
(assume "n" "n=0")
(simp "n=0")
(use "Truth")
(assume "x" "xs" "IHxs")
(ng)
(cases)
(ng)
(assume "Trivial")
(use "Trivial")
(use "IHxs")
;; Proof finished.
(save "ListLhInit")

;; ListLhRest
(set-goal "all xs,n(n<=Lh xs -> Lh(n rest xs)=Lh xs--n)")
(ind)
(ng)
(assume "n" "n=0")
(simp "n=0")
(use "Truth")
(assume "x" "xs" "IHxs")
(ng)
(cases)
(ng)
(assume "Trivial")
(use "Trivial")
(use "IHxs")
;; Proof finished.
(save "ListLhRest")

;; ListInitAppd
(set-goal "all xs1,xs2 Lh xs1 init(xs1++xs2) eqd xs1")
(ind)
(ng)
(assume "xs")
(use "InitEqD")
(assume "x" "xs" "IH" "xs2")
(ng)
(simp "IH")
(use "InitEqD")
;; Proof finished.
(save "ListInitAppd")

;; ListInitAppdPartial
(set-goal "all xs^1,xs^2(
 STotalList xs^1 -> Lh xs^1 init(xs^1++xs^2) eqd xs^1)")
(assume "xs^1" "xs^2" "Txs1")
(elim "Txs1")
(ng)
(use "InitEqD")
(assume "x^" "xs^" "Txs" "IH")
(ng)
(simp "IH")
(use "InitEqD")
;; Proof finished.
(save "ListInitAppdPartial")

;; ListInitAppdGen
(set-goal "all n,xs1,xs2(n<=Lh xs1 -> n init(xs1++xs2)eqd n init xs1)")
(ind)
(ng)
(strip)
(use "InitEqD")
(assume "n" "IHn")
(cases)
(ng #t)
(assume "xs1")
(use "Efq")
(assume "x" "xs1" "xs2")
(ng)
(assume "n<=Lh xs1")
(simp "IHn")
(use "InitEqD")
(use "n<=Lh xs1")
;; Proof finished.
(save "ListInitAppdGen")

;; ListRestAppd
(set-goal "all xs1,xs2 Lh xs1 rest(xs1++xs2) eqd xs2")
(ind)
(ng)
(assume "xs")
(use "InitEqD")
(assume "x" "xs" "IH" "xs2")
(ng)
(simp "IH")
(use "InitEqD")
;; Proof finished.
(save "ListRestAppd")

;; ListRestAppdPartial
(set-goal "all xs^1,xs^2(
 STotalList xs^1 -> Lh xs^1 rest(xs^1++xs^2) eqd xs^2)")
(assume "xs^1" "xs^2" "Txs1")
(elim "Txs1")
(ng)
(use "InitEqD")
(assume "x^" "xs^" "Txs" "IH")
(ng)
(simp "IH")
(use "InitEqD")
;; Proof finished.
(save "ListRestAppdPartial")

;; ListRestAppdGen
(set-goal "all n^,xs1,xs^2 (n^ +Lh xs1)rest(xs1++xs^2) eqd n^ rest xs^2")
(assume "n^")
(ind)
(ng)
(assume "xs^2")
(use "InitEqD")
(assume "x" "xs1" "IHxs1" "xs^2")
(ng)
(use "IHxs1")
;; Proof finished.
(save "ListRestAppdGen")

;; Now ListFilter

(add-program-constant
 "ListFilter" (py "(alpha=>boole)=>list alpha=>list alpha") t-deg-zero)
(add-infix-display-string "ListFilter" "filter" 'pair-op) ;right associative
(add-computation-rules
 "(alpha=>boole)filter(Nil alpha)" "(Nil alpha)"
 "(alpha=>boole)filter x::xs" "[if ((alpha=>boole)x)
                                   (x::(alpha=>boole)filter xs)
                                   ((alpha=>boole)filter xs)]")

(set-totality-goal "ListFilter")
(assume "(alpha=>boole)^" "Tf")
(assume "xs^" "Txs")
(elim "Txs")
(ng)
(use "TotalListNil")
(assume "x^" "Tx")
(ng)
(assume "xs^1" "Txs1")
(assume "IH")
(use "BooleIfTotal")
(use "Tf")
(use "Tx")
(use "TotalListCons")
(use "Tx")
(use "IH")
(use "IH")
;; Proof finished.
(save-totality)

;; (Foldl bin-op init-val list).  If list is empty, return init-val.
;; If not, apply ListFoldl with (i) initial value: the result of
;; applying bin-op to init-val and the head of list and (ii) the tail
;; of the list.

(add-program-constant
 "Foldl" (py "(alpha1=>alpha2=>alpha1)=>alpha1=>list alpha2=>alpha1")
 t-deg-zero)
(add-computation-rules
 "(Foldl alpha1 alpha2)(alpha1=>alpha2=>alpha1)y(Nil alpha2)" "y"
 "(Foldl alpha1 alpha2)(alpha1=>alpha2=>alpha1)y(z::zs)"
 "(Foldl alpha1 alpha2)(alpha1=>alpha2=>alpha1)
                       ((alpha1=>alpha2=>alpha1)y z)zs")

(set-totality-goal "Foldl")
(assume "(alpha1=>alpha2=>alpha1)^" "Tf")
(assert "allnc zs^(
          TotalList zs^ -> 
          allnc y^(
            Total y^ -> 
            Total((Foldl alpha1 alpha2)(alpha1=>alpha2=>alpha1)^ y^ zs^)))")
(assume "zs^" "Tzs")
(elim "Tzs")
(ng)
(assume "y^" "Ty")
(use "Ty")
(assume "z^" "Tz" "zs^1" "Tzs1" "IHzs1" "y^" "Ty")
(ng)
(use "IHzs1")
(use "Tf")
(use "Ty")
(use "Tz")
(assume "Assertion" "y^" "Ty" "zs^" "Tzs")
(use "Assertion")
(use "Tzs")
(use "Ty")
;; Proof finished.
(save-totality)

;; (Foldr bin-op init-val list).  If list is empty, return init-val.
;; If not, apply bin-op to the head of list and the result of applying
;; Foldr to bin-op, init-val and the tail of the list.

(add-program-constant
 "Foldr" (py "(alpha1=>alpha2=>alpha2)=>alpha2=>list alpha1=>alpha2")
 t-deg-zero)
(add-computation-rules
 "(Foldr alpha1 alpha2)(alpha1=>alpha2=>alpha2)z(Nil alpha1)" "z"
 "(Foldr alpha1 alpha2)(alpha1=>alpha2=>alpha2)z(y::ys)"
 "(alpha1=>alpha2=>alpha2)y
  ((Foldr alpha1 alpha2)(alpha1=>alpha2=>alpha2)z ys)") 

(set-totality-goal "Foldr")
(assume "(alpha1=>alpha2=>alpha2)^" "Tf" "z^" "Tz" "ys^" "Tys")
(elim "Tys")
(ng)
(use "Tz")
(assume "y^" "Ty" "ys^1" "Tys1" "IHys1")
(ng)
(use "Tf")
(use "Ty")
(use "IHys1")
;; Proof finished.
(save-totality)

;; ListFrom m n returns the list of increasing natural numbers
;; starting from m of length n.

(add-program-constant "ListFrom" (py "nat=>nat=>list nat") t-deg-zero)
(add-computation-rules
 "ListFrom m 0" "(Nil nat)"
 "ListFrom m(Succ n)" "m::ListFrom(Succ m)n")

;; (pp (nt (pt "ListFrom 2 5")))
;; 2::3::4::5::6:

(set-totality-goal "ListFrom")
(assert "all n,m TotalList(ListFrom m n)")
 (ind)
 (assume "m")
 (use "TotalListNil")
 (assume "n" "IH" "m")
 (ng)
 (use "TotalListCons")
 (use "NatTotalVar")
 (use "IH")
(assume "Assertion")
(use "AllTotalElim")
(assume "n")
(use "AllTotalElim")
(assume "m")
(use "Assertion")
;; Proof finished.
(save-totality)

;; Some important concepts for list depend on a decidable equality for
;; the list elements and hence are defined for finitary algebras only.

(add-program-constant "ListNatIn" (py "nat=>list nat=>boole") t-deg-zero)
(add-infix-display-string "ListNatIn" "in" 'pair-op)
(add-computation-rules
 "n in(Nil nat)" "False"
 "n in(m::(list nat))" "[if (n=m) True (n in (list nat))]")

(set-totality-goal "ListNatIn")
(use "AllTotalElim")
(assume "n")
(use "AllTotalElim")
(ind)
(use "TotalBooleFalse")
(assume "m" "(list nat)" "IHn")
(ng)
(cases (pt "n=m"))
(strip)
(use "TotalBooleTrue")
(strip)
(use "IHn")
;; Proof finished.
(save-totality)

;; ListListNatEqToEqD
(set-goal "all (list list nat)_1,(list list nat)_2(
 (list list nat)_1=(list list nat)_2 ->
 (list list nat)_1 eqd (list list nat)_2)")
(ind)
(cases)
(assume "Useless")
(use "InitEqD")
(assume "(list nat)_1" "(list list nat)_1" "Absurd")
(use "EfqEqD")
(use "Absurd")
(assume "(list nat)_1" "(list list nat)_1" "IH")
(cases)
(assume "Absurd")
(use "EfqEqD")
(use "Absurd")
(ng)
(assume "(list nat)_2" "(list list nat)_2" "Conj")
(inst-with-to "Conj" 'left "(list nat)_1=(list nat)_2")
(inst-with-to "Conj" 'right "(list list nat)_1=(list list nat)_2")
(drop "Conj")
(assert "(list nat)_1 eqd (list nat)_2")
 (use "ListNatEqToEqD")
 (use "(list nat)_1=(list nat)_2")
(assume "(list nat)_1 eqd (list nat)_2")
(assert "(list list nat)_1 eqd (list list nat)_2")
 (use "IH")
 (use "(list list nat)_1=(list list nat)_2")
(assume "(list list nat)_1 eqd (list list nat)_2")
(elim "(list list nat)_1 eqd (list list nat)_2")
(assume "(list list nat)^1")
(elim "(list nat)_1 eqd (list nat)_2")
(assume "(list nat)^")
(use "InitEqD")
;; Proof finished.
(save "ListListNatEqToEqD")

(remove-var-name "x" "xs" "phi" "psi" "y" "ys" "z" "zs")
