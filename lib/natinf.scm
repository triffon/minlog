; $Id: natinf.scm 2470 2011-05-16 19:21:05Z schwicht $
(display "loading natinf.scm ...") (newline)

; The natural numbers plus an infinite object
; ===========================================

; We need the type nat ysumu as range of the weight function.  Since
; we want to use e.g. + for this type, we only load parts of nat.scm

; (load "~/minlog/init.scm")

(add-alg "nat" '("Zero" "nat") '("Succ" "nat=>nat"))

(define (make-numeric-term n)
  (if (= n 0)
      (pt "Zero")
      (make-term-in-app-form
       (pt "Succ")
       (make-numeric-term (- n 1)))))

(define (is-numeric-term? term)
  (or
   (and (term-in-const-form? term)
	(string=? "Zero" (const-to-name (term-in-const-form-to-const term))))
   (and (term-in-app-form? term)
	(let ((op (term-in-app-form-to-op term)))
	  (and (term-in-const-form? op)
	       (string=? "Succ" (const-to-name
				 (term-in-const-form-to-const op)))
	       (is-numeric-term? (term-in-app-form-to-arg term)))))))

(define (numeric-term-to-number term)
  (if (equal? term (pt "Zero"))
      0
      (+ 1 (numeric-term-to-number (term-in-app-form-to-arg term)))))

(add-program-constant "NatPlus" (py "nat=>nat=>nat") t-deg-one)

(add-token
 "+++" 'add-op
 (lambda (x y)
   (mk-term-in-app-form
    (make-term-in-const-form (pconst-name-to-pconst "NatPlus")) x y)))

(add-display
 (py "nat")
 (lambda (x)
   (if (term-in-app-form? x)
       (let ((op (term-in-app-form-to-final-op x))
	     (args (term-in-app-form-to-args x)))
	 (if (and (term-in-const-form? op)
		  (string=? "NatPlus"
			    (const-to-name (term-in-const-form-to-const op)))
		  (= 2 (length args)))
	     (list 'add-op "+++"
		   (term-to-token-tree (car args))
		   (term-to-token-tree (cadr args)))
	     #f))
       #f)))

(add-computation-rule (pt "nat+++0") (pt "nat"))
(add-computation-rule (pt "nat1+++Succ nat2") (pt "Succ(nat1+++nat2)"))

(quote (begin
(set-goal (pf "all nat 0+++nat=nat"))
(ind)
(use "Truth-Axiom")
(assume "nat" "IH")
(use "IH")

(set-goal (pf "all nat1,nat2 Succ nat1+++nat2=Succ(nat1+++nat2)"))
(assume "nat1")
(ind)
(use "Truth-Axiom")
(assume "nat2" "IH")
(use "IH")

(set-goal (pf "all nat1,nat2,nat3 nat1+++(nat2+++nat3)=nat1+++nat2+++nat3"))
(assume "nat1" "nat2")
(ind)
(use "Truth-Axiom")
(assume "nat3" "IH")
(use "IH")
)) ;matches quote

(add-rewrite-rule (pt "0+++nat") (pt "nat"))
(add-rewrite-rule (pt "Succ nat1+++nat2") (pt "Succ(nat1+++nat2)"))
(add-rewrite-rule (pt "nat1+++(nat2+++nat3)") (pt "nat1+++nat2+++nat3"))

(quote (begin
; "NatPlusComm"
(set-goal (pf "all nat1,nat2.nat1+++nat2=nat2+++nat1"))
(assume "nat1")
(ind)
(use "Truth-Axiom")
(assume "nat2" "IH")
(use "IH")
(save "NatPlusComm")
)) ;matches quote


(add-program-constant "NatLt" (py "nat=>nat=>boole") t-deg-one)

(add-token
 "<<" 'rel-op
 (lambda (x y)
   (mk-term-in-app-form
    (make-term-in-const-form (pconst-name-to-pconst "NatLt")) x y)))

(add-display
 (py "boole")
 (lambda (x)
   (if (term-in-app-form? x)
       (let ((op (term-in-app-form-to-final-op x))
	     (args (term-in-app-form-to-args x)))
	 (if (and (term-in-const-form? op)
		  (string=? "NatLt"
			    (const-to-name (term-in-const-form-to-const op)))
		  (= 2 (length args)))
	     (list 'rel-op "<<"
		   (term-to-token-tree (car args))
		   (term-to-token-tree (cadr args)))
	     #f))
       #f)))

(add-computation-rule (pt "nat<<0") (pt "False"))
(add-computation-rule (pt "0<<Succ nat") (pt "True"))
(add-computation-rule (pt "Succ nat1<<Succ nat2") (pt "nat1<<nat2"))

(add-rewrite-rule (pt "nat<<nat") (pt "False"))
(add-rewrite-rule (pt "nat<<Succ nat") (pt "True"))

(add-program-constant "Pred" (py "nat=>nat") t-deg-one)

(add-computation-rule (pt "Pred 0") (pt "0"))
(add-computation-rule (pt "Pred(Succ nat)") (pt "nat"))

(add-program-constant "NatMinus" (py "nat=>nat=>nat") t-deg-one)

(add-token
 "-" 'add-op
 (lambda (x y)
   (mk-term-in-app-form
    (make-term-in-const-form (pconst-name-to-pconst "NatMinus")) x y)))

(add-display
 (py "nat")
 (lambda (x)
   (if (term-in-app-form? x)
       (let ((op (term-in-app-form-to-final-op x))
	     (args (term-in-app-form-to-args x)))
	 (if (and (term-in-const-form? op)
		  (string=? "NatMinus"
			    (const-to-name (term-in-const-form-to-const op)))
		  (= 2 (length args)))
	     (list 'add-op "-"
		   (term-to-token-tree (car args))
		   (term-to-token-tree (cadr args)))
	     #f))
       #f)))

(add-computation-rule (pt "nat-0") (pt "nat"))
(add-computation-rule (pt "nat1-Succ nat2") (pt "Pred(nat1-nat2)"))

(add-rewrite-rule (pt "nat-nat") (pt "0"))
(add-rewrite-rule (pt "0-nat") (pt "0"))
(add-rewrite-rule (pt "Pred(Succ nat1-nat2)") (pt "nat1-nat2"))
(add-rewrite-rule (pt "nat1+++nat2-nat1") (pt "nat2"))
(add-rewrite-rule (pt "nat1+++nat2-nat2") (pt "nat1"))
(add-rewrite-rule (pt "nat1+++(nat2 - nat3)") (pt "nat1+++nat2-nat3"))

(add-var-name "n" "m" "k" (py "nat"))

(add-var-name "x" "y" "z" (py "nat ysumu"))

; (pp (pt "Inl 0"))
; (pp (pt "(DummyR nat)"))
; (pp (term-to-type (pt "Inl n")))
; (pp (term-to-type (pt "(DummyR nat)")))

(add-program-constant
 "NatinfPlus"
 (py "nat ysumu=>nat ysumu=>nat ysumu") t-deg-one)

(add-token
 "+" 'add-op
 (lambda (x y)
   (mk-term-in-app-form
    (make-term-in-const-form (pconst-name-to-pconst "NatinfPlus")) x y)))

(add-display
 (py "nat ysumu")
 (lambda (x)
   (let* ((op (term-in-app-form-to-final-op x))
	  (args (term-in-app-form-to-args x)))
     (if (and (term-in-const-form? op)
	      (string=? "NatinfPlus"
			(const-to-name (term-in-const-form-to-const op)))
	      (= 2 (length args)))
	 (list 'add-op "+"
	       (term-to-token-tree (car args))
	       (term-to-token-tree (cadr args)))
	 #f))))

(add-computation-rule (pt "x+Inl 0") (pt "x"))
(add-computation-rule (pt "Inl n+Inl(Succ m)") (pt "Inl(Succ(n+++m))"))
(add-computation-rule (pt "(DummyR nat)+Inl(Succ m)") (pt "(DummyR nat)"))
(add-computation-rule (pt "x+(DummyR nat)") (pt "(DummyR nat)"))

(add-rewrite-rule (pt "Inl 0+x") (pt "x"))
(add-rewrite-rule (pt "Inl(Succ n)+Inl m") (pt "Inl(Succ(n+++m))"))
(add-rewrite-rule (pt "x1+(x2+x3)") (pt "x1+x2+x3"))

(add-program-constant
 "NatinfLe" (py "nat ysumu=>nat ysumu=>boole") t-deg-one)

(add-token
 "<=" 'rel-op
 (lambda (x y)
   (mk-term-in-app-form
    (make-term-in-const-form (pconst-name-to-pconst "NatinfLe")) x y)))

(add-display
 (py "boole")
 (lambda (x)
   (let* ((op (term-in-app-form-to-final-op x))
	  (args (term-in-app-form-to-args x)))
     (if (and (term-in-const-form? op)
	      (string=? "NatinfLe"
			(const-to-name (term-in-const-form-to-const op)))
	      (= 2 (length args)))
	 (list 'rel-op "<="
	       (term-to-token-tree (car args))
	       (term-to-token-tree (cadr args)))
	 #f))))

(add-computation-rule (pt "Inl 0<=y") (pt "True"))
(add-computation-rule (pt "Inl(Succ n)<=Inl 0") (pt "False"))
(add-computation-rule (pt "Inl(Succ n)<=Inl(Succ m)") (pt "Inl n<=Inl m"))
(add-computation-rule (pt "Inl(Succ n)<=(DummyR nat)") (pt "True"))
(add-computation-rule (pt "(DummyR nat)<=Inl m") (pt "False"))
(add-computation-rule (pt "(DummyR nat)<=(DummyR nat)") (pt "True"))

(add-rewrite-rule (pt "x<=x") (pt "True"))
(add-rewrite-rule (pt "x<=(DummyR nat)") (pt "True"))
(add-rewrite-rule (pt "x<=x+y") (pt "True"))

(add-program-constant
 "NatinfLt" (py "nat ysumu=>nat ysumu=>boole") t-deg-one)

(add-token
 "<" 'rel-op
 (lambda (x y)
   (mk-term-in-app-form
    (make-term-in-const-form (pconst-name-to-pconst "NatinfLt")) x y)))

(add-display
 (py "boole")
 (lambda (x)
   (let* ((op (term-in-app-form-to-final-op x))
	  (args (term-in-app-form-to-args x)))
     (if (and (term-in-const-form? op)
	      (string=? "NatinfLt"
			(const-to-name (term-in-const-form-to-const op)))
	      (= 2 (length args)))
	 (list 'rel-op "<"
	       (term-to-token-tree (car args))
	       (term-to-token-tree (cadr args)))
	 #f))))

(add-computation-rule (pt "x<Inl 0") (pt "False"))
(add-computation-rule (pt "Inl 0<Inl(Succ m)") (pt "True"))
(add-computation-rule (pt "Inl(Succ n)<Inl(Succ m)") (pt "Inl n<Inl m"))
(add-computation-rule (pt "(DummyR nat)<Inl(Succ m)") (pt "False"))
(add-computation-rule (pt "Inl n<(DummyR nat)") (pt "True"))
(add-computation-rule (pt "(DummyR nat)<(DummyR nat)") (pt "False"))

(add-rewrite-rule (pt "x<x") (pt "False"))
(add-rewrite-rule (pt "x+y<x") (pt "False"))
(add-rewrite-rule (pt "(DummyR nat)<y") (pt "False"))
(add-rewrite-rule (pt "Inl m<Inl(Succ m)") (pt "True"))


(add-program-constant
 "NatinfMin" (py "nat ysumu=>nat ysumu=>nat ysumu") t-deg-one)

(add-token
 "min" 'mul-op
 (lambda (x y)
   (mk-term-in-app-form
    (make-term-in-const-form (pconst-name-to-pconst "NatinfMin")) x y)))

(add-display
 (py "nat ysumu")
 (lambda (x)
   (let* ((op (term-in-app-form-to-final-op x))
	  (args (term-in-app-form-to-args x)))
     (if (and (term-in-const-form? op)
	      (string=? "NatinfMin"
			(const-to-name (term-in-const-form-to-const op)))
	      (= 2 (length args)))
	 (list 'mul-op "min"
	       (term-to-token-tree (car args))
	       (term-to-token-tree (cadr args)))
	 #f))))

(add-computation-rule (pt "Inl 0 min y") (pt "Inl 0"))
(add-computation-rule (pt "Inl(Succ n)min Inl 0") (pt "Inl 0"))
(add-computation-rule (pt "Inl(Succ n)min Inl(Succ m)")
		      (pt "(Inl n min Inl m)+Inl 1"))
(add-computation-rule (pt "Inl(Succ n)min (DummyR nat)") (pt "Inl(Succ n)"))
(add-computation-rule (pt "(DummyR nat) min y") (pt "y"))

(add-rewrite-rule (pt "x min Inl 0") (pt "Inl 0"))
(add-rewrite-rule (pt "x min x") (pt "x"))
(add-rewrite-rule (pt "(x+y) min x") (pt "x"))
(add-rewrite-rule (pt "x min (x+y)") (pt "x"))

(add-rewrite-rule (pt "x min y<=x") (pt "True"))
(add-rewrite-rule (pt "x min y<=y") (pt "True"))
(add-rewrite-rule (pt "x min y<x") (pt "True"))
(add-rewrite-rule (pt "x min y<y") (pt "True"))
