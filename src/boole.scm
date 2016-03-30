;; $Id: boole.scm 2665 2014-01-08 09:54:29Z schwicht $
;; 7. Formulas and comprehension terms
;; ===================================

;; First we add some tokens (this can only be done after loading
;; minitab.scm, which is done immediately before loading the present file).

(add-token "andd" 'and-jct make-andd)
(add-token "andr" 'and-jct make-andr)
(add-token "andl" 'and-jct make-andl)
(add-token "andu" 'and-jct make-andu)
(add-token "andi" 'and-jct make-andi)

(add-token "ord" 'or-jct make-ord)
(add-token "orl" 'or-jct make-orl)
(add-token "orr" 'or-jct make-orr)
(add-token "oru" 'or-jct make-oru)
(add-token "ori" 'or-jct make-ori)
(add-token "ornc" 'or-jct make-ornc)

(add-token "eqd" 'pred-infix make-eqd)
(add-idpredconst-display "EqD" 'pred-infix "eqd")

(add-token "exd" 'quantor (lambda (v k) (apply mk-exd (append v (list k)))))
(add-token "exl" 'quantor (lambda (v k) (apply mk-exl (append v (list k)))))
(add-token "exr" 'quantor (lambda (v k) (apply mk-exr (append v (list k)))))
(add-token "exu" 'quantor (lambda (v k) (apply mk-exu (append v (list k)))))
(add-token "exi" 'quantor (lambda (v k) (apply mk-exi (append v (list k)))))

;; We introduce a prefix display string Des for Destr

;; (pp (pt "(Destr boole)boole"))

(add-token
 "Des"
 'prefix-op
 (lambda (x) (make-term-in-app-form
	      (make-term-in-const-form
	       (let ((type (term-to-type x)))
		 (if (alg-form? type)
		     (alg-to-destr-const type)
		     (myerror "alg-form expected" type))))
	      x)))

;; (pt "Des boole")

(add-display
 (py "alpha")
 (lambda (x)
   (if (term-in-app-form? x)
       (let ((op (term-in-app-form-to-final-op x))
	     (args (term-in-app-form-to-args x)))
	 (if (and (term-in-const-form? op)
		  (string=? "Destr"
			    (const-to-name (term-in-const-form-to-const op)))
		  (= 1 (length args)))
	     (list 'prefix-op "Des" (term-to-token-tree (car args)))
	     #f))
       #f)))

;; (pp (pt "Des boole"))

(add-token
 "DesYprod"
 'prefix-op
 (lambda (x) (make-term-in-app-form
	      (make-term-in-const-form
	       (let ((type (term-to-type x)))
		 (if (alg-form? type)
		     (alg-to-destr-const type #f) ;opt-prim-prod-flag is #f
		     (myerror "alg-form expected" type))))
	      x)))

;; (pt "DesYprod boole")

(add-display
 (py "alpha")
 (lambda (x)
   (if (term-in-app-form? x)
       (let ((op (term-in-app-form-to-final-op x))
	     (args (term-in-app-form-to-args x)))
	 (if (and (term-in-const-form? op)
		  (string=? "Destr"
			    (const-to-name (term-in-const-form-to-const op)))
		  (= 1 (length args)))
	     (let* ((uninst-destr-type
		     (const-to-uninst-type (term-in-const-form-to-const op)))
		    (val-type (arrow-form-to-val-type uninst-destr-type))
		    (product-types (ysum-without-unit-to-components val-type))
		    (prim-prod?
		     (not (apply or-op (map yprod-form? product-types)))))
	       (list 'prefix-op
		     (if prim-prod? "Des" "DesYprod")
		     (term-to-token-tree (car args))))
	     #f))
       #f)))

;; 7-8. Booleans
;; =============

;; We need to initialize some global variables (needed for is-used?),
;; before we can call add-alg.

(define THEOREMS '())
(define GLOBAL-ASSUMPTIONS '())

(add-alg "unit" '("Dummy" "unit"))
(define dummy-const (constr-name-to-constr "Dummy"))

(add-alg "boole" '("True" "boole") '("False" "boole"))

(add-new-application
 (lambda (type) (equal? type (make-alg "boole")))
 (lambda (test alt1)
   (let* ((type (term-to-type alt1))
	  (var (type-to-new-var type)))
     (make-term-in-abst-form
      var (make-term-in-if-form
	   test (list alt1 (make-term-in-var-form var)))))))

(add-display
 (py "boole")
 (lambda (term)
   (let ((op (term-in-app-form-to-final-op term))
	 (args (term-in-app-form-to-args term)))
     (if (and (term-in-const-form? op)
	      (string=? "=" (const-to-name (term-in-const-form-to-const op)))
	      (= 2 (length args)))
	 (list 'rel-op "="
	       (term-to-token-tree (car args))
	       (term-to-token-tree (cadr args)))
	 #f))))

(add-display
 (py "boole")
 (lambda (term)
   (let ((op (term-in-app-form-to-final-op term))
	 (args (term-in-app-form-to-args term)))
     (if (and (term-in-const-form? op)
	      (string=? "E" (const-to-name (term-in-const-form-to-const op)))
	      (= 1 (length args)))
	 (list 'prefix-op "E" (term-to-token-tree (car args)))
	 #f))))

(define (trueval? val)
  (and (nbe-constr-value? val)
       (string=? "True"
		 (const-to-name (nbe-constr-value-to-constr val)))))

(define true-const (constr-name-to-constr "True"))
(define trueobj (const-to-object-or-arity true-const))
(define truth (make-atomic-formula (make-term-in-const-form true-const)))
(add-token "T" 'const (make-term-in-const-form true-const))

(define (falseval? val)
  (and (nbe-constr-value? val)
       (string=? "False"
		 (const-to-name (nbe-constr-value-to-constr val)))))

(define false-const (constr-name-to-constr "False"))
(define falseobj (const-to-object-or-arity false-const))
(define falsity (make-atomic-formula (make-term-in-const-form false-const)))
(add-token "F" 'const (make-term-in-const-form false-const))

(define (make-negation formula) (make-imp formula falsity))
(add-token "not" 'prefix-jct make-negation)

(define falsity-log
  (make-predicate-formula
   (make-pvar (make-arity) -1 h-deg-zero n-deg-zero "bot")))

(define (make-negation-log formula) (make-imp formula falsity-log))
(add-token "notl" 'prefix-jct make-negation-log)

;; 2004-12-31.  Moved here from pconst.scm.  Reason: =-at and e-at need
;; AndConst, which requires the algebra boole.

(define (finalg-to-=-const finalg)
  (if (not (finalg? finalg))
      (myerror "finalg-to-=-const" "finitary algebra expected" finalg)
      (make-const (=-at finalg)
		  "=" 'fixed-rules
		  (mk-arrow finalg finalg (make-alg "boole")) empty-subst
		  1 'rel-op)))

(add-program-constant "AndConst" (py "boole=>boole=>boole"))

;; The computation rules for the constants introduced here can be
;; added only later in ets.scm, since the construction of the proofs
;; for their rules needs EqD.

;; (add-computation-rules
;;  "AndConst True boole^" "boole^"
;;  "AndConst boole^ True" "boole^"
;;  "AndConst False boole^" "False"
;;  "AndConst boole^ False" "False")

;; We add infix notation "andb" (also "and") (left associative) for AndConst.
;; Coq has "/\"

(add-token
 "andb" 'and-op
 (lambda (x y)
   (mk-term-in-app-form
    (make-term-in-const-form (pconst-name-to-pconst "AndConst")) x y)))

(add-token
 "and" 'and-op
 (lambda (x y)
   (mk-term-in-app-form
    (make-term-in-const-form (pconst-name-to-pconst "AndConst")) x y)))

(add-display
 (py "boole")
 (lambda (x)
   (if (term-in-app-form? x)
       (let ((op (term-in-app-form-to-final-op x))
	     (args (term-in-app-form-to-args x)))
	 (if (and (term-in-const-form? op)
		  (string=? "AndConst"
			    (const-to-name (term-in-const-form-to-const op)))
		  (= 2 (length args)))
	     (list 'and-op "andb"
		   (term-to-token-tree (car args))
		   (term-to-token-tree (cadr args)))
	     #f))
       #f)))

(define and-const (term-in-const-form-to-const (pt "AndConst")))

(add-program-constant "ImpConst" (py "boole=>boole=>boole"))

;; (add-computation-rules
;; "ImpConst False boole^" "True"
;; "ImpConst True boole^" "boole^"
;; "ImpConst boole^ True" "True")

;; We add an infix notation "impb" (left associative) for ImpConst

(add-token
 "impb" 'imp-op
 (lambda (x y)
   (mk-term-in-app-form
    (make-term-in-const-form (pconst-name-to-pconst "ImpConst")) x y)))

(add-display
 (py "boole")
 (lambda (x)
   (if (term-in-app-form? x)
       (let ((op (term-in-app-form-to-final-op x))
	     (args (term-in-app-form-to-args x)))
	 (if (and (term-in-const-form? op)
		  (string=? "ImpConst"
			    (const-to-name (term-in-const-form-to-const op)))
		  (= 2 (length args)))
	     (list 'imp-op "impb"
		   (term-to-token-tree (car args))
		   (term-to-token-tree (cadr args)))
	     #f))
       #f)))

(define imp-const (term-in-const-form-to-const (pt "ImpConst")))

(add-program-constant "OrConst" (py "boole=>boole=>boole"))

;; (add-computation-rules
;; "OrConst True boole^" "True"
;; "OrConst boole^ True" "True"
;; "OrConst False boole^" "boole^"
;; "OrConst boole^ False" "boole^")

;; We add an infix notation "orb" (left associative) for OrConst
;; Coq has "\/"

(add-token
 "orb" 'or-op
 (lambda (x y)
   (mk-term-in-app-form
    (make-term-in-const-form (pconst-name-to-pconst "OrConst")) x y)))

(add-display
 (py "boole")
 (lambda (x)
   (if (term-in-app-form? x)
       (let ((op (term-in-app-form-to-final-op x))
	     (args (term-in-app-form-to-args x)))
	 (if (and (term-in-const-form? op)
		  (string=? "OrConst"
			    (const-to-name (term-in-const-form-to-const op)))
		  (= 2 (length args)))
	     (list 'or-op "orb"
		   (term-to-token-tree (car args))
		   (term-to-token-tree (cadr args)))
	     #f))
       #f)))

(define or-const (term-in-const-form-to-const (pt "OrConst")))

(add-program-constant "NegConst" (py "boole=>boole"))

;; (add-computation-rules
;; "NegConst True" "False"
;; "NegConst False" "True")

;; We add a prefix notation "negb" for NegConst

(add-token
 "negb" 'prefix-op
 (lambda (x)
   (mk-term-in-app-form
    (make-term-in-const-form (pconst-name-to-pconst "NegConst")) x)))

(add-display
 (py "boole")
 (lambda (x)
   (if (term-in-app-form? x)
       (let ((op (term-in-app-form-to-final-op x))
	     (args (term-in-app-form-to-args x)))
	 (if (and (term-in-const-form? op)
		  (string=? "NegConst"
			    (const-to-name (term-in-const-form-to-const op)))
		  (= 1 (length args)))
	     (list 'prefix-op "negb"
		   (term-to-token-tree (car args)))
	     #f))
       #f)))

(define neg-const (term-in-const-form-to-const (pt "NegConst")))

;; In pproof.scm we have
;; and-atom-to-left-proof "boole1 andb boole2 -> boole1"
;; atoms-to-and-atom-proof "boole1 -> boole2 -> boole1 andb boole2

;; In atr.scm we have
;; imp-to-atom-proof "(boole1 -> boole2) -> ImpConst boole1 boole2"
;; and-to-atom-proof "boole1 & boole2 -> boole1 and boole2"
;; atom-to-imp-proof "ImpConst boole1 boole2 -> boole1 -> boole2
;; atom-to-and-proof "boole1 and boole2 -> boole1 & boole2"
;; qf-to-atom-imp-qf-proof: atom(r_C) -> C
;; qf-to-qf-imp-atom-proof: C -> atom(r_C)

(define (=-at finalg)
  (nbe-make-object
   (mk-arrow finalg finalg (make-alg "boole"))
   (lambda (obj1)
     (nbe-make-object
      (mk-arrow finalg (make-alg "boole"))
      (lambda (obj2)
	(let* ((val1 (nbe-object-to-value obj1))
	       (val2 (nbe-object-to-value obj2))
	       (constr1? (nbe-constr-value? val1))
	       (constr2? (nbe-constr-value? val2))
	       (reprod-obj (nbe-make-object
			    (make-alg "boole")
			    (nbe-make-termfam
			     (make-alg "boole")
			     (lambda (k)
			       (mk-term-in-app-form
				(make-term-in-const-form
				 (finalg-to-=-const finalg))
				(nbe-fam-apply (nbe-reify obj1) k)
				(nbe-fam-apply (nbe-reify obj2) k)))))))
	  (cond
	   ((and constr1? constr2?)
	    (let ((name1 (nbe-constr-value-to-name val1))
		  (name2 (nbe-constr-value-to-name val2)))
	      (if
	       (not (string=? name1 name2))
	       falseobj
	       (let* ((args1 (nbe-constr-value-to-args val1))
		      (args2 (nbe-constr-value-to-args val2))
		      (argtypes1 (map nbe-object-to-type args1))
		      (argtypes2 (map nbe-object-to-type args2))
		      (argtypes
		       (if (equal? argtypes1 argtypes2)
			   argtypes1
			   (myerror "=-at" "equal argtypes expected"
				    (map type-to-string argtypes1)
				    (map type-to-string argtypes2))))
		      (prevs
		       (do ((l1 args1 (cdr l1))
			    (l2 args2 (cdr l2))
			    (ltypes argtypes (cdr ltypes))
			    (res
			     '()
			     (let* ((arg1 (car l1))
				    (arg2 (car l2))
				    (type (car ltypes))
				    (prev
				     (case (tag type)
				       ((alg)
					(nbe-object-app (=-at type)
							arg1 arg2))
				       ((arrow) ;unit -> finalg
					(nbe-object-app
					 (=-at (arrow-form-to-val-type type))
					 (nbe-object-app
					  arg1
					  (const-to-object-or-arity
					   dummy-const))
					 (nbe-object-app
					  arg2
					  (const-to-object-or-arity
					   dummy-const))))
				       (else (myerror "=-at" "type expected"
						      type)))))
			       (let ((prevval (nbe-object-to-value prev)))
				 (cond
				  ((trueval? prevval) res)
				  ((falseval? prevval) (cons 'f res))
				  (else (cons prev res)))))))
			   ((or (memq 'f res) (null? l1)) res))))
		 (cond
		  ((null? prevs)
		   trueobj)
		  ((memq 'f prevs)
		   falseobj)
		  (else
		   (do ((l (cdr prevs) (cdr l))
			(obj
			 (car prevs)
			 (nbe-make-object
			  (make-alg "boole")
			  (nbe-make-termfam
			   (make-alg "boole")
			   (lambda (k)
			     (mk-term-in-app-form
			      (make-term-in-const-form
			       (pconst-name-to-pconst "AndConst"))
			      (nbe-fam-apply (nbe-reify (car l)) k)
			      (nbe-fam-apply (nbe-reify obj) k)))))))
		       ((null? l) obj))))))))
	   ((or constr1? constr2?)
	    (let* ((constr-obj (if constr1? obj1 obj2))
		   (constr-val (if constr1? val1 val2))
		   (obj (if constr1? obj2 obj1)))
	      (do ((l (nbe-constr-value-to-args constr-val) (cdr l)))
		  ((or (null? l)
		       (let* ((arg (car l))
			      (argalg (nbe-object-to-type arg))
			      (prev (nbe-object-app (in-at finalg argalg)
						    obj arg))
			      (prevval (nbe-object-to-value prev)))
			 (trueval? prevval)))
		   (if (null? l)
		       reprod-obj
		       falseobj)))))
	   ((and (nbe-fam-value? val1) (nbe-fam-value? val2))
	    (let ((term1 (nbe-extract val1))
		  (term2 (nbe-extract val2)))
	      (if (and (term=? term1 term2)
		       (synt-total? term1) (synt-total? term2))
		  trueobj
		  reprod-obj)))
	   (else reprod-obj))))))))

(define (in-at finalg1 finalg2)
  (nbe-make-object
   (mk-arrow finalg1 finalg2 (make-alg "boole"))
   (lambda (obj1)
     (nbe-make-object
      (mk-arrow finalg2 (make-alg "boole"))
      (lambda (obj2)
	(let ((val1 (nbe-object-to-value obj1))
	      (val2 (nbe-object-to-value obj2)))
	  (cond
	   ((and (equal? finalg1 finalg2)
		 (trueval? (nbe-object-to-value
			    (nbe-object-app (=-at finalg1) obj1 obj2))))
	    trueobj)
	   ((nbe-constr-value? val2)
	    (do ((l (nbe-constr-value-to-args val2) (cdr l)))
		((or (null? l)
		     (let* ((arg (car l))
			    (argtype (nbe-object-to-type arg))
			    (prev (nbe-object-app (in-at finalg1 argtype)
						  obj1 arg))
			    (prevval (nbe-object-to-value prev)))
		       (trueval? prevval)))
		 (if (null? l)
		     falseobj
		     trueobj))))
	   (else falseobj))))))))

(define (finalg-to-e-const finalg)
  (if (not (finalg? finalg))
      (myerror "finalg-to-e-const" "finitary algebra expected" finalg)
      (make-const (e-at finalg)
		  "E" 'fixed-rules
		  (make-arrow finalg (make-alg "boole")) empty-subst
		  1 'prefix-op)))

(define (e-at finalg)
  (nbe-make-object
   (make-arrow finalg (make-alg "boole"))
   (lambda (obj)
     (let ((val (nbe-object-to-value obj))
	   (reprod-obj (nbe-make-object
			(make-alg "boole")
			(nbe-make-termfam
			 (make-alg "boole")
			 (lambda (k)
			   (mk-term-in-app-form
			    (make-term-in-const-form
			     (finalg-to-e-const finalg))
			    (nbe-fam-apply (nbe-reify obj) k)))))))
       (cond
	((nbe-constr-value? val)
	 (let* ((args (nbe-constr-value-to-args val))
		(argtypes (map nbe-object-to-type args))
		(prevs
		 (do ((l args (cdr l))
		      (ltypes argtypes (cdr ltypes))
		      (res
		       '()
		       (let* ((arg (car l))
			      (type (car ltypes))
			      (prev (nbe-object-app (e-at type) arg)))
			 (if (trueval? (nbe-object-to-value prev))
			     res
			     (cons prev res)))))
		     ((null? l) res))))
	   (if (null? prevs)
	       trueobj
	       (do ((l (cdr prevs) (cdr l))
		    (obj
		     (car prevs)
		     (nbe-make-object
		      (make-alg "boole")
		      (nbe-make-termfam
		       (make-alg "boole")
		       (lambda (k)
			 (mk-term-in-app-form
			  (make-term-in-const-form
			   (pconst-name-to-pconst "AndConst"))
			  (nbe-fam-apply (nbe-reify (car l)) k)
			  (nbe-fam-apply (nbe-reify obj) k)))))))
		   ((null? l) obj)))))
	((and (nbe-fam-value? val) (synt-total? (nbe-extract val)))
	 trueobj)
	(else reprod-obj))))))

(define (sfinalg-to-se-const sfinalg)
  (if (not (sfinalg? sfinalg))
      (myerror "sfinalg-to-se-const"
	       "structure finitary algebra expected"
	       sfinalg)
      (make-const (se-at sfinalg)
		  "SE" 'fixed-rules
		  (make-arrow sfinalg (make-alg "boole")) empty-subst
		  1 'prefix-op)))

(define (se-at sfinalg)
  (nbe-make-object
   (make-arrow sfinalg (make-alg "boole"))
   (lambda (obj)
     (let ((val (nbe-object-to-value obj)))
       (cond
        ((nbe-constr-value? val)
         (let* ((alg-name (alg-form-to-name sfinalg))
                (alg-names (alg-name-to-simalg-names alg-name))
                (args (nbe-constr-value-to-args val))
                (argtypes (map nbe-object-to-type args))
                (prevs
                 (do ((l args (cdr l))
                      (ltypes argtypes (cdr ltypes))
                      (res
                       '()
                       (let* ((arg (car l))
                              (type (car ltypes))
                              (prev
                               (if (and (alg-form? type)
                                        (member (alg-form-to-name type)
                                                alg-names))
                                   (nbe-object-app (se-at type) arg)
                                   '())))
                         (if (or (null? prev)
                                 (trueval? (nbe-object-to-value prev)))
                             res
                             (cons prev res)))))
                     ((null? l) res))))
           (if (null? prevs)
               trueobj
               (do ((l (cdr prevs) (cdr l))
                    (obj
                     (car prevs)
                     (nbe-make-object
                      (make-alg "boole")
                      (nbe-make-termfam
                       (make-alg "boole")
                       (lambda (k)
                         (mk-term-in-app-form
                          (make-term-in-const-form
                           (pconst-name-to-const "AndConst"))
                          (nbe-fam-apply (nbe-reify (car l)) k)
                          (nbe-fam-apply (nbe-reify obj) k)))))))
                   ((null? l) obj)))))
        ((and (nbe-fam-value? val) (synt-total? (nbe-extract val)))
	 trueobj)
        ((nbe-fam-value? val) ;reproduce
         (nbe-make-object
          (make-alg "boole")
          (nbe-make-termfam
           (make-alg "boole")
           (lambda (k)
             (mk-term-in-app-form
              (make-term-in-const-form
               (sfinalg-to-se-const sfinalg))
              (nbe-fam-apply (nbe-reify obj) k))))))
        (else (myerror "se-at" "value expected" val)))))))

;; The pconst "Inhab" is a constscheme providing a canonical inhabitant
;; of an arbitrary type alpha.  It can be given a concrete value.
;; Example: (add-computation-rules "(Inhab boole)" "False")

(add-program-constant "Inhab" (py "alpha"))

;; Type product and type sum as algebras with parameters

(add-algs "yprod" 'prod-typeop '("alpha1=>alpha2=>yprod" "PairConstr"))

;; The treatment is similar as in lib/list.scm, but with two parameter
;; types rather than one.  Since the two argument types are left open,
;; we have a polymorphic type here.  It is called a record since it is
;; an algebra with one constructor only.  Notice that rationals and
;; reals are record types with two fields as well, but with fixed
;; argument types.  One could treat triples, quadruples etc similarly.

;; (pp (pt "(PairConstr boole boole)boole1 boole2"))

(add-token
 "pair" 'pair-op ;hence right associative
 (lambda (x1 x2)
   (let ((type1 (term-to-type x1))
	 (type2 (term-to-type x2)))
     (mk-term-in-app-form
      (make-term-in-const-form
       (let* ((constr (constr-name-to-constr "PairConstr"))
	      (tvars (const-to-tvars constr))
	      (subst (make-substitution tvars (list type1 type2))))
	 (const-substitute constr subst #f)))
      x1 x2))))

;; (pp (pt "boole1 pair boole2"))

(add-display
 (py "alpha1 yprod alpha2")
 (lambda (x)
   (if (term-in-app-form? x)
       (let ((op (term-in-app-form-to-final-op x))
	     (args (term-in-app-form-to-args x)))
	 (if (and (term-in-const-form? op)
		  (string=? "PairConstr"
			    (const-to-name (term-in-const-form-to-const op)))
		  (= 2 (length args)))
	     (list 'pair-op "pair"
		   (term-to-token-tree (car args))
		   (term-to-token-tree (cadr args)))
	     #f))
       #f)))

;; (pp (pt "boole1 pair boole2"))
;; (pp (pt "boole1 pair(boole2 pair boole3)"))
;; (pp (pt "(boole1 pair boole2)pair boole3"))
;; (pp (pt "boole1@(boole2@boole3)"))
;; (pp (pt "(boole1@boole2)@ boole3"))

;; To access the two fields of a pair, we provide lft and rht as names
;; to be used (prefix) in display strings.

(add-program-constant "PairOne" (py "alpha1 yprod alpha2=>alpha1"))

;; (pp (pt "(PairOne boole boole)(boole1 pair boole2)"))

(add-token
 "lft"
 'prefix-op
 (lambda (x) (make-term-in-app-form
	      (make-term-in-const-form
	       (let* ((const (pconst-name-to-pconst "PairOne"))
		      (tvars (const-to-tvars const))
		      (pairtype (term-to-type x))
		      (types (alg-form-to-types pairtype))
		      (subst (make-substitution tvars types)))
		 (const-substitute const subst #f)))
	      x)))

;; (pp (pt "lft(boole1 pair boole2)"))

(add-display
 (py "alpha")
 (lambda (x)
   (if (term-in-app-form? x)
       (let ((op (term-in-app-form-to-final-op x))
	     (args (term-in-app-form-to-args x)))
	 (if (and (term-in-const-form? op)
		  (string=? "PairOne"
			    (const-to-name (term-in-const-form-to-const op)))
		  (= 1 (length args)))
	     (list 'prefix-op "lft" (term-to-token-tree (car args)))
	     #f))
       #f)))

;; (pp (pt "lft(boole1 pair boole2)"))

;; (add-computation-rule "lft(alpha1 pair alpha2)" "alpha1")

;; (pp (nt (pt "lft(boole1 pair boole2)")))

(add-program-constant "PairTwo" (py "alpha1 yprod alpha2=>alpha2"))

;; (pp (pt "(PairTwo boole boole)(boole1 pair boole2)"))

(add-token
 "rht"
 'prefix-op
 (lambda (x) (make-term-in-app-form
	      (make-term-in-const-form
	       (let* ((const (pconst-name-to-pconst "PairTwo"))
		      (tvars (const-to-tvars const))
		      (pairtype (term-to-type x))
		      (types (alg-form-to-types pairtype))
		      (subst (make-substitution tvars types)))
		 (const-substitute const subst #f)))
	      x)))

;; (pp (pt "rht(boole1 pair boole2)"))

(add-display
 (py "alpha")
 (lambda (x)
   (if (term-in-app-form? x)
       (let ((op (term-in-app-form-to-final-op x))
	     (args (term-in-app-form-to-args x)))
	 (if (and (term-in-const-form? op)
		  (string=? "PairTwo"
			    (const-to-name (term-in-const-form-to-const op)))
		  (= 1 (length args)))
	     (list 'prefix-op "rht" (term-to-token-tree (car args)))
	     #f))
       #f)))

;; (pp (pt "rht(boole1 pair boole2)"))

;; (add-computation-rule "rht(alpha1 pair alpha2)" "alpha2")

;; (pp (nt (pt "rht(boole1 pair boole2)")))

(define (make-term-in-cons-form term1 term2)
  (mk-term-in-app-form
    (make-term-in-const-form
     (let* ((constr (constr-name-to-constr "PairConstr"))
	    (tvars (const-to-tvars constr))
	    (type1 (term-to-type term1))
	    (type2 (term-to-type term2))
	    (subst (make-substitution tvars (list type1 type2))))
       (const-substitute constr subst #f)))
    term1 term2))

;; (pp (make-term-in-cons-form (pt "True") (pt "False")))

(define (mk-term-in-cons-form term . rest)
  (if (null? rest)
      term
      (make-term-in-cons-form
       term
       (apply mk-term-in-cons-form rest))))

;; (pp (mk-term-in-cons-form (pt "True") (pt "False") (pt "False")))

(define (term-in-cons-form? term)
  (let ((op (term-in-app-form-to-final-op term))
	(args (term-in-app-form-to-args term)))
    (and (term-in-const-form? op)
	 (string=? "PairConstr"
		   (const-to-name (term-in-const-form-to-const op)))
	 (= 2 (length args)))))

(define (term-in-cons-form-to-left term)
  (let ((args (term-in-app-form-to-args term)))
    (if (pair? args)
	(car args)
	(myerror "term-in-cons-form-to-left" "term in cons form expected"
		 term))))

;; (pp (term-in-cons-form-to-left (pt "True pair False")))
;; True

(define (term-in-cons-form-to-right term)
  (let ((args (term-in-app-form-to-args term)))
    (if (= 2 (length args))
	(cadr args)
	(myerror "term-in-cons-form-to-right" "term in cons form expected"
		 term))))

;; (pp (term-in-cons-form-to-right (pt "True pair False")))
;; False

(define (make-term-in-car-form term)
  (make-term-in-app-form
   (make-term-in-const-form
     (let* ((const (pconst-name-to-pconst "PairOne"))
	    (tvars (const-to-tvars const))
	    (type (term-to-type term))
	    (types (if (and (alg-form? type)
			    (string=? "yprod" (alg-form-to-name type)))
		       (alg-form-to-types type)
		       (myerror "make-term-in-car-form"
				"term of product type expected" term)))
	    (subst (make-substitution tvars types)))
       (const-substitute const subst #f)))
   term))

;; (pp (make-term-in-car-form (pt "True pair False")))
;; lft(True pair False)

;; (pp (nt (make-term-in-car-form (pt "True pair False"))))
;; True

(define (make-term-in-cdr-form term)
  (make-term-in-app-form
   (make-term-in-const-form
     (let* ((const (pconst-name-to-pconst "PairTwo"))
	    (tvars (const-to-tvars const))
	    (type (term-to-type term))
	    (types (if (yprod-form? type)
		       (alg-form-to-types type)
		       (myerror "make-term-in-cdr-form"
				"term of product type expected" term)))
	    (subst (make-substitution tvars types)))
       (const-substitute const subst #f)))
   term))

;; (pp (make-term-in-cdr-form (pt "True pair False")))
;; rht(True pair False)

;; (pp (nt (make-term-in-cdr-form (pt "True pair False"))))
;; False

(define (term-to-components term . opt-nonneg-integer)
  (let ((type (term-to-type term)))
    (if
     (null? opt-nonneg-integer)
     (cond
      ((star-form? type)
       (let ((left (if (term-in-pair-form? term)
		       (term-in-pair-form-to-left term)
		       (make-term-in-lcomp-form term)))
	     (right (if (term-in-pair-form? term)
			(term-in-pair-form-to-right term)
			(make-term-in-rcomp-form term))))
	 (cons left (term-to-components right))))
      ((yprod-form? type)
       (let ((left (if (term-in-cons-form? term)
		       (term-in-cons-form-to-left term)
		       (make-term-in-car-form term)))
	     (right (if (term-in-cons-form? term)
			(term-in-cons-form-to-right term)
			(make-term-in-cdr-form term))))
	 (cons left (term-to-components right))))
      (else (list term)))
     (let ((n (car opt-nonneg-integer)))
       (cond
	((zero? n) '())
	((= 1 n) (list term))
	((and (integer? n) (< 1 n))
	 (cond
	  ((star-form? type)
	   (let ((left (if (term-in-pair-form? term)
			   (term-in-pair-form-to-left term)
			   (make-term-in-lcomp-form term)))
		 (right (if (term-in-pair-form? term)
			    (term-in-pair-form-to-right term)
			    (make-term-in-rcomp-form term))))
	     (cons left (term-to-components right (- n 1)))))
	  ((yprod-form? type)
	   (let ((left (if (term-in-cons-form? term)
			   (term-in-cons-form-to-left term)
			   (make-term-in-car-form term)))
		 (right (if (term-in-cons-form? term)
			    (term-in-cons-form-to-right term)
			    (make-term-in-cdr-form term))))
	     (cons left (term-to-components right (- n 1)))))
	  (else (myerror "term-to-components"
			 "term of product type expected" term))))
	(else (myerror "term-to-components"
		       "non-negative integer expected" n)))))))

;; (for-each pp (term-to-components (pt "True pair False pair True")))
;; (for-each pp (term-to-components (pt "True pair False pair True") 3))
;; (for-each pp (term-to-components (pt "True pair False pair True") 2))

;; Constructor, accessors and test for the type product operator yprod.

(define (make-yprod type1 type2) (make-alg "yprod" type1 type2))

;; The following is for correspondence with star, but probably not needed.

(define (yprod-form-to-left-type yprod-type)
  (car (alg-form-to-types yprod-type)))

(define (yprod-form-to-right-type yprod-type)
  (cadr (alg-form-to-types yprod-type)))

(define (yprod-form? x)
  (and (alg-form? x)
       (string=? "yprod" (alg-form-to-name x))
       (= 2 (length (alg-form-to-types x)))))

(define (mk-yprod . x)
  (cond ((null? x) (make-alg "unit"))
	((null? (cdr x)) (car x))
	(else (make-yprod (car x) (apply mk-yprod (cdr x))))))

;; (pp (mk-yprod (py "alpha1") (py "alpha2") (py "alpha3")))
;; alpha1 yprod alpha2 yprod alpha3

(define (yprod-form? type)
  (and (alg-form? type) (string=? "yprod" (alg-form-to-name type))))

;; Now the sum type operator:

(add-algs "ysum" 'sum-typeop '("alpha1=>ysum" "InL") '("alpha2=>ysum" "InR"))

;; We do not simplify the display "(InL rho sigma)r", since the type
;; sigma cannot be inferred from r.

;; Constructor, accessors and test for the type sum operator ysum.

(define (make-ysum type1 type2) (make-alg "ysum" type1 type2))

;; The following is for correspondence with star, but probably not needed.

(define (ysum-form-to-left-type ysum-type)
  (car (alg-form-to-types ysum-type)))

(define (ysum-form-to-right-type ysum-type)
  (cadr (alg-form-to-types ysum-type)))

(define (ysum-form? x)
  (and (alg-form? x)
       (string=? "ysum" (alg-form-to-name x))
       (= 2 (length (alg-form-to-types x)))))

(define (mk-ysum x . rest)
  (if (null? rest)
      x
      (make-ysum x (apply mk-ysum rest))))

(define (make-uysum type) (make-alg "uysum" type))

(add-algs "uysum" 'prefix-typeop
	  '("DummyL" "uysum")
	  '("InrUysum" "alpha1=>uysum"))

(add-prefix-display-string "InrUysum" "Inr")

;; (pp (py "uysum boole"))
;; (pp (pt "Inr boole"))
;; (pp (term-to-type (pt "Inr boole")))
;; (pp (pt "(DummyL boole)"))
;; (pp (term-to-type (pt "(DummyL boole)")))

(add-algs "ysumu" 'postfix-typeop
	  '("InlYsumu" "alpha1=>ysumu")
	  '("DummyR" "ysumu"))

(add-prefix-display-string "InlYsumu" "Inl")

;; (pp (py "boole ysumu"))
;; (pp (pt "Inl boole"))
;; (pp (term-to-type (pt "Inl boole")))
;; (pp (pt "(DummyR boole)"))
;; (pp (term-to-type (pt "(DummyR boole)")))

(define (make-ysumu type) (make-alg "ysumu" type))

(define (mk-ysum-without-unit type . rest)
  (if (null? rest)
      type
      (if (and (alg-form? type) (string=? "unit" (alg-form-to-name type)))
	  (if (and (= 1 (length rest))
		   (alg-form? (car rest))
		   (string=? "unit" (alg-form-to-name (car rest))))
	      (make-alg "boole")
	      (make-alg "uysum" (apply mk-ysum-without-unit rest)))
	  (if (and (= 1 (length rest))
		   (alg-form? (car rest))
		   (string=? "unit" (alg-form-to-name (car rest))))
	      (make-alg "ysumu" type)
	      (make-ysum type (apply mk-ysum-without-unit rest))))))

;; (pp (mk-ysum-without-unit (py "unit") (py "alpha")))
;; uysum alpha

(define (ysum-without-unit-to-components type . opt-nonneg-integer)
  (if
   (null? opt-nonneg-integer)
   (cond
    ((and (alg-form? type) (string=? "ysum" (alg-form-to-name type)))
     (cons (car (alg-form-to-types type))
	   (ysum-without-unit-to-components (cadr (alg-form-to-types type)))))
    ((and (alg-form? type) (string=? "uysum" (alg-form-to-name type)))
     (cons (make-alg "unit")
	   (ysum-without-unit-to-components (car (alg-form-to-types type)))))
    ((and (alg-form? type) (string=? "ysumu" (alg-form-to-name type)))
     (append (ysum-without-unit-to-components (car (alg-form-to-types type)))
	     (list (make-alg "unit"))))
    ((and (alg-form? type) (string=? "boole" (alg-form-to-name type)))
     (list (make-alg "unit") (make-alg "unit")))
    ((and (alg-form? type) (string=? "unit" (alg-form-to-name type)))
     (list (make-alg "unit")))
    (else (list type)))
   (let ((n (car opt-nonneg-integer)))
     (cond
      ((zero? n) '())
      ((= 1 n) (list type))
      ((and (integer? n) (< 1 n))
       (cond
	((and (alg-form? type) (string=? "ysum" (alg-form-to-name type)))
	 (cons (car (alg-form-to-types type))
	       (ysum-without-unit-to-components
		(cadr (alg-form-to-types type))
		(- n 1))))
	((and (alg-form? type) (string=? "uysum" (alg-form-to-name type)))
	 (cons (make-alg "unit")
	       (ysum-without-unit-to-components
		(car (alg-form-to-types type))
		(- n 1))))
	((and (alg-form? type) (string=? "ysumu" (alg-form-to-name type)))
	 (append (ysum-without-unit-to-components
		  (car (alg-form-to-types type))
		  (- n 1))
		 (list (make-alg "unit"))))
	((and (alg-form? type) (string=? "boole" (alg-form-to-name type)))
	 (list (make-alg "unit") (make-alg "unit")))
	((and (alg-form? type) (string=? "unit" (alg-form-to-name type)))
	 (list (make-alg "unit")))
	(else (myerror "ysum-without-unit-to-components"
		       "ysum or algOr or boole or unit expected" type))))
      (else (myerror "ysum-without-unit-to-components"
		     "non-negative integer expected" n))))))

;; (for-each pp (ysum-without-unit-to-components (py "uysum alpha")))
;; unit
;; alpha

;; In make-injection n is a non-negative integer

(define (make-injection ysum-without-unit n)
  (if (not (alg-form? ysum-without-unit))
      (myerror "make-injection" "algebra form expected" ysum-without-unit))
  (let ((name (alg-form-to-name ysum-without-unit)))
    (if (not (or (string=? "ysum" name)
		 (string=? "uysum" name)
		 (string=? "ysumu" name)
		 (string=? "boole" name)))
	(myerror "make-injection" "composed algebra expected"
		 ysum-without-unit))
    (cond
     ((string=? "boole" name)
      (cond
       ((zero? n) (make-term-in-const-form true-const))
       ((= 1 n) (make-term-in-const-form false-const))
       (else (myerror "make-injection" "0 or 1 expected" n))))
     ((string=? "uysum" name)
      (let* ((right-type (car (alg-form-to-types ysum-without-unit)))
	     (inl-constr (constr-name-to-constr "DummyL"))
	     (inr-constr (constr-name-to-constr "InrUysum"))
	     (tvars (alg-name-to-tvars "uysum"))
	     (tsubst (make-substitution tvars (list right-type)))
	     (subst-inl-constr (const-substitute inl-constr tsubst #t))
	     (subst-inr-constr (const-substitute inr-constr tsubst #t))
	     (left-dummy (make-term-in-const-form subst-inl-constr))
	     (right-injection (make-term-in-const-form subst-inr-constr)))
	(cond
	 ((zero? n) left-dummy)
	 ((and (= 1 n) ;and right-type atomic
	       (not (and (alg-form? right-type)
			 (member (alg-form-to-name right-type)
				 '("ysum" "uysum" "ysumu" "boole")))))
	  right-injection)
	 (else (compose-or-apply
		right-injection (make-injection right-type (- n 1)))))))
     ((string=? "ysumu" name)
      (let* ((left-type (car (alg-form-to-types ysum-without-unit)))
	     (inl-constr (constr-name-to-constr "InlYsumu"))
	     (inr-constr (constr-name-to-constr "DummyR"))
	     (tvars (alg-name-to-tvars "ysumu"))
	     (tsubst (make-substitution tvars (list left-type)))
	     (subst-inl-constr (const-substitute inl-constr tsubst #t))
	     (subst-inr-constr (const-substitute inr-constr tsubst #t))
	     (left-injection (make-term-in-const-form subst-inl-constr))
	     (right-dummy (make-term-in-const-form subst-inr-constr)))
	(cond
	 ((and (zero? n) ;and left-type atomic
	       (not (and (alg-form? left-type)
			 (member (alg-form-to-name left-type)
				 '("ysum" "uysum" "ysumu" "boole")))))
	  left-injection)
	 ((= 1 n) right-dummy)
	 (else (compose-or-apply
		left-injection (make-injection left-type 0))))))
     ((string=? "ysum" name)
      (let* ((left-type (ysum-form-to-left-type ysum-without-unit))
	     (right-type (ysum-form-to-right-type ysum-without-unit))
	     (inl-constr (constr-name-to-constr "InL"))
	     (inr-constr (constr-name-to-constr "InR"))
	     (tvars (alg-name-to-tvars "ysum"))
	     (tsubst (make-substitution tvars (list left-type right-type)))
	     (subst-inl-constr (const-substitute inl-constr tsubst #t))
	     (subst-inr-constr (const-substitute inr-constr tsubst #t))
	     (left-injection (make-term-in-const-form subst-inl-constr))
	     (right-injection (make-term-in-const-form subst-inr-constr)))
	(cond
	 ((zero? n) left-injection)
	 ((and (= 1 n) ;and right-type atomic
	       (not (and (alg-form? right-type)
			 (member (alg-form-to-name right-type)
				 '("ysum" "uysum" "ysumu" "boole")))))
	  right-injection)
	 (else (compose-or-apply
		right-injection (make-injection right-type (- n 1)))))))
     (else (myerror "make-injection" "unexpected type" ysum-without-unit)))))

(define (compose-or-apply term1 term2)
  (let* ((type1 (term-to-type term1))
	 (type2 (term-to-type term2)))
    (if (not (arrow-form? type1))
	(myerror "compose-or-apply" "type in arrow form expected" type1
		 "for term" term1))
    (cond
     ((and (arrow-form? type2)
	   (equal? (arrow-form-to-val-type type2)
		   (arrow-form-to-arg-type type1)))
					;compose
      (let ((var (type-to-new-var (arrow-form-to-arg-type type2))))
	(make-term-in-abst-form
	 var (make-term-in-app-form
	      term1 (make-term-in-app-form
		     term2 (make-term-in-var-form var))))))
     ((equal? type2 (arrow-form-to-arg-type type1))
					;apply
      (make-term-in-app-form term1 term2))
     (else (myerror "compose-or-apply"
		    "composable of applicable types expected" type1 type2
		    "for terms" term1 term2)))))

;; (pp (make-injection (py "alpha1 ysum alpha2") 0))
;; (InL alpha1 alpha2)

;; (pp (make-injection (py "alpha1 ysum alpha2") 1))
;; (InR alpha2 alpha1)



