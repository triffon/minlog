;; $Id: etsd.scm 2670 2014-01-08 09:57:57Z schwicht $
;; Extracted terms for the Dialectica interpretation
;; =================================================

(define (formula-to-etdp-type formula)
  (car (formula-to-etd-types formula)))

(define (formula-to-etdn-type formula)
  (cadr (formula-to-etd-types formula)))

(define (formula-to-etd-types formula)
  (case (tag formula)
    ((atom) (list (make-tconst "nulltype") (make-tconst "nulltype")))
    ((predicate)
     (let ((pred (predicate-form-to-predicate formula)))
       (cond ((pvar-form? pred)
	      (list (if (pvar-with-positive-content? pred)
			(PVAR-TO-TVARP pred)
			(make-tconst "nulltype"))
		    (if (pvar-with-negative-content? pred)
			(PVAR-TO-TVARN pred)
			(make-tconst "nulltype"))))
	     ((predconst-form? pred)
	      (list (make-tconst "nulltype") (make-tconst "nulltype")))
	     ((idpredconst-form? pred)
	      (myerror "formula-to-etd-types"
		       "not implemented for idpredconst" pred))
	     (else (myerror
		    "formula-to-etd-types" "predicate expected" pred)))))
    ((imp impnc)
     (let* ((prev-prem (formula-to-etd-types
			(imp-impnc-form-to-premise formula)))
	    (prev-conc (formula-to-etd-types
			 (imp-impnc-form-to-conclusion formula)))
	    (etdp-type-prem (car prev-prem))
	    (etdn-type-prem (cadr prev-prem))
	    (etdp-type-conc (car prev-conc))
	    (etdn-type-conc (cadr prev-conc)))
       (list (make-star-et
	      (make-arrow-et etdp-type-prem etdp-type-conc)
	      (mk-arrow-et etdp-type-prem etdn-type-conc etdn-type-prem))
	     (make-star-et etdp-type-prem etdn-type-conc))))
    ((and)
     (let* ((prev-left (formula-to-etd-types (and-form-to-left formula)))
	    (prev-right (formula-to-etd-types (and-form-to-right formula)))
	    (etdp-type-left (car prev-left))
	    (etdn-type-left (cadr prev-left))
	    (etdp-type-right (car prev-right))
	    (etdn-type-right (cadr prev-right)))
       (list (make-star-et etdp-type-left etdp-type-right)
	     (make-star-et etdn-type-left etdn-type-right))))
    ((all)
     (let* ((type (var-to-type (all-form-to-var formula)))
	    (prev-kernel (formula-to-etd-types (all-form-to-kernel formula)))
	    (etdp-type-kernel (car prev-kernel))
	    (etdn-type-kernel (cadr prev-kernel)))
       (list (make-arrow-et type etdp-type-kernel)
	     (make-star-et type etdn-type-kernel))))
    ((ex)
     (let* ((type (var-to-type (ex-form-to-var formula)))
	    (prev-kernel (formula-to-etd-types (ex-form-to-kernel formula)))
	    (etdp-type-kernel (car prev-kernel))
	    (etdn-type-kernel (cadr prev-kernel)))
       (list (make-star-et type etdp-type-kernel)
	     etdn-type-kernel)))
    ((allnc) (formula-to-etd-types (allnc-form-to-kernel formula)))
    ((exca excl) (formula-to-etd-types (unfold-formula formula)))
    (else (myerror "formula-to-etd-types" "formula expected" formula))))

;; Often we have to check whether a formula has positive or negative
;; computational content.  This can be done without computing its
;; etd-types, by using formula-of-nulltypep? and formula-of-nulltypen?
;; (defined in term.scm).

;; make-pvar-to-d-pvar returns a procedure associating Dialectica pvars
;; to predicate variables.  Remembers the assignment done so far.

(define (make-pvar-to-d-pvar)
  (let ((assoc-list '()))
    (lambda (pvar)
      (define (add-etd-type test pvar-to-tvar)
	(lambda (x)
	  (if (test pvar)
	      (cons (pvar-to-tvar pvar) x)
	      x)))
      (let ((info (assoc pvar assoc-list)))
	(if info
	    (cadr info)
	    (let* ((add-etdp-type
		    (add-etd-type pvar-with-positive-content? PVAR-TO-TVARP))
		   (add-etdn-type
		    (add-etd-type pvar-with-negative-content? PVAR-TO-TVARN))
		   (arity (pvar-to-arity pvar))
		   (types (arity-to-types arity))
		   (newarity
		    (apply make-arity (add-etdp-type (add-etdn-type types))))
		   (newpvar (arity-to-new-pvar newarity)))
	      (set! assoc-list (cons (list pvar newpvar) assoc-list))
	      newpvar))))))

;; formula-to-d-formula calculates the dialectica translation of a formula

(define (formula-to-d-formula formula)
  (define (make-let make-quant type)
    (lambda (k)
      (if (nulltype? type)
	  (k 'eps (lambda (f) f))
	  (let ((var (type-to-new-var type)))
	    (k (make-term-in-var-form var) (lambda (f) (make-quant var f)))))))
  (let* ((pvar-to-d-pvar (make-pvar-to-d-pvar))
	 (types (formula-to-etd-types formula))
	 (typep (car types))
	 (typen (cadr types))
	 (letp (make-let make-ex typep))
	 (letn (make-let make-all typen)))
    (letp (lambda (real add-ex)
	    (letn (lambda (chal add-all)
		    (add-ex
		     (add-all (real-and-chal-and-formula-to-d-formula-aux
			       real chal formula pvar-to-d-pvar)))))))))

;; (pp (formula-to-d-formula (pf "ex boole1 all boole2 boole1=boole2")))
;; (pp (formula-to-d-formula (pf "all boole1 ex boole2 boole1=boole2")))
;; (pp (formula-to-d-formula (pf "all nat1 exca nat2 nat1<nat2")))

(define (real-and-chal-and-formula-to-d-formula real chal formula)
  (let* ((pvar-to-var (make-pvar-to-var))
	 (types (formula-to-etd-types formula))
	 (typep (car types))
	 (typen (cadr types)))
    (if (not (or (and (eq? 'eps real) (nulltype? typep))
		 (and (term-form? real) (equal? (term-to-type real) typep))))
	(myerror "real-and-chal-and-formula-to-d-formula"
		 "equal types expected"
		 (if (term-form? real) (term-to-type real) real)
		 typep))
    (if (not (or (and (eq? 'eps chal) (nulltype? typen))
		 (and (term-form? chal) (equal? (term-to-type chal) typen))))
	(myerror "real-and-chal-and-formula-to-d-formula"
		 "equal types expected"
		 (if (term-form? chal) (term-to-type chal) chal)
		 typen))
    (real-and-chal-and-formula-to-d-formula-aux real chal formula
						pvar-to-var)))

(define (real-and-chal-and-formula-to-d-formula-aux real chal formula
						    pvar-to-d-pvar)
  (case (tag formula)
    ((atom) formula)
    ((predicate)
     (let ((pred (predicate-form-to-predicate formula))
	   (args (predicate-form-to-args formula)))
       (if
	(pvar-form? pred)
	(let* ((make-add (lambda (content? term)
			   (lambda (x) (if (content? pred) (cons term x) x))))
	       (add-real (make-add pvar-with-positive-content? real))
	       (add-chal (make-add pvar-with-negative-content? chal))
	       (new-pvar (pvar-to-d-pvar pred)))
	  (apply make-predicate-formula
		 (cons new-pvar (add-real (add-chal args)))))
	formula)))
    ((imp impnc)
     (let* ((prem (imp-impnc-form-to-premise formula))
	    (conc (imp-impnc-form-to-conclusion formula))
	    (p1? (formula-of-nulltypep? prem))
	    (n1? (formula-of-nulltypen? prem))
	    (p2? (formula-of-nulltypep? conc))
	    (n2? (formula-of-nulltypen? conc))
	    (real1
	     (if p1? 'eps (if n2? chal (make-term-in-lcomp-form chal)))) ;x
	    (chal2
	     (if n2? 'eps (if p1? chal (make-term-in-rcomp-form chal)))) ;u
	    (real-l
	     (if p2? 'eps (if n1? real (make-term-in-lcomp-form real)))) ;f
	    (real-r
	     (if n1? 'eps (if p2? real (make-term-in-rcomp-form real)))) ;g
	    (chal1 (mk-term-in-app-form-et real-r real1 chal2)) ;gxu
	    (real2 (mk-term-in-app-form-et real-l real1))) ;fx
       (make-imp (real-and-chal-and-formula-to-d-formula-aux
		  real1 chal1 prem pvar-to-d-pvar)
		 (real-and-chal-and-formula-to-d-formula-aux
		  real2 chal2 conc pvar-to-d-pvar))))
    ((and)
     (let* ((left (and-form-to-left formula))
	    (right (and-form-to-right formula))
	    (p1? (formula-of-nulltypep? left))
	    (n1? (formula-of-nulltypen? left))
	    (p2? (formula-of-nulltypep? right))
	    (n2? (formula-of-nulltypen? right))
	    (real1 (if p1? 'eps (if p2? real (make-term-in-lcomp-form real))))
	    (chal1 (if n1? 'eps (if n2? chal (make-term-in-lcomp-form chal))))
	    (real2 (if p2? 'eps (if p1? real (make-term-in-rcomp-form real))))
	    (chal2 (if n2? 'eps (if n1? chal (make-term-in-rcomp-form chal)))))
       (make-and (real-and-chal-and-formula-to-d-formula-aux
		  real1 chal1 left pvar-to-d-pvar)
		 (real-and-chal-and-formula-to-d-formula-aux
		  real2 chal2 right pvar-to-d-pvar))))
    ((all)
     (let* ((var (all-form-to-var formula))
	    (kernel (all-form-to-kernel formula))
	    (p? (formula-of-nulltypep? kernel))
	    (n? (formula-of-nulltypen? kernel))
	    (new-term (if n? chal (make-term-in-lcomp-form chal)))
	    (new-chal (if n? 'eps (make-term-in-rcomp-form chal)))
	    (new-real (if p? 'eps (make-term-in-app-form real new-term)))
	    (new-kernel (formula-subst kernel var new-term)))
       (real-and-chal-and-formula-to-d-formula-aux
	new-real new-chal new-kernel pvar-to-d-pvar)))
    ((ex)
     (let* ((var (ex-form-to-var formula))
	    (kernel (ex-form-to-kernel formula))
	    (p? (formula-of-nulltypep? kernel))
	    (new-real (if p? 'eps (make-term-in-rcomp-form real)))
	    (new-term (if p? real (make-term-in-lcomp-form real)))
	    (new-kernel (formula-subst kernel var new-term)))
       (real-and-chal-and-formula-to-d-formula-aux
	new-real chal new-kernel pvar-to-d-pvar)))
    ((allnc)
     (let ((var (allnc-form-to-var formula))
	   (kernel (allnc-form-to-kernel formula)))
       (make-all var (real-and-chal-and-formula-to-d-formula-aux
		      real chal kernel pvar-to-d-pvar))))
    ((exca excl)
     (real-and-chal-and-formula-to-d-formula-aux
      real chal (unfold-formula formula) pvar-to-d-pvar))
    (else (myerror "real-and-chal-and-formula-to-d-formula-aux"
		   "formula expected"
		   formula))))

;; We assign to a proof M a term [M]^+ (real) and an alist associating
;; terms to avars: u_i mapsto [M]^-_i (chals).  All these terms may
;; contain the x_u_i's free, and in addition the [M]^-_i may contain y
;; free.  Here the x_u_i's are given by a local variable
;; avar-of-typep-to-var, and y is given by a local variable
;; formula-of-typen-to-var.  x_u_i has typep of the assumed formula,
;; and y has typen of the goal formula.

;; Notice that because of the use of pvar-to-d-pvar (rather than
;; pvar-to-var) we cannot in general build terms from formulas when
;; contracting.  At this point we need to substitute formulas for the
;; pvars.

(define (make-avar-of-typep-to-var)
					;returns a procedure assigning to
					;assumption variables new object vars
					;of the corresponding etdp-type.
					;Remembers the assignment done so far.
  (let ((avar-assoc-list '()))
    (lambda (avar)
      (let ((info (assoc-wrt avar=? avar avar-assoc-list)))
	(if info
	    (cadr info)
	    (let* ((formula (avar-to-formula avar))
		   (type (formula-to-etdp-type formula))
		   (new-var (type-to-new-var type)))
	      (begin (set! avar-assoc-list
			   (cons (list avar new-var) avar-assoc-list))
		     new-var)))))))

(define (make-formula-of-typen-to-var)
					;returns a procedure assigning
					;to formulas new object vars
					;of the corresponding
					;of the corresponding etdp-type.
					;Remembers the assignment done so far.
  (let ((formula-assoc-list '()))
    (lambda (formula)
      (let ((info (assoc-wrt classical-formula=? formula formula-assoc-list)))
	(if info
	    (cadr info)
	    (let* ((typen (formula-to-etdn-type formula))
		   (new-var (type-to-new-var typen)))
	      (begin (set! formula-assoc-list
			   (cons (list formula new-var) formula-assoc-list))
		     new-var)))))))

;; proof-without-d-real-or-chals? checks whether the proof is
;; Dialectica irrelevant, i.e., neither a realiser nor challenges can
;; be extracted.

(define (proof-without-d-real-or-chals? proof)
  (let* ((formula (proof-to-formula proof))
	 (context (proof-to-context proof))
	 (avars (context-to-avars context)))
    (and (formula-of-nulltypep? formula)
	 (check-all
	  (lambda (avar) (formula-of-nulltypen? (avar-to-formula avar)))
	  avars))))

(define (proof-to-extracted-d-term proof)
  (let ((avars (proof-to-free-avars proof)))
    (if (pair? avars)
	(apply myerror (append (list "proof-to-extracted-d-term"
				     "proof contains free assumptions")
			       (map car avars)))
	(car (proof-to-extracted-d-terms proof)))))

;; proof-to-extracted-d-terms returns the extracted realiser and a list
;; of extracted challenges labelled with their avars.

(define (proof-to-extracted-d-terms proof)
  (let ((avar-of-typep-to-var (make-avar-of-typep-to-var))
	(formula-of-typen-to-var (make-formula-of-typen-to-var))
	(pvar-to-d-pvar (make-pvar-to-d-pvar)))
    (proof-to-extracted-d-terms-aux
     (rm-falsity-log proof)
     avar-of-typep-to-var formula-of-typen-to-var pvar-to-d-pvar)))

;; The following functions do for terms what make-arrow-et etc (in
;; ets.scm) do for types.  Probably they would be helpful in ets.scm as
;; well.

(define (make-term-in-pair-form-et term-or-eps1 term-or-eps2)
  (if (eq? term-or-eps1 'eps)
      term-or-eps2
      (if (eq? term-or-eps2 'eps)
	  term-or-eps1
	  (make-term-in-pair-form term-or-eps1 term-or-eps2))))

(define (make-term-in-abst-form-et var term)
  (mk-term-in-abst-form-et var term))

(define (mk-term-in-abst-form-et x . rest)
  (if (null? rest)
      x
      (let ((term (apply mk-term-in-abst-form-et rest)))
	(if (eq? term 'eps)
	    'eps
	    (if x
		(make-term-in-abst-form x term)
		term)))))

(define (make-term-in-app-form-et term1 term2)
  (mk-term-in-app-form-et term1 term2))

(define (mk-term-in-app-form-et x . rest)
  (if (null? rest)
      x
      (if (eq? x 'eps)
	  'eps
	  (let ((term (if (eq? 'eps (car rest))
			  x
			  (mk-term-in-app-form x (car rest)))))
	    (apply mk-term-in-app-form-et (cons term (cdr rest)))))))

(define (mk-term-in-pair-form-et x . rest)
  (if (null? rest)
      x
      (make-term-in-pair-form-et
       x (apply mk-term-in-pair-form-et rest))))

(define (cons-true x l)
  (if x (cons x l) l))

(define (term-of-star-type-to-projs term n)
  (if (= 1 n) (list term)
      (let ((left (if (term-in-pair-form? term)
		      (term-in-pair-form-to-left term)
		      (make-term-in-lcomp-form term)))
	    (right (if (term-in-pair-form? term)
		       (term-in-pair-form-to-right term)
		       (make-term-in-rcomp-form term))))
	(cons left (term-of-star-type-to-projs right (- n 1))))))

(define (make-term-in-app-form-wrt-iterated-pairs op arg n)
  (if
   (= 1 n) (make-term-in-app-form op arg)
   (if
    (or (not ETSD-LET-ENABLED) (term-is-inappropriate-for-let? arg)
	(term-is-inappropriate-for-let? (nt arg)))
    (apply mk-term-in-app-form (cons op (term-of-star-type-to-projs arg n)))
    (let* ((x (type-to-new-var (term-to-type arg)))
	   (xterm (make-term-in-var-form x))
	   (xprojs (term-of-star-type-to-projs xterm n))
	   (cId-const (pconst-name-to-pconst "cId"))
	   (cId-term
	    (make-term-in-const-form
	     (let* ((tvars (const-to-tvars cId-const))
		    (tsubst
		     (make-substitution
		      tvars (list (make-arrow (var-to-type x)
					      (arrow-form-to-final-val-type
					       (term-to-type op) n))))))
	       (const-substitute cId-const tsubst #f)))))
      (mk-term-in-app-form
       cId-term
       (make-term-in-abst-form
	x (apply mk-term-in-app-form (cons op xprojs)))
       arg)))))

(define (proof-to-extracted-d-terms-aux-check-result proof
						     avar-of-typep-to-var
						     formula-of-typen-to-var
						     result)
  (let* ((real (car result))
	 (avars-and-chals (cdr result))
	 (formula (proof-to-formula proof))
	 (vars (do ((l (proof-to-free-avars proof) (cdr l))
		    (res (proof-to-free proof)
			 (if (formula-of-nulltypep? (avar-to-formula (car l)))
			     res
			     (cons (avar-of-typep-to-var (car l)) res))))
		   ((null? l) res)))
	 (varn (formula-of-typen-to-var formula))
	 (new-free-vars (if (eq? real 'eps) '()
			    (set-minus (term-to-free real) vars)))
	 (typep (formula-to-etdp-type formula)))
    (if (and (not (eq? real 'eps)) (not (term? real)))
	(myerror "Realizer of proof is not a term" real
		 (proof-to-expr proof)))
    (if (and (not (and (eq? real 'eps) (nulltype? typep)))
	     (not (equal? (term-to-type real) typep)))
	(myerror "Realizer of proof is not of correct type" real typep
		 (proof-to-expr proof)))
    (if (pair? new-free-vars)
	(myerror "Realizer contains superfluous free variables" real
		 new-free-vars vars
		 (proof-to-expr-with-formulas proof)))
    (for-each
     (lambda (avar-and-chal)
       (let* ((avar (car avar-and-chal))
	      (chal (cadr avar-and-chal))
	      (new-free-vars
	       (if (eq? chal 'eps) '()
		   (set-minus (term-to-free chal) (cons varn vars))))
	      (typen (formula-to-etdn-type (avar-to-formula avar))))
	 (if (and (not (eq? chal 'eps)) (not (term? chal)))
	     (begin
	       (spp (proof-to-expr-with-aconsts proof))
	       (spp chal)
	       (comment "Challenge is not a term")
	       (check-term chal)))
	 (if (and (not (and (eq? chal 'eps) (nulltype? typen)))
		  (not (equal? (term-to-type chal) typen)))
	     (myerror "Challenge is not of correct type" chal typen))
	 (if (pair? new-free-vars)
	     (myerror "Challenge contains superfluous free variables" chal
		      new-free-vars
		      (proof-to-expr-with-formulas proof)))))
     avars-and-chals)
    result))

(define (proof-to-extracted-d-terms-aux-check-result proof
						     avar-of-typep-to-var
						     formula-of-typen-to-var
						     result)
  result)

(define (proof-to-extracted-d-terms-aux
	 proof avar-of-typep-to-var formula-of-typen-to-var pvar-to-d-pvar)
  (proof-to-extracted-d-terms-aux-check-result
   proof
   avar-of-typep-to-var
   formula-of-typen-to-var
   (if
    (proof-without-d-real-or-chals? proof)
    (cons 'eps (map (lambda (avar) (list avar 'eps))
		    (context-to-avars (proof-to-context proof))))
    (case (tag proof)
      ((proof-in-avar-form)
       (let* ((avar (proof-in-avar-form-to-avar proof))
	      (formula (avar-to-formula avar))
	      (types (formula-to-etd-types formula))
	      (typep (car types))
	      (typen (cadr types))
	      (p? (nulltype? typep))
	      (n? (nulltype? typen)))
	 (list (if (not p?)
		   (make-term-in-var-form (avar-of-typep-to-var avar))
		   'eps)
	       (list avar (if (not n?)
			      (make-term-in-var-form
			       (formula-of-typen-to-var formula))
			      'eps)))))
      ((proof-in-aconst-form)
       (let* ((aconst (proof-in-aconst-form-to-aconst proof))
	      (name (aconst-to-name aconst))
	      (p? (formula-of-nulltypep? (aconst-to-formula aconst))))
	 (if
	  p? 'eps
	  (case (aconst-to-kind aconst)
	    ((axiom)
	     (cond ((string=? "Ind" name)
		    (myerror "not implemented" "Ind"))
		   ((string=? "Cases" name)
		    (myerror "not implemented" "Cases"))
		   ((string=? "Intro" name)
		    (myerror "not implemented" "Intro"))
		   ((string=? "Elim" name)
		    (myerror "not implemented" "Elim"))
		   ((string=? "Ex-Intro" name)
		    (list (ex-formula-to-ex-intro-extracted-d-term
			   (car (aconst-to-repro-data aconst)))))
		   ((string=? "Ex-Elim" name)
		    (myerror "not implemented" "Ex-Elim"))
		   (else (myerror "proof-to-extracted-d-terms-aux"
				  "unexpected axiom" name))))
	    ((theorem) ;TODO - define a program constant if one does not exist
	     (list (make-term-in-const-form
		    (theorem-or-global-assumption-to-d-pconst aconst))))
	    ((global-assumption)
	     (cond ((string=? "Efq" name)
		    (let* ((formula (proof-to-formula proof))
			   (etype (formula-to-etdp-type formula)))
		      (list (type-to-canonical-inhabitant etype))))
		   (else (list (make-term-in-const-form
				(theorem-or-global-assumption-to-d-pconst
				 aconst))))))))))
      ((proof-in-imp-intro-form proof-in-impnc-intro-form)
       (let* ((avar (proof-in-imp-impnc-all-allnc-intro-form-to-var proof))
	      (kernel (proof-in-imp-impnc-all-allnc-intro-form-to-kernel proof))
	      (prev (proof-to-extracted-d-terms-aux
		     kernel avar-of-typep-to-var formula-of-typen-to-var
		     pvar-to-d-pvar))
	      (avars-and-chals (cdr prev))
	      (rest-avars-and-chals
	       (list-transform-positive avars-and-chals
		 (lambda (p) (not (avar=? (car p) avar)))))
	      (info (assoc-wrt avar=? avar avars-and-chals))
	      (formula (proof-to-formula proof))
	      (prem (imp-impnc-form-to-premise formula))
	      (conc (imp-impnc-form-to-conclusion formula))
	      (p1? (formula-of-nulltypep? prem))
	      (n1? (formula-of-nulltypen? prem))
	      (n2? (formula-of-nulltypen? conc))
	      (arg-var (if p1? #f (avar-of-typep-to-var avar))) ;x
	      (kernel-var (if n2? #f (formula-of-typen-to-var conc))) ;z
	      (kernel-real (car prev)) ;t
	      (arg-chal (if info (cadr info)
			    (if n1? 'eps
				(type-to-canonical-inhabitant
				 (formula-to-etdn-type prem))))) ;r
	      (real (make-term-in-pair-form-et
		     (mk-term-in-abst-form-et arg-var kernel-real)
		     (mk-term-in-abst-form-et arg-var kernel-var arg-chal)))
					;substitute y0,y1 for x,z:
	      (rest-avars-and-subst-chals
	       (if (and p1? n2?)
		   rest-avars-and-chals
		   (let* ((chal-var (formula-of-typen-to-var formula)) ;y
			  (chal-varterm (make-term-in-var-form chal-var))
			  (subst-arg
			   (cons-true arg-var (cons-true kernel-var '())))
			  (subst-val
			   (if (and arg-var kernel-var)
			       (list (make-term-in-lcomp-form chal-varterm)
				     (make-term-in-rcomp-form chal-varterm))
			       (list chal-varterm)))
			  (subst (make-substitution subst-arg subst-val)))
		     (map (lambda (p)
			    (list (car p)
				  (term-substitute-et (cadr p) subst)))
			  rest-avars-and-chals)))))
	 (cons real rest-avars-and-subst-chals)))
      ((proof-in-imp-elim-form proof-in-impnc-elim-form)
       (cond
	((or (proof-in-ind-rule-form? proof) (proof-in-cases-rule-form? proof))
	 (let* ((cases? (proof-in-cases-rule-form? proof))
		(ind? (not cases?))
		(final-op (proof-to-final-allnc-elim-op
			   (proof-in-all-elim-form-to-op
			    (proof-to-final-imp-elim-op proof))))
		(term (proof-in-all-elim-form-to-arg
		       (proof-to-final-imp-elim-op proof)))
		(var (type-to-new-var (term-to-type term)))
		(aconst (proof-in-aconst-form-to-aconst final-op))
		(steps (proof-to-imp-elim-args proof))
		(prevs (map (lambda (step)
			      (proof-to-extracted-d-terms-aux
			       step avar-of-typep-to-var
			       formula-of-typen-to-var pvar-to-d-pvar))
			    steps))
		(step-reals (map car prevs))
		(avarss (map (lambda (l) (map car l)) (map cdr prevs)))
		(avars (remove-duplicates-wrt avar=? (apply append avarss)))
		(all-formulas (aconst-to-repro-data aconst))
					;only for ind rule
		(all-formula (car all-formulas))
		(kernel (all-form-to-kernel all-formula))
		(rec-const (car (arrow-types-to-rec-consts
				 (make-arrow
				  (var-to-type
				   (all-form-to-var all-formula))
				  (formula-to-etdp-type kernel)))))
		(step-flas (map proof-to-formula steps))
		(uninst-fla (aconst-to-uninst-formula
			     (apply all-formulas-to-ind-aconst all-formulas)))
		(uninst-step-flas (imp-form-to-premises
				   (all-form-to-kernel uninst-fla)))
		(varss (map (lambda (step-fla uninst-step-fla)
			      (if (all-form? uninst-step-fla)
				  (all-form-to-vars
				   step-fla
				   (length (all-form-to-vars
					    uninst-step-fla)))
				  '()))
			    step-flas uninst-step-flas))
		(xs ;(...,x,...)
		 (map (lambda (fla) (if (formula-of-nulltypen? fla) #f
					(formula-of-typen-to-var fla)))
		      step-flas))
		(p? (formula-of-nulltypep? kernel))
		(n? (formula-of-nulltypen? kernel))
		(formula (proof-to-formula proof))
		(chal-var (if n? #f (formula-of-typen-to-var formula))))
	   (if (> (length all-formulas) 1)
	       (myerror "Not implemented for simultaneous induction"))
	   (let* ((step-reals0 ;(...,lambda n tn0,...)
		   (if
		    (or n? cases?)
		    step-reals
		    (if p? '()
			(map (lambda (vars t)
			       (apply
				mk-term-in-abst-form
				(append
				 vars (list (apply
					     mk-term-in-app-form
					     (cons
					      t
					      (if (null? vars) '()
						  (append
						   (map make-term-in-var-form
							vars)
						   (list 'left)))))))))
			     varss step-reals))))
		  (auxreal ;tilde{t}
		   (if p? 'eps
		       (make-term-in-abst-form
			var
			(if cases?
					;cases
			    (make-term-in-if-form
			     (make-term-in-var-form var) step-reals0)
					;recursion
			    (apply mk-term-in-app-form
				   (cons (make-term-in-const-form rec-const)
					 (cons (make-term-in-var-form var)
					       step-reals0)))))))
		  (real (mk-term-in-app-form-et auxreal term)) ;tilde{t}term
		  (recargs-list
		   (map
		    (lambda (avar)
		      (if
		       (formula-of-nulltypen? (avar-to-formula avar))
		       'eps
		       (let ((chals
			      (map (lambda (prev)
				     (let* ((avar-chal-alist (cdr prev))
					    (info (assoc-wrt avar=? avar
							     avar-chal-alist))
					    (typen (formula-to-etdn-type
						    (avar-to-formula avar))))
				       (cond
					((nulltype? typen) 'eps)
					(info (cadr info))
					(else (type-to-canonical-inhabitant
					       typen)))))
				   prevs)))
			 (map
			  (lambda (vars x t chal avars-in-step)
			    (if
			     (null? vars) ;base case
			     (if n? chal
				 (mk-term-in-abst-form-et
				  chal-var
				  (term-subst-et
				   chal x (make-term-in-var-form chal-var))))
			     (let*
				 ((pd-var ;p
				   (if cases? #f
				       (type-to-new-var
					(make-arrow-et
					 (formula-to-etdn-type kernel)
					 (formula-to-etdn-type
					  (avar-to-formula avar))))))
				  (pd-real ;tilde{t}n
				   (if cases? 'eps
				       (make-term-in-app-form-et
					auxreal
					(make-term-in-var-form
					 (list-ref vars
						   (- (length vars) 1))))))
				  (chal-tuple ;<n, tilde{t}n, chal-var>
					;tilde{t}n used only for ind-rule
				   (apply
				    mk-term-in-pair-form-et
				    (append (map make-term-in-var-form vars)
					    (cons-true
					;put pd-real only if not cases
					     (and ind? pd-real)
					     (if n? '()
						 (list
						  (make-term-in-var-form
						   chal-var)))))))
				  (subst-chal
					;s = r_i[x:=<n, tilde{t}n, chal-var>]
				   (term-subst-et chal x chal-tuple))
				  (step-real1 ;tn1
				   (if
				    (or cases? n?) 'eps
				    (apply mk-term-in-app-form
					   (append
					    (list t)
					    (map make-term-in-var-form vars)
					    (if p? '() (list 'right))))))
				  (pd-chal ;tn1(tilde{t}n)chal-var
				   (mk-term-in-app-form-et
				    step-real1 pd-real
				    (if n? 'eps
					(make-term-in-var-form chal-var))))
				  (if-term
				   (if ;on induction do contraction
				    cases? subst-chal
				    (if ;contract only if avar is used in step
				     (member-wrt avar=? avar avars-in-step)
				     (contract
				      avar
				      avar-of-typep-to-var
				      formula-of-typen-to-var
				      pvar-to-d-pvar
				      subst-chal
				      (mk-term-in-app-form-et
				       (make-term-in-var-form pd-var)
				       pd-chal))
				     (mk-term-in-app-form-et
				      (make-term-in-var-form pd-var)
				      pd-chal)))))
			       (apply ;step-reals are not used in cases
				mk-term-in-abst-form-et
				(append vars
					(list pd-var chal-var if-term))))))
			  varss xs step-reals chals avarss))))
		    avars))
		  (rec-consts
					;these make sense only for induction
					;for cases just use avars - a list of
					;the same length
		   (if cases? avars
		       (map (lambda (avar)
			      (if (formula-of-nulltypen?
				   (avar-to-formula avar))
				  'eps
				  (car (arrow-types-to-rec-consts
					(mk-arrow-et
					 (var-to-type
					  (all-form-to-var all-formula))
					 (formula-to-etdn-type kernel)
					 (formula-to-etdn-type
					  (avar-to-formula avar)))))))
			    avars)))
		  (chals ;(...,\tilde{r}_i,...)
		   (map (lambda (avar rec-const recargs)
			  (if
			   (formula-of-nulltypen? (avar-to-formula avar))
			   'eps
			   (make-term-in-abst-form
			    var
			    (if cases?
					;cases
				(make-term-in-if-form
				 (make-term-in-var-form var) recargs)
					;induction
				(apply mk-term-in-app-form
				       (cons (make-term-in-const-form
					      rec-const)
					     (cons
					      (make-term-in-var-form var)
					      recargs)))))))
			avars rec-consts recargs-list)))
	     (cons real
		   (map (lambda (avar chal)
			  (list
			   avar
			   (if (formula-of-nulltypen? (avar-to-formula avar))
			       'eps
			       (mk-term-in-app-form-et
				chal term
				(if n? 'eps
				    (make-term-in-var-form chal-var))))))
			avars chals)))))
	((proof-in-ex-elim-rule-form? proof)
	 (let* ((main (proof-in-imp-elim-form-to-arg
		       (proof-in-imp-elim-form-to-op proof)))
		(side (proof-in-imp-elim-form-to-arg proof))
		(side-prev
		 (proof-to-extracted-d-terms-aux
		  side
		  avar-of-typep-to-var formula-of-typen-to-var pvar-to-d-pvar))
		(main-prev
		 (proof-to-extracted-d-terms-aux
		  main
		  avar-of-typep-to-var formula-of-typen-to-var pvar-to-d-pvar))
		(side-real (car side-prev)) ;t
		(side-avars-and-chals (cdr side-prev))
		(main-real (car main-prev)) ;s
		(main-avars-and-chals (cdr main-prev))
		(side-avars (map car side-avars-and-chals))
		(main-avars (map car main-avars-and-chals))
		(shared-avars (intersection-wrt avar=? side-avars main-avars))
		(left-avars (set-minus-wrt avar=? side-avars shared-avars))
		(right-avars (set-minus-wrt avar=? main-avars shared-avars))
		(main-fla (proof-to-formula main)) ;ex x A(x)
		(side-fla (proof-to-formula side)) ;all x(A(x) -> B)
		(conc
		 (imp-form-to-conclusion (all-form-to-kernel side-fla))) ;B
		(p1? (formula-of-nulltypep? (ex-form-to-kernel main-fla)))
		(n1? (formula-of-nulltypen? (ex-form-to-kernel main-fla)))
		(p2? (formula-of-nulltypep? conc))
		(n2? (formula-of-nulltypen? conc))
		(real-etc
		 (let* ((side-var (formula-of-typen-to-var side-fla)) ;x
			(main-var (formula-of-typen-to-var main-fla)) ;z
			(chal-varterm (if n2? 'eps
					  (make-term-in-var-form
					   (formula-of-typen-to-var conc)))) ;y
			(s0 (if p1? main-real
				(make-term-in-lcomp-form main-real)))
			(s1 (if p1? 'eps (make-term-in-rcomp-form main-real)))
			(real (if p2? 'eps
				  (mk-term-in-app-form-et
				   side-real s0
				   (if n1? 'eps 'left)
				   s1))) ;t(s0)0(s1))
					;substitute (s0,(s1,y)) for x in side
			(side-avars-and-subst-chals ;(ui,p'i) and (uk,p'k)
			 (map (lambda (p)
				(list (car p)
				      (term-subst-et
				       (cadr p) side-var
				       (make-term-in-pair-form-et
					s0 (make-term-in-pair-form-et
					    s1 chal-varterm)))))
			      side-avars-and-chals))
					;substitute t(s0)1(s1)y for z in main
			(main-avars-and-subst-chals ;(uj,q'j) and (uk,q'k)
			 (if n1? main-avars-and-chals
			     (map (lambda (p)
				    (list (car p)
					  (term-subst-et
					   (cadr p) main-var
					   (mk-term-in-app-form-et
					    side-real s0
					    (if p2? 'eps 'right)
					    s1
					    chal-varterm))))
				  main-avars-and-chals))))
		   (list real
			 side-avars-and-subst-chals
			 main-avars-and-subst-chals)))
		(real (car real-etc))
		(side-avars-and-subst-chals (cadr real-etc))
		(main-avars-and-subst-chals (caddr real-etc))
					;How to get from u:C to |C|^x_w,
					;and then to r_C?
					;x via avar-of-typep-to-var from u.
					;w via formula-of-typen-to-var from C.
					;|C|^x_w via
					;real-and-chal-and-formula-to-d-formula
					;r_C via qf-to-term.
					;Here we need to abstract w.
		(u-and-p-and-q-to-u-and-r
		 (lambda (u p q)
		   (let ((fla (avar-to-formula u)))
		     (if (formula-of-nulltypen? fla)
			 (list u 'eps)
			 (list u (contract u avar-of-typep-to-var
					   formula-of-typen-to-var
					   pvar-to-d-pvar p q))))))
		(avars-and-subst-chals ;all (ui,p'i), (uj,q'j), (uk,r_k)
		 (map
		  (lambda (avar)
		    (cond
		     ((member-wrt avar=? avar left-avars)
		      (list
		       avar
		       (cadr (assoc-wrt
			      avar=? avar side-avars-and-subst-chals))))
		     ((member-wrt avar=? avar right-avars)
		      (list
		       avar
		       (cadr (assoc-wrt
			      avar=? avar main-avars-and-subst-chals))))
		     (else ;shared-avar
		      (u-and-p-and-q-to-u-and-r
		       avar
		       (cadr (assoc-wrt
			      avar=? avar side-avars-and-subst-chals))
		       (cadr (assoc-wrt
			      avar=? avar main-avars-and-subst-chals))))))
		  (context-to-avars (proof-to-context proof)))))
	   (cons real avars-and-subst-chals)))
	(else ;imp-impnc-elim form, not ind-, cases- or ex-elim-rule-form
	 (let* ((op (cond
		     ((proof-in-imp-elim-form? proof)
		      (proof-in-imp-elim-form-to-op proof))
		     ((proof-in-impnc-elim-form? proof)
		      (proof-in-impnc-elim-form-to-op proof))
		     (else (myerror "proof-to-extracted-d-terms-aux"
				    "unexpected proof with tag"
				    (tag proof)))))
		(arg (cond
		      ((proof-in-imp-elim-form? proof)
		       (proof-in-imp-elim-form-to-arg proof))
		      ((proof-in-impnc-elim-form? proof)
		       (proof-in-impnc-elim-form-to-arg proof))
		      (else (myerror "proof-to-extracted-d-terms-aux"
				     "unexpected proof with tag"
				     (tag proof)))))
		(op-prev (proof-to-extracted-d-terms-aux
			  op avar-of-typep-to-var formula-of-typen-to-var
			  pvar-to-d-pvar))
		(arg-prev (proof-to-extracted-d-terms-aux
			   arg avar-of-typep-to-var formula-of-typen-to-var
			   pvar-to-d-pvar))
		(op-real (car op-prev)) ;t
		(op-avars-and-chals (cdr op-prev))
		(arg-real (car arg-prev)) ;s
		(arg-avars-and-chals (cdr arg-prev))
		(op-avars (map car op-avars-and-chals))
		(arg-avars (map car arg-avars-and-chals))
		(shared-avars (intersection-wrt avar=? op-avars arg-avars))
		(left-avars (set-minus-wrt avar=? op-avars shared-avars))
		(right-avars (set-minus-wrt avar=? arg-avars shared-avars))
		(impl (proof-to-formula op)) ;A -> B
		(prem (imp-impnc-form-to-premise impl))
		(conc (imp-impnc-form-to-conclusion impl))
		(p1? (formula-of-nulltypep? prem))
		(n1? (formula-of-nulltypen? prem))
		(p2? (formula-of-nulltypep? conc))
		(n2? (formula-of-nulltypen? conc))
		(chal-varterm
		 (if n2? 'eps
		     (make-term-in-var-form
		      (formula-of-typen-to-var conc)))) ;y
		(op-real-l
		 (if p2? 'eps
		     (if n1? op-real (make-term-in-lcomp-form op-real)))) ;t0
		(op-real-r
		 (if n1? 'eps
		     (if p2? op-real (make-term-in-rcomp-form op-real)))) ;t1
		(real (mk-term-in-app-form-et
		       op-real-l arg-real)) ;t0s
					;substitute (s,y) for x in op
		(op-avars-and-subst-chals ;(ui,p'i) and (uk,p'k)
		 (if (and p1? n2?)
		     op-avars-and-chals
		     (let ((op-var (formula-of-typen-to-var impl))) ;x
		       (map (lambda (p)
			      (list (car p) (term-subst-et
					     (cadr p) op-var
					     (make-term-in-pair-form-et
					      arg-real chal-varterm))))
			    op-avars-and-chals))))
					;substitute t1sy for z in arg
		(arg-avars-and-subst-chals ;(uj,q'j) and (uk,q'k)
		 (if n1?
		     arg-avars-and-chals
		     (let ((arg-var (formula-of-typen-to-var prem))) ;z
		       (map (lambda (p)
			      (list (car p)
				    (term-subst-et
				     (cadr p) arg-var
				     (mk-term-in-app-form-et ;t1sy
				      op-real-r arg-real
				      chal-varterm))))
			    arg-avars-and-chals))))
					;How to get from u:C to |C|^x_w,
					;and then to r_C?
					;x via avar-of-typep-to-var from u.
					;w via formula-of-typen-to-var from C.
					;|C|^x_w via
					;real-and-chal-and-formula-to-d-formula
					;r_C via qf-to-term.
					;Here we need to abstract w.
		(u-and-p-and-q-to-u-and-r
		 (lambda (u p q)
		   (let ((fla (avar-to-formula u)))
		     (if (formula-of-nulltypen? fla)
			 (list u 'eps)
			 (list u (contract u avar-of-typep-to-var
					   formula-of-typen-to-var
					   pvar-to-d-pvar p q))))))
		(avars-and-subst-chals ;all (ui,p'i), (uj,q'j), (uk,r_k)
		 (map
		  (lambda (avar)
		    (cond
		     ((member-wrt avar=? avar left-avars)
		      (list
		       avar
		       (cadr (assoc-wrt avar=? avar
					op-avars-and-subst-chals))))
		     ((member-wrt avar=? avar right-avars)
		      (list
		       avar
		       (cadr (assoc-wrt
			      avar=? avar arg-avars-and-subst-chals))))
		     (else ;shared-avar
		      (u-and-p-and-q-to-u-and-r
		       avar
		       (cadr (assoc-wrt
			      avar=? avar op-avars-and-subst-chals))
		       (cadr (assoc-wrt
			      avar=? avar arg-avars-and-subst-chals))))))
		  (context-to-avars (proof-to-context proof)))))
	   (cons real avars-and-subst-chals)))))
      ((proof-in-all-intro-form)
       (let* ((var (proof-in-all-intro-form-to-var proof)) ;x
	      (kernel (proof-in-all-intro-form-to-kernel proof))
	      (prev (proof-to-extracted-d-terms-aux
		     kernel
		     avar-of-typep-to-var formula-of-typen-to-var
		     pvar-to-d-pvar))
	      (kernel-real (car prev)) ;t
	      (avars-and-chals (cdr prev))
	      (kernel-formula (proof-to-formula kernel))
	      (types (formula-to-etd-types kernel-formula))
	      (typep (car types))
	      (typen (cadr types))
	      (p? (nulltype? typep))
	      (n? (nulltype? typen))
	      (real (if p? 'eps (make-term-in-abst-form var kernel-real)))
	      (chal-var (formula-of-typen-to-var (proof-to-formula proof))) ;y
	      (chal-varterm (make-term-in-var-form chal-var))
	      (avars-and-subst-chals
	       (if n? ;substitute y for x
		   (map (lambda (p)
			  (list (car p) (term-subst-et
					 (cadr p) var chal-varterm)))
			avars-and-chals)
					;substitute y0,y1 for x,z
		   (let* ((kernel-var
			   (formula-of-typen-to-var kernel-formula))) ;z
		     (map (lambda (p)
			    (list (car p)
				  (term-substitute-et
				   (cadr p)
				   (list (list var (make-term-in-lcomp-form
						    chal-varterm))
					 (list kernel-var
					       (make-term-in-rcomp-form
						chal-varterm))))))
			  avars-and-chals)))))
	 (cons real avars-and-subst-chals)))
      ((proof-in-all-elim-form)
       (cond
	((proof-in-gind-rule-form? proof)
	 (let* ((args (proof-in-elim-form-to-args proof))
		(final-op (proof-in-elim-form-to-final-op proof))
		(formula (proof-to-formula proof)) ;at(b) -> A
		(vars-and-kernel (allnc-form-to-vars-and-final-kernel
				  (proof-to-formula final-op)))
		(kernel (cadr vars-and-kernel))
		(f (length (car vars-and-kernel)))
		(mu-and-terms (list-head (list-tail args f)
					 (- (length args) f 1)))
		(mu (car mu-and-terms))
		(guard-term (car (last-pair args)))
		(prog-proof (car (last-pair mu-and-terms)))
		(prog (proof-to-formula prog-proof))
		(terms
		 (cdr (list-head  mu-and-terms (- (length mu-and-terms) 1))))
		(m (length terms)) ;m is the number of induction variables
		(prev-real-and-avars-and-chals
		 (proof-to-extracted-d-terms-aux
		  prog-proof
		  avar-of-typep-to-var
		  formula-of-typen-to-var pvar-to-d-pvar))
		(prev-real (car prev-real-and-avars-and-chals)) ;t
		(prev-avars-and-chals ;<u_i,r_i>
		 (cdr prev-real-and-avars-and-chals))
		(prev-avars (map car prev-avars-and-chals)) ;u_i
		(prev-chals (map cadr prev-avars-and-chals)) ;r_i
		(prev-chal-var
		 (formula-of-typen-to-var prog)) ;z'=<\vec{n},f,z>
		(types (map term-to-type terms)) ;\vec{\rho}
		(new-vars (map type-to-new-var types)) ;\vec{n}
		(new-vars-terms (map make-term-in-var-form new-vars))
		(new-vars-2 (map type-to-new-var types))
		(new-vars-terms-2 (map make-term-in-var-form new-vars-2))
		(etd-types (formula-to-etd-types formula))
		(typep (car etd-types)) ;\tau^+(A)
		(typen (cadr etd-types)) ;\tau^-(A)
		(p? (nulltype? typep))
		(n? (nulltype? typen))
		(chal-var (if n? 'eps (formula-of-typen-to-var formula))) ;z
		(chal-var-term (if n? 'eps (make-term-in-var-form chal-var)))
		(real-grecguard-type-info (append types (list typep)))
		(real-grecguard-term
		 (if p? 'eps
		     (make-term-in-const-form
		      (type-info-to-grecguard-const
		       real-grecguard-type-info))))
		(real-step
		 (if p? 'eps
		     (apply
		      mk-term-in-abst-form-et
		      (append
		       new-vars
		       (list
			(apply
			 mk-term-in-app-form-et
			 (cons prev-real
			       (append new-vars-terms (list  'left)))))))))
		(real
		 (if p? 'eps
		     (apply mk-term-in-app-form ;\tilde{t}
			    (cons real-grecguard-term
				  (cons mu
					(append new-vars-terms
						(list real-step
						      guard-term)))))))
		(guard (mk-term-in-app-form
			(pt "NatLt")
			(apply mk-term-in-app-form (cons mu new-vars-terms-2))
			(apply mk-term-in-app-form (cons mu new-vars-terms))))
		(real-guarded
		 (if p? 'eps ;\[\tilde{t}]_{<\mu\vec{n}} ;!
		     (apply
		      mk-term-in-abst-form
		      (append new-vars-2
			      (list
			       (apply
				mk-term-in-app-form
				(cons
				 real-grecguard-term
				 (cons
				  mu (append new-vars-terms-2
					     (list real-step
						   guard))))))))))
		(chal-grecguard-value-types ;\tau^-(A) => \tau^-(C_i)
		 (map (lambda (a)
			(make-arrow-et
			 typen
			 (formula-to-etdn-type
			  (avar-to-formula a))))
		      prev-avars))
		(chal-grecguard-type-infos (map (lambda (ty)
						  (append types (list ty)))
						chal-grecguard-value-types))
		(chal-grecguard-terms
		 (map (lambda (ti)
			(make-term-in-const-form
			 (type-info-to-grecguard-const ti)))
		      chal-grecguard-type-infos))
		(chal-subst ;[z':=<\vec{n},[\tilde{t}]_{<\mu\vec{n}},z>]
		 (make-subst prev-chal-var
			     (apply mk-term-in-pair-form-et
				    (append new-vars-terms
					    (list
					     real-guarded chal-var-term)))))
		(prev-subst-chals ;r_i[]
		 (map (lambda (prev-chal)
			(if (eq? prev-chal 'eps)
			    'eps
			    (term-substitute-et prev-chal chal-subst)))
		      prev-chals))
		(ps ;p_i:\vec{\rho}=>\tau^-(A)=>\tau^-(C_i)
		 (map (lambda (ty)
			(type-to-new-var (apply mk-arrow-et
						(append types (list ty)))))
		      chal-grecguard-value-types))
		(aux-chal ;t\vec{n} 1 [\tilde{t}]_{<\mu\vec{n}} z
		 (apply mk-term-in-app-form-et
			(cons prev-real
			      (append new-vars-terms
				      (cons
				       (if p? 'eps 'right)
				       (list real-guarded chal-var-term))))))
		(if-terms
		 (map (lambda (p prev-subst-chal avar)
			(if
			 (eq? prev-subst-chal 'eps)
			 'eps
			 (contract
			  avar
			  avar-of-typep-to-var
			  formula-of-typen-to-var
			  pvar-to-d-pvar
			  prev-subst-chal
			  (make-term-in-app-form-wrt-iterated-pairs
			   (make-term-in-var-form p)
			   aux-chal
			   (if n? m (+ 1 m))))))
		      ps prev-subst-chals prev-avars))
		(chals ;r_i(z)
		 (map
		  (lambda (grecguard-term p if-term)
		    (if (eq? if-term 'eps)
			'eps
			(apply mk-term-in-app-form-et
			       (cons grecguard-term
				     (cons mu
					   (append
					    terms
					    (list
					     (apply mk-term-in-abst-form
						    (append new-vars
							    (list p if-term)))
					     chal-var-term
					     guard-term)))))))
		  chal-grecguard-terms ps if-terms))
		(new-avars-and-chals (map list prev-avars chals)))
	   (cons real new-avars-and-chals)))
	(else
	 (let* ((op (proof-in-all-elim-form-to-op proof))
		(arg (proof-in-all-elim-form-to-arg proof)) ;s
		(op-prev
		 (proof-to-extracted-d-terms-aux
		  op avar-of-typep-to-var formula-of-typen-to-var
		  pvar-to-d-pvar))
		(op-real (car op-prev)) ;t
		(op-var (formula-of-typen-to-var (proof-to-formula op))) ;z
		(avars-and-chals (cdr op-prev))
		(formula (proof-to-formula proof)) ;A(s)
		(types (formula-to-etd-types formula))
		(typep (car types))
		(typen (cadr types))
		(p? (nulltype? typep))
		(n? (nulltype? typen))
		(real (if p? 'eps (mk-term-in-app-form op-real arg))) ;ts
		(avars-and-subst-chals
		 (map (lambda (p)
			(list (car p)
			      (term-subst-et
			       (cadr p) op-var
			       (if n?
					;substitute s for z
				   arg
					;else substitute s,y for z
				   (let* ((chal-var (formula-of-typen-to-var
						     formula)) ;y
					  (chal-varterm
					   (make-term-in-var-form chal-var)))
				     (make-term-in-pair-form
				      arg chal-varterm))))))
		      avars-and-chals)))
	   (cons real avars-and-subst-chals)))))
      ((proof-in-allnc-intro-form)
       (let* ((var (proof-in-all-intro-form-to-var proof)) ;x
	      (kernel (proof-in-all-intro-form-to-kernel proof))
	      (prev (proof-to-extracted-d-terms-aux
		     kernel
		     avar-of-typep-to-var formula-of-typen-to-var
		     pvar-to-d-pvar))
	      (kernel-real (car prev)) ;t
	      (avars-and-chals (cdr prev))
	      (kernel-formula (proof-to-formula kernel))
	      (types (formula-to-etd-types kernel-formula))
	      (typen (cadr types))
	      (n? (nulltype? typen))
	      (real kernel-real)
	      (avars-and-subst-chals
	       (if n? avars-and-chals
					;substitute y for z
		   (let* ((chal-var (formula-of-typen-to-var
				     (proof-to-formula proof))) ;y
			  (chal-varterm (make-term-in-var-form chal-var))
			  (kernel-var (formula-of-typen-to-var
				       (proof-to-formula kernel)))) ;z
		     (map (lambda (p)
			    (list (car p)
				  (term-subst-et
				   (cadr p) kernel-var chal-varterm)))
			  avars-and-chals)))))
	 (cons real avars-and-subst-chals)))
      ((proof-in-allnc-elim-form)
       (let* ((op (proof-in-allnc-elim-form-to-op proof))
	      (arg (proof-in-allnc-elim-form-to-arg proof)) ;s
	      (op-prev
	       (proof-to-extracted-d-terms-aux
		op avar-of-typep-to-var formula-of-typen-to-var
		pvar-to-d-pvar))
	      (op-real (car op-prev)) ;t
	      (avars-and-chals (cdr op-prev))
	      (formula (proof-to-formula proof)) ;A(s)
	      (types (formula-to-etd-types formula))
	      (typen (cadr types))
	      (n? (nulltype? typen))
	      (real op-real) ;t
	      (avars-and-subst-chals
	       (if n? avars-and-chals
					;else substitute y for z
		   (let* ((chal-var (formula-of-typen-to-var formula)) ;y
			  (chal-varterm (make-term-in-var-form chal-var))
			  (op-var (formula-of-typen-to-var
				   (proof-to-formula op)))) ;z
		     (map (lambda (p)
			    (list (car p)
				  (term-subst-et
				   (cadr p) op-var chal-varterm)))
			  avars-and-chals)))))
	 (cons real avars-and-subst-chals)))
      ((proof-in-and-intro-form)
       (let* ((left (proof-in-and-intro-form-to-left proof))
	      (right (proof-in-and-intro-form-to-right proof))
	      (left-prev
	       (proof-to-extracted-d-terms-aux
		left avar-of-typep-to-var formula-of-typen-to-var
		pvar-to-d-pvar))
	      (right-prev
	       (proof-to-extracted-d-terms-aux
		right avar-of-typep-to-var formula-of-typen-to-var
		pvar-to-d-pvar))
	      (left-real (car left-prev)) ;t
	      (left-avars-and-chals (cdr left-prev))
	      (right-real (car right-prev)) ;s
	      (right-avars-and-chals (cdr right-prev))
	      (left-branch-avars (map car left-avars-and-chals))
	      (right-branch-avars (map car right-avars-and-chals))
	      (shared-avars
	       (intersection-wrt avar=? left-branch-avars right-branch-avars))
	      (left-avars
	       (set-minus-wrt avar=? left-branch-avars shared-avars))
	      (right-avars
	       (set-minus-wrt avar=? right-branch-avars shared-avars))
	      (conj (proof-to-formula proof)) ;A & B
	      (lconj (and-form-to-left conj)) ;A
	      (rconj (and-form-to-right conj)) ;B
	      (p1? (formula-of-nulltypep? lconj))
	      (n1? (formula-of-nulltypen? lconj))
	      (p2? (formula-of-nulltypep? rconj))
	      (n2? (formula-of-nulltypen? rconj))
	      (real (make-term-in-pair-form-et left-real right-real))
	      (chal-varterm
	       (if (and n1? n2?) 'eps
		   (make-term-in-var-form (formula-of-typen-to-var conj)))) ;y
	      (chal-varterm-l
	       (if n1? 'eps
		   (if n2? chal-varterm
		       (make-term-in-lcomp-form chal-varterm)))) ;y0
	      (chal-varterm-r
	       (if n2? 'eps
		   (if n1? chal-varterm
		       (make-term-in-rcomp-form chal-varterm)))) ;y1
					;substitute y0 for x in left
	      (left-avars-and-subst-chals ;(ui,p'i) and (uk,p'k)
	       (if n1?
		   left-avars-and-chals
		   (let ((left-var (formula-of-typen-to-var lconj))) ;x
		     (map (lambda (p)
			    (list (car p) (term-subst-et
					   (cadr p) left-var chal-varterm-l)))
			  op-avars-and-chals))))
					;substitute y1 for z in right
	      (right-avars-and-subst-chals ;(uj,q'j) and (uk,q'k)
	       (if n2?
		   right-avars-and-chals
		   (let ((right-var (formula-of-typen-to-var rconj))) ;z
		     (map (lambda (p)
			    (list (car p)
				  (term-subst-et
				   (cadr p) right-var chal-varterm-r)))
			  arg-avars-and-chals))))
					;How to get from u:C to |C|^x_w,
					;and then to r_C?
					;x via avar-of-typep-to-var from u.
					;w via formula-of-typen-to-var from C.
					;|C|^x_w via
					;real-and-chal-and-formula-to-d-formula
					;r_C via qf-to-term.
					;Here we need to abstract w.
	      (u-and-p-and-q-to-u-and-r
	       (lambda (u p q)
		 (let ((fla (avar-to-formula u)))
		   (if (formula-of-nulltypen? fla)
		       (list u 'eps)
		       (list u (contract u avar-of-typep-to-var
					 formula-of-typen-to-var
					 pvar-to-d-pvar p q))))))
	      (avars-and-subst-chals ;all (ui,p'i), (uj,q'j), (uk,r_k)
	       (map
		(lambda (avar)
		  (cond
		   ((member-wrt avar=? avar left-avars)
		    (list
		     avar
		     (cadr
		      (assoc-wrt avar=? avar left-avars-and-subst-chals))))
		   ((member-wrt avar=? avar right-avars)
		    (list
		     avar
		     (cadr (assoc-wrt
			    avar=? avar right-avars-and-subst-chals))))
		   (else ;shared-avar
		    (u-and-p-and-q-to-u-and-r
		     avar
		     (cadr (assoc-wrt
			    avar=? avar left-avars-and-subst-chals))
		     (cadr (assoc-wrt
			    avar=? avar right-avars-and-subst-chals))))))
		(context-to-avars (proof-to-context proof)))))
	 (cons real avars-and-subst-chals)))
      ((proof-in-and-elim-left-form)
       (let* ((kernel (proof-in-and-elim-left-form-to-kernel proof))
	      (prev
	       (proof-to-extracted-d-terms-aux
		kernel
		avar-of-typep-to-var formula-of-typen-to-var pvar-to-d-pvar))
	      (conj-real (car prev)) ;t
	      (avars-and-chals (cdr prev))
	      (conj (proof-to-formula kernel))
	      (lconj (and-form-to-left conj))
	      (rconj (and-form-to-right conj))
	      (p1? (formula-of-nulltypep? lconj))
	      (n1? (formula-of-nulltypen? lconj))
	      (p2? (formula-of-nulltypep? rconj))
	      (n2? (formula-of-nulltypen? rconj))
					;right formula is challenged by
					;a canonical inhabitant
	      (dummy
	       (if n2? 'eps
		   (type-to-canonical-inhabitant
		    (formula-to-etdn-type rconj))))
	      (real (if p1? 'eps
			(if p2? conj-real
			    (make-term-in-lcomp-form conj-real))))
	      (lconj-var (formula-of-typen-to-var lconj))
	      (lconj-varterm (if n1? 'eps
				 (make-term-in-var-form lconj-var))) ;y
	      (avars-and-subst-chals
	       (if (and n1? n2?)
		   avars-and-chals
					;substitute (y,dummy) for x
		   (let ((chal-var (formula-of-typen-to-var conj)))
		     (map (lambda (p)
			    (list (car p) (term-subst-et
					   (cadr p) chal-var
					   (make-term-in-pair-form-et
					    lconj-varterm dummy))))
			  avars-and-chals)))))
	 (cons real avars-and-subst-chals)))
      ((proof-in-and-elim-right-form)
       (let* ((kernel (proof-in-and-elim-right-form-to-kernel proof))
	      (prev (proof-to-extracted-d-terms-aux
		     kernel
		     avar-of-typep-to-var formula-of-typen-to-var
		     pvar-to-d-pvar))
	      (conj-real (car prev)) ;t
	      (avars-and-chals (cdr prev))
	      (conj (proof-to-formula kernel))
	      (lconj (and-form-to-left conj))
	      (rconj (and-form-to-right conj))
	      (p1? (formula-of-nulltypep? lconj))
	      (n1? (formula-of-nulltypen? lconj))
	      (p2? (formula-of-nulltypep? rconj))
	      (n2? (formula-of-nulltypen? rconj))
					;left formula is challenged by a
					;canonical inhabitant
	      (dummy
	       (if n1? 'eps
		   (type-to-canonical-inhabitant
		    (formula-to-etdn-type lconj))))
	      (real
	       (if p2? 'eps
		   (if p1? conj-real (make-term-in-rcomp-form conj-real))))
	      (rconj-var (formula-of-typen-to-var rconj))
	      (rconj-varterm (if n2? 'eps
				 (make-term-in-var-form rconj-var))) ;y
	      (avars-and-subst-chals
	       (if (and n1? n2)
		   avars-and-chals
					;substitute (dummy,y) for x
		   (let ((chal-var (formula-of-typen-to-var conj)))
		     (map (lambda (p)
			    (list (car p) (term-subst-et
					   (cadr p) chal-var
					   (make-term-in-pair-form-et
					    dummy rconj-varterm))))
			  avars-and-chals)))))
	 (cons real avars-and-subst-chals)))
      (else (myerror "unexpected proof with tag" (tag proof)))))))

(define (proof-in-gind-rule-form? proof)
  (and (proof-in-all-elim-form? proof)
       (let ((proof1 (proof-to-final-all-elim-op proof)))
	 (and (proof-in-imp-elim-form? proof1)
	      (let ((imp-op (proof-in-imp-elim-form-to-op proof1)))
		(and (proof-in-all-elim-form? imp-op)
		     (let ((final-op (proof-to-final-allnc-elim-op
				      (proof-to-final-all-elim-op imp-op))))
		       (and (proof-in-aconst-form? final-op)
			    (string=? "GInd" (aconst-to-name
					      (proof-in-aconst-form-to-aconst
					       final-op)))))))))))

(define ETSD-DEBUG-GLOBAL-COUNTER 0)

(define (before-after before after thunk)
  (let ((counter ETSD-DEBUG-GLOBAL-COUNTER))
    (display "Before ")
    (display counter)
    (newline)
    (display (force before))
    (newline)
    (set! ETSD-DEBUG-GLOBAL-COUNTER (+ counter 1))
    (let ((result (force thunk)))
      (display "After ")
      (display counter)
      (newline)
      (display (force after))
      (newline)
      result)))

;; TODO - comment needed here
(define (all-formula-and-alts-to-etd-if-term all-formula alts)
  (let* ((var (all-form-to-var all-formula))
	 (test-type (var-to-type var))
	 (test-var (type-to-new-var test-type)))
    (make-term-in-abst-form
     test-var (make-term-in-if-form
	       (make-term-in-var-form test-var) alts))))

(define (term-substitute-et term tosubst)
  (if (eq? 'eps term)
      'eps
      (term-substitute term tosubst)))

(define (term-subst-et term arg val)
  (if (eq? 'eps term)
      'eps
      (term-subst term arg val)))

;; For an avar u with a formula C with negative content tau^-(C) \ne
;; eps and terms p, q and qs of type tau^-(C) we generate an if-term of
;; type tau^-(C) used for contraction.

(define ETSD-LET-ENABLED #t)

(define (contract u avar-of-typep-to-var formula-of-typen-to-var pvar-to-d-pvar
		  p q . qs)
  (let* ((fla (avar-to-formula u))
	 (eps-or-x (if (formula-of-nulltypep? fla)
		       'eps
		       (make-term-in-var-form (avar-of-typep-to-var u))))
	 (w (formula-of-typen-to-var fla))
	 (d-fla (real-and-chal-and-formula-to-d-formula-aux
		 eps-or-x (make-term-in-var-form w) fla pvar-to-d-pvar))
	 (boolean-term
	  (if (quant-free? d-fla)
	      (if (null? (formula-to-pvars d-fla))
		  (qf-to-term d-fla)
		  (myerror "contract" "unexpected pvars in formula" d-fla))
	      (myerror "contract" "quantifier-free formula expected" d-fla)))
	 (abst-boolean-term (make-term-in-abst-form w boolean-term))
	 (cId-const (pconst-name-to-pconst "cId"))
	 (cId-term (make-term-in-const-form
		    (let* ((tvars (const-to-tvars cId-const))
			   (subst (make-substitution
				   tvars (list (make-arrow (var-to-type w)
							   (var-to-type w))))))
		      (const-substitute cId-const subst #f)))))
    (letrec
	((contract-aux
	  (lambda (p q . qs)
	    (let ((prev (if (null? qs) q
			    (apply contract-aux (cons q qs)))))
					;TODO - comment needed
	      (if (or (not ETSD-LET-ENABLED) (term-is-inappropriate-for-let? p)
		      (term-is-inappropriate-for-let? (nt p)))
		  (make-term-in-if-form
		   (make-term-in-app-form abst-boolean-term p)
		   (list prev p))
		  (mk-term-in-app-form ;let via cId
		   cId-term
		   (make-term-in-abst-form
		    w (make-term-in-if-form
		       (make-term-in-app-form
			abst-boolean-term
			(make-term-in-var-form w))
		       (list prev (make-term-in-var-form w))))
		   p))))))
      (apply contract-aux (cons p (cons q qs))))))

;; TODO - comment needed
(define (term-is-inappropriate-for-let? term)
  (or (term-in-var-form? term)
      (term-in-const-form? term)
      (is-numeric-term? term)
      (and (term-in-pair-form? term)
	   (term-is-inappropriate-for-let?
	    (term-in-pair-form-to-left term))
	   (term-is-inappropriate-for-let?
	    (term-in-pair-form-to-right term)))))

(define (ex-formula-to-ex-intro-extracted-d-term ex-formula)
  (let* ((var (ex-form-to-var ex-formula))
         (kernel (ex-form-to-kernel ex-formula))
	 (kernel-types (formula-to-etd-types kernel))
	 (kernel-typep (car kernel-types))
	 (kernel-typen (cadr kernel-types))
	 (p? (nulltype? kernel-typep))
	 (n? (nulltype? kernel-typen))
	 (real-var (if p? #f (type-to-new-var kernel-typep)))
	 (chal-var (if n? #f (type-to-new-var kernel-typen)))
	 (real (if p? 'eps (make-term-in-var-form real-var)))
	 (chal (if n? 'eps (make-term-in-var-form chal-var))))
      (make-term-in-abst-form
       var (make-term-in-pair-form-et
	    (make-term-in-abst-form-et
	     real-var (make-term-in-pair-form-et
		       (make-term-in-var-form var) real))
	    (mk-term-in-abst-form-et real-var chal-var chal)))))

;; theorem-or-global-assumption-to-d-pconst realises a theorem or a
;; global assumption with an appropriately instantiated program
;; constant corresponding to the assumption constant.

(define (theorem-or-global-assumption-to-d-pconst thm-or-ga)
  (let* ((thm-or-ga-name (aconst-to-name thm-or-ga))
	 (d-pconst-name
	  (theorem-or-global-assumption-name-to-d-pconst-name thm-or-ga-name))
	 (d-pconst (pconst-name-to-pconst d-pconst-name))
	 (tpsubst (aconst-to-tpsubst thm-or-ga))
	 (tsubst (list-transform-positive tpsubst
		   (lambda (x) (tvar-form? (car x)))))
	 (psubst (list-transform-positive tpsubst
		   (lambda (x) (pvar-form? (car x)))))
	 (new-tsubst
	  (do ((l psubst (cdr l))
	       (res '() (let* ((pvar (caar l))
			       (cterm (cadar l))
			       (formula (cterm-to-formula cterm))
			       (types (formula-to-etd-types formula))
			       (typep (car types))
			       (typen (cadr types))
			       (p? (nulltype? typep))
			       (n? (nulltype? typen)))
			  (cond
			   ((and p? n?) res)
			   ((and p? (not n?))
			    (cons (list (PVAR-TO-TVARP pvar) typep) res))
			   ((and (not p?) n?)
			    (cons (list (PVAR-TO-TVARN pvar) typen) res))
			   ((and (not p?) (not n?))
			    (cons (list (PVAR-TO-TVARN pvar) typen)
				  (cons (list (PVAR-TO-TVARP pvar) typep)
					res)))))))
	      ((null? l) (reverse res)))))
    (const-substitute d-pconst
		      (compose-substitutions tsubst new-tsubst) #f)))

;; theorem-or-global-assumption-name-to-d-pconst-name generates a
;; program constant name, corresponding to an assumption constant name

(define (theorem-or-global-assumption-name-to-d-pconst-name string)
  (string-append "d"
		 (list->string (remove-numerals (string->list string)))))

;; rm-falsity-log translates a proof by substituting logical falsity
;; with arithmetical falsity.

;; TODO - We need a special treatment of the substitution bot -> F in
;; proof-subst, or more precisely in aconst-substitute-aux.  There we
;; should replace the global assumptions "EfqLog" by "Efq" and
;; "StabLog" by "Stab" (without unfolding them into proofs) and the
;; theorems "Excl-Intro" by "Exca-Intro" and "Excl-Elim" by
;; "Exca-Elim".  One might unfold the latter into proofs.

(define (rm-falsity-log proof)
  (let ((proof-with-F-for-bot (proof-subst
			       proof
			       (predicate-form-to-predicate (pf "bot"))
			       (make-cterm (pf "F")))))
    (if (proof=? (np proof-with-F-for-bot) (np proof))
	proof
	proof-with-F-for-bot)))

;; does a proof contain the logical falsity?

(define (proof-contains-bot? proof)
  (not (proof=? (np (rm-falsity-log proof)) (np proof))))
