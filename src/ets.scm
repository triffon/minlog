;; $Id: ets.scm 2691 2014-01-24 09:19:47Z schwicht $
;; 16. Extracted terms
;; ===================

(define (make-arrow-et type1 type2)
  (if (nulltype? type1)
      type2
      (if (nulltype? type2)
          (make-tconst "nulltype")
          (make-arrow type1 type2))))

(define (mk-arrow-et x . rest)
  (if (null? rest)
      x
      (make-arrow-et x (apply mk-arrow-et rest))))

(define (make-star-et type1 type2)
  (if (nulltype? type1)
      type2
      (if (nulltype? type2)
          type1
          (make-star type1 type2))))

;; When we want to execute the program, we have to replace cL by the
;; extracted program of its proof, and cGA by an assumed extracted term
;; to be provided by the user.  This can be achieved by adding
;; computation rules for cL and cGA.  We can be rather flexible here and
;; enable/block rewriting by using animate/deanimate as desired.

;; Notice that the type of the extracted term provided for a cGA must be
;; the et-type of the assumed formula.  When predicate variables are
;; present, one must use the type variables assigned to them in
;; PVAR-TO-TVAR-ALIST.

(define (animate thm-or-ga-name . opt-eterm)
  (let* ((pconst-name
	  (theorem-or-global-assumption-name-to-pconst-name thm-or-ga-name))
	 (pconst (pconst-name-to-pconst pconst-name))
	 (info1 (assoc thm-or-ga-name THEOREMS)))
    (if
     info1
     (let* ((proof (theorem-name-to-proof thm-or-ga-name))
	    (eterm (proof-to-extracted-term proof))
	    (neterm (nt eterm)))
       (add-computation-rule (make-term-in-const-form pconst) neterm))
     (let ((info2 (assoc thm-or-ga-name GLOBAL-ASSUMPTIONS)))
       (if
	info2
	(let* ((eterm (if (pair? opt-eterm)
			  (car opt-eterm)
			  (myerror "animate" "eterm expected for"
				   thm-or-ga-name)))
	       (et-type (formula-to-et-type
			 (aconst-to-uninst-formula
			  (global-assumption-name-to-aconst
			   thm-or-ga-name)))))
	  (if (not (equal? (term-to-type eterm) et-type))
	      (myerror "animate" "equal types expected"
		       (term-to-type eterm)
		       et-type))
	  (add-computation-rule (make-term-in-const-form pconst) eterm)))))))

(define (deanimate thm-or-ga-name)
  (let* ((pconst-name
	  (theorem-or-global-assumption-name-to-pconst-name thm-or-ga-name))
	 (pconst (pconst-name-to-pconst pconst-name))
	 (term (make-term-in-const-form pconst)))
    (remove-computation-rules-for term)))

;; formula-to-et-type and idpredconst-to-et-type are defined
;; simultaneously.  This makes sense, since the clauses and also the
;; cterms of an idpredconst are prior to the idpredconst.

(define (formula-to-et-type formula)
  (case (tag formula)
    ((atom) (make-tconst "nulltype"))
    ((predicate)
     (let ((pred (predicate-form-to-predicate formula)))
       (cond ((pvar-form? pred)
	      (if (pvar-with-positive-content? pred)
		  (PVAR-TO-TVAR pred)
		  (make-tconst "nulltype")))
	     ((predconst-form? pred)
	      (if (string=? "Total" (predconst-to-name pred))
		  (car (arity-to-types (predconst-to-arity pred)))
		  (make-tconst "nulltype")))
	     ((idpredconst-form? pred) (idpredconst-to-et-type pred))
	     (else (myerror
		    "formula-to-et-type" "predicate expected" pred)))))
    ((imp)
     (make-arrow-et
      (formula-to-et-type (imp-form-to-premise formula))
      (formula-to-et-type (imp-form-to-conclusion formula))))
    ((impnc)
     (formula-to-et-type (impnc-form-to-conclusion formula)))
    ((and)
     (make-star-et
      (formula-to-et-type (and-form-to-left formula))
      (formula-to-et-type (and-form-to-right formula))))
    ((all)
     (make-arrow-et
      (var-to-type (all-form-to-var formula))
      (formula-to-et-type (all-form-to-kernel formula))))
    ((ex) (make-star-et
	   (var-to-type (ex-form-to-var formula))
	   (formula-to-et-type (ex-form-to-kernel formula))))
    ((allnc)
     (formula-to-et-type (allnc-form-to-kernel formula)))
    ((exnc) ;obsolete
     (formula-to-et-type (exnc-form-to-kernel formula)))
    ((exca excl excu)
     (formula-to-et-type (unfold-formula formula)))
    (else (myerror "formula-to-et-type" "formula expected" formula))))

(define (idpredconst-to-et-type idpc)
  (let* ((name (idpredconst-to-name idpc))
	 (opt-alg-name (idpredconst-name-to-opt-alg-name name)))
    (if
     (null? opt-alg-name)
     (make-tconst "nulltype")
     (let* ((string (car opt-alg-name))
	    (types (idpredconst-to-types idpc))
	    (cterms (idpredconst-to-cterms idpc))
	    (tvars (idpredconst-name-to-tvars name))
	    (idpc-pvars (idpredconst-name-to-pvars name))
	    (param-pvars (idpredconst-name-to-param-pvars name))
	    (names (idpredconst-name-to-simidpc-names name))
	    (clauses-with-names
	     (apply append (map idpredconst-name-to-clauses-with-names names)))
	    (clauses (map car clauses-with-names))
	    (et-types (map formula-to-et-type clauses))
	    (idpc-tvars (map PVAR-TO-TVAR idpc-pvars))
	    (et-tvars (set-minus (apply union (map type-to-tvars et-types))
				 idpc-tvars))
	    (relevant-types (do ((l1 tvars (cdr l1))
				 (l2 types (cdr l2))
				 (res '() (let ((tvar (car l1))
						(type (car l2)))
					    (if (member tvar et-tvars)
						(cons type res)
						res))))
				((null? l2) (reverse res))))
	    (relevant-cterm-types
	     (do ((l1 param-pvars (cdr l1))
		  (l2 cterms (cdr l2))
		  (res '() (let* ((pvar (car l1))
				  (cterm (car l2))
				  (formula (cterm-to-formula cterm))
				  (cterm-et-type
				   (formula-to-et-type formula)))
			     (if (and (pvar-with-positive-content? pvar)
				      (member (PVAR-TO-TVAR pvar) et-tvars))
				 (cons cterm-et-type res)
				 res))))
		 ((null? l1) (reverse res))))
	    (relevant-types-and-cterm-types
	     (append relevant-types relevant-cterm-types))
	    (nc-indicator (append (make-list (length relevant-types) #f)
				  (map nulltype? relevant-cterm-types)))
	    (new-alg-name (alg-name-and-nc-indicator-to-alg-name
			   string nc-indicator)))
       (cond
	((string=? "nulltype" new-alg-name) (make-tconst "nulltype"))
	((string=? "identity" new-alg-name)
	 (car (list-transform-positive relevant-types-and-cterm-types
		(lambda (t) (not (nulltype? t))))))
	(else ;proper alg name
	 (apply make-alg
		new-alg-name
		(list-transform-positive relevant-types-and-cterm-types
		  (lambda (t) (not (nulltype? t)))))))))))

(define ALG-NAME-AND-NC-INDICATOR-TO-ALG-NAME '())

(set! ALG-NAME-AND-NC-INDICATOR-TO-ALG-NAME
      (append (list (list (list "identity" '(#t)) "nulltype")
		    (list (list "ysum" '(#t #f)) "uysum")
		    (list (list "ysum" '(#f #t)) "ysumu")
		    (list (list "ysum" '(#t #t)) "boole")
		    (list (list "yprod" '(#t #f)) "identity")
		    (list (list "yprod" '(#f #t)) "identity")
		    (list (list "yprod" '(#t #t)) "nulltype"))
	      ALG-NAME-AND-NC-INDICATOR-TO-ALG-NAME))

(define (alg-name-and-nc-indicator-to-alg-name alg-name nc-indicator)
  (let ((info1 (assoc (list alg-name nc-indicator)
		      ALG-NAME-AND-NC-INDICATOR-TO-ALG-NAME)))
    (cond
     (info1 (cadr info1))
     ((apply and-op (map not nc-indicator)) alg-name)
     (else ;check whether the default addition was done
      (let* ((default-alg-name
	       (apply string-append alg-name (map (lambda (p) (if p "nc" "cr"))
						  nc-indicator)))
	     (info2 (assoc default-alg-name ALGEBRAS)))
	(if
	 info2 default-alg-name ;else create new algebras
	 (let* ((tvars (alg-name-to-tvars alg-name))
		(tsubst
		 (do ((l1 tvars (cdr l1))
		      (l2 nc-indicator (cdr l2))
		      (res '()
			   (if (car l2)
			       (cons (list (car l1) (make-tconst "nulltype"))
				     res)
			       res)))
		     ((null? l1) (reverse res))))
		(simalg-names (alg-name-to-simalg-names alg-name))
		(typed-constr-names
		 (apply union (map alg-name-to-typed-constr-names
				   simalg-names)))
		(simalg-names-et
		 (map (lambda (name)
			(apply string-append
			       name (map (lambda (p) (if p "nc" "cr"))
					 nc-indicator)))
		      simalg-names))
		(constr-names
		 (map typed-constr-name-to-name typed-constr-names))
		(constr-names-et
		 (map (lambda (name)
			(apply string-append
			       name (map (lambda (p) (if p "Nc" "Cr"))
					 nc-indicator)))
		      constr-names))
		(constr-types
		 (map typed-constr-name-to-type typed-constr-names))
		(constr-types-with-nulltype
		 (map (lambda (type) (type-substitute type tsubst))
		      constr-types))
		(tvars-with-nulltype
		 (alg-form-to-types (arrow-form-to-final-val-type
				     (car constr-types-with-nulltype))))
		(simalgs-with-nulltype
		 (map (lambda (simalg-name)
			(apply make-alg simalg-name tvars-with-nulltype))
		      simalg-names))
		(simalg-strings (map type-to-string simalgs-with-nulltype))
		(shortened-constr-types-with-nulltype
		 (map remove-nulltype-argtypes constr-types-with-nulltype))
		(shortened-constr-type-strings-with-nulltype
		 (map type-to-string shortened-constr-types-with-nulltype))
		(constr-type-strings-et
		 (map (lambda (string)
			(string-replace-substrings
			 string simalg-strings simalg-names-et))
		      shortened-constr-type-strings-with-nulltype))
		(constr-type-strings-et-with-names
		 (map list constr-type-strings-et constr-names-et)))
	   (apply add-algs simalg-names-et constr-type-strings-et-with-names)
	   (apply string-append alg-name (map (lambda (p) (if p "nc" "cr"))
					      nc-indicator)))))))))

(define (formula-of-nulltype? formula)
  (case (tag formula)
    ((atom) #t)
    ((predicate)
     (let ((pred (predicate-form-to-predicate formula)))
       (cond
	((pvar-form? pred)
	 (not (pvar-with-positive-content? pred)))
	((predconst-form? pred)
	 (not (string=? (predconst-to-name pred) "Total")))
	((idpredconst-form? pred)
	 (let* ((name (idpredconst-to-name pred))
		(opt-alg-name (idpredconst-name-to-opt-alg-name name)))
	   (or (null? opt-alg-name)
	       (and (string=? "identity" (car opt-alg-name))
		    (equal? (make-tconst "nulltype")
			    (idpredconst-to-et-type pred))))))
	(else (myerror "formula-of-nulltype?" "predicate expected" pred)))))
    ((imp) (formula-of-nulltype? (imp-form-to-conclusion formula)))
    ((impnc) (formula-of-nulltype? (impnc-form-to-conclusion formula)))
    ((and) (and (formula-of-nulltype? (and-form-to-left formula))
		(formula-of-nulltype? (and-form-to-right formula))))
    ((all) (formula-of-nulltype? (all-form-to-kernel formula)))
    ((ex) #f)
    ((allnc) (formula-of-nulltype? (allnc-form-to-kernel formula)))
    ((exnc) ;obsolete
     (formula-of-nulltype? (exnc-form-to-kernel formula)))
    ((exca excl excu) (formula-of-nulltype? (unfold-formula formula)))
    (else (myerror "formula-of-nulltype?" "formula expected" formula))))

(define (formula-of-nulltype-under-extension? formula)
  (case (tag formula)
    ((atom) #t)
    ((predicate)
     (let ((pred (predicate-form-to-predicate formula)))
       (cond ((pvar-form? pred)
	      (not (pvar-with-positive-content? pred)))
	     ((predconst-form? pred)
	      (not (string=? (predconst-to-name pred) "Total")))
	     ((idpredconst-form? pred)
	      (let* ((name (idpredconst-to-name pred))
		     (opt-alg-name (idpredconst-name-to-opt-alg-name name)))
		(or (and (null? opt-alg-name)
			 (not (string=? name "EdD"))
			 (not (string=? name "ExU"))
			 (not (string=? name "ExUT"))
			 (not (string=? name "AndU")))
		    (and (not (null? opt-alg-name))
			 (string=? "identity" (car opt-alg-name))
			 (equal? (make-tconst "nulltype")
				 (idpredconst-to-et-type pred))))))
	     (else (myerror "formula-of-nulltype-under-extension?"
			    "predicate expected" pred)))))
    ((imp)
     (formula-of-nulltype-under-extension? (imp-form-to-conclusion formula)))
    ((impnc)
     (formula-of-nulltype-under-extension? (impnc-form-to-conclusion formula)))
    ((and)
     (and (formula-of-nulltype-under-extension? (and-form-to-left formula))
	  (formula-of-nulltype-under-extension? (and-form-to-right formula))))
    ((all) (formula-of-nulltype-under-extension? (all-form-to-kernel formula)))
    ((ex) #f)
    ((allnc)
     (formula-of-nulltype-under-extension? (allnc-form-to-kernel formula)))
    ((exnc) ;obsolete
     (formula-of-nulltype-under-extension? (exnc-form-to-kernel formula)))
    ((exca excl excu)
     (formula-of-nulltype-under-extension? (unfold-formula formula)))
    (else (myerror "formula-of-nulltype-under-extension?"
		   "formula expected" formula))))

;; Initial THEOREMS moved here because formula-substitute (used in
;; make-proof-in-aconst-form for AllncTotalIntro) needs
;; formula-of-nulltype?

;; Axioms AllTotalIntro (was AllPartial-All), AllTotalElim (was
;; All-AllPartial), AllncTotalIntro, AllncTotalElim are viewed as
;; initial theorems, with the same name.  This makes it easy to use
;; them in interactive proofs.  Further abbreviation axioms
;; AtomToEqDTrue EqDTrueToAtom ExTotalIntro (was ExPartial-Ex) and
;; ExTotalElim (was Ex-ExPartial) will be added to THEOREMS in
;; ets.scm, when Leibniz equality EqD and ExR are available.  From
;; them Truth := atom(True) (a preferred alternative to Truth-Axiom)
;; is proved and added to THEOREMS.  Then EqDCompat EqDCompatRev
;; EqDSym EqDTrans EqDCompatApp EFEqD are proven and added to
;; THEOREMS.  Also InhabTotal (needed to express that an arbitrary
;; type given by a type variable is inhabited) and InhabTotalMR
;; (needed for its realizability interpretation) are proved from the
;; corresponding axioms and added (in ets.scm) to THEOREMS.

(set!
 THEOREMS
 (list
  (list "AllTotalIntro" alltotal-intro-aconst
	(make-proof-in-aconst-form alltotal-intro-aconst))
  (list "AllTotalElim" alltotal-elim-aconst
	(make-proof-in-aconst-form alltotal-elim-aconst))
  (list "AllncTotalIntro" allnctotal-intro-aconst
	(make-proof-in-aconst-form allnctotal-intro-aconst))
  (list "AllncTotalElim" allnctotal-elim-aconst
	(make-proof-in-aconst-form allnctotal-elim-aconst))
  ;; (list "AtomTrue" atom-true-aconst atom-true-proof)
  ;; (list "AtomFalse" atom-false-aconst atom-false-proof)
  ;; the following are obsolete
  ;; (list "Efq-Atom" efq-atom-aconst efq-atom-proof)
  (list "All-AllPartial" all-allpartial-aconst
	(make-proof-in-aconst-form all-allpartial-aconst))
  (list "AllPartial-All" allpartial-all-aconst
	(make-proof-in-aconst-form allpartial-all-aconst))
  (list "Eq-Compat-Rev" eq-compat-rev-aconst eq-compat-rev-proof)
;;  (list "Truth-Axiom" truth-aconst (make-proof-in-aconst-form truth-aconst))
  (list "Truth-Axiom" (make-aconst "Truth-Axiom" 'axiom truth empty-subst)
	(make-proof-in-aconst-form
	 (make-aconst "Truth-Axiom" 'axiom truth empty-subst)))
  (list "Eq-Refl" eq-refl-aconst (make-proof-in-aconst-form eq-refl-aconst))
  (list "Eq-Sym" eq-sym-aconst (make-proof-in-aconst-form eq-sym-aconst))
  (list "Eq-Trans" eq-trans-aconst
	(make-proof-in-aconst-form eq-trans-aconst))
  (list "Eq-Ext" ext-aconst (make-proof-in-aconst-form ext-aconst))
  (list "Eq-Compat" eq-compat-aconst
	(make-proof-in-aconst-form eq-compat-aconst))))

;; We add totality for the algebras introduced before.  This can be
;; done only here, because we need formula-of-nulltype?

(set! COMMENT-FLAG #f)
(add-totality "unit")
(add-totality "boole")
(add-totality "yprod")
(add-rtotality "yprod")
(add-totality "ysum")
(add-rtotality "ysum")
(add-totality "uysum")
(add-rtotality "uysum")
(add-totality "ysumu")
(add-rtotality "ysumu")
(set! COMMENT-FLAG #t)

;; We initially supply the following global assumptions.
;; This can be done only here, because for add-global-assumption we need
;; formula-to-et-type.
;; EfqLog: bot -> Pvar
;; StabLog: ((Pvar -> bot) -> bot) -> Pvar
;; Efq: F -> Pvar
;; Stab: ((Pvar -> F) -> F) -> Pvar

(add-global-assumption
 "EfqLog" (make-imp
	   falsity-log
	   (make-predicate-formula (mk-pvar (make-arity)))))

(add-global-assumption
 "StabLog"
 (let ((p (make-predicate-formula (mk-pvar (make-arity)))))
   (make-imp (make-imp (make-imp p falsity-log) falsity-log) p)))

(add-global-assumption
 "Efq" (make-imp
	(make-atomic-formula
	 (make-term-in-const-form (constr-name-to-constr "False")))
	(make-predicate-formula (mk-pvar (make-arity)))))

(add-global-assumption
 "Stab"
 (let ((f (make-atomic-formula
	   (make-term-in-const-form (constr-name-to-constr "False"))))
       (p (make-predicate-formula (mk-pvar (make-arity)))))
   (make-imp (make-imp (make-imp p f) f) p)))

(define (make-avar-to-var)
  ;; returns a procedure assigning to assumption variables whose types
  ;; have computational content new object vars of the corresponding
  ;; et-type.  Remembers the assignment done so far.
  (let ((avar-assoc-list '()))
    (lambda (avar)
      (let ((info (assoc-wrt avar=? avar avar-assoc-list)))
	(if info
	    (cadr info)
	    (let* ((formula (avar-to-formula avar))
		   (type (formula-to-et-type formula))
		   (new-var (if (nulltype? type)
				(myerror "make-avar-to-var"
					 "computational content expected in"
					 formula)
				(type-to-new-var type))))
	      (begin (set! avar-assoc-list
			   (cons (list avar new-var) avar-assoc-list))
		     new-var)))))))

;; proof-to-extracted-term gets either a proof or else a theorem name.
;; In the former case it works its way through the proof, until it
;; comes to an assumption variable, an axiom, a theorem or a global
;; assumption.  When it is a theorem, theorem-to-extracted-term is
;; called.  This also happens in the latter case above, when a theorem
;; name is the input.  theorem-to-extracted-term applies as default
;; theorem-or-global-assumption-to-pconst, where in case of a lemma L
;; the pconst has name cL.  It will unfold under normalization if the
;; lemma is animated.  However, in some cases theorem-to-extracted-term
;; directly gives short and meaningful terms:

;; InhabTotal -> (Inhab rho)

;; AllTotalIntro AllTotalElim AllncTotalIntro AllncTotalElim
;; ExTotalIntro ExTotalElim -> [x]x

;; obsolete: All-AllPartial AllPartial-All Ex-ExPartial ExPartial-Ex -> [x]x

;; Eq-Compat Eq-Compat-Rev -> [x]x

;; Pconst+Total -> Pconst

;; Pconst+STotal -> the extract from the proof

;; AlgEqTotal -> [n,m]n=m

;; AlgETotal -> [n]E n

;; BooleIfTotal -> [free][if test arg1 arg2]

;; EqDCompat EqDCompatRev -> [x]x

;; Id -> [x]x in case unfold-let-flag is true.

(define (proof-to-extracted-term . opt-proof-or-thm-name-and-unfold-let-flag)
  (if
   (null? opt-proof-or-thm-name-and-unfold-let-flag)
   (proof-to-extracted-term (current-proof) #f)
   (let ((first (car opt-proof-or-thm-name-and-unfold-let-flag))
	 (rest (cdr opt-proof-or-thm-name-and-unfold-let-flag)))
     (if
      (null? rest)
      (if (or (proof-form? first) (string? first))
	  (let*  ((proof-or-thm-name first)
		  (proof (if (proof-form? proof-or-thm-name)
			     proof-or-thm-name
			     (theorem-name-to-proof proof-or-thm-name))))
	    (cond
	     ((formula-of-nulltype? (proof-to-formula proof)) 'eps)
	     ((string? proof-or-thm-name)
	      (theorem-to-extracted-term
	       (theorem-name-to-aconst proof-or-thm-name)
	       #f)) ;no unfolding of cId
	     (else (let ((avar-to-var (make-avar-to-var)))
		     (proof-to-extracted-term-aux proof avar-to-var #f)))))
					;else first is the unfold-let-flag
	  (let ((avar-to-var (make-avar-to-var)))
	    (proof-to-extracted-term-aux (current-proof) avar-to-var first)))
      (let ((unfold-let-flag (car rest)))
	(if (or (proof-form? first) (string? first))
	    (let*  ((proof-or-thm-name first)
		    (proof (if (proof-form? proof-or-thm-name)
			       proof-or-thm-name
			       (theorem-name-to-proof proof-or-thm-name))))
	      (cond
	       ((formula-of-nulltype? (proof-to-formula proof)) 'eps)
	       ((string? proof-or-thm-name)
		(theorem-to-extracted-term
		 (theorem-name-to-aconst proof-or-thm-name)
		 unfold-let-flag))
	       (else (let ((avar-to-var (make-avar-to-var)))
		       (proof-to-extracted-term-aux
			proof avar-to-var unfold-let-flag)))))
	    (myerror "proof-to-extracted-term"
		     "proof or theorem name expected"
		     first)))))))

(define (proof-to-extracted-term-aux proof avar-to-var unfold-let-flag)
  (case (tag proof)
    ((proof-in-avar-form)
     (make-term-in-var-form
      (avar-to-var (proof-in-avar-form-to-avar proof))))
    ((proof-in-aconst-form)
     (let ((aconst (proof-in-aconst-form-to-aconst proof)))
       (case (aconst-to-kind aconst)
	 ((axiom) (axiom-to-extracted-term aconst))
	 ((theorem) (theorem-to-extracted-term aconst unfold-let-flag))
	 ((global-assumption)
	  (global-assumption-to-extracted-term aconst avar-to-var))
	 (else (myerror "proof-to-extracted-term-aux"
			"unknown kind of aconst"
			(aconst-to-kind aconst))))))
    ((proof-in-imp-intro-form)
     (let* ((avar (proof-in-imp-intro-form-to-avar proof))
	    (avar-type (formula-to-et-type (avar-to-formula avar)))
	    (kernel (proof-in-imp-intro-form-to-kernel proof))
	    (kernel-term (proof-to-extracted-term-aux
			  kernel avar-to-var unfold-let-flag)))
       (if (nulltype? avar-type)
	   kernel-term
	   (make-term-in-abst-form (avar-to-var avar) kernel-term))))
    ((proof-in-imp-elim-form)
     (let* ((op (proof-in-imp-elim-form-to-op proof))
	    (arg (proof-in-imp-elim-form-to-arg proof))
	    (arg-type (formula-to-et-type (proof-to-formula arg)))
	    (op-term (proof-to-extracted-term-aux
		      op avar-to-var unfold-let-flag)))
       (if (nulltype? arg-type)
	   op-term
	   (make-term-in-app-form
	    op-term (proof-to-extracted-term-aux
		     arg avar-to-var unfold-let-flag)))))
    ((proof-in-impnc-intro-form)
     (proof-to-extracted-term-aux
      (proof-in-impnc-intro-form-to-kernel proof)
      avar-to-var unfold-let-flag))
    ((proof-in-impnc-elim-form)
     (proof-to-extracted-term-aux
      (proof-in-impnc-elim-form-to-op proof) avar-to-var unfold-let-flag))
    ((proof-in-and-intro-form)
     (let* ((left (proof-in-and-intro-form-to-left proof))
	    (right (proof-in-and-intro-form-to-right proof))
	    (left-type (formula-to-et-type (proof-to-formula left)))
	    (right-type (formula-to-et-type (proof-to-formula right))))
       (if (nulltype? left-type)
	   (proof-to-extracted-term-aux right avar-to-var unfold-let-flag)
	   (if (nulltype? right-type)
	       (proof-to-extracted-term-aux
		left avar-to-var unfold-let-flag)
	       (make-term-in-pair-form
		(proof-to-extracted-term-aux
		 left avar-to-var unfold-let-flag)
		(proof-to-extracted-term-aux
		 right avar-to-var unfold-let-flag))))))
    ((proof-in-and-elim-left-form)
     (let* ((kernel (proof-in-and-elim-left-form-to-kernel proof))
	    (formula (proof-to-formula kernel))
	    (left-type (formula-to-et-type (and-form-to-left formula)))
	    (right-type (formula-to-et-type (and-form-to-right formula)))
	    (kernel-term (proof-to-extracted-term-aux
			  kernel avar-to-var unfold-let-flag)))
       (if (or (nulltype? left-type) (nulltype? right-type))
	   kernel-term
	   (make-term-in-lcomp-form kernel-term))))
    ((proof-in-and-elim-right-form)
     (let* ((kernel (proof-in-and-elim-right-form-to-kernel proof))
	    (formula (proof-to-formula kernel))
	    (left-type (formula-to-et-type (and-form-to-left formula)))
	    (right-type (formula-to-et-type (and-form-to-right formula)))
	    (kernel-term (proof-to-extracted-term-aux
			  kernel avar-to-var unfold-let-flag)))
       (if (or (nulltype? left-type) (nulltype? right-type))
	   kernel-term
	   (make-term-in-rcomp-form kernel-term))))
    ((proof-in-all-intro-form)
     (let ((var (proof-in-all-intro-form-to-var proof))
	   (kernel (proof-in-all-intro-form-to-kernel proof)))
       (make-term-in-abst-form
	var (proof-to-extracted-term-aux kernel avar-to-var unfold-let-flag))))
    ((proof-in-all-elim-form)
     (let ((op (proof-in-all-elim-form-to-op proof))
	   (arg (proof-in-all-elim-form-to-arg proof)))
       (make-term-in-app-form
	(proof-to-extracted-term-aux op avar-to-var unfold-let-flag) arg)))
    ((proof-in-allnc-intro-form)
     (let ((kernel (proof-in-allnc-intro-form-to-kernel proof)))
       (proof-to-extracted-term-aux kernel avar-to-var unfold-let-flag)))
    ((proof-in-allnc-elim-form)
     (let ((op (proof-in-allnc-elim-form-to-op proof)))
       (proof-to-extracted-term-aux op avar-to-var unfold-let-flag)))
    (else (myerror "proof-to-extracted-term-aux"
		   "proof tag expected" (tag proof)))))

(define (axiom-to-extracted-term aconst)
  (let ((name (aconst-to-name aconst)))
    (cond
     ((string=? "Ind" name)
      (make-term-in-const-form
       (apply all-formulas-to-et-rec-const
	      (aconst-to-repro-data aconst))))
     ((string=? "Cases" name)
      (cases-aconst-to-if-term aconst))
     ((string=? "GInd" name)
      (make-term-in-const-form
       (gind-aconst-to-et-grecguard-const aconst)))
     ((string=? "Intro" name)
      (let* ((number-and-idpc (aconst-to-repro-data aconst))
	     (idpc (cadr number-and-idpc))
	     (name (idpredconst-to-name idpc))
	     (opt-alg-name (idpredconst-name-to-opt-alg-name name))
	     (string (if (pair? opt-alg-name)
			 (car opt-alg-name)
			 (myerror "axiom-to-extracted-term"
				  "opt-alg-name expected"
				  idpc))))
	(apply number-and-idpredconst-to-et-constr-term number-and-idpc)))
     ((string=? "Elim" name)
      (let* ((uninst-fla (aconst-to-uninst-formula aconst))
	     (kernel (all-allnc-form-to-final-kernel uninst-fla))
	     (prems (imp-impnc-form-to-premises kernel))
	     (idpc-fla (if (pair? prems) (car prems)
			   (myerror "axiom-to-extracted-term"
				    "imp premises expected in"
				    kernel)))
	     (pred (if (predicate-form? idpc-fla)
		       (predicate-form-to-predicate idpc-fla)
		       (myerror "axiom-to-extracted-term"
				"predicate formula expected"
				idpc-fla)))
	     (idpc-name (if (idpredconst-form? pred)
			    (idpredconst-to-name pred)
			    (myerror "axiom-to-extracted-term"
				     "idpredconst expected" pred)))
	     (opt-alg-name (idpredconst-name-to-opt-alg-name idpc-name))
	     (clauses (idpredconst-name-to-clauses idpc-name)))
	(cond ;uniform one-clause defined idpc
	 ((and ;invariant idpc
	   (null? (idpredconst-name-to-opt-alg-name idpc-name))
	   (or ;either a special one allowing arbitrary conclusions
					;(to be extended to e.g. EvenMR)
	    (member idpc-name '("EqD" "ExU" "AndU"))
					;or a uniform one-clause defined idpc
	    (and (= 1 (length clauses))
		 (predicate-form?
		  (impnc-form-to-final-conclusion
		   (allnc-form-to-final-kernel (car clauses)))))))
	  (let* ;then the extracted term is an identity
	      ((identity-type (formula-to-et-type (aconst-to-formula aconst)))
	       (val-type (arrow-form-to-val-type identity-type))
	       (var (type-to-new-var val-type)))
	    (make-term-in-abst-form var (make-term-in-var-form var))))
	 ((and ;identity idpc
	   (pair? opt-alg-name)
	   (string=? "identity" (car opt-alg-name)))
	  (let* ((imp-formulas (aconst-to-repro-data aconst))
		 (imp-formula (car imp-formulas))
		 (prem (imp-form-to-premise imp-formula))
		 (idpc (predicate-form-to-predicate prem))
		 (arg-type (idpredconst-to-et-type idpc))
		 (tpsubst (aconst-to-tpsubst aconst))
		 (concl (imp-impnc-form-to-final-conclusion kernel))
		 (subst-concl (formula-substitute concl tpsubst))
		 (val-type
		  (if (not (formula-of-nulltype? subst-concl))
		      (formula-to-et-type subst-concl)
		      (myerror "axiom-to-extracted-term"
			       "formula with content expected"
			       subst-concl))))
	    (if (nulltype? arg-type) ;then the extracted term is [b]b
		(let ((b (type-to-new-var val-type)))
		  (make-term-in-abst-form
		   b (make-term-in-var-form b)))
					;else the extracted term is [x,f]f x
		(let ((x (type-to-new-var arg-type))
		      (f (type-to-new-var
			  (make-arrow arg-type val-type))))
		  (mk-term-in-abst-form
		   x f (make-term-in-app-form
			(make-term-in-var-form f)
			(make-term-in-var-form x)))))))
	 (else ;default case
	  (make-term-in-const-form
	   (apply imp-formulas-to-et-rec-const
		  (aconst-to-repro-data aconst)))))))
     ((string=? "Closure" name)
      (let* ((tpsubst (aconst-to-tpsubst aconst))
	     (uninst-fla (aconst-to-uninst-formula aconst))
	     (kernel (all-allnc-form-to-final-kernel uninst-fla))
	     (prem (imp-form-to-premise kernel))
	     (subst-prem (formula-substitute prem tpsubst))
	     (alg (if (not (formula-of-nulltype? subst-prem))
		      (formula-to-et-type subst-prem)
		      (myerror "axiom-to-extracted-term"
			       "formula with content expected"
			       subst-prem))))
	(make-term-in-const-form (alg-to-destr-const alg))))
     ((string=? "Gfp" name)
      (let* ((inst-fla (aconst-to-inst-formula aconst))
	     (et-type (formula-to-et-type inst-fla))
	     (alg (arrow-form-to-final-val-type et-type))
	     (alg-name (if (alg-form? alg)
			   (alg-form-to-name alg)
			   (myerror "axiom-to-extracted-term"
				    "algebra form expected" alg)))
	     (alg-types (alg-form-to-types alg))
	     (simalg-names (alg-name-to-simalg-names alg-name))
	     (arg-types (arrow-form-to-arg-types et-type))
	     (improper-corec? (= (length simalg-names)
				 (length arg-types)))
	     (uninst-step-types (if improper-corec?
				    arg-types
				    (cdr arg-types)))
	     (f-or-types (map (lambda (type)
				(if (arrow-form? type)
				    (arrow-form-to-arg-type type)
				    #f))
			      uninst-step-types))
	     (alg-or-arrow-types
	      (map (lambda (f-or-type simalg-name)
		     (if f-or-type
			 (make-arrow
			  f-or-type
			  (apply make-alg simalg-name alg-types))
			 (apply make-alg simalg-name alg-types)))
		   f-or-types simalg-names))
	     (alg-or-arrow-type
	      (if improper-corec?
		  alg
		  (make-arrow (car arg-types) alg)))
	     (rest-alg-or-arrow-types
	      (remove alg-or-arrow-type alg-or-arrow-types))
	     (corec-const (apply alg-or-arrow-types-to-corec-const
				 alg-or-arrow-type
				 rest-alg-or-arrow-types)))
	(make-term-in-const-form corec-const)))
     ((string=? "Ex-Intro" name)
      (ex-formula-to-ex-intro-et (car (aconst-to-repro-data aconst))))
     ((string=? "Ex-Elim" name)
      (apply ex-formula-and-concl-to-ex-elim-et (aconst-to-repro-data aconst)))
     ((string=? "InhabTotal" name)
      (let* ((formula (aconst-to-formula aconst))
	     (args (predicate-form-to-args formula)))
	(car args)))
     ((string=? "Exnc-Intro" name) ;obsolete
      (exnc-formula-to-exnc-intro-et (car (aconst-to-repro-data aconst))))
     ((string=? "Exnc-Elim" name) ;obsolete
      (apply exnc-formula-and-concl-to-exnc-elim-et
	     (aconst-to-repro-data aconst)))
     ((string=? "Eq-Compat" name) ;obsolete
      (let* ((formula (unfold-formula (aconst-to-formula aconst)))
	     (type (formula-to-et-type formula))
	     (arg-type (if (arrow-form? type)
			   (arrow-form-to-arg-type type)
			   (myerror "axiom-to-extracted-term"
				    "arrow type expected"
				    type)))
	     (var (type-to-new-var arg-type)))
	(make-term-in-abst-form var (make-term-in-var-form var))))
					;the next item is obsolete
     ((or (and (<= (string-length "AllTotal") (string-length name))
	       (string=? (substring name 0 (string-length "AllTotal"))
			 "AllTotal"))
	  (and (<= (string-length "AllncTotal") (string-length name))
	       (string=? (substring name 0 (string-length "AllncTotal"))
			 "AllncTotal"))
	  (and (<= (string-length "ExTotal") (string-length name))
	       (string=? (substring name 0 (string-length "ExTotal"))
			 "ExTotal")))
      (let* ((formula (unfold-formula (aconst-to-formula aconst)))
	     (type (formula-to-et-type formula))
	     (arg-type (if (arrow-form? type)
			   (arrow-form-to-arg-type type)
			   (myerror "axiom-to-extracted-term"
				    "arrow type expected"
				    type)))
	     (var (type-to-new-var arg-type)))
	(make-term-in-abst-form var (make-term-in-var-form var))))
					;the next item is obsolete
     ((or (and (<= (string-length "All-AllPartial") (string-length name))
	       (member (substring name 0 (string-length "All-AllPartial"))
		       (list "All-AllPartial" "AllPartial-All")))
	  (and (<= (string-length "ExPartial-Ex") (string-length name))
	       (member (substring name 0 (string-length "ExPartial-Ex"))
		       (list "ExPartial-Ex" "Ex-ExPartial"))))
      (let* ((formula (unfold-formula (aconst-to-formula aconst)))
	     (type (formula-to-et-type formula))
	     (arg-type (if (arrow-form? type)
			   (arrow-form-to-arg-type type)
			   (myerror "axiom-to-extracted-term"
				    "arrow type expected"
				    type)))
	     (var (type-to-new-var arg-type)))
	(make-term-in-abst-form var (make-term-in-var-form var))))
     (else (myerror "axiom-to-extracted-term" "axiom expected" name)))))

(define (theorem-to-extracted-term aconst . opt-unfold-let-flag)
  (if
   (null? opt-unfold-let-flag)
   (theorem-to-extracted-term aconst #f)
   (let* ((unfold-let-flag (car opt-unfold-let-flag))
	  (thm-name (aconst-to-name aconst))
	  (proof (theorem-name-to-proof thm-name))
	  (tpsubst (aconst-to-tpsubst aconst))
	  (tsubst (list-transform-positive tpsubst
		    (lambda (x) (tvar-form? (car x)))))
	  (psubst (list-transform-positive tpsubst
		    (lambda (x) (pvar-form? (car x))))))
     (cond
      ((string=? "InhabTotal" thm-name)
       (let ((formula (aconst-to-formula aconst))) ;Total(Inhab rho)
	 (car (predicate-form-to-args formula))))
      ((member thm-name (list "AllTotalIntro" "AllTotalElim"
			      "AllncTotalIntro" "AllncTotalElim"
			      "ExTotalIntro" "ExTotalElim" ;obsolete:
			      "All-AllPartial" "AllPartial-All"
			      "Ex-ExPartial" "ExPartial-Ex"))
       (let* ((formula (unfold-formula (aconst-to-formula aconst)))
	      (type (formula-to-et-type formula))
	      (arg-type (if (arrow-form? type)
			    (arrow-form-to-arg-type type)
			    (myerror "theorem-to-extracted-term"
				     "arrow type expected" type)))
	      (var (type-to-new-partial-var arg-type)))
	 (make-term-in-abst-form var (make-term-in-var-form var))))
      ((member thm-name (list "Eq-Compat" "Eq-Compat-Rev"))
       (comment "warning: Equal is obsolete.  Use EqD instead.")
       (let* ((formula (unfold-formula (aconst-to-formula aconst)))
	      (type (formula-to-et-type formula))
	      (arg-type (if (arrow-form? type)
			    (arrow-form-to-arg-type type)
			    (myerror "theorem-to-extracted-term"
				     "arrow type expected" type)))
	      (var (type-to-new-partial-var arg-type)))
	 (make-term-in-abst-form var (make-term-in-var-form var))))
      ((and (final-substring? "Total" thm-name)
	    (pconst-name? (substring thm-name 0 (- (string-length thm-name)
						   (string-length "Total")))))
       (let* ((pconst (pconst-name-to-pconst
		       (substring thm-name 0 (- (string-length thm-name)
						(string-length "Total")))))
	      (subst-pconst (const-substitute pconst tsubst #t)))
	 (make-term-in-const-form subst-pconst)))
      ((and (final-substring? "STotal" thm-name)
	    (pconst-name? (substring thm-name 0 (- (string-length thm-name)
						   (string-length "STotal")))))
       (proof-to-extracted-term proof))
      ((and (final-substring? "EqTotal" thm-name)
	    (assoc (string-downcase
		    (substring thm-name 0 (- (string-length thm-name)
					     (string-length "EqTotal"))))
		   ALGEBRAS))
       (let* ((formula (aconst-to-formula aconst))
	      (concl (imp-impnc-all-allnc-form-to-final-conclusion formula))
	      (arg (if (predicate-form? concl)
		       (car (predicate-form-to-args concl))
		       (myerror "theorem-to-extracted-term"
				"predicate form expected" concl)))
	      (free (term-to-free arg))
	      (type (if (pair? free)
			(var-to-type (car free))
			(myerror "theorem-to-extracted-term"
				 "free variables expected in" arg))))
	 (if (not (finalg? type))
	     (myerror "theorem-to-extracted-term"
		      "finalg variable expected" (car free)))
	 (apply mk-term-in-abst-form (append free (list arg)))))
      ((and (final-substring? "ETotal" thm-name)
	    (assoc (string-downcase
		    (substring thm-name 0 (- (string-length thm-name)
					     (string-length "ETotal"))))
		   ALGEBRAS))
       (let* ((formula (aconst-to-formula aconst))
	      (concl (imp-impnc-all-allnc-form-to-final-conclusion formula))
	      (arg (if (predicate-form? concl)
		       (car (predicate-form-to-args concl))
		       (myerror "theorem-to-extracted-term"
				"predicate form expected" concl)))
	      (free (term-to-free arg))
	      (type (if (pair? free)
			(var-to-type (car free))
			(myerror "theorem-to-extracted-term"
				 "free variables expected in" arg))))
	 (if (not (finalg? type))
	     (myerror "theorem-to-extracted-term"
		      "finalg variable expected" (car free)))
	 (apply mk-term-in-abst-form (append free (list arg)))))
      ((string=? "BooleIfTotal" thm-name)
       (let* ((formula (aconst-to-formula aconst))
	      (concl (imp-impnc-all-allnc-form-to-final-conclusion formula))
	      (args (if (predicate-form? concl)
			(predicate-form-to-args concl)
			(myerror "theorem-to-extracted-term"
				 "predicate form expected" concl)))
	      (if-term (if (pair? args) (car args)
			   (myerror "theorem-to-extracted-term"
				    "arguments expected" concl)))
	      (free (term-to-free if-term)))
	 (apply mk-term-in-abst-form (append free (list if-term)))))
      ((or (member thm-name (list "EqDCompat" "EqDCompatRev"))
	   (and (string=? thm-name "Id") unfold-let-flag))
       (let* ((uninst-formula (aconst-to-uninst-formula aconst))
	      (concl (imp-impnc-all-allnc-form-to-final-conclusion
		      uninst-formula))
	      (pvar (predicate-form-to-predicate concl))
	      (cterm (let ((info (assoc pvar tpsubst)))
		       (if info (cadr info)
			   (predicate-to-cterm pvar))))
	      (cterm-formula (cterm-to-formula cterm))
	      (et-type (formula-to-et-type cterm-formula))
	      (var (if (nulltype? et-type)
		       (myerror "theorem-to-extracted-term"
				"computationally relevant formula expected"
				formula)
		       (type-to-new-partial-var et-type))))
	 (make-term-in-abst-form var (make-term-in-var-form var))))
      (else (make-term-in-const-form
	     (theorem-or-global-assumption-to-pconst aconst)))))))

(define (global-assumption-to-extracted-term aconst avar-to-var)
  (let* ((name (aconst-to-name aconst))
	 (info (assoc name GLOBAL-ASSUMPTIONS)))
    (if
     info
     (cond
      ((string=? "StabLog" name)
       (let* ((formula (unfold-formula (aconst-to-formula aconst)))
	      (kernel (allnc-form-to-final-kernel formula))
	      (concl (imp-form-to-conclusion kernel)))
	 (case (tag concl)
	   ((atom predicate ex exnc)
	    (if
	     (not (equal? falsity-log concl))
	     (let* ((pconst
		     (theorem-or-global-assumption-to-pconst aconst))
		    (term (make-term-in-const-form pconst)))
	       (comment "StabLog realized by ad hoc term "
			(term-to-string term))
	       term) ;else first unfold
	     (proof-to-extracted-term-aux
	      (proof-of-stab-log-at concl) avar-to-var)))
	   ((imp impnc and all allnc) ;first unfold
	    (proof-to-extracted-term-aux
	     (proof-of-stab-log-at concl) avar-to-var))
	   (else (myerror "global-assumption-to-extracted-term"
			  "formula expected"
			  concl)))))
      ((string=? "EfqLog" name)
       (let* ((formula (unfold-formula (aconst-to-formula aconst)))
	      (kernel (allnc-form-to-final-kernel formula))
	      (concl (imp-form-to-conclusion kernel)))
	 (case (tag concl)
	   ((atom predicate ex exnc)
	    (if (not (equal? falsity-log concl))
		(let* ((pconst
			(theorem-or-global-assumption-to-pconst aconst))
		       (term (make-term-in-const-form pconst)))
		  (comment "EfqLog realized by ad hoc term "
			   (term-to-string term))
		  term) ;else first unfold
		(proof-to-extracted-term-aux
		 (proof-of-efq-log-at concl) avar-to-var)))
	   ((imp impnc and all allnc) ;first unfold
	    (proof-to-extracted-term-aux
	     (proof-of-efq-log-at concl) avar-to-var))
	   (else (myerror
		  "global-assumption-to-extracted-term" "formula expected"
		  concl)))))
      ((string=? "Efq" name)
       (let* ((formula (aconst-to-formula aconst))
	      (etype (formula-to-et-type formula)))
	 (type-to-canonical-inhabitant etype)))
      ((or (and (<= (string-length "Eq-Compat-Rev")
		    (string-length name))
		(string=?
		 (substring name 0 (string-length "Eq-Compat-Rev"))
		 "Eq-Compat-Rev"))
	   (and (<= (string-length "Compat-Rev")
		    (string-length name))
		(string=?
		 (substring name 0 (string-length "Compat-Rev"))
		 "Compat-Rev"))
	   (and (<= (string-length "Compat")
		    (string-length name))
		(string=?
		 (substring name 0 (string-length "Compat"))
		 "Compat")))
       (let* ((formula (unfold-formula (aconst-to-formula aconst)))
	      (type (formula-to-et-type formula))
	      (arg-type (if (arrow-form? type)
			    (arrow-form-to-arg-type type)
			    (myerror "global-assumption-to-extracted-term"
				     "arrow type expected"
				     type)))
	      (var (type-to-new-partial-var arg-type)))
	 (make-term-in-abst-form var (make-term-in-var-form var))))
      (else
       (make-term-in-const-form
	(theorem-or-global-assumption-to-pconst aconst))))
     (myerror "global-assumption-to-extracted-term"
	      "global assumption expected"
	      name))))

(define (all-formulas-to-et-rec-const . all-formulas)
  (if (nested-alg-name?
       (alg-form-to-name (var-to-type (all-form-to-var (car all-formulas)))))
      (myerror "all-formulas-to-et-rec-const"
	       "all-formula for an unnested algebra expected"
	       (car all-formulas)
	       "unfold all-formula and use imp-formulas-to-elim-aconst"))
  (let* ((uninst-imp-formulas-and-tpsubst
	  (apply all-formulas-to-uninst-imp-formulas-and-tpsubst all-formulas))
	 (uninst-imp-formulas (car uninst-imp-formulas-and-tpsubst))
	 (tpsubst (cadr uninst-imp-formulas-and-tpsubst))
	 (tsubst (list-transform-positive tpsubst
		   (lambda (x) (tvar-form? (car x)))))
	 (psubst (list-transform-positive tpsubst
		  (lambda (x) (pvar-form? (car x)))))
	 (relevant-psubst (list-transform-positive psubst
			   (lambda (x)
			     (not (formula-of-nulltype?
				   (cterm-to-formula (cadr x)))))))
	 (pvars (map car relevant-psubst))
	 (cterms (map cadr relevant-psubst))
	 (et-types (map (lambda (cterm)
			  (formula-to-et-type (cterm-to-formula cterm)))
			cterms))
	 (new-tvars (map PVAR-TO-TVAR pvars))
	 (new-tsubst (make-substitution new-tvars et-types))
	 (uninst-recop-types (map formula-to-et-type uninst-imp-formulas))
	 (vars (map all-form-to-var all-formulas))
	 (types (map var-to-type vars))
	 (alg-names
	  (map (lambda (type)
		 (if (alg-form? type)
		     (alg-form-to-name type)
		     (myerror "all-formulas-to-et-rec-const" "alg expected"
			      type)))
	       types))
	 (alg-names-with-uninst-recop-types
	  (map list alg-names uninst-recop-types))
	 (simalg-names (alg-name-to-simalg-names (car alg-names)))
	 (sorted-alg-names (list-transform-positive simalg-names
			     (lambda (x) (member x alg-names))))
	 (typed-constr-names
	  (apply append
		 (map alg-name-to-typed-constr-names sorted-alg-names)))
	 (constr-names (map typed-constr-name-to-name typed-constr-names))
	 (alg-name (car alg-names))
	 (uninst-recop-type
	  (cadr (assoc alg-name alg-names-with-uninst-recop-types)))
	 (inst-recop-type (type-substitute uninst-recop-type
					   (append tsubst new-tsubst))))
    (alg-name-etc-to-rec-const
     alg-name uninst-recop-type (append tsubst new-tsubst) inst-recop-type
     0 constr-names alg-names-with-uninst-recop-types)))

(define (cases-aconst-to-if-term aconst)
  (let* ((uninst-imp-formula (aconst-to-uninst-formula aconst))
	 (tpsubst (aconst-to-tpsubst aconst))
	 (tsubst (list-transform-positive tpsubst
		   (lambda (x) (tvar-form? (car x)))))
	 (psubst (list-transform-positive tpsubst
		   (lambda (x) (pvar-form? (car x)))))
	 (relevant-psubst (list-transform-positive psubst
			    (lambda (x)
			      (not (formula-of-nulltype?
				    (cterm-to-formula (cadr x)))))))
	 (pvars (map car relevant-psubst))
	 (cterms (map cadr relevant-psubst))
	 (et-types (map (lambda (cterm)
			  (formula-to-et-type
			   (cterm-to-formula cterm)))
			cterms))
	 (new-tvars (map PVAR-TO-TVAR pvars))
	 (new-tsubst (make-substitution new-tvars et-types))
	 (uninst-casesop-type (formula-to-et-type uninst-imp-formula))
	 (s ;number of step types
	  (- (length (arrow-form-to-arg-types uninst-casesop-type)) 1))
	 (inst-casesop-type
	  (type-substitute uninst-casesop-type (append tsubst new-tsubst)))
	 (alt-types
          (cdr (arrow-form-to-arg-types inst-casesop-type (+ s 1))))
	 (test-type (arrow-form-to-arg-type inst-casesop-type))
	 (alt-vars (map type-to-new-var alt-types))
	 (test-var (type-to-new-var test-type)))
    (apply mk-term-in-abst-form
	   test-var
	   (append alt-vars
		   (list (make-term-in-if-form
			  (make-term-in-var-form test-var)
			  (map make-term-in-var-form alt-vars)))))))

(define (gind-aconst-to-et-grecguard-const aconst)
  (let* ((uninst-gind-formula (aconst-to-uninst-formula aconst))
         (measure-var-and-vars (all-form-to-vars uninst-gind-formula))
         (vars (cdr measure-var-and-vars))
         (m (length vars))
         (tpsubst (aconst-to-tpsubst aconst))
         (tsubst (list-transform-positive tpsubst
                   (lambda (x) (tvar-form? (car x)))))
         (pvar-and-cterm
          (list-search-positive tpsubst
            (lambda (x) (pvar-form? (car x)))))
         (cterm (cadr pvar-and-cterm))
         (et-type (formula-to-et-type (cterm-to-formula cterm)))
         (arg-types (map var-to-type vars))
	 (subst-arg-types (map (lambda (type) (type-substitute type tsubst))
			       arg-types))
         (type-info (append subst-arg-types (list et-type))))
    (type-info-to-grecguard-const type-info)))

;; Terminology:
;; clause            - with assigned predicate variable instead of the idpc
;; uninst-intro-fla  - with idpc substituted, but still with tvars, param-pvars
;; intro-fla         - fully substituted

(define (number-and-idpredconst-to-et-constr-term i idpc)
  (let* ((name (idpredconst-to-name idpc))
	 (opt-alg-name (idpredconst-name-to-opt-alg-name name))
	 (alg-name (if (pair? opt-alg-name) (car opt-alg-name)
		       (myerror "number-and-idpredconst-to-et-constr-term"
				"alg name expected for" name)))
	 (clauses (idpredconst-name-to-clauses name))
	 (clause
	  (if (and (integer? i) (not (negative? i)) (< i (length clauses)))
	      (list-ref clauses i)
	      (myerror "number-and-idpredconst-to-et-constr-term" i
		       "should be an index of a clause for" name)))
	 (clauses-with-names (idpredconst-name-to-clauses-with-names name))
	 (clause-with-name (list-ref clauses-with-names i))
	 (types (idpredconst-to-types idpc))
	 (cterms (idpredconst-to-cterms idpc))
	 (tvars (idpredconst-name-to-tvars name))
	 (idpc-pvars (idpredconst-name-to-pvars name))
	 (param-pvars (idpredconst-name-to-param-pvars name))
	 (simidpc-names (idpredconst-name-to-simidpc-names name))
	 (simidpc-clauses
	  (apply union (map idpredconst-name-to-clauses simidpc-names)))
	 (simidpc-et-types (map formula-to-et-type simidpc-clauses))
	 (simidpc-et-tvars
	  (set-minus (apply union (map type-to-tvars simidpc-et-types))
		     idpc-pvars))
	 (relevant-types (do ((l1 tvars (cdr l1))
			      (l2 types (cdr l2))
			      (res '() (let ((tvar (car l1))
					     (type (car l2)))
					 (if (member tvar simidpc-et-tvars)
					     (cons type res)
					     res))))
			     ((null? l2) (reverse res))))
	 (relevant-cterm-types
	  (do ((l1 param-pvars (cdr l1))
	       (l2 cterms (cdr l2))
	       (res '() (let* ((pvar (car l1))
			       (cterm (car l2))
			       (formula (cterm-to-formula cterm))
			       (cterm-et-type (formula-to-et-type formula)))
			  (if (and
			       (pvar-with-positive-content? pvar)
			       (member (PVAR-TO-TVAR pvar) simidpc-et-tvars))
			      (cons cterm-et-type res)
			      res))))
	      ((null? l1) (reverse res))))
	 (val-types (append relevant-types relevant-cterm-types))
	 (nc-indicator (map nulltype? val-types))
	 (alg-name-et
	  (alg-name-and-nc-indicator-to-alg-name alg-name nc-indicator)))
    (cond
     ((string=? "identity" alg-name-et)
      (let* ((et-type (idpredconst-to-et-type idpc))
	     (var (type-to-new-partial-var et-type)))
	(make-term-in-abst-form var (make-term-in-var-form var))))
     ((string=? "nulltype" alg-name-et) 'eps)
     (else
      (let* ((known-alg-name?
	      (not (string=? (string-append "alg" name) alg-name)))
	     (alg-tvars (alg-name-to-tvars alg-name))
	     (tsubst (make-substitution alg-tvars val-types))
	     (constr-name
	      (cond
	       (known-alg-name?
		(car (list-ref (alg-name-to-typed-constr-names alg-name-et) i)))
	       ((< 1 (length clause-with-name))
		(let ((suffixes
		       (if (string=? alg-name alg-name-et)
			   '()
			   (map (lambda (b) (if b "Nc" "Cr")) nc-indicator))))
		  (apply string-append "C" (cadr clause-with-name) suffixes)))
	       (else (myerror "number-and-idpredconst-to-et-constr-term"
			      "constr name missing for" clause))))
	     (constr (constr-name-to-constr constr-name))
	     (subst-constr (const-substitute constr tsubst #t)))
	(make-term-in-const-form subst-constr))))))

;; imp-formulas is a list of formulas I xs^ -> A[xs^].  uninst-elim-formula
;; is Ij xs^ -> K1[Xs,Ps] -> .. -> Kk[Xs,Ps] -> Pj xs^

(define (imp-formulas-to-et-rec-const . imp-formulas)
  (let* ((uninst-elim-formulas-etc
	  (apply imp-formulas-to-uninst-elim-formulas-etc imp-formulas))
	 (uninst-elim-formulas (car uninst-elim-formulas-etc))
	 (tsubst (cadr uninst-elim-formulas-etc))
	 (psubst-for-param-pvars (caddr uninst-elim-formulas-etc))
	 (psubst-for-pvars (cadddr uninst-elim-formulas-etc))
	 (uninst-recop-types (map formula-to-et-type uninst-elim-formulas))
	 (idpc-names (map (lambda (uninst-elim-formula)
			    (idpredconst-to-name
			     (predicate-form-to-predicate
			      (imp-form-to-premise uninst-elim-formula))))
			  uninst-elim-formulas))
	 (alg-names (map idpredconst-name-to-alg-name idpc-names))
	 (alg-names-with-uninst-recop-types
	  (map list alg-names uninst-recop-types))
	 (uninst-recop-type (car uninst-recop-types))
	 (alg-name (car alg-names))
	 (param-pvar-cterms (map cadr psubst-for-param-pvars))
	 (param-pvar-formulas (map cterm-to-formula param-pvar-cterms))
	 (param-pvar-et-types (map formula-to-et-type param-pvar-formulas))
	 (param-pvar-tsubst
	  (map (lambda (x param-pvar-et-type) ;x pair in psubst-for-param-pvars
		 (let* ((param-pvar (car x))
			(tvar (PVAR-TO-TVAR param-pvar)))
		   (list tvar param-pvar-et-type)))
	       psubst-for-param-pvars param-pvar-et-types))
	 (pvar-cterm-et-types
	  (map (lambda (cterm) (formula-to-et-type (cterm-to-formula cterm)))
	       (map cadr psubst-for-pvars)))
	 (pvar-tsubst
	  (map (lambda (x y) (let* ((pvar (car x))
				    (tvar (PVAR-TO-TVAR pvar)))
			       (list tvar y)))
	       psubst-for-pvars pvar-cterm-et-types))
	 (inst-recop-type
	  (type-substitute uninst-recop-type
			   (append tsubst param-pvar-tsubst pvar-tsubst)))
	 (simalg-names (alg-name-to-simalg-names alg-name))
	 (sorted-alg-names (list-transform-positive simalg-names
			     (lambda (x) (member x alg-names))))
	 (typed-constr-names
	  (apply append
		 (map alg-name-to-typed-constr-names sorted-alg-names)))
	 (constr-names (map typed-constr-name-to-name typed-constr-names)))
    (alg-name-etc-to-rec-const
     alg-name uninst-recop-type
     (append tsubst param-pvar-tsubst pvar-tsubst)
     inst-recop-type 0 constr-names
     alg-names-with-uninst-recop-types)))

(define (ex-formula-to-ex-intro-et ex-formula)
  (let* ((var (ex-form-to-var ex-formula))
         (kernel (ex-form-to-kernel ex-formula))
	 (kernel-type (formula-to-et-type kernel)))
    (if (nulltype? kernel-type)
	(make-term-in-abst-form var (make-term-in-var-form var))
	(let ((new-var (type-to-new-var kernel-type)))
	  (mk-term-in-abst-form
	   var new-var (make-term-in-pair-form
			(make-term-in-var-form var)
			(make-term-in-var-form new-var)))))))

(define (ex-formula-and-concl-to-ex-elim-et ex-formula concl)
  (let* ((var (ex-form-to-var ex-formula))
	 (type (var-to-type var))
         (kernel (ex-form-to-kernel ex-formula))
	 (kernel-type (formula-to-et-type kernel))
	 (ex-type (formula-to-et-type ex-formula))
	 (concl-type (formula-to-et-type concl)))
    (if (nulltype? kernel-type)
	(let* ((fct-type (make-arrow type concl-type))
	       (fct-var (type-to-new-var fct-type)))
	  (mk-term-in-abst-form
	   var fct-var (make-term-in-app-form
			(make-term-in-var-form fct-var)
			(make-term-in-var-form var))))
	(let* ((fct-type (mk-arrow type kernel-type concl-type))
	       (fct-var (type-to-new-var fct-type))
	       (pair-var (type-to-new-var (make-star type kernel-type)))
	       (pair-var-term (make-term-in-var-form pair-var)))
	  (mk-term-in-abst-form
	   pair-var fct-var
	   (mk-term-in-app-form
	    (make-term-in-var-form fct-var)
	    (make-term-in-lcomp-form pair-var-term)
	    (make-term-in-rcomp-form pair-var-term)))))))

(define (exnc-formula-to-exnc-intro-et exnc-formula) ;obsolete
  (let* ((kernel (exnc-form-to-kernel exnc-formula))
	 (kernel-type (formula-to-et-type kernel))
	 (new-var (type-to-new-var kernel-type)))
    (make-term-in-abst-form new-var (make-term-in-var-form new-var))))

(define (exnc-formula-and-concl-to-exnc-elim-et exnc-formula concl) ;obsolete
  (let* ((kernel (exnc-form-to-kernel exnc-formula))
	 (kernel-type (formula-to-et-type kernel))
	 (concl-type (formula-to-et-type concl))
	 (new-var (type-to-new-var concl-type)))
    (if (nulltype? kernel-type)
	(make-term-in-abst-form new-var (make-term-in-var-form new-var))
	(let* ((kernel-var (type-to-new-var kernel-type))
	       (fct-type (make-arrow kernel-type concl-type))
	       (fct-var (type-to-new-var fct-type)))
	  (mk-term-in-abst-form
	   kernel-var fct-var
	   (make-term-in-app-form
	    (make-term-in-var-form fct-var)
	    (make-term-in-var-form kernel-var)))))))

;; Moreover we initially supply the identity theorem Id: Pvar -> Pvar.
;; This can be done only here, because for add-theorem we need
;; formula-to-et-type.

(define id-proof
  (let* ((pvar (mk-pvar (make-arity)))
	 (predicate-formula (make-predicate-formula pvar))
	 (avar (make-avar predicate-formula -1 "")))
    (make-proof-in-imp-intro-form
     avar (make-proof-in-avar-form avar))))

(add-theorem "Id" id-proof)

;; Usage: When an object (value of a variable or realizer of a premise)
;; might be used more than once, make sure (if necessary by a cut) that
;; the goal has the form A -> B or all x A.  Now use Id: P -> P.
;; (use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?") is
;; often preferable, since (use "Id") can take a long time.  Its
;; realizer then has the form [f,x]f x.  If cId is not animated, one
;; obtains cId([x]body)arg, to be written [let x arg body].  When cId
;; is animated, normalization substitutes arg for x in body.

;; (animate "Id")
;; ;; ok, computation rule (cId alpha3) -> [(alpha3)_0](alpha3)_0 added
;; (deanimate "Id")

;; We add some initial inductive definitions.  This can be done only
;; here, since their clauses are added as theorems and might be c.r.

(set! COMMENT-FLAG #f)

(add-ids (list (list "EqD" (make-arity (py "alpha") (py "alpha"))))
	 '("allnc alpha^ EqD alpha^ alpha^" "InitEqD"))

(add-ids (list (list "ExD" (make-arity) "yprod"))
	 '("all alpha^((Pvar alpha)alpha^ -> ExD)" "InitExD"))

(add-ids (list (list "ExL" (make-arity) "identity"))
	 '("all alpha^((Pvar alpha)alpha^ --> ExL)" "InitExL"))

(add-ids (list (list "ExR" (make-arity) "identity"))
	 '("allnc alpha^((Pvar alpha)alpha^ -> ExR)" "InitExR"))

(add-ids (list (list "ExU" (make-arity)))
	 '("allnc alpha^((Pvar alpha)alpha^ --> ExU)" "InitExU"))

(add-ids (list (list "ExDT" (make-arity) "yprod"))
	 '("all alpha((Pvar alpha)alpha -> ExDT)" "InitExDT"))

(add-ids (list (list "ExLT" (make-arity) "identity"))
	 '("all alpha((Pvar alpha)alpha --> ExLT)" "InitExLT"))

(add-ids (list (list "ExRT" (make-arity) "identity"))
	 '("allnc alpha((Pvar alpha)alpha -> ExRT)" "InitExRT"))

(add-ids (list (list "ExUT" (make-arity)))
	 '("allnc alpha((Pvar alpha)alpha --> ExUT)" "InitExUT"))

(add-ids (list (list "AndD" (make-arity) "yprod"))
	 '("Pvar1 -> Pvar2 -> AndD" "InitAndD"))

(add-ids (list (list "AndL" (make-arity) "identity"))
 	 '("Pvar1 -> Pvar2 --> AndL" "InitAndL"))

(add-ids (list (list "AndR" (make-arity) "identity"))
	 '("Pvar1 --> Pvar2 -> AndR" "InitAndR"))

(add-ids (list (list "AndU" (make-arity)))
	 '("Pvar1 --> Pvar2 --> AndU" "InitAndU"))

(add-ids (list (list "OrD" (make-arity) "ysum"))
	 '("Pvar1 -> OrD" "InlOrD")
	 '("Pvar2 -> OrD" "InrOrD"))

(add-ids (list (list "OrR" (make-arity) "uysum"))
	 '("Pvar1 --> OrR" "InlOrR")
	 '("Pvar2 -> OrR" "InrOrR"))

(add-ids (list (list "OrL" (make-arity) "ysumu"))
	 '("Pvar1 -> OrL" "InlOrL")
	 '("Pvar2 --> OrL" "InrOrL"))

;; OrU has computational content, because we know on which side we are.

(add-ids (list (list "OrU" (make-arity) "boole"))
	 '("Pvar1 --> OrU" "InlOrU")
	 '("Pvar2 --> OrU" "InrOrU"))

(add-ids (list (list "OrNc" (make-arity)))
	 '("Pvar1 -> OrNc" "InlOrNc")
	 '("Pvar2 -> OrNc" "InrOrNc"))

;; atom-to-eqd-true-aconst and eqd-true-to-atom-aconst can be added
;; only here, because they need EqD.

(define atom-to-eqd-true-aconst
  (make-aconst "AtomToEqDTrue" 'axiom
	       (pf "all boole^(boole^ -> boole^ eqd True)")
	       empty-subst))

(define eqd-true-to-atom-aconst
  (make-aconst "EqDTrueToAtom" 'axiom
	       (pf "all boole^(boole^ eqd True -> boole^)")
	       empty-subst))

(define truth-proof
  (let* ((idpc (make-idpredconst "EqD" (list (make-alg "boole")) '()))
	 (initeqd-aconst (number-and-idpredconst-to-intro-aconst 0 idpc)))
    (mk-proof-in-elim-form
     (make-proof-in-aconst-form eqd-true-to-atom-aconst)
     (make-term-in-const-form true-const)
     (mk-proof-in-elim-form
      (make-proof-in-aconst-form initeqd-aconst)
      (make-term-in-const-form true-const)))))

(add-theorem "Truth" truth-proof)

(define truth-aconst (theorem-name-to-aconst "Truth"))

;; atom-true-proof can be defined only here, because it needs EqD
;; atom-to-eqd-true-aconst and eqd-true-to-atom-aconst

(define atom-true-proof
  (let* ((type (make-alg "boole"))
	 (name (default-var-name type))
	 (var1 (make-var type 1 0 name))
	 (var2 (make-var type 2 0 name))
	 (varterm1 (make-term-in-var-form var1))
	 (varterm2 (make-term-in-var-form var2))
	 (u1 (formula-to-new-avar (make-atomic-formula varterm1)))
	 (eqd-fla (make-eqd varterm1 varterm2)) ;p^ eqd q^
	 (true-term (make-term-in-const-form true-const))
	 (fla1 (make-atomic-formula (make-=-term varterm1 true-term)))
	 (fla2 (make-atomic-formula (make-=-term varterm2 true-term)))
	 (imp-fla (mk-imp eqd-fla fla2 fla1))
	 (aconst (imp-formulas-to-elim-aconst imp-fla))
	 (var (make-var type -1 0 name))
	 (varterm (make-term-in-var-form var))
	 (fla (make-atomic-formula (make-=-term varterm true-term)))
	 (u (make-avar fla -1 "u"))
	 (idpc (make-idpredconst "EqD" (list (make-alg "boole")) '()))
	 (initeqd-aconst (number-and-idpredconst-to-intro-aconst 0 idpc)))
    (mk-proof-in-intro-form
     var1 u1 (mk-proof-in-elim-form
	      (make-proof-in-aconst-form aconst)
	      varterm1 true-term
	      (mk-proof-in-elim-form ;p^ eqd True
	       (make-proof-in-aconst-form atom-to-eqd-true-aconst)
	       varterm1 (make-proof-in-avar-form u1))
	      (make-proof-in-allnc-intro-form ;allnc q^(q^ =True -> p^ =True)
	       var (make-proof-in-imp-intro-form
		    u (make-proof-in-avar-form u)))
	      (mk-proof-in-elim-form ;atom True
	       (make-proof-in-aconst-form eqd-true-to-atom-aconst)
	       true-term
	       (mk-proof-in-elim-form
		(make-proof-in-aconst-form initeqd-aconst)
		(make-term-in-const-form true-const)))))))

(add-theorem "AtomTrue" atom-true-proof)

(define atom-true-aconst
  (make-aconst "AtomTrue" 'theorem
	       (pf "all boole^(boole^ -> boole^ =True)")
	       empty-subst))

;; atom-false-proof can be defined only here, because it needs truth-aconst

(define atom-false-proof
  (let* ((type (make-alg "boole"))
	 (name (default-var-name type))
	 (var (make-var type -1 t-deg-one name))
	 (varterm (make-term-in-var-form var))
	 (u1 (make-avar (pf "T -> F") 1  "u"))
	 (u2 (make-avar (pf "F -> F") 2  "u")))
    (make-proof-in-all-intro-form
     var (mk-proof-in-elim-form
	  (make-proof-in-aconst-form
	   (all-formula-to-cases-aconst
	    (pf "all boole((boole -> F) -> boole=False)")))
	  varterm
	  (mk-proof-in-intro-form
	   u1 (mk-proof-in-elim-form
	       (make-proof-in-avar-form u1)
	       (make-proof-in-aconst-form truth-aconst)))
	  (mk-proof-in-intro-form
	   u2 (make-proof-in-aconst-form truth-aconst))))))

(add-theorem "AtomFalse" atom-false-proof)

(define atom-false-aconst
  (make-aconst "AtomFalse" 'theorem
	       (pf "all boole((boole -> F) -> boole=False)")
	       empty-subst))

;; efq-atom-proof imp-to-atom-proof atom-to-imp-proof
;; and-atom-to-left-proof and-atom-to-right-proof
;; atoms-to-and-atom-proof dec-cases-proof moved here, because they
;; need truth-aconst .

(define efq-atom-proof ;obsolete.  Use in examples/ordinals not really needed
  (let ((var (type-to-new-var (py "boole"))))
    (make-proof-in-all-intro-form
     var
     (mk-proof-in-elim-form
      (make-proof-in-aconst-form
       (all-formula-to-cases-aconst (pf "all boole(F -> boole)")))
      (make-term-in-var-form var)
      (let ((u1 (formula-to-new-avar (pf "F") "u")))
        (mk-proof-in-intro-form
         u1 (make-proof-in-aconst-form truth-aconst)))
      (let ((u1 (formula-to-new-avar (pf "F") "u")))
        (mk-proof-in-intro-form u1 (make-proof-in-avar-form u1)))))))

(add-theorem "Efq-Atom" efq-atom-proof) ;obsolete

(define efq-atom-aconst ;obsolete.  Use in examples/ordinals not really needed
  (make-aconst "Efq-Atom" 'theorem
	       (pf "all boole(F -> boole)")
	       empty-subst))

;; We prove "(boole1 -> boole2) -> boole1 impb boole2" from cases axioms

;; "all boole2((T -> boole2) -> True impb boole2) ->
;;  all boole2((F -> boole2) -> False impb boole2) ->
;;  all boole10,boole2((boole10 -> boole2) -> boole10 impb boole2)"

(define imp-to-atom-proof
  (let ((var1 (type-to-new-var (py "boole")))
        (var2 (type-to-new-var (py "boole")))
        (var3 (type-to-new-var (py "boole"))))
    (make-proof-in-all-intro-form
     var1
     (mk-proof-in-elim-form
      (make-proof-in-aconst-form
       (all-formula-to-cases-aconst
        (pf
	 "all boole1,boole2((boole1 -> boole2) -> ImpConst boole1 boole2)")))
      (make-term-in-var-form var1)
      (make-proof-in-all-intro-form
       var2
       (mk-proof-in-elim-form
        (make-proof-in-aconst-form
         (all-formula-to-cases-aconst
          (pf "all boole2((T -> boole2) -> ImpConst True boole2)")))
        (make-term-in-var-form var2)
        (mk-proof-in-intro-form
         (formula-to-new-avar (pf "T -> T"))
         (make-proof-in-aconst-form truth-aconst))
        (let ((u (formula-to-new-avar (pf "T -> F"))))
          (mk-proof-in-intro-form
           u (make-proof-in-imp-elim-form
              (make-proof-in-avar-form u)
              (make-proof-in-aconst-form truth-aconst))))))
      (make-proof-in-all-intro-form
       var3
       (mk-proof-in-elim-form
	(make-proof-in-aconst-form
	 (all-formula-to-cases-aconst
	  (pf "all boole2((F -> boole2) -> ImpConst False boole2)")))
	(make-term-in-var-form var3)
	(mk-proof-in-intro-form
	 (formula-to-new-avar (pf "F -> T"))
	 (make-proof-in-aconst-form truth-aconst))
	(mk-proof-in-intro-form
	 (formula-to-new-avar (pf "F -> F"))
	 (make-proof-in-aconst-form truth-aconst))))))))

(define atom-to-imp-proof
  (let ((var1 (pv "boole1"))
        (var2 (pv "boole2")))
    (mk-proof-in-intro-form
     var1
     (mk-proof-in-elim-form
      (make-proof-in-aconst-form
       (all-formula-to-cases-aconst
        (pf "all boole1,boole2(ImpConst boole1 boole2 -> boole1 -> boole2)")))
      (make-term-in-var-form var1)
      (mk-proof-in-intro-form
       var2
       (mk-proof-in-elim-form
        (make-proof-in-aconst-form
         (all-formula-to-cases-aconst
          (pf "all boole2(ImpConst True boole2 -> T -> boole2)")))
        (make-term-in-var-form var2)
        (mk-proof-in-intro-form
         (formula-to-new-avar (pf "T"))
         (formula-to-new-avar (pf "T"))
         (make-proof-in-aconst-form truth-aconst))
        (let ((u (formula-to-new-avar (pf "F"))))
          (mk-proof-in-intro-form
           u (formula-to-new-avar (pf "T"))
           (make-proof-in-avar-form u)))))
      (mk-proof-in-intro-form
       var2
       (mk-proof-in-elim-form
        (make-proof-in-aconst-form
         (all-formula-to-cases-aconst
          (pf "all boole2(ImpConst False boole2 -> F -> boole2)")))
        (make-term-in-var-form var2)
        (mk-proof-in-intro-form
         (formula-to-new-avar (pf "T"))
	 (formula-to-new-avar (pf "F"))
	 (make-proof-in-aconst-form truth-aconst))
	(let ((u (formula-to-new-avar (pf "F"))))
	  (mk-proof-in-intro-form
	   (formula-to-new-avar (pf "T")) u
	   (make-proof-in-avar-form u)))))))))

(define and-atom-to-left-proof
  (mk-proof-in-intro-form
   (pv "boole1")
   (mk-proof-in-elim-form
    (make-proof-in-aconst-form
     (all-formula-to-cases-aconst
      (pf "all boole1,boole2(AndConst boole1 boole2 -> boole1)")))
    (pt "boole1")
    (mk-proof-in-intro-form
     (pv "boole2")
     (formula-to-new-avar (pf "boole2"))
     (make-proof-in-aconst-form truth-aconst))
    (let ((u (formula-to-new-avar (pf "F"))))
      (mk-proof-in-intro-form
       (pv "boole2") u (make-proof-in-avar-form u))))))

(define and-atom-to-right-proof
  (let ((var1 (pv "boole1"))
        (var2 (pv "boole2")))
    (mk-proof-in-intro-form
     var1
     var2
     (mk-proof-in-elim-form
      (make-proof-in-aconst-form
       (all-formula-to-cases-aconst
	(pf "all boole2(AndConst boole1 boole2 -> boole2)")))
      (make-term-in-var-form var1)
      (make-term-in-var-form var2)
      (mk-proof-in-intro-form
       (formula-to-new-avar (pf "AndConst boole1 True"))
       (make-proof-in-aconst-form truth-aconst))
      (mk-proof-in-elim-form
       (make-proof-in-aconst-form
	(all-formula-to-cases-aconst
	 (pf "all boole1(AndConst boole1 False -> F)")))
       (make-term-in-var-form var1)
       (let ((u (formula-to-new-avar (pf "F"))))
	 (mk-proof-in-intro-form u (make-proof-in-avar-form u)))
       (let ((u (formula-to-new-avar (pf "F"))))
	 (mk-proof-in-intro-form u (make-proof-in-avar-form u))))))))

(define atoms-to-and-atom-proof
  (let ((var1 (pv "boole1"))
        (var2 (pv "boole2")))
    (mk-proof-in-intro-form
     var1
     (mk-proof-in-elim-form
      (make-proof-in-aconst-form
       (all-formula-to-cases-aconst
        (pf "all boole1,boole2(boole1 -> boole2 -> AndConst boole1 boole2)")))
      (make-term-in-var-form var1)
      (mk-proof-in-intro-form
       var2
       (mk-proof-in-elim-form
        (make-proof-in-aconst-form
         (all-formula-to-cases-aconst
          (pf "all boole2(T -> boole2 -> AndConst True boole2)")))
        (make-term-in-var-form var2)
        (mk-proof-in-intro-form
         (formula-to-new-avar (pf "T"))
         (mk-proof-in-intro-form
          (formula-to-new-avar (pf "T"))
          (make-proof-in-aconst-form truth-aconst)))
        (let ((u (formula-to-new-avar (pf "F"))))
          (mk-proof-in-intro-form
           (formula-to-new-avar (pf "T"))
           (mk-proof-in-intro-form
            u (make-proof-in-avar-form u))))))
      (mk-proof-in-intro-form
       var2
       (mk-proof-in-elim-form
        (make-proof-in-aconst-form
         (all-formula-to-cases-aconst
          (pf "all boole2(F -> boole2 -> AndConst False boole2)")))
        (make-term-in-var-form var2)
        (let ((u (formula-to-new-avar (pf "F"))))
          (mk-proof-in-intro-form
           u (mk-proof-in-intro-form
              (formula-to-new-avar (pf "T"))
              (make-proof-in-avar-form u))))
        (let ((u (formula-to-new-avar (pf "F"))))
          (mk-proof-in-intro-form
           u (mk-proof-in-intro-form
              (formula-to-new-avar (pf "F"))
              (make-proof-in-avar-form u))))))))))

(define dec-cases-proof
  (let ((var (pv "boole")))
    (mk-proof-in-intro-form
     var
     (mk-proof-in-elim-form
      (make-proof-in-aconst-form
       (all-formula-to-cases-aconst
        (pf "all boole((boole -> (Pvar boole)True) ->
                    ((boole -> F) -> (Pvar boole)False) ->
                    (Pvar boole)boole)")))
      (make-term-in-var-form var)
      (let ((u1 (formula-to-new-avar
                 (pf "T -> (Pvar boole)True") DEFAULT-AVAR-NAME))
            (u2 (formula-to-new-avar
                 (pf "(T -> F) -> (Pvar boole)False")
                 DEFAULT-AVAR-NAME)))
        (mk-proof-in-intro-form
         u1 u2
         (mk-proof-in-elim-form
          (make-proof-in-avar-form u1)
          (make-proof-in-aconst-form truth-aconst))))
      (let ((u1 (formula-to-new-avar
                 (pf "F -> (Pvar boole)True") DEFAULT-AVAR-NAME))
            (u2 (formula-to-new-avar
                 (pf "(F -> F) -> (Pvar boole)False")
                 DEFAULT-AVAR-NAME))
            (u3 (formula-to-new-avar (pf "F") DEFAULT-AVAR-NAME)))
        (mk-proof-in-intro-form
         u1 u2
         (mk-proof-in-elim-form
          (make-proof-in-avar-form u2)
          (make-proof-in-imp-intro-form
           u3 (make-proof-in-avar-form u3)))))))))

;; We initially supply the Cases Lemma If: all boole((boole -> Pvar) ->
;; ((boole -> F) -> Pvar) -> Pvar).  This can be done only here,
;; because for add-theorem we need formula-to-et-type and
;; proof-to-extracted-term .

(define (formula-to-if-proof formula)
  (let* ((var (type-to-new-var (make-alg "boole")))
	 (varterm (make-term-in-var-form var))
	 (varatom (make-atomic-formula varterm))
	 (imp1 (make-imp varatom formula))
	 (imp2 (make-imp (make-imp varatom falsity) formula))
	 (if-kernel (mk-imp imp1 imp2 formula))
	 (all-formula (make-all var if-kernel)))
    (make-proof-in-all-intro-form
     var
     (apply
      mk-proof-in-elim-form
      (append
       (list (make-proof-in-aconst-form
	      (all-formula-to-cases-aconst all-formula)))
       (map make-term-in-var-form (formula-to-free formula))
       (list
	(make-term-in-var-form var)
	(let ((u1 (formula-to-new-avar
		   (make-imp truth formula) DEFAULT-AVAR-NAME))
	      (u2 (formula-to-new-avar
		   (make-imp (make-imp truth falsity) formula)
		   DEFAULT-AVAR-NAME)))
	  (mk-proof-in-intro-form
	   u1 u2
	   (mk-proof-in-elim-form
	    (make-proof-in-avar-form u1)
	    (make-proof-in-aconst-form truth-aconst))))
	(let ((u1 (formula-to-new-avar
		   (make-imp falsity formula) DEFAULT-AVAR-NAME))
	      (u2 (formula-to-new-avar
		   (make-imp (make-imp falsity falsity) formula)
		   DEFAULT-AVAR-NAME))
	      (u3 (formula-to-new-avar falsity DEFAULT-AVAR-NAME)))
	  (mk-proof-in-intro-form
	   u1 u2
	   (mk-proof-in-elim-form
	    (make-proof-in-avar-form u2)
	    (make-proof-in-imp-intro-form
	     u3 (make-proof-in-avar-form u3)))))))))))

(add-theorem "If" (formula-to-if-proof (pf "Pvar")))

;; If: all boole((boole -> Pvar) -> ((boole -> F) -> Pvar) -> Pvar) can
;; be used for case distinctions.  After animation of cIf we have added
;; the computation rule (cIf alpha4) ->
;; [boole0,alpha4_1,alpha4_2][if boole0 alpha4_1 alpha4_2]

;; (animate "If")

;; We need to define eqd-compat-proof in order to put "EqDCompat" into
;; THEOREMS when loading init.  This can be done only here, because for
;; add-theorem we need formula-to-et-type.

(define eqd-compat-proof
  (let* ((tvar (make-tvar -1 DEFAULT-TVAR-NAME))
	 (name (default-var-name tvar))
	 (var1 (make-var tvar 1 0 name))
	 (var2 (make-var tvar 2 0 name))
	 (varterm1 (make-term-in-var-form var1))
	 (varterm2 (make-term-in-var-form var2))
	 (pvar (make-pvar (make-arity tvar) -1 0 0 ""))
	 (eqd-fla (make-eqd varterm1 varterm2))
	 (fla1 (make-predicate-formula pvar varterm1))
	 (fla2 (make-predicate-formula pvar varterm2))
	 (imp-fla (mk-imp eqd-fla fla1 fla2))
	 (aconst (imp-formulas-to-elim-aconst imp-fla))
	 (u (formula-to-new-avar eqd-fla "u"))
	 (u1 (formula-to-new-avar fla1 "u")))
    (mk-proof-in-nc-intro-form
     var1 var2 (make-proof-in-imp-intro-form
		u (mk-proof-in-elim-form
		   (make-proof-in-aconst-form aconst)
		   varterm1 varterm2
		   (make-proof-in-avar-form u)
		   (make-proof-in-allnc-intro-form
		    var1 (make-proof-in-imp-intro-form
			  u1 (make-proof-in-avar-form u1))))))))

(add-theorem "EqDCompat" eqd-compat-proof)

;; ok, EqDCompat has been added as a new theorem.
;; ok, program constant cEqDCompat: alpha5=>alpha5
;; of t-degree 0 and arity 0 added

;; These messages are to be suppressed (as for "Id" "If")

(define eqd-compat-rev-proof
  (let* ((tvar (make-tvar -1 DEFAULT-TVAR-NAME))
	 (name (default-var-name tvar))
	 (var1 (make-var tvar 1 0 name))
	 (var2 (make-var tvar 2 0 name))
	 (varterm1 (make-term-in-var-form var1))
	 (varterm2 (make-term-in-var-form var2))
	 (pvar (make-pvar (make-arity tvar) -1 0 0 ""))
	 (eqd-fla (make-eqd varterm1 varterm2))
	 (fla1 (make-predicate-formula pvar varterm1))
	 (fla2 (make-predicate-formula pvar varterm2))
	 (imp-fla (mk-imp eqd-fla fla2 fla1))
	 (aconst (imp-formulas-to-elim-aconst imp-fla))
	 (u (formula-to-new-avar eqd-fla "u"))
	 (u2 (formula-to-new-avar fla2 "u")))
    (mk-proof-in-nc-intro-form
     var1 var2 (make-proof-in-imp-intro-form
		u (mk-proof-in-elim-form
		   (make-proof-in-aconst-form aconst)
		   varterm1 varterm2
		   (make-proof-in-avar-form u)
		   (make-proof-in-allnc-intro-form
		    var2 (make-proof-in-imp-intro-form
			  u2 (make-proof-in-avar-form u2))))))))

(add-theorem "EqDCompatRev" eqd-compat-rev-proof)

(define efeqd-proof
  (let* ((aconst (theorem-name-to-aconst "EqDCompat"))
	 (uninst-formula (aconst-to-uninst-formula aconst))
	 (tvar (var-to-type (allnc-form-to-var uninst-formula)))
	 (final-conclusion
	  (imp-impnc-all-allnc-form-to-final-conclusion uninst-formula))
	 (pvar (predicate-form-to-predicate final-conclusion))
	 (vars (all-allnc-form-to-vars uninst-formula))
	 (var1 (car vars))
	 (var2 (cadr vars))
	 (varterm1 (make-term-in-var-form var1))
	 (varterm2 (make-term-in-var-form var2))
	 (boolevar (make-var (py "boole") -1 t-deg-zero ""))
	 (boolevarterm (make-term-in-var-form boolevar))
	 (if-term (make-term-in-if-form
		   boolevarterm (list varterm1 varterm2)))
	 (cterm (make-cterm boolevar (make-eqd if-term varterm2)))
	 (tsubst (make-subst tvar (py "boole")))
	 (psubst (make-subst-wrt pvar-cterm-equal? pvar cterm))
	 (inst-aconst (make-aconst (aconst-to-name aconst) ;"EqDCompat"
				   (aconst-to-kind aconst) ;'theorem
				   uninst-formula
				   (append tsubst psubst)))
	 (avar (formula-to-new-avar (make-eqd
				     (make-term-in-const-form false-const)
				     (make-term-in-const-form true-const))))
	 (idpc (make-idpredconst "EqD" (list tvar) '()))
	 (initeqd-aconst (number-and-idpredconst-to-intro-aconst 0 idpc))
	 (initeqd-proof (mk-proof-in-elim-form
			 (make-proof-in-aconst-form initeqd-aconst)
			 varterm2))
	 (elim-proof (mk-proof-in-elim-form
		      (make-proof-in-aconst-form inst-aconst)
		      varterm1 varterm2
		      (make-term-in-const-form false-const)
		      (make-term-in-const-form true-const)
		      (make-proof-in-avar-form avar)
		      initeqd-proof))
	 (elim-proof-with-normalized-formula
	   (list 'proof-in-imp-elim-form
		 (nf (proof-to-formula elim-proof))
		 (proof-in-imp-elim-form-to-op elim-proof)
		 (proof-in-imp-elim-form-to-arg elim-proof))))
    (mk-proof-in-nc-intro-form
     var1 var2 avar elim-proof-with-normalized-formula)))

(add-theorem "EFEqD" efeqd-proof)

;; extotal-elim-aconst and extotal-intro-aconst can be added only here,
;; because they need ExR.

(define extotal-intro-aconst
  (let* ((tvar (make-tvar -1 DEFAULT-TVAR-NAME))
	 (name (default-var-name tvar))
	 (var (make-var tvar -1 1 name))
	 (varpartial (make-var tvar -1 t-deg-zero name))
	 (varterm (make-term-in-var-form var))
	 (varpartialterm (make-term-in-var-form varpartial))
	 (pvar (make-pvar (make-arity tvar) -1 h-deg-zero n-deg-zero ""))
	 (ex-fla (mk-ex var (make-predicate-formula pvar varterm)))
	 (expartial-fla
	  (mk-exr varpartial
		  (mk-and (make-total varpartialterm)
			  (make-predicate-formula pvar varpartialterm))))
	 (formula-of-extotal-intro-aconst (mk-imp expartial-fla ex-fla)))
    (make-aconst "ExTotalIntro"
		 'axiom formula-of-extotal-intro-aconst empty-subst)))

;; (pp (aconst-to-formula extotal-intro-aconst))
;; exr alpha^(Total alpha^ & (Pvar alpha)alpha^) -> ex alpha (Pvar alpha)alpha

(define extotal-elim-aconst
  (let* ((tvar (make-tvar -1 DEFAULT-TVAR-NAME))
	 (name (default-var-name tvar))
	 (var (make-var tvar -1 1 name))
	 (varpartial (make-var tvar -1 t-deg-zero name))
	 (varterm (make-term-in-var-form var))
	 (varpartialterm (make-term-in-var-form varpartial))
	 (pvar (make-pvar (make-arity tvar) -1 h-deg-zero n-deg-zero ""))
	 (ex-fla (mk-ex var (make-predicate-formula pvar varterm)))
	 (expartial-fla
	  (mk-exr varpartial
		  (mk-and (make-total varpartialterm)
			  (make-predicate-formula pvar varpartialterm))))
	 (formula-of-extotal-elim-aconst (mk-imp ex-fla expartial-fla)))
    (make-aconst "ExTotalElim"
		 'axiom formula-of-extotal-elim-aconst empty-subst)))

;; (pp (aconst-to-formula extotal-elim-aconst))
;; ex alpha (Pvar alpha)alpha -> exr alpha^(Total alpha^ & (Pvar alpha)alpha^)

(add-theorem "ExTotalIntro" (make-proof-in-aconst-form extotal-intro-aconst))
(add-theorem "ExTotalElim" (make-proof-in-aconst-form extotal-elim-aconst))

;; ex-expartial-aconst and expartial-ex-aconst can be added only here,
;; because they need ExR.

;; Obsolete (but kept for backwards compatability)
(define ex-expartial-aconst
  (let* ((tvar (make-tvar -1 DEFAULT-TVAR-NAME))
	 (name (default-var-name tvar))
	 (var (make-var tvar -1 1 name))
	 (varpartial (make-var tvar -1 t-deg-zero name))
	 (varterm (make-term-in-var-form var))
	 (varpartialterm (make-term-in-var-form varpartial))
	 (pvar (make-pvar (make-arity tvar) -1 h-deg-zero n-deg-zero ""))
	 (ex-fla (mk-ex var (make-predicate-formula pvar varterm)))
	 (expartial-fla
	  (mk-exr varpartial
		  (mk-and (make-total varpartialterm)
			  (make-predicate-formula pvar varpartialterm))))
	 (formula-of-ex-expartial-aconst (mk-imp ex-fla expartial-fla)))
    (make-aconst "Ex-ExPartial"
		 'axiom formula-of-ex-expartial-aconst empty-subst)))

;; Obsolete (but kept for backwards compatability)
(define expartial-ex-aconst
  (let* ((tvar (make-tvar -1 DEFAULT-TVAR-NAME))
	 (name (default-var-name tvar))
	 (var (make-var tvar -1 1 name))
	 (varpartial (make-var tvar -1 t-deg-zero name))
	 (varterm (make-term-in-var-form var))
	 (varpartialterm (make-term-in-var-form varpartial))
	 (pvar (make-pvar (make-arity tvar) -1 h-deg-zero n-deg-zero ""))
	 (ex-fla (mk-ex var (make-predicate-formula pvar varterm)))
	 (expartial-fla
	  (mk-exr varpartial
		  (mk-and (make-total varpartialterm)
			  (make-predicate-formula pvar varpartialterm))))
	 (formula-of-expartial-ex-aconst (mk-imp expartial-fla ex-fla)))
    (make-aconst "ExPartial-Ex"
		 'axiom formula-of-expartial-ex-aconst empty-subst)))

;; Obsolete (but kept for backwards compatability)
(add-theorem "Ex-ExPartial" (make-proof-in-aconst-form ex-expartial-aconst))
(add-theorem "ExPartial-Ex" (make-proof-in-aconst-form expartial-ex-aconst))

(add-theorem "AtomToEqDTrue"
	     (make-proof-in-aconst-form atom-to-eqd-true-aconst))

(add-theorem "EqDTrueToAtom"
	     (make-proof-in-aconst-form eqd-true-to-atom-aconst))

(define exdtotal-aconst
  (let* ((tvar (make-tvar -1 DEFAULT-TVAR-NAME))
	 (name (default-var-name tvar))
	 (vartotal (make-var tvar -1 t-deg-one name))
	 (var (make-var tvar -1 t-deg-zero name))
	 (vartotalterm (make-term-in-var-form vartotal))
	 (varterm (make-term-in-var-form var))
	 (pvar (make-pvar (make-arity tvar) -1 h-deg-zero n-deg-zero ""))
	 (exdtotal-fla
	  (mk-exd vartotal (make-predicate-formula pvar vartotalterm)))
	 (exr-fla (mk-exr var (mk-andd (make-total varterm)
				       (make-predicate-formula pvar varterm))))
	 (formula-of-exdtotal-aconst (mk-imp exdtotal-fla exr-fla)))
    (make-aconst "ExDTotal" 'axiom formula-of-exdtotal-aconst empty-subst)))

(define exltotal-aconst
  (let* ((tvar (make-tvar -1 DEFAULT-TVAR-NAME))
	 (name (default-var-name tvar))
	 (vartotal (make-var tvar -1 t-deg-one name))
	 (var (make-var tvar -1 t-deg-zero name))
	 (vartotalterm (make-term-in-var-form vartotal))
	 (varterm (make-term-in-var-form var))
	 (pvar (make-pvar (make-arity tvar) -1 h-deg-zero n-deg-zero ""))
	 (exltotal-fla
	  (mk-exl vartotal (make-predicate-formula pvar vartotalterm)))
	 (exr-fla (mk-exr var (mk-andr (make-predicate-formula pvar varterm)
				       (make-total varterm))))
	 (formula-of-exltotal-aconst (mk-imp exltotal-fla exr-fla)))
    (make-aconst "ExLTotal" 'axiom formula-of-exltotal-aconst empty-subst)))

(define exrtotal-aconst
  (let* ((tvar (make-tvar -1 DEFAULT-TVAR-NAME))
	 (name (default-var-name tvar))
	 (vartotal (make-var tvar -1 t-deg-one name))
	 (var (make-var tvar -1 t-deg-zero name))
	 (vartotalterm (make-term-in-var-form vartotal))
	 (varterm (make-term-in-var-form var))
	 (pvar (make-pvar (make-arity tvar) -1 h-deg-zero n-deg-zero ""))
	 (exrtotal-fla
	  (mk-exr vartotal (make-predicate-formula pvar vartotalterm)))
	 (exr-fla (mk-exr var (mk-andr (make-total varterm)
				       (make-predicate-formula pvar varterm))))
	 (formula-of-exrtotal-aconst (mk-imp exrtotal-fla exr-fla)))
    (make-aconst "ExRTotal" 'axiom formula-of-exrtotal-aconst empty-subst)))

(define exutotal-aconst
  (let* ((tvar (make-tvar -1 DEFAULT-TVAR-NAME))
	 (name (default-var-name tvar))
	 (vartotal (make-var tvar -1 t-deg-one name))
	 (var (make-var tvar -1 t-deg-zero name))
	 (vartotalterm (make-term-in-var-form vartotal))
	 (varterm (make-term-in-var-form var))
	 (pvar (make-pvar (make-arity tvar) -1 h-deg-zero n-deg-zero ""))
	 (exutotal-fla
	  (mk-exu vartotal (make-predicate-formula pvar vartotalterm)))
	 (exu-fla (mk-exu var (mk-andu (make-total varterm)
				       (make-predicate-formula pvar varterm))))
	 (formula-of-exutotal-aconst (mk-imp exutotal-fla exu-fla)))
    (make-aconst "ExUTotal" 'axiom formula-of-exutotal-aconst empty-subst)))

;; (pp (aconst-to-formula exdtotal-aconst))
;; (pp (aconst-to-formula exltotal-aconst))
;; (pp (aconst-to-formula exrtotal-aconst))
;; (pp (aconst-to-formula exutotal-aconst))

;; 2012-09-13.  These (and some of the later) axioms can and should be
;; proved.

(define exdtotal-rev-aconst
  (let* ((tvar (make-tvar -1 DEFAULT-TVAR-NAME))
	 (name (default-var-name tvar))
	 (vartotal (make-var tvar -1 t-deg-one name))
	 (var (make-var tvar -1 t-deg-zero name))
	 (vartotalterm (make-term-in-var-form vartotal))
	 (varterm (make-term-in-var-form var))
	 (pvar (make-pvar (make-arity tvar) -1 h-deg-zero n-deg-zero ""))
	 (exdtotal-fla
	  (mk-exd vartotal (make-predicate-formula pvar vartotalterm)))
	 (exr-fla (mk-exr var (mk-andd (make-total varterm)
				       (make-predicate-formula pvar varterm))))
	 (formula-of-exdtotal-rev-aconst (mk-imp exr-fla exdtotal-fla)))
    (make-aconst
     "ExDTotalRev" 'axiom formula-of-exdtotal-rev-aconst empty-subst)))

(define exltotal-rev-aconst
  (let* ((tvar (make-tvar -1 DEFAULT-TVAR-NAME))
	 (name (default-var-name tvar))
	 (vartotal (make-var tvar -1 t-deg-one name))
	 (var (make-var tvar -1 t-deg-zero name))
	 (vartotalterm (make-term-in-var-form vartotal))
	 (varterm (make-term-in-var-form var))
	 (pvar (make-pvar (make-arity tvar) -1 h-deg-zero n-deg-zero ""))
	 (exltotal-fla
	  (mk-exl vartotal (make-predicate-formula pvar vartotalterm)))
	 (exr-fla (mk-exr var (mk-andr (make-predicate-formula pvar varterm)
				       (make-total varterm))))
	 (formula-of-exltotal-rev-aconst (mk-imp exr-fla exltotal-fla)))
    (make-aconst
     "ExLTotalRev" 'axiom formula-of-exltotal-rev-aconst empty-subst)))

(define exrtotal-rev-aconst
  (let* ((tvar (make-tvar -1 DEFAULT-TVAR-NAME))
	 (name (default-var-name tvar))
	 (vartotal (make-var tvar -1 t-deg-one name))
	 (var (make-var tvar -1 t-deg-zero name))
	 (vartotalterm (make-term-in-var-form vartotal))
	 (varterm (make-term-in-var-form var))
	 (pvar (make-pvar (make-arity tvar) -1 h-deg-zero n-deg-zero ""))
	 (exrtotal-fla
	  (mk-exr vartotal (make-predicate-formula pvar vartotalterm)))
	 (exr-fla (mk-exr var (mk-andr (make-total varterm)
				       (make-predicate-formula pvar varterm))))
	 (formula-of-exrtotal-rev-aconst (mk-imp exr-fla exrtotal-fla)))
    (make-aconst
     "ExRTotalRev" 'axiom formula-of-exrtotal-rev-aconst empty-subst)))

(define exutotal-rev-aconst
  (let* ((tvar (make-tvar -1 DEFAULT-TVAR-NAME))
	 (name (default-var-name tvar))
	 (vartotal (make-var tvar -1 t-deg-one name))
	 (var (make-var tvar -1 t-deg-zero name))
	 (vartotalterm (make-term-in-var-form vartotal))
	 (varterm (make-term-in-var-form var))
	 (pvar (make-pvar (make-arity tvar) -1 h-deg-zero n-deg-zero ""))
	 (exutotal-fla
	  (mk-exu vartotal (make-predicate-formula pvar vartotalterm)))
	 (exu-fla (mk-exu var (mk-andu (make-total varterm)
				       (make-predicate-formula pvar varterm))))
	 (formula-of-exutotal-rev-aconst (mk-imp exu-fla exutotal-fla)))
    (make-aconst
     "ExUTotalRev" 'axiom formula-of-exutotal-rev-aconst empty-subst)))

;; (pp (aconst-to-formula exdtotal-rev-aconst))
;; (pp (aconst-to-formula exltotal-rev-aconst))
;; (pp (aconst-to-formula exrtotal-rev-aconst))
;; (pp (aconst-to-formula exutotal-rev-aconst))

(define inhabtotal-aconst
  (let ((formula-of-inhab-total-aconst
	 (make-total (make-term-in-const-form
		      (pconst-name-to-pconst "Inhab")))))
    (make-aconst
     "InhabTotal" 'axiom formula-of-inhab-total-aconst empty-subst)))

(add-theorem "InhabTotal" (make-proof-in-aconst-form inhabtotal-aconst))

(define inhabtotalmr-aconst
  (let* ((inhab-term (make-term-in-const-form (pconst-name-to-pconst "Inhab")))
	 (formula-of-inhab-totalmr-aconst
	  (make-totalmr inhab-term inhab-term)))
    (make-aconst
     "InhabTotalMR" 'axiom formula-of-inhab-totalmr-aconst empty-subst)))

(add-theorem "InhabTotalMR" (make-proof-in-aconst-form inhabtotalmr-aconst))

(define and-const-total-proof
  (let* ((bvar1 (make-var (make-alg "boole") 1 0 ""))
	 (bvar2 (make-var (make-alg "boole") 2 0 ""))
	 (bvarterm1 (make-term-in-var-form bvar1))
	 (bvarterm2 (make-term-in-var-form bvar2))
	 (totalb-idpc (make-idpredconst "TotalBoole" '() '()))
	 (totalb-fla1 (make-predicate-formula totalb-idpc bvarterm1))
	 (totalb-fla2 (make-predicate-formula totalb-idpc bvarterm2))
	 (and-term (mk-term-in-app-form
		    (make-term-in-const-form and-const) bvarterm1 bvarterm2))
	 (totalb-and-fla (make-predicate-formula totalb-idpc and-term))
	 (imp-fla (make-imp totalb-fla1 totalb-and-fla))
	 (aconst (imp-formulas-to-elim-aconst imp-fla))
	 (intro-aconst (number-and-idpredconst-to-intro-aconst 1 totalb-idpc))
	 (u1 (formula-to-new-avar totalb-fla1 "u"))
	 (u2 (formula-to-new-avar totalb-fla2 "u")))
    (make-proof-in-allnc-intro-form
     bvar1 (make-proof-in-imp-intro-form
	    u1 (make-proof-in-allnc-intro-form
		bvar2 (make-proof-in-imp-intro-form
		       u2 (mk-proof-in-elim-form
			   (make-proof-in-aconst-form aconst)
			   bvarterm1 bvarterm2
			   (make-proof-in-avar-form u1)
			   (make-proof-in-avar-form u2)
			   (make-proof-in-aconst-form intro-aconst))))))))

(add-theorem "AndConstTotal" and-const-total-proof)

(define imp-const-total-proof
  (let* ((bvar1 (make-var (make-alg "boole") 1 0 ""))
	 (bvar2 (make-var (make-alg "boole") 2 0 ""))
	 (bvarterm1 (make-term-in-var-form bvar1))
	 (bvarterm2 (make-term-in-var-form bvar2))
	 (totalb-idpc (make-idpredconst "TotalBoole" '() '()))
	 (totalb-fla1 (make-predicate-formula totalb-idpc bvarterm1))
	 (totalb-fla2 (make-predicate-formula totalb-idpc bvarterm2))
	 (imp-term (mk-term-in-app-form
		    (make-term-in-const-form imp-const) bvarterm1 bvarterm2))
	 (totalb-imp-fla (make-predicate-formula totalb-idpc imp-term))
	 (imp-fla (make-imp totalb-fla1 (make-imp totalb-fla2 totalb-imp-fla)))
	 (elim-aconst (imp-formulas-to-elim-aconst imp-fla))
	 (u1 (formula-to-new-avar totalb-fla1 "u"))
	 (u2 (formula-to-new-avar totalb-fla2 "u"))
	 (intro-proof1 (make-proof-in-imp-intro-form
			u2 (make-proof-in-avar-form u2)))
	 (intro-proof2 (make-proof-in-imp-intro-form
			u2 (make-proof-in-aconst-form
			    (number-and-idpredconst-to-intro-aconst
			     0 totalb-idpc))))
	 (elim-proof (mk-proof-in-elim-form
		      (make-proof-in-aconst-form elim-aconst)
		      bvarterm1 bvarterm2
		      (make-proof-in-avar-form u1) intro-proof1 intro-proof2)))
    (mk-proof-in-nc-intro-form
     bvar1 (mk-proof-in-intro-form
	    u1 (mk-proof-in-nc-intro-form
		bvar2 elim-proof)))))

(add-theorem "ImpConstTotal" imp-const-total-proof)

(define or-const-total-proof
  (let* ((bvar1 (make-var (make-alg "boole") 1 0 ""))
	 (bvar2 (make-var (make-alg "boole") 2 0 ""))
	 (bvarterm1 (make-term-in-var-form bvar1))
	 (bvarterm2 (make-term-in-var-form bvar2))
	 (totalb-idpc (make-idpredconst "TotalBoole" '() '()))
	 (totalb-fla1 (make-predicate-formula totalb-idpc bvarterm1))
	 (totalb-fla2 (make-predicate-formula totalb-idpc bvarterm2))
	 (or-term (mk-term-in-app-form
		   (make-term-in-const-form or-const) bvarterm1 bvarterm2))
	 (totalb-or-fla (make-predicate-formula totalb-idpc or-term))
	 (imp-fla (make-imp totalb-fla1 (make-imp totalb-fla2 totalb-or-fla)))
	 (elim-aconst (imp-formulas-to-elim-aconst imp-fla))
	 (u1 (formula-to-new-avar totalb-fla1 "u"))
	 (u2 (formula-to-new-avar totalb-fla2 "u"))
	 (intro-proof1 (make-proof-in-imp-intro-form
			u2 (make-proof-in-aconst-form
			    (number-and-idpredconst-to-intro-aconst
			     0 totalb-idpc))))
	 (intro-proof2 (make-proof-in-imp-intro-form
			u2 (make-proof-in-avar-form u2)))
	 (elim-proof (mk-proof-in-elim-form
		      (make-proof-in-aconst-form elim-aconst)
		      bvarterm1 bvarterm2
		      (make-proof-in-avar-form u1) intro-proof1 intro-proof2)))
    (mk-proof-in-nc-intro-form
     bvar1 (mk-proof-in-intro-form
	    u1 (mk-proof-in-nc-intro-form
		bvar2 elim-proof)))))

(add-theorem "OrConstTotal" or-const-total-proof)

(define neg-const-total-proof
  (let* ((bvar (make-var (make-alg "boole") 1 0 ""))
	 (bvarterm (make-term-in-var-form bvar))
	 (totalb-idpc (make-idpredconst "TotalBoole" '() '()))
	 (totalb-fla (make-predicate-formula totalb-idpc bvarterm))
	 (neg-term (mk-term-in-app-form
		    (make-term-in-const-form neg-const) bvarterm))
	 (totalb-neg-fla (make-predicate-formula totalb-idpc neg-term))
	 (imp-fla (make-imp totalb-fla totalb-neg-fla))
	 (elim-aconst (imp-formulas-to-elim-aconst imp-fla))
	 (u1 (formula-to-new-avar totalb-fla "u"))
	 (elim-proof
	  (mk-proof-in-elim-form
	   (make-proof-in-aconst-form elim-aconst)
	   bvarterm
	   (make-proof-in-avar-form u1)
	   (make-proof-in-aconst-form
	    (number-and-idpredconst-to-intro-aconst 1 totalb-idpc))
	   (make-proof-in-aconst-form
	    (number-and-idpredconst-to-intro-aconst 0 totalb-idpc)))))
    (mk-proof-in-nc-intro-form
     bvar (mk-proof-in-intro-form u1 elim-proof))))

(add-theorem "NegConstTotal" neg-const-total-proof)

(define pair-one-total-proof ;of allnc xy^(TotalYprod xy^ -> Total(lft xy^))
  (let* ((tvar1 (make-tvar 1 DEFAULT-TVAR-NAME))
	 (tvar2 (make-tvar 2 DEFAULT-TVAR-NAME))
	 (alg (make-yprod tvar1 tvar2))
	 (idpc (alg-to-totality-idpredconst alg))
	 (var (make-var alg -1 0 ""))
	 (varterm (make-term-in-var-form var))
	 (prem (make-predicate-formula idpc varterm))
	 (pconst (pconst-name-to-pconst "PairOne"))
	 (pconst-term (make-term-in-const-form pconst))
	 (appterm (make-term-in-app-form pconst-term varterm))
	 (concl (make-total appterm))
	 (imp-formula (make-imp prem concl))
	 (elim-aconst (imp-formulas-to-elim-aconst imp-formula))
	 (var1 (make-var tvar1 1 0 ""))
	 (var2 (make-var tvar2 2 0 ""))
	 (varterm1 (make-term-in-var-form var1))
	 (varterm2 (make-term-in-var-form var2))
	 (u1 (formula-to-new-avar (make-total varterm1)))
	 (u2 (formula-to-new-avar (make-total varterm2)))
	 (clause-proof (mk-proof-in-nc-intro-form
			var1 var2 (mk-proof-in-intro-form
				   u1 u2 (make-proof-in-avar-form u1))))
	 (u (formula-to-new-avar prem))
	 (elim-proof
	  (mk-proof-in-elim-form
	   (make-proof-in-aconst-form elim-aconst)
	   varterm (make-proof-in-avar-form u) clause-proof)))
    (mk-proof-in-nc-intro-form
     var (mk-proof-in-intro-form u elim-proof))))

(add-theorem "PairOneTotal" pair-one-total-proof)

(define pair-two-total-proof ;of allnc xy^(TotalYprod xy^ -> Total(rht xy^))
  (let* ((tvar1 (make-tvar 1 DEFAULT-TVAR-NAME))
	 (tvar2 (make-tvar 2 DEFAULT-TVAR-NAME))
	 (alg (make-yprod tvar1 tvar2))
	 (idpc (alg-to-totality-idpredconst alg))
	 (var (make-var alg -1 0 ""))
	 (varterm (make-term-in-var-form var))
	 (prem (make-predicate-formula idpc varterm))
	 (pconst (pconst-name-to-pconst "PairTwo"))
	 (pconst-term (make-term-in-const-form pconst))
	 (appterm (make-term-in-app-form pconst-term varterm))
	 (concl (make-total appterm))
	 (imp-formula (make-imp prem concl))
	 (elim-aconst (imp-formulas-to-elim-aconst imp-formula))
	 (var1 (make-var tvar1 1 0 ""))
	 (var2 (make-var tvar2 2 0 ""))
	 (varterm1 (make-term-in-var-form var1))
	 (varterm2 (make-term-in-var-form var2))
	 (u1 (formula-to-new-avar (make-total varterm1)))
	 (u2 (formula-to-new-avar (make-total varterm2)))
	 (clause-proof (mk-proof-in-nc-intro-form
			var1 var2 (mk-proof-in-intro-form
				   u1 u2 (make-proof-in-avar-form u2))))
	 (u (formula-to-new-avar prem))
	 (elim-proof
	  (mk-proof-in-elim-form
	   (make-proof-in-aconst-form elim-aconst)
	   varterm (make-proof-in-avar-form u) clause-proof)))
    (mk-proof-in-nc-intro-form
     var (mk-proof-in-intro-form u elim-proof))))

(add-theorem "PairTwoTotal" pair-two-total-proof)

(define boole-if-total-proof
  (let* ((bvar (make-var (make-alg "boole") -1 0 ""))
	 (bvarterm (make-term-in-var-form bvar))
	 (totalb-idpc (make-idpredconst "TotalBoole" '() '()))
	 (totalb-fla (make-predicate-formula totalb-idpc bvarterm))
	 (tvar (make-tvar -1 DEFAULT-TVAR-NAME))
	 (name (default-var-name tvar))
	 (var1 (make-var tvar 1 0 name))
	 (var2 (make-var tvar 2 0 name))
	 (varterm1 (make-term-in-var-form var1))
	 (varterm2 (make-term-in-var-form var2))
	 (total-fla1 (make-total varterm1))
	 (total-fla2 (make-total varterm2))
	 (if-term (make-term-in-if-form bvarterm (list varterm1 varterm2)))
	 (imp-fla (make-imp totalb-fla (make-total if-term)))
	 (aconst (imp-formulas-to-elim-aconst imp-fla))
	 (u (formula-to-new-avar totalb-fla "u"))
	 (u1 (formula-to-new-avar total-fla1 "u"))
	 (u2 (formula-to-new-avar total-fla2 "u")))
    (make-proof-in-allnc-intro-form
     bvar (make-proof-in-imp-intro-form
	   u (mk-proof-in-nc-intro-form
	      var1 var2 (mk-proof-in-intro-form
			 u1 u2 (mk-proof-in-elim-form
				(make-proof-in-aconst-form aconst)
				bvarterm varterm1 varterm2
				(make-proof-in-avar-form u)
				(make-proof-in-avar-form u1)
				(make-proof-in-avar-form u2))))))))

(add-theorem "BooleIfTotal" boole-if-total-proof)

(define boole-eq-total-proof
  (let* ((bvar1 (make-var (make-alg "boole") 1 0 ""))
	 (bvarterm1 (make-term-in-var-form bvar1))
	 (totalb-idpc (make-idpredconst "TotalBoole" '() '()))
	 (totalb-fla1 (make-predicate-formula totalb-idpc bvarterm1))
	 (bvar2 (make-var (make-alg "boole") 2 0 ""))
	 (bvarterm2 (make-term-in-var-form bvar2))
	 (totalb-idpc (make-idpredconst "TotalBoole" '() '()))
	 (totalb-fla2 (make-predicate-formula totalb-idpc bvarterm2))
	 (eq-term (make-=-term bvarterm1 bvarterm2))
	 (totaleq-fla (make-predicate-formula totalb-idpc eq-term))
	 (eq-term-true (make-=-term (make-term-in-const-form true-const)
				    bvarterm2))
	 (totaleq-fla-true (make-predicate-formula totalb-idpc eq-term-true))
	 (eq-term-false (make-=-term (make-term-in-const-form false-const)
				    bvarterm2))
	 (totaleq-fla-false (make-predicate-formula totalb-idpc eq-term-false))
	 (imp-fla (make-imp totalb-fla1
			    (make-allnc
			     bvar2 (make-imp totalb-fla2 totaleq-fla))))
	 (aconst (imp-formulas-to-elim-aconst imp-fla))
	 (imp-fla-true (make-imp totalb-fla2 totaleq-fla-true))
	 (aconst-true (imp-formulas-to-elim-aconst imp-fla-true))
	 (imp-fla-false (make-imp totalb-fla2 totaleq-fla-false))
	 (aconst-false (imp-formulas-to-elim-aconst imp-fla-false))
	 (intro-aconst-true
	  (number-and-idpredconst-to-intro-aconst 0 totalb-idpc))
	 (intro-aconst-false
	  (number-and-idpredconst-to-intro-aconst 1 totalb-idpc))
	 (u1 (formula-to-new-avar totalb-fla1))
	 (u2 (formula-to-new-avar totalb-fla2))
	 (proof-true
	  (make-proof-in-allnc-intro-form
	   bvar2 (make-proof-in-imp-intro-form
		  u2 (mk-proof-in-elim-form
		      (make-proof-in-aconst-form aconst-true)
		      bvarterm2 (make-proof-in-avar-form u2)
		      (make-proof-in-aconst-form intro-aconst-true)
		      (make-proof-in-aconst-form intro-aconst-false)))))
	 (proof-false
	  (make-proof-in-allnc-intro-form
	   bvar2 (make-proof-in-imp-intro-form
		  u2 (mk-proof-in-elim-form
		      (make-proof-in-aconst-form aconst-false)
		      bvarterm2 (make-proof-in-avar-form u2)
		      (make-proof-in-aconst-form intro-aconst-false)
		      (make-proof-in-aconst-form intro-aconst-true))))))
    (make-proof-in-allnc-intro-form
     bvar1 (make-proof-in-imp-intro-form
	    u1 (mk-proof-in-elim-form
		(make-proof-in-aconst-form aconst)
		bvarterm1 (make-proof-in-avar-form u1)
		proof-true proof-false)))))

(add-theorem "BooleEqTotal" boole-eq-total-proof)

(set! COMMENT-FLAG #t)

;; We now aim at giving an internal proof of soundness.

;; make-pvar-to-mr-pvar returns a procedure associating to pvar an
;; mr-pvar with an additional realizer argument.  Usually the type of
;; this argument will be the tvar associated by PVAR-TO-TVAR to pvar.
;; However the idpc-pvar used locally in the stored clauses of an
;; idpredconst needs an mr-pvar where the realizer argument can have a
;; constructor type.  Therefore we have an optional type argument.

(define (make-pvar-to-mr-pvar)
  (let ((assoc-list '()))
    (lambda (pvar . opt-type)
      (let ((info (assoc pvar assoc-list)))
	(if info
	    (cadr info)
	    (let* ((type (if (null? opt-type)
			     (PVAR-TO-TVAR pvar)
			     (car opt-type)))
		   (arity (pvar-to-arity pvar))
		   (types (arity-to-types arity))
		   (newarity (apply make-arity type types))
		   (newpvar (arity-to-new-pvar newarity)))
	      (set! assoc-list (cons (list pvar newpvar) assoc-list))
	      newpvar))))))

(define PVAR-TO-MR-PVAR-ALIST '())

(define (PVAR-TO-MR-PVAR pvar)
  (let ((info (assoc pvar PVAR-TO-MR-PVAR-ALIST)))
    (if info
	(cadr info)
	(let* ((type (PVAR-TO-TVAR pvar))
	       (arity (pvar-to-arity pvar))
	       (types (arity-to-types arity))
	       (newarity (apply make-arity type types))
	       (newpvar (arity-to-new-pvar newarity)))
	      (set! PVAR-TO-MR-PVAR-ALIST
		    (cons (list pvar newpvar) PVAR-TO-MR-PVAR-ALIST))
	      newpvar))))

(define (idpredconst-to-mr-idpredconst idpc)
  (let* ((idpc-name (idpredconst-to-name idpc))
	 (types (idpredconst-to-types idpc))
	 (cterms (idpredconst-to-cterms idpc))
	 (mr-idpc-name (string-append idpc-name "MR"))
	 (tsubst (idpredconst-name-and-types-to-tsubst idpc-name types))
	 (idpc-names (idpredconst-name-to-simidpc-names idpc-name))
	 (clauses (apply append (map idpredconst-name-to-clauses idpc-names)))
	 (clause-et-types (map formula-to-et-type clauses))
	 (clause-et-tvars (apply union (map type-to-tvars clause-et-types)))
	 (param-pvars (idpredconst-name-to-param-pvars idpc-name))
	 (et-tvars-of-param-pvars (map PVAR-TO-TVAR param-pvars))
	 (mr-et-tvars (list-transform-positive clause-et-tvars
			(lambda (tvar) (member tvar et-tvars-of-param-pvars))))
	 (pvar-et-type-list
	  (map (lambda (pvar cterm)
		 (let ((formula (cterm-to-formula cterm)))
		   (list pvar (if (formula-of-nulltype? formula)
				  (make-alg "unit")
				  (formula-to-et-type formula)))))
	       param-pvars cterms))
	 (c-r-pvar-et-type-list
	  (list-transform-positive pvar-et-type-list
	    (lambda (x) (member (PVAR-TO-TVAR (car x)) mr-et-tvars))))
	 (et-tsubst (map (lambda (x)
			   (let ((pvar (car x))
				 (et-type (cadr x)))
			     (list (PVAR-TO-TVAR pvar) et-type)))
			 c-r-pvar-et-type-list))
	 (orig-and-mr-tvars (idpredconst-name-to-tvars mr-idpc-name))
	 (orig-and-mr-types (map (lambda (tvar)
				   (let ((info1 (assoc tvar tsubst))
					 (info2 (assoc tvar et-tsubst)))
				     (cond
				      (info1 (cadr info1))
				      (info2 (cadr info2))
				      (else tvar))))
				 orig-and-mr-tvars))
	 (mr-cterms
	  (map (lambda (pvar cterm)
		 (let ((vars (cterm-to-vars cterm))
		       (formula (cterm-to-formula cterm)))
		   (if ;c.r. param-pvar
		    (member (PVAR-TO-TVAR pvar) mr-et-tvars)
		    (if ;n.c. cterm
		     (formula-of-nulltype? formula)
		     (let* ((mr-formula (real-and-formula-to-mr-formula-aux
					 'eps formula))
			    (mr-var (type-to-new-partial-var (make-alg "unit")))
			    (mr-vars (cons mr-var vars)))
		       (apply make-cterm (append mr-vars (list mr-formula))))
					;else c.r. cterm
		     (let* ((et-type (formula-to-et-type formula))
			    (mr-var (type-to-new-partial-var et-type))
			    (mr-vars (cons mr-var vars))
			    (mr-formula (real-and-formula-to-mr-formula-aux
					 (make-term-in-var-form mr-var)
					 formula)))
		       (apply make-cterm (append mr-vars (list mr-formula)))))
					;else n.c. param-pvar
		    (if ;n.c. cterm
		     (formula-of-nulltype? formula)
		     (let ((mr-formula (real-and-formula-to-mr-formula-aux
					'eps formula)))
		       (apply make-cterm (append vars (list mr-formula))))
					;else c.r. cterm
		     (let* ((et-type (formula-to-et-type formula))
			    (mr-var (type-to-new-partial-var et-type))
			    (mr-formula (real-and-formula-to-mr-formula-aux
					 (make-term-in-var-form mr-var)
					 formula))
			    (exu-mr-formula (make-exu mr-var mr-formula)))
		       (apply make-cterm
			      (append vars (list exu-mr-formula))))))))
	       param-pvars cterms)))
    (make-idpredconst mr-idpc-name orig-and-mr-types mr-cterms)))

(define (real-and-formula-to-mr-formula real formula)
  (let ((type (formula-to-et-type formula)))
    (if (or (and (eq? 'eps real) (nulltype? type))
	    (and (term-form? real) (equal? (term-to-type real) type)))
	(real-and-formula-to-mr-formula-aux real formula)
	(myerror "real-and-formula-to-mr-formula" "equal types expected"
		 (if (term-form? real)
		     (type-to-string (term-to-type real))
		     real)
		 type))))

(define (real-and-formula-to-mr-formula-aux real formula)
  (case (tag formula)
    ((atom) formula)
    ((predicate)
     (let ((pred (predicate-form-to-predicate formula))
	   (args (predicate-form-to-args formula)))
       (cond
	((pvar-form? pred)
	 (if (pvar-with-positive-content? pred)
	     (apply make-predicate-formula (PVAR-TO-MR-PVAR pred) real args)
	     formula))
	((predconst-form? pred)
	 (if (string=? "Total" (predconst-to-name pred))
	     (let* ((arg (car args))
		    (type (term-to-type arg)))
	       (cond ((tvar-form? type) (make-totalmr real arg))
		     ((or (alg-form? type)
			  (arrow-form? type)
			  (star-form? type))
		      (real-and-formula-to-mr-formula-aux
		       real (unfold-formula formula)))
		     (else (myerror
			    "real-and-formula-to-mr-formula-aux"
			    "type of tvar-, alg-, arrow- or star-form expected"
			    type))))
	     formula))
	((idpredconst-form? pred)
	 (let* ((idpc-name (idpredconst-to-name pred))
		(clauses (idpredconst-name-to-clauses idpc-name))
		(opt-alg-name (idpredconst-name-to-opt-alg-name idpc-name)))
	   (cond
	    ((pair? opt-alg-name) ;c.r.idpc
	     (if ;ExL, ExR, ExLT, ExRT, AndL, AndR
	      (string=? "identity" (car opt-alg-name))
	      (cond
	       ((member idpc-name '("ExL" "ExLT"))
		(let* ((var (exl-form-to-var formula))
		       (kernel (exl-form-to-kernel formula))
		       (subst-kernel (formula-subst kernel var real)))
		  (if
		   (formula-of-nulltype? kernel)
		   (real-and-formula-to-mr-formula-aux 'eps subst-kernel)
		   (let* ((realvar (type-to-new-partial-var
				    (formula-to-et-type kernel)))
			  (realterm (make-term-in-var-form realvar)))
		     (make-exu realvar
			       (real-and-formula-to-mr-formula-aux
				realterm subst-kernel))))))
	       ((member idpc-name '("ExR" "ExRT"))
		(let ((var (exl-form-to-var formula))
		      (kernel (exl-form-to-kernel formula)))
		  (make-exu var (real-and-formula-to-mr-formula-aux
				 real kernel))))
	       ((string=? "AndL" idpc-name)
		(let ((left (andl-form-to-left formula))
		      (right (andl-form-to-right formula)))
		  (if
		   (formula-of-nulltype? right)
		   (make-andu (real-and-formula-to-mr-formula-aux real left)
			      (real-and-formula-to-mr-formula-aux 'eps right))
		   (let* ((right-type (formula-to-et-type right))
			  (right-realvar (type-to-new-partial-var right-type))
			  (right-realterm (make-term-in-var-form
					   right-realvar)))
		     (make-andu (real-and-formula-to-mr-formula-aux
				 real left)
				(make-exu
				 right-realvar
				 (real-and-formula-to-mr-formula-aux
				  right-realterm right)))))))
	       ((string=? "AndR" idpc-name)
		(let ((left (andr-form-to-left formula))
		      (right (andr-form-to-right formula)))
		  (if
		   (formula-of-nulltype? left)
		   (make-andu (real-and-formula-to-mr-formula-aux 'eps left)
			      (real-and-formula-to-mr-formula-aux real right))
		   (let* ((left-type (formula-to-et-type left))
			  (left-realvar (type-to-new-partial-var left-type))
			  (left-realterm (make-term-in-var-form left-realvar)))
		     (make-andu (make-exu
				 left-realvar
				 (real-and-formula-to-mr-formula-aux
				  left-realterm left))
				(real-and-formula-to-mr-formula-aux
				 real right))))))
	       (else (myerror "real-and-formula-to-mr-formula-aux"
			      "ExL, ExR, ExLT, ExRT, AndL or AndR expected"
			      idpc-name)))
					;else use mr-idpredconst
	      (apply make-predicate-formula
		     (idpredconst-to-mr-idpredconst pred)
		     real args)))
	    (;non-computational one-clause defined idpc like "EqD" "ExU" "AndU"
	     (and (= 1 (length clauses))
		  (predicate-form?
		   (impnc-form-to-final-conclusion
		    (allnc-form-to-final-kernel (car clauses)))))
	     (let* ;same mr formula with exu x(x mr A) / eps mr A for
					;c.r./n.c. param formulas A
		 ((types (idpredconst-to-types pred))
		  (cterms (idpredconst-to-cterms pred))
		  (formulas (map cterm-to-formula cterms))
		  (et-types (map formula-to-et-type formulas))
		  (vars-and-eps
		   (map (lambda (x) (if (nulltype? x) 'eps
					(type-to-new-partial-var x)))
			et-types))
		  (mr-formulas
		   (map (lambda (x formula)
			  (if (var-form? x)
			      (make-exu
			       x (real-and-formula-to-mr-formula-aux
				  (make-term-in-var-form x)
				  formula))
			      (real-and-formula-to-mr-formula-aux
			       'eps formula)))
			vars-and-eps formulas))
		  (mr-cterms
		   (map (lambda (cterm mr-formula)
			  (apply make-cterm (append (cterm-to-vars cterm)
						    (list mr-formula))))
			cterms mr-formulas))
		  (mr-idpc (make-idpredconst idpc-name types mr-cterms)))
	       (apply make-predicate-formula mr-idpc args)))
	    (else ;witnessing idpc like "EvenMR"
	     formula)))))))
    ((imp)
     (let* ((prem (imp-form-to-premise formula))
	    (type1 (formula-to-et-type prem))
	    (concl (imp-form-to-conclusion formula))
	    (type2 (formula-to-et-type concl)))
       (cond
	((nulltype? type1)
	 (make-impnc (real-and-formula-to-mr-formula-aux 'eps prem)
		     (real-and-formula-to-mr-formula-aux real concl)))
	((nulltype? type2)
	 (let*  ((var (type-to-new-partial-var type1))
		 (varterm (make-term-in-var-form var)))
	   (make-allnc var (make-impnc (real-and-formula-to-mr-formula-aux
					varterm prem)
				       (real-and-formula-to-mr-formula-aux
					'eps concl)))))
	(else ;neither type1 nor type2 equals nulltype
	 (let*  ((var (type-to-new-partial-var type1))
		 (varterm (make-term-in-var-form var))
		 (appterm (make-term-in-app-form real varterm)))
	   (make-allnc var (make-impnc (real-and-formula-to-mr-formula-aux
					varterm prem)
				       (real-and-formula-to-mr-formula-aux
					appterm concl))))))))
    ((impnc)
     (let* ((prem (impnc-form-to-premise formula))
	    (type1 (formula-to-et-type prem))
	    (concl (impnc-form-to-conclusion formula))
	    (type2 (formula-to-et-type concl)))
       (cond
	((nulltype? type1)
	 (make-impnc (real-and-formula-to-mr-formula-aux 'eps prem)
		     (real-and-formula-to-mr-formula-aux real concl)))
	((nulltype? type2)
	 (let*  ((var (type-to-new-partial-var type1))
		 (varterm (make-term-in-var-form var)))
	   (make-allnc var (make-impnc (real-and-formula-to-mr-formula-aux
					varterm prem)
				       (real-and-formula-to-mr-formula-aux
					'eps concl)))))
	(else ;neither type1 nor type2 equals nulltype
	 (let*  ((var (type-to-new-partial-var type1))
		 (varterm (make-term-in-var-form var)))
	   (make-allnc var (make-impnc (real-and-formula-to-mr-formula-aux
					varterm prem)
				       (real-and-formula-to-mr-formula-aux
					real concl))))))))
    ((and)
     (let* ((left (and-form-to-left formula))
	    (type1 (formula-to-et-type left))
	    (right (and-form-to-right formula))
	    (type2 (formula-to-et-type right)))
       (cond
	((and (nulltype? type1) (nulltype? type2))
	 (make-and (real-and-formula-to-mr-formula-aux 'eps left)
		   (real-and-formula-to-mr-formula-aux 'eps right)))
	((nulltype? type1)
	 (make-and (real-and-formula-to-mr-formula-aux 'eps left)
		   (real-and-formula-to-mr-formula-aux real right)))
	((nulltype? type2)
	 (make-and (real-and-formula-to-mr-formula-aux real left)
		   (real-and-formula-to-mr-formula-aux 'eps right)))
	(else ;neither type1 nor type2 equals nulltype
	 (let*  ((term1 (make-term-in-lcomp-form real))
		 (term2 (make-term-in-rcomp-form real)))
	   (make-and (real-and-formula-to-mr-formula-aux term1 left)
		     (real-and-formula-to-mr-formula-aux term2 right)))))))
    ((all)
     (let* ((var (all-form-to-var formula))
	    (kernel (all-form-to-kernel formula))
	    (type (formula-to-et-type kernel)))
       (if (nulltype? type)
	   (make-allnc var (real-and-formula-to-mr-formula-aux 'eps kernel))
	   (let* ((varterm (make-term-in-var-form var))
		  (appterm (make-term-in-app-form real varterm)))
	     (make-allnc var (real-and-formula-to-mr-formula-aux
			      appterm kernel))))))
    ((allnc)
     (let* ((var (allnc-form-to-var formula))
	    (kernel (allnc-form-to-kernel formula))
	    (type (formula-to-et-type kernel)))
       (if (nulltype? type)
	   (make-allnc var (real-and-formula-to-mr-formula-aux 'eps kernel))
	   (make-allnc var (real-and-formula-to-mr-formula-aux real kernel)))))
    ((ex)
     (let* ((var (ex-form-to-var formula))
	    (kernel (ex-form-to-kernel formula))
	    (type (formula-to-et-type kernel)))
       (if (nulltype? type)
	   (real-and-formula-to-mr-formula-aux
	    'eps (formula-subst kernel var real))
	   (let* ((term1 (make-term-in-lcomp-form real))
		  (term2 (make-term-in-rcomp-form real)))
	     (real-and-formula-to-mr-formula-aux
	      term2 (formula-subst kernel var term1))))))
    ((exnc) ;obsolete
     (let* ((var (exnc-form-to-var formula))
	    (kernel (exnc-form-to-kernel formula))
	    (type (formula-to-et-type kernel)))
       (if (nulltype? type)
	   (make-exnc var (real-and-formula-to-mr-formula-aux 'eps kernel))
	   (make-exnc var (real-and-formula-to-mr-formula-aux real kernel)))))
    ((exca excl excu)
     (real-and-formula-to-mr-formula-aux real (unfold-formula formula)))
    (else (myerror "real-and-formula-to-mr-formula-aux" "formula expected"
		   formula))))

(define (all-formulas-to-mr-ind-proof . all-formulas)
  (if (nested-alg-name?
       (alg-form-to-name (var-to-type (all-form-to-var (car all-formulas)))))
      (myerror "all-formulas-to-mr-ind-proof"
	       "all-formula for an unnested algebra expected"
	       (car all-formulas)
	       "unfold all-formula"))
  (let* ((free (apply union (map formula-to-free all-formulas)))
	 (vars (map all-form-to-var all-formulas))
	 (kernels (map all-form-to-kernel all-formulas))
	 (orig-ind-aconst (apply all-formulas-to-ind-aconst all-formulas))
	 (orig-inst-formula (aconst-to-inst-formula orig-ind-aconst))
	 (step-formulas ;D1 ... Dk
	  (imp-form-to-premises (all-form-to-kernel orig-inst-formula)))
	 (real-vars-with-eps ;f1 ... eps ... fk
	  (map (lambda (fla)
		 (let ((et-type (formula-to-et-type fla)))
		   (if (nulltype? et-type)
		       'eps
		       (type-to-new-var et-type))))
	       step-formulas))
	 (real-terms-with-eps
	  (map (lambda (x)
		 (if (var-form? x)
		     (make-term-in-var-form x)
		     x))
	       real-vars-with-eps))
	 (avars ;u1: f1 mr D1 ... ui: eps mr Di ... uk: fk mr Dk
	  (map (lambda (r fla)
		 (formula-to-new-avar
		  (real-and-formula-to-mr-formula-aux r fla)
		  "u"))
	       real-terms-with-eps step-formulas))
	 (real-vars-with-eps-and-avars ;f1 u1 ... eps ui ... fk uk
	  (zip real-vars-with-eps avars))
	 (real-vars-and-avars ;f1 u1 ... ui ... fk uk
	  (list-transform-positive real-vars-with-eps-and-avars
	    (lambda (x) (not (equal? 'eps x)))))
	 (real-vars ;f1 ... fk
	  (list-transform-positive real-vars-and-avars var-form?))
         (real-terms
          (list-transform-positive real-terms-with-eps
	    (lambda (x) (not (equal? 'eps x)))))
	 (arrow-types (map formula-to-et-type all-formulas))
	 (proper-arrow-types
	  (list-transform-positive arrow-types
	    (lambda (x) (not (nulltype? x)))))
	 (rec-consts ;adapted to allnc free
	  (apply arrow-types-to-rec-consts proper-arrow-types))
         (rec-terms (map make-term-in-const-form rec-consts))
	 (alg-names-for-rec
	  (map (lambda (type)
		 (alg-form-to-name (arrow-form-to-arg-type type)))
	       proper-arrow-types))
	 (alg-names-with-rec-terms
	  (map list alg-names-for-rec rec-terms))
	 (fully-applied-rec-consts-or-eps
	  (do ((l1 arrow-types (cdr l1))
	       (l2 vars (cdr l2))
	       (l3 rec-terms
		   (if (nulltype? (car l1))
		       l3
		       (cdr l3)))
	       (res '() (cons (if (nulltype? (car l1))
				  'eps
				  (apply mk-term-in-app-form
					 (car l3)
					 (make-term-in-var-form (car l2))
					 real-terms))
			      res)))
	      ((null? l1) (reverse res))))
	 (mr-all-formulas
	  (map (lambda (var x kernel)
		 (make-all var (real-and-formula-to-mr-formula-aux x kernel)))
	       vars fully-applied-rec-consts-or-eps kernels))
	 (orig-uninst-step-formulas
	  (imp-form-to-premises
           (all-form-to-kernel (aconst-to-uninst-formula orig-ind-aconst))))
	 (component-lengths ;(s1 ... sk) with si=mi+ni
	  (map (lambda (x)
		 (length (car (all-form-to-vars-and-final-kernel x))))
	       orig-uninst-step-formulas))
	 (hyp-lengths ;(n1 ... nk)
	  (map (lambda (x)
		 (length (imp-form-to-premises
			  (cadr (all-form-to-vars-and-final-kernel x)))))
	       orig-uninst-step-formulas))
	 (param-lengths ;(m1 ... mk)
	  (map (lambda (s n) (- s n)) component-lengths hyp-lengths))
	 (mr-ind-aconst (apply all-formulas-to-ind-aconst mr-all-formulas))
	 (mr-inst-formula (aconst-to-inst-formula mr-ind-aconst))
	 (mr-step-formulas ;(D1^mr ... Dk^mr)
	  (imp-form-to-premises (all-form-to-kernel mr-inst-formula)
				(length orig-uninst-step-formulas)))
	 (var (all-form-to-var mr-inst-formula)) ;x_j
	 (var-lists ;((y1 ... ym y_{m+1} ... y_{m+n}) ...)
	  (map (lambda (s x)
		 (if (zero? s) '()
		     (list-head (car (all-form-to-vars-and-final-kernel x))
				s)))
	       component-lengths mr-step-formulas))
	 (prem-lists
	  (map (lambda (s n x)
		 (if (zero? s) '()
		     (list-head (imp-form-to-premises
				 (cadr (all-form-to-vars-and-final-kernel x)))
				n)))
	       component-lengths hyp-lengths mr-step-formulas))
	 (prem-avar-lists ;((v1 ... vn) ...)
	  (map (lambda (prems)
		 (map (lambda (fla) (formula-to-new-avar fla "v")) prems))
	       prem-lists))
	 (y-lists ;((y_{m+1} ... y_{m+n}) ...)
	  (map (lambda (l m) (list-tail l m)) var-lists param-lengths))
	 (prem-vars-lists ;list of lists of vec{x}'s
	  (map (lambda (prems ys)
		 (map (lambda (fla y)
			(list-head
			 (car (all-form-to-vars-and-final-kernel fla))
			 (length (arrow-form-to-arg-types (var-to-type y)))))
		      prems ys))
	       prem-lists y-lists))
	 (applied-y-lists
	  (map (lambda (ys prem-vars-list)
		 (map (lambda (y prem-vars)
			(apply mk-term-in-app-form
			       (map make-term-in-var-form
				    (cons y prem-vars))))
		      ys prem-vars-list))
	       y-lists prem-vars-lists))
	 (mr-step-formula-realizer-lists
	  (map (lambda (applied-y-list)
		 (map (lambda (term)
			(let ((info
			       (assoc (alg-form-to-name (term-to-type term))
				      alg-names-with-rec-terms)))
			  (if info
			      (apply mk-term-in-app-form
				     (cadr info)
				     (cons term real-terms))
			      'eps)))
		      applied-y-list))
	       applied-y-lists))
	 (mr-step-formula-realizer-and-prem-avar-lists
	  (map (lambda (mr-step-formula-realizers prem-avars)
		 (zip mr-step-formula-realizers prem-avars))
	       mr-step-formula-realizer-lists prem-avar-lists))
	 (mr-step-formula-real-term-and-prem-avar-lists
	  (map (lambda (mr-step-formula-realizers-and-prem-avars)
		 (list-transform-positive
		     mr-step-formula-realizers-and-prem-avars
		   (lambda (x) (not (equal? 'eps x)))))
	       mr-step-formula-realizer-and-prem-avar-lists))
	 (mr-step-proofs
	  (map (lambda (u ys l)
		 (let ((vs (list-transform-positive l avar-form?))
		       (varterms-and-avarproofs
			(map (lambda (x)
			       (cond
				((term-form? x) x)
				((avar-form? x) (make-proof-in-avar-form x))
				(else (myerror "term or avar expected" x))))
			     l)))
		   (apply
		    mk-proof-in-intro-form
		    (append
		     ys vs (list (apply mk-proof-in-elim-form
					(make-proof-in-avar-form u)
					(append (map make-term-in-var-form ys)
						varterms-and-avarproofs)))))))
	       avars
	       var-lists
	       mr-step-formula-real-term-and-prem-avar-lists)))
    (apply
     mk-proof-in-nc-intro-form
     (append
      free
      (list
       (apply
	mk-proof-in-intro-form
        var
	(append
	 real-vars-and-avars
	 (list
	  (apply
	   mk-proof-in-elim-form
	   (make-proof-in-aconst-form mr-ind-aconst)
	   (append
	    (map make-term-in-var-form (formula-to-free mr-inst-formula))
	    (cons
	     (make-term-in-var-form var)
	     mr-step-proofs)))))))))))

(define (all-formula-to-mr-cases-proof all-formula)
  (let* ((free (formula-to-free all-formula))
	 (var (all-form-to-var all-formula))
	 (kernel (all-form-to-kernel all-formula))
	 (orig-cases-aconst (all-formula-to-cases-aconst all-formula))
	 (orig-inst-formula (aconst-to-inst-formula orig-cases-aconst))
	 (cases-step-formulas ;Di1 ... Diq
	  (imp-form-to-premises
	   (all-form-to-kernel orig-inst-formula)
	   (length (imp-form-to-premises
		    (all-form-to-kernel
		     (aconst-to-uninst-formula orig-cases-aconst)))))))
    (if
     (formula-of-nulltype? kernel)
     (let* ((mr-all-formula
	     (real-and-formula-to-mr-formula-aux 'eps all-formula))
	    (cases-aconst (all-formula-to-cases-aconst mr-all-formula)))
       (make-proof-in-aconst-form cases-aconst))
     (let* ((real-vars ;f1 ... fq
	     (map (lambda (fla) (type-to-new-var (formula-to-et-type fla)))
		  cases-step-formulas))
	    (real-terms (map make-term-in-var-form real-vars))
	    (avars ;u1: f1 mr Di1 ... uq: fq mr Diq
	     (map (lambda (r fla)
		    (formula-to-new-avar
		     (real-and-formula-to-mr-formula-aux r fla)
		     "u"))
		  real-terms cases-step-formulas))
	    (real-vars-and-avars ;f1 u1 ... fq uq
	     (zip real-vars avars))
	    (if-term (make-term-in-if-form
		      (make-term-in-var-form var) real-terms))
	    (mr-all-formula
	     (make-all var (real-and-formula-to-mr-formula-aux
			    if-term kernel)))
	    (cases-aconst (all-formula-to-cases-aconst mr-all-formula)))
       (apply
	mk-proof-in-nc-intro-form
	(append
	 free
	 (list
	  (apply
	   mk-proof-in-intro-form
           var
	   (append
	    real-vars-and-avars
	    (list
	     (apply
	      mk-proof-in-elim-form
	      (make-proof-in-aconst-form cases-aconst)
	      (append
	       (map make-term-in-var-form (formula-to-free mr-all-formula))
	       (cons (make-term-in-var-form var)
		     (map make-proof-in-avar-form avars))))))))))))))

(define (gind-aconst-to-mr-gind-proof aconst)
  (let* ((uninst-gind-formula (aconst-to-uninst-formula aconst))
         (all-formula (car (aconst-to-repro-data aconst)))
         (free (formula-to-free all-formula))
         (measure-var-and-vars (all-form-to-vars uninst-gind-formula))
         (measure-var (car measure-var-and-vars))
         (vars (cdr measure-var-and-vars))
         (m (length vars))
         (kernel-formula (all-form-to-final-kernel all-formula m)) ;A(xs)
         (kernel-formula-et-type (formula-to-et-type kernel-formula)))
    (if
     (nulltype? kernel-formula-et-type)
     (let* ((mr-all-formula
             (real-and-formula-to-mr-formula-aux 'eps all-formula))
            (gind-aconst
	     (all-formula-and-number-to-gind-aconst mr-all-formula m)))
       (make-proof-in-aconst-form gind-aconst))
     (let* ((inst-formula (aconst-to-inst-formula aconst))
            (prog-formula ;Prog_mu{xs | A(xs)}
             (imp-form-to-premise (all-form-to-final-kernel inst-formula)))
            (prog-formula-et-type (formula-to-et-type prog-formula))
            (real-var (type-to-new-var prog-formula-et-type)) ;G
            (real-term (make-term-in-var-form real-var))
            (prog-avar ;v: G mr Prog_mu{xs | A(xs)}
             (formula-to-new-avar
              (real-and-formula-to-mr-formula-aux real-term prog-formula)
              "v"))
            (types (map term-to-type vars))
            (tpsubst (aconst-to-tpsubst aconst))
            (tsubst (list-transform-positive tpsubst
                      (lambda (x) (tvar-form? (car x)))))
            (type-info (append types (list kernel-formula-et-type)))
	    (grec-const (type-info-to-grec-const type-info))
            (grec-term (make-term-in-const-form grec-const)) ;[[GInd]]
            (grecguard-const (type-info-to-grecguard-const type-info))
	    (grecguard-term (make-term-in-const-form grecguard-const))
            (applied-grec-term
             (apply mk-term-in-app-form
                    grec-term
		    (append (map make-term-in-var-form
				 measure-var-and-vars)
			    (list real-term))))
	    (mr-kernel-formula ;GRec mu xs G mr A(xs)
             (real-and-formula-to-mr-formula-aux
              applied-grec-term kernel-formula))
            (mr-all-formula ;all xs.GRec mu xs G mr A(xs)
             (apply mk-all (append vars (list mr-kernel-formula))))
            (mr-free (formula-to-free mr-all-formula))
            (mr-gind-aconst
             (all-formula-and-number-to-gind-aconst mr-all-formula m))
            (mr-gind-inst-formula
             (aconst-to-inst-formula mr-gind-aconst))
            (mr-measure-var (all-form-to-var mr-gind-inst-formula))
            (mr-prog-formula
             (imp-form-to-premise
              (all-form-to-final-kernel mr-gind-inst-formula)))
            (subst-mr-prog-formula
             (formula-subst mr-prog-formula mr-measure-var
                            (make-term-in-var-form measure-var)))
            (mr-prog-prem-avar ;u:all ys(mu ys < mu xs -> GRec mu ys G mr A(ys))
             (formula-to-new-avar
              (imp-form-to-premise
               (all-form-to-final-kernel subst-mr-prog-formula)) "u"))
            (new-vars (map var-to-new-var vars)) ;ys
            (test-term ;mu ys < mu xs
             (mk-term-in-app-form
	      (if (not (assoc "nat" ALGEBRAS))
		  (myerror "First execute (libload \"nat.scm\")")
		  (pt "NatLt"))
	      (apply mk-term-in-app-form
		     (map make-term-in-var-form
			  (cons measure-var new-vars)))
	      (apply mk-term-in-app-form
		     (map make-term-in-var-form
			  measure-var-and-vars))))
	    (prev-applied-grecguard-term ;GRecGuard mu ys G (mu xs < mu ys)
             (apply mk-term-in-app-form
                    grecguard-term
		    (make-term-in-var-form measure-var)
		    (append (map make-term-in-var-form new-vars)
			    (list real-term test-term))))
	    (test-var (type-to-new-partial-var (py "boole")))
            (prev-applied-grecguard-var-term
             (apply mk-term-in-app-form
                    grecguard-term
		    (make-term-in-var-form measure-var)
		    (append (map make-term-in-var-form new-vars)
			    (list real-term
				  (make-term-in-var-form test-var)))))
            (vars-to-new-vars-subst
             (make-substitution vars (map make-term-in-var-form new-vars)))
            (subst-kernel-formula
             (formula-substitute kernel-formula vars-to-new-vars-subst))
            (cterm (make-cterm test-var
                               (real-and-formula-to-mr-formula-aux
                                prev-applied-grecguard-var-term
                                subst-kernel-formula)))
					;this is a hack ... is there no better
					;way to do this substitution?
            (tsubst-eq-compat-rev-proof
             (proof-subst (make-proof-in-aconst-form eq-compat-rev-aconst)
                          (car (formula-to-tvars
                                (aconst-to-formula eq-compat-rev-aconst)))
                          (py "boole")))
            (tpsubst-eq-compat-rev-proof
             (proof-subst tsubst-eq-compat-rev-proof
                          (car (formula-to-pvars
                                (proof-to-formula tsubst-eq-compat-rev-proof)))
                          cterm))
            (aux-avar (formula-to-new-avar (make-atomic-formula test-term)))
            (aux-proof ;M' : all ys(mu ys < mu xs -> GRecGuard
					;mu ys G (mu ys < mu xs) mr A(ys))
             (apply
              mk-proof-in-intro-form
              (append
               new-vars
               (list
                aux-avar
                (mk-proof-in-elim-form
                 tpsubst-eq-compat-rev-proof test-term (pt "True")
                 (mk-proof-in-elim-form
                  (make-proof-in-aconst-form
                   (finalg-to-=-to-eq-aconst (py "boole")))
                  test-term (pt "True")
                  (mk-proof-in-elim-form
                   (make-proof-in-aconst-form atom-true-aconst)
                   test-term
                   (make-proof-in-avar-form aux-avar)))
                 (apply mk-proof-in-elim-form
                        (make-proof-in-avar-form mr-prog-prem-avar)
			(append (map make-term-in-var-form new-vars)
				(list (make-proof-in-avar-form
				       aux-avar)))))))))
	    (mr-prog-proof ;M : Prog_mu{xs | GRec mu xs G mr A(xs)}
             (apply
              mk-proof-in-intro-form
              (append
               vars
               (list
                mr-prog-prem-avar
                (apply
                 mk-proof-in-elim-form
                 (make-proof-in-avar-form prog-avar)
		 (append
		  (map make-term-in-var-form vars)
		  (list
		   (apply mk-term-in-abst-form
			  (append new-vars
				  (list prev-applied-grecguard-term)))
		   aux-proof))))))))
       (apply
        mk-proof-in-nc-intro-form
        (append
         free
         (list
          (apply
           mk-proof-in-intro-form
           measure-var
	   (append
	    vars
	    (list
	     real-var
	     prog-avar
	     (apply
	      mk-proof-in-elim-form
	      (make-proof-in-aconst-form mr-gind-aconst)
	      (append
	       (map make-term-in-var-form mr-free)
	       (list (make-term-in-var-form measure-var))
	       (map make-term-in-var-form vars)
	       (list mr-prog-proof)))))))))))))

(define (type-to-inhabtotal-mr-proof type)
  (let* ((uninst-formula (aconst-to-uninst-formula inhabtotalmr-aconst))
	 (arg (car (predicate-form-to-args uninst-formula)))
	 (mr-tvar (term-to-type arg)))
    (cond
     ((tvar-form? type)
      (make-proof-in-aconst-form
       (aconst-substitute inhabtotalmr-aconst (make-subst mr-tvar type))))
     ((alg-form? type)
      (let* ((inhab (type-to-canonical-inhabitant type))
	     (inhab-const (term-in-const-form-to-const inhab))
	     (constr-name (const-to-name inhab-const))
	     (alg-name (alg-form-to-name type))
	     (char-list (string->list alg-name))
	     (capitalized-alg-name
	      (list->string
	       (cons (char-upcase (car char-list)) (cdr char-list))))
	     (clause-name
	      (string-append "Total" capitalized-alg-name constr-name "MR"))
	     (info (assoc clause-name THEOREMS)))
	(if info
	    (let ((theorem (cadr info))
		  (tsubst (make-subst mr-tvar type)))
	      (make-proof-in-aconst-form (aconst-substitute theorem tsubst)))
	    (myerror "type-to-inhabtotal-mr-proof"
		     "theorem name expected" clause-name))))
     ((arrow-form? type)
      (let* ((arg-type (arrow-form-to-arg-type type))
	     (val-type (arrow-form-to-val-type type))
	     (var (type-to-new-partial-var arg-type))
	     (real-var (type-to-new-partial-var arg-type))
	     (var-term (make-term-in-var-form var))
	     (real-var-term (make-term-in-var-form real-var))
	     (total-formula (make-total var-term))
	     (mr-prem (real-and-formula-to-mr-formula-aux
		       real-var-term total-formula))
	     (u (formula-to-new-avar mr-prem))
	     (prev (type-to-inhabtotal-mr-proof val-type)))
	(mk-proof-in-nc-intro-form var real-var u prev)))
     ((star-form? type)
      (let* ((left (star-form-to-left-type type))
	     (right (star-form-to-right-type type))
	     (prev-left (type-to-inhabtotal-mr-proof left))
	     (prev-right (type-to-inhabtotal-mr-proof right)))
	(make-proof-in-and-intro-form prev-left prev-right)))
     (else "type-to-inhabtotal-mr-proof"
	   "type of tvar-, alg-, arrow- or star-form expected" type))))

(define (ex-formula-to-ex-intro-mr-proof ex-formula)
  (let* ((free (formula-to-free ex-formula))
	 (var (ex-form-to-var ex-formula))
	 (kernel (ex-form-to-kernel ex-formula))
	 (kernel-type (formula-to-et-type kernel)))
    (if
     (nulltype? kernel-type)
     (let* ((mr-formula (real-and-formula-to-mr-formula-aux 'eps kernel))
	    (avar (formula-to-new-avar mr-formula "u")))
       (apply
	mk-proof-in-nc-intro-form
	(append free (list (mk-proof-in-intro-form
			    var avar (make-proof-in-avar-form avar))))))
     (let* ((real-var (type-to-new-var kernel-type))
	    (real-term (make-term-in-var-form real-var))
	    (mr-formula (real-and-formula-to-mr-formula-aux
			 real-term kernel))
	    (avar (formula-to-new-avar mr-formula "u")))
       (apply
	mk-proof-in-nc-intro-form
	(append free (list (mk-proof-in-intro-form
			    var real-var avar
			    (make-proof-in-avar-form avar)))))))))

(define (ex-formula-and-concl-to-ex-elim-mr-proof ex-formula concl)
  (let* ((free (union (formula-to-free ex-formula) (formula-to-free concl)))
	 (var (ex-form-to-var ex-formula))
	 (type (var-to-type var))
	 (kernel (ex-form-to-kernel ex-formula))
	 (kernel-type (formula-to-et-type kernel))
	 (ex-type (formula-to-et-type ex-formula))
	 (concl-type (formula-to-et-type concl)))
    (if
     (nulltype? kernel-type)
     (let* ((mr-kernel (real-and-formula-to-mr-formula-aux 'eps kernel))
	    (u (formula-to-new-avar mr-kernel "u")))
       (if
	(nulltype? concl-type)
	(let* ((mr-concl (real-and-formula-to-mr-formula-aux 'eps concl))
	       (v (formula-to-new-avar
		   (make-all var (make-imp mr-kernel mr-concl)) "v")))
	  (apply
	   mk-proof-in-nc-intro-form
	   (append free (list (mk-proof-in-intro-form
			       var u v (mk-proof-in-elim-form
					(make-proof-in-avar-form v)
					(make-term-in-var-form var)
					(make-proof-in-avar-form u)))))))
	(let* ((z (type-to-new-var
		   (formula-to-et-type
		    (make-all var (make-imp kernel concl)))))
	       (zx (make-term-in-app-form (make-term-in-var-form z)
					  (make-term-in-var-form var)))
	       (mr-concl (real-and-formula-to-mr-formula-aux zx concl))
	       (v (formula-to-new-avar
		   (make-all var (make-imp mr-kernel mr-concl)) "v")))
	  (apply
	   mk-proof-in-nc-intro-form
	   (append free (list (mk-proof-in-intro-form
			       var u z v
			       (mk-proof-in-elim-form
				(make-proof-in-avar-form v)
				(make-term-in-var-form var)
				(make-proof-in-avar-form u)))))))))
     (let* ((pair-var (type-to-new-var (make-star type kernel-type)))
	    (pair-var-term (make-term-in-var-form pair-var))
	    (left-term (make-term-in-lcomp-form pair-var-term))
	    (right-term (make-term-in-rcomp-form pair-var-term))
	    (mr-kernel (real-and-formula-to-mr-formula-aux
			(make-term-in-rcomp-form pair-var-term)
			(formula-subst
			 kernel var (make-term-in-lcomp-form pair-var-term))))
	    (u (formula-to-new-avar mr-kernel "u"))
	    (g (type-to-new-var (formula-to-et-type
				 kernel)))
	    (g-mr-kernel (real-and-formula-to-mr-formula-aux
			  (make-term-in-var-form g) kernel)))
       (if
	(nulltype? concl-type)
	(let* ((mr-concl (real-and-formula-to-mr-formula-aux 'eps concl))
	       (v (formula-to-new-avar
		   (make-all var (make-imp g-mr-kernel mr-concl)) "v")))
	  (apply
	   mk-proof-in-nc-intro-form
	   (append free (list (mk-proof-in-intro-form
			       pair-var u v
			       (mk-proof-in-elim-form
				(make-proof-in-avar-form v)
				left-term right-term
				(make-proof-in-avar-form u)))))))
	(let* ((z (type-to-new-var
		   (formula-to-et-type
		    (make-all var (make-imp kernel concl)))))
	       (zxg (mk-term-in-app-form (make-term-in-var-form z)
					 (make-term-in-var-form var)
					 (make-term-in-var-form g)))
	       (mr-concl (real-and-formula-to-mr-formula-aux zxg concl))
	       (mr-kernel-with-var-and-g
		(real-and-formula-to-mr-formula-aux
		 (make-term-in-var-form g) kernel))
	       (v (formula-to-new-avar
		   (mk-all var g (make-imp mr-kernel-with-var-and-g
					   mr-concl)) "v")))
	  (apply
	   mk-proof-in-nc-intro-form
	   (append free (list (mk-proof-in-intro-form
			       pair-var u z v
			       (mk-proof-in-elim-form
				(make-proof-in-avar-form v)
				left-term right-term
				(make-proof-in-avar-form u))))))))))))

(define (exnc-formula-to-exnc-intro-mr-proof ;obsolete
	 exnc-formula)
  (let* ((free (formula-to-free exnc-formula))
	 (var (exnc-form-to-var exnc-formula))
	 (kernel (exnc-form-to-kernel exnc-formula))
	 (kernel-type (formula-to-et-type kernel)))
    (if
     (nulltype? kernel-type)
     (let* ((mr-formula (real-and-formula-to-mr-formula-aux
			 'eps exnc-formula))
	    (mr-free (formula-to-free mr-formula))
	    (aconst (exnc-formula-to-exnc-intro-aconst mr-formula)))
       (apply
	mk-proof-in-intro-form
	(append
	 free
	 (list (apply mk-proof-in-elim-form
		      (make-proof-in-aconst-form aconst)
		      (map make-term-in-var-form mr-free))))))
     (let* ((real-var (type-to-new-var kernel-type))
	    (real-term (make-term-in-var-form real-var))
	    (mr-formula (real-and-formula-to-mr-formula-aux
			 real-term exnc-formula))
	    (mr-free (formula-to-free mr-formula))
	    (aconst (exnc-formula-to-exnc-intro-aconst mr-formula)))
       (apply
	mk-proof-in-nc-intro-form
	(append
	 free
	 (list var
	       (make-proof-in-all-intro-form
		real-var
		(apply mk-proof-in-elim-form
		       (make-proof-in-aconst-form aconst)
		       (map make-term-in-var-form
			    (append mr-free (list var))))))))))))

(define (compat-aconst-to-mr-compat-proof aconst)
  (let* ((name (aconst-to-name aconst))
	 (kind (aconst-to-kind aconst))
	 (tpsubst (aconst-to-tpsubst aconst))
	 (tsubst (list-transform-positive tpsubst
		   (lambda (x) (tvar-form? (car x)))))
	 (psubst (list-transform-positive tpsubst
		   (lambda (x) (pvar-form? (car x)))))
	 (uninst-formula (aconst-to-uninst-formula aconst))
	 (var1 (allnc-form-to-var uninst-formula))
	 (kernel1 (allnc-form-to-kernel uninst-formula))
	 (var2 (allnc-form-to-var kernel1))
	 (kernel2 (allnc-form-to-kernel kernel1))
	 (eq-fla (imp-form-to-premise kernel2))
	 (fla1 (imp-form-to-premise (imp-form-to-conclusion kernel2)))
	 (pvar (predicate-form-to-predicate fla1))
	 (cterm (if (pair? psubst)
		    (cadr (car psubst))
		    (make-cterm var1 (make-predicate-formula
				      pvar (make-term-in-var-form var1)))))
	 (fla (cterm-to-formula cterm))
	 (et-type (formula-to-et-type fla)))
    (if
     (nulltype? et-type)
     (let* ((mr-fla (real-and-formula-to-mr-formula-aux 'eps fla))
	    (vars (cterm-to-vars cterm))
	    (var (if (pair? vars)
		     (car vars)
		     (myerror
		      "eq-compat-aconst-to-mr-eq-compat-proof"
		      "var expected in cterm" cterm)))
	    (new-cterm (make-cterm var mr-fla))
	    (new-tpsubst (append tsubst (list (list pvar new-cterm))))
	    (new-aconst (make-aconst name kind uninst-formula new-tpsubst)))
       (make-proof-in-aconst-form new-aconst))
     (let* ((free (cterm-to-free cterm))
	    (y1 (car (cterm-to-vars cterm)))
	    (y2 (var-to-new-var y1))
	    (f (type-to-new-var et-type))
	    (y1-term (make-term-in-var-form y1))
	    (y2-term (make-term-in-var-form y2))
	    (f-term (make-term-in-var-form f))
	    (mr-fla (real-and-formula-to-mr-formula-aux f-term fla))
	    (new-cterm (make-cterm y1 mr-fla))
	    (new-tpsubst (append tsubst (list (list pvar new-cterm))))
	    (new-aconst (make-aconst name kind uninst-formula new-tpsubst))
	    (subst-eq-fla (formula-substitute
			   eq-fla
			   (list (list var1 y1-term) (list var2 y2-term))))
	    (u (formula-to-new-avar subst-eq-fla "u")))
       (apply
	mk-proof-in-nc-intro-form
	(append
	 free
	 (list y1 y2 u
	       (make-proof-in-all-intro-form
		f
		(apply
		 mk-proof-in-elim-form
		 (make-proof-in-aconst-form new-aconst) f-term
		 (append
		  (map make-term-in-var-form free)
		  (list y1-term y2-term (make-proof-in-avar-form u))))))))))))

(define (efq-ga-to-mr-efq-ga-proof aconst)
  (let* ((name (aconst-to-name aconst)) ;EfqLog or Efq
	 (kind (aconst-to-kind aconst)) ;global-assumption
	 (tpsubst (aconst-to-tpsubst aconst))
	 (tsubst (list-transform-positive tpsubst
		  (lambda (x) (tvar-form? (car x))))) ;empty
	 (psubst (list-transform-positive tpsubst
		  (lambda (x) (pvar-form? (car x)))))
	 (uninst-formula (aconst-to-uninst-formula aconst))
	 (fla1 (imp-form-to-conclusion uninst-formula))
	 (pvar (predicate-form-to-predicate fla1))
	 (cterm (if (pair? psubst)
		    (cadr (car psubst))
		    (make-cterm fla1)))
	 (fla (cterm-to-formula cterm))
	 (et-type (formula-to-et-type fla))
	 (real (if (nulltype? et-type)
		   'eps
		   (type-to-canonical-inhabitant et-type)))
	 (mr-fla (real-and-formula-to-mr-formula-aux real fla))
	 (new-cterm (make-cterm mr-fla))
	 (new-tpsubst (append tsubst (list (list pvar new-cterm))))
	 (new-aconst (make-aconst name kind uninst-formula new-tpsubst)))
    (make-proof-in-aconst-form new-aconst)))

(define (number-and-idpredconst-to-intro-mr-proof i idpc)
  (let* ((intro-aconst (number-and-idpredconst-to-intro-aconst i idpc))
	 (constr (proof-to-extracted-term
		  (make-proof-in-aconst-form intro-aconst)))
	 (mr-type (arrow-form-to-final-val-type (term-to-type constr)))
	 (mr-idpc (idpredconst-to-mr-idpredconst idpc))
	 (mr-intro-aconst (number-and-idpredconst-to-intro-aconst i mr-idpc))
	 (inst-clause (aconst-to-inst-formula intro-aconst))
	 (inst-clause-vars (all-allnc-form-to-vars inst-clause))
	 (inst-clause-kernel (all-allnc-form-to-final-kernel inst-clause))
	 (inst-mr-clause (aconst-to-inst-formula mr-intro-aconst))
	 (inst-mr-clause-vars (all-allnc-form-to-vars inst-mr-clause))
	 (inst-mr-clause-kernel
	  (all-allnc-form-to-final-kernel inst-mr-clause))
	 (prems (imp-impnc-form-to-premises inst-clause-kernel))
	 (concl (imp-impnc-form-to-final-conclusion inst-clause-kernel))
	 (idpc-name (idpredconst-to-name idpc))
	 (idpc-pvars (idpredconst-name-to-pvars idpc-name))
	 (idpc-tvars (map PVAR-TO-TVAR idpc-pvars))
	 (idpc-names (idpredconst-name-to-simidpc-names idpc-name))
	 (clauses-with-idpc-pvars
	  (apply append (map idpredconst-name-to-clauses idpc-names)))
	 (et-tvars (set-minus (apply union (map (lambda (x)
						  (type-to-tvars
						   (formula-to-et-type x)))
						clauses-with-idpc-pvars))
			      idpc-tvars))
	 (param-pvars (idpredconst-name-to-param-pvars idpc-name))
	 (et-tvars-of-param-pvars (map PVAR-TO-TVAR param-pvars))
	 (mr-et-tvars (list-transform-positive et-tvars
			(lambda (tvar)
			  (member tvar et-tvars-of-param-pvars))))
	 (et-types ;some may be nulltype
	  (map (lambda (fla)
		 (formula-to-et-type-for-mr-clauses
		  fla mr-et-tvars idpc-pvars PVAR-TO-MR-PVAR))
	       prems))
	 (orig-mr-clause-vars
	  (list-head inst-mr-clause-vars (length inst-clause-vars)))
	 (new-mr-clause-vars
	  (list-tail inst-mr-clause-vars (length inst-clause-vars)))
	 (vars-and-eps (do ((l1 et-types (cdr l1))
			    (l2 new-mr-clause-vars (if (nulltype? (car l1))
						       l2
						       (cdr l2)))
			    (res '() (if (nulltype? (car l1))
					 (cons 'eps res)
					 (cons (car l2) res))))
			   ((null? l1) (reverse res))))
	 (mr-prems (imp-impnc-form-to-premises inst-mr-clause-kernel))
	 (avars (map formula-to-new-avar mr-prems))
	 (vars-with-avars (do ((l1 vars-and-eps (cdr l1))
			       (l2 avars (cdr l2))
			       (res '() (let ((var-or-eps (car l1))
					      (avar (car l2)))
					  (if (eq? var-or-eps 'eps)
					      (cons avar res)
					      (cons avar
						    (cons var-or-eps res))))))
			      ((null? l1) (reverse res))))
	 (free (formula-to-free inst-clause))
	 (mr-free (formula-to-free inst-mr-clause))
	 (elim-proof
	  (apply mk-proof-in-elim-form
		 (make-proof-in-aconst-form mr-intro-aconst)
		 (append (map make-term-in-var-form mr-free)
			 (map make-term-in-var-form inst-mr-clause-vars)
			 (map make-proof-in-avar-form avars)))))
    (apply
     mk-proof-in-nc-intro-form
     (append free orig-mr-clause-vars vars-with-avars (list elim-proof)))))

;; Recall that in inductively defined predicates every clause has the
;; form allnc xs^1 all xs^2 (impnc-param-prems --> imp-param-prems ->
;; rec-prems -> X rs).  Every param-prem has only param-pvars free and
;; they can only occur strictly positive.  Every rec-prem has the form
;; allnc ys^1 all ys^2 (Bs1 --> Bs2 -> X ss) with Bs1 and Bs2 without
;; pvars and X from idpc-pvars.  For simplicity in
;; imp-formulas-to-mr-elim-proof we require that in every recursive
;; premise the list Bs1,Bs2 has at most one element.  This allows usage
;; of proof-to-allnc-impnc-proof to bring t mr clause in clause form.

;; To do: adapt imp-formulas-to-mr-elim-proof to the general form of
;; clauses.  See p. 344 in [SW12].

(define (imp-formulas-to-mr-elim-proof . imp-formulas)
  (let* ((prems (map imp-form-to-premise imp-formulas))
	 (concls (map imp-form-to-conclusion imp-formulas))
	 (prem (car prems))
	 (concl (car concls))
	 (idpc (predicate-form-to-predicate prem))
	 (idpc-param-vars
	  (apply union (map cterm-to-free (idpredconst-to-cterms idpc))))
	 (prem-vars  (formula-to-free prem))
	 (concl-vars (formula-to-free concl))
	 (idpc-arg-vars (set-minus prem-vars idpc-param-vars))
	 (concl-rest-vars (set-minus concl-vars prem-vars))
	 (idpc-name (idpredconst-to-name idpc))
	 (tpsubst (idpredconst-to-tpsubst idpc))
	 (idpc-pvars (idpredconst-name-to-pvars idpc-name))
	 (vars ;w ...
	  (map
	   (lambda (prem)
	     (type-to-new-partial-var
	      (idpredconst-to-et-type (predicate-form-to-predicate prem))))
	   prems))
	 (mr-prems ;w mr I rs
	  (map (lambda (var prem)
		 (let ((idpc (predicate-form-to-predicate prem))
		       (args (predicate-form-to-args prem)))
		   (apply make-predicate-formula
			  (idpredconst-to-mr-idpredconst idpc)
			  (make-term-in-var-form var) args)))
	       vars prems))
	 (orig-elim-aconst (apply imp-formulas-to-elim-aconst imp-formulas))
	 (orig-uninst-formula (aconst-to-uninst-formula orig-elim-aconst))
	 (orig-uninst-clauses ;(K0 ... K{k-1})
	  (imp-form-to-premises (imp-form-to-conclusion orig-uninst-formula)))
	 (k (length orig-uninst-clauses))
	 (orig-inst-formula (aconst-to-inst-formula orig-elim-aconst))
	 (orig-inst-clauses ;Ki for i<k
	  (imp-form-to-premises (imp-form-to-conclusion orig-inst-formula) k))
	 (real-vars-with-eps ;w0 ... eps ... w{k-1}
	  (map (lambda (fla)
		 (let ((et-type (formula-to-et-type fla)))
		   (if (nulltype? et-type)
		       'eps
		       (type-to-new-partial-var et-type))))
	       orig-inst-clauses))
	 (real-terms-with-eps
	  (map (lambda (x)
		 (if (var-form? x)
		     (make-term-in-var-form x)
		     x))
	       real-vars-with-eps))
	 (avars ;u0: w0 mr K0 ... ui: eps mr Ki ... u{k-1}: w{k-1} mr K{k-1}
	  (map (lambda (r fla)
		 (formula-to-new-avar
		  (real-and-formula-to-mr-formula-aux r fla)
		  "u"))
	       real-terms-with-eps orig-inst-clauses))
	 (real-vars-with-eps-and-avars ;w0 u0 ... eps ui ... w{k-1} u{k-1}
	  (zip real-vars-with-eps avars))
	 (real-vars-and-avars ;w0 u0 ... ui ... w{k-1} u{k-1}
	  (list-transform-positive real-vars-with-eps-and-avars
	    (lambda (x) (not (equal? 'eps x)))))
	 (real-terms
          (list-transform-positive real-terms-with-eps
	    (lambda (x) (not (equal? 'eps x)))))
	 (arrow-type-or-nulltype-list (map formula-to-et-type imp-formulas))
	 (arrow-types
	  (list-transform-positive arrow-type-or-nulltype-list arrow-form?))
	 (rec-const-or-eps-list
	  (map (lambda (type) (if (arrow-form? type)
				  (apply arrow-types-to-rec-const arrow-types)
				  'eps))
	       arrow-type-or-nulltype-list))
	 (fully-applied-rec-const-or-eps-list
	  (map (lambda (type var rec-const-or-eps)
		 (if (arrow-form? type)
		     (apply mk-term-in-app-form
			    (make-term-in-const-form rec-const-or-eps)
			    (make-term-in-var-form var)
			    real-terms)
		     'eps))
	       arrow-type-or-nulltype-list vars rec-const-or-eps-list))
	 (mr-imp-formulas
	  (map (lambda (mr-prem x concl)
		 (make-imp mr-prem (real-and-formula-to-mr-formula-aux
				    x concl)))
	       mr-prems fully-applied-rec-const-or-eps-list concls))
	 (mr-elim-aconst (apply imp-formulas-to-elim-aconst mr-imp-formulas))
	 (mr-imp-formula (car mr-imp-formulas))
	 (mr-prem (imp-form-to-premise mr-imp-formula))
	 (mr-idpc (predicate-form-to-predicate mr-prem))
	 (mr-idpc-param-vars
	  (apply union (map cterm-to-free (idpredconst-to-cterms mr-idpc))))
	 (mr-concl (imp-form-to-conclusion mr-imp-formula))
	 (mr-prem-vars (formula-to-free mr-prem))
	 (mr-concl-vars (formula-to-free mr-concl))
	 (mr-concl-rest-vars (set-minus mr-concl-vars mr-prem-vars))
	 (mr-prem-avar (formula-to-new-avar mr-prem)) ;of w mr I xs
	 (avar-proofs-in-clause-form ;of w0 mr K0 ..., in clause form (7.15)
	  (map (lambda (avar orig-uninst-clause)
		 (real-mr-clause-proof-and-clause-to-clause-proof
		  (make-proof-in-avar-form avar) orig-uninst-clause))
	       avars orig-uninst-clauses))
	 (mr-clauses (map proof-to-formula avar-proofs-in-clause-form))
	 (rec-prems-list
	  (map (lambda (idpc-clause)
		 (idpc-clause-to-rec-premises idpc-clause idpc-pvars))
	       orig-uninst-clauses))
	 (ns (map length rec-prems-list))
	 (vars-list (map all-allnc-form-to-vars mr-clauses))
	 (xs-and-us-list
	   (map (lambda (vars n)
		  (list-head vars (- (length vars)
				     (if
				      (eq? 'eps (car rec-const-or-eps-list))
				      n
				      (* 2 n)))))
		vars-list ns))
	 (fs-and-gs-list
	   (map (lambda (vars n)
		  (list-tail vars (- (length vars)
				     (if
				      (eq? 'eps (car rec-const-or-eps-list))
				      n
				      (* 2 n)))))
		vars-list ns))
	 (fs-list (map (lambda (fs-and-gs n) (list-head fs-and-gs n))
		       fs-and-gs-list ns))
	 (abstr-mr-clause-realizer-lists
	  (map (lambda (fs)
		 (if
		  (eq? 'eps (car rec-const-or-eps-list))
		  '()
		  (map (lambda (f)
			 (let* ((type (var-to-type f))
				(arg-types (arrow-form-to-arg-types type))
				(arg-vars
				 (map type-to-new-partial-var arg-types))
				(fully-applied-f-term
				 (apply mk-term-in-app-form
					(make-term-in-var-form f)
					(map make-term-in-var-form arg-vars))))
			   (apply
			    mk-term-in-abst-form
			    (append arg-vars
				    (list (apply mk-term-in-app-form
						 (make-term-in-const-form
						  (car rec-const-or-eps-list))
						 fully-applied-f-term
						 real-terms))))))
		       fs)))
	       fs-list))
	 (clause-et-types (map formula-to-et-type orig-uninst-clauses))
	 (clause-et-tvars (apply union (map type-to-tvars clause-et-types)))
	 (param-pvars (idpredconst-name-to-param-pvars idpc-name))
	 (et-tvars-of-param-pvars (map PVAR-TO-TVAR param-pvars))
	 (mr-et-tvars (list-transform-positive clause-et-tvars
			(lambda (tvar) (member tvar et-tvars-of-param-pvars))))
	 (mr-clause-proofs
	  (map
	   (lambda (avar-proof
		    orig-uninst-clause
		    orig-inst-clause
		    xs-and-us fs gs)
	     (let* ((clause-vars (all-allnc-form-to-vars orig-inst-clause)) ;ys
		    (xs (list-head xs-and-us (length clause-vars)))
		    (us (list-tail xs-and-us (length clause-vars)))
		    (orig-uninst-clause-kernel
		     (all-allnc-form-to-final-kernel orig-uninst-clause))
		    (orig-uninst-clause-prems
		     (imp-impnc-form-to-premises orig-uninst-clause-kernel))
		    (applied-avar-proof
		     (apply mk-proof-in-elim-form
			    avar-proof
			    (append
			     (map make-term-in-var-form xs-and-us)
			     (map make-term-in-var-form fs)
			     gs)))
		    (abstr-applied-avar-proof
		     (apply mk-proof-in-nc-intro-form
			    (append us fs (list applied-avar-proof))))
		    (renamed-mr-clause
		     (proof-to-formula abstr-applied-avar-proof))
		    (prems-in-renamed-mr-clause
		     (list-head
		      (imp-impnc-form-to-premises
		       (allnc-form-to-final-kernel renamed-mr-clause))
		      (length orig-uninst-clause-prems)))
		    (labelled-prems
		     (map
		      (lambda (orig-uninst-clause-prem prem)
			(if ;prem has c.r. substituted param-pvar
					;with hidden tvar
			 (apply
			  or-op
			  (map (lambda (pvar)
				 (and ;pvar with hidden tvar
				  (not (member (PVAR-TO-TVAR pvar)
					       mr-et-tvars))
					;c.r. substituted pvar
				  (let ((info (assoc pvar tpsubst)))
				    (or (not info)
					(not (formula-of-nulltype?
					      (cterm-to-formula
					       (cadr info))))))))
			       (intersection
				(formula-to-pvars orig-uninst-clause-prem)
				param-pvars)))
			 (list #t prem)
			 (list #f prem)))
		      orig-uninst-clause-prems
		      prems-in-renamed-mr-clause))
		    (init-labelled-prems ;up to last (tt prem)
		     (list-and-test-to-head-up-to-last
		      labelled-prems
		      (lambda (labelled-prem) (car labelled-prem)))))
	       (if ;no prem has c.r. substituted param-pvar with hidden tvar
		(null? init-labelled-prems)
		(apply mk-proof-in-nc-intro-form
		       (append xs (list abstr-applied-avar-proof)))
		(let*
		    ((full-opt-var-and-prem-list
		      (do ((l init-labelled-prems (cdr l))
			   (vars us (if (caar l) (cdr vars) vars))
			   (res '() (if (caar l)
					(cons (cadar l) (cons (car vars) res))
					(cons (cadar l) res))))
			  ((null? l) (reverse res))))
		     (l (length full-opt-var-and-prem-list)) ;l>=2
		     (prem1 (list-ref full-opt-var-and-prem-list (- l 1)))
		     (var1 (list-ref full-opt-var-and-prem-list (- l 2)))
		     (opt-var-and-prem-list
		      (list-head full-opt-var-and-prem-list (- l 2)))
		     (rest-of-mr-clause
		      (impnc-form-to-final-conclusion
		       (allnc-form-to-final-kernel renamed-mr-clause)
		       (length init-labelled-prems)))
		     (exu-imp-proof
		      (allnc-impnc-to-exu-imp-proof
		       opt-var-and-prem-list var1 prem1 clause-vars
		       rest-of-mr-clause))
		     (proof-of-modified-mr-clause
		      (mk-proof-in-elim-form
		       exu-imp-proof abstr-applied-avar-proof)))
		  (apply mk-proof-in-nc-intro-form
			 (append xs (list proof-of-modified-mr-clause)))))))
	   avar-proofs-in-clause-form
	   orig-uninst-clauses
	   orig-inst-clauses
	   xs-and-us-list
	   fs-list
	   abstr-mr-clause-realizer-lists)))
    (apply mk-proof-in-nc-intro-form
	   (append
	    (union prem-vars concl-vars)
	    (list (car vars) mr-prem-avar) ;w avar:w mr I xs
	    real-vars-and-avars
	    (list (apply
		   mk-proof-in-elim-form
		   (make-proof-in-aconst-form mr-elim-aconst)
		   (append
		    (map make-term-in-var-form idpc-arg-vars) ;xs
		    (map make-term-in-var-form mr-idpc-param-vars)
		    (map make-term-in-var-form mr-concl-rest-vars)
		    (cons (make-term-in-var-form (car vars)) ;w
			  (cons (make-proof-in-avar-form mr-prem-avar)
				mr-clause-proofs)))))))))

;; In proof-to-allnc-impnc-proof we assume that we have a proof of
;; allnc xs1(As1 --> allnc xs2(As2 --> ... allnc xsn(As n --> B)...))
;; with xs2 not free in As1, ..., xsn not free in As1,...,As{n-1}.  We
;; prove allnc xs1,xs2,...,xsn(As1 --> As2 --> ... As n --> B).

(define (proof-to-allnc-impnc-proof proof)
  (letrec ((formula-to-var-avar-list
	    (lambda (formula)
	      (case (tag formula)
		((imp impnc)
		 (let* ((prem (imp-impnc-form-to-premise formula))
			(conc (imp-impnc-form-to-conclusion formula))
			(avar (formula-to-new-avar prem)))
		   (cons avar (formula-to-var-avar-list conc))))
		((all allnc)
		 (let ((var (all-allnc-form-to-var formula))
		       (kernel (all-allnc-form-to-kernel formula)))
		   (cons var (formula-to-var-avar-list kernel))))
		(else '())))))
    (let* ((var-avar-list (formula-to-var-avar-list (proof-to-formula proof)))
	   (varterm-avarproof-list
	    (map (lambda (x)
		   (if (var-form? x)
		       (make-term-in-var-form x)
		       (make-proof-in-avar-form x)))
		 var-avar-list))
	   (elim-proof
	    (apply mk-proof-in-elim-form
		   proof
		   varterm-avarproof-list))
	   (var-list (list-transform-positive var-avar-list var-form?))
	   (avar-list (list-transform-positive var-avar-list avar-form?)))
      (apply mk-proof-in-nc-intro-form
	     (append var-list avar-list (list elim-proof))))))

;; In real-mr-clause-proof-and-clause-to-clause-proof we assume that we
;; have a proof of (real mr clause) =: mr-formula.  The result is a
;; proof of the clause form of mr-formula.  We need the original
;; uninst-clause to determine how deep we need to go into mr-formula.

(define (real-mr-clause-proof-and-clause-to-clause-proof proof uninst-clause)
  (letrec
      ((formula-and-depth-to-var-avar-list
	(lambda (formula n)
	  (if
	   (zero? n) '()
	   (case (tag formula)
	     ((imp impnc)
	      (let* ((prem (imp-impnc-form-to-premise formula))
		     (conc (imp-impnc-form-to-conclusion formula))
		     (avar (formula-to-new-avar prem)))
		(cons avar (formula-and-depth-to-var-avar-list
			    conc (- n 1)))))
	     ((all allnc)
	      (let ((var (all-allnc-form-to-var formula))
		    (kernel (all-allnc-form-to-kernel formula)))
		(cons var (formula-and-depth-to-var-avar-list
			   kernel n))))
	     (else '()))))))
    (let* ((n (length (imp-impnc-form-to-premises
		       (all-allnc-form-to-final-kernel uninst-clause))))
	   (var-avar-list (formula-and-depth-to-var-avar-list
			   (proof-to-formula proof) n))
	   (varterm-avarproof-list
	    (map (lambda (x)
		   (if (var-form? x)
		       (make-term-in-var-form x)
		       (make-proof-in-avar-form x)))
		 var-avar-list))
	   (elim-proof
	    (apply mk-proof-in-elim-form
		   proof
		   varterm-avarproof-list))
	   (var-list (list-transform-positive var-avar-list var-form?))
	   (avar-list (list-transform-positive var-avar-list avar-form?)))
      (apply mk-proof-in-nc-intro-form
	     (append var-list avar-list (list elim-proof))))))

(define (allnc-impnc-to-exu-imp-proof
	 opt-var-and-prem-list var1 prem1 vars concl)
  (if (member var1 (formula-to-free concl))
      (myerror "allnc-impnc-to-exu-imp-proof" "unexpected free variable" var1
	       "in conclusion" concl))
  (if
   (null? opt-var-and-prem-list)
   (let* ((exu-formula (make-exu var1 prem1))
	  (imp-formula (make-imp exu-formula concl))
	  (exu-elim-aconst (imp-formulas-to-elim-aconst imp-formula))
	  (u-formula
	   (apply mk-allnc var1 (append vars (list (make-impnc prem1 concl)))))
	  (u (formula-to-new-avar u-formula))
	  (v (formula-to-new-avar exu-formula)))
     (mk-proof-in-intro-form
      u (apply
	 mk-proof-in-nc-intro-form
	 (append
	  vars (list (mk-proof-in-nc-intro-form
		      v (apply
			 mk-proof-in-elim-form
			 (make-proof-in-aconst-form exu-elim-aconst)
			 (append
			  (map make-term-in-var-form
			       (formula-to-free
				(aconst-to-inst-formula exu-elim-aconst)))
			  (list
			   (make-proof-in-avar-form v)
			   (mk-proof-in-nc-intro-form
			    var1 (apply mk-proof-in-elim-form
					(make-proof-in-avar-form u)
					(make-term-in-var-form var1)
					(map make-term-in-var-form
					     vars))))))))))))
   (let ((var-or-prem (car opt-var-and-prem-list)))
     (if
      (var-form? var-or-prem)
      (let* ((x var-or-prem)
	     (prem (if (null? (cdr opt-var-and-prem-list))
		       (myerror "allnc-impnc-to-exu-imp-proof"
				"list var - prem - rest expected"
				opt-var-and-prem-list)
		       (cadr opt-var-and-prem-list)))
	     (rest (cddr opt-var-and-prem-list))
	     (prev (allnc-impnc-to-exu-imp-proof rest var1 prem1 vars concl))
	     (exu-formula (make-exu x prem))
	     (prev-concl (imp-form-to-conclusion (proof-to-formula prev)))
	     (prev-concl-kernel (allnc-form-to-final-kernel prev-concl))
	     (imp-formula (make-imp exu-formula prev-concl-kernel))
	     (exu-elim-aconst (imp-formulas-to-elim-aconst imp-formula))
	     (prev-prem (imp-form-to-premise (proof-to-formula prev)))
	     (xs-and-vars (allnc-form-to-vars prev-prem))
	     (prev-prem-kernel (allnc-form-to-final-kernel prev-prem))
	     (u-formula (apply
			 mk-allnc
			 x (append xs-and-vars
				   (list (make-impnc prem prev-prem-kernel)))))
	     (v-formula (make-exu x prem))
	     (u (formula-to-new-avar u-formula))
	     (v (formula-to-new-avar v-formula))
	     (w (formula-to-new-avar prem)))
	(mk-proof-in-intro-form
	 u (apply
	    mk-proof-in-nc-intro-form
	    (append
	     vars
	     (list
	      v (mk-proof-in-elim-form
		 (make-proof-in-aconst-form exu-elim-aconst)
		 (make-proof-in-avar-form v)
		 (mk-proof-in-nc-intro-form
		  x w (apply
		       mk-proof-in-elim-form
		       prev
		       (apply
			mk-proof-in-nc-intro-form
			(append
			 xs-and-vars
			 (list (apply mk-proof-in-elim-form
				      (make-proof-in-avar-form u)
				      (make-term-in-var-form x)
				      (append
				       (map make-term-in-var-form
					    xs-and-vars)
				       (list (make-proof-in-avar-form w)))))))
		       (map make-term-in-var-form vars)))))))))
					;else no exu-elim needed
      (let* ((rest (cdr opt-var-and-prem-list))
	     (prev (allnc-impnc-to-exu-imp-proof rest var1 prem1 vars concl))
	     (prev-prem (imp-form-to-premise (proof-to-formula prev)))
	     (xs-and-vars (allnc-form-to-vars prev-prem))
	     (prev-prem-kernel (allnc-form-to-final-kernel prev-prem))
	     (impnc-formula (make-impnc var-or-prem prev-prem-kernel))
	     (u (formula-to-new-avar
		 (apply mk-allnc (append xs-and-vars (list impnc-formula)))))
	     (v (formula-to-new-avar var-or-prem)))
	(mk-proof-in-intro-form
	 u (apply
	    mk-proof-in-nc-intro-form
	    (append
	     vars (list v (apply
			   mk-proof-in-elim-form
			   prev
			   (apply
			    mk-proof-in-nc-intro-form
			    (append
			     xs-and-vars
			     (list (apply mk-proof-in-elim-form
					  (make-proof-in-avar-form u)
					  (append
					   (map make-term-in-var-form
						xs-and-vars)
					   (list (make-proof-in-avar-form
						  v)))))))
			   (map make-term-in-var-form vars)))))))))))

(define (exl-formula-to-exl-intro-mr-proof exl-formula)
  (let* ((free (formula-to-free exl-formula))
	 (var (exl-form-to-var exl-formula))
	 (kernel (exl-form-to-kernel exl-formula))
	 (kernel-type (formula-to-et-type kernel)))
    (if
     (nulltype? kernel-type)
     (let* ((mr-formula ;x mr exl x A, which is the same as eps mr A
	     (real-and-formula-to-mr-formula-aux 'eps kernel))
	    (avar (formula-to-new-avar mr-formula)))
       (apply
	mk-proof-in-nc-intro-form
	(append free (list var avar (make-proof-in-avar-form avar)))))
     (let* ((real-var (type-to-new-partial-var kernel-type))
	    (real-term (make-term-in-var-form real-var))
	    (mr-formula (real-and-formula-to-mr-formula-aux real-term kernel))
	    (exu-formula (make-exu real-var mr-formula))
	    (idpc (predicate-form-to-predicate exu-formula))
	    (aconst (number-and-idpredconst-to-intro-aconst 0 idpc))
	    (inst-formula (aconst-to-inst-formula aconst))
	    (inst-formula-free (formula-to-free inst-formula)))
       (if (equal? inst-formula-free (append free (list var)))
	   (make-proof-in-aconst-form aconst)
	   (apply
	    mk-proof-in-nc-intro-form
	    (append free (list var (apply mk-proof-in-elim-form
					  (make-proof-in-aconst-form aconst)
					  (map make-term-in-var-form
					       inst-formula-free))))))))))

(define (exr-formula-to-exr-intro-mr-proof exr-formula)
  (let* ((free (formula-to-free exr-formula))
	 (var (exr-form-to-var exr-formula))
	 (kernel (exr-form-to-kernel exr-formula))
	 (kernel-type (formula-to-et-type kernel)))
    (if
     (nulltype? kernel-type)
     (let* ((mr-formula ;eps mr A
	     (real-and-formula-to-mr-formula-aux 'eps kernel))
	    (exu-formula (make-exu var mr-formula))
	    (idpc (predicate-form-to-predicate exu-formula))
	    (aconst (number-and-idpredconst-to-intro-aconst 0 idpc)))
       (make-proof-in-aconst-form aconst))
     (let* ((real-var (type-to-new-partial-var kernel-type)) ;a
	    (real-term (make-term-in-var-form real-var))
	    (mr-formula ;a mr A
	     (real-and-formula-to-mr-formula-aux real-term kernel))
	    (exu-formula (make-exu var mr-formula))
	    (idpc (predicate-form-to-predicate exu-formula))
	    (aconst (number-and-idpredconst-to-intro-aconst 0 idpc))
	    (exu-formula-free (formula-to-free exu-formula))
	    (elim-proof (apply mk-proof-in-elim-form
			       (make-proof-in-aconst-form aconst)
			       (append
				(map make-term-in-var-form exu-formula-free)
				(list (make-term-in-var-form var))))))
       (apply mk-proof-in-nc-intro-form
	      (append free (list var real-var elim-proof)))))))

(define (exu-formula-to-exu-intro-mr-proof exu-formula)
  (let* ((free (formula-to-free exu-formula))
	 (var (exu-form-to-var exu-formula))
	 (kernel (exu-form-to-kernel exu-formula))
	 (kernel-type (formula-to-et-type kernel)))
    (if
     (nulltype? kernel-type)
     (let* ((mr-formula ;eps mr A
	     (real-and-formula-to-mr-formula-aux 'eps kernel))
	    (exu-formula (make-exu var mr-formula))
	    (idpc (predicate-form-to-predicate exu-formula))
	    (aconst (number-and-idpredconst-to-intro-aconst 0 idpc))
	    (inst-formula (aconst-to-inst-formula aconst))
	    (inst-formula-free (formula-to-free inst-formula)))
       (if (equal? inst-formula-free (append free (list var)))
	   (make-proof-in-aconst-form aconst)
	   (apply
	    mk-proof-in-nc-intro-form
	    (append free (list var (apply mk-proof-in-elim-form
					  (make-proof-in-aconst-form aconst)
					  (map make-term-in-var-form
					       inst-formula-free)))))))
     (let* ((real-var (type-to-new-partial-var kernel-type)) ;a
	    (real-term (make-term-in-var-form real-var))
	    (mr-formula ;a mr A
	     (real-and-formula-to-mr-formula-aux real-term kernel))
	    (exu-formula1 (make-exu real-var mr-formula))
	    (u (formula-to-new-avar mr-formula))
	    (free1 (formula-to-free exu-formula1))
	    (idpc1 (predicate-form-to-predicate exu-formula1))
	    (aconst1 (number-and-idpredconst-to-intro-aconst 0 idpc1))
	    (elim-proof1 ;of exu a a mr A from u:a mr A
	     (apply mk-proof-in-elim-form
		    (make-proof-in-aconst-form aconst1)
		    (append (map make-term-in-var-form free1)
			    (list (make-term-in-var-form real-var)
				  (make-proof-in-avar-form u)))))
	    (exu-formula2 (make-exu var exu-formula1))
	    (free2 (formula-to-free exu-formula2))
	    (idpc2 (predicate-form-to-predicate exu-formula2))
	    (aconst2 (number-and-idpredconst-to-intro-aconst 0 idpc2))
	    (elim-proof2 ;of exu x,a a mr A from u:a mr A
	     (apply mk-proof-in-elim-form
		    (make-proof-in-aconst-form aconst2)
		    (append (map make-term-in-var-form free2)
			    (list (make-term-in-var-form var)
				  elim-proof1)))))
       (apply
	mk-proof-in-nc-intro-form
	(append free (list var real-var u elim-proof2)))))))

(define (andr-formula-to-andr-intro-mr-proof andr-formula)
  (let* ((free (formula-to-free andr-formula))
	 (left (andr-form-to-left andr-formula))
	 (right (andr-form-to-right andr-formula))
	 (left-type (formula-to-et-type left))
	 (right-type (formula-to-et-type right))
	 (right-realvar (type-to-new-partial-var right-type)) ;b
	 (right-realterm (make-term-in-var-form right-realvar))
	 (mr-right-formula ;b mr B
	  (real-and-formula-to-mr-formula-aux right-realterm right)))
    (if
     (nulltype? left-type)
     (let* ((mr-left-formula ;eps mr A
	     (real-and-formula-to-mr-formula-aux 'eps left))
	    (andu-formula ;eps mr A andu b mr B
	     (make-andu mr-left-formula mr-right-formula))
	    (mr-free (formula-to-free andu-formula))
	    (idpc (predicate-form-to-predicate andu-formula))
	    (andu-aconst (number-and-idpredconst-to-intro-aconst 0 idpc))
	    (mr-left-avar (formula-to-new-avar mr-left-formula)))
       (apply
	mk-proof-in-nc-intro-form
	(append
	 free (list mr-left-avar right-realvar
		    (apply
		     mk-proof-in-elim-form
		     (make-proof-in-aconst-form andu-aconst)
		     (append (map make-term-in-var-form mr-free)
			     (list (make-proof-in-avar-form
				    mr-left-avar))))))))
     (let* ((left-realvar (type-to-new-partial-var left-type)) ;a
	    (left-realterm (make-term-in-var-form left-realvar))
	    (mr-left-formula ;a mr A
	     (real-and-formula-to-mr-formula-aux left-realterm left))
	    (mr-left-free (formula-to-free mr-left-formula))
	    (exu-formula ;exu a a mr A
	     (make-exu left-realvar mr-left-formula))
	    (exu-idpc (predicate-form-to-predicate exu-formula))
	    (exu-aconst (number-and-idpredconst-to-intro-aconst 0 exu-idpc))
	    (mr-left-avar (formula-to-new-avar mr-left-formula))
	    (andu-formula ;exu a a mr A andu b mr B
	     (make-andu exu-formula mr-right-formula))
	    (mr-free (formula-to-free andu-formula))
	    (andu-idpc (predicate-form-to-predicate andu-formula))
	    (andu-aconst (number-and-idpredconst-to-intro-aconst 0 andu-idpc))
	    (mr-left-avar (formula-to-new-avar mr-left-formula))
	    (exu-proof ;of exu a a mr A
	     (apply mk-proof-in-elim-form
		    (make-proof-in-aconst-form exu-aconst)
		    (append (map make-term-in-var-form mr-left-free)
			    (list (make-proof-in-avar-form mr-left-avar))))))
       (apply
	mk-proof-in-nc-intro-form
	(append
	 free (list left-realvar mr-left-avar right-realvar
		    (apply
		     mk-proof-in-elim-form
		     (make-proof-in-aconst-form andu-aconst)
		     (append (map make-term-in-var-form mr-free)
			     (list exu-proof))))))))))

(define (andl-formula-to-andl-intro-mr-proof andl-formula)
  (let* ((free (formula-to-free andl-formula))
	 (left (andl-form-to-left andl-formula))
	 (right (andl-form-to-right andl-formula))
	 (left-type (formula-to-et-type left))
	 (right-type (formula-to-et-type right))
	 (left-realvar (type-to-new-partial-var left-type)) ;a
	 (left-realterm (make-term-in-var-form left-realvar))
	 (mr-left-formula ;a mr A
	  (real-and-formula-to-mr-formula-aux left-realterm left)))
    (if
     (nulltype? right-type)
     (let* ((mr-right-formula ;eps mr B
	     (real-and-formula-to-mr-formula-aux 'eps right))
	    (andu-formula ;a mr A andu eps mr B
	     (make-andu mr-left-formula mr-right-formula))
	    (mr-free (formula-to-free andu-formula))
	    (idpc (predicate-form-to-predicate andu-formula))
	    (andu-aconst (number-and-idpredconst-to-intro-aconst 0 idpc))
	    (mr-right-avar (formula-to-new-avar mr-right-formula)))
       (apply
	mk-proof-in-nc-intro-form
	(append
	 free (list left-realvar mr-right-avar
		    (apply
		     mk-proof-in-elim-form
		     (make-proof-in-aconst-form andu-aconst)
		     (append (map make-term-in-var-form mr-free)
			     (list (make-proof-in-avar-form
				    mr-right-avar)))))))) ;check
     (let* ((right-realvar (type-to-new-partial-var right-type)) ;a
	    (right-realterm (make-term-in-var-form right-realvar))
	    (mr-right-formula ;b mr B
	     (real-and-formula-to-mr-formula-aux right-realterm right))
	    (mr-right-free (formula-to-free mr-right-formula))
	    (exu-formula ;exu b b mr B
	     (make-exu right-realvar mr-right-formula))
	    (exu-idpc (predicate-form-to-predicate exu-formula))
	    (exu-aconst (number-and-idpredconst-to-intro-aconst 0 exu-idpc))
	    (mr-right-avar (formula-to-new-avar mr-right-formula))
	    (andu-formula ;a mr A andu exu b b mr B
	     (make-andu mr-left-formula exu-formula))
	    (mr-free (formula-to-free andu-formula))
	    (andu-idpc (predicate-form-to-predicate andu-formula))
	    (andu-aconst (number-and-idpredconst-to-intro-aconst 0 andu-idpc))
	    (mr-right-avar (formula-to-new-avar mr-right-formula))
	    (exu-proof ;of exu b b mr B
	     (apply mk-proof-in-elim-form
		    (make-proof-in-aconst-form exu-aconst)
		    (append (map make-term-in-var-form mr-right-free)
			    (list (make-proof-in-avar-form mr-right-avar))))))
       (apply
	mk-proof-in-nc-intro-form
	(append
	 free (list left-realvar right-realvar mr-right-avar
		    (apply
		     mk-proof-in-elim-form
		     (make-proof-in-aconst-form andu-aconst)
		     (append (map make-term-in-var-form mr-free)
			     (list exu-proof))))))))))

(define (exl-formula-and-concl-to-exl-elim-mr-proof exl-formula concl)
  (let* ((free (union (formula-to-free exl-formula) (formula-to-free concl)))
	 (var (exl-form-to-var exl-formula))
	 (var-term (make-term-in-var-form var))
	 (type (var-to-type var))
	 (kernel (exl-form-to-kernel exl-formula))
	 (kernel-type (formula-to-et-type kernel))
	 (concl-type (formula-to-et-type concl))
	 (f-or-eps (if (nulltype? concl-type) 'eps
		       (type-to-new-partial-var (make-arrow type concl-type))))
	 (f-term-or-eps (if (nulltype? concl-type) 'eps
			    (make-term-in-var-form f-or-eps)))
	 (v-formula ;f mr all x(A --> P)
	  (real-and-formula-to-mr-formula-aux
	   f-term-or-eps (make-all var (make-impnc kernel concl))))
	 (v (formula-to-new-avar v-formula "v")))
    (if
     (nulltype? kernel-type)
     (let* ((mr-kernel ;x mr exl x A, which is the same as eps mr A
	     (real-and-formula-to-mr-formula-aux 'eps kernel))
	    (u (formula-to-new-avar mr-kernel "u"))
	    (elim-proof (mk-proof-in-elim-form
			 (make-proof-in-avar-form v)
			 var-term (make-proof-in-avar-form u))))
       (apply mk-proof-in-nc-intro-form
	      (append free (if (nulltype? concl-type)
			       (list var u v elim-proof)
			       (list var u f-or-eps v elim-proof)))))
     (let* ((real-var ;a
	     (type-to-new-partial-var kernel-type))
	    (real-term (make-term-in-var-form real-var))
	    (mr-kernel ;x mr exl x A, which is exu a a mr A
	     (real-and-formula-to-mr-formula-aux var-term exl-formula))
	    (u (formula-to-new-avar mr-kernel "u"))
	    (mr-concl ;fx mr P
	     (real-and-formula-to-mr-formula-aux
	      (if (nulltype? concl-type) 'eps
		  (make-term-in-app-form f-term-or-eps var-term))
	      concl))
	    (imp-formula (make-imp mr-kernel mr-concl))
	    (aconst (imp-formulas-to-elim-aconst imp-formula))
	    (aconst-free (formula-to-free imp-formula))
	    (elim-proof ;of fx mr P
	     (apply mk-proof-in-elim-form
		    (make-proof-in-aconst-form aconst)
		    (append (map make-term-in-var-form aconst-free)
			    (list (make-proof-in-avar-form u)
				  (mk-proof-in-elim-form
				   (make-proof-in-avar-form v) var-term))))))
       (apply mk-proof-in-nc-intro-form
	      (append free (if (nulltype? concl-type)
			       (list var u v elim-proof)
			       (list var u f-or-eps v elim-proof))))))))

(define (exr-formula-and-concl-to-exr-elim-mr-proof exr-formula concl)
  (let* ((free (union (formula-to-free exr-formula) (formula-to-free concl)))
	 (var (exr-form-to-var exr-formula))
	 (var-term (make-term-in-var-form var))
	 (type (var-to-type var))
	 (kernel (exr-form-to-kernel exr-formula))
	 (kernel-type (formula-to-et-type kernel))
	 (concl-type (formula-to-et-type concl)))
    (if
     (nulltype? kernel-type)
     (let* ((mr-kernel ;eps mr exr x A, which is the same as exu x eps mr A
	     (real-and-formula-to-mr-formula-aux 'eps exr-formula))
	    (u (formula-to-new-avar mr-kernel "u"))
	    (b-or-eps (if (nulltype? concl-type) 'eps
			  (type-to-new-partial-var concl-type)))
	    (b-term-or-eps (if (nulltype? concl-type) 'eps
			       (make-term-in-var-form b-or-eps)))
	    (v-formula ;b mr allnc x(A -> P)
	     (real-and-formula-to-mr-formula-aux
	      b-term-or-eps (make-allnc var (make-imp kernel concl))))
	    (v (formula-to-new-avar v-formula "v"))
	    (mr-concl ;b mr P
	     (real-and-formula-to-mr-formula-aux b-term-or-eps concl))
	    (imp-formula (make-imp mr-kernel mr-concl))
	    (aconst (imp-formulas-to-elim-aconst imp-formula))
	    (aconst-free (formula-to-free imp-formula))
	    (elim-proof ;of b mr P
	     (apply mk-proof-in-elim-form
		    (make-proof-in-aconst-form aconst)
		    (append (map make-term-in-var-form aconst-free)
			    (list (make-proof-in-avar-form u)
				  (make-proof-in-avar-form v))))))
       (apply mk-proof-in-nc-intro-form
	      (append free (if (nulltype? concl-type)
			       (list u v elim-proof)
			       (list u b-or-eps v elim-proof)))))
     (let* ((real-var ;a
	     (type-to-new-partial-var kernel-type))
	    (real-term (make-term-in-var-form real-var))
	    (mr-kernel ;a mr exr x A, which is exu x a mr A
	     (real-and-formula-to-mr-formula-aux real-term exr-formula))
	    (u (formula-to-new-avar mr-kernel "u"))
	    (f-or-eps (if (nulltype? concl-type) 'eps
			  (type-to-new-partial-var
			   (make-arrow kernel-type concl-type))))
	    (f-term-or-eps (if (nulltype? concl-type) 'eps
			       (make-term-in-var-form f-or-eps)))
	    (v-formula ;f mr allnc x(A -> P)
	     (real-and-formula-to-mr-formula-aux
	      f-term-or-eps (make-allnc var (make-imp kernel concl))))
	    (v (formula-to-new-avar v-formula "v"))
	    (mr-concl ;fa mr P
	     (real-and-formula-to-mr-formula-aux
	      (if (nulltype? concl-type) 'eps
		  (make-term-in-app-form f-term-or-eps real-term))
	      concl))
	    (imp-formula (make-imp mr-kernel mr-concl))
	    (aconst (imp-formulas-to-elim-aconst imp-formula))
	    (aconst-free (formula-to-free imp-formula))
	    (elim-proof ;of fa mr P
	     (apply mk-proof-in-elim-form
		    (make-proof-in-aconst-form aconst)
		    (append (map make-term-in-var-form aconst-free)
			    (list (make-proof-in-avar-form u)
				  (mk-proof-in-nc-intro-form
				   var (mk-proof-in-elim-form
					(make-proof-in-avar-form v)
					var-term real-term)))))))
       (apply mk-proof-in-nc-intro-form
	      (append free (if (nulltype? concl-type)
			       (list u v elim-proof)
			       (list real-var u f-or-eps v elim-proof))))))))

(define (andr-formula-and-concl-to-andr-elim-mr-proof andr-formula concl)
  (let* ((free (union (formula-to-free andr-formula) (formula-to-free concl)))
	 (left (andr-form-to-left andr-formula))
	 (left-type (formula-to-et-type left))
	 (right (andr-form-to-right andr-formula))
	 (right-type (formula-to-et-type right))
	 (concl-type (formula-to-et-type concl)))
    (cond
     ((and (nulltype? left-type) (nulltype? right-type))
      (let* ((mr-andr ;eps mr (A andr B), which is eps mr A andu eps mr B
	      (real-and-formula-to-mr-formula-aux 'eps andr-formula))
	     (u (formula-to-new-avar mr-andr "u"))
	     (c-or-eps (if (nulltype? concl-type) 'eps
			   (type-to-new-partial-var concl-type)))
	     (c-term-or-eps (if (nulltype? concl-type) 'eps
				(make-term-in-var-form c-or-eps)))
	     (v-formula ;eps mr A --> eps mr B --> c mr P, i.e.,
					;f mr (A --> B -> P)
	      (real-and-formula-to-mr-formula-aux
	       c-term-or-eps (make-impnc left (make-imp right concl))))
	     (v (formula-to-new-avar v-formula "v"))
	     (mr-concl ;c mr P
	      (real-and-formula-to-mr-formula-aux c-term-or-eps concl))
	     (andu-imp-formula (make-imp mr-andr mr-concl))
	     (andu-elim-aconst (imp-formulas-to-elim-aconst andu-imp-formula))
	     (andu-elim-aconst-free (formula-to-free andu-imp-formula))
	     (andu-elim-proof ;of c mr P
	      (apply mk-proof-in-elim-form
		     (make-proof-in-aconst-form andu-elim-aconst)
		     (append (map make-term-in-var-form andu-elim-aconst-free)
			     (list (make-proof-in-avar-form u)
				   (make-proof-in-avar-form v))))))
	(apply mk-proof-in-nc-intro-form
	       (append free (if (nulltype? concl-type)
				(list u v andu-elim-proof)
				(list u c-or-eps v andu-elim-proof))))))
     ((and (nulltype? left-type) (not (nulltype? right-type)))
      (let* ((b (type-to-new-partial-var right-type))
	     (b-term (make-term-in-var-form b))
	     (mr-andr ;b mr (A andr B), which is eps mr A andu b mr B
	      (real-and-formula-to-mr-formula-aux b-term andr-formula))
	     (u (formula-to-new-avar mr-andr "u"))
	     (f-or-eps (if (nulltype? concl-type) 'eps
			   (type-to-new-partial-var
			    (make-arrow right-type concl-type))))
	     (f-term-or-eps (if (nulltype? concl-type) 'eps
				(make-term-in-var-form f-or-eps)))
	     (v-formula ;eps mr A --> allnc b(b mr B --> fb mr P), i.e.,
					;f mr (A --> B -> P)
	      (real-and-formula-to-mr-formula-aux
	       f-term-or-eps (make-impnc left (make-imp right concl))))
	     (v (formula-to-new-avar v-formula "v"))
	     (mr-concl ;fb mr P
	      (real-and-formula-to-mr-formula-aux
	       (if (nulltype? concl-type) 'eps
		   (make-term-in-app-form f-term-or-eps b-term))
	       concl))
	     (u1 (formula-to-new-avar (andu-form-to-left mr-andr))) ;eps mr A
	     (v-elim-proof ;of b mr B --> fb mr P
	      (mk-proof-in-elim-form (make-proof-in-avar-form v)
				     (make-proof-in-avar-form u1)
				     (make-term-in-var-form b)))
	     (v-intro-proof ;of eps mr A --> b mr B --> fb mr P
	      (mk-proof-in-nc-intro-form u1 v-elim-proof))
	     (andu-imp-formula (make-imp mr-andr mr-concl))
	     (andu-elim-aconst (imp-formulas-to-elim-aconst andu-imp-formula))
	     (andu-elim-aconst-free (formula-to-free andu-imp-formula))
	     (andu-elim-proof ;of fb mr P
	      (apply mk-proof-in-elim-form
		     (make-proof-in-aconst-form andu-elim-aconst)
		     (append (map make-term-in-var-form andu-elim-aconst-free)
			     (list (make-proof-in-avar-form u)
				   v-intro-proof)))))
	(apply mk-proof-in-nc-intro-form
	       (append free (if (nulltype? concl-type)
				(list b u v andu-elim-proof)
				(list b u f-or-eps v andu-elim-proof))))))
     ((and (not (nulltype? left-type)) (nulltype? right-type))
      (let* ((a (type-to-new-partial-var left-type))
	     (a-term (make-term-in-var-form a))
	     (mr-andr ;eps mr (A andr B), which is exu a a mr A andu eps mr B
	      (real-and-formula-to-mr-formula-aux 'eps andr-formula))
	     (u (formula-to-new-avar mr-andr "u"))
	     (c-or-eps (if (nulltype? concl-type) 'eps
			   (type-to-new-partial-var concl-type)))
	     (c-term-or-eps (if (nulltype? concl-type) 'eps
				(make-term-in-var-form c-or-eps)))
	     (v-formula ;allnc a(a mr A --> eps mr B --> c mr P)), i.e.,
					;c mr (A --> B -> P)
	      (real-and-formula-to-mr-formula-aux
	       c-term-or-eps (make-impnc left (make-imp right concl))))
	     (v (formula-to-new-avar v-formula "v"))
	     (mr-concl ;c mr P
	      (real-and-formula-to-mr-formula-aux c-term-or-eps concl))
	     (exu-imp-formula ;exu a a mr A -> eps mr B --> c mr P)
	      (make-imp
	       (andu-form-to-left mr-andr)
	       (make-impnc (andu-form-to-right mr-andr) mr-concl)))
	     (exu-elim-aconst (imp-formulas-to-elim-aconst exu-imp-formula))
	     (exu-elim-aconst-free (formula-to-free exu-imp-formula))
	     (u1 ;exu a a mr A
	      (formula-to-new-avar (andu-form-to-left mr-andr)))
	     (u2 (formula-to-new-avar (andu-form-to-right mr-andr))) ;eps mr B
	     (exu-elim-proof ;of b mr B --> c mr P
	      (apply mk-proof-in-elim-form
		     (make-proof-in-aconst-form exu-elim-aconst)
		     (append (map make-term-in-var-form exu-elim-aconst-free)
			     (list (make-proof-in-avar-form u1)
				   (make-proof-in-avar-form v)))))
	     (exu-intro-proof ;of exu a a mr A --> eps mr B --> c mr P
	      (mk-proof-in-nc-intro-form u1 exu-elim-proof))
	     (andu-imp-formula (make-imp mr-andr mr-concl))
	     (andu-elim-aconst (imp-formulas-to-elim-aconst andu-imp-formula))
	     (andu-elim-aconst-free (formula-to-free andu-imp-formula))
	     (andu-elim-proof ;of c mr P
	      (apply mk-proof-in-elim-form
		     (make-proof-in-aconst-form andu-elim-aconst)
		     (append (map make-term-in-var-form andu-elim-aconst-free)
			     (list (make-proof-in-avar-form u)
				   exu-intro-proof)))))
	(apply mk-proof-in-nc-intro-form
	       (append free (if (nulltype? concl-type)
				(list u v andu-elim-proof)
				(list u c-or-eps v andu-elim-proof))))))
     ((and (not (nulltype? left-type)) (not (nulltype? right-type)))
      (let* ((a (type-to-new-partial-var left-type))
	     (a-term (make-term-in-var-form a))
	     (b (type-to-new-partial-var right-type))
	     (b-term (make-term-in-var-form b))
	     (mr-andr ;b mr (A andr B), which is exu a a mr A andu b mr B
	      (real-and-formula-to-mr-formula-aux b-term andr-formula))
	     (u (formula-to-new-avar mr-andr "u"))
	     (f-or-eps (if (nulltype? concl-type) 'eps
			   (type-to-new-partial-var
			    (make-arrow right-type concl-type))))
	     (f-term-or-eps (if (nulltype? concl-type) 'eps
				(make-term-in-var-form f-or-eps)))
	     (v-formula ;allnc a(a mr A --> allnc b(b mr B --> fb mr P)), i.e.,
					;f mr (A --> B -> P)
	      (real-and-formula-to-mr-formula-aux
	       f-term-or-eps (make-impnc left (make-imp right concl))))
	     (v (formula-to-new-avar v-formula "v"))
	     (mr-concl ;fb mr P
	      (real-and-formula-to-mr-formula-aux
	       (if (nulltype? concl-type) 'eps
		   (make-term-in-app-form f-term-or-eps b-term))
	       concl))
	     (exu-imp-formula ;exu a a mr A -> allnc b(b mr B --> fb mr P)
	      (make-imp
	       (andu-form-to-left mr-andr)
	       (make-allnc
		b (make-impnc (andu-form-to-right mr-andr) mr-concl))))
	     (exu-elim-aconst (imp-formulas-to-elim-aconst exu-imp-formula))
	     (exu-elim-aconst-free (formula-to-free exu-imp-formula))
	     (u1 ;exu a a mr A
	      (formula-to-new-avar (andu-form-to-left mr-andr)))
	     (exu-elim-proof ;of b mr B --> fb mr P
	      (apply mk-proof-in-elim-form
		     (make-proof-in-aconst-form exu-elim-aconst)
		     (append (map make-term-in-var-form exu-elim-aconst-free)
			     (list (make-proof-in-avar-form u1)
				   (make-proof-in-avar-form v)
				   (make-term-in-var-form b)))))
	     (exu-intro-proof ;of exu a a mr A --> b mr B --> fb mr P
	      (mk-proof-in-nc-intro-form u1 exu-elim-proof))
	     (andu-imp-formula (make-imp mr-andr mr-concl))
	     (andu-elim-aconst (imp-formulas-to-elim-aconst andu-imp-formula))
	     (andu-elim-aconst-free (formula-to-free andu-imp-formula))
	     (andu-elim-proof ;of fb mr P
	      (apply mk-proof-in-elim-form
		     (make-proof-in-aconst-form andu-elim-aconst)
		     (append (map make-term-in-var-form andu-elim-aconst-free)
			     (list (make-proof-in-avar-form u)
				   exu-intro-proof)))))
	(apply mk-proof-in-nc-intro-form
	       (append free (if (nulltype? concl-type)
				(list b u v andu-elim-proof)
				(list b u f-or-eps v andu-elim-proof))))))
     (else (myerror "andr-formula-and-concl-to-andr-elim-mr-proof"
		    "unexpected types" left-type right-type)))))

(define (andl-formula-and-concl-to-andl-elim-mr-proof andl-formula concl)
  (let* ((free (union (formula-to-free andl-formula) (formula-to-free concl)))
	 (left (andl-form-to-left andl-formula))
	 (left-type (formula-to-et-type left))
	 (right (andl-form-to-right andl-formula))
	 (right-type (formula-to-et-type right))
	 (concl-type (formula-to-et-type concl)))
    (cond
     ((and (nulltype? left-type) (nulltype? right-type))
      (let* ((mr-andl ;eps mr (A andl B), which is eps mr A andu eps mr B
	      (real-and-formula-to-mr-formula-aux 'eps andl-formula))
	     (u (formula-to-new-avar mr-andl "u"))
	     (c-or-eps (if (nulltype? concl-type) 'eps
			   (type-to-new-partial-var concl-type)))
	     (c-term-or-eps (if (nulltype? concl-type) 'eps
				(make-term-in-var-form c-or-eps)))
	     (v-formula ;eps mr A --> eps mr B --> c mr P, i.e.,
					;f mr (A -> B --> P)
	      (real-and-formula-to-mr-formula-aux
	       c-term-or-eps (make-imp left (make-impnc right concl))))
	     (v (formula-to-new-avar v-formula "v"))
	     (mr-concl ;c mr P
	      (real-and-formula-to-mr-formula-aux c-term-or-eps concl))
	     (andu-imp-formula (make-imp mr-andl mr-concl))
	     (andu-elim-aconst (imp-formulas-to-elim-aconst andu-imp-formula))
	     (andu-elim-aconst-free (formula-to-free andu-imp-formula))
	     (andu-elim-proof ;of c mr P
	      (apply mk-proof-in-elim-form
		     (make-proof-in-aconst-form andu-elim-aconst)
		     (append (map make-term-in-var-form andu-elim-aconst-free)
			     (list (make-proof-in-avar-form u)
				   (make-proof-in-avar-form v))))))
	(apply mk-proof-in-nc-intro-form
	       (append free (if (nulltype? concl-type)
				(list u v andu-elim-proof)
				(list u c-or-eps v andu-elim-proof))))))
     ((and (nulltype? left-type) (not (nulltype? right-type)))
      (let* ((b (type-to-new-partial-var right-type))
	     (b-term (make-term-in-var-form b))
	     (mr-andl ;eps mr (A andl B), which is eps mr A andu exu b b mr B
	      (real-and-formula-to-mr-formula-aux eps andl-formula))
	     (u (formula-to-new-avar mr-andr "u"))
	     (c-or-eps (if (nulltype? concl-type) 'eps
			   (type-to-new-partial-var
			    (make-arrow right-type concl-type))))
	     (c-term-or-eps (if (nulltype? concl-type) 'eps
				(make-term-in-var-form c-or-eps)))
	     (v-formula ;eps mr A --> allnc b(b mr B --> c mr P), i.e.,
					;c mr (A -> B --> P)
	      (real-and-formula-to-mr-formula-aux
	       c-term-or-eps (make-impnc left (make-imp right concl))))
	     (v (formula-to-new-avar v-formula "v"))
	     (mr-concl ;c mr P
	      (real-and-formula-to-mr-formula-aux c-term-or-eps concl))
	     (exu-imp-formula ;eps mr A -> exu b b mr B -> c mr P)
	      (make-imp
	       (andu-form-to-left mr-andr)
	       (make-imp (andu-form-to-right mr-andr) mr-concl)))
	     (exu-elim-aconst (imp-formulas-to-elim-aconst exu-imp-formula))
	     (exu-elim-aconst-free (formula-to-free exu-imp-formula))
	     (u1 (formula-to-new-avar (andu-form-to-left mr-andr))) ;eps mr A
	     (u2 ;exu b b mr B
	      (formula-to-new-avar (andu-form-to-right mr-andr)))
	     (exu-elim-proof ;of exu b b mr B --> c mr P
	      (apply mk-proof-in-elim-form
		     (make-proof-in-aconst-form exu-elim-aconst)
		     (append (map make-term-in-var-form exu-elim-aconst-free)
			     (list (make-proof-in-avar-form u1)
				   (make-proof-in-avar-form v)))))
	     (exu-intro-proof ;of eps mr A --> exu b b mr B --> c mr P
	      (mk-proof-in-nc-intro-form u1 exu-elim-proof))
	     (andu-imp-formula (make-imp mr-andl mr-concl))
	     (andu-elim-aconst (imp-formulas-to-elim-aconst andu-imp-formula))
	     (andu-elim-aconst-free (formula-to-free andu-imp-formula))
	     (andu-elim-proof ;of c mr P
	      (apply mk-proof-in-elim-form
		     (make-proof-in-aconst-form andu-elim-aconst)
		     (append (map make-term-in-var-form andu-elim-aconst-free)
			     (list (make-proof-in-avar-form u)
				   exu-intro-proof)))))
	(apply mk-proof-in-nc-intro-form
	       (append free (if (nulltype? concl-type)
				(list u v andu-elim-proof)
				(list u c-or-eps v andu-elim-proof))))))
     ((and (not (nulltype? left-type)) (nulltype? right-type))
      (let* ((a (type-to-new-partial-var left-type))
	     (a-term (make-term-in-var-form a))
	     (mr-andl ;eps mr (A andl B), which is exu a a mr A andu eps mr B
	      (real-and-formula-to-mr-formula-aux 'eps andl-formula))
	     (u (formula-to-new-avar mr-andr "u"))
	     (f-or-eps (if (nulltype? concl-type) 'eps
			   (type-to-new-partial-var
			    (make-arrow left-type concl-type))))
	     (f-term-or-eps (if (nulltype? concl-type) 'eps
				(make-term-in-var-form f-or-eps)))
	     (v-formula ;allnc a(a mr A --> eps mr B --> fa mr P)), i.e.,
					;f mr (A -> B --> P)
	      (real-and-formula-to-mr-formula-aux
	       f-term-or-eps (make-imp left (make-impnc right concl))))
	     (v (formula-to-new-avar v-formula "v"))
	     (mr-concl ;fa mr P
	      (real-and-formula-to-mr-formula-aux
	       (if (nulltype? concl-type) 'eps
		   (make-term-in-app-form f-term-or-eps a-term))
	       concl))
	     (exu-imp-formula ;exu a a mr A -> eps mr B --> c mr P)
	      (make-imp
	       (andu-form-to-left mr-andl)
	       (make-impnc (andu-form-to-right mr-andl) mr-concl)))
	     (exu-elim-aconst (imp-formulas-to-elim-aconst exu-imp-formula))
	     (exu-elim-aconst-free (formula-to-free exu-imp-formula))
	     (u1 ;exu a a mr A
	      (formula-to-new-avar (andu-form-to-left mr-andl)))
	     (u2 (formula-to-new-avar (andu-form-to-right mr-andl))) ;eps mr B
	     (exu-elim-proof ;of eps mr B --> c mr P
	      (apply mk-proof-in-elim-form
		     (make-proof-in-aconst-form exu-elim-aconst)
		     (append (map make-term-in-var-form exu-elim-aconst-free)
			     (list (make-proof-in-avar-form u1)
				   (make-proof-in-avar-form v)))))
	     (exu-intro-proof ;of exu a a mr A --> eps mr B --> c mr P
	      (mk-proof-in-nc-intro-form u1 exu-elim-proof))
	     (andu-imp-formula (make-imp mr-andl mr-concl))
	     (andu-elim-aconst (imp-formulas-to-elim-aconst andu-imp-formula))
	     (andu-elim-aconst-free (formula-to-free andu-imp-formula))
	     (andu-elim-proof ;of c mr P
	      (apply mk-proof-in-elim-form
		     (make-proof-in-aconst-form andu-elim-aconst)
		     (append (map make-term-in-var-form andu-elim-aconst-free)
			     (list (make-proof-in-avar-form u)
				   exu-intro-proof)))))
	(apply mk-proof-in-nc-intro-form
	       (append free (if (nulltype? concl-type)
				(list u v andu-elim-proof)
				(list u c-or-eps v andu-elim-proof))))))
     ((and (not (nulltype? left-type)) (not (nulltype? right-type)))
      (let* ((a (type-to-new-partial-var left-type))
	     (a-term (make-term-in-var-form a))
	     (b (type-to-new-partial-var right-type))
	     (b-term (make-term-in-var-form b))
	     (mr-andl ;b mr (A andl B), which is exu a a mr A andu b mr B
	      (real-and-formula-to-mr-formula-aux b-term andl-formula))
	     (u (formula-to-new-avar mr-andl "u"))
	     (f-or-eps (if (nulltype? concl-type) 'eps
			   (type-to-new-partial-var
			    (make-arrow right-type concl-type))))
	     (f-term-or-eps (if (nulltype? concl-type) 'eps
				(make-term-in-var-form f-or-eps)))
	     (v-formula ;allnc a(a mr A --> allnc b(b mr B --> fb mr P)), i.e.,
					;f mr (A --> B -> P)
	      (real-and-formula-to-mr-formula-aux
	       f-term-or-eps (make-impnc left (make-imp right concl))))
	     (v (formula-to-new-avar v-formula "v"))
	     (mr-concl ;fb mr P
	      (real-and-formula-to-mr-formula-aux
	       (if (nulltype? concl-type) 'eps
		   (make-term-in-app-form f-term-or-eps b-term))
	       concl))
	     (exu-imp-formula ;exu a a mr A -> allnc b(b mr B --> fb mr P)
	      (make-imp
	       (andu-form-to-left mr-andl)
	       (make-allnc
		b (make-impnc (andu-form-to-right mr-andl) mr-concl))))
	     (exu-elim-aconst (imp-formulas-to-elim-aconst exu-imp-formula))
	     (exu-elim-aconst-free (formula-to-free exu-imp-formula))
	     (u1 ;exu a a mr A
	      (formula-to-new-avar (andu-form-to-left mr-andl)))
	     (exu-elim-proof ;of b mr B --> fb mr P
	      (apply mk-proof-in-elim-form
		     (make-proof-in-aconst-form exu-elim-aconst)
		     (append (map make-term-in-var-form exu-elim-aconst-free)
			     (list (make-proof-in-avar-form u1)
				   (make-proof-in-avar-form v)
				   (make-term-in-var-form b)))))
	     (exu-intro-proof ;of exu a a mr A --> b mr B --> fb mr P
	      (mk-proof-in-nc-intro-form u1 exu-elim-proof))
	     (andu-imp-formula (make-imp mr-andl mr-concl))
	     (andu-elim-aconst (imp-formulas-to-elim-aconst andu-imp-formula))
	     (andu-elim-aconst-free (formula-to-free andu-imp-formula))
	     (andu-elim-proof ;of fb mr P
	      (apply mk-proof-in-elim-form
		     (make-proof-in-aconst-form andu-elim-aconst)
		     (append (map make-term-in-var-form andu-elim-aconst-free)
			     (list (make-proof-in-avar-form u)
				   exu-intro-proof)))))
	(apply mk-proof-in-nc-intro-form
	       (append free (if (nulltype? concl-type)
				(list b u v andu-elim-proof)
				(list b u f-or-eps v andu-elim-proof))))))
     (else (myerror "andl-formula-and-concl-to-andl-elim-mr-proof"
		    "unexpected types" left-type right-type)))))

(define (eqd-elim-aconst-to-eqd-mr-elim-proof aconst)
  (let* ((imp-formulas (aconst-to-repro-data aconst))
	 (imp-formula (car imp-formulas))
	 (eqd-prem (imp-form-to-premise imp-formula))
	 (eqd-terms (predicate-form-to-args eqd-prem))
	 (uninst-formula (aconst-to-uninst-formula aconst))
	 (tvar (car (formula-to-tvars uninst-formula)))
	 (pvar (car (formula-to-pvars uninst-formula)))
	 (tpsubst (aconst-to-tpsubst aconst))
	 (type (let ((info (assoc tvar tpsubst)))
		 (if info (cadr info) tvar)))
	 (cterm (let ((info (assoc pvar tpsubst)))
		  (if info (cadr info) (predicate-to-cterm pvar))))
	 (vars (cterm-to-vars cterm))
	 (formula (formula-substitute
		   (cterm-to-formula cterm)
		   (make-substitution-wrt var-term-equal? vars eqd-terms)))
	 (et-type (formula-to-et-type formula))
	 (real (if (nulltype? et-type)
		   'eps
		   (make-term-in-var-form (type-to-new-partial-var et-type))))
	 (mr-formula (real-and-formula-to-mr-formula-aux real formula))
	 (mr-imp-formula (make-imp eqd-prem mr-formula))
	 (eqd-elim-aconst-with-mr-formula
	  (imp-formulas-to-elim-aconst mr-imp-formula))
	 (free (formula-to-free mr-imp-formula))
	 (u (formula-to-new-avar eqd-prem))
	 (elim-proof (apply mk-proof-in-elim-form
			    (make-proof-in-aconst-form
			     eqd-elim-aconst-with-mr-formula)
			    (append (map make-term-in-var-form free)
				    (list (make-proof-in-avar-form u))))))
    (if (nulltype? et-type)
	(apply mk-proof-in-nc-intro-form
	       (append free (list u elim-proof)))
	(let ((z (term-in-var-form-to-var real)))
	  (apply mk-proof-in-nc-intro-form
		 (append (remove z free) (list u z elim-proof)))))))

(define (exu-formula-and-concl-to-exu-elim-mr-proof exu-formula concl)
  (let* ((free (union (formula-to-free exu-formula) (formula-to-free concl)))
	 (var (exu-form-to-var exu-formula))
	 (var-term (make-term-in-var-form var))
	 (type (var-to-type var))
	 (kernel (exu-form-to-kernel exu-formula))
	 (kernel-type (formula-to-et-type kernel))
	 (concl-type (formula-to-et-type concl)))
    (if
     (nulltype? kernel-type)
     (let* ((mr-kernel ;eps mr exu x A, which is the same as exu x eps mr A
	     (real-and-formula-to-mr-formula-aux 'eps exu-formula))
	    (u (formula-to-new-avar mr-kernel "u"))
	    (b-or-eps (if (nulltype? concl-type) 'eps
			  (type-to-new-partial-var concl-type)))
	    (b-term-or-eps (if (nulltype? concl-type) 'eps
			       (make-term-in-var-form b-or-eps)))
	    (v-formula ;b mr allnc x(A -> P)
	     (real-and-formula-to-mr-formula-aux
	      b-term-or-eps (make-allnc var (make-imp kernel concl))))
	    (v (formula-to-new-avar v-formula "v"))
	    (mr-concl ;b mr P
	     (real-and-formula-to-mr-formula-aux b-term-or-eps concl))
	    (imp-formula (make-imp mr-kernel mr-concl))
	    (aconst (imp-formulas-to-elim-aconst imp-formula))
	    (aconst-free (formula-to-free imp-formula))
	    (elim-proof ;of b mr P
	     (apply mk-proof-in-elim-form
		    (make-proof-in-aconst-form aconst)
		    (append (map make-term-in-var-form aconst-free)
			    (list (make-proof-in-avar-form u)
				  (make-proof-in-avar-form v))))))
       (apply mk-proof-in-nc-intro-form
	      (append free (if (nulltype? concl-type)
			       (list u v elim-proof)
			       (list u b-or-eps v elim-proof)))))
     (let* ((real-var ;a
	     (type-to-new-partial-var kernel-type))
	    (real-term (make-term-in-var-form real-var))
	    (mr-kernel ;a mr A
	     (real-and-formula-to-mr-formula-aux real-term kernel))
	    (u1 ;exu a a mr A
	     (formula-to-new-avar (make-exu real-var mr-kernel)))
	    (b-or-eps (if (nulltype? concl-type) 'eps
			  (type-to-new-partial-var concl-type)))
	    (b-term-or-eps (if (nulltype? concl-type) 'eps
			       (make-term-in-var-form b-or-eps)))
	    (mr-concl ;b mr P
	     (real-and-formula-to-mr-formula-aux b-term-or-eps concl))
	    (v-formula ;allnc x,a(a mr A --> b mr P)
	     (mk-allnc var real-var (make-impnc mr-kernel mr-concl)))
	    (v (formula-to-new-avar v-formula "v"))
	    (imp-formula1 ;exu a a mr A -> b mr P
	     (make-imp (make-exu real-var mr-kernel) mr-concl))
	    (aconst1 (imp-formulas-to-elim-aconst imp-formula1))
	    (aconst1-free (formula-to-free imp-formula1))
	    (elim-proof1 ;of b mr P
	     (apply mk-proof-in-elim-form
		    (make-proof-in-aconst-form aconst1)
		    (append (map make-term-in-var-form aconst1-free)
			    (list (make-proof-in-avar-form u1)
				  (mk-proof-in-elim-form
				   (make-proof-in-avar-form v)
				   var-term)))))
	    (intro-proof ;of allnc x(exu a a mr A --> b mr P)
	     (mk-proof-in-nc-intro-form var u1 elim-proof1))
	    (u ;exu x,a a mr A
	     (formula-to-new-avar (mk-exu var real-var mr-kernel)))
	    (imp-formula ;exu x,a a mr A -> b mr P
	     (make-imp (mk-exu var real-var mr-kernel) mr-concl))
	    (aconst (imp-formulas-to-elim-aconst imp-formula))
	    (aconst-free (formula-to-free imp-formula))
	    (elim-proof ;of b mr P
	     (apply mk-proof-in-elim-form
		    (make-proof-in-aconst-form aconst)
		    (append (map make-term-in-var-form aconst-free)
			    (list (make-proof-in-avar-form u)
				  intro-proof)))))
       (apply mk-proof-in-nc-intro-form
	      (append free (if (nulltype? concl-type)
			       (list u v elim-proof)
			       (list u b-or-eps v elim-proof))))))))

(define (andu-formula-and-concl-to-andu-elim-mr-proof andu-formula concl)
  (let* ((free (union (formula-to-free andu-formula) (formula-to-free concl)))
	 (left (andu-form-to-left andu-formula))
	 (left-type (formula-to-et-type left))
	 (right (andu-form-to-right andu-formula))
	 (right-type (formula-to-et-type right))
	 (concl-type (formula-to-et-type concl)))
    (cond
     ((and (nulltype? left-type) (nulltype? right-type))
      (let* ((c-or-eps (if (nulltype? concl-type) 'eps
			   (type-to-new-partial-var concl-type)))
	     (c-term-or-eps (if (nulltype? concl-type) 'eps
				(make-term-in-var-form c-or-eps)))
	     (eps-mr-left (real-and-formula-to-mr-formula-aux 'eps left))
	     (eps-mr-right (real-and-formula-to-mr-formula-aux 'eps right))
	     (u-formula ;eps mr A andu eps mr B
	      (make-andu eps-mr-left eps-mr-right))
	     (u (formula-to-new-avar u-formula "u"))
	     (c-mr-concl (real-and-formula-to-mr-formula-aux
			  c-term-or-eps concl))
	     (v-formula (mk-impnc eps-mr-left eps-mr-right c-mr-concl))
	     (v (formula-to-new-avar v-formula "v"))
	     (andu-imp-formula (make-imp u-formula c-mr-concl))
	     (andu-elim-aconst (imp-formulas-to-elim-aconst andu-imp-formula))
	     (free (formula-to-free andu-imp-formula))
	     (andu-elim-proof ;of c mr C
	      (apply mk-proof-in-elim-form
		     (make-proof-in-aconst-form andu-elim-aconst)
		     (append (map make-term-in-var-form free)
			     (list (make-proof-in-avar-form u)
				   (make-proof-in-avar-form v))))))
	(if (nulltype? concl-type)
	    (apply mk-proof-in-nc-intro-form
		   (append free (list u v andu-elim-proof)))
	    (apply mk-proof-in-nc-intro-form
		   (append (remove c-or-eps free)
			   (list u c-or-eps v andu-elim-proof))))))
     ((and (nulltype? left-type) (not (nulltype? right-type)))
      (let* ((b (type-to-new-partial-var right-type))
	     (b-term (make-term-in-var-form b))
	     (c-or-eps (if (nulltype? concl-type) 'eps
			   (type-to-new-partial-var concl-type)))
	     (c-term-or-eps (if (nulltype? concl-type) 'eps
				(make-term-in-var-form c-or-eps)))
	     (eps-mr-left (real-and-formula-to-mr-formula-aux 'eps left))
	     (u1 (formula-to-new-avar eps-mr-left "u"))
	     (b-mr-right (real-and-formula-to-mr-formula-aux b-term right))
	     (c-mr-concl (real-and-formula-to-mr-formula-aux
			  c-term-or-eps concl))
	     (v-formula (make-impnc
			 eps-mr-left (make-allnc
				      b (make-impnc b-mr-right c-mr-concl))))
	     (v (formula-to-new-avar v-formula "v"))
	     (u2-formula (make-exu b b-mr-right)) ;exu b b mr B
	     (u2 (formula-to-new-avar u2-formula "u"))
	     (u-formula ;eps mr A andu exu b b mr B
	      (make-andu eps-mr-left u2-formula))
	     (u (formula-to-new-avar u-formula "u"))
	     (imp-formula2 (make-imp u2-formula c-mr-concl))
	     (andu-imp-formula (make-imp u-formula c-mr-concl))
	     (aconst2 (imp-formulas-to-elim-aconst imp-formula2))
	     (free2 (formula-to-free imp-formula2))
	     (andu-elim-aconst (imp-formulas-to-elim-aconst andu-imp-formula))
	     (free (formula-to-free andu-imp-formula))
	     (elim-proof2 ;of c mr C
	      (apply mk-proof-in-elim-form
		     (make-proof-in-aconst-form aconst2)
		     (append (map make-term-in-var-form free2)
			     (list (make-proof-in-avar-form u2)
				   (mk-proof-in-elim-form
				    (make-proof-in-avar-form v)
				    (make-proof-in-avar-form u1))))))
	     (intro-proof2 ;of eps mr A --> exu b b mr B --> c mr C
	      (mk-proof-in-nc-intro-form u1 u2 elim-proof2))
	     (andu-elim-proof ;of c mr C
	      (apply mk-proof-in-elim-form
		     (make-proof-in-aconst-form andu-elim-aconst)
		     (append (map make-term-in-var-form free)
			     (list (make-proof-in-avar-form u)
				   intro-proof2)))))
	(if (nulltype? concl-type)
	    (apply mk-proof-in-nc-intro-form
		   (append free (list u v andu-elim-proof)))
	    (apply mk-proof-in-nc-intro-form
		   (append (remove c-or-eps free)
			   (list u c-or-eps v andu-elim-proof))))))
     ((and (not (nulltype? left-type)) (nulltype? right-type))
      (let* ((a (type-to-new-partial-var left-type))
	     (a-term (make-term-in-var-form a))
	     (c-or-eps (if (nulltype? concl-type) 'eps
			   (type-to-new-partial-var concl-type)))
	     (c-term-or-eps (if (nulltype? concl-type) 'eps
				(make-term-in-var-form c-or-eps)))
	     (a-mr-left (real-and-formula-to-mr-formula-aux a-term left))
	     (eps-mr-right (real-and-formula-to-mr-formula-aux 'eps right))
	     (c-mr-concl (real-and-formula-to-mr-formula-aux
			  c-term-or-eps concl))
	     (v-formula (make-allnc
			 a (mk-impnc a-mr-left eps-mr-right c-mr-concl)))
	     (v (formula-to-new-avar v-formula "v"))
	     (u1-formula (make-exu a a-mr-left)) ;exu a a mr A
	     (u1 (formula-to-new-avar u1-formula "u"))
	     (u-formula ;exu a a mr A andu eps mr B
	      (make-andu u1-formula eps-mr-right))
	     (u (formula-to-new-avar u-formula "u"))
	     (imp-formula1 (make-imp u1-formula
				     (make-impnc eps-mr-right c-mr-concl)))
	     (andu-imp-formula (make-imp u-formula c-mr-concl))
	     (aconst1 (imp-formulas-to-elim-aconst imp-formula1))
	     (andu-elim-aconst (imp-formulas-to-elim-aconst andu-imp-formula))
	     (free (formula-to-free andu-imp-formula)) ;same as free1
	     (elim-proof1 ;of eps mr B --> c mr C
	      (apply mk-proof-in-elim-form
		     (make-proof-in-aconst-form aconst1)
		     (append (map make-term-in-var-form free)
			     (list (make-proof-in-avar-form u1)
				   (make-proof-in-avar-form v)))))
	     (intro-proof1 ;of exu a a mr A --> eps mr B --> c mr C
	      (mk-proof-in-nc-intro-form u1 elim-proof1))
	     (andu-elim-proof ;of c mr C
	      (apply mk-proof-in-elim-form
		     (make-proof-in-aconst-form andu-elim-aconst)
		     (append (map make-term-in-var-form free)
			     (list (make-proof-in-avar-form u)
				   intro-proof1)))))
	(if (nulltype? concl-type)
	    (apply mk-proof-in-nc-intro-form
		   (append free (list u v andu-elim-proof)))
	    (apply mk-proof-in-nc-intro-form
		   (append (remove c-or-eps free)
			   (list u c-or-eps v andu-elim-proof))))))
     ((and (not (nulltype? left-type)) (not (nulltype? right-type)))
      (let* ((a (type-to-new-partial-var left-type))
	     (a-term (make-term-in-var-form a))
	     (b (type-to-new-partial-var right-type))
	     (b-term (make-term-in-var-form b))
	     (c-or-eps (if (nulltype? concl-type) 'eps
			   (type-to-new-partial-var concl-type)))
	     (c-term-or-eps (if (nulltype? concl-type) 'eps
				(make-term-in-var-form c-or-eps)))
	     (a-mr-left (real-and-formula-to-mr-formula-aux a-term left))
	     (u11 (formula-to-new-avar a-mr-left "u"))
	     (b-mr-right (real-and-formula-to-mr-formula-aux b-term right))
	     (c-mr-concl (real-and-formula-to-mr-formula-aux
			  c-term-or-eps concl))
	     (v-formula (make-allnc
			 a (make-impnc
			    a-mr-left
			    (make-allnc
			     b (make-impnc b-mr-right c-mr-concl)))))
	     (v (formula-to-new-avar v-formula "v"))
	     (u1-formula (make-exu a a-mr-left)) ;exu a a mr A
	     (u1 (formula-to-new-avar u1-formula "u"))
	     (u2-formula (make-exu b b-mr-right)) ;exu b b mr B
	     (u2 (formula-to-new-avar u2-formula "u"))
	     (u-formula ;exu a a mr A andu exu b b mr B
	      (make-andu u1-formula u2-formula))
	     (u (formula-to-new-avar u-formula "u"))
	     (imp-formula2 (make-imp u2-formula c-mr-concl))
	     (imp-formula1 (make-imp u1-formula
				     (make-impnc u2-formula c-mr-concl)))
	     (andu-imp-formula (make-imp u-formula c-mr-concl))
	     (aconst2 (imp-formulas-to-elim-aconst imp-formula2))
	     (free2 (formula-to-free imp-formula2))
	     (aconst1 (imp-formulas-to-elim-aconst imp-formula1))
	     (andu-elim-aconst (imp-formulas-to-elim-aconst andu-imp-formula))
	     (free (formula-to-free andu-imp-formula)) ;same as free1
	     (elim-proof2 ;of c mr C
	      (apply mk-proof-in-elim-form
		     (make-proof-in-aconst-form aconst2)
		     (append (map make-term-in-var-form free2)
			     (list (make-proof-in-avar-form u2)
				   (mk-proof-in-elim-form
				    (make-proof-in-avar-form v)
				    a-term
				    (make-proof-in-avar-form u11))))))
	     (intro-proof2 ;of allnc a(a mr A --> exu b b mr B --> c mr C)
	      (mk-proof-in-nc-intro-form a u11 u2 elim-proof2))
	     (elim-proof1 ;of exu b b mr B --> c mr C
	      (apply mk-proof-in-elim-form
		     (make-proof-in-aconst-form aconst1)
		     (append (map make-term-in-var-form free)
			     (list (make-proof-in-avar-form u1)
				   intro-proof2))))
	     (intro-proof1 ;of exu a a mr A --> exu b b mr B --> c mr C
	      (mk-proof-in-nc-intro-form u1 elim-proof1))
	     (andu-elim-proof ;of c mr C
	      (apply mk-proof-in-elim-form
		     (make-proof-in-aconst-form andu-elim-aconst)
		     (append (map make-term-in-var-form free)
			     (list (make-proof-in-avar-form u)
				   intro-proof1)))))
	(if (nulltype? concl-type)
	    (apply mk-proof-in-nc-intro-form
		   (append free (list u v andu-elim-proof)))
	    (apply mk-proof-in-nc-intro-form
		   (append (remove c-or-eps free)
			   (list u c-or-eps v andu-elim-proof))))))
     (else (myerror "andu-formula-and-concl-to-andu-elim-mr-proof"
		    "unexpected types" left-type right-type)))))

(define (make-avar-or-ga-to-var)
  ;; returns a procedure assigning to assumption variables or
  ;; constants (gas) whose types have computational content new object
  ;; variables of the corresponding et-type.  It remembers the
  ;; assignment done so far.
  (let ((avar-assoc-list '())
	(ga-assoc-list '()))
    (lambda (x)
      (let ((info (if (avar-form? x)
		      (assoc-wrt avar=? x avar-assoc-list)
		      (assoc-wrt aconst=? x ga-assoc-list))))
	(if info
	    (cadr info)
	    (let* ((formula (if (avar-form? x)
				(avar-to-formula x)
				(aconst-to-formula x)))
		   (type (formula-to-et-type formula))
		   (new-var (if (nulltype? type)
				(myerror "make-avar-or-ga-to-var"
					 "computational content expected in"
					 formula)
				(type-to-new-partial-var type))))
	      (if (avar-form? x)
		  (begin (set! avar-assoc-list
			       (cons (list x new-var) avar-assoc-list))
			 new-var)
		  (begin (set! ga-assoc-list
			       (cons (list x new-var) ga-assoc-list))
			 new-var))))))))

(define (make-avar-or-ga-to-mr-avar avar-or-ga-to-var)
  ;; returns a procedure assigning to an avar or ga u:A a new avar
  ;; u':x_u mr A.  Remembers the assignment done so far.
  (let ((avar-assoc-list '())
	(ga-assoc-list '()))
    (lambda (x)
      (let ((info (if (avar-form? x)
		      (assoc-wrt avar=? x avar-assoc-list)
		      (assoc-wrt aconst=? x ga-assoc-list))))
	(if info
	    (cadr info)
	    (let* ((formula (if (avar-form? x)
				(avar-to-formula x)
				(aconst-to-formula x)))
		   (type (formula-to-et-type formula))
		   (mr-formula (real-and-formula-to-mr-formula-aux
				(if (nulltype? type)
				    'eps
				    (make-term-in-var-form
				     (avar-or-ga-to-var x)))
				formula))
		   (mr-avar (formula-to-new-avar mr-formula "umr")))
	      (if (avar-form? x)
		  (begin (set! avar-assoc-list
			       (cons (list x mr-avar) avar-assoc-list))
			 mr-avar)
		  (begin (set! ga-assoc-list
			       (cons (list x mr-avar) ga-assoc-list))
			 mr-avar))))))))

(define (proof-to-soundness-proof . opt-proof-or-thm-name)
  (if (null? opt-proof-or-thm-name)
      (proof-to-soundness-proof (current-proof))
      (let* ((proof-or-thm-name (car opt-proof-or-thm-name))
	     (proof (cond ((proof-form? proof-or-thm-name) proof-or-thm-name)
			  ((string? proof-or-thm-name)
			   (theorem-name-to-proof proof-or-thm-name))
			  (else (myerror "proof-to-soundness-proof"
					 "proof or theorem name expected"
					 proof-or-thm-name))))
	     (avar-or-ga-to-var (make-avar-or-ga-to-var))
	     (avar-or-ga-to-mr-avar (make-avar-or-ga-to-mr-avar
				     avar-or-ga-to-var)))
	(proof-to-soundness-proof-aux
	 proof avar-or-ga-to-var avar-or-ga-to-mr-avar))))

(define (proof-to-soundness-proof-aux
	 proof avar-or-ga-to-var avar-or-ga-to-mr-avar)
  (case (tag proof)
    ((proof-in-avar-form)
     (let* ((avar (proof-in-avar-form-to-avar proof))
	    (mr-avar (avar-or-ga-to-mr-avar avar)))
       (make-proof-in-avar-form mr-avar)))
    ((proof-in-aconst-form)
     (if
      (non-computational-invariant? (proof-to-formula proof) '())
      proof
      (let* ((aconst (proof-in-aconst-form-to-aconst proof))
	     (name (aconst-to-name aconst)))
	(case (aconst-to-kind aconst)
	  ((axiom) (axiom-to-soundness-proof aconst))
	  ((theorem) (theorem-to-soundness-proof aconst))
	  ((global-assumption) (global-assumption-to-soundness-proof
				aconst avar-or-ga-to-mr-avar))
	  (else (myerror
		 "proof-to-soundness-proof-aux" "unknown kind of aconst"
		 (aconst-to-kind aconst)))))))
    ((proof-in-imp-intro-form)
     (let* ((avar (proof-in-imp-intro-form-to-avar proof))
	    (mr-avar (avar-or-ga-to-mr-avar avar))
	    (avar-type (formula-to-et-type (avar-to-formula avar)))
	    (kernel (proof-in-imp-intro-form-to-kernel proof))
	    (kernel-proof (proof-to-soundness-proof-aux
			   kernel avar-or-ga-to-var avar-or-ga-to-mr-avar))
	    (impnc-intro-proof
	     (mk-proof-in-nc-intro-form mr-avar kernel-proof)))
       (if (nulltype? avar-type)
	   impnc-intro-proof
	   (mk-proof-in-nc-intro-form
	    (avar-or-ga-to-var avar) impnc-intro-proof))))
    ((proof-in-imp-elim-form)
     (let* ((op (proof-in-imp-elim-form-to-op proof))
	    (arg (proof-in-imp-elim-form-to-arg proof))
	    (arg-type (formula-to-et-type (proof-to-formula arg)))
	    (op-proof (proof-to-soundness-proof-aux
		       op avar-or-ga-to-var avar-or-ga-to-mr-avar))
	    (arg-proof (proof-to-soundness-proof-aux
			arg avar-or-ga-to-var avar-or-ga-to-mr-avar)))
       (if (nulltype? arg-type)
	   (mk-proof-in-elim-form op-proof arg-proof)
	   (mk-proof-in-elim-form
	    op-proof
	    (proof-to-extracted-term-aux
	     arg avar-or-ga-to-var #t) ;unfold-let-flag is true here
	    arg-proof))))
    ((proof-in-impnc-intro-form)
     (let* ((avar (proof-in-impnc-intro-form-to-avar proof))
	    (mr-avar (avar-or-ga-to-mr-avar avar))
	    (avar-type (formula-to-et-type (avar-to-formula avar)))
	    (kernel (proof-in-impnc-intro-form-to-kernel proof))
	    (kernel-proof (proof-to-soundness-proof-aux
			   kernel avar-or-ga-to-var avar-or-ga-to-mr-avar))
	    (impnc-intro-proof
	     (mk-proof-in-nc-intro-form mr-avar kernel-proof)))
       (if (nulltype? avar-type)
	   impnc-intro-proof
	   (mk-proof-in-nc-intro-form
	    (avar-or-ga-to-var avar) impnc-intro-proof))))
    ((proof-in-impnc-elim-form)
     (let* ((op (proof-in-impnc-elim-form-to-op proof))
	    (arg (proof-in-impnc-elim-form-to-arg proof))
	    (arg-type (formula-to-et-type (proof-to-formula arg)))
	    (op-proof (proof-to-soundness-proof-aux
		       op avar-or-ga-to-var avar-or-ga-to-mr-avar))
	    (arg-proof (proof-to-soundness-proof-aux
			arg avar-or-ga-to-var avar-or-ga-to-mr-avar)))
       (if (nulltype? arg-type)
	   (mk-proof-in-elim-form op-proof arg-proof)
	   (mk-proof-in-elim-form
	    op-proof
	    (proof-to-extracted-term-aux arg avar-or-ga-to-var #t)
	    arg-proof))))
    ((proof-in-and-intro-form)
     (let* ((left (proof-in-and-intro-form-to-left proof))
	    (right (proof-in-and-intro-form-to-right proof))
	    (left-proof (proof-to-soundness-proof-aux
			 left avar-or-ga-to-var avar-or-ga-to-mr-avar))
	    (right-proof (proof-to-soundness-proof-aux
			  right avar-or-ga-to-var avar-or-ga-to-mr-avar)))
       (make-proof-in-and-intro-form left-proof right-proof)))
    ((proof-in-and-elim-left-form)
     (let* ((kernel (proof-in-and-elim-left-form-to-kernel proof))
	    (kernel-proof (proof-to-soundness-proof-aux
			   kernel avar-or-ga-to-var avar-or-ga-to-mr-avar)))
       (make-proof-in-and-elim-left-form kernel-proof)))
    ((proof-in-and-elim-right-form)
     (let* ((kernel (proof-in-and-elim-right-form-to-kernel proof))
	    (kernel-proof (proof-to-soundness-proof-aux
			   kernel avar-or-ga-to-var avar-or-ga-to-mr-avar)))
       (make-proof-in-and-elim-right-form kernel-proof)))
    ((proof-in-all-intro-form)
     (let* ((var (proof-in-all-intro-form-to-var proof))
	    (kernel (proof-in-all-intro-form-to-kernel proof))
	    (kernel-proof (proof-to-soundness-proof-aux
			   kernel avar-or-ga-to-var avar-or-ga-to-mr-avar)))
       (mk-proof-in-nc-intro-form var kernel-proof)))
    ((proof-in-all-elim-form)
     (let* ((op (proof-in-all-elim-form-to-op proof))
	    (op-proof (proof-to-soundness-proof-aux
		       op avar-or-ga-to-var avar-or-ga-to-mr-avar))
	    (arg (proof-in-all-elim-form-to-arg proof)))
       (mk-proof-in-elim-form op-proof arg)))
    ((proof-in-allnc-intro-form)
     (let* ((var (proof-in-allnc-intro-form-to-var proof))
	    (kernel (proof-in-allnc-intro-form-to-kernel proof))
	    (kernel-proof (proof-to-soundness-proof-aux
			   kernel avar-or-ga-to-var avar-or-ga-to-mr-avar)))
       (mk-proof-in-nc-intro-form var kernel-proof)))
    ((proof-in-allnc-elim-form)
     (let* ((op (proof-in-allnc-elim-form-to-op proof))
	    (op-proof (proof-to-soundness-proof-aux
		       op avar-or-ga-to-var avar-or-ga-to-mr-avar))
	    (arg (proof-in-allnc-elim-form-to-arg proof)))
       (mk-proof-in-elim-form op-proof arg)))
    (else (myerror "proof-to-soundness-proof-aux" "proof expected" proof))))

(define (axiom-to-soundness-proof aconst)
  (let ((name (aconst-to-name aconst)))
    (cond
     ((string=? "Ind" name)
      (apply all-formulas-to-mr-ind-proof (aconst-to-repro-data aconst)))
     ((string=? "Cases" name)
      (all-formula-to-mr-cases-proof (car (aconst-to-repro-data aconst))))
     ((string=? "GInd" name) (gind-aconst-to-mr-gind-proof aconst))
     ((string=? "Intro" name)
      (let* ((repro-data (aconst-to-repro-data aconst))
	     (number (car repro-data))
	     (idpc (cadr repro-data))
	     (idpc-name (idpredconst-to-name idpc)))
	(cond ;extra treatment for ;ExL, ExR, ExLT, ExRT, AndL and AndR
	 ((member idpc-name '("ExL" "ExLT"))
	  (let* ((cterms (idpredconst-to-cterms idpc))
		 (cterm (car cterms))
		 (exl-formula (make-exl (car (cterm-to-vars cterm))
					(cterm-to-formula cterm))))
	    (exl-formula-to-exl-intro-mr-proof exl-formula)))
	 ((member idpc-name '("ExR" "ExRT"))
	  (let* ((cterms (idpredconst-to-cterms idpc))
		 (cterm (car cterms))
		 (exr-formula (make-exr (car (cterm-to-vars cterm))
					(cterm-to-formula cterm))))
	    (exr-formula-to-exr-intro-mr-proof exr-formula)))
	 ((member idpc-name '("ExU" "ExUT"))
	  (let* ((cterms (idpredconst-to-cterms idpc))
		 (cterm (car cterms))
		 (exu-formula (make-exu (car (cterm-to-vars cterm))
					(cterm-to-formula cterm))))
	    (exu-formula-to-exu-intro-mr-proof exu-formula)))
	 ((string=? "AndL" idpc-name)
	  (let* ((cterms (idpredconst-to-cterms idpc))
		 (left-cterm (car cterms))
		 (right-cterm (cadr cterms))
		 (left (cterm-to-formula left-cterm))
		 (right (cterm-to-formula right-cterm))
		 (andl-formula (make-andl left right)))
	    (andl-formula-to-andl-intro-mr-proof andl-formula)))
	 ((string=? "AndR" idpc-name)
	  (let* ((cterms (idpredconst-to-cterms idpc))
		 (left-cterm (car cterms))
		 (right-cterm (cadr cterms))
		 (left (cterm-to-formula left-cterm))
		 (right (cterm-to-formula right-cterm))
		 (andr-formula (make-andr left right)))
	    (andr-formula-to-andr-intro-mr-proof andr-formula)))
	 (else (number-and-idpredconst-to-intro-mr-proof number idpc)))))
     ((string=? "Elim" name)
      (let* ((imp-formulas (aconst-to-repro-data aconst))
	     (imp-formula (car imp-formulas))
	     (prem (imp-form-to-premise imp-formula))
	     (concl (imp-form-to-conclusion imp-formula))
	     (idpc (predicate-form-to-predicate prem))
	     (idpc-name (idpredconst-to-name idpc)))
	(cond ;extra treatment for ExL, ExR, ExLT, ExRT, AndL, AndR
					;EqD, ExU, ExUT, AndU
	 ((member idpc-name '("ExL" "ExLT"))
	  (let* ((cterms (idpredconst-to-cterms idpc))
		 (cterm (car cterms))
		 (exl-formula (make-exl (car (cterm-to-vars cterm))
					(cterm-to-formula cterm))))
	    (exl-formula-and-concl-to-exl-elim-mr-proof exl-formula concl)))
	 ((member idpc-name '("ExR" "ExRT"))
	  (let* ((cterms (idpredconst-to-cterms idpc))
		 (cterm (car cterms))
		 (exr-formula (make-exr (car (cterm-to-vars cterm))
					(cterm-to-formula cterm))))
	    (exr-formula-and-concl-to-exr-elim-mr-proof exr-formula concl)))
	 ((string=? "AndL" idpc-name)
	  (let* ((cterms (idpredconst-to-cterms idpc))
		 (left-cterm (car cterms))
		 (right-cterm (cadr cterms))
		 (left (cterm-to-formula left-cterm))
		 (right (cterm-to-formula right-cterm))
		 (andl-formula (make-andl left right)))
	    (andl-formula-and-concl-to-andl-elim-mr-proof andl-formula concl)))
	 ((string=? "AndR" idpc-name)
	  (let* ((cterms (idpredconst-to-cterms idpc))
		 (left-cterm (car cterms))
		 (right-cterm (cadr cterms))
		 (left (cterm-to-formula left-cterm))
		 (right (cterm-to-formula right-cterm))
		 (andr-formula (make-andr left right)))
	    (andr-formula-and-concl-to-andr-elim-mr-proof andr-formula concl)))
	 ((string=? "EqD" idpc-name)
	  (eqd-elim-aconst-to-eqd-mr-elim-proof aconst))
	 ((member idpc-name '("ExU" "ExUT"))
	  (let* ((cterms (idpredconst-to-cterms idpc))
		 (cterm (car cterms))
		 (exu-formula (make-exu (car (cterm-to-vars cterm))
					(cterm-to-formula cterm))))
	    (exu-formula-and-concl-to-exu-elim-mr-proof exu-formula concl)))
	 ((string=? "AndU" idpc-name)
	  (let* ((cterms (idpredconst-to-cterms idpc))
		 (cterm1 (car cterms))
		 (cterm2 (cadr cterms))
		 (andu-formula
		  (make-andu (cterm-to-formula cterm1)
			     (cterm-to-formula cterm2))))
	    (andu-formula-and-concl-to-andu-elim-mr-proof andu-formula concl)))
	 (else (apply imp-formulas-to-mr-elim-proof imp-formulas)))))
     ((string=? "Closure" name)
      (let ((coidpc (predicate-form-to-predicate
		     (imp-form-to-premise
		      (allnc-form-to-final-kernel
		       (aconst-to-formula aconst))))))
	(coidpredconst-to-closure-mr-proof coidpc)))
     ((string=? "Gfp" name)
      (apply imp-formulas-to-mr-gfp-proof (aconst-to-repro-data aconst)))
     ((string=? "Ex-Intro" name)
      (ex-formula-to-ex-intro-mr-proof
       (car (aconst-to-repro-data aconst))))
     ((string=? "Ex-Elim" name)
      (apply ex-formula-and-concl-to-ex-elim-mr-proof
	     (aconst-to-repro-data aconst)))
     ((string=? "InhabTotal" name)
      (let* ((formula (aconst-to-formula aconst))
	     (arg (car (predicate-form-to-args formula)))
	     (type (term-to-type arg)))
	(type-to-inhabtotal-mr-proof type)))
     ((string=? "InhabTotalMR" name) (make-proof-in-aconst-form aconst))
     ((string=? "Exnc-Intro" name) ;obsolete
      (exnc-formula-to-exnc-intro-mr-proof
       (car (aconst-to-repro-data aconst))))
     ((string=? "Eq-Compat" name) ;obsolete
      (compat-aconst-to-mr-compat-proof aconst pvar-to-mr-pvar))
     (else (myerror "axiom-to-soundness-proof" "unexpected axiom" name)))))

(define (theorem-to-soundness-proof aconst)
  (let* ((thm-name (aconst-to-name aconst))
	 (proof (theorem-name-to-proof thm-name))
	 (tpsubst (aconst-to-tpsubst aconst))
	 (tsubst (list-transform-positive tpsubst
		   (lambda (x) (tvar-form? (car x)))))
	 (psubst (list-transform-positive tpsubst
		   (lambda (x) (pvar-form? (car x))))))
    (cond
     ((string=? "Id" thm-name)
      (let* ((pvar (predicate-form-to-predicate
		    (imp-impnc-all-allnc-form-to-final-conclusion
		     (aconst-to-uninst-formula aconst))))
	     (cterm (let ((info (assoc pvar psubst)))
		      (if info
			  (cadr info)
			  (predicate-to-cterm pvar))))
	     (cterm-formula (cterm-to-formula cterm))
	     (et-type (formula-to-et-type cterm-formula)))
	(if
	 (nulltype? et-type)
	 (let* ((mr-formula (real-and-formula-to-mr-formula
			     'eps cterm-formula))
		(mr-cterm (make-cterm mr-formula))
		(mr-tpsubst (append tsubst (list (list pvar mr-cterm))))
		(orig-aconst (theorem-name-to-aconst thm-name))
		(mr-aconst (aconst-substitute orig-aconst mr-tpsubst)))
	   (make-proof-in-aconst-form mr-aconst))
					;et-type not nulltype
	 (let* ((mr-var (type-to-new-partial-var et-type))
		(mr-formula (real-and-formula-to-mr-formula
			     (make-term-in-var-form mr-var) cterm-formula))
		(mr-cterm (make-cterm mr-formula))
		(mr-tpsubst (append tsubst (list (list pvar mr-cterm))))
		(orig-aconst (theorem-name-to-aconst thm-name))
		(mr-aconst (aconst-substitute orig-aconst mr-tpsubst))
					;allnc xs(a mr A -> a mr A)
		(mr-aconst-formula (aconst-to-formula mr-aconst))
		(vars (all-allnc-form-to-vars mr-aconst-formula)))
	   (if (equal? vars (append (remove mr-var vars) (list mr-var)))
	       (make-proof-in-aconst-form mr-aconst)
	       (let ((elim-proof
		      (apply
		       mk-proof-in-elim-form
		       (make-proof-in-aconst-form mr-aconst)
		       (map make-term-in-var-form vars))))
		 (apply mk-proof-in-nc-intro-form
			(append (remove mr-var vars)
				(list mr-var elim-proof)))))))))
     ((member thm-name (list "EqDCompatRev" "EqDCompat"))
      (let* ((pvar (predicate-form-to-predicate
		    (imp-impnc-all-allnc-form-to-final-conclusion
		     (aconst-to-uninst-formula aconst))))
	     (cterm (let ((info (assoc pvar psubst)))
		      (if info
			  (cadr info)
			  (predicate-to-cterm pvar))))
	     (cterm-vars (cterm-to-vars cterm))
	     (cterm-formula (cterm-to-formula cterm))
	     (et-type (formula-to-et-type cterm-formula)))
	(if
	 (nulltype? et-type)
	 (let* ((mr-formula (real-and-formula-to-mr-formula
			     'eps cterm-formula))
		(mr-cterm
		 (apply make-cterm (append cterm-vars (list mr-formula))))
		(mr-tpsubst (append tsubst (list (list pvar mr-cterm))))
		(orig-aconst (theorem-name-to-aconst thm-name))
		(mr-aconst (aconst-substitute orig-aconst mr-tpsubst)))
	   (make-proof-in-aconst-form mr-aconst))
					;et-type not nulltype
	 (let* ((mr-var (type-to-new-partial-var et-type))
		(mr-formula (real-and-formula-to-mr-formula
			     (make-term-in-var-form mr-var) cterm-formula))
		(mr-cterm
		 (apply make-cterm (append cterm-vars (list mr-formula))))
		(mr-tpsubst (append tsubst (list (list pvar mr-cterm))))
		(orig-aconst (theorem-name-to-aconst thm-name))
		(mr-aconst (aconst-substitute orig-aconst mr-tpsubst))
					;allnc xs,n,m(n=m -> a mr A(m) ->
					;a mr A(n)) or conversely
		(mr-aconst-formula (aconst-to-formula mr-aconst))
		(vars (all-allnc-form-to-vars mr-aconst-formula))
		(eqd-hyp ;n=m
		 (car (imp-impnc-form-to-premises
		       (all-allnc-form-to-final-kernel mr-aconst-formula))))
		(u (formula-to-new-avar eqd-hyp))
		(elim-proof
		 (apply mk-proof-in-elim-form
			(make-proof-in-aconst-form mr-aconst)
			(append (map make-term-in-var-form vars)
				(list (make-proof-in-avar-form u))))))
	   (apply mk-proof-in-nc-intro-form
		  (append (remove mr-var vars)
			  (list u mr-var elim-proof)))))))
     (else
      (let ((info (assoc (string-append thm-name "Sound") THEOREMS)))
	(if info
	    (make-proof-in-aconst-form (cadr info))
	    (let* ((inst-proof (theorem-aconst-to-inst-proof aconst))
		   (free (formula-to-free (proof-to-formula inst-proof)))
		   (closed-inst-proof
		    (apply mk-proof-in-nc-intro-form
			   (append free (list inst-proof)))))
	      (proof-to-soundness-proof closed-inst-proof))))))))

(define (global-assumption-to-soundness-proof aconst avar-or-ga-to-mr-avar)
  (let* ((name (aconst-to-name aconst))
	 (info (assoc name GLOBAL-ASSUMPTIONS)))
    (if info
	(cond
	 ((or (string=? "Efq" name) (string=? "EfqLog" name))
	  (efq-ga-to-mr-efq-ga-proof aconst))
					;the next item is obsolete
	 ((or (and (<= (string-length "Eq-Compat-Rev") (string-length name))
		   (string=? (substring name 0 (string-length "Eq-Compat-Rev"))
			     "Eq-Compat-Rev"))
	      (and (<= (string-length "Compat-Rev") (string-length name))
		   (string=? (substring name 0 (string-length "Compat-Rev"))
			     "Compat-Rev"))
	      (and (<= (string-length "Compat") (string-length name))
		   (string=? (substring name 0 (string-length "Compat"))
			     "Compat")))
	  (compat-aconst-to-mr-compat-proof aconst))
	 (else (let ((mr-avar (avar-or-ga-to-mr-avar aconst)))
		 (make-proof-in-avar-form mr-avar))))
	(myerror "global-assumption-to-soundness-proof"
		 "global assumption expected" name))))

(define (proof-to-soundness-formula proof)
  (real-and-formula-to-mr-formula
   (proof-to-extracted-term proof)
   (proof-to-formula proof)))

