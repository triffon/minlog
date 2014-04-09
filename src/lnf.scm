;; $Id: lnf.scm 2674 2014-01-08 10:00:51Z schwicht $

;; (proceed thm1 ...) searches for a proof of the goal from the present
;; hypotheses plus the optionally provided theorems, as long as this can
;; be done uniquely, i.e., only one of all the given facts is applicable
;; (tested with match).  If there is a choice, proceed stops.

;; Notice that proceed may well lead into dead ends: the allegedly
;; unique way to preceed may have a better alternative by using a
;; not explicitely listed theorem or global assumption.

;; Notice also that proceed may create infinite loops, e.g. for
;; (A -> A) -> A.

(define (proceed . names)
  (if
   (null? (pproof-state-to-num-goals))
   (begin (display-comment "  Proof finished.")
	  (if COMMENT-FLAG (newline)))
   (let* ((num-goals (pproof-state-to-num-goals))
	  (proof (pproof-state-to-proof))
	  (num-goal (car num-goals))
	  (number (num-goal-to-number num-goal))
	  (goal (num-goal-to-goal num-goal))
	  (context (goal-to-context goal))
	  (sig-vars (context-to-vars context))
	  (avars (context-to-avars context))
	  (goal-formula (goal-to-formula goal))
	  (hypname-info (num-goal-to-hypname-info num-goal))
	  (indices (hypname-info-to-indices hypname-info))
	  (labeled-avar-hyps
	   (do ((l avars (cdr l))
		(i 1 (+ 1 i))
		(res '() (let* ((avar (car l))
				(avar-proof (make-proof-in-avar-form avar))
				(info (member i indices))
				(string (if info
					    (index-and-hypname-info-to-name
					     i hypname-info)
					    (number-to-string i))))
			   (cons (list string avar-proof) res))))
	       ((null? l) (reverse res))))
	  (labeled-hyps
	   (append
	    labeled-avar-hyps
	    (map (lambda (name)
		   (cond
		    ((not (string? name))
		     (myerror "proceed: string expected" name))
		    ((string=? "Truth-Axiom" name)
		     (list name (make-proof-in-aconst-form truth-aconst)))
		    ((assoc name THEOREMS)
		     (list name (theorem-name-to-proof name)))
		    ((assoc name GLOBAL-ASSUMPTIONS)
		     (list name (make-proof-in-aconst-form
				 (global-assumption-name-to-aconst name))))
		    (else (myerror "proceed: name of theorem or"
				   "global assumption expected" name))))
		 names)))
	  (labels (map car labeled-hyps))
	  (hyps (map cadr labeled-hyps))
	  (hyp-formulas (map proof-to-formula hyps))
	  (sig-tvars-and-sig-vars-list
	   (map (lambda (labeled-hyp)
		  (if (assoc (car labeled-hyp)
			     (append THEOREMS GLOBAL-ASSUMPTIONS))
		      sig-vars
		      (append (formula-to-tvars
			       (proof-to-formula (cadr labeled-hyp)))
			      sig-vars)))
		labeled-hyps))
 	  (match-results
  	   (map  (lambda (x y)
 		   (let ((result
 			  (fla-and-sig-tvars-and-vars-and-goal-fla-to-use-data
 			   x y goal-formula)))
 		     (if result
 			 (let ((x-list (car result))
 			       (vars (cadr result)) ;we omit the alist (cddr)
 			       (toinst (cadddr result)))
 			   (list x-list vars toinst))
 			 #f)))
 		hyp-formulas sig-tvars-and-sig-vars-list))
	  (labeled-match-results (map list labels match-results))
	  (labeled-hits
	   (list-transform-positive labeled-match-results
	     (lambda (x) (pair? (cadr x))))))
     (cond
      ((= 1 (length labeled-hits))
       (let* ((labeled-hit (car labeled-hits))
	      (label (car labeled-hit))
	      (x-list-and-vars-and-alist-and-toinst (cadr labeled-hit))
	      (x-list (car x-list-and-vars-and-alist-and-toinst))
	      (vars (cadr x-list-and-vars-and-alist-and-toinst))
	      (toinst (caddr x-list-and-vars-and-alist-and-toinst))
	      (x (cadr (assoc label labeled-hyps)))
	      (types
	       (let ((info1 (assoc label THEOREMS))
		     (info2 (assoc label GLOBAL-ASSUMPTIONS))
		     (tsubst (list-transform-positive toinst
			       (lambda (x) (tvar-form? (car x))))))
		 (if (and (or info1 info2) (pair? tsubst)) ;else '()
		     (let* ((aconst (if
				     info1
				     (theorem-name-to-aconst label)
				     (global-assumption-name-to-aconst label)))
			    (fla (aconst-to-formula aconst))
			    (tvars (formula-to-tvars fla)))
		       (map (lambda (tvar) (type-substitute tvar tsubst))
			    tvars))
		     '()))))
	 (if ;no terms required
	  (null? vars)
	  (begin
	    (if COMMENT-FLAG (newline))
	    (display-comment "proceed: (use-with " label " ...)")
	    (if COMMENT-FLAG (newline))
	    (apply use-with (cons x (append types x-list)))
	    (if
	     (null? (pproof-state-to-num-goals))
	     *the-non-printing-object*
	     (let* ((num-goals (pproof-state-to-num-goals))
		    (num-goal (car num-goals))
		    (goal (num-goal-to-goal num-goal))
		    (goal-formula (goal-to-formula goal)))
	       (if (or (prime-form? goal-formula)
		       (and-form? goal-formula)
		       (ex-form? goal-formula))
		   (apply proceed names)
		   (begin (if COMMENT-FLAG (newline))
			  (display-comment "proceed: (strip)")
			  (if COMMENT-FLAG (newline))
			  (strip)
			  (apply proceed names))))))
	  (begin (if COMMENT-FLAG (newline))
		 (display-comment
		  "proceed: terms required for hypothesis " label)
		 (if COMMENT-FLAG (newline))))))
      ((= 0 (length labeled-hits))
       (if
	(and-form? goal-formula)
	(begin (if COMMENT-FLAG (newline))
	       (display-comment "proceed: (split)")
	       (if COMMENT-FLAG (newline))
	       (split)
	       (apply proceed names))
	(if (or (prime-form? goal-formula) (ex-form? goal-formula))
	    (begin (display-comment "no (more) usable hypotheses")
		   (if COMMENT-FLAG (newline)))
	    (begin (if COMMENT-FLAG (newline))
		   (display-comment "proceed: (strip)")
		   (if COMMENT-FLAG (newline))
		   (strip) (apply proceed names)))))
      (else
       (let ((labeled-hits-not-requiring-terms-and-not-creating-goals
	      (list-transform-positive labeled-hits
		(lambda (labeled-hit)
		  (and (pair? (cadr labeled-hit))
		       (let* ((x-list-and-vars-and-alist-and-toinst (cadr labeled-hit))
			      (x-list (car x-list-and-vars-and-alist-and-toinst))
			      (vars (cadr x-list-and-vars-and-alist-and-toinst)))
			 (and (null? vars)
			      (not (member DEFAULT-GOAL-NAME x-list)))))))))
	 (if
	  (pair? labeled-hits-not-requiring-terms-and-not-creating-goals)
	  (let*  ((labeled-hit
		   (car
		    labeled-hits-not-requiring-terms-and-not-creating-goals))
		  (label (car labeled-hit))
		  (x-list-and-vars-and-alist-and-toinst (cadr labeled-hit))
		  (x-list (car x-list-and-vars-and-alist-and-toinst))
		  (toinst (caddr x-list-and-vars-and-alist-and-toinst))
		  (x (cadr (assoc label labeled-hyps)))
		  (types
		   (let ((info1 (assoc label THEOREMS))
			 (info2 (assoc label GLOBAL-ASSUMPTIONS))
			 (tsubst (list-transform-positive toinst
				   (lambda (x) (tvar-form? (car x))))))
		     (if (and (or info1 info2) (pair? tsubst)) ;else '()
			 (let* ((aconst (if
					 info1
					 (theorem-name-to-aconst label)
					 (global-assumption-name-to-aconst
					  label)))
				(fla (aconst-to-formula aconst))
				(tvars (formula-to-tvars fla)))
			   (map (lambda (tvar) (type-substitute tvar tsubst))
				tvars))
			 '()))))
	    (if COMMENT-FLAG (newline))
	    (display-comment "proceed: (use-with " label ")")
	    (if COMMENT-FLAG (newline))
	    (apply use-with (cons x (append types x-list)))
	    (if (null? (pproof-state-to-num-goals))
		*the-non-printing-object*
		(let* ((num-goals (pproof-state-to-num-goals))
		       (num-goal (car num-goals))
		       (goal (num-goal-to-goal num-goal))
		       (goal-formula (goal-to-formula goal)))
		  (if (or (prime-form? goal-formula)
			  (and-form? goal-formula)
			  (ex-form? goal-formula))
		      (apply proceed names)
		      (begin (if COMMENT-FLAG (newline))
			     (display-comment "proceed: (strip)")
			     (if COMMENT-FLAG (newline))
			     (strip)
			     (apply proceed names))))))
	  (begin (if COMMENT-FLAG (newline))
		 (apply display-comment
			(cons "proceed: more than one usable hypothesis: "
			      (map (lambda (x) (string-append (car x) " "))
				   labeled-hits)))
		 (if COMMENT-FLAG (newline))))))))))



