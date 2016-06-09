;; $Id: atr.scm 2692 2014-01-24 09:20:17Z schwicht $

;; 17. A-translation
;; =================

;; Based on Berger, Buchholz, Schwichtenberg: Refined program extraction
;; from classical proofs, APAL 114 (2002), 3--25

;; A formula is relevant if it ends with bot.

(define (atr-relevant? formula)
  (case (tag formula)
    ((atom) #f)
    ((predicate) (formula=? formula falsity-log))
    ((imp impnc) (atr-relevant? (imp-impnc-form-to-conclusion formula)))
    ((all allnc) (atr-relevant? (all-allnc-form-to-kernel formula)))
    ((and tensor ex exca excl) #f)
    (else (myerror "atr-relevant?" "formula expected" formula))))

;; Definite and goal formulas are defined by a simultaneous recursion.

(define (atr-definite? formula)
  (case (tag formula)
    ((atom predicate) #t)
    ((imp impnc)
     (let ((prem (imp-impnc-form-to-premise formula))
	   (concl (imp-impnc-form-to-conclusion formula)))
       (and (atr-definite? concl)
	    (atr-goal? prem)
	    (or (atr-relevant? concl) (not (atr-relevant? prem))))))
    ((all allnc) (atr-definite? (all-allnc-form-to-kernel formula)))
    ((and tensor ex exca excl) #f)
    (else (myerror "atr-definite?" "formula expected" formula))))

(define (atr-goal? formula)
  (case (tag formula)
    ((atom predicate) #t)
    ((imp impnc)
     (let ((prem (imp-impnc-form-to-premise formula))
	   (concl (imp-impnc-form-to-conclusion formula)))
       (and (atr-goal? concl)
	    (atr-definite? prem)
	    (or (atr-relevant? prem) (quant-free? prem)))))
    ((all allnc)
     (let ((kernel (all-allnc-form-to-kernel formula)))
       (and (atr-goal? kernel) (not (atr-relevant? kernel)))))
    ((and tensor ex exca excl) #f)
    (else (myerror "atr-goal?" "formula expected" formula))))

;; and-to-atom-proof: boole1 & boole2 -> AndConst boole1 boole2
;; atom-to-and-proof: AndConst boole1 boole2 -> boole1 & boole2

(define and-to-atom-proof
  (let ((p1 (type-to-new-var (make-alg "boole")))
	(p2 (type-to-new-var (make-alg "boole"))))
    (make-proof-in-all-intro-form
     p1 (mk-proof-in-elim-form
	 (make-proof-in-aconst-form
	  (all-formula-to-cases-aconst
	   (pf "all boole1,boole2.boole1 & boole2 -> AndConst boole1 boole2")))
	 (make-term-in-var-form p1)
	 (make-proof-in-all-intro-form
	  p2 (mk-proof-in-elim-form
	      (make-proof-in-aconst-form
	       (all-formula-to-cases-aconst
		(pf "all boole2.T & boole2 -> AndConst True boole2")))
	      (make-term-in-var-form p2)
	      (mk-proof-in-intro-form
	       (formula-to-new-avar (pf "T & T"))
	       (make-proof-in-aconst-form truth-aconst))
	      (let ((u (formula-to-new-avar (pf "T & F"))))
		(mk-proof-in-intro-form
		 u (make-proof-in-and-elim-right-form
		    (make-proof-in-avar-form u))))))
	 (make-proof-in-all-intro-form
	  p2 (mk-proof-in-elim-form
	      (make-proof-in-aconst-form
	       (all-formula-to-cases-aconst
		(pf "all boole2.(F & boole2) -> AndConst False boole2")))
	      (make-term-in-var-form p2)
	      (let ((u (formula-to-new-avar (pf "F & T"))))
		(mk-proof-in-intro-form
		 u (make-proof-in-and-elim-left-form
		    (make-proof-in-avar-form u))))
	      (let ((u (formula-to-new-avar (pf "F & F"))))
		(mk-proof-in-intro-form
		 u (make-proof-in-and-elim-left-form
		    (make-proof-in-avar-form u))))))))))

(define atom-to-and-proof
  (let ((p1 (type-to-new-var (make-alg "boole")))
	(p2 (type-to-new-var (make-alg "boole"))))
    (make-proof-in-all-intro-form
     p1 (mk-proof-in-elim-form
	 (make-proof-in-aconst-form
	  (all-formula-to-cases-aconst
	   (pf "all boole1,boole2.AndConst boole1 boole2 -> boole1 & boole2")))
	 (make-term-in-var-form p1)
	 (make-proof-in-all-intro-form
	  p2 (mk-proof-in-elim-form
	      (make-proof-in-aconst-form
	       (all-formula-to-cases-aconst
		(pf "all boole2.AndConst True boole2 -> T & boole2")))
	      (make-term-in-var-form p2)
	      (make-proof-in-imp-intro-form
	       (formula-to-new-avar (pf "T"))
	       (make-proof-in-and-intro-form
		(make-proof-in-aconst-form truth-aconst)
		(make-proof-in-aconst-form truth-aconst)))
	      (let ((u (formula-to-new-avar (pf "F"))))
		(make-proof-in-imp-intro-form
		 u (make-proof-in-and-intro-form
		    (make-proof-in-aconst-form truth-aconst)
		    (make-proof-in-avar-form u))))))
	 (make-proof-in-all-intro-form
	  p2 (mk-proof-in-elim-form
	      (make-proof-in-aconst-form
	       (all-formula-to-cases-aconst
		(pf "all boole2.AndConst False boole2 -> F & boole2")))
	      (make-term-in-var-form p2)
	      (let ((u (formula-to-new-avar (pf "F"))))
		(make-proof-in-imp-intro-form
		 u (make-proof-in-and-intro-form
		    (make-proof-in-avar-form u)
		    (make-proof-in-aconst-form truth-aconst))))
	      (let ((u (formula-to-new-avar (pf "F"))))
		(make-proof-in-imp-intro-form
		 u (make-proof-in-and-intro-form
		    (make-proof-in-avar-form u)
		    (make-proof-in-avar-form u))))))))))

;; qf-to-atom-imp-qf-proof: atom(r_C) -> C
;; qf-to-qf-imp-atom-proof: C -> atom(r_C)

(define (qf-to-atom-imp-qf-proof formula)
  (case (tag formula)
    ((atom)
     (let ((u (formula-to-new-avar formula)))
       (make-proof-in-imp-intro-form u (make-proof-in-avar-form u))))
    ((predicate)
     (myerror "qf-to-atom-imp-qf-proof" "atom expected" formula))
    ((imp)
     (let* ((prem (imp-form-to-premise formula))
	    (concl (imp-form-to-conclusion formula))
	    (term1 (qf-to-term prem))
	    (term2 (qf-to-term concl))
	    (term (mk-term-in-app-form
		   (make-term-in-const-form imp-const) term1 term2))
	    (atom (make-atomic-formula term))
	    (u1 (formula-to-new-avar prem))
	    (u (formula-to-new-avar atom)))
       (mk-proof-in-intro-form
	u u1 (make-proof-in-imp-elim-form
	      (qf-to-atom-imp-qf-proof concl)
	      (mk-proof-in-elim-form
	       atom-to-imp-proof
	       term1 term2
	       (make-proof-in-avar-form u)
	       (make-proof-in-imp-elim-form
		(qf-to-qf-imp-atom-proof prem)
		(make-proof-in-avar-form u1)))))))
    ((and)
     (let* ((left (and-form-to-left formula))
	    (right (and-form-to-right formula))
	    (term1 (qf-to-term left))
	    (term2 (qf-to-term right))
	    (term (mk-term-in-app-form
		   (make-term-in-const-form and-const) term1 term2))
	    (atom (make-atomic-formula term))
	    (u (formula-to-new-avar atom))
	    (and-term-proof
	     (mk-proof-in-elim-form
	      atom-to-and-proof term1 term2 (make-proof-in-avar-form u))))
       (make-proof-in-imp-intro-form
	u (make-proof-in-and-intro-form
	   (make-proof-in-imp-elim-form
	    (qf-to-atom-imp-qf-proof left)
	    (make-proof-in-and-elim-left-form and-term-proof))
	   (make-proof-in-imp-elim-form
	    (qf-to-atom-imp-qf-proof right)
	    (make-proof-in-and-elim-right-form and-term-proof))))))
    (else (myerror "qf-to-atom-imp-qf-proof" "quantifier free formula expected"
		   formula))))

(define (qf-to-qf-imp-atom-proof formula)
  (case (tag formula)
    ((atom)
     (let ((u (formula-to-new-avar formula)))
       (make-proof-in-imp-intro-form u (make-proof-in-avar-form u))))
    ((predicate)
     (myerror "qf-to-qf-imp-atom-proof" "atom expected" formula))
    ((imp)
     (let* ((prem (imp-form-to-premise formula))
	    (concl (imp-form-to-conclusion formula))
	    (term1 (qf-to-term prem))
	    (term2 (qf-to-term concl))
	    (atom1 (make-atomic-formula term1))
	    (atom2 (make-atomic-formula term2))
	    (v1 (formula-to-new-avar atom1))
	    (u (formula-to-new-avar formula)))
       (make-proof-in-imp-intro-form
	u (mk-proof-in-elim-form
	   imp-to-atom-proof
	   term1 term2
	   (make-proof-in-imp-intro-form
	    v1 (make-proof-in-imp-elim-form
		(qf-to-qf-imp-atom-proof concl)
		(make-proof-in-imp-elim-form
		 (make-proof-in-avar-form u)
		 (make-proof-in-imp-elim-form
		  (qf-to-atom-imp-qf-proof prem)
		  (make-proof-in-avar-form v1)))))))))
    ((and)
     (let* ((left (and-form-to-left formula))
	    (right (and-form-to-right formula))
	    (term1 (qf-to-term left))
	    (term2 (qf-to-term right))
	    (atom1 (make-atomic-formula term1))
	    (atom2 (make-atomic-formula term2))
	    (u (formula-to-new-avar formula)))
       (make-proof-in-imp-intro-form
	u (mk-proof-in-elim-form
	   and-to-atom-proof
	   term1 term2
	   (make-proof-in-and-intro-form
	    (make-proof-in-imp-elim-form
	     (qf-to-qf-imp-atom-proof left)
	     (make-proof-in-and-elim-left-form
	      (make-proof-in-avar-form u)))
	    (make-proof-in-imp-elim-form
	     (qf-to-qf-imp-atom-proof right)
	     (make-proof-in-and-elim-right-form
	      (make-proof-in-avar-form u))))))))
    (else (myerror "qf-to-qf-imp-atom-proof" "quantifier free formula expected"
		   formula))))

;; qf-to-qf-cases-proof: (C -> bot) -> ((C -> F) -> bot) -> bot

(define (qf-to-qf-cases-proof formula)
  (let* ((neg-formula (make-imp formula falsity))
	 (u1 (formula-to-new-avar (make-imp formula falsity-log)))
	 (u2 (formula-to-new-avar (make-imp neg-formula falsity-log)))
	 (term (qf-to-term formula))
	 (atom (make-atomic-formula term))
	 (v1 (formula-to-new-avar atom))
	 (v2 (formula-to-new-avar (make-imp atom falsity)))
	 (w (formula-to-new-avar formula))
	 (pvar (predicate-form-to-predicate
		(imp-form-to-final-conclusion
		 (all-form-to-final-kernel
		  (proof-to-formula dec-cases-proof)))))
	 (cterm (make-cterm
		 (type-to-new-partial-var (make-alg "boole")) falsity-log))
	 (subst-dec-cases-proof (proof-subst dec-cases-proof pvar cterm)))
    (mk-proof-in-intro-form
     u1 u2 (mk-proof-in-elim-form
	    subst-dec-cases-proof
	    term
	    (make-proof-in-imp-intro-form
	     v1 (make-proof-in-imp-elim-form
		 (make-proof-in-avar-form u1)
		 (make-proof-in-imp-elim-form
		  (qf-to-atom-imp-qf-proof formula)
		  (make-proof-in-avar-form v1))))
	    (make-proof-in-imp-intro-form
	     v2 (make-proof-in-imp-elim-form
		 (make-proof-in-avar-form u2)
		 (make-proof-in-imp-intro-form
		  w (make-proof-in-imp-elim-form
		     (make-proof-in-avar-form v2)
		     (make-proof-in-imp-elim-form
		      (qf-to-qf-imp-atom-proof formula)
		      (make-proof-in-avar-form w))))))))))

;; We construct proofs from F -> bot:
;; M_D: D^F -> D
;; H_G: G -> (G^F -> bot) -> bot
;; N_R: ((R^F -> F) -> bot) -> R   for R relevant and definite
;; K_I: I -> I^F                   for I irrelevant and goal

(define F-to-bot-avar (formula-to-new-avar (make-imp falsity falsity-log)))
(define F-cterm (make-cterm falsity))

(define (atr-rel-definite-proof formula)
  (if
   (atr-definite? formula)
   (if
    (atr-relevant? formula)
    (case (tag formula)
      ((predicate) ;falsity-log
       (let ((u (formula-to-new-avar
		 (mk-imp (mk-imp falsity falsity) falsity-log)))
	     (v (formula-to-new-avar falsity)))
	 (make-proof-in-imp-intro-form
	  u (make-proof-in-imp-elim-form
	     (make-proof-in-avar-form u)
	     (make-proof-in-imp-intro-form
	      v (make-proof-in-avar-form v))))))
      ((imp)
       (let* ((prem (imp-form-to-premise formula))
	      (concl (imp-form-to-conclusion formula))
	      (prem-F (formula-subst prem falsity-log-pvar F-cterm))
	      (concl-F (formula-subst concl falsity-log-pvar F-cterm))
	      (u1 (formula-to-new-avar prem))
	      (u2 (formula-to-new-avar
		   (mk-imp (mk-neg (mk-imp prem-F concl-F)) falsity-log)))
	      (u3 (formula-to-new-avar (mk-neg concl-F)))
	      (u4 (formula-to-new-avar (mk-imp prem-F concl-F)))
	      (u5 (formula-to-new-avar prem-F)))
	 (mk-proof-in-intro-form
	  u2 u1 (make-proof-in-imp-elim-form
		 (atr-rel-definite-proof concl)
		 (make-proof-in-imp-intro-form
		  u3 (mk-proof-in-elim-form
		      (atr-arb-goal-proof prem)
		      (make-proof-in-avar-form u1)
		      (make-proof-in-imp-intro-form
		       u5 (make-proof-in-imp-elim-form
			   (make-proof-in-avar-form u2)
			   (make-proof-in-imp-intro-form
			    u4 (make-proof-in-imp-elim-form
				(make-proof-in-avar-form u3)
				(make-proof-in-imp-elim-form
				 (make-proof-in-avar-form u4)
				 (make-proof-in-avar-form u5))))))))))))
      ((impnc)
       (let* ((prem (impnc-form-to-premise formula))
	      (concl (impnc-form-to-conclusion formula))
	      (prem-F (formula-subst prem falsity-log-pvar F-cterm))
	      (concl-F (formula-subst concl falsity-log-pvar F-cterm))
	      (u1 (formula-to-new-avar prem))
	      (u2 (formula-to-new-avar
		   (mk-imp (mk-neg (mk-impnc prem-F concl-F)) falsity-log)))
	      (u3 (formula-to-new-avar (mk-neg concl-F)))
	      (u4 (formula-to-new-avar (mk-impnc prem-F concl-F)))
	      (u5 (formula-to-new-avar prem-F)))
	 (make-proof-in-imp-intro-form
	  u2 (make-proof-in-impnc-intro-form
	      u1 (make-proof-in-imp-elim-form
		  (atr-rel-definite-proof concl)
		  (make-proof-in-imp-intro-form
		   u3 (mk-proof-in-elim-form
		       (atr-arb-goal-proof prem)
		       (make-proof-in-avar-form u1)
		       (make-proof-in-imp-intro-form
			u5 (make-proof-in-imp-elim-form
			    (make-proof-in-avar-form u2)
			    (make-proof-in-imp-intro-form
			     u4 (make-proof-in-imp-elim-form
				 (make-proof-in-avar-form u3)
				 (make-proof-in-impnc-elim-form
				  (make-proof-in-avar-form u4)
				  (make-proof-in-avar-form u5)))))))))))))
      ((all)
       (let* ((var (all-form-to-var formula))
	      (kernel (all-form-to-kernel formula))
	      (kernel-F (formula-subst kernel falsity-log-pvar F-cterm))
	      (u2 (formula-to-new-avar
		   (mk-imp (mk-neg (mk-all var kernel-F)) falsity-log)))
	      (u3 (formula-to-new-avar (mk-neg kernel-F)))
	      (u4 (formula-to-new-avar (mk-all var kernel-F))))
	 (mk-proof-in-intro-form
	  u2 var (make-proof-in-imp-elim-form
		  (atr-rel-definite-proof kernel)
		  (make-proof-in-imp-intro-form
		   u3 (make-proof-in-imp-elim-form
		       (make-proof-in-avar-form u2)
		       (make-proof-in-imp-intro-form
			u4 (make-proof-in-imp-elim-form
			    (make-proof-in-avar-form u3)
			    (make-proof-in-all-elim-form
			     (make-proof-in-avar-form u4)
			     (make-term-in-var-form var))))))))))
      ((allnc)
       (let* ((var (allnc-form-to-var formula))
	      (kernel (allnc-form-to-kernel formula))
	      (kernel-F (formula-subst kernel falsity-log-pvar F-cterm))
	      (u2 (formula-to-new-avar
		   (mk-imp (mk-neg (mk-allnc var kernel-F)) falsity-log)))
	      (u3 (formula-to-new-avar (mk-neg kernel-F)))
	      (u4 (formula-to-new-avar (mk-allnc var kernel-F))))
	 (mk-proof-in-intro-form
	  u2 var (make-proof-in-imp-elim-form
		  (atr-rel-definite-proof kernel)
		  (make-proof-in-imp-intro-form
		   u3 (make-proof-in-imp-elim-form
		       (make-proof-in-avar-form u2)
		       (make-proof-in-imp-intro-form
			u4 (make-proof-in-imp-elim-form
			    (make-proof-in-avar-form u3)
			    (make-proof-in-allnc-elim-form
			     (make-proof-in-avar-form u4)
			     (make-term-in-var-form var))))))))))
      ((and tensor ex exca excl)
       (myerror "atr-rel-definite-proof" "unexpected formula"
		formula))
      (else (myerror "atr-rel-definite-proof" "formula expected" formula)))
    (myerror "atr-rel-definite-proof" "relevant formula expected"
	     formula))
   (myerror "atr-rel-definite-proof" "definite formula expected" formula)))

(define (atr-arb-definite-proof formula)
  (if
   (atr-definite? formula)
   (if
    (atr-relevant? formula)
    (let* ((formula-F (formula-subst formula falsity-log-pvar F-cterm))
	   (u1 (formula-to-new-avar (mk-neg formula-F)))
	   (u2 (formula-to-new-avar formula-F)))
      (make-proof-in-imp-intro-form
       u2 (make-proof-in-imp-elim-form
	   (atr-rel-definite-proof formula)
	   (make-proof-in-imp-intro-form
	    u1 (make-proof-in-imp-elim-form
		(make-proof-in-avar-form F-to-bot-avar)
		(make-proof-in-imp-elim-form
		 (make-proof-in-avar-form u1)
		 (make-proof-in-avar-form u2)))))))
    (case (tag formula)
      ((atom predicate)
       (let ((u (formula-to-new-avar formula)))
	 (make-proof-in-imp-intro-form
	  u (make-proof-in-avar-form u))))
      ((imp)
       (let* ((prem (imp-form-to-premise formula)) ;irrelevant
	      (concl (imp-form-to-conclusion formula)) ;also irrelevant
	      (formula-F (formula-subst formula falsity-log-pvar F-cterm))
	      (u1 (formula-to-new-avar formula-F))
	      (u2 (formula-to-new-avar prem)))
	 (mk-proof-in-intro-form
	  u1 u2 (make-proof-in-imp-elim-form
		 (atr-arb-definite-proof concl)
		 (make-proof-in-imp-elim-form
		  (make-proof-in-avar-form u1)
		  (make-proof-in-imp-elim-form
		   (atr-irrel-goal-proof prem)
		   (make-proof-in-avar-form u2)))))))
      ((impnc)
       (let* ((prem (impnc-form-to-premise formula)) ;irrelevant
	      (concl (impnc-form-to-conclusion formula)) ;also irrelevant
	      (formula-F (formula-subst formula falsity-log-pvar F-cterm))
	      (u1 (formula-to-new-avar formula-F))
	      (u2 (formula-to-new-avar prem)))
	 (make-proof-in-imp-intro-form
	  u1 (make-proof-in-impnc-intro-form
	      u2 (make-proof-in-imp-elim-form
		  (atr-arb-definite-proof concl)
		  (make-proof-in-impnc-elim-form
		   (make-proof-in-avar-form u1)
		   (make-proof-in-imp-elim-form
		    (atr-irrel-goal-proof prem)
		    (make-proof-in-avar-form u2))))))))
      ((all)
       (let* ((var (all-form-to-var formula))
	      (kernel (all-form-to-kernel formula))
	      (formula-F (formula-subst formula falsity-log-pvar F-cterm))
	      (u (formula-to-new-avar formula-F)))
	 (mk-proof-in-intro-form
	  u var (make-proof-in-imp-elim-form
		 (atr-arb-definite-proof kernel)
		 (make-proof-in-all-elim-form
		  (make-proof-in-avar-form u)
		  (make-term-in-var-form var))))))
      ((allnc)
       (let* ((var (allnc-form-to-var formula))
	      (kernel (allnc-form-to-kernel formula))
	      (formula-F (formula-subst formula falsity-log-pvar F-cterm))
	      (u (formula-to-new-avar formula-F)))
	 (mk-proof-in-nc-intro-form
	  u var (make-proof-in-imp-elim-form
		 (atr-arb-definite-proof kernel)
		 (make-proof-in-allnc-elim-form
		  (make-proof-in-avar-form u)
		  (make-term-in-var-form var))))))
      ((and tensor ex exca excl)
       (myerror "atr-arb-definite-proof" "unexpected formula"
		formula))
      (else (myerror "atr-arb-definite-proof" "formula expected" formula))))
   (myerror "atr-arb-definite-proof" "definite formula expected" formula)))

(define (atr-irrel-goal-proof formula)
  (if
   (atr-goal? formula)
   (if
    (atr-relevant? formula)
    (myerror "atr-irrel-goal-proof" "irrelevant formula expected" formula)
    (case (tag formula)
      ((atom predicate)
       (let ((u (formula-to-new-avar formula)))
	 (make-proof-in-imp-intro-form
	  u (make-proof-in-avar-form u))))
      ((imp)
       (let* ((prem (imp-form-to-premise formula)) ;irrelevant
	      (concl (imp-form-to-conclusion formula)) ;also irrelevant
	      (prem-F (formula-subst prem falsity-log-pvar F-cterm))
	      (u1 (formula-to-new-avar formula))
	      (u2 (formula-to-new-avar prem-F)))
	 (mk-proof-in-intro-form
	  u1 u2 (make-proof-in-imp-elim-form
		 (atr-irrel-goal-proof concl)
		 (make-proof-in-imp-elim-form
		  (make-proof-in-avar-form u1)
		  (make-proof-in-imp-elim-form
		   (atr-arb-definite-proof prem)
		   (make-proof-in-avar-form u2)))))))
      ((impnc)
       (let* ((prem (impnc-form-to-premise formula)) ;irrelevant
	      (concl (impnc-form-to-conclusion formula)) ;also irrelevant
	      (prem-F (formula-subst prem falsity-log-pvar F-cterm))
	      (u1 (formula-to-new-avar formula))
	      (u2 (formula-to-new-avar prem-F)))
	 (make-proof-in-imp-intro-form
	  u1 (make-proof-in-impnc-intro-form
	      u2 (make-proof-in-imp-elim-form
		  (atr-irrel-goal-proof concl)
		  (make-proof-in-impnc-elim-form
		   (make-proof-in-avar-form u1)
		   (make-proof-in-imp-elim-form
		    (atr-arb-definite-proof prem)
		    (make-proof-in-avar-form u2))))))))
      ((all)
       (let ((var (all-form-to-var formula))
	     (kernel (all-form-to-kernel formula))
	     (u (formula-to-new-avar formula)))
	 (mk-proof-in-intro-form
	  u var (make-proof-in-imp-elim-form
		 (atr-irrel-goal-proof kernel)
		 (make-proof-in-all-elim-form
		  (make-proof-in-avar-form u)
		  (make-term-in-var-form var))))))
      ((allnc)
       (let ((var (allnc-form-to-var formula))
	     (kernel (allnc-form-to-kernel formula))
	     (u (formula-to-new-avar formula)))
	 (mk-proof-in-intro-form
	  u var (make-proof-in-imp-elim-form
		 (atr-irrel-goal-proof kernel)
		 (make-proof-in-allnc-elim-form
		  (make-proof-in-avar-form u)
		  (make-term-in-var-form var))))))
      (else (myerror "atr-irrel-goal-proof" "formula expected" formula))))
   (myerror "atr-irrel-goal-proof" "goal formula expected" formula)))

(define (atr-arb-goal-proof formula)
  (if
   (atr-goal? formula)
   (if
    (atr-relevant? formula)
    (case (tag formula)
      ((predicate) ;falsity-log
       (let ((u1 (formula-to-new-avar falsity-log))
	     (u2 (formula-to-new-avar (mk-imp falsity falsity-log))))
	 (mk-proof-in-intro-form
	  u1 u2 (make-proof-in-avar-form u1))))
      ((imp)
       (let* ((prem (imp-form-to-premise formula))
	      (concl (imp-form-to-conclusion formula))
	      (formula-F (formula-subst formula falsity-log-pvar F-cterm))
	      (prem-F (imp-form-to-premise formula-F))
	      (concl-F (imp-form-to-conclusion formula-F))
	      (u1 (formula-to-new-avar formula))
	      (u2 (formula-to-new-avar (mk-imp formula-F falsity-log)))
	      (u3 (formula-to-new-avar (mk-neg prem-F)))
	      (u4 (formula-to-new-avar prem-F))
	      (u5 (formula-to-new-avar concl-F))
	      (u6 (formula-to-new-avar prem))
	      (proof-of-prem-to-bot
	       (make-proof-in-imp-intro-form
		u6 (mk-proof-in-elim-form
		    (atr-arb-goal-proof concl)
		    (make-proof-in-imp-elim-form
		     (make-proof-in-avar-form u1)
		     (make-proof-in-avar-form u6))
		    (make-proof-in-imp-intro-form
		     u5 (make-proof-in-imp-elim-form
			 (make-proof-in-avar-form u2)
			 (make-proof-in-imp-intro-form
			  u4 (make-proof-in-avar-form u5)))))))
	      (renamed-elab-list
	       (formula-and-elab-path-to-renamed-elab-list concl-F '() '()))
	      (context (map (lambda (x) (if (formula-form? x)
					    (formula-to-new-avar x)
					    x))
			    (reverse (cdr (reverse renamed-elab-list)))))
	      (proof-of-neg-prem-F-to-bot
	       (make-proof-in-imp-intro-form
		u3 (make-proof-in-imp-elim-form
		    (make-proof-in-avar-form u2)
		    (apply mk-proof-in-intro-form
			   u4 (append
			       context
			       (list (make-proof-in-imp-elim-form
				      (make-proof-in-avar-form u3)
				      (make-proof-in-avar-form u4)))))))))
	 (if
	  (atr-relevant? prem)
	  (mk-proof-in-intro-form
	   u1 u2 (make-proof-in-imp-elim-form
		  proof-of-prem-to-bot
		  (make-proof-in-imp-elim-form
		   (atr-rel-definite-proof prem)
		   proof-of-neg-prem-F-to-bot)))
	  (mk-proof-in-intro-form
	   u1 u2 (mk-proof-in-elim-form
		  (qf-to-qf-cases-proof prem-F)
		  (make-proof-in-imp-intro-form
		   u4 (make-proof-in-imp-elim-form
		       proof-of-prem-to-bot
		       (make-proof-in-imp-elim-form
			(atr-arb-definite-proof prem)
			(make-proof-in-avar-form u4))))
		  proof-of-neg-prem-F-to-bot)))))
      ((impnc)
       (let* ((prem (impnc-form-to-premise formula))
	      (concl (impnc-form-to-conclusion formula))
	      (formula-F (formula-subst formula falsity-log-pvar F-cterm))
	      (prem-F (impnc-form-to-premise formula-F))
	      (concl-F (impnc-form-to-conclusion formula-F))
	      (u1 (formula-to-new-avar formula))
	      (u2 (formula-to-new-avar (mk-imp formula-F falsity-log)))
	      (u3 (formula-to-new-avar (mk-neg prem-F)))
	      (u4 (formula-to-new-avar prem-F))
	      (u5 (formula-to-new-avar concl-F))
	      (u6 (formula-to-new-avar prem))
	      (proof-of-prem-to-bot
	       (make-proof-in-imp-intro-form
		u6 (mk-proof-in-elim-form
		    (atr-arb-goal-proof concl)
		    (make-proof-in-impnc-elim-form
		     (make-proof-in-avar-form u1)
		     (make-proof-in-avar-form u6))
		    (make-proof-in-imp-intro-form
		     u5 (make-proof-in-imp-elim-form
			 (make-proof-in-avar-form u2)
			 (make-proof-in-impnc-intro-form
			  u4 (make-proof-in-avar-form u5)))))))
	      (renamed-elab-list
	       (formula-and-elab-path-to-renamed-elab-list concl-F '() '()))
	      (context (map (lambda (x) (if (formula-form? x)
					    (formula-to-new-avar x)
					    x))
			    (reverse (cdr (reverse renamed-elab-list)))))
	      (proof-of-neg-prem-F-to-bot
	       (make-proof-in-imp-intro-form
		u3 (make-proof-in-imp-elim-form
		    (make-proof-in-avar-form u2)
		    (make-proof-in-impnc-intro-form
		     u4 (apply mk-proof-in-intro-form
			       (append
				context
				(list (make-proof-in-imp-elim-form
				       (make-proof-in-avar-form u3)
				       (make-proof-in-avar-form u4))))))))))
	 (if
	  (atr-relevant? prem)
	  (mk-proof-in-intro-form
	   u1 u2 (make-proof-in-imp-elim-form
		  proof-of-prem-to-bot
		  (make-proof-in-imp-elim-form
		   (atr-rel-definite-proof prem)
		   proof-of-neg-prem-F-to-bot)))
	  (mk-proof-in-intro-form
	   u1 u2 (mk-proof-in-elim-form
		  (qf-to-qf-cases-proof prem-F)
		  (make-proof-in-imp-intro-form
		   u4 (make-proof-in-imp-elim-form
		       proof-of-prem-to-bot
		       (make-proof-in-imp-elim-form
			(atr-arb-definite-proof prem)
			(make-proof-in-avar-form u4))))
		  proof-of-neg-prem-F-to-bot))))))
    (let* ((formula-F (formula-subst formula falsity-log-pvar F-cterm))
	   (u1 (formula-to-new-avar (mk-imp formula-F falsity-log)))
	   (u2 (formula-to-new-avar formula)))
      (mk-proof-in-intro-form
       u2 u1 (make-proof-in-imp-elim-form
	      (make-proof-in-avar-form u1)
	      (make-proof-in-imp-elim-form
	       (atr-irrel-goal-proof formula)
	       (make-proof-in-avar-form u2))))))
   (myerror "atr-arb-goal-proof" "goal formula expected" formula)))

;; We now prove (G1^F -> ... -> Gn^F -> bot) -> G1 -> ... -> Gn -> bot.

(define (atr-goals-F-to-bot-proof . goals)
  (let* ((goals-F (map (lambda (f) (formula-subst f falsity-log-pvar F-cterm))
		       goals))
	 (goals-F-to-bot (apply mk-imp (append goals-F (list falsity-log))))
	 (u (formula-to-new-avar goals-F-to-bot))
	 (goal-F-avars (map (lambda (f) (formula-to-new-avar f)) goals-F))
	 (goal-avars (map (lambda (f) (formula-to-new-avar f)) goals)))
    (do ((gs (reverse goals) (cdr gs))
	 (vs (reverse goal-avars) (cdr vs))
	 (ws (reverse goal-F-avars) (cdr ws))
	 (proof-of-bot
	  (apply mk-proof-in-elim-form
		 (make-proof-in-avar-form u)
		 (map make-proof-in-avar-form goal-F-avars))
	  (mk-proof-in-elim-form
	   (atr-arb-goal-proof (car gs))
	   (make-proof-in-avar-form (car vs))
	   (make-proof-in-imp-intro-form
	    (car ws) proof-of-bot))))
	((null? gs)
	 (apply mk-proof-in-intro-form
		u (append goal-avars (list proof-of-bot)))))))

;; Given a proof of As -> Ds -> all ys(Gs -> bot) -> bot with As
;; arbitrary, Ds definite and Gs goal formulas, we transform it into a
;; proof of (F -> bot) -> As -> Ds^F -> all ys(Gs^F -> bot) -> bot.

(define (atr-min-excl-proof-to-bot-reduced-proof min-excl-proof)
  (let* ((formula (unfold-formula (proof-to-formula min-excl-proof)))
	 (params-and-kernel (all-form-to-vars-and-final-kernel formula))
	 (params (car params-and-kernel))
	 (kernel (cadr params-and-kernel))
	 (prems (imp-form-to-premises kernel))
	 (rev-prems (reverse prems))
	 (wrong-formula (car rev-prems))
	 (vars-and-final-kernel
	  (all-form-to-vars-and-final-kernel wrong-formula))
	 (vars (car vars-and-final-kernel))
	 (goals (imp-impnc-form-to-premises (cadr vars-and-final-kernel)))
	 (goals-F (map (lambda (f) (formula-subst f falsity-log-pvar F-cterm))
		       goals))
	 (as-and-ds (reverse (cdr rev-prems)))
	 (us-and-bot-reduced-ad-proofs
	  (map (lambda (d)
		 (if (atr-definite? d)
		     (let* ((d-F (formula-subst d falsity-log-pvar F-cterm))
			    (u (formula-to-new-avar d-F))
			    (bot-reduced-d-proof
			     (make-proof-in-imp-elim-form
			      (atr-arb-definite-proof d) ;of D^F -> D
			      (make-proof-in-avar-form u))))
		       (list u bot-reduced-d-proof))
		     (let ((u (formula-to-new-avar d)))
		       (list u (make-proof-in-avar-form u)))))
	       as-and-ds))
	 (us (map car us-and-bot-reduced-ad-proofs))
	 (bot-reduced-ad-proofs (map cadr us-and-bot-reduced-ad-proofs))
	 (bot-reduced-wrong-formula
	  (apply mk-all
		 (append vars
			 (list (apply mk-imp
				      (append goals-F
					      (list falsity-log)))))))
	 (u (formula-to-new-avar bot-reduced-wrong-formula))
	 (wrong-formula-proof
	  (apply mk-proof-in-intro-form
		 (append vars
			 (list (make-proof-in-imp-elim-form
				(apply atr-goals-F-to-bot-proof goals)
				(apply mk-proof-in-elim-form
				       (make-proof-in-avar-form u)
				       (map make-term-in-var-form
					    vars)))))))
	 (proof-of-bot
	  (apply mk-proof-in-elim-form
		 (append (list min-excl-proof)
			 (map make-term-in-var-form params)
			 bot-reduced-ad-proofs
			 (list wrong-formula-proof)))))
    (apply mk-proof-in-intro-form
	   F-to-bot-avar
	   (append us (list u proof-of-bot)))))

;; Substituting the formula ex ys Gs^F for bot in the proof given above
;; of (F -> bot) -> As -> Ds^F -> all ys(Gs^F -> bot) -> bot, both the
;; efq-premise and the wrong formula become provable and we obtain a
;; proof of As' -> Ds^F -> ex ys Gs^F, where As' is defined to be
;; As[bot := ex ys Gs^F].

(define (atr-min-excl-proof-to-ex-proof min-excl-proof)
  (let* ((formula (unfold-formula (proof-to-formula min-excl-proof)))
	 (params-and-kernel (all-form-to-vars-and-final-kernel formula))
	 (params (car params-and-kernel))
	 (kernel (cadr params-and-kernel))
	 (prems (imp-form-to-premises kernel))
	 (rev-prems (reverse prems))
	 (wrong-formula (if (null? rev-prems)
			    (myerror "atr-min-excl-proof-to-ex-proof"
				     "premises expected in kernel formula"
				     kernel)
			    (car rev-prems)))
	 (vars-and-final-kernel
	  (all-form-to-vars-and-final-kernel wrong-formula))
	 (vars (car vars-and-final-kernel))
	 (goals (imp-impnc-form-to-premises (cadr vars-and-final-kernel)))
	 (ex-formula
	  (cond
	   ((null? vars)
	    (myerror "atr-min-excl-proof-to-ex-proof"
		     "generalized variables expected in wrong formula"
		     wrong-formula))
	   ((null? goals)
	    (myerror "atr-min-excl-proof-to-ex-proof"
		     "goals expected in wrong formula"
		     wrong-formula))
	   (else (apply mk-ex (append vars (list (apply mk-and goals)))))))
	 (ex-formula-F (formula-subst ex-formula falsity-log-pvar F-cterm))
	 (ex-cterm (make-cterm ex-formula-F))
	 (bot-reduced-proof
	  (np (atr-min-excl-proof-to-bot-reduced-proof min-excl-proof)))
	 (subst-proof-with-ex
	  (proof-subst bot-reduced-proof falsity-log-pvar ex-cterm))
	 (formula-with-ex (proof-to-formula subst-proof-with-ex))
	 (params-and-kernel-with-ex
	  (all-form-to-vars-and-final-kernel formula-with-ex))
	 (kernel-with-ex (cadr params-and-kernel-with-ex))
	 (prems-with-ex (imp-form-to-premises kernel-with-ex))
	 (as-with-ex-and-ds-F
	  (reverse (cdr (reverse (cdr prems-with-ex)))))
	 (us (map formula-to-new-avar as-with-ex-and-ds-F))
	 (efq-proof (np (proof-of-efq-at ex-formula-F)))
	 (goals-F (map (lambda (f) (formula-subst f falsity-log-pvar F-cterm))
		       goals))
	 (vs (map formula-to-new-avar goals-F))
	 (proof-of-wrong-formula-F ;all vars(Gs^F -> ex vars Gs^F)
	  (apply
	   mk-proof-in-intro-form
	   (append
	    vars vs
	    (list (apply mk-proof-in-ex-intro-form
			 (append (map make-term-in-var-form vars)
				 (list ex-formula-F
				       (apply mk-proof-in-and-intro-form
					      (map make-proof-in-avar-form
						   vs))))))))))
    (apply
     mk-proof-in-intro-form
     (append params us
	     (list (apply mk-proof-in-elim-form
			  subst-proof-with-ex efq-proof
			  (append (map make-proof-in-avar-form us)
				  (list proof-of-wrong-formula-F))))))))

;; For backwards comparibility we temporarily keep

(define atr-min-excl-proof-to-intuit-ex-proof
  atr-min-excl-proof-to-ex-proof)

;; Given a proof of As -> Ds -> all ys(Gs -> bot) -> bot with As
;; arbitrary, Ds definite and Gs goal formulas.  Let ss be realizers of
;; As' := As[bot := ex ys Gs^F] and ts be realizers of Ds^F, both under
;; the assumptions As and Ds.  The following procedure constructs an
;; eterm such that As -> Ds->Gs^F[ys:=eterm].

(define (atr-min-excl-proof-to-structured-extracted-term
	 min-excl-proof . realizers-for-nondefinite-formulas)
  (if (not (min-excl-formula? (proof-to-formula min-excl-proof)))
      (myerror "atr-min-excl-proof-to-structured-extracted-term"
	       "min-excl-formula expected"
	       (proof-to-formula min-excl-proof)))
  (let* ((intuit-ex-proof
	  (atr-min-excl-proof-to-intuit-ex-proof min-excl-proof))
	 (formula (proof-to-formula intuit-ex-proof))
	 (params-and-kernel (all-form-to-vars-and-final-kernel formula))
	 (params (car params-and-kernel))
	 (intuit-ex-proof-with-params
	  (apply mk-proof-in-elim-form
		 intuit-ex-proof
		 (map make-term-in-var-form params)))
	 (eterm (proof-to-extracted-term intuit-ex-proof-with-params)))
    (apply
     mk-term-in-abst-form
     (append params
	     (list  (apply mk-term-in-app-form
			   eterm
			   realizers-for-nondefinite-formulas))))))

(define (min-excl-formula? formula)
  (let* ((params-and-kernel (all-form-to-vars-and-final-kernel formula))
	 (params (car params-and-kernel))
	 (kernel (cadr params-and-kernel))
	 (prems (imp-form-to-premises kernel))
	 (concl (imp-form-to-final-conclusion kernel))
	 (rev-prems (reverse prems))
	 (wrong-formula (if (null? rev-prems)
			    (myerror "min-excl-formula?"
				     "premises expected in kernel formula"
				     kernel)
			    (car rev-prems)))
	 (vars-and-final-kernel
	  (all-form-to-vars-and-final-kernel wrong-formula))
	 (vars (car vars-and-final-kernel))
	 (final-kernel (cadr vars-and-final-kernel))
	 (goals (imp-impnc-form-to-premises (cadr vars-and-final-kernel)))
	 (ds (reverse (cdr rev-prems))))
    (if (null? vars)
	(myerror "min-excl-formula?"
		 "generalized variables expected in wrong formula"
		 wrong-formula))
    (if (null? goals)
	(myerror "min-excl-formula?"
		 "goals expected in wrong formula"
		 wrong-formula))
    (if (not (formula=? concl falsity-log))
	(myerror "min-excl-formula?" "falsity-log expected" concl))
    (if (not (formula=?
	      (imp-impnc-form-to-final-conclusion final-kernel) falsity-log))
	(myerror "min-excl-formula?"
		 "falsity-log expected as final conclusion of"
		 final-kernel))
    (if (not (apply and-op (map atr-goal? goals)))
	(let ((not-atr-goals
	       (list-transform-positive goals
		 (lambda (goal) (not (atr-goal? goal))))))
	  (apply myerror
		 "min-excl-formula?" "goal formulas expected"
		 not-atr-goals)))
    (if (not (apply and-op (map atr-definite? ds)))
	(if COMMENT-FLAG
	    (begin
	      (comment "min-excl-formula?")
	      (comment "warning: non definite premise(s)")
	      (do ((l ds (cdr l)))
		  ((null? l))
		(if (not (atr-definite? (car l)))
		    (comment (formula-to-string (car l))))))))
    (if (or (null? vars) (null? goals))
	(myerror "min-excl-formula?" "unexpected formula" formula))
    #t))

;; For backward compatibility we keep

(define (min-excl-proof? proof)
  (min-excl-formula? (proof-to-formula proof)))

;; atr-expand-theorems expands all non-definite theorems.  It only
;; makes sense before substituting for bot.

(define (atr-expand-theorems proof)
  (case (tag proof)
    ((proof-in-avar-form) proof)
    ((proof-in-aconst-form)
     (let* ((aconst (proof-in-aconst-form-to-aconst proof))
	    (name (aconst-to-name aconst))
	    (kind (aconst-to-kind aconst)))
       (if (and (eq? 'theorem (aconst-to-kind aconst))
		(not (atr-definite? (aconst-to-formula aconst))))
	   (let* ((inst-proof (theorem-aconst-to-inst-proof aconst))
		  (free (formula-to-free (proof-to-formula inst-proof))))
	     (atr-expand-theorems
	      (apply mk-proof-in-nc-intro-form
		     (append free (list inst-proof)))))
	   proof)))
    ((proof-in-imp-elim-form)
     (let ((op (proof-in-imp-elim-form-to-op proof))
	   (arg (proof-in-imp-elim-form-to-arg proof)))
       (make-proof-in-imp-elim-form
	(atr-expand-theorems op)
	(atr-expand-theorems arg))))
    ((proof-in-imp-intro-form)
     (let ((avar (proof-in-imp-intro-form-to-avar proof))
	   (kernel (proof-in-imp-intro-form-to-kernel proof)))
       (make-proof-in-imp-intro-form
	avar (atr-expand-theorems kernel))))
    ((proof-in-impnc-elim-form)
     (let ((op (proof-in-impnc-elim-form-to-op proof))
	   (arg (proof-in-impnc-elim-form-to-arg proof)))
       (make-proof-in-impnc-elim-form
	(atr-expand-theorems op)
	(atr-expand-theorems arg))))
    ((proof-in-impnc-intro-form)
     (let ((avar (proof-in-impnc-intro-form-to-avar proof))
	   (kernel (proof-in-impnc-intro-form-to-kernel proof)))
       (make-proof-in-impnc-intro-form
	avar (atr-expand-theorems kernel))))
    ((proof-in-and-intro-form)
     (let ((left (proof-in-and-intro-form-to-left proof))
	   (right (proof-in-and-intro-form-to-right proof)))
       (make-proof-in-and-intro-form
	(atr-expand-theorems left)
	(atr-expand-theorems right))))
    ((proof-in-and-elim-left-form)
     (let ((kernel (proof-in-and-elim-left-form-to-kernel proof)))
       (make-proof-in-and-elim-left-form
	(atr-expand-theorems kernel))))
    ((proof-in-and-elim-right-form)
     (let ((kernel (proof-in-and-elim-right-form-to-kernel proof)))
       (make-proof-in-and-elim-right-form
	(atr-expand-theorems kernel))))
    ((proof-in-all-intro-form)
     (let ((var (proof-in-all-intro-form-to-var proof))
	   (kernel (proof-in-all-intro-form-to-kernel proof)))
       (make-proof-in-all-intro-form
	var (atr-expand-theorems kernel))))
    ((proof-in-all-elim-form)
     (let ((op (proof-in-all-elim-form-to-op proof))
	   (arg (proof-in-all-elim-form-to-arg proof)))
       (make-proof-in-all-elim-form
	(atr-expand-theorems op) arg)))
    ((proof-in-allnc-intro-form)
     (let ((var (proof-in-allnc-intro-form-to-var proof))
	   (kernel (proof-in-allnc-intro-form-to-kernel proof)))
       (make-proof-in-allnc-intro-form
	var (atr-expand-theorems kernel))))
    ((proof-in-allnc-elim-form)
     (let ((op (proof-in-allnc-elim-form-to-op proof))
	   (arg (proof-in-allnc-elim-form-to-arg proof)))
       (make-proof-in-allnc-elim-form
	(atr-expand-theorems op) arg)))
    (else (myerror "atr-expand-theorems"
		   "proof tag expected" (tag proof)))))
