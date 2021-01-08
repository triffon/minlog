;; (load "~/git/minlog/init.scm")
(load "names.scm")

; 16. Extracted terms
; ===================
; (ets.scm and etsd.scm)

;; Tests for number-and-idpredconst-to-et-constr-term

(add-pvar-name "P" (make-arity (py "nat")))

(define ltlist-idpc (predicate-form-to-predicate
		     (pf "(RTotalLtlist (cterm (n^) P n^))(ltlist nat)^")))
(pp (number-and-idpredconst-to-et-constr-term 0 ltlist-idpc))
;; (LEmpty alpha426)

(PVAR-TO-TVAR '(pvar (arity (alg "nat")) -1 0 0 "P"))
;; (tvar 426 "alpha")

(pp (number-and-idpredconst-to-et-constr-term 1 ltlist-idpc))
;; (LTcons alpha426)

(define ltree-idpc (predicate-form-to-predicate
		    (pf "(RTotalLtree (cterm (n^) P n^))(ltree nat)^")))
(pp (number-and-idpredconst-to-et-constr-term 0 ltree-idpc))
;; (LLeaf alpha426)

(pp (number-and-idpredconst-to-et-constr-term 1 ltree-idpc))
;; (LBranch alpha426)

(define ltlist-idpc-nc (predicate-form-to-predicate
			(pf "(RTotalLtlist (cterm (n^) T))(ltlist nat)^")))
(pp (number-and-idpredconst-to-et-constr-term 0 ltlist-idpc-nc))
;; ok, algebra ltlistnc added
;; ok, algebra ltreenc added
;; LEmptyNc

(pp (number-and-idpredconst-to-et-constr-term 1 ltlist-idpc-nc))
;; LTconsNc

(define ltree-idpc-nc (predicate-form-to-predicate
		       (pf "(RTotalLtree (cterm (n^) T))(ltree nat)^")))
(pp (number-and-idpredconst-to-et-constr-term 0 ltree-idpc-nc))
;; LLeafNc

(pp (number-and-idpredconst-to-et-constr-term 1 ltree-idpc-nc))
;; LBranchNc

(define pione-idpc
  (predicate-form-to-predicate
   (pf "(PiOne (cterm (x^, x^1) (Pvar alpha alpha)x^ x^1))x^")))

(pp (number-and-idpredconst-to-et-constr-term 0 pione-idpc))
;; [alpha614^4062]alpha614^4062

(define pione-idpc
  (predicate-form-to-predicate (pf "(PiOne (cterm (x^, x^1) T))x^")))

(number-and-idpredconst-to-et-constr-term 0 pione-idpc)
;; eps

;; Tests for axiom-to-extracted-term .  This is the only place where
;; number-and-idpredconst-to-et-constr-term is used, in Intro case

(define intro-aconst (number-and-idpredconst-to-intro-aconst 1 ltree-idpc))
(pp (rename-variables (aconst-to-inst-formula intro-aconst)))

;; allnc (ltlist nat)^(
;;  (RTotalLtlist (cterm (n^) P n^))(ltlist nat)^ ->
;;  (RTotalLtree (cterm (n^) P n^))((LBranch nat)(ltlist nat)^))

;; axiom-to-extracted-term is used when we extract a term from a proof
;; obtained by formula-to-ef-proof

(define proof
  (formula-to-ef-proof (pf "(RTotalLtlist (cterm (n^) P n^))(ltlist nat)^")))

;; (proof-to-expr-with-formulas proof)
;; Uses Intro: (RTotalLtlist (cterm (n^) P n^))(LEmpty nat)

(define eterm (proof-to-extracted-term proof))
(define neterm (nt eterm))
(pp neterm)
;; (LEmpty alpha426)

(remove-pvar-name "P")

;; 2012-11-09.  To be moved into a new file testsound.scm

;; 2012-02-15.  Modularization of proof-to-soundness-proof .  Let a
;; theorem Thm (thought of as coming with its proof M) prove A.  Then
;; we should have ThmSound proving et(M) mr A in our proof library.
;; Then proof-to-soundness-proof at Thm inserts ThmSound.  There is no
;; circularity here, since t mr A is invariant, i.e., eps mr(t mr A) is
;; the formula t mr A itself (cf. 7.2.4 in pc10).

;; In the special case of a theorem PconstTotal proving totality of
;; Pconst the extracted term is Pconst rather than cPconstTotal (which
;; when animated would unfold into a term with recursion operators).
;; Then PconstTotalSound proves Pconst mr PconstTotal, with a simple
;; standard proof.

;; Contents.  I Axioms.  Nothing needed for nci axioms.  For intro and
;; elim aconsts distinguish c.r. and n.c. cases.  II Theorems.  Again
;; nothing needed for nci theorems.  Otherwise we can (always? better
;; not) create ThmSound.  Special case: PconstTotalSound.  Again it
;; should not be enforced that both are there.  Only in the model files
;; nat and list all this should be done.

;; Naming conventions.  Suffix MR of theorem name indicates a clause name.
;; They are created by add-mr-ids.

;; Test of imp-formulas-to-mr-elim-proof

;; (add-algs "bin"
;; 	  '("bin" "BinNil")
;; 	  '("bin=>bin=>bin" "BinBranch"))

(add-var-name "a" "b" (py "bin"))
(add-totality "bin")
;; (add-mr-ids "TotalBin")

(display-idpc "TotalBin")
 ;; 	TotalBinBinNil:	TotalBin BinNil
 ;; 	TotalBinBinBranch:	allnc a^(
 ;; TotalBin a^ -> allnc a^0(TotalBin a^0 -> TotalBin(BinBranch a^ a^0)))

;; (display-idpc "TotalBinMR")
 ;; 	TotalBinBinNilMR:	TotalBinMR BinNil BinNil
 ;; 	TotalBinBinBranchMR:	allnc a^,a^0(
 ;; TotalBinMR a^0 a^ -> 
 ;; allnc a^1,a^2(
 ;;  TotalBinMR a^2 a^1 -> TotalBinMR(BinBranch a^0 a^2)(BinBranch a^ a^1)))

(add-pvar-name "P" (make-arity (py "bin")))

;; (define proof (imp-formulas-to-mr-elim-proof (pf "TotalBin a^ -> P a^")))
;; imp-formulas-to-mr-elim-proof must be adapted to totality premises
;; (cdp proof)

(remove-pvar-name "P")

;; Tests for more general situations.
;; 1.  Parameter in the conclusion of imp-formula

(add-pvar-name "P" (make-arity (py "nat") (py "bin")))

;; (define proof (imp-formulas-to-mr-elim-proof (pf "TotalBin a^ -> P l^ a^")))
;; (cdp proof)

(remove-pvar-name "P")

;; 2.  Inductive predicate with param-pvar substituted by cterm with param
;; Take RTotalList

;; (add-mr-ids "RTotalList")

(add-pvar-name "S" (make-arity (py "nat") (py "alpha")))
(add-pvar-name "P" (make-arity (py "nat") (py "list alpha")))

(define proof (imp-formulas-to-mr-elim-proof
	       (pf "(RTotalList (cterm (x^) S n^ x^))xs^ -> P l^ xs^")))
;; (cdp proof)

(remove-pvar-name "S" "P")

;; 3.  idpc with tvar alpha, and tsubst alpha |-> nat

(add-pvar-name "S" (make-arity (py "nat")))
(add-pvar-name "P" (make-arity (py "list nat")))
(add-var-name "ns" (py "list nat"))

(define proof (imp-formulas-to-mr-elim-proof
	       (pf "(RTotalList (cterm (n^) S n^))ns^ -> P ns^")))
;; (cdp proof)

(remove-pvar-name "S" "P")

;; 4.  Same with parameters

(add-pvar-name "S" (make-arity (py "boole") (py "nat")))
(add-pvar-name "P" (make-arity (py "boole") (py "list nat")))

(define proof
  (imp-formulas-to-mr-elim-proof
   (pf "(RTotalList (cterm (n^) S boole^1 n^))ns^ -> P boole^2 ns^")))
;; (cdp proof)

(remove-pvar-name "S" "P")

;; 5.  Simultaneous predicates

;; (add-ids (list (list "Ev" (make-arity (py "nat")) "algEv")
;; 	       (list "Od" (make-arity (py "nat")) "algOd"))
;; 	 '("Ev 0" "InitEv")
;; 	 '("allnc n^(Od n^ -> Ev(n^ +1))" "GenEv")
;; 	 '("allnc n^(Ev n^ -> Od(n^ +1))" "GenOd"))

(add-pvar-name "P" (make-arity (py "nat")))
(add-mr-ids "Ev")

(define proof
  (imp-formulas-to-mr-elim-proof (pf "Od n^ -> P n^") (pf "Ev n^ -> P1 n^")))
;; (cdp proof)

(remove-pvar-name "P")

;; (add-algs (list "tlist" "tree")
;; 	  '("tlist" "Empty")
;; 	  '("tree=>tlist=>tlist" "Tcons")
;; 	  '("tree" "Leaf")
;; 	  '("tlist=>tree" "Branch"))

(add-totality "tlist")
;; (add-mr-ids "TotalTree")

(add-pvar-name "S" (make-arity (py "tlist")))
(add-pvar-name "P" (make-arity (py "tree")))

(add-var-name "ts" (py "tlist"))
(add-var-name "t" (py "tree"))

;; (define proof (imp-formulas-to-mr-elim-proof
;; 	       (pf "TotalTree t^ -> P t^") (pf "TotalTlist ts^ -> S ts^")))
;; (cdp proof)

(remove-pvar-name "S" "P")
(remove-var-name "t" "ts")

;; Test for imp-formulas-to-mr-elim-proof with a binary idpc

;; (add-algs "bbin"
;; 	  '("bbin" "BbinNil")
;; 	  '("boole=>bbin=>bbin=>bbin" "BbinBranch"))

(py "bbin boole")

(remove-var-name "a" "b")
(add-var-name "a" "b" (py "bbin boole"))
(add-var-name "q" (py "boole"))
(remove-pvar-name "Y")
(add-pvar-name "Y" (make-arity (py "boole")))

(add-ids (list (list "I" (make-arity (py "bbin boole")) "algI"))
	 '("I(BbinNil boole)" "InitI")
	 '("allnc q,a,b(Y q -> I a -> q=True -> I b ->
           I((BbinBranch boole) q a b))"
	   "GenI"))

(display-alg "algI")
	;; CInitI:	algI alpha1
	;; CGenI:	alpha1=>algI alpha1=>algI alpha1=>algI alpha1

(display-idpc "I")
(add-mr-ids "I")
(display-idpc "IMR")
(pp "GenIMR")

;; all q,a,b,alpha793^(
;;  (Pvar alpha793 boole)^443 alpha793^ q -> 
;;  all (algI alpha793)^0(
;;   (IMR (cterm (alpha793^1,p^) (Pvar alpha793 boole)^443 alpha793^1 p^))
;;   (algI alpha793)^0 
;;   a -> 
;;   q=True -> 
;;   all (algI alpha793)^1(
;;    (IMR (cterm (alpha793^2,p^) (Pvar alpha793 boole)^443 alpha793^2 p^))
;;    (algI alpha793)^1 
;;    b -> 
;;    (IMR (cterm (alpha793^2,p^) (Pvar alpha793 boole)^443 alpha793^2 p^))
;;    ((CGenI alpha793)alpha793^(algI alpha793)^0(algI alpha793)^1)
;;    ((BbinBranch boole)q a b))))

(add-pvar-name "Z" (make-arity))

(define imp-formula (pf "(I (cterm (q^) Y q^))a^ -> Z"))

(define proof (imp-formulas-to-mr-elim-proof imp-formula))
;; (cdp proof)
;; ok
;; (pp (rename-variables (proof-to-formula proof)))

;; Test of ex-formula-to-ex-intro-mr-proof

(define proof (ex-formula-to-ex-intro-mr-proof (pf "ex x^ (Pvar alpha)^ x^")))
;; (cdp proof)
(pp (proof-to-formula proof))
;; all x^((Pvar alpha)^ x^ -> (Pvar alpha)^ x^)

(define proof (ex-formula-to-ex-intro-mr-proof (pf "ex x^ (Pvar alpha) x^")))
;; (cdp proof)
(pp (rename-variables (proof-to-formula proof)))

;; all x^,gamma^(
;;  (Pvar gamma alpha)^ gamma^ x^ -> (Pvar gamma alpha)^ gamma^ x^)

;; Test of ex-formula-and-concl-to-ex-elim-mr-proof
(define proof (ex-formula-and-concl-to-ex-elim-mr-proof
	       (pf "ex x (Pvar alpha)^ x") (pf "Pvar")))
;; (cdp proof)
(pp (rename-variables (proof-to-formula proof)))

;; all x(
;;  (Pvar alpha)^ x -> 
;;  all (alpha=>beta)^(
;;   all x0((Pvar alpha)^ x0 -> (Pvar beta)^((alpha=>beta)^ x0)) -> 
;;   (Pvar beta)^((alpha=>beta)^ x)))

(define proof (ex-formula-and-concl-to-ex-elim-mr-proof
	       (pf "ex x (Pvar alpha)x") (pf "Pvar")))
;; (cdp proof)
(pp (rename-variables (proof-to-formula proof)))

;; all (alpha@@gamma)(
;;  (Pvar alpha gamma)^(left(alpha@@gamma))(right(alpha@@gamma)) -> 
;;  all (alpha=>gamma=>beta)^0(
;;   all x,gamma^1(
;;    (Pvar alpha gamma)^ x gamma^1 -> 
;;    (Pvar beta)^((alpha=>gamma=>beta)^0 x gamma^1)) -> 
;;   (Pvar beta)^((alpha=>gamma=>beta)^0 left(alpha@@gamma)right(alpha@@gamma))))

(define ex-formula (pf "ex x (Pvar alpha)x"))
(define concl (pf "Pvar"))
(define proof (ex-formula-and-concl-to-ex-elim-mr-proof ex-formula concl))
(cdp proof) ;ok after making the pair-var total
;; degrees of totality do not fit for variable
;; x
;; and term
;; left(alpha@@gamma)^15827
(pp (rename-variables (proof-to-formula proof)))

;; all (alpha@@gamma)(
;;  (Pvar alpha gamma)^(left(alpha@@gamma))(right(alpha@@gamma)) -> 
;;  all (alpha=>gamma=>beta)^0(
;;   all x,gamma^1(
;;    (Pvar alpha gamma)^ x gamma^1 -> 
;;    (Pvar beta)^((alpha=>gamma=>beta)^0 x gamma^1)) -> 
;;   (Pvar beta)^((alpha=>gamma=>beta)^0 left(alpha@@gamma)right(alpha@@gamma))))

;; Test of exr-formula-and-concl-to-exr-elim-mr-proof
;; (define proof (exr-formula-and-concl-to-exr-elim-mr-proof
;; 	       (pf "exr p^ Y p^") (pf "Pvar")))
;; (cdp proof)

;; (pp (rename-variables (proof-to-formula proof)))

;; all alpha1063^(
;;  (ExRMR alpha1063
;;    boole
;;    (cterm (alpha1063^0,p^) (Pvar alpha1063 boole)^495 alpha1063^0 p^))
;;  alpha1063^ -> 
;;  all (alpha1063=>beta)^0(
;;   all p^,alpha1063^1(
;;    (Pvar alpha1063 boole)^495 alpha1063^1 p^ -> 
;;    (Pvar beta)^((alpha1063=>beta)^0 alpha1063^1)) -> 
;;   (Pvar beta)^((alpha1063=>beta)^0 alpha1063^)))

;; Test of andlr-formula-and-concl-to-andl-elim-mr-proof

(remove-pvar-name "Y")
(add-pvar-name "Y" "Z" (make-arity))
(define proof (andlr-formula-and-concl-to-andlr-elim-mr-proof
	       (pf "Pvar^ andr Y") (pf "Z")))
;; (cdp proof)

(pp (rename-variables (proof-to-formula proof)))

;; allnc alpha1267^(
;;  (AndRMR (cterm () Pvar^)
;;    (cterm (alpha1267^0) (Pvar alpha1267)^576 alpha1267^0))
;;  alpha1267^ -> 
;;  allnc (alpha1267=>alpha1265)^0(
;;   (Pvar^ -> 
;;    allnc alpha1267^1(
;;     (Pvar alpha1267)^576 alpha1267^1 -> 
;;     (Pvar alpha1265)^575((alpha1267=>alpha1265)^0 alpha1267^1))) -> 
;;   (Pvar alpha1265)^575((alpha1267=>alpha1265)^0 alpha1267^)))

;; Test of proof-to-soundness-proof

(add-alg "pos" '("One" "pos") '("SZero" "pos=>pos") '("SOne" "pos=>pos"))
(add-totality "pos")
(add-mr-ids "TotalPos")

;; PosTotalVar
(set-goal "all pos TotalPos pos")
(ind)
(use "TotalPosOne")
(assume "pos" "Tpos")
(use "TotalPosSZero")
(use "Tpos")
(assume "pos" "Tpos")
(use "TotalPosSOne")
(use "Tpos")
;; Proof finished.
(save "PosTotalVar")

(remove-var-name "q")
(add-var-name "q" (py "pos"))

(add-pvar-name "P" (make-arity (py "pos")))

;; (define proof (imp-formulas-to-mr-elim-proof (pf "TotalPos q^ -> P q^")))
;; (cdp proof)

(add-program-constant "PosS" (py "pos=>pos") t-deg-zero)
(add-computation-rules
 "PosS One" "SZero One"
 "PosS(SZero pos)" "SOne pos"
 "PosS(SOne pos)" "SZero(PosS pos)")

;; PosSTotal
(set-totality-goal "PosS")
(assume "q^" "Tq")
(elim "Tq")
;; ?_3:TotalPos(PosS One)
(ng #t)
(use "TotalPosSZero")
(use "TotalPosOne")
;; ?_4:allnc pos^(
;;      TotalPos pos^ -> TotalPos(PosS pos^) -> TotalPos(PosS(SZero pos^)))
(assume "q^1" "Tq1" "TSq1")
(ng #t)
(use "TotalPosSOne")
(use "Tq1")
;; ?_5:allnc pos^(
;;      TotalPos pos^ -> TotalPos(PosS pos^) -> TotalPos(PosS(SOne pos^)))
(assume "q^1" "Tq1" "TSq1")
(ng #t)
(use "TotalPosSZero")
(use "TSq1")
;; Proof finished.
(save-totality)

;; (define sproof (proof-to-soundness-proof "PosSTotal"))
;; (cdp sproof)

;; (define proof
;;   (imp-formulas-to-mr-elim-proof (pf "TotalPos q^ -> TotalPos(PosS q^)")))
;; (cdp proof)

(remove-var-name "q")
(remove-pvar-name "P")

;; Tests of proof-to-soundness-proof

(set-goal "(Pvar^1 -> Pvar2 -> Pvar3) -> Pvar^1 -> Pvar2 -> Pvar^1 -> Pvar3")
(assume "u" "u1" "u2" "u3")
(use-with "u" "u1" "u2")
(cdp (proof-to-soundness-proof))

(set-goal "(Pvar1 -> Pvar2 -> Pvar3) -> Pvar1 -> Pvar2 -> Pvar1 -> Pvar3")
(assume "u" "u1" "u2" "u3")
(use-with "u" "u1" "u2")
(cdp (proof-to-soundness-proof))

;; (add-var-name "x" "y" (py "alpha"))
(set-goal "allnc x^,y^(x^ eqd y^ -> (Pvar alpha)x^ -> (Pvar alpha)y^)")
(assume "x^" "y^" "EqHyp" "Px")
(use "EqDCompat" (pt "x^"))
(use "EqHyp")
(use "Px")
;; Proof finished.

(cdp (proof-to-soundness-proof))

;; 2020-08-14.  Invariance axioms in soundness proofs.

;; ImpElimExample
(set-goal "T ornc F")
(assert "T oru F")
;; 2,3
(intro 0)
(use "Truth")
;; 2
(assume "Disj")
(elim "Disj")
;; 6,7
(assume "Left")
(intro 0)
(use "Left")
;; 7
(assume "Right")
(intro 1)
(use "Right")
;; Proof finished.
(save "ImpElimExample")

(define sproof (proof-to-soundness-proof))
;; (cdp sproof)
(proof-to-expr-with-formulas sproof)

;; Elim: exnc p^ (OrUMR (cterm () T) (cterm () F))p^ -> 
;; allnc p^((OrUMR (cterm () T) (cterm () F))p^ -> T ornc F) -> T ornc F
;; InvarEx: T oru F -> exnc p^ (OrUMR (cterm () T) (cterm () F))p^
;; Elim: T oru F -> (T -> T ornc F) -> (F -> T ornc F) -> T ornc F
;; InvarAll: allnc p^((OrUMR (cterm () T) (cterm () F))p^ -> T oru F)
;; Intro: T -> T ornc F
;; Intro: F -> T ornc F
;; Intro: T -> (OrUMR (cterm () T) (cterm () F))True
;; Truth: T
;; Disj: T oru F
;; umr: (OrUMR (cterm () T) (cterm () F))p^14954
;; Left: T
;; Right: F

;; ((lambda (Disj)
;;    ((Elim (InvarEx Disj))
;;      (lambda (p^14954)
;;        (lambda (umr)
;;          (((Elim ((InvarAll p^14954) umr))
;;             (lambda (Left) (Intro Left)))
;;            (lambda (Right) (Intro Right)))))))
;;   ((InvarAll #t) (Intro Truth)))

;; Impintroexample
(set-goal "T oru F -> T ornc F")
(assume "u")
(elim "u")
(assume "Left")
(intro 0)
(use "Left")
(assume "Right")
(intro 1)
(use "Right")
;; Proof finished.
;; (cdp)
(save "ImpIntroExample")

(define sproof (proof-to-soundness-proof "ImpIntroExample"))
;; (cdp sproof)
(proof-to-expr-with-formulas sproof)

;; Elim: exnc p^ (OrUMR (cterm () T) (cterm () F))p^ -> 
;; allnc p^((OrUMR (cterm () T) (cterm () F))p^ -> T ornc F) -> T ornc F
;; InvarEx: T oru F -> exnc p^ (OrUMR (cterm () T) (cterm () F))p^
;; Elim: T oru F -> (T -> T ornc F) -> (F -> T ornc F) -> T ornc F
;; InvarAll: allnc p^((OrUMR (cterm () T) (cterm () F))p^ -> T oru F)
;; Intro: T -> T ornc F
;; Intro: F -> T ornc F
;; u: T oru F
;; umr: (OrUMR (cterm () T) (cterm () F))p^14982
;; Left: T
;; Right: F

;; (lambda (u)
;;   ((Elim (InvarEx u))
;;     (lambda (p^14982)
;;       (lambda (umr)
;;         (((Elim ((InvarAll p^14982) umr))
;;            (lambda (Left) (Intro Left)))
;;           (lambda (Right) (Intro Right)))))))

;; 2012-11-09.  To be moved into a new file testetsd.scm

;; Tests for extraction with realizability and Dialectica
;; Based on Trifon Trifonov's /dialectica/minlog/etsd-test.scm.

;; (load "~/minlog/init.scm")
;; (load "changes.scm")

;; (set! COMMENT-FLAG #f)
;; (libload "nat.scm")
;; (load "liblist.scm")
;; (set! COMMENT-FLAG #t)

(define (extraction-test-et proof)
  (extraction-test-aux proof proof-to-extracted-term))

(define (extraction-test-etd proof)
  (extraction-test-aux proof proof-to-extracted-d-term))

(define (extraction-test-aux proof extract)
  (let ((et (extract proof)))
    (if (eq? 'eps et)
	(display 'eps)
	(begin
	  (pp (rename-variables et))
	  (newline)
	  (pp (rename-variables (nt et)))))
    (newline)))

(define (extraction-test proof)
  (extraction-test-et proof)
  (extraction-test-etd proof))

;;----------------------------------------------------------------------
;; simple proof by cases
;;----------------------------------------------------------------------

(set-goal "all n1 ex n2 all n3(n1=n3 -> n2=n3)")
(cases)
(ex-intro (pt "0"))
(assume "n" "u")
(use "u")
(assume "n1")
(strip)
(ex-intro (pt "Succ n1"))
(assume "n" "u")
(use "u")
(extraction-test (current-proof))

;;----------------------------------------------------------------------
;; simple proof by induction
;;----------------------------------------------------------------------

(set-goal "all n1 ex n2 all n3(n1=n3 -> n2=n3)")
(ind)
(ex-intro (pt "0"))
(assume "n" "u")
(use "u")
(assume "n1")
(strip)
(ex-intro (pt "Succ n1"))
(assume "n" "u")
(use "u")
(extraction-test (current-proof))

;;----------------------------------------------------------------------
;; simple proof by general induction
;;----------------------------------------------------------------------

(set-goal "all n1 ex n2 all n3(n1=n3 -> n2=n3)")
(gind (pt "[n]n"))
(assume "n1")
(strip)
(ex-intro (pt "n1"))
(assume "n" "u")
(use "u")
(extraction-test (current-proof))

;;----------------------------------------------------------------------
;; proof by induction in which the IH is used
;;----------------------------------------------------------------------

(set-goal "all n1 ex n2 all n3(n1<n3 -> n2<=n3)")
(ind)
;; base case
(ex-intro (pt "1"))
(cases)
;; base subcase
(assume "u")
(use "u")
;; step subcase
(assume "n3" "u")
(use "u")
;; step case
(assume "n1" "IH")
(by-assume "IH" "n2" "v")
(ex-intro (pt "Succ n2"))
(cases)
;; base subcase
(assume "u")
(use "u")
;; step subcase
(assume "n3" "u")
(use "v")
(use "u")
(extraction-test-et (current-proof))
;; (extraction-test (current-proof))
;; Dialectica part takes too long

;;----------------------------------------------------------------------
;; proof by induction with a relevant assumption for Dialectica
;;----------------------------------------------------------------------

(set-goal
     "all n1,n2(all n3(n1<n3 -> n2<=n3) ->
                all n3(Succ n1<n3 -> Succ n2<=n3)) ->
      all n1 ex n2 all n3(n1<n3 -> n2<=n3)")
(assume "L")
(ind)
;; base case
(ex-intro (pt "1"))
(cases)
;; base subcase
(assume "u")
(use "u")
;; step subcase
(assume "n3" "u")
(use "u")
;; step case
(assume "n1" "IH")
(by-assume "IH" "n2" "v")
(ex-intro (pt "Succ n2"))
(use "L")
(use "v")
(extraction-test (current-proof))

;;----------------------------------------------------------------------
;; simple proof by list induction
;;----------------------------------------------------------------------

(add-var-name "ns" (py "list nat"))

(set-goal "all ns1 ex ns2 all ns3(ns1=ns3 -> ns2=ns3)")
(ind)
(ex-intro (pt "(Nil nat)"))
(assume "ns" "u")
(use "u")
(assume "n" "ns1")
(strip)
(ex-intro (pt "n::ns1"))
(assume "ns" "u")
(use "u")
(extraction-test (current-proof))

;;----------------------------------------------------------------------
;; proof by list induction in which the IH is used
;;----------------------------------------------------------------------
(set-goal "all ns1 ex ns2 all ns3(Lh ns1<Lh ns3 -> Lh ns2<=Lh ns3)")
(ind)
;; base case
(ex-intro (pt "0:"))
(cases)
;; base subcase
(assume "u")
(use "u")
;; step subcase
(assume "n3" "ns3" "u")
(use "u")
;; step case
(assume "n1" "ns1" "IH")
(by-assume "IH" "ns2" "v")
(ex-intro (pt "0::ns2"))
(cases)
;; base subcase
(assume "u")
(use "u")
;; step subcase
(assume "n3" "ns3" "u")
(use "v")
(use "u")
(extraction-test-et (current-proof))
;; (extraction-test (current-proof))
;; Dialectica part takes too long

;;----------------------------------------------------------------------
;; proof by list induction with a relevant assumption for Dialectica
;;----------------------------------------------------------------------

(set-goal
      "all ns1,n1,ns2(
       all ns3(Lh ns1<Lh ns3 -> Lh ns2<=Lh ns3) ->
       all ns3(Lh(n1::ns1)<Lh ns3 -> Lh(0::ns2)<=Lh ns3)) ->
       all ns1 ex ns2 all ns3(Lh ns1<Lh ns3 -> Lh ns2<=Lh ns3)")
(assume "L")
(ind)
;; base case
(ex-intro (pt "0:"))
(cases)
;; base subcase
(assume "u")
(use "u")
;; step subcase
(assume "n3" "ns3" "u")
(use "u")
;; step case
(assume "n1" "ns1" "IH")
(by-assume "IH" "ns2" "v")
(ex-intro (pt "n1::ns2"))
(use "L" (pt "n1"))
(use "v")
(extraction-test (current-proof))

;;----------------------------------------------------------------------
;; proof by cases using predicate variables
;;----------------------------------------------------------------------

(add-pvar-name "P" (make-arity (py "nat") (py "nat")))

(set-goal "P 0 1 -> all n1 ex n2 P(Succ n1)(Succ n2) -> all n1 ex n2 P n1 n2")
(assume "Base" "Step")
(cases)
(ex-intro (pt "1"))
(use "Base")
(assume "n1")
(inst-with-to "Step" (pt "n1") "Step1")
(by-assume "Step1" "n2" "Step2")
(ex-intro (pt "Succ n2"))
(use "Step2")
(extraction-test (current-proof))

;; (proof-to-expr-with-formulas (current-proof))
;; (proof-to-expr-with-formulas (np (current-proof)))

(set-goal
 "P^ 0 1 -> all n1 ex n2 P^(Succ n1)(Succ n2) -> all n1 ex n2 P^ n1 n2")
(assume "Base" "Step")
(cases)
(ex-intro (pt "1"))
(use "Base")
(assume "n1")
(inst-with-to "Step" (pt "n1") "Step1")
(by-assume "Step1" "n2" "Step2")
(ex-intro (pt "Succ n2"))
(use "Step2")
(extraction-test (current-proof))

(set-goal
 "P' 0 1 -> all n1 ex n2 P'(Succ n1)(Succ n2) -> all n1 ex n2 P' n1 n2")
(assume "Base" "Step")
(cases)
(ex-intro (pt "1"))
(use "Base")
(assume "n1")
(inst-with-to "Step" (pt "n1") "Step1")
(by-assume "Step1" "n2" "Step2")
(ex-intro (pt "Succ n2"))
(use "Step2")
(extraction-test (current-proof))

(set-goal
    "P^' 0 1 ->
     all n1 ex n2 P^'(Succ n1)(Succ n2) ->
     all n1 ex n2 P^' n1 n2")
(assume "Base" "Step")
(cases)
(ex-intro (pt "1"))
(use "Base")
(assume "n1")
(inst-with-to "Step" (pt "n1") "Step1")
(by-assume "Step1" "n2" "Step2")
(ex-intro (pt "Succ n2"))
(use "Step2")
(extraction-test (current-proof))

;;----------------------------------------------------------------------
;; proof by induction using predicate variables
;;----------------------------------------------------------------------

(set-goal
     "P 0 1 ->
      all n1,n2(P n1 n2 -> P(Succ n1)(Succ n2)) ->
      all n1 ex n2 P n1 n2")
(assume "Base" "Step")
(ind)
(ex-intro (pt "1"))
(use "Base")
(assume "n1" "IH")
(by-assume "IH" "n2" "IH1")
(inst-with-to "Step" (pt "n1") "Step1")
(ex-intro (pt "Succ n2"))
(use "Step1")
(use "IH1")
(extraction-test-et (current-proof))
;; (extraction-test-etd (current-proof))
;; Dialectica gives a contraction error, because of presence of pvars

(set-goal
     "P^' 0 1 ->
      all n1,n2(P^' n1 n2 -> P^'(Succ n1)(Succ n2)) ->
      all n1 ex n2 P^' n1 n2")
(assume "Base" "Step")
(ind)
(ex-intro (pt "1"))
(use "Base")
(assume "n1" "IH")
(by-assume "IH" "n2" "IH1")
(inst-with-to "Step" (pt "n1") "Step1")
(ex-intro (pt "Succ n2"))
(use "Step1")
(use "IH1")
(extraction-test-et (current-proof))
;; (extraction-test-etd (current-proof))
;; Dialectica gives a contraction error, because of presence of pvars

(set-goal "P^' 0 1 ->
   allnc n1,n2(P^' n1 n2 -> P^'(Succ n1)(Succ n2)) ->
   all n1 ex n2 P^' n1 n2")
(assume "Base" "Step")
(ind)
(ex-intro (pt "1"))
(use "Base")
(assume "n1" "IH")
(by-assume "IH" "n2" "IH1")
(inst-with-to "Step" (pt "n1") "Step1")
(ex-intro (pt "Succ n2"))
(use "Step1")
(use "IH1")
(extraction-test-et (current-proof))
;; Dialectica not yet properly implemented for allnc.

;;----------------------------------------------------------------------
;; general induction with predicate variables
;;----------------------------------------------------------------------

(set-goal
     "all n1(all n3(n3<n1 -> ex n2 P n3 n2) -> ex n2 P n1 n2) ->
      all n1 ex n2 P n1 n2")
(assume "L")
(gind (pt "[n]n"))
(assume "n1" "GIH")
(use "L")
(use "GIH")
(extraction-test-et (current-proof))
;; (extraction-test-etd (current-proof))
;; Dialectica gives a contraction error, because of presence of pvars

(remove-pvar-name "P")

;;----------------------------------------------------------------------
;; proof by list induction using predicate variables
;;----------------------------------------------------------------------

(add-pvar-name "P" (make-arity (py "list nat") (py "list nat")))

(set-goal
     "P(Nil nat)(0:) ->
      all ns1,ns2,n(P ns1 ns2 -> P(n::ns1)(n::ns2)) ->
      all ns1 ex ns2 P ns1 ns2")
(assume "Base" "Step")
(ind)
(ex-intro (pt "0:"))
(use "Base")
(assume "n" "ns1" "IH")
(by-assume "IH" "ns2" "IH1")
(inst-with-to "Step" (pt "ns1") "Step1")
(ex-intro (pt "n::ns2"))
(use "Step1")
(use "IH1")
(extraction-test-et (current-proof))
;; Dialectica gives a contraction error, because of presence of pvars

(set-goal
     "P^'(Nil nat)(0:) ->
      all ns1,ns2,n(P^' ns1 ns2 -> P^'(n::ns1)(n::ns2)) ->
      all ns1 ex ns2 P^' ns1 ns2")
(assume "Base" "Step")
(ind)
(ex-intro (pt "0:"))
(use "Base")
(assume "n" "ns1" "IH")
(by-assume "IH" "ns2" "IH1")
(inst-with-to "Step" (pt "ns1") "Step1")
(ex-intro (pt "n::ns2"))
(use "Step1")
(use "IH1")
(extraction-test-et (current-proof))
;; Dialectica gives a contraction error, because of presence of pvars

(set-goal
     "P^'(Nil nat)(0:) ->
      allnc ns1,ns2,n(P^' ns1 ns2 -> P^'(n::ns1)(n::ns2)) ->
      all ns1 ex ns2 P^' ns1 ns2")
(assume "Base" "Step")
(ind)
(ex-intro (pt "0:"))
(use "Base")
(assume "n" "ns1" "IH")
(by-assume "IH" "ns2" "IH1")
(inst-with-to "Step" (pt "ns1") "Step1")
(ex-intro (pt "n::ns2"))
(use "Step1")
(use "IH1")
(extraction-test-et (current-proof))
;; Dialectica not yet properly implemented for allnc.

(remove-pvar-name "P")
(remove-var-name "ns")

;;----------------------------------------------------------------------
;; proof by list induction on general lists using predicate variables
;;----------------------------------------------------------------------

(add-pvar-name "P" (make-arity (py "list alpha") (py "list alpha")))

(set-goal
     "P(Nil alpha)(Nil alpha) ->
      all xs1,xs2,x(P xs1 xs2 -> P(x::xs1)(x::xs2)) ->
      all xs1 ex xs2 P xs1 xs2")
(assume "Base" "Step")
(ind)
(ex-intro (pt "(Nil alpha)"))
(use "Base")
(assume "x" "xs1" "IH")
(by-assume "IH" "xs2" "IH1")
(inst-with-to "Step" (pt "xs1") "Step1")
(ex-intro (pt "x::xs2"))
(use "Step1")
(use "IH1")
(extraction-test-et (current-proof))
;; Dialectica gives a contraction error, because of presence of pvars

(set-goal
     "P^'(Nil alpha)(Nil alpha) ->
      all xs1,xs2,x(P^' xs1 xs2 -> P^'(x::xs1)(x::xs2)) ->
      all xs1 ex xs2 P^' xs1 xs2")
(assume "Base" "Step")
(ind)
(ex-intro (pt "(Nil alpha)"))
(use "Base")
(assume "x" "xs1" "IH")
(by-assume "IH" "xs2" "IH1")
(inst-with-to "Step" (pt "xs1") "Step1")
(ex-intro (pt "x::xs2"))
(use "Step1")
(use "IH1")
(extraction-test-et (current-proof))
;; Dialectica gives a contraction error, because of presence of pvars

(set-goal
     "P^'(Nil alpha)(Nil alpha) ->
      allnc xs1,xs2,x(P^' xs1 xs2 -> P^'(x::xs1)(x::xs2)) ->
      all xs1 ex xs2 P^' xs1 xs2")
(assume "Base" "Step")
(ind)
(ex-intro (pt "(Nil alpha)"))
(use "Base")
(assume "x" "xs1" "IH")
(by-assume "IH" "xs2" "IH1")
(inst-with-to "Step" (pt "xs1") "Step1")
(ex-intro (pt "x::xs2"))
(use "Step1")
(use "IH1")
(extraction-test-et (current-proof))
;; Dialectica not yet properly implemented for allnc.

(remove-pvar-name "P")

;;----------------------------------------------------------------------
;; simple proof by induction using a weak existential
;;----------------------------------------------------------------------
(set-goal "all nat1 exca nat2 all nat3(nat1=nat3 -> nat2=nat3)")
(ind)
(assume "v")
(use "v" (pt "0"))
(assume "n" "u")
(use "u")
(assume "nat1" "IH" "v")
(use "v" (pt "Succ nat1"))
(assume "n" "u")
(use "u")
(extraction-test-etd (current-proof))

;; End of tests for extraction with realizability and Dialectica

;; Tests for functions related to soundness proofs involving inductive
;; and coinductive predicates.

(add-co "Even")
(add-mr-ids "Even")
(add-co "EvenMR")

(pp "CoEvenMRClause")

;; all n^,n^0(
;;  CoEvenMR n^ n^0 -> 
;;  n^ eqd 0 andnc n^0 eqd 0 ornc 
;;  exnc n^1,n^2(CoEvenMR n^1 n^2 andnc n^ eqd n^1+2 andnc n^0 eqd Succ n^2))

(set-goal "allnc n^,m^(EvenMR n^ m^ -> TotalNatNc m^)")
(assume "n^" "m^" "Enm")
(elim "Enm")
;; 3,4
(use "TotalNatNcZero")
;; 4
(assume "n^1" "m^1" "Useless")
(use "TotalNatNcSucc")
;; Proof finished.
;; (cdp)

(set-goal "allnc m^(exnc n^ CoEvenMR n^ m^ -> CoTotalNatNc m^)")
(assume "n^" "ExHyp")
(coind "ExHyp")
(drop "ExHyp")
(assume "m^2" "ExHyp2")
(by-assume "ExHyp2" "n^2" "n2Prop")
(inst-with-to "CoEvenMRClause" (pt "n^2") (pt "m^2") "n2Prop" "Inst")
(elim "Inst")
(drop "Inst")
(assume "Conjnc")
(intro 0)
(use "Conjnc")
;; 12
(drop "Inst")
(assume "ExHyp3")
(by-assume "ExHyp3" "n^3" "n3Prop")
(by-assume "n3Prop" "m^3" "n3m3Prop")
(intro 1)
(intro 0 (pt "m^3"))
(split)
(intro 1)
(intro 0 (pt "n^3"))
(use "n3m3Prop")
(use "n3m3Prop")
;; Proof finished.

;; Code discarded 2020-07-16.  GfpCoTotalNatMR and
;; CoTotalNatClauseSound removed, since axiom-to-soundness-proof
;; automatizes the generation of such proofs.  The rest is obsolete.

;; ;; OrDMRToDisj OrRMRToDisj AndLMRToConj added.  CoRecNat1 CoRecNat21
;; ;; CoRecNat22 added.  GfpCoTotalNatMR added: (CoRec nat nat) realizes
;; ;; the Gfp axiom for CoTotalNat.

;; ;; OrDMRToDisj (~ Half of Lemma on realizers for lor, case A,B cr)
;; (set-goal "allnc (beta1 ysum beta2)^(
;;  (OrDMR (cterm (beta1^0) (Pvar beta1)^1 beta1^0)
;;         (cterm (beta2^0) (Pvar beta2)^2 beta2^0))(beta1 ysum beta2)^ ->
;;  exnc beta1^((Pvar beta1)^1 beta1^ andnc
;;              (beta1 ysum beta2)^ eqd(InL beta1 beta2)beta1^)
;;  ornc
;;  exnc beta2^((Pvar beta2)^2 beta2^ andnc
;;              (beta1 ysum beta2)^ eqd(InR beta2 beta1)beta2^))")
;; (assume "(beta1 ysum beta2)^" "OrDMRHyp")
;; (elim "OrDMRHyp")
;; ;; 3,4
;; (assume "beta1^" "Pbeta1")
;; (intro 0)
;; (intro 0 (pt "beta1^"))
;; (split)
;; (use "Pbeta1")
;; (use "InitEqD")
;; ;; 4
;; (assume "beta2^" "Pbeta2")
;; (intro 1)
;; (intro 0 (pt "beta2^"))
;; (split)
;; (use "Pbeta2")
;; (use "InitEqD")
;; ;; Proof finished.
;; (save "OrDMRToDisj")
;; ;; (cdp)

;; ;; OrRMRToDisj (~ Half of Lemma on realizers for lor, case A nc and B cr)
;; (set-goal "allnc (uysum beta2)^(
;;  (OrRMR (cterm () Pvar^1) (cterm (beta2^0) (Pvar beta2)^2 beta2^0))
;;   (uysum beta2)^ ->
;;  (Pvar^1 andnc (uysum beta2)^ eqd(DummyL beta2)) ornc
;;  exnc beta2^((Pvar beta2)^2 beta2^ andnc (uysum beta2)^ eqd Inr beta2^))")
;; (assume "(uysum beta2)^" "OrRMRHyp")
;; (elim "OrRMRHyp")
;; (assume "P1")
;; (intro 0)
;; (split)
;; (use "P1")
;; (use "InitEqD")
;; ;; 4
;; (assume "beta2^" "Pbeta2")
;; (intro 1)
;; (intro 0 (pt "beta2^"))
;; (split)
;; (use "Pbeta2")
;; (use "InitEqD")
;; ;; Proof finished.
;; (save "OrRMRToDisj")
;; ;; (cdp)

;; ;; AndLMRToConj (~ Half of Lemma on realizers for land, case A cr and B nc)
;; (set-goal "allnc beta1^(
;;  (AndLMR (cterm (beta1^0) (Pvar beta1)^1 beta1^0) (cterm () Pvar^2))beta1^ ->
;;  (Pvar beta1)^1 beta1^ andnc Pvar^2)")
;; (assume "beta1^" "AndLMRHyp")
;; (elim "AndLMRHyp")
;; (assume "beta1^1" "P1Hyp" "P2Hyp")
;; (split)
;; (use "P1Hyp")
;; (use "P2Hyp")
;; ;; Proof finished.
;; (save "AndLMRToConj")
;; ;; (cdp)

;; (add-var-name "f" (py "nat=>uysum(nat ysum nat)"))
;; (add-var-name "w" (py "nat ysum nat"))

;; ;; CoRecNat1
;; (set-goal "all f^,n^(f^ n^ eqd(DummyL nat ysum nat) ->
;;  (CoRec nat=>nat)n^ f^ eqd 0)")
;; (assume "f^" "n^" "EqHyp")
;; (simp-with (make-proof-in-aconst-form
;; 	    (alg-or-arrow-types-to-corec-aconst (py "nat=>nat"))))
;; (ng)
;; (simp-with "EqHyp")
;; (ng)
;; (use "InitEqD")
;; ;; Proof finished.
;; (save "CoRecNat1")
;; ;; (cdp)

;; ;; CoRecNat21
;; (set-goal "all f^,n^,n^1(f^ n^ eqd((Inr((InL nat nat) n^1))) ->
;;  (CoRec nat=>nat)n^ f^ eqd Succ n^1)")
;; (assume "f^" "n^" "n^1" "EqHyp")
;; (simp-with (make-proof-in-aconst-form
;; 	    (alg-or-arrow-types-to-corec-aconst (py "nat=>nat"))))
;; (ng)
;; (simp-with "EqHyp")
;; (ng)
;; (use "InitEqD")
;; ;; Proof finished.
;; (save "CoRecNat21")
;; ;; (cdp)

;; ;; CoRecNat22
;; (set-goal "all f^,n^,n^1(f^ n^ eqd((Inr((InR nat nat) n^1))) ->
;;  (CoRec nat=>nat)n^ f^ eqd Succ((CoRec nat=>nat)n^1 f^))")
;; (assume "f^" "n^" "n^1" "EqHyp1")
;; (assert "all n^2(Succ((CoRec nat=>nat)n^1 f^) eqd n^2 ->
;;  (CoRec nat=>nat)n^ f^ eqd n^2)")
;;  (assume "n^2" "EqHyp2")
;;  (simp-with (make-proof-in-aconst-form
;;  	    (alg-or-arrow-types-to-corec-aconst (py "nat=>nat"))))
;;  (ng)
;;  (simp "EqHyp1")
;;  (ng)
;;  (use "EqHyp2")
;; (assume "Assertion")
;; (use "Assertion")
;; (use "InitEqD")
;; ;; Proof finished.
;; (save "CoRecNat22")
;; ;; (cdp)

;; (add-pvar-name "X" (make-arity (py "nat")))
;; (set! PVAR-TO-TVAR-ALIST
;;       (cons (list (predicate-form-to-predicate (pf "X nat")) (py "nat"))
;; 	     PVAR-TO-TVAR-ALIST))
;; (add-pvar-name "XMR" (make-arity (py "nat") (py "nat")))
;; (set! PVAR-TO-MR-PVAR-ALIST
;;       (cons (list (predicate-form-to-predicate (pf "X nat"))
;; 		  (predicate-form-to-predicate (pf "XMR^ nat nat")))
;; 	    PVAR-TO-MR-PVAR-ALIST))

;; ;; Caution: naming conventions require that the suffix MR of a theorem
;; ;; name indicates a clause name.

;; ;; CoRecGfpCoTotalNatMR (or CoRecCoTotalNatMR)
;; (set-goal (rename-variables
;; 	   (real-and-formula-to-mr-formula
;; 	    (pt "(CoRec nat=>nat)")
;; 	    (aconst-to-formula
;; 	     (imp-formulas-to-gfp-aconst (pf "X n^ -> CoTotalNat n^"))))))
;; (assume "n^" "m^" "XMRmn" "f^" "Step")
;; (use-with
;;  (make-proof-in-aconst-form
;;   (imp-formulas-to-gfp-aconst (pf "XMR^ m^ n^ -> CoTotalNatMR m^ n^")))
;;  (make-cterm
;;   (pv "m^1") (pv "n^1")
;;   (pf "exnc m^2(XMR^ m^2 n^1 andnc m^1 eqd((CoRec nat=>nat)m^2 f^))"))
;;  (pt "n^") (pt "((CoRec nat=>nat)m^ f^)")
;;  (pt "f^") "?" "?")
;; ;; 3,4
;; (drop "Step")
;; (intro 0 (pt "m^"))
;; (split)
;; (use "XMRmn")
;; (use "InitEqD")
;; ;; 4
;; (drop "XMRmn")
;; (assume "n^1" "m^1" "ExHyp")
;; (by-assume "ExHyp" "m^2" "n1m1Prop")
;; (elim "n1m1Prop")
;; (drop "n1m1Prop")
;; (assume "XMRm2n1" "m1Def")
;; (inst-with-to "Step" (pt "n^1") (pt "m^2") "XMRm2n1" "OrRMRHyp")
;; (drop "Step" "XMRm2n1")
;; (inst-with-to
;;  "OrRMRToDisj"
;;  (py "nat ysum nat")
;;  (make-cterm (pf "n^1 eqd 0"))
;;  (make-cterm
;;   (pv "w^")
;;   (real-and-formula-to-mr-formula
;;    (pt "w^")
;;    (pf "exr n^((CoTotalNat n^ ord X n^) andl n^1 eqd(Succ n^))")))
;;  (pt "f^ m^2")
;;  "OrRMRHyp"
;;  "OrRMRToDisjInst")
;; (drop "OrRMRHyp")
;; (elim "OrRMRToDisjInst")
;; ;; 23,24
;; (drop "OrRMRToDisjInst")
;; (assume "Conj1")
;; (intro 0)
;; (split)
;; (use "Conj1")
;; (simp "m1Def")
;; (use "CoRecNat1")
;; (use "Conj1")
;; ;; 24
;; (drop "OrRMRToDisjInst")
;; (assume "Conj1")
;; (by-assume "Conj1" "w^" "wProp")
;; (intro 1)
;; (elim "wProp")
;; (drop "wProp")
;; (assume "ExRHyp" "fm2Prop")
;; (inst-with-to
;;  "ExRMRElim" (py "nat ysum nat") (py "nat")
;;  (make-cterm
;;   (pv "w^")
;;   (pv "n^")
;;   (real-and-formula-to-mr-formula
;;    (pt "w^")
;;    (pf "(CoTotalNat n^ ord X n^) andl n^1 eqd(Succ n^)")))
;;  (pt "w^") (pt "n^") "ExRHyp"
;;  "Inst")
;; (drop "ExRHyp")
;; (by-assume "Inst" "n^2" "n2Prop")
;; (inst-with-to
;;  "AndLMRToConj"
;;  (py "nat ysum nat")
;;  (make-cterm (pv "w^") (pf "(OrDMR (cterm (n^) CoTotalNatMR n^ n^2)
;;                             (cterm (n^) XMR^ n^ n^2))w^"))
;;  (make-cterm (pf "n^1 eqd Succ n^2"))
;;  (pt "w^")
;;  "n2Prop"
;;  "AndLMRToConjInst")
;; (drop "n2Prop")
;; (elim "AndLMRToConjInst")
;; (drop "AndLMRToConjInst")
;; (assume "OrDMRHyp" "n1=Sn2")
;; (inst-with-to
;;  "OrDMRToDisj"
;;  (py "nat")
;;  (py "nat")
;;  (make-cterm
;;   (pv "n^")
;;   (real-and-formula-to-mr-formula
;;    (pt "n^")
;;    (pf "CoTotalNat n^2")))
;;  (make-cterm
;;   (pv "n^")
;;   (real-and-formula-to-mr-formula
;;    (pt "n^")
;;    (pf "X n^2")))
;;  (pt "w^")
;;  "OrDMRHyp"
;;  "OrDMRToDisjInst")
;; (drop "OrDMRHyp")
;; (elim "OrDMRToDisjInst")
;; ;; 56,57
;; (drop "OrDMRToDisjInst")
;; (assume "ExHyp1")
;; (intro 0 (pt "n^2"))
;; (by-assume "ExHyp1" "m^3" "m3Prop")
;; (intro 0 (pt "m^3"))
;; (split)
;; (intro 0)
;; (use "m3Prop")
;; (split)
;; (use "n1=Sn2")
;; (simp "m1Def")
;; (use "CoRecNat21")
;; (simp "fm2Prop")
;; (simp "m3Prop")
;; (ng #t)
;; (use "InitEqD")
;; ;; 57
;; (drop "OrDMRToDisjInst")
;; (assume "ExHyp2")
;; (intro 0 (pt "n^2"))
;; (by-assume "ExHyp2" "m^3" "m3Prop")
;; (intro 0 (pt "(CoRec nat=>nat)m^3 f^"))
;; (split)
;; (intro 1)
;; (intro 0 (pt "m^3"))
;; (split)
;; (use "m3Prop")
;; (use "InitEqD")
;; (split)
;; (use "n1=Sn2")
;; (simp "m1Def")
;; (use "CoRecNat22")
;; (simp "fm2Prop")
;; (simp "m3Prop")
;; (ng #t)
;; (use "InitEqD")
;; ;; Proof finished.
;; (save "CoRecGfpCoTotalNatMR")
;; ;; (cdp)

;; ;; We show that (Destr nat) realizes the closure aconst for the
;; ;; idpredconst CoTotalNat

;; ;; CoTotalNatClauseSound
;; (set-goal (rename-variables
;; 	   (real-and-formula-to-mr-formula
;; 	    (pt "(Destr nat)")
;; 	    (proof-to-formula
;; 	     (theorem-name-to-proof "CoTotalNatClause")))))
;; (assume "n^" "m^" "CoTMRmn")
;; (assert "CoEqPNatNc m^ n^")
;;  (use "CoTotalNatMRToCoEqPNatNc")
;;  (use "CoTMRmn")
;; (assume "m~n")
;; (assert "m^ eqd n^")
;; (use (make-proof-in-aconst-form (finalg-to-bisim-aconst (py "nat"))))
;;  (use "m~n")
;; (assume "m=n")
;; (simp "m=n")
;; (assert "CoTotalNatNc n^")
;;  (simp "<-" "m=n")
;;  (use "CoEqPNatNcToCoTotalNatNc" (pt "n^"))
;;  (use "m~n")
;; (assume "CoTn")
;; (inst-with-to "CoTotalNatNcClause" (pt "n^") "CoTn"
;; 	      "CoTotalNatNcClauseInst")
;; (elim "CoTotalNatNcClauseInst")
;; ;; 19.20
;; (drop "CoTotalNatNcClauseInst")
;; (assume "n=0")
;; (simp "n=0")
;; (ng #t)
;; (use "InlOrRMR")
;; (use "InitEqD")
;; ;; 20
;; (drop "CoTotalNatNcClauseInst")
;; (assume "ExHyp")
;; (by-assume "ExHyp" "n^1" "n1Prop")
;; (simp "n1Prop")
;; (ng #t)
;; (use "InrOrRMR")
;; (simp "<-" "n1Prop")
;; ;; (pp "InitExRMR")
;; (inst-with-to
;;  "InitExRMR" (py "nat") (py "nat")
;;  (make-cterm
;;   (pv "m^5") (pv "n^5")
;;   (pf "(AndLMR (cterm (n^3) CoTotalNatMR n^3 n^5) (cterm () n^ eqd Succ n^5))
;;        m^5"))
;;  "InitExRMRInst")
;; (use "InitExRMRInst" (pt "n^1"))
;; (drop "InitExRMRInst")
;; ;; (use "InitAndLMR")
;; (inst-with-to
;;  "InitAndLMR"
;;  (py "nat")
;;  (make-cterm (pv "n^0") (pf "CoTotalNatMR n^0 n^1"))
;;  (make-cterm (pf "n^ eqd Succ n^1"))
;;  (pt "n^1")
;;  "InitAndLMRInst")
;; (use "InitAndLMRInst")
;; (drop "InitAndLMRInst")
;; (use "CoEqPNatNcToCoTotalNatMR")
;; (use "CoTotalNatNcToCoEqPNatNc")
;; (use "n1Prop")
;; (use "n1Prop")
;; ;; Proof finished.
;; (save "CoTotalNatClauseSound")
;; ;; (cdp)

