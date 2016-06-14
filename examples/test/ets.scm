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
;; obtained by formula-to-efq-proof

(define proof
  (formula-to-efq-proof (pf "(RTotalLtlist (cterm (n^) P n^))(ltlist nat)^")))

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
(add-mr-ids "TotalBin")

(display-idpc "TotalBin")
 ;; 	TotalBinBinNil:	TotalBin BinNil
 ;; 	TotalBinBinBranch:	allnc a^(
 ;; TotalBin a^ -> allnc a^0(TotalBin a^0 -> TotalBin(BinBranch a^ a^0)))

(display-idpc "TotalBinMR")
 ;; 	TotalBinBinNilMR:	TotalBinMR BinNil BinNil
 ;; 	TotalBinBinBranchMR:	allnc a^,a^0(
 ;; TotalBinMR a^0 a^ -> 
 ;; allnc a^1,a^2(
 ;;  TotalBinMR a^2 a^1 -> TotalBinMR(BinBranch a^0 a^2)(BinBranch a^ a^1)))

(add-pvar-name "P" (make-arity (py "bin")))

(define proof (imp-formulas-to-mr-elim-proof (pf "TotalBin a^ -> P a^")))
;; (cdp proof)

(remove-pvar-name "P")

;; Tests for more general situations.
;; 1.  Parameter in the conclusion of imp-formula

(add-pvar-name "P" (make-arity (py "nat") (py "bin")))

(define proof (imp-formulas-to-mr-elim-proof (pf "TotalBin a^ -> P l^ a^")))
;; (cdp proof)

(remove-pvar-name "P")

;; 2.  Inductive predicate with param-pvar substituted by cterm with param
;; Take RTotalList

(add-mr-ids "RTotalList")

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
(add-mr-ids "TotalTree")

(add-pvar-name "S" (make-arity (py "tlist")))
(add-pvar-name "P" (make-arity (py "tree")))

(add-var-name "ts" (py "tlist"))
(add-var-name "t" (py "tree"))

(define proof (imp-formulas-to-mr-elim-proof
	       (pf "TotalTree t^ -> P t^") (pf "TotalTlist ts^ -> S ts^")))
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
	       (pf "ex x^ (Pvar alpha)^ x^") (pf "Pvar")))
;; (cdp proof)
(pp (rename-variables (proof-to-formula proof)))

;; all x^(
;;  (Pvar alpha)^ x^ -> 
;;  all (alpha=>beta)^(
;;   all x^0((Pvar alpha)^ x^0 -> (Pvar beta)^((alpha=>beta)^ x^0)) -> 
;;   (Pvar beta)^((alpha=>beta)^ x^)))

(define proof (ex-formula-and-concl-to-ex-elim-mr-proof
	       (pf "ex x^ (Pvar alpha) x^") (pf "Pvar")))
;; (cdp proof)
(pp (rename-variables (proof-to-formula proof)))

;; all (alpha@@gamma)^(
;;  (Pvar gamma alpha)^(right(alpha@@gamma)^)(left(alpha@@gamma)^) -> 
;;  all (alpha=>gamma=>beta)^0(
;;   all x^,gamma^1(
;;    (Pvar gamma alpha)^ gamma^1 x^ -> 
;;    (Pvar beta)^((alpha=>gamma=>beta)^0 x^ gamma^1)) -> 
;;   (Pvar beta)^
;;   ((alpha=>gamma=>beta)^0 left(alpha@@gamma)^ right(alpha@@gamma)^)))

;; Test of exr-formula-and-concl-to-exr-elim-mr-proof
(define proof (exr-formula-and-concl-to-exr-elim-mr-proof
	       (pf "exr p^ Y p^") (pf "Pvar")))
;; (cdp proof)

(pp (rename-variables (proof-to-formula proof)))

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

;; Test of andl-formula-and-concl-to-andl-elim-mr-proof

(remove-pvar-name "Y")
(add-pvar-name "Y" "Z" (make-arity))
(define proof (andlr-formula-and-concl-to-andlr-elim-mr-proof
	       (pf "Pvar^ andr Y") (pf "Z")))
;; (cdp proof)

(pp (rename-variables (proof-to-formula proof)))

;; all alpha1103^(
;;  (AndRMR (cterm () Pvar^)
;;    (cterm (alpha1103^0) (Pvar alpha1103)^498 alpha1103^0))
;;  alpha1103^ -> 
;;  all (alpha1103=>alpha1081)^0(
;;   (Pvar^ --> 
;;    all alpha1103^1(
;;     (Pvar alpha1103)^498 alpha1103^1 -> 
;;     (Pvar alpha1081)^497((alpha1103=>alpha1081)^0 alpha1103^1))) -> 
;;   (Pvar alpha1081)^497((alpha1103=>alpha1081)^0 alpha1103^)))

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

(define proof (imp-formulas-to-mr-elim-proof (pf "TotalPos q^ -> P q^")))
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

(define sproof (proof-to-soundness-proof "PosSTotal"))
;; (cdp sproof)

(define proof
  (imp-formulas-to-mr-elim-proof (pf "TotalPos q^ -> TotalPos(PosS q^)")))
;; (cdp proof)

(remove-var-name "q")
(remove-pvar-name "P")

;; Tests of proof-to-soundness-proof

(define proof
  (make-proof-in-imp-elim-form
   (make-proof-in-avar-form
    (make-avar (pf "Pvar1 -> Pvar2") -1 "u"))
   (make-proof-in-avar-form
    (make-avar (pf "Pvar1") -1 "v"))))

(cdp (proof-to-soundness-proof proof))

(define proof
  (make-proof-in-imp-elim-form
   (make-proof-in-avar-form
    (make-avar (pf "Pvar^1 -> Pvar2") -1 "u"))
   (make-proof-in-avar-form
    (make-avar (pf "Pvar^1") -1 "v"))))

(cdp (proof-to-soundness-proof proof))

(define proof
  (make-proof-in-imp-intro-form
   (make-avar (pf "Pvar^1") -1 "v")
   (make-proof-in-imp-elim-form
    (make-proof-in-avar-form
     (make-avar (pf "Pvar^1 -> Pvar2") -1 "u"))
    (make-proof-in-avar-form
     (make-avar (pf "Pvar^1") -1 "v")))))

(cdp (proof-to-soundness-proof proof))

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

(set-goal "F -> Pvar")
(use "Efq")
(cdp (proof-to-soundness-proof))

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

;; proof-to-soundness-proof

(add-co "TotalBoole")
;; (add-mr-ids "TotalBoole") ;already in lib/nat.scm
(add-co "TotalBooleMR")
(add-co "TotalNat")
(add-co "TotalNatMR")
;; (add-totality "bin") ;already above
;; (add-mr-ids "TotalBin") ;already above
(add-co "TotalBin")
(add-co "TotalBinMR")
(add-totality "ordl")
(add-mr-ids "TotalOrdl")
(add-co "TotalOrdl")
(add-co "TotalOrdlMR")
(add-totality "intv")
(add-mr-ids "TotalIntv")
(add-co "TotalIntv")
(add-co "TotalIntvMR")
(add-co "TotalList")
(add-co "TotalListMR")
;; (add-mr-ids "RTotalList") ;already above
(add-co "RTotalList")
(add-co "RTotalListMR")
(add-totality "ntree")
(add-co "TotalNtree")
;; (add-mr-ids "TotalNtree")
;; types-to-embedding
;; increasing types expected
;; alpha1492
;; ntree

;; (add-co "TotalNtreeMR")
(add-totality "ltlist")
(add-mr-ids "TotalLtlist")
(add-co "TotalLtlist")
(add-co "TotalLtlistMR")
(add-mr-ids "RTotalLtlist")
(add-co "RTotalLtlist")
(add-co "RTotalLtlistMR")

(set! COMMENT-FLAG #f)
;; closure axioms
(define coidpc (predicate-form-to-predicate (pf "CoTotalBoole boole^")))
(define proof (coidpredconst-to-closure-mr-proof coidpc))
(pp (rename-variables (proof-to-formula proof)))

;; all p^,p^0(
;;  CoTotalBooleMR p^0 p^ -> 
;;  (OrUMR (cterm () p^ eqd True) (cterm () p^ eqd False))(Des p^0))

(proof-to-expr-with-formulas proof)

(define coidpc (predicate-form-to-predicate (pf "CoTotalNat nat^")))
;; (define proof (coidpredconst-to-closure-mr-proof coidpc))
;; Exception in cdr: () is not a pair

;; check coidpredconst-to-closure-mr-proof-or-elim

;; Same error in all other examples
(define coidpc (predicate-form-to-predicate (pf "CoTotalBin bin^")))
;; (define proof (coidpredconst-to-closure-mr-proof coidpc))

;; (cdp proof)

;; (define coidpc (predicate-form-to-predicate (pf "CoTotalList (list alpha)^")))
;; (define proof (coidpredconst-to-closure-mr-proof coidpc))
;; (cdp proof)

;; (define coidpc
;;   (predicate-form-to-predicate
;;    (pf "(CoRTotalList (cterm (nat^) TotalNat nat^))(list nat)^")))
;; (define proof (coidpredconst-to-closure-mr-proof coidpc))
;; (cdp proof)

;; (define coidpc
;;   (predicate-form-to-predicate
;;    (pf "(CoRTotalList (cterm (alpha^) (Pvar alpha)alpha^))(list alpha)^")))
;; (define proof (coidpredconst-to-closure-mr-proof coidpc))
;; (cdp proof)

;; (define coidpc (predicate-form-to-predicate (pf "CoTotalNtree ntree^")))
;; (define proof (coidpredconst-to-closure-mr-proof coidpc))
;; (cdp proof)

;; (define coidpc (predicate-form-to-predicate (pf "CoTotalIntv intv^")))
;; (define proof (coidpredconst-to-closure-mr-proof coidpc))
;; (cdp proof)

;; (define coidpc (predicate-form-to-predicate (pf "CoTotalOrdl ordl^")))
;; (define proof (coidpredconst-to-closure-mr-proof coidpc))
;; (cdp proof)

;; (define coidpc (predicate-form-to-predicate (pf "CoTotalLtlist(ltlist alpha)^")))
;; (define proof (coidpredconst-to-closure-mr-proof coidpc))
;; (cdp proof)

;; (define coidpc (predicate-form-to-predicate (pf "CoTotalLtree(ltree alpha)^")))
;; (define proof (coidpredconst-to-closure-mr-proof coidpc))
;; (cdp proof)

;; (define coidpc
;;   (predicate-form-to-predicate
;;    (pf "(CoRTotalLtlist (cterm (alpha^) (Pvar alpha)alpha^))(ltlist alpha)^")))
;; (define proof (coidpredconst-to-closure-mr-proof coidpc))
;; (cdp proof)

;; (define coidpc
;;   (predicate-form-to-predicate
;;    (pf "(CoRTotalLtree (cterm (alpha^) (Pvar alpha)alpha^))(ltree alpha)^")))
;; (define proof (coidpredconst-to-closure-mr-proof coidpc))
;; (cdp proof)

;; gfp axioms
(define imp-formulas
  (list (pf "(Pvar boole)boole^ -> CoTotalBoole boole^")))
;; (define proof (apply imp-formulas-to-mr-gfp-proof imp-formulas))
;; make-term-in-app-form
;; unexpected terms.  Operator:
;; (CoRec alpha1572=>boole)alpha1572^9609
;; with argument type
;; alpha1572=>boole
;; Argument:
;; alpha1572^9606
;; of type
;; alpha1572

;; (cdp proof)

;; Same error in all other examples
;; (define imp-formulas (list (pf "(Pvar nat)n^ -> CoTotalNat n^")))
;; (define proof (apply imp-formulas-to-mr-gfp-proof imp-formulas))
;; (cdp proof)

;; (define imp-formulas (list (pf "(Pvar bin)bin^ -> CoTotalBin bin^")))
;; (define proof (apply imp-formulas-to-mr-gfp-proof imp-formulas))
;; (cdp proof)

;; (define imp-formulas (list (pf "(Pvar intv)intv^ -> CoTotalIntv intv^")))
;; (define proof (apply imp-formulas-to-mr-gfp-proof imp-formulas))
;; (cdp proof)

;; (define imp-formulas
;;   (list (pf "(Pvar (list nat))(list nat)^ -> (CoRTotalList (cterm (n^) (Pvar nat)n^))list nat^")))
;; (define proof (apply imp-formulas-to-mr-gfp-proof imp-formulas))
;; (cdp proof)

(set! COMMENT-FLAG #t)
