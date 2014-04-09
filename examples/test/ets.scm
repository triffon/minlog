;; (load "~/minlog/init.scm")
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

;; 2012-11-09.  End of file testsound.scm

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
(extraction-test (current-proof))

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
(extraction-test (current-proof))

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
