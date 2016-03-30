;; (load "~/git/minlog/init.scm")
(load "names.scm")

; 10. Proofs
; ==========
; (proof.scm)

;; Tests for decorate.

(set-goal "A -> B -> A")
(assume "H1" "H2")
(use "H1")
;; Proof finished.

(define test (decorate (current-proof) (pf "A --> B --> A")))
;; (cdp test)

(pp (proof-to-formula test))
;; A -> B --> A

;; "AndRLemma"
(set-goal "A andd B -> B")
(assume "u")
(use "u")
;; Proof finished.
(save "AndRLemma")

(define proof (theorem-name-to-proof "AndRLemma"))
;; (cdp proof)
;; (proof-to-expr-with-formulas proof)

;; Elim: A andd B -> (A -> B -> B) -> B
;; u: A andd B
;; u0: A
;; u1: B

;; (lambda (u) ((Elim u) (lambda (u0) (lambda (u1) u1))))

(define decproof
  (fully-decorate (theorem-name-to-proof "AndRLemma")
		  (pf "A andu B -> B")))

(pp (proof-to-formula decproof))
;; A andr B -> B

(for-each pp (cdr (proof-to-final-allnc-elim-op-and-args
		   (mk-proof-in-elim-form
		    (make-proof-in-avar-form
		     (make-avar (pf "allnc p1,p2,p3 T") 7 "u"))
		    (pt "p4") (pt "p5") (pt "p6")))))
;; p4
;; p5
;; p6

;; Tests for normalization of proofs (via rec-at)

(add-pvar-name "S" (make-arity (py "boole") (py "nat")))

;; Induction with a parameter

(define proof (mk-proof-in-elim-form
	       (make-proof-in-aconst-form
		(all-formulas-to-ind-aconst (pf "all n S^ p n")))
	       (pt "p") (pt "Succ n")
	       (make-proof-in-avar-form
		(make-avar (pf "S^ p 0") -1 "u"))
	       (make-proof-in-avar-form
		(make-avar (pf "all n0(S^ p n0 -> S^ p(Succ n0))") -1 "v"))))
;; (proof-to-expr-with-formulas proof)

;; Ind: allnc p all n(S^ p 0 -> all n0(S^ p n0 -> S^ p(Succ n0)) -> S^ p n)
;; u: S^ p 0
;; v: all n(S^ p n -> S^ p(Succ n))

;; ((((Ind p) (+ n 1)) u) v)

(define nproof (np proof))
;; (cdp nproof)
;; (proof-to-expr-with-formulas nproof)
;; Ind: allnc p all n(S^ p 0 -> all n0(S^ p n0 -> S^ p(Succ n0)) -> S^ p n)
;; v: all n(S^ p n -> S^ p(Succ n))
;; u: S^ p 0

;; ((v n) ((((Ind p) n) u) v))

;; Tests for the corresponding proof using idpcs.

(pp (rename-variables
     (aconst-to-formula
      (imp-formulas-to-elim-aconst (pf "Even n^ -> S^ p n^")))))
;; allnc n^,p(
;;  Even n^ ->
;;  S^ p 0 -> allnc n^0(Even n^0 -> S^ p n^0 -> S^ p(n^0+2)) -> S^ p n^)

;; Note that the parameter p is bound after n^, not before (as with Ind)

(define proof (mk-proof-in-elim-form
	       (make-proof-in-aconst-form
		(imp-formulas-to-elim-aconst (pf "Even n^ -> S^ p n^")))
	       (pt "Succ(Succ n^)") (pt "negb p")
	       (mk-proof-in-elim-form
		(make-proof-in-aconst-form
		 (number-and-idpredconst-to-intro-aconst
		  1 (make-idpredconst "Even" '() '())))
		(pt "n^")
		(make-proof-in-avar-form
		 (make-avar (pf "Even n^") -1 "w")))
	       (make-proof-in-avar-form
		(make-avar (pf "S^(negb p)0") -1 "u"))
	       (make-proof-in-avar-form
		(make-avar
		 (pf "allnc n^0(
                       Even n^0 -> S^(negb p)n^0 -> S^(negb p)(n^0+2))")
		 -1 "v"))))

;; (cdp proof)
;; (proof-to-expr-with-formulas proof)
;; Elim: allnc n^,p(
;;  Even n^ ->
;;  S^ p 0 -> allnc n^0(Even n^0 -> S^ p n^0 -> S^ p(n^0+2)) -> S^ p n^)
;; Intro: allnc n^(Even n^ -> Even(n^ +2))
;; w: Even n^
;; u: S^(negb p)0
;; v: allnc n^(Even n^ -> S^(negb p)n^ -> S^(negb p)(n^ +2))

;; (((((Elim (+ (+ n^ 1) 1)) (not p)) ((Intro n^) w)) u) v)

(pp (proof-to-formula proof))
;; S^(negb p)(Succ(Succ n^))

(define nproof (np proof))

;; (cdp nproof)
;; (proof-to-expr-with-formulas nproof)
;; Elim: allnc n^,p(
;;  Even n^ ->
;;  S^ p 0 -> allnc n^0(Even n^0 -> S^ p n^0 -> S^ p(n^0+2)) -> S^ p n^)
;; v: allnc n^(Even n^ -> S^(negb p)n^ -> S^(negb p)(n^ +2))
;; w: Even n^
;; u: S^(negb p)0

;; (((v n^) w) (((((Elim n^) (not p)) w) u) v))

;; The same with a parameter in the idpc

(add-ids (list (list "I" (make-arity (py "boole") (py "nat")) "nat"))
	 '("allnc p^ I p^ 0" "InitI")
	 '("allnc p^,n^(I p^ n^ -> I p^(n^ +2))" "GenI"))

(add-var-name "q" (py "boole"))

(pp (rename-variables
     (aconst-to-formula
      (imp-formulas-to-elim-aconst (pf "I p^ n^ -> S q^ n^")))))

;; allnc p^,n^,q^(
;;  I p^ n^ ->
;;  allnc p^0 S q^ 0 ->
;;  allnc p^0,n^0(I p^0 n^0 -> S q^ n^0 -> S q^(n^0+2)) -> S q^ n^)

(define idpc
  (idpredconst-name-and-types-and-cterms-to-idpredconst "I" '() '()))

(pp (rename-variables
     (aconst-to-formula
      (number-and-idpredconst-to-intro-aconst 1 idpc))))
;; allnc p^,n^(I p^ n^ -> I p^(n^ +2))

(define proof
  (mk-proof-in-elim-form
   (make-proof-in-aconst-form
    (imp-formulas-to-elim-aconst (pf "I p^ n^ -> S q^ n^")))
   (pt "p^") (pt "n^ +2") (pt "negb q^")
   (mk-proof-in-elim-form
    (make-proof-in-aconst-form
     (number-and-idpredconst-to-intro-aconst 1 idpc))
    (pt "p^") (pt "n^")
    (make-proof-in-avar-form
     (make-avar (pf "I p^ n^") -1 "w")))
   (make-proof-in-avar-form
    (make-avar (pf "allnc p^ S(negb q^)0") -1 "u"))
   (make-proof-in-avar-form
    (make-avar (pf "allnc p^,n^(I p^ n^ -> S(negb q^)n^ -> S(negb q^)(n^ +2))")
	       -1 "v"))))

;; (cdp proof)
;; (proof-to-expr-with-formulas proof)
;; Elim: allnc p^,n^,q^(
;;  I p^ n^ ->
;;  allnc p^0 S q^ 0 ->
;;  allnc p^0,n^0(I p^0 n^0 -> S q^ n^0 -> S q^(n^0+2)) -> S q^ n^)
;; Intro: allnc p^,n^(I p^ n^ -> I p^(n^ +2))
;; w: I p^ n^
;; u: allnc p^ S(negb q^)0
;; v: allnc p^,n^(I p^ n^ -> S(negb q^)n^ -> S(negb q^)(n^ +2))

;; ((((((Elim p^) (+ n^ 2)) (not q^)) (((Intro p^) n^) w)) u) v)

(define nproof (np proof))
;; (cdp nproof)
;; (proof-to-expr-with-formulas nproof)
;; Elim: allnc p^,n^,q^(
;;  I p^ n^ ->
;;  allnc p^0 S q^ 0 ->
;;  allnc p^0,n^0(I p^0 n^0 -> S q^ n^0 -> S q^(n^0+2)) -> S q^ n^)
;; v: allnc p^,n^(I p^ n^ -> S(negb q^)n^ -> S(negb q^)(n^ +2))
;; w: I p^ n^
;; u: allnc p^ S(negb q^)0

;; ((((v p^) n^) w) ((((((Elim p^) n^) (not q^)) w) u) v))

(remove-var-name "q")
(remove-pvar-name "S")

;; Branch-labeled binary trees with a label at each branching node.

(add-var-name "t" (py "bbin alpha"))
(add-var-name "a" "b" (py "bbin nat"))
(add-pvar-name "P" (make-arity (py "nat") (py "bbin nat")))
(add-pvar-name "S" (make-arity (py "nat") (py "nat")))

(define elim-aconst
  (imp-formulas-to-elim-aconst
   (pf "(RTotalBbin (cterm (n^) S m^ n^))a^ -> P k^ a^")))

(pp (rename-variables (aconst-to-formula elim-aconst)))

;; allnc a^,m^,k^(
;;  (RTotalBbin (cterm (n^) S m^ n^))a^ ->
;;  P k^(BbinNil nat) ->
;;  allnc n^(
;;   S m^ n^ ->
;;   allnc a^0(
;;    (RTotalBbin (cterm (n^0) S m^ n^0))a^0 ->
;;    P k^ a^0 ->
;;    allnc a^1(
;;     (RTotalBbin (cterm (n^0) S m^ n^0))a^1 ->
;;     P k^ a^1 -> P k^((BbinBranch nat)n^ a^0 a^1)))) ->
;;  P k^ a^)

(define idpredconst
  (make-idpredconst
   "RTotalBbin"
   (list (py "nat")) (list (make-cterm (pv "n^") (pf "S m^ n^")))))

(define intro-aconst
  (number-and-idpredconst-to-intro-aconst 1 idpredconst))

(pp (rename-variables (aconst-to-formula intro-aconst)))

;; allnc m^,n^(
;;  S m^ n^ ->
;;  allnc a^(
;;   (RTotalBbin (cterm (n^0) S m^ n^0))a^ ->
;;   allnc a^0(
;;    (RTotalBbin (cterm (n^0) S m^ n^0))a^0 ->
;;    (RTotalBbin (cterm (n^0) S m^ n^0))((BbinBranch nat)n^ a^ a^0))))

;; Hand construction of a redex (as 2013-10-28)

(define proof
  (let ((u1 (make-avar (pf "S m^ n^") 1 "u"))
	(u2 (make-avar (pf "(RTotalBbin (cterm (n^) S m^ n^))a^") 2 "u"))
	(u3 (make-avar (pf "(RTotalBbin (cterm (n^) S m^ n^))b^") 3 "u"))
	(v0 (make-avar (pf "P k^(BbinNil nat)") 0 "v"))
	(v1 (make-avar (pf
"allnc n^(
  S m^ n^ ->
  allnc a^0(
   (RTotalBbin (cterm (n^0) S m^ n^0))a^0 ->
   P k^ a^0 ->
   allnc a^1(
    (RTotalBbin (cterm (n^0) S m^ n^0))a^1 ->
    P k^ a^1 -> P k^((BbinBranch nat)n^ a^0 a^1))))") 1 "v")))
    (mk-proof-in-elim-form
     (make-proof-in-aconst-form elim-aconst)
     (pt "(BbinBranch nat)n^ a^ b^") (pt "m^") (pt "k^")
     (mk-proof-in-elim-form
      (make-proof-in-aconst-form intro-aconst)
      (pt "m^") (pt "n^") (make-proof-in-avar-form u1)
      (pt "a^") (make-proof-in-avar-form u2)
      (pt "b^") (make-proof-in-avar-form u3))
     (make-proof-in-avar-form v0)
     (make-proof-in-avar-form v1))))

;; (cdp proof)
;; (proof-to-expr-with-formulas proof)
;; Elim: allnc a^,m^,k^(
;;  (RTotalBbin (cterm (n^) S m^ n^))a^ ->
;;  P k^(BbinNil nat) ->
;;  allnc n^(
;;   S m^ n^ ->
;;   allnc a^0(
;;    (RTotalBbin (cterm (n^0) S m^ n^0))a^0 ->
;;    P k^ a^0 ->
;;    allnc a^1(
;;     (RTotalBbin (cterm (n^0) S m^ n^0))a^1 ->
;;     P k^ a^1 -> P k^((BbinBranch nat)n^ a^0 a^1)))) ->
;;  P k^ a^)
;; Intro: allnc m^,n^(
;;  S m^ n^ ->
;;  allnc a^(
;;   (RTotalBbin (cterm (n^0) S m^ n^0))a^ ->
;;   allnc a^0(
;;    (RTotalBbin (cterm (n^0) S m^ n^0))a^0 ->
;;    (RTotalBbin (cterm (n^0) S m^ n^0))((BbinBranch nat)n^ a^ a^0))))
;; u1: S m^ n^
;; u2: (RTotalBbin (cterm (n^) S m^ n^))a^
;; u3: (RTotalBbin (cterm (n^) S m^ n^))b^
;; v0: P k^(BbinNil nat)
;; v1: allnc n^(
;;  S m^ n^ ->
;;  allnc a^(
;;   (RTotalBbin (cterm (n^0) S m^ n^0))a^ ->
;;   P k^ a^ ->
;;   allnc a^0(
;;    (RTotalBbin (cterm (n^0) S m^ n^0))a^0 ->
;;    P k^ a^0 -> P k^((BbinBranch nat)n^ a^ a^0))))

;; ((((((Elim (((BbinBranch n^) a^) b^)) m^) k^)
;;     (((((((Intro m^) n^) u1) a^) u2) b^) u3))
;;    v0)
;;   v1)

(define nproof (np proof))

;; (cdp nproof)
(proof-to-expr-with-formulas nproof)

;; Elim: allnc a^,m^,k^(
;;  (RTotalBbin (cterm (n^) S m^ n^))a^ -> 
;;  P k^(BbinNil nat) -> 
;;  allnc n^(
;;   S m^ n^ -> 
;;   allnc a^0(
;;    (RTotalBbin (cterm (n^0) S m^ n^0))a^0 -> 
;;    P k^ a^0 -> 
;;    allnc a^1(
;;     (RTotalBbin (cterm (n^0) S m^ n^0))a^1 -> 
;;     P k^ a^1 -> P k^((BbinBranch nat)n^ a^0 a^1)))) -> 
;;  P k^ a^)
;; v1: allnc n^(
;;  S m^ n^ -> 
;;  allnc a^(
;;   (RTotalBbin (cterm (n^0) S m^ n^0))a^ -> 
;;   P k^ a^ -> 
;;   allnc a^0(
;;    (RTotalBbin (cterm (n^0) S m^ n^0))a^0 -> 
;;    P k^ a^0 -> P k^((BbinBranch nat)n^ a^ a^0))))
;; u1: S m^ n^
;; u2: (RTotalBbin (cterm (n^) S m^ n^))a^
;; v0: P k^(BbinNil nat)
;; u3: (RTotalBbin (cterm (n^) S m^ n^))b^

;; ((((((((v1 n^) u1) a^) u2)
;;      ((((((Elim a^) m^) k^) u2) v0) v1))
;;     b^)
;;    u3)
;;   ((((((Elim b^) m^) k^) u3) v0) v1))

;; Note that in the elim-aconst variables are generalized in the order
;; idpc-arg-vars idpc-cterm-vars competitor-extra-vars

(remove-var-name "t" "a" "b")
(remove-pvar-name "P" "S")

;; Tests for aconst-rename

;; When normalizing a proof via nbe in the elim case the associated
;; rec constant has to accomodate the free variables in inst-formula
;; of the elim-aconst.  The tvars in their types may be affected by
;; the tpsubst of the elim-aconst.  When such a type clash occurs, we
;; rename type variables implicitly bound by tsubst away from tvars,
;; using aconst-rename.  Also unfold-totality is needed when
;; normalizing proofs with elim for totality.  Example:

(set-goal
 "allnc xs^((RTotalList (cterm (x^) Total x^)) xs^ -> exl n n=Lh(xs^))")
(assume "xs^" "Txs")
(elim "Txs")
;; Base
(intro 0 (pt "0"))
(use "Truth")
;; Step
(assume "x^" "Tx" "xs^1" "Txs1" "IH")
(by-assume "IH" "n" "IHn")
(intro 0 (pt "Succ n"))
(ng #t)
(use "IHn")
;; Proof finished.
;; (cdp) ;ok

;; (cdp (np (current-proof))) ;ok
;; (trace aconst-rename) ;is used here.

;; Remark: for debugging via trace it can be helpful to insert
;; reproduce for an item in a let list and then trace reproduce.

;; (define (reproduce x) x)
;; (trace reproduce)

;; Tests for rec-at when used for normalizing proofs with Elim/Intro.

;; We trace normalization of a simple proof involving the elimination
;; axiom for Even.  The proof is first translated into a term.  The
;; bound assumption variable u: Even n^ is translated into an object
;; variable.  Its type is nbeEven, an algebra newly created when Even
;; was added.  The constructors of nbeEven have types nbeEven and
;; nat=>nbeEven=>nbeEven (the latter for GenEven).  Note that in
;; contrast the type of the computational content of GenEven (more
;; precisely, its extracted term) is nat=>nat.  The elimination axiom
;; is translated into a recursion operator.

(add-pvar-name "P" (make-arity (py "nat")))

(set-goal "P 0 -> allnc n^(Even n^ -> P n^ -> P(n^ +2)) -> P 4")
(assume "Base" "Step")
(use (make-proof-in-aconst-form
      (imp-formulas-to-elim-aconst (pf "Even n^ -> P n^"))))
(use "GenEven")
(use "GenEven")
(use "InitEven")
(use "Base")
(use "Step")
;; Proof finished.

(proof-to-expr-with-formulas)

;; Elim: allnc n^(Even n^ -> P 0 -> allnc n^0(Even n^0 -> P n^0 -> P(n^0+2)) -> P n^)
;; Intro: allnc n^(Even n^ -> Even(n^ +2))
;; Intro: Even 0
;; Base: P 0
;; Step: allnc n^(Even n^ -> P n^ -> P(n^ +2))

;; (lambda (Base)
;;   (lambda (Step)
;;     ((((Elim 4) ((Intro 2) ((Intro 0) Intro))) Base) Step)))

;; To normalize this proof it is first translated into a term where
;; Elim is trabslated int an recursion operator.  Then this term in
;; normalized, and finally the result translated back ino a proof.
;; This is essentially done by nbe-normalize-proof-without-eta-aux .
;; It involves the following steps.

(define proof (current-proof))
;; (cdp proof)

(define formula (proof-to-formula proof))
(define genavars (append (proof-to-free-and-bound-avars proof)
		  (proof-to-aconsts-without-rules proof)))
(define vars (map (lambda (x)
	     (type-to-new-var
			(nbe-formula-to-type
			 (cond ((avar-form? x) (avar-to-formula x))
		     ((aconst-form? x) (aconst-to-formula x))
		     (else (myerror
			    "nbe-normalize-proof"
			    "genavar expected" x))))))
	   genavars))
(define genavar-var-alist (map list genavars vars))
(define var-genavar-alist (map list vars genavars))
(define pterm (proof-and-genavar-var-alist-to-pterm
	genavar-var-alist proof))
(define npterm (nbe-normalize-term-without-eta pterm))

(pp (rename-variables npterm))

;; [alpha526,(nat=>nbeEven=>alpha526=>alpha526)_0]
;;  (nat=>nbeEven=>alpha526=>alpha526)_0 2(Intro 0 Intro)
;;  ((nat=>nbeEven=>alpha526=>alpha526)_0 0 Intro alpha526)

(define nproof
  (npterm-and-var-genavar-alist-and-formula-to-proof
   npterm var-genavar-alist '() (unfold-formula formula)))
(proof-to-expr-with-formulas nproof)

;; Intro: allnc n^(Even n^ -> Even(n^ +2))
;; Intro: Even 0
;; u: P 0
;; u0: allnc n^(Even n^ -> P n^ -> P(n^ +2))

;; (lambda (u)
;;   (lambda (u0)
;;     (((u0 2) ((Intro 0) Intro)) (((u0 0) Intro) u))))

;; (cdp nproof)

;; .....allnc n^(Even n^ -> P n^ -> P(n^ +2)) by assumption u2183
;; .....2
;; ....Even 2 -> P 2 -> P(2+2) by allnc elim
;; ......allnc n^(Even n^ -> Even(n^ +2)) by axiom Intro
;; ......0
;; .....Even 0 -> Even(0+2) by allnc elim
;; .....Even 0 by axiom Intro
;; ....Even(0+2) by imp elim
;; ...P 2 -> P(2+2) by imp elim
;; ......allnc n^(Even n^ -> P n^ -> P(n^ +2)) by assumption u2183
;; ......0
;; .....Even 0 -> P 0 -> P(0+2) by allnc elim
;; .....Even 0 by axiom Intro
;; ....P 0 -> P(0+2) by imp elim
;; ....P 0 by assumption u2182
;; ...P(0+2) by imp elim
;; ..P(2+2) by imp elim
;; .allnc n^(Even n^ -> P n^ -> P(n^ +2)) -> P(2+2) by imp intro u2183
;; P 0 -> allnc n^(Even n^ -> P n^ -> P(n^ +2)) -> P(2+2) by imp intro u2182

(remove-pvar-name "P")

;; Tests for remove-predecided-if-theorems

(add-var-name "i" "j" (py "nat"))

;; TestThm
(set-goal "all i,j ex k(i<=k & j<=k)")
(assume "i" "j")
(use "If" (pt "i<=j"))
(assume "PosHyp1")
(ex-intro "j")
(split)
(use "PosHyp1")
(use "Truth")
(assume "NegHyp1")
(use "If" (pt "i<=j"))
(assume "PosHyp2")
(use "Efq")
(use "NegHyp1")
(use "PosHyp2")
(assume "NegHyp2")
(ex-intro "i")
(split)
(use "Truth")
(use "NatLtToLe")
(use "NatNotLeToLt")
(use "NegHyp2")
;; Proof finished
(save "TestThm")

(define testproof (theorem-name-to-proof "TestThm"))
(proof-to-expr-with-formulas testproof)
(pp (rename-variables (nt (proof-to-extracted-term testproof))))
;; [n,n0][if (n<=n0) n0 [if (n<=n0) 0 n]]

(define rem-testproof (remove-predecided-if-theorems testproof))
(proof-to-expr rem-testproof)
(pp (rename-variables (nt (proof-to-extracted-term rem-testproof))))
;; [n,n0][if (n<=n0) n0 n]

;; TestThm1
(set-goal "all i,j ex k(i<=k & j<=k)")
(assume "i" "j")
(use "If" (pt "i<=j"))
(assume "PosHyp1")
(ex-intro "j")
(split)
(use "PosHyp1")
(use "Truth")
(assume "NegHyp1")
(use "If" (pt "i<=j--Pred i"))
(assume "PosHyp2")
(use "Efq")
(use "NegHyp1")
(use "NatLeTrans" (pt "j--Pred i"))
(use "PosHyp2")
(ng)
(use "Truth")
(assume "NegHyp2")
(ex-intro "i")
(split)
(use "Truth")
(use "NatLtToLe")
(use "NatNotLeToLt")
(use "NegHyp1")
;; Proof finished
(save "TestThm1")

(define testproof1 (theorem-name-to-proof "TestThm1"))
(proof-to-expr-with-formulas testproof1)
(pp (rename-variables (nt (proof-to-extracted-term testproof1))))
;; [n,n0](cIf nat)(n<=n0)n0((cIf nat)(n<=n0--Pred n)0 n)

(define rem-testproof1 (remove-predecided-if-theorems testproof1))
(proof-to-expr rem-testproof1)
(pp (nt (proof-to-extracted-term rem-testproof1)))
;; [n0,n1](cIf nat)(n0<=n1)n1 n0

;; TestThm2
(set-goal "all i,j ex k(i<=k & j<=k)")
(assume "i" "j")
(use "If" (pt "i<=j--Pred i"))
(assume "PosHyp1")
(ex-intro "j")
(split)
(use "NatLeTrans" (pt "j--Pred i"))
(use "PosHyp1")
(ng)
(use "Truth")
(use "Truth")
(assume "NegHyp1")
(use "If" (pt "i<=j--Pred i--Pred(Pred i)"))
(assume "PosHyp2")
(use "Efq")
(use "NegHyp1")
(use "NatLeTrans" (pt "j--Pred i--Pred(Pred i)"))
(use "PosHyp2")
(use "NatLeTrans" (pt "j--Pred i--0"))
(use "NatLeMonMinus")
(use "Truth")
(use "Truth")
(use "Truth")
(assume "NegHyp2")
(ex-intro "i+j")
(split)
(ng)
(use "Truth")
(ng)
(use "Truth")
;; Proof finished
(save "TestThm2")

(define testproof2 (theorem-name-to-proof "TestThm2"))
(proof-to-expr-with-formulas testproof2)
(pp (rename-variables (nt (proof-to-extracted-term testproof2))))
;; [n,n0]
;;  (cIf nat)(n<=n0--Pred n)n0((cIf nat)(n<=n0--(Pred n+Pred(Pred n)))0(n+n0))

(define rem-testproof2 (remove-predecided-if-theorems testproof2))
(proof-to-expr rem-testproof2)
(pp (rename-variables (nt (proof-to-extracted-term rem-testproof2))))
;; [n,n0](cIf nat)(n<=n0--Pred n)n0(n+n0)

;; Tests for proof-to-one-step-reduct formula-and-psubsts-to-mon-proof

;; This is for hand normalization of proofs, including beta conversion
;; and idpredconst-elim-intro conversion.  The latter uses for nested
;; idpredconstants formula-and-psubsts-to-mon-proof .  An elim-intro
;; redex occurs when an elim aconst is applied to terms and the result
;; of applying an intro-aconst to terms and an idpc-proof.  This redex
;; is contracted as follows.  (1) Unnested idpredconst (s. 2013-10-03).
;; step-proof applied to idpc-params, intro-args and pd-proof:
;; elim-aconst applied to idpc-params, terms, intro-args and
;; step-proofs.  (2) Nested idpredconst (s. 2013-10-29).  step-proof
;; applied to idpc-params, intro-args and pd-proof: monotonicity proof
;; for the formula of intro-arg applied to terms, intro-arg and
;; sub-proofs.  The latter are obtained via andd-intros from
;; idpc-avars and elim-aconst applied to terms, idpc-avar and
;; step-proofs.  Here we test (2).

(add-var-name "a" (make-alg "ntree"))
(add-var-name "as" (make-alg "list" (make-alg "ntree")))
(add-totality "ntree")

(add-pvar-name "P" (make-arity (py "ntree")))

(display-idpc "RTotalList")

(set-goal "allnc as^((RTotalList (cterm (a^) TotalNtree a^))as^ ->
  allnc as^((RTotalList (cterm (a^) TotalNtree a^ andd P a^))as^ ->
  P(NBranch as^)) ->
  P(NBranch as^))")
(assume "as^" "IntroArg" "Step")
(use (make-proof-in-aconst-form
      (imp-formulas-to-elim-aconst (pf "TotalNtree a^ -> P a^"))))
(use "TotalNtreeNBranch")
(use "IntroArg")
(use "Step")
;; Proof finished

;; Now the test of proof-to-one-step-reduct

(define proof (current-proof))
;; (cdp proof) ;ok

(define nproof (proof-to-one-step-reduct proof))

;; (cdp nproof) ;ok

(remove-pvar-name "P")
(remove-var-name "a" "as")

;; Tests for aconst-substitute

;; We test (admissible) top-substitution in alltotal-elim-aconst and
;; alltotal-intro-aconst .

(pp (aconst-to-uninst-formula alltotal-elim-aconst))

;; all alpha (Pvar alpha)alpha ->
;; allnc alpha^(Total alpha^ -> (Pvar alpha)alpha^)

(pp (aconst-to-uninst-formula alltotal-intro-aconst))

;; allnc alpha^(Total alpha^ -> (Pvar alpha)alpha^) ->
;; all alpha (Pvar alpha)alpha

(define topsubst
  (make-substitution
   (list (py "alpha")
	 (pv "x")
	 (make-pvar (make-arity (py "alpha")) -1 0 0 ""))
   (list (py "nat")
	 (pt "n")
	 (make-cterm (pv "n^") (pf "(Pvar nat)n^")))))

(pp-subst topsubst)
;;   alpha -> nat
;;   x -> n
;;   (Pvar alpha) ->  (cterm (n^) (Pvar nat)n^)

(pp (rename-variables
     (aconst-to-formula (aconst-substitute alltotal-elim-aconst topsubst))))
;; all n (Pvar nat)n -> allnc n^(TotalNat n^ -> (Pvar nat)n^)

(pp (rename-variables
     (aconst-to-formula (aconst-substitute alltotal-intro-aconst topsubst))))
;; allnc n^(TotalNat n^ -> (Pvar nat)n^) -> all n (Pvar nat)n

;; Tests for proof-substitute for an aconst.

(add-pvar-name "P" (make-arity (py "list alpha")))
(add-pvar-name "S" (make-arity (py "nat")))

;; For testing, direct construction of the Cases aconst:

(define aconst0
  (make-aconst
   "Cases"
   'axiom
   (pf "all xs(P(Nil alpha) -> all x,xs P(x::xs) -> P xs)")
   (list (list (py "alpha") (py "list beta"))
	 (list (make-pvar (make-arity (py "list alpha"))
			  -1 h-deg-zero n-deg-zero "P")
	       (make-cterm (pv "list list beta")
			   (pf "Lh(list list beta)=n -> S m"))))
   (pf "all (list list beta)(Lh(list list beta)=n -> S m)")))

(check-aconst aconst0)

(pp-subst (aconst-to-tpsubst aconst0))
;;   alpha -> list beta
;;   P ->  (cterm ((list list beta)) Lh(list list beta)=n -> S m)

(cdp (proof-substitute
      (mk-proof-in-elim-form (make-proof-in-aconst-form aconst0)
			     (pt "n1") (pt "m1"))
      (list (list (py "beta") (py "boole")))))

(cdp (proof-substitute
      (mk-proof-in-elim-form (make-proof-in-aconst-form aconst0)
			     (pt "n1") (pt "m1"))
      (list (list (pv "n1") (pt "n2"))
	    (list (pv "m1") (pt "m2")))))

(cdp (proof-substitute
      (mk-proof-in-elim-form (make-proof-in-aconst-form aconst0)
			     (pt "n1") (pt "m1"))
      (list (list (py "beta") (py "boole"))
	    (list (pv "n1") (pt "n2"))
	    (list (pv "m1") (pt "m2")))))

(cdp (proof-substitute
      (mk-proof-in-elim-form (make-proof-in-aconst-form aconst0)
			     (pt "n1") (pt "m1"))
      (list (list (py "beta") (py "boole"))
	    (list (pv "n1") (pt "n2"))
	    (list (pv "m1") (pt "m2"))
	    (list (predicate-form-to-predicate (pf "S nat"))
		  (make-cterm (pv "n") (pf "n=m3"))))))

(remove-pvar-name "P" "S")

;; Generic example for proof-substitute for an aconst applied to args.

(add-var-name "b" (py "beta"))
(add-var-name "g" (py "beta=>beta"))
(add-pvar-name "P" (make-arity (py "beta")))

(define aconst
  (make-aconst "Testaconst" 'global-assumption (pf "F -> all x Q x")
	       (list (list (py "alpha") (py "beta"))
		     (list (make-pvar (make-arity (py "alpha")) -1 0 0 "Q")
			   (make-cterm (pv "b") (pf "P(g b)"))))))

(pp (rename-variables (aconst-to-formula aconst)))
;; allnc g(F -> all b P(g b))

(define proof
  (make-proof-in-allnc-elim-form
   (make-proof-in-aconst-form aconst)
   (pt "g1")))
(dp proof)
;; .allnc g(F -> all b78 P(g b78)) by global assumption Testaconst
;; .g1
;; F -> all b78 P(g1 b78) by allnc elim

(add-var-name "w" (py "gamma"))
(add-var-name "h" (py "gamma=>gamma"))
(add-pvar-name "S" (make-arity (py "gamma")))

(define topasubst
  (list (list (py "beta") (py "gamma"))
	(list (pv "g1") (pt "h1"))
	(list (make-pvar (make-arity (py "beta")) -1 0 0 "P")
	      (make-cterm (pv "w") (pf "S(h w)")))))

(pp-subst topasubst)
;;   beta -> gamma
;;   g1 -> h1
;;   P ->  (cterm (w) S(h w))

(dp (proof-substitute proof topasubst))
;; ..allnc h,h1(F -> all w83 S(h(h1 w83))) by global assumption Testaconst
;; ..h
;; .allnc h1(F -> all w83 S(h(h1 w83))) by allnc elim
;; .h1
;; F -> all w83 S(h(h1 w83)) by allnc elim

(remove-var-name "h" "w" "g" "b")
(remove-pvar-name "P" "S")

;; Tests for formula-to-efq-proof

(define proof (formula-to-efq-proof (pf "Even 0")))

;; (cdp proof)

(add-co "Even")

(define proof (formula-to-efq-proof (pf "CoEven 0")))
;; (cdp proof)

(define nproof (np proof))
;; (cdp nproof) ;ok
(pp (rename-variables (proof-to-extracted-term nproof)))
;; (CoRec nat)(DummyL nat ysumu)

;; Tests for make-proof-in-iterated-imp-elim-form

(define init-proof
  (make-proof-in-avar-form (formula-to-new-avar (pf "Pvar1"))))

(define imp-proofs
  (list (make-proof-in-avar-form (formula-to-new-avar (pf "Pvar1 --> Pvar2")))
	(make-proof-in-avar-form (formula-to-new-avar (pf "Pvar2 -> Pvar3")))
	(make-proof-in-avar-form (formula-to-new-avar (pf "Pvar3 --> Pvar4")))
	(make-proof-in-avar-form (formula-to-new-avar (pf "Pvar4 -> Pvar5")))))

(define proof
  (apply make-proof-in-iterated-imp-elim-form init-proof imp-proofs))
(proof-to-expr-with-formulas proof)
;; u2184: Pvar4 -> Pvar5
;; u2185: Pvar3 --> Pvar4
;; u2186: Pvar2 -> Pvar3
;; u2187: Pvar1 --> Pvar2
;; u2179: Pvar1

;; (u2184 (u2185 (u2186 (u2187 u2179))))

;; Tests for formula-and-falsity-avar-to-efq-proof

(cdp (formula-and-falsity-avar-to-efq-proof
      (pf "boole1 eqd boole2") (make-avar (pf "F") -1 "")))

(cdp (formula-and-falsity-avar-to-efq-proof
      (pf "TotalBoole boole^") (make-avar (pf "F") -1 "")))

;; Tests for eqd-proofs-and-predicate-proof-to-proof

;; Given eqd-proofs of r1 eqd s1, ..., rn eqd sn and a predicate-proof
;; of I r1 ... rn we construct a proof of I s1 ... sn using EqDCompat

(define predicate-proof
  (make-proof-in-avar-form
   (formula-to-new-avar (pf "(Pvar nat nat nat) n1 n2 n3"))))

(define eqd-proofs
  (list (make-proof-in-avar-form (formula-to-new-avar (pf "n1 eqd m1")))
	(make-proof-in-avar-form (formula-to-new-avar (pf "n2 eqd m2")))
	(make-proof-in-avar-form (formula-to-new-avar (pf "n3 eqd m3")))))

(define proof
  (eqd-proofs-and-predicate-proof-to-proof eqd-proofs predicate-proof))

;; (cdp proof)
;; (proof-to-expr-with-formulas proof)

;; EqDCompat: allnc m,m0,n^,n^0(
;;  n^ eqd n^0 --> (Pvar nat nat nat)m m0 n^ -> (Pvar nat nat nat)m m0 n^0)
;; EqDCompat: allnc m,n,n^0,n^1(
;;  n^0 eqd n^1 --> (Pvar nat nat nat)m n^0 n -> (Pvar nat nat nat)m n^1 n)
;; EqDCompat: allnc n,n0,n^1,n^2(
;;  n^1 eqd n^2 --> (Pvar nat nat nat)n^1 n n0 -> (Pvar nat nat nat)n^2 n n0)
;; u2191: n3 eqd m3
;; u2189: n2 eqd m2
;; u2190: n1 eqd m1
;; u2188: (Pvar nat nat nat)n1 n2 n3

;; ((((((EqDCompat m1) m2) n3) m3) u2191)
;;   ((((((EqDCompat m1) n3) n2) m2) u2189)
;;     ((((((EqDCompat n2) n3) n1) m1) u2190) u2188)))

