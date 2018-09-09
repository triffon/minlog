;; (load "~/git/minlog/init.scm")
(load "names.scm")

(define testidpcs
  (list
   ;; idpcs in ets.scm
   (idpredconst-name-and-types-and-cterms-to-idpredconst "TotalUnit" '() '())
   (idpredconst-name-and-types-and-cterms-to-idpredconst "TotalBoole" '() '())
   (idpredconst-name-and-types-and-cterms-to-idpredconst
    "TotalYprod" (list (py "alpha1") (py "alpha2")) '())
   (idpredconst-name-and-types-and-cterms-to-idpredconst
    "TotalYsum" (list (py "alpha1") (py "alpha2")) '())
   (idpredconst-name-and-types-and-cterms-to-idpredconst
    "TotalUysum" (list (py "alpha")) '())
   (idpredconst-name-and-types-and-cterms-to-idpredconst
    "TotalYsumu" (list (py "alpha")) '())
   (idpredconst-name-and-types-and-cterms-to-idpredconst
    "EqD" (list (py "alpha")) '())
   (idpredconst-name-and-types-and-cterms-to-idpredconst
    "ExD" (list (py "alpha")) (list (make-cterm (pv "x^") (pf "Q x^"))))
   (idpredconst-name-and-types-and-cterms-to-idpredconst
    "ExL" (list (py "alpha")) (list (make-cterm (pv "x^") (pf "Q x^"))))
   (idpredconst-name-and-types-and-cterms-to-idpredconst
    "ExR" (list (py "alpha")) (list (make-cterm (pv "x^") (pf "Q x^"))))
   (idpredconst-name-and-types-and-cterms-to-idpredconst
    "ExNc" (list (py "alpha")) (list (make-cterm (pv "x^") (pf "Q x^"))))
   (idpredconst-name-and-types-and-cterms-to-idpredconst
    "ExDT" (list (py "alpha")) (list (make-cterm (pv "x") (pf "Q x"))))
   (idpredconst-name-and-types-and-cterms-to-idpredconst
    "ExLT" (list (py "alpha")) (list (make-cterm (pv "x") (pf "Q x"))))
   (idpredconst-name-and-types-and-cterms-to-idpredconst
    "ExRT" (list (py "alpha")) (list (make-cterm (pv "x") (pf "Q x"))))
   (idpredconst-name-and-types-and-cterms-to-idpredconst
    "ExNcT" (list (py "alpha")) (list (make-cterm (pv "x") (pf "Q x"))))
   (idpredconst-name-and-types-and-cterms-to-idpredconst
    "AndD" '() (list (make-cterm (pf "A")) (make-cterm (pf "B"))))
   (idpredconst-name-and-types-and-cterms-to-idpredconst
    "AndL" '() (list (make-cterm (pf "A")) (make-cterm (pf "B"))))
   (idpredconst-name-and-types-and-cterms-to-idpredconst
    "AndR" '() (list (make-cterm (pf "A")) (make-cterm (pf "B"))))
   (idpredconst-name-and-types-and-cterms-to-idpredconst
    "AndNc" '() (list (make-cterm (pf "A")) (make-cterm (pf "B"))))
   (idpredconst-name-and-types-and-cterms-to-idpredconst
    "OrD" '() (list (make-cterm (pf "A")) (make-cterm (pf "B"))))
   (idpredconst-name-and-types-and-cterms-to-idpredconst
    "OrL" '() (list (make-cterm (pf "A")) (make-cterm (pf "B"))))
   (idpredconst-name-and-types-and-cterms-to-idpredconst
    "OrR" '() (list (make-cterm (pf "A")) (make-cterm (pf "B"))))
   (idpredconst-name-and-types-and-cterms-to-idpredconst
    "OrU" '() (list (make-cterm (pf "A")) (make-cterm (pf "B"))))
   ;; idpcs in lib/nat.scm
   (idpredconst-name-and-types-and-cterms-to-idpredconst "TotalNat" '() '())
   ;; (idpredconst-name-and-types-and-cterms-to-idpredconst "TotalNatMR" '() '())
   ;; idpcs in lib/list.scm
   (idpredconst-name-and-types-and-cterms-to-idpredconst
    "TotalList" (list (py "alpha")) '())
   ;; (idpredconst-name-and-types-and-cterms-to-idpredconst
   ;;  "TotalListMR" (list (py "alpha")) '())
   (idpredconst-name-and-types-and-cterms-to-idpredconst
    "RTotalList"
    (list (py "alpha")) (list (make-cterm (pv "x^") (pf "Q1 x^"))))
   (idpredconst-name-and-types-and-cterms-to-idpredconst
    "STotalList" (list (py "alpha")) '())
   (idpredconst-name-and-types-and-cterms-to-idpredconst
    "STotalListMR" (list (py "alpha")) '())
   ;; defined idpcs
   (idpredconst-name-and-types-and-cterms-to-idpredconst "Even" '() '())
   (idpredconst-name-and-types-and-cterms-to-idpredconst "Ev" '() '())
   (idpredconst-name-and-types-and-cterms-to-idpredconst "Od" '() '())
   (idpredconst-name-and-types-and-cterms-to-idpredconst
    "PiOne" (list (py "alpha"))
    (list (make-cterm (pv "x^") (pv "y^") (pf "R x^ y^"))))
   (idpredconst-name-and-types-and-cterms-to-idpredconst
    "TrCl" (list (py "alpha"))
    (list (make-cterm (pv "x^") (pv "y^") (pf "R x^ y^"))))
   (idpredconst-name-and-types-and-cterms-to-idpredconst
    "Acc" (list (py "alpha")) '())
   (idpredconst-name-and-types-and-cterms-to-idpredconst
    "Cup" (list (py "alpha")) (list (make-cterm (pv "x^") (pf "Q1 x^"))
				    (make-cterm (pv "x^") (pf "Q2 x^"))))
   (idpredconst-name-and-types-and-cterms-to-idpredconst
    "Cap" (list (py "alpha")) (list (make-cterm (pv "x^") (pf "Q1 x^"))
				    (make-cterm (pv "x^") (pf "Q2 x^"))))
   ))

(define testidpcnames (map idpredconst-to-name testidpcs))

;; Tests for add-ids (introducing inductively defined predicates)

(map car (alg-name-to-typed-constr-names "algEv"))
;; ("CInitEv" "CGenEv")
(map car (alg-name-to-typed-constr-names "algOd"))
;; ("CGenOd")

;; However, here we get an error:

;; (add-ids
;;  (list (list "One" (make-arity (py "nat")) "algOne")
;;        (list "Two" (make-arity (py "nat")) "algTwo"))
;;  '("allnc n One(2*n)" "InitOne")
;;  '("allnc n(One n -> Two(2*n))" "InitTwo"))

;; unnecessary simultaneous definition for alpha114

;; The clauses for EqD contain the type variable alpha, which can be
;; substituted by itself.

(define idpc
  (idpredconst-name-and-types-and-cterms-to-idpredconst
   "EqD" (list (py "alpha")) '()))

(pp (make-predicate-formula idpc (pt "x^1")  (pt "x^2")))
;; "x^1 eqd x^2"

;; ... or else can be substituted e.g. by nat

(define idpc-inst
  (idpredconst-name-and-types-and-cterms-to-idpredconst
   "EqD" (list (py "nat")) '()))

(pp (make-predicate-formula idpc-inst (pt "n1") (pt "n2")))
;; "n1 eqd n2"

;; The clauses for OrD contain the parameter predicate variables A and
;; B, which can be substituted by themselves.

(define idpc
  (idpredconst-name-and-types-and-cterms-to-idpredconst
   "OrD" '()
   (list (make-cterm (pf "A")) (make-cterm (pf "B")))))

(pp (make-predicate-formula idpc))
;; A ord B

;; ... or else can be substituted e.g. {|T} and {|F}

(define idpc-inst
  (idpredconst-name-and-types-and-cterms-to-idpredconst
   "OrD" '() (list  (make-cterm (pf "T")) (make-cterm (pf "F")))))

(pp (make-predicate-formula idpc-inst))
;; T ord F

;; We need decorated inductively defined existential quantifiers, for
;; instance (ExD with D for double) for a kernel with computational
;; content, and one (ExL with L for left) for a kernel without.  The
;; reason is to avoid garbage in extracted programs.

(define idpc (predicate-form-to-predicate (pf "exd n n=m")))
(idpredconst-to-string idpc)
;; "exd n n=m"

(define idpc (predicate-form-to-predicate (pf "exl p1 p1=p2")))
(idpredconst-to-string idpc)
;; "exl p1 p1=p2"

;; The transitive closure of a relation.

(display-idpc "TrCl")

;; TrCl
;; 	InitTrCl:	allnc x^,y^(R x^ y^ -> (TrCl (cterm (x^0,x^1) R x^0 x^1))x^ y^)
;; 	GenTrCl:	allnc x^,y^,z^(
;;  R x^ y^ ->
;;  (TrCl (cterm (x^0,x^1) R x^0 x^1))y^ z^ ->
;;  (TrCl (cterm (x^0,x^1) R x^0 x^1))x^ z^)

;; Here the clauses contain the type variable alpha and the parameter
;; predicate variable R, which can be substituted by themselves

(define idpc
  (idpredconst-name-and-types-and-cterms-to-idpredconst
   "TrCl"
   (list (py "alpha"))
   (list (make-cterm (pv "x^1") (pv "x^2") (pf "R x^1 x^2")))))

(pp (make-predicate-formula idpc (pt "x^3") (pt "x^4")))
;; (TrCl (cterm (x^1,x^2) R x^1 x^2))x^3 x^4

;; ... or else can be substituted e.g. by nat and {n1,n2|n1<n2}

(define idpc-inst
  (idpredconst-name-and-types-and-cterms-to-idpredconst
   "TrCl"
   (list (py "nat"))
   (list (make-cterm (pv "n^1") (pv "n^2") (pf "n^1<n^2")))))

(pp (make-predicate-formula idpc-inst (pt "n3") (pt "n4")))
;; (TrCl (cterm (n^1,n^2) n^1<n^2))n3 n4

;; One can also directly parse such formulas

(pp (pf "(TrCl (cterm (n^1,n^2) n^1=n^2))n1 n2"))

;; Another possibility is to substitute:

(define topsubst
  (list (list (py "alpha") (py "nat"))
	(list (pv "x1") (pt "n1"))
	(list (pv "x2") (pt "n2"))
	(list (predicate-form-to-predicate (pf "R x^1 x^2"))
	      (make-cterm (pv "n^1") (pv "n^2") (pf "n^1=n^2")))))

(pp-subst topsubst)
;;   alpha -> nat
;;   x1 -> n1
;;   x2 -> n2
;;   R ->  (cterm (n^1,n^2) n^1=n^2)

(pp (rename-variables
     (formula-substitute
      (pf "(TrCl (cterm (x^1,x^2) R x^1 x^2))x1 x2")
      topsubst)))

;; (TrCl (cterm (n^,n^0) n^ =n^0))n1 n2

;; The clauses with the given parameter pvar R and the internally
;; chosen idpc-pvar R326 are

(for-each pp (idpredconst-name-to-clauses "TrCl"))
;; allnc x^,y^(R x^ y^ -> R326 x^ y^)
;; allnc x^,y^,z^(R x^ y^ -> R326 y^ z^ -> R326 x^ z^)

;; The actual clauses are aconsts:

(pp (rename-variables
     (aconst-to-formula
     (number-and-idpredconst-to-intro-aconst
      0 (idpredconst-name-and-types-and-cterms-to-idpredconst
	 "TrCl"
	 (list (py "nat"))
	 (list (make-cterm (pv "n^1") (pv "n^2") (pf "ex l n^1+l=n^2"))))))))

;; allnc n^,n^0(
;;  ex l n^ +l=n^0 -> (TrCl (cterm (n^1,n^2) ex l n^1+l=n^2))n^ n^0)

(pp (rename-variables
     (aconst-to-formula
     (number-and-idpredconst-to-intro-aconst
      1 (idpredconst-name-and-types-and-cterms-to-idpredconst
	 "TrCl"
	 (list (py "nat"))
	 (list (make-cterm (pv "n^1") (pv "n^2") (pf "ex l n^1+l=n^2"))))))))

;; allnc n^,n^0,n^1(
;;  ex l n^ +l=n^0 ->
;;  (TrCl (cterm (n^2,n^3) ex l n^2+l=n^3))n^0 n^1 ->
;;  (TrCl (cterm (n^2,n^3) ex l n^2+l=n^3))n^ n^1)

;; The et-type of the idpredconst depends on the et-type of the
;; parameter cterm.

(pp (idpredconst-to-et-type
     (predicate-form-to-predicate
      (pf "(TrCl (cterm (n^2,n^3) ex l n^2+l=n^3))n^ n^1"))))
;; lnat nat

;; In case the parameter cterm is n.c. we can avoid the unit type in
;; lnat unit by creating a new algebra lnatnc:

(pp (idpredconst-to-et-type
     (predicate-form-to-predicate
      (pf "(TrCl (cterm (n^2,n^3) n^2<n^3))n^ n^1"))))

;; ok, algebra lnatnc added
;; lnatnc

(display-alg "lnat" "lnatnc")

;; lnat
;; 	LnatZero:	alpha=>lnat alpha
;; 	LnatSucc:	alpha=>lnat alpha=>lnat alpha
;; lnatnc
;; 	LnatZeroNc:	lnatnc
;; 	LnatSuccNc:	lnatnc=>lnatnc

;; However, this is a feature we do not inded to use any more.  In fact,
;; check-aconst rejects the predicate above:

;; (check-idpredconst (predicate-form-to-predicate
;;       (pf "(TrCl (cterm (n^2,n^3) n^2<n^3))n^ n^1")))

;; check-idpredconst
;; c.r. formula expected
;; n^2<n^3
;; for param-pvar
;; (pvar (arity alpha alpha) -1 0 0 R)

(add-mr-ids "TrCl")
;; ok, inductively defined predicate constant TrClMR added

(for-each pp (map rename-variables (idpredconst-name-to-clauses "TrClMR")))

;; all x^,y^,alpha694^(
;;  (Pvar alpha694 alpha alpha)^419 alpha694^ x^ y^ -> 
;;  (Pvar lnat alpha694 alpha alpha)^420((LnatZero alpha694)alpha694^)x^ y^)
;; all x^,y^,z^,alpha694^(
;;  (Pvar alpha694 alpha alpha)^419 alpha694^ x^ y^ -> 
;;  all (lnat alpha694)^0(
;;   (Pvar lnat alpha694 alpha alpha)^420(lnat alpha694)^0 y^ z^ -> 
;;   (Pvar lnat alpha694 alpha alpha)^420
;;   ((LnatSucc alpha694)alpha694^(lnat alpha694)^0)
;;   x^ 
;;   z^))

(add-mr-ids "RTC")

(for-each pp (map rename-variables (idpredconst-name-to-clauses "RTCMR")))

;; all x^,y^,alpha694^(
;;  (Pvar alpha694 alpha alpha)^425 alpha694^ x^ y^ -> 
;;  (Pvar algRTC alpha694 alpha alpha)^426((CInitRTC alpha694)alpha694^)x^ y^)
;; all x^,y^(
;;  R x^ y^ -> (Pvar algRTC alpha694 alpha alpha)^426(CLInitRTC alpha694)x^ x^)
;; all x^,y^(
;;  R x^ y^ -> (Pvar algRTC alpha694 alpha alpha)^426(CRInitRTC alpha694)y^ y^)
;; all x^,y^,z^,alpha694^(
;;  (Pvar alpha694 alpha alpha)^425 alpha694^ x^ y^ -> 
;;  all (algRTC alpha694)^0(
;;   (Pvar algRTC alpha694 alpha alpha)^426(algRTC alpha694)^0 y^ z^ -> 
;;   (Pvar algRTC alpha694 alpha alpha)^426
;;   ((CGenRTC alpha694)alpha694^(algRTC alpha694)^0)
;;   x^ 
;;   z^))

;; The general function add-mr-ids adds for any c.r. inductive
;; predicate I an n.c. inductive predicate IMR such that IMR(n0,n)
;; says that n0 realizes I(n).  For the special case of totality
;; predicates like TotalNat we obtain TotalNatMR with clauses

;; TotalNatZeroMR:	TotalNatMR Zero Zero
;; TotalNatSuccMR:
;; all nat^,nat^0(TotalNatMR nat^0 nat^ -> TotalNatMR(Succ nat^0)(Succ nat^))

;; Note that the two arguments must always be equal; in fact, one can
;; easily prove all n^1,n^(TotalNatMR n^1 n^ -> n^1 eqd n^):

;; ;; TotalNatMRToEq
;; (set-goal "all nat^1,nat^(TotalNatMR nat^1 nat^ -> nat^1 eqd nat^)")
;; (assume "nat^1" "nat^" "TMRn1n")
;; (elim "TMRn1n")
;; (use "InitEqD")
;; (assume "nat^2" "nat^3" "Useless" "n2=n3")
;; (simp "n2=n3")
;; (use "InitEqD")
;; ;; Proof finished.
;; ;; (cdp)

;; Therefore add-mr-ids is an overkill for totality predicates.  It
;; suffices to use the n.c. predicate TotalNatNc

;; (add-ids (list (list "TotalNatNc" (make-arity (py "nat"))))
;; 	 '("TotalNatNc Zero" "TotalNatZeroNc")
;; 	 '("all nat^(TotalNatNc nat^ -> TotalNatNc(Succ nat^))"
;; 	   "TotalNatSuccNc"))

;; Then we can prove

;; (set-goal "all nat^1,nat^(TotalNatMR nat^1 nat^ -> TotalNatNc nat^)")
;; (assume "nat^1" "nat^" "TMRn1n")
;; (elim "TMRn1n")
;; (use "TotalNatZeroNc")
;; (assume "nat^2" "nat^3" "Useless")
;; (use "TotalNatSuccNc")
;; ;; Proof finished.
;; ;; (cdp)

;; ;; and the converse

;; (set-goal "all nat^(TotalNatNc nat^ -> TotalNatMR nat^ nat^)")
;; (assume "nat^" "TNcn")
;; (elim "TNcn")
;; (use "TotalNatZeroMR")
;; (assume "nat^1" "Useless")
;; (use "TotalNatSuccMR")
;; ;; Proof finished.
;; ;; (cdp)

;; Therefore (add-mr-ids idpc-name) rejects idpc-names starting with
;; Total and suggests TotalAlgNc instead of TotalAlgMR

;; 2018-06-16:  Redone.  In add-mr-ids error message removed for the
;; case idpc-name starts with Total.  Reason: this makes the theory
;; cleaner (less exceptions).  One can show TotalNatMR n^ m^ -> n^ eqd m^
;; and also TotalNatNc n^ iff TotalNatMR n^ n^, and use this later .

;; Tests for add-totality

(add-var-name "ts" (py "(infltlist alpha)"))
(add-var-name "t" (py "(infltree alpha)"))

(add-totality "infltlist")

;; ok, inductively defined predicate constant TotalInfltlist added
;; ok, inductively defined predicate constant TotalInfltree added

(display-idpc "TotalInfltlist" "TotalInfltree")

;; TotalInfltlist
;; 	TotalInfltlistInfLEmpty:	TotalInfltlist(InfLEmpty alpha)
;; 	TotalInfltlistInfLTcons:	allnc t^(
;;  TotalInfltree t^ -> 
;;  allnc ts^(TotalInfltlist ts^ -> TotalInfltlist((InfLTcons alpha)t^ ts^)))
;; TotalInfltree
;; 	TotalInfltreeInfLLeaf:	allnc x^(Total x^ -> TotalInfltree((InfLLeaf alpha)x^))
;; 	TotalInfltreeInfLBranch:	allnc ts^(TotalInfltlist ts^ -> TotalInfltree((InfLBranch alpha)ts^))
;; 	TotalInfltreeInfLLim:	allnc (nat=>infltree alpha)^(
;;  allnc n^(TotalNat n^ -> TotalInfltree((nat=>infltree alpha)^ n^)) -> 
;;  TotalInfltree((InfLLim alpha)(nat=>infltree alpha)^))

(remove-var-name "ts" "t")

;; Tests for term-to-totality-formula

(add-var-name "ns" (py "list nat"))

(pp (term-to-totality-formula (pt "xs^")))
;; TotalList xs^

(pp (term-to-totality-formula (pt "ns^")))
;; TotalList ns^

(remove-var-name "ns")

;; Tests for add-co

(add-co "Even")
(add-co "Ev")
(add-co "TrCl")

(pp (rename-variables (aconst-to-formula
		       (theorem-name-to-aconst "CoEvenClause"))))
;; allnc n^(CoEven n^ -> n^ eqd 0 orr exr n^0(CoEven n^0 andl n^ eqd n^0+2))

(pp (rename-variables (aconst-to-formula
		       (theorem-name-to-aconst "CoTrClClause"))))

;; allnc x^,x^0(
;;  (CoTrCl (cterm (x^1,x^2) R x^1 x^2))x^ x^0 ->
;;  exr x^1,y^(R x^1 y^ andl x^ eqd x^1 andnc x^0 eqd y^) ord
;;  exr x^1,y^,z^(
;;   R x^1 y^ &
;;   (CoTrCl (cterm (x^2,x^3) R x^2 x^3))y^ z^ andl x^ eqd x^1 andnc x^0 eqd z^))

(define aconst (theorem-name-to-aconst "CoTrClClause"))
(define proof (make-proof-in-aconst-form aconst))
(pp (proof-to-extracted-term proof))
;; (cCoTrClClause alpha807)
(pp (nt (proof-to-extracted-term proof)))
;; (Destr lnat alpha807)

(pp (formula-to-et-type (pf "R x^ y^")))
;; alpha807

(define proof (theorem-name-to-proof "CoEvenClause"))
(define nproof (np proof))
;; (cdp nproof) ;ok

(add-totality "bin")
(display-idpc "TotalBin")
(add-co "TotalBin")

(pp (rename-variables (aconst-to-formula
		       (theorem-name-to-aconst "CoTotalBinClause"))))

;; allnc bin^(
;;  CoTotalBin bin^ ->
;;  bin^ eqd BinNil orr
;;  exr bin^0(
;;   CoTotalBin bin^0 &
;;   exr bin^1(CoTotalBin bin^1 andl bin^ eqd BinBranch bin^0 bin^1)))

;; Tests for add-mr-ids followed by add-co to obtain CoEvenMR

(add-mr-ids "Even")
;; ok, inductively defined predicate constant EvenMR added

(display-idpc "EvenMR")
;; EvenMR	non-computational
;; 	InitEvenMR:	EvenMR 0 0
;; 	GenEvenMR:	all n^,n^0(EvenMR n^0 n^ -> EvenMR(Succ n^0)(n^ +2))

(add-co "EvenMR")
;; ok, coinductively defined predicate constant CoEvenMR added
;; ok, CoEvenMRClause has been added as a new theorem.

(pp "CoEvenMRClause")

;; all n^,n^0(
;;  CoEvenMR n^0 n^ -> 
;;  n^ eqd 0 andnc n^0 eqd 0 ornc 
;;  exnc n^1,n^2(CoEvenMR n^2 n^1 andnc n^ eqd n^1+2 andnc n^0 eqd Succ n^2))

;; Tests for imp-formulas-to-uninst-gfp-formulas-etc

(define imp-formulas (list (pf "n^ =0 -> CoEven n^")))

(define uninst-gfp-formula-etc
  (apply imp-formulas-to-uninst-gfp-formula-etc imp-formulas))

(define uninst-gfp-formula (car uninst-gfp-formula-etc))

(define tpsubst (apply append (cdr uninst-gfp-formula-etc)))

(define aconst (make-aconst "Gfp" 'axiom uninst-gfp-formula tpsubst))

(pp (rename-variables (aconst-to-formula aconst)))

;; allnc n^(
;;  n^ =0 ->
;;  allnc n^0(
;;   n^0=0 -> n^0 eqd 0 orr exr n^1((CoEven n^1 orl n^1=0) andl n^0 eqd n^1+2)) ->
;;  CoEven n^)

;; Tests for alg-to-uninst-destr-type-and-tsubst

(pp (car (alg-to-uninst-destr-type-and-tsubst (make-alg "nat"))))
;; nat=>uysum nat

(pp (car (alg-to-uninst-destr-type-and-tsubst (py "list alpha"))))
;; list alpha=>uysum(alpha@@list alpha)

(pp-subst (cadr (alg-to-uninst-destr-type-and-tsubst (py "list alpha1"))))
;;   alpha -> alpha1

(pp (car (alg-to-uninst-destr-type-and-tsubst (make-alg "intv"))))
;; intv=>uysum(intv ysum intv ysum intv)

(pp (car (alg-to-uninst-destr-type-and-tsubst (py "ltlist alpha"))))
;; ltlist alpha=>uysum(ltree alpha@@ltlist alpha)

;; Tests for alg-to-destr-const

(pp (make-term-in-const-form (alg-to-destr-const (py "nat"))))
(pp (nbe-normalize-term-without-eta
     (make-term-in-const-form (alg-to-destr-const (py "nat")))))
;; [n0]Des n0

(pp (nbe-normalize-term-without-eta
     (make-term-in-app-form
      (make-term-in-const-form (alg-to-destr-const (py "nat")))
      (pt "Succ n"))))
;; Inr n

(pp (nt (make-term-in-app-form
	 (make-term-in-const-form (alg-to-destr-const (py "nat")))
	 (pt "0"))))
;; (DummyL nat)

(pp (nt (make-term-in-app-form
	 (make-term-in-const-form (alg-to-destr-const (py "nat")))
	 (pt "Succ(Succ n)"))))
;; Inr(Succ n)

(pp (nt (make-term-in-app-form
	 (make-term-in-const-form (alg-to-destr-const (py "list alpha")))
	 (pt "(Nil alpha)"))))
;; (DummyL alpha@@list alpha)

(pp (nt (make-term-in-app-form
	 (make-term-in-const-form (alg-to-destr-const (py "list alpha")))
	 (pt "x::xs"))))
;; Inr(x@xs)

(pp (nt (make-term-in-app-form
	 (make-term-in-const-form (alg-to-destr-const (py "intv")))
	 (pt "CInt"))))
;; (DummyL intv ysum intv ysum intv)

(pp (nt (make-term-in-app-form
	 (make-term-in-const-form (alg-to-destr-const (py "intv")))
	 (pt "CIntN intv"))))
;; Inr((InL intv (intv ysum intv))intv)

(pp (nt (make-term-in-app-form
	 (make-term-in-const-form (alg-to-destr-const (py "intv")))
	 (pt "CIntZ intv"))))
;; Inr((InR (intv ysum intv) intv)((InL intv intv)intv))

(pp (nt (make-term-in-app-form
	 (make-term-in-const-form (alg-to-destr-const (py "intv")))
	 (pt "CIntP intv"))))
;; Inr((InR (intv ysum intv) intv)((InR intv intv)intv))
