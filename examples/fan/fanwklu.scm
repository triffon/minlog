;; 2014-10-13.  fanwklu.scm

;; 2011-07-14.  Adapted to lib/list.scm instead of the obsolete
;; lib/listrev.scm .  Reasons for discarding listrev.scm .  (1) It
;; duplicates list.scm for an isomorphic copy.  (2) A list should be
;; seen as a stack (last in, first out) and not as a function.  (3) The
;; algebra list in listrev has Cons of type "list=>alpha1=>list" and
;; hence a recursive argument before a parameter argument.  This leads
;; to a totality predicate with an illegal clause.

;; Formalization of the equivalence of Fan and a weakened form of WKL,
;; with EffUniq as an additional hypothesis.  Based on

;; @Article{Schwichtenberg05c,
;;   author = 	 {Helmut Schwichtenberg},
;;   title = 	 {{A direct proof of the equivalence between Brouwer's fan
;;                 theorem and K{\"o}nig's lemma with a uniqueness hypothesis}},
;;   journal = 	 {Journal of Universal Computer Science},
;;   year = 	 2005,
;;   volume =	 11,
;;   number =	 12,
;;   pages =	 {2086--2095},
;;   note =	 {\url|http://www.jucs.org/jucs_11_12/a_direct_proof_of|}
;; }

;; (load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(libload "list.scm")
(set! COMMENT-FLAG #t)

(add-var-name "x" "y" (py "alpha"))
(add-var-name "xy" (py "alpha yprod alpha"))
(add-var-name "xys" (py "list(alpha yprod alpha)"))

;; ListZip and ListUnzip added as program constants

(add-program-constant "ListZip" (py "list(alpha yprod alpha)=>list alpha"))
(add-prefix-display-string "ListZip" "Zip")
(add-computation-rules
 "Zip(Nil alpha yprod alpha)" "(Nil alpha)"
 "Zip(xy::xys)" "lft xy::rht xy::Zip xys")

;; (pp (nt (pt "Zip((5 pair 4)::(3 pair 2)::(1 pair 0):)")))
;; 5::4::3::2::1::0:

;; (pp (rename-variables (term-to-totality-formula (pt "(ListZip alpha)"))))

;; allnc xys^(TotalList xys^ -> TotalList(Zip xys^))

;; ListZipTotal
(set-goal (rename-variables (term-to-totality-formula (pt "(ListZip alpha)"))))
(assume "xys^" "Txys")
(elim "Txys")
(ng #t)
(use "TotalListNil")
;; Step
(assume "xy^" "Txy" "xys^1" "Useless" "IH")
(ng #t)
(elim "Txy")
(assume "x^" "Tx" "y^" "Ty")
(ng #t)
(use "TotalListCons")
(use "Tx")
(use "TotalListCons")
(use "Ty")
(use "IH")
;; Proof finished.
(save "ListZipTotal")

(add-var-name "xs" "ys" (py "list alpha"))

(add-program-constant
 "ListUnzip" (py "nat=>list alpha=>list(alpha yprod alpha)"))
(add-infix-display-string "ListUnzip" "unzip" 'pair-op) ;right associative

(add-computation-rules
 "0 unzip xs" "(Nil alpha yprod alpha)"
 "Succ n unzip(Nil alpha)" "(Nil alpha yprod alpha)"
 "Succ n unzip x:" "(Nil alpha yprod alpha)"
 "Succ n unzip x::y::xs" "(x pair y)::n unzip xs")

;; (pp (nt (pt "3 unzip 5::4::3::2::1::0:")))
;; (5 pair 4)::(3 pair 2)::(1 pair 0):

;; ListUnzipTotal
(set-goal
 (rename-variables (term-to-totality-formula (pt "(ListUnzip alpha)"))))
(assume "n^" "Tn")
(elim "Tn")
(assume "xs^" "Txs")
(ng #t)
(use "TotalListNil")
;; Step
(assume "n^1" "Tn1" "IHn1" "xs^" "Txs")
(elim "Txs")
;; Base
(ng #t)
(use "TotalListNil")
;; Step
(assume "x^1" "Tx1" "xs^1" "Txs1" "Useless1")
(elim "Txs1")
(ng #t)
(use "TotalListNil")
(assume "x^2" "Tx2" "xs^2" "Txs2" "Useless2")
(ng #t)
(use "TotalListCons")
(use "TotalYprodPairConstr")
(use "Tx1")
(use "Tx2")
(use "IHn1")
(use "Txs2")
;; Proof finished.
(save "ListUnzipTotal")

(add-ids (list (list "STotalYprod" (make-arity (py "alpha1 yprod alpha2"))
	       "unit"))
	 '("allnc alpha1^,alpha2^ STotalYprod(alpha1^ pair alpha2^)"
	   "STotalYprodInit"))

;; STotalYprodEqDPair
(set-goal "allnc xy^(STotalYprod xy^ -> xy^ eqd(lft xy^ pair rht xy^))")
(assume "xy^" "STxy")
(elim "STxy")
(assume "x^" "y^")
(ng #t)
(use "InitEqD")
;; Proof finished.
(save "STotalYprodEqDPair")

(add-ids
 (list (list "STotalPairList" (make-arity (py "list(alpha1 yprod alpha2)"))
	     "nat"))
 '("STotalPairList(Nil alpha1 yprod alpha2)" "STotalPairListNil")
 '("allnc alpha1^,alpha2^,(list(alpha1 yprod alpha2))^(
    STotalPairList (list(alpha1 yprod alpha2))^ ->
    STotalPairList((alpha1^ pair alpha2^)::(list(alpha1 yprod alpha2))^))"
   "STotalPairListCons"))

(display-idpc "STotalPairList")

;; UnzipZipPair
(set-goal "all xys^(STotalPairList xys^ -> (Lh xys^ unzip Zip xys^) eqd xys^)")
(assume "xys^" "STxys")
(elim "STxys")
(ng #t)
(use "InitEqD")
(assume "x^" "y^" "xys^1" "STxys1" "IH")
(ng #t)
(simp "IH")
(use "InitEqD")
;; Proof finished.
(save "UnzipZipPair")

;; LhZipPair
(set-goal "all xys^(STotalList xys^ -> Lh Zip xys^ =2*Lh xys^)")
(assume "xys^" "STxys")
(elim "STxys")
(ng #t)
(use "Truth")
(assume "xy^" "xys^1" "STxys1" "IH")
(ng #t)
(use "IH")
;; Proof finished.
(save "LhZipPair")

;; (add-rewrite-rule (pt "Lh Zip xys") (pt "2*Lh xys"))

(add-program-constant "Half" (py "nat=>nat"))
(add-computation-rules
 "Half 0" "0"
 "Half 1" "0"
 "Half(Succ(Succ nat))" "Succ(Half nat)")

;; (pp (nt (pt "Half 17")))

;; HalfTotal
(set-goal (rename-variables (term-to-totality-formula (pt "Half"))))
(assert "allnc n^(TotalNat n^ -> TotalNat(Half n^) & TotalNat(Half(Succ n^)))")
 (use "AllTotalElim")
 (ind)
 (ng #t)
 (split)
 (use "TotalNatZero")
 (use "TotalNatZero")
 (assume "n1" "IH")
 (ng #t)
 (split)
 (use "IH")
 (use "TotalNatSucc")
 (use "IH")
(assume "Assertion" "n^" "Tn")
(use "Assertion")
(use "Tn")
;; Proof finished.
(save "HalfTotal")

(add-program-constant "Even" (py "nat=>boole"))

(add-computation-rules
 "Even 0" "True"
 "Even 1" "False"
 "Even(Succ(Succ n))" "Even n")

;; (pp (nt (pt "Even 17")))

;; EvenTotal
(set-goal (rename-variables (term-to-totality-formula (pt "Even"))))
(assert "allnc n^(TotalNat n^ ->
   TotalBoole(Even n^) & TotalBoole(Even(Succ n^)))")
 (use "AllTotalElim")
 (ind)
 (ng #t)
 (split)
 (use "TotalBooleTrue")
 (use "TotalBooleFalse")
 (assume "n1" "IH")
 (ng #t)
 (split)
 (use "IH")
 (use "IH")
(assume "Assertion" "n^" "Tn")
(use "Assertion")
(use "Tn")
;; Proof finished.
(save "EvenTotal")

;; "ListFzip" and "ListFunzip" added as program constants

(add-program-constant "ListFzip" (py "(nat=>alpha yprod alpha)=>nat=>alpha"))
(add-infix-display-string "ListFzip" "fzip" 'pair-op) ;right associative

(add-token
 "Fzip" 'prefix-op
 (lambda (x) (make-term-in-app-form
	      (make-term-in-const-form
	       (let* ((const (pconst-name-to-pconst "ListFzip"))
		      (tvars (const-to-tvars const))
		      (pairfcttype (term-to-type x))
		      (pairtype (arrow-form-to-val-type pairfcttype))
		      (type (star-form-to-left-type pairtype))
		      (subst (make-substitution tvars (list type))))
		 (const-substitute const subst #f)))
	      x)))

(add-display
 (py "nat=>alpha")
 (lambda (x)
   (if (term-in-app-form? x)
       (let ((op (term-in-app-form-to-final-op x))
	     (args (term-in-app-form-to-args x)))
	 (if (and (term-in-const-form? op)
		  (string=? "ListFzip"
			    (const-to-name (term-in-const-form-to-const op)))
		  (= 1 (length args)))
	     (list 'prefix-op "Fzip"
		   (term-to-token-tree (car args)))
	     #f))
       #f)))

(add-computation-rules
 "nat=>alpha yprod alpha fzip nat"
 "[if (Even nat)
          (lft(nat=>alpha yprod alpha(Half nat)))
          (rht(nat=>alpha yprod alpha(Half nat)))]")

;; (pp (nt (pt "([n]2*n pair 2*n+1)fzip 16")))
;; 16

;; ListFzipTotal
(set-goal (rename-variables (term-to-totality-formula (pt "(ListFzip alpha)"))))
(assume "(nat=>alpha yprod alpha)^" "Hyp" "n^" "Tn")
(ng #t)
(use "BooleIfTotal")
(use "EvenTotal")
(use "Tn")
;; ?_5:Total(lft((nat=>alpha yprod alpha)^(Half n^)))
(use "PairOneTotal")
(use "Hyp")
(use "HalfTotal")
(use "Tn")
(use "PairTwoTotal")
(use "Hyp")
(use "HalfTotal")
(use "Tn")
;; Proof finished.
(save "ListFzipTotal")

;; Here we needed totality properties PairOneTotal and PairTwoTotal of
;; the defined yprod, or else totality axioms for the primitive pair.

(add-program-constant "ListFunzip" (py "(nat=>alpha)=>nat=>alpha yprod alpha"))
(add-infix-display-string "ListFunzip" "funzip" 'pair-op) ;right associative

(add-token
 "Funzip" 'prefix-op
 (lambda (x) (make-term-in-app-form
	      (make-term-in-const-form
	       (let* ((const (pconst-name-to-pconst "ListFunzip"))
		      (tvars (const-to-tvars const))
		      (fcttype (term-to-type x))
		      (type (arrow-form-to-val-type fcttype))
		      (subst (make-substitution tvars (list type))))
		 (const-substitute const subst #f)))
	      x)))

(add-display
 (py "nat=>alpha yprod alpha")
 (lambda (x)
   (if (term-in-app-form? x)
       (let ((op (term-in-app-form-to-final-op x))
	     (args (term-in-app-form-to-args x)))
	 (if (and (term-in-const-form? op)
		  (string=? "ListFunzip"
			    (const-to-name (term-in-const-form-to-const op)))
		  (= 1 (length args)))
	     (list 'prefix-op "Funzip"
		   (term-to-token-tree (car args)))
	     #f))
       #f)))

(add-computation-rules
 "nat=>alpha funzip nat" "(nat=>alpha)(2*nat)pair(nat=>alpha)(2*nat+1)")

;; (pp (nt (pt "([n]n)funzip 3")))
;; 6 pair 7

;; (pp (nt (pt "Zip(Funzip([n]n)fbar 3)")))
;; 0::1::2::3::4::5:
;; (pp (nt (pt "Zip(Funzip(nat=>nat)fbar 3)")))

;; (nat=>nat)0::
;; (nat=>nat)1::(nat=>nat)2::(nat=>nat)3::(nat=>nat)4::((nat=>nat)5):

(add-var-name "a" "b" "c" (py "list boole")) ;node
(add-var-name "r" "s" "t" (py "list boole=>boole")) ;tree, bar
(add-var-name "as" "bs" "cs" (py "nat=>list boole")) ;sequences of nodes
(add-var-name "f" "g" "h" (py "nat=>boole")) ;path
(add-var-name "i" "j" (py "nat")) ;natural numbers
(add-var-name "p" "q" (py "boole")) ;booleans
(add-var-name "ns" "ms" "ks" (py "nat=>nat")) ;sequences of numbers

(add-computation-rule (pt "(Inhab boole)") (pt "True"))

;; EqDFBar
(set-goal "all n,(nat=>alpha)^1,(nat=>alpha)^2(
  all i(i<n -> (nat=>alpha)^1 i eqd (nat=>alpha)^2 i) ->
  ((nat=>alpha)^1 fbar n)eqd((nat=>alpha)^2 fbar n))")
(ind)
(assume "(nat=>alpha)^1" "(nat=>alpha)^2" "H1")
(ng #t)
(use "InitEqD")
(assume "n" "IH" "(nat=>alpha)^1" "(nat=>alpha)^2" "H1")
(ng #t)
(simp-with
 "IH" (pt "[n](nat=>alpha)^1(Succ n)") (pt "[n](nat=>alpha)^2(Succ n)") "?")
(simp "H1")
(use "InitEqD")
(use "Truth")
(assume "i" "i<n")
(use "H1")
(use "i<n")
;; Proof finished.
(save "EqDFBar")

(add-tvar-name "beta")

;; AppIf
(set-goal "allnc (alpha=>beta)^,alpha^1,alpha^2 all p
  (alpha=>beta)^[if p alpha^1 alpha^2]eqd
  [if p ((alpha=>beta)^alpha^1) ((alpha=>beta)^alpha^2)]")
(assume "(alpha=>beta)^" "alpha^1" "alpha^2")
(ind)
(ng #t)
(use "InitEqD")
(ng #t)
(use "InitEqD")
;; Proof finished.
(save "AppIf")

;; =FBar
(set-goal
 "all n,f^1,f^2(all i(i<n -> f^1 i=f^2 i) -> (f^1 fbar n)=(f^2 fbar n))")
(ind)
(assume "f^1" "f^2" "H1")
(ng #t)
(use "Truth")
(assume "n" "IH" "f^1" "f^2" "H1")
(ng #t)
(simp "IH")
(simp "H1")
(ng #t)
(use "Truth")
(use "Truth")
(assume "i" "i<n")
(use "H1")
(use "i<n")
;; Proof finished.
(save "=FBar")

;; =FBarIfGen
(set-goal "all f^,b,n,m(
  n<=m -> (([i][if (i<m) (i thof b) (f^ n)])fbar n)=b bar n)")
(assume "f^" "b" "n" "m")
(simp "ListBarFBar")
(assume "n<=m")
(use "=FBar")
(assume "i" "i<n")
(ng #t)
(assert "i<m")
 (use "NatLtLeTrans" (pt "n"))
 (use "i<n")
 (use "n<=m")
(assume "i<m")
(simp "i<m")
(ng #t)
(use "Truth")
;; Proof finished.
(save "=FBarIfGen")

;; =FBarIf
(set-goal "all b,n,m(
  n<=m -> (([i][if (i<m) (i thof b) True])fbar n)=b bar n)")
(assume "b" "n" "m")
(simp "ListBarFBar")
(assume "n<=m")
(use "=FBar")
(assume "i" "i<n")
(ng #t)
(assert "i<m")
 (use "NatLtLeTrans" (pt "n"))
 (use "i<n")
 (use "n<=m")
(assume "i<m")
(simp "i<m")
(ng #t)
(use "Truth")
;; Proof finished.
(save "=FBarIf")

;; ListLhBar
(set-goal "all n,a(Lh a=n -> a bar n=a)")
(ind)
(cases)
(assume "Useless")
(use "Truth")
(assume "p" "a" "Absurd")
(use "Efq")
(use "Absurd")
(assume "n" "IHn")
(cases)
(assume "Absurd")
(use "Efq")
(use "Absurd")
(assume "p" "a" "Lh a=n")
(ng #t)
(use "IHn")
(use "Lh a=n")
;; Proof finished.
(save "ListLhBar")

;; ListBarBar
(set-goal "all m,n,a a bar(n+m)bar n=a bar n")
(assume "m")
(ind)
(assume "a")
(ng #t)
(use "Truth")
(assume "n" "IHn")
(cases)
(ng #t)
(use "IHn")
(assume "p" "a")
(ng #t)
(use "IHn")
;; Proof finished.
(save "ListBarBar")

(add-global-assumption
 "ListBarBarCor" "all a,n,m(n<=m -> a bar m bar n=a bar n)")

;; Definition of Tree
(add-ids
 (list (list "Tree" (make-arity (py "list boole=>boole"))))
 '("all t(all a AllBNat(Lh a)([n]t a impb t(a bar n)) -> Tree t)" "TreeIntro"))

;; Alternative, with a logical formula:

(add-ids
 (list (list "TreeL" (make-arity (py "list boole=>boole"))))
 '("all t(all a,n(n<=Lh a -> t a -> t(a bar n)) -> TreeL t)" "GenTreeL"))

;; Definition of Upclosed
(add-ids
 (list (list "Upclosed" (make-arity (py "list boole=>boole"))))
 '("all s(all a AllBNat(Lh a)([n]s(a bar n)impb s a) -> Upclosed s)"
   "GenUpclosed"))

;; Alternative, with a logical formula:

(add-ids
 (list (list "UpclosedL" (make-arity (py "list boole=>boole"))))
 '("all s(all a,n(n<Lh a -> s(a bar n) -> s a) -> UpclosedL s)"
   "GenUpclosedL"))

;; Notice that both definitions do not have computational content.
;; (there are no "algUpclosed" "algTree" at the end of the first lines)

(add-var-name "bc" (py "list(boole yprod boole)"))
(add-var-name "ss" (py "(list(boole yprod boole))=>boole"))
(add-var-name "gh" (py "nat=>boole yprod boole"))

(add-rewrite-rules
 "Even(nat+nat)" "True"
 "Even(Succ(nat+nat))" "False")

(add-rewrite-rules
 "Half(nat+nat)" "nat"
 "Half(Succ(nat+nat))" "nat")

;; FanImpPFan
(set-goal "all s^(
all f ex m s^(f fbar m) -> ex k all f exca m(m<k+1 ! s^(f fbar m))) ->
all n,ss(
 all bc,n(n<=Lh bc -> ss(bc bar n) -> ss bc) ->
 all gh(
  ((([i]lft(gh i))fbar n)=(([i]rht(gh i))fbar n) -> F) ->
  ex m ss(gh fbar m)) ->
 ex k
  all gh(
   ((([i]lft(gh i))fbar n)=(([i]rht(gh i))fbar n) -> F) ->
    ss(gh fbar k)))")
(assume "Fan" "n" "ss" "Upclosed_ss" "Bar_ss")
(assert "all f ex m  AllBNat n([i]((f fbar m)__(2*i)=(f fbar m)__(2*i+1)impb
                                 False)impb
                           ss(Half Lh(f fbar m)unzip(f fbar m))) ->
          ex k all f exca m.
             m<k+1 !
             AllBNat n([i]((f fbar m)__(2*i)=(f fbar m)__(2*i+1)impb
                            False)impb
                      ss(Half Lh(f fbar m)unzip(f fbar m)))")
;; We instantiate Fan with s_n
(use-with "Fan" (pt "[a]AllBNat n([i](a__(2*i)=a__(2*i+1) impb False)impb
                                     ss((Half(Lh a)unzip a)))"))
(assume "FanInst")
(drop "Fan")
;; We need to show that s_n bars every path.
(assert
 "all f ex m AllBNat n([i]((f fbar m)__(2*i)=(f fbar m)__(2*i+1)impb
                                False)impb
                           ss(Half Lh(f fbar m)unzip f fbar m))")
 (assume "f")
 (cases (pt "AllBNat n([i]f(2*i)=f(2*i+1))"))
 (assume "Case1")
 ;; For easier use we write our case assumption in logical form
 (assert "all i(i<n -> f(2*i)=f(2*i+1))")
  (use-with "AllBNatElim" (pt "[i]f(2*i)=f(2*i+1)") (pt "n")
            "Case1")
 (drop "Case1")
 (assume "Case1Log")
 ;; We guess that 2*n will be the proper m
 (ex-intro (pt "2*n"))
 ;; For easier use we write our goal in logical form
 (use-with
  "AllBNatIntro"
  (pt "[i]((f fbar 2*n)__(2*i)=(f fbar 2*n)__(2*i+1)impb False)impb
          ss(Half Lh(f fbar 2*n)unzip f fbar 2*n)")
  (pt "n") "?")
 (assume "i" "i<n")
 (ng #t)
 ;; From i<n we infer (f fbar n+n)__(i+i)=f(i+i)
 (assert "(f fbar n+n)__(i+i)=f(i+i)")
  (add-global-assumption
   "FanImpPFanAux2" "all f,i,n(i<n -> (f fbar n+n)__(i+i)=f(i+i))")
  (use "FanImpPFanAux2")
  (use "i<n")
 (assume "H1")
 (simp "H1")
 ;; From i<n we infer (f fbar n+n)__(Succ(i+i))=f(Succ(i+i))
 (assert "(f fbar n+n)__(Succ(i+i))=f(Succ(i+i))")
  (add-global-assumption
   "FanImpPFanAux2a" "all f,i,n(i<n -> (f fbar n+n)__(Succ(i+i))=f(Succ(i+i)))")
  (use "FanImpPFanAux2a")
  (use "i<n")
 (assume "H2")
 (simp "H2")
 (assert "f(2*i)=f(2*i+1)")
  (use "Case1Log")
  (use "i<n")
 (assume "H3")
 (simp "H3")
 (use "Truth")

 (assume "Case2")
 ;; By Bar_ss with gh := Funzip f we can find an m such tha
 ;; bc := (Funzip f fbar m) is in ss
 (assert "ex m ss(Funzip f fbar m)")
  (use "Bar_ss")
  (add-global-assumption
   "FanImpPFanAux3"
   "all f,n((AllBNat n([i]f(2*i)=f(2*i+1)) -> F) ->
         (([i]lft(f funzip i))fbar n)=(([i]rht(f funzip i))fbar n) -> F)")
  (use "FanImpPFanAux3")
  (use "Case2")
 (assume "ExHyp")
 (by-assume "ExHyp" "m" "ExHypInst")
;; By Upclosed_ss we can assume n<=m
 (add-global-assumption
  "FanImpPFanAux4"
  "all ss,gh,m,n(all bc,n(n<=Lh bc -> ss(bc bar n) -> ss bc) ->
                         ss(gh fbar m) ->
                         ss(gh fbar(m max n)))")
 (assert "ss(Funzip f fbar(m max n))")
  (use "FanImpPFanAux4")
  (use "Upclosed_ss")
  (use "ExHypInst")
 (assume "H1")
;; Now we can take a:= Zip(bc) = Zip(Funzip f fbar(m+n)) = f fbar(2*(m+n))
 (ex-intro (pt "2*(m max n)"))
  (add-global-assumption
   "FanImpPFanAux5"
   "all f,m,n (Half Lh(f fbar 2*(m max n))unzip f fbar 2*(m max n))=
              (Funzip f fbar m)")
  (simp "FanImpPFanAux5")
  (simp "ExHypInst")
  (use "AllBNatIntro")
  (strip)
  (use "Truth")

(assume "FanInstHyp")
(inst-with-to "FanInst" "FanInstHyp" "ExHyp")
(drop "FanInst" "FanInstHyp")
(by-assume "ExHyp" "k" "Uniform-sn-bound")
(ex-intro (pt "k max n"))
(assume "gh" "ghdiff")
;; We use ss(gh fbar 2*(k max n)) from sn(a), for a = f fbar(2*(k max n))
(add-global-assumption
 "FanImpPFanAux6"
 "all gh,n,ss,k(
 ((([i]lft(gh i))fbar n)=(([i]rht(gh i))fbar n) -> F) ->
 all f
  exca m(
   m<k+1 !
   AllBNat n
   ([i]
     ((f fbar m)__(2*i)=(f fbar m)__(2*i+1)impb False)impb
     ss(Half Lh(f fbar m)unzip f fbar m))) ->
   ss(gh fbar k max n))")
(use "FanImpPFanAux6")
(use "ghdiff")
(use "Uniform-sn-bound")
;; Proof finished.
(save "FanImpPFan")

;; Variable names to be used in the extracted term.

(add-var-name "fan" (py "(list boole=>boole)=>((nat=>boole)=>nat)=>nat"))
(add-var-name "pbar" (py "(nat=>boole yprod boole)=>nat"))

(define eterm (proof-to-extracted-term (theorem-name-to-proof "FanImpPFan")))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [fan,n,ss,pbar]
;;  fan
;;  ([a]
;;    AllBNat n
;;    ([n0]
;;      ((n0+n0 thof a)=(Succ(n0+n0)thof a)impb False)impb
;;      ss(Half Lh a unzip a)))
;;  ([f]
;;    [if (AllBNat n([n0]f(n0+n0)=f(Succ(n0+n0))))
;;      (n+n)
;;      (pbar([n0]f(n0+n0)pair f(Succ(n0+n0)))max n+
;;      pbar([n0]f(n0+n0)pair f(Succ(n0+n0)))max n)])max
;;  n

;; We are given a functional fan realizing Fan, a number n, a set ss
;; of pair nodes and a functional pbar mapping a pair path differing
;; at n to a bar.  Apply fan to (1) the set of all nodes a such that
;; for all n0<n, if the elements of a at 2*n0 and 2*n0+1 are distinct,
;; then the result of unzipping a at half of its length is in ss, and
;; (2) a witness that every path f hits this set, and take the max of
;; this number and n.  For (2), distinguish cases whether for some
;; n0<n, f at 2*n0 equals f at 2*n0+1.  If so, take 2*n.  If not, let
;; n be the result of applying pbar to the unzipped form of f, and
;; take 2*n+2*n.

(add-var-name "pq" (py "boole yprod boole"))

;; FanBound
(set-goal "all n,ss(
 all bc,n(n<=Lh bc -> ss(bc bar n) -> ss bc) ->
 all gh(
  ((([i]lft(gh i))fbar n)=(([i]rht(gh i))fbar n) -> F) ->
  ex m ss(gh fbar m)) ->
 ex k
  all gh(
   ((([i]lft(gh i))fbar n)=(([i]rht(gh i))fbar n) -> F) ->
   ss(gh fbar k))) ->
all t(
 Tree t ->
 all g,h,n(
  ((g fbar n)=(h fbar n) -> F) -> ex m(t(g fbar m) -> t(h fbar m) -> F)) ->
 all n
  ex k(n<=k & all b,c(Lh b=k -> Lh c=k -> t b -> t c -> b bar n=c bar n)))")
(assume "PFan" "t" "Tree t" "EffUniq t" "n")
;; We apply PFan to ss_t = { bc | t b impb t c impb False }
;; So we assert its conclusion
(assert "ex k
          all gh(
           ((([i]lft(gh i))fbar n)=
            (([i]rht(gh i))fbar n) -> F) ->
           ([bc]t(([pq]lft pq)map bc)impb t(([pq]rht pq)map bc)impb False)
           (gh fbar k))")
 (use-with
  "PFan"
  (pt "n")
  (pt "[bc]t(([pq]lft pq)map bc)impb t(([pq]rht pq)map bc)impb False")
  "?" "?")
 (drop "PFan")
 ;; The first premise follows from Tree
 (ng #t)
 (add-global-assumption "FanBoundAux1"
      "all t(Tree t -> all bc,n(
        n<=Lh bc ->
        t(([pq0]lft pq0)map bc bar n)impb
        t(([pq0]rht pq0)map bc bar n)impb False ->
        t(([pq0]lft pq0)map bc)impb t(([pq0]rht pq0)map bc)impb False))")
 (use-with "FanBoundAux1" (pt "t") "Tree t")
 ;; (drop "Tree t")
 ;; The second premise follows from EffUniq t.  We assert its conclusion
 (assume "gh" "ghdiff")
 (assert "ex m(t(([i]lft(gh i))fbar m) -> t(([i]rht(gh i))fbar m) -> F)")
  (use-with "EffUniq t" (pt "[i]lft(gh i)") (pt "[i]rht(gh i)")
	    (pt "n") "ghdiff")
  (drop "EffUniq t")
 (assume "ExHyp")
 (by-assume "ExHyp" "m" "ExHypInst")
 (ex-intro (pt "m"))
 (ng #t)
 (assume "H1" "H2")
 (use "ExHypInst")
 (use "H1")
 (use "H2")
(assume "PFanConcl")
(drop "PFan" "EffUniq t")
(by-assume "PFanConcl" "k" "PFanBound k")
(ex-intro (pt "n max k"))
(split)
(use "NatMaxUB1")
(assume "b" "c" "H1" "H2" "H3" "H4")
(inst-with-to
 "PFanBound k"
 (pt "[i][if (i<(n max k)+1) (b__i pair c__i) (True pair True)]")
 "H")
(ng "H")

(assert
 "(([n0]lft[if (n0<Succ(n max k)) ((n0 thof b)pair n0 thof c) (True pair True)])
  fbar n)eqd
  (([n0][if (n0<Succ(n max k)) (n0 thof b) True])fbar n)")
 (use "EqDFBar")
 (ng #t)
 (assume "i" "i<n")
 (use-with "AppIf" (py "boole yprod boole") (py "boole")
	   (pt "(PairOne boole boole)")
	   (pt "(i thof b)pair i thof c") (pt "True pair True")
	   (pt "i<Succ(n max k)"))
(assume "Assertion1")
(simphyp-with-to "H" "Assertion1" "SimpH1")
(drop "H" "Assertion1")

(assert
 "(([n0]lft[if (n0<Succ(n max k)) ((n0 thof b)pair n0 thof c) (True pair True)])
  fbar k)eqd
  (([n0][if (n0<Succ(n max k)) (n0 thof b) True])fbar k)")
 (use "EqDFBar")
 (ng #t)
 (assume "i" "i<k")
 (use-with "AppIf" (py "boole yprod boole") (py "boole")
	   (pt "(PairOne boole boole)")
	   (pt "(i thof b)pair i thof c") (pt "True pair True")
	   (pt "i<Succ(n max k)"))
(assume "Assertion2")
(simphyp-with-to "SimpH1" "Assertion2" "SimpH2")
(drop "SimpH1" "Assertion2")

(assert
 "(([n0]rht[if (n0<Succ(n max k)) ((n0 thof b)pair n0 thof c) (True pair True)])
  fbar n)eqd
  (([n0][if (n0<Succ(n max k)) (n0 thof c) True])fbar n)")
 (use "EqDFBar")
 (ng #t)
 (assume "i" "i<n")
 (use-with "AppIf" (py "boole yprod boole") (py "boole")
	   (pt "(PairTwo boole boole)")
	   (pt "(i thof b)pair i thof c") (pt "True pair True")
	   (pt "i<Succ(n max k)"))
(assume "Assertion3")
(simphyp-with-to "SimpH2" "Assertion3" "SimpH3")
(drop "SimpH2" "Assertion3")

(assert
 "(([n0]rht[if (n0<Succ(n max k)) ((n0 thof b)pair n0 thof c) (True pair True)])
  fbar k)eqd
  (([n0][if (n0<Succ(n max k)) (n0 thof c) True])fbar k)")
 (use "EqDFBar")
 (ng #t)
 (assume "i" "i<k")
 (use-with "AppIf" (py "boole yprod boole") (py "boole")
	   (pt "(PairTwo boole boole)")
	   (pt "(i thof b)pair i thof c") (pt "True pair True")
	   (pt "i<Succ(n max k)"))
(assume "Assertion4")
(simphyp-with-to "SimpH3" "Assertion4" "SimpH4")
(drop "SimpH3" "Assertion4")

(use "Stab")
(assume "NegEq")
(inst-with "SimpH4" "?" "?")
(use 20)
(add-global-assumption
 "FanBoundAux4" "all t,k,b(Tree t -> k<=Lh b -> t b -> t(b bar k))")
(simp "=FBarIf")
(use "FanBoundAux4")
(use "Tree t")
(simp "H2")
(use "NatMaxUB2")
(use "H4")
(use "NatLeTrans" (pt "n max k"))
(use "NatMaxUB2")
(use "Truth")
(simp "=FBarIf")
(simp "=FBarIf")
(use "NegEq")
(use "NatLeTrans" (pt "n max k"))
(use "NatMaxUB1")
(use "Truth")
(use "NatLeTrans" (pt "n max k"))
(use "NatMaxUB1")
(use "Truth")
(simp "=FBarIf")
(use "FanBoundAux4")
(use "Tree t")
(simp "H1")
(use "NatMaxUB2")
(use "H3")
(use "NatLeTrans" (pt "n max k"))
(use "NatMaxUB2")
(use "Truth")
;; Proof finished.
(save "FanBound")

(add-var-name
 "pfan"
 (py "nat=>(list(boole yprod boole)=>boole)=>
           ((nat=>boole yprod boole)=>nat)=>nat"))

(add-var-name "uniq" (py "(nat=>boole)=>(nat=>boole)=>nat=>nat"))

(define eterm (proof-to-extracted-term (theorem-name-to-proof "FanBound")))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [pfan,r,uniq,n]
;;  n max
;;  pfan n
;;  ([bc]
;;    r((PairOne boole boole)map bc)impb
;;    r((PairTwo boole boole)map bc)impb False)
;;  ([gh]uniq([n0]lft(gh n0))([n0]rht(gh n0))n)

;; We are given a functional pfan realizing PFan, a tree r, a realizer
;; uniq of the effective uniqueness property and a number n.  Take the
;; max of n and the result of applying pfan to this number, the set of
;; all pair nodes whose left and rht parts cannot both be in r, and
;; the functional mapping a pair path to the result of applying uniq
;; to it and this number.

;; Construction of the path

;; "Path"
(set-goal "all t,ks,as(
 Tree t ->
 all n n<=ks n ->
 all n,b,c(Lh b=ks n -> Lh c=ks n -> t b -> t c -> b bar n=c bar n) ->
 all n ks n<=ks(n+1) ->
 all n Lh(as n)=n -> all n t(as n) -> ex f all n t(f fbar n))")
(assume "t" "ks" "as" "Tree t" "Incr" "FanBd" "Mon" "Inf1" "Inf2")

;; Take f n := (b_{n+1})__n, with b_n := as(ks n)bar n.
(ex-intro (pt "[n](as(ks(Succ n))bar Succ n)__n"))

;; We assert Path: all n f fbar n=b__n
(assert "all n(([n](as(ks(Succ n))bar Succ n)__n)fbar n)=as(ks n)bar n")
 (ind)
 (ng #t)
 (use "Truth")
 (assume "n" "IH")
 (simp "FBarAppdLast")
 (simp (pf "([n]n thof as(ks(Succ n))bar Succ n)n=
            (n thof as(ks(Succ n))bar Succ n)")) ;will follow by ng
 (simp "IH")
 ;; Goal b_n ++ (n thof b_{n+1}) = b_{n+1}
 ;; To be able to apply BarAppdLast we replace b_n by (b_{n+1} bar n).
 ;; This is (6) and will follow from FanBd and (2)
 (simp (pf "as(ks n)bar n=as(ks(Succ n))bar Succ n bar n"))
 (simp "BarAppdLast")
 (use "Truth")
 (ng #t)
 (use "Truth")
 ;; ?_15: as(ks n)bar n=as(ks(Succ n))bar Succ n bar n
 ;; This is (6) and follows from FanBd and (2)
 (add-global-assumption
  "ListBooleTrans"
  "all a1,a2,a3(a1=a2 -> a2=a3 -> a1=a3)")
 (use "ListBooleTrans" (pt "as(ks(Succ n))bar(Succ n) bar n"))
 ;; ?: as(ks n)bar n=as(ks(Succ n))bar Succ n bar n
 ;; Now as(ks n)=as(ks(Succ n))bar(ks n) follows from FanBd, because both
 ;; are of length (ks n) and in
 (simp (pf "as(ks n)bar n=as(ks(Succ n))bar(ks n)bar n"))
 ;; ?: as(ks(Succ n))bar ks n bar n=as(ks(Succ n))bar Succ n bar n
 ;; We now need to apply ListBarBar twice
 (pp "ListBarBar")
 (assert "ks n=n+((ks n)--n)")
  (add-global-assumption "PathAux1" "all n,m(n<=m -> m=n+(m--n))")
  (use "PathAux1")
  (use "Incr")
 (assume "EqHyp1")
 (simp "EqHyp1")
 (simp "ListBarBar")
 (simp (pf "all n,a a bar(Succ n)bar n=a bar n"))
 (use "Truth")
 (use-with "ListBarBar" (pt "1"))
 (use "FanBd")
 (use "Inf1")
 (use "Truth")
 (use "Inf2")
 (add-global-assumption
  "TreeClosed" "all t,a,n(Tree t -> t a -> n<=Lh a -> t(a bar n))")
 (use "TreeClosed")
 (use "Tree t")
 (use "Inf2")
 (simp "Inf1")
 (use "Mon")
 (use "Truth")
 (use "Truth")

;; ?_4: all n (([n](as(ks(Succ n))bar Succ n)__n)fbar n)=as(ks n)bar n ->
;;      all n t(([n](as(ks(Succ n))bar Succ n)__n)fbar n) from

(assume "H1" "n")
(simp "H1")

;; ?_40: t(as(ks n)bar n)
 (inversion "Tree t")
 (assume "t1" "H2" "EqHyp")
 (simphyp "H2" "<-" "EqHyp")
 (assert "all a,n(n<Lh a -> t a impb t(a bar n))")
 (assume "a" "n1")
 (use-with "AllBNatElim"
	   (pt "[n]t a impb t(a bar n)")
	   (pt "Lh a")
	   "?" (pt "n1"))
 (use 10)
 (drop 10)
 (assume "H3")
 (assert "all a,n(n<=Lh a -> t a impb t(a bar n))")
  (assume "a" "n1" "n1<=Lh a")
  (use "NatLeCases" (pt "n1") (pt "Lh a"))
  (use "n1<=Lh a")
  (use "H3")
  (assume "n1=Lh a")
  (simp "n1=Lh a")
  (simp "ListLhBar")
  (assume "t a")
  (use "t a")
  (use "Truth")
 (assume "H4")
 (use "H4")
 (simp "Inf1")
 (use "Incr")
 (use "Inf2")
;; Proof finished.
(save "Path")

(define eterm (proof-to-extracted-term (theorem-name-to-proof "Path")))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [r,ns,as,n]n thof as(ns(Succ n))bar Succ n

;; We are given a tree r, a sequence ns of numbers provided by
;; FanBound, a sequence as of nodes witnessing the infinity of r, and
;; an argument n for the path to be constructed.  Take the n-th
;; element of the sequence as applied to ns(n+1).

;; (pp "Path")
;; (pp "FanBound")
;; (pp "FanImpPFan")

;; We will need AC to construct ks and as

(add-global-assumption
 "ACNat" "all n ex k (Pvar nat nat)^ n k ->
           ex ks all n (Pvar nat nat)^ n(ks n)" 1)

(add-global-assumption
 "ACListBoole"
 "all n ex a (Pvar nat list boole)^ n a ->
   ex as all n (Pvar nat list boole)^ n(as n)" 1)

;; We also need the canonical monotone upper bound (Mon ks0) of ks0

(add-program-constant "Mon" (py "(nat=>nat)=>nat=>nat") t-deg-one)

;; To block later unfoldings have no rules for "Mon", but add its
;; needed properties as global assumptions.

(add-global-assumption "MonIncr" "all ns,n ns n<=Mon ns n")
(add-global-assumption "MonMon" "all ns,n Mon ns n<=Mon ns(Succ n)")

;; "FanImpWKL!"
(set-goal "all s^(
all f ex m s^(f fbar m) -> ex k all f exca m(m<k+1 ! s^(f fbar m))) ->
all t(
 Tree t ->
 all n ex a(Lh a=n & t a) ->
 all g,h,n(
  ((g fbar n)=(h fbar n) -> F) -> ex m(t(g fbar m) -> t(h fbar m) -> F)) ->
 ex f all n t(f fbar n))")
(assume "Fan" "t" "Tree t" "Inf t" "EffUniq t")
;; We assert "Inf t" in the form "ex as ..."
(assert "ex as all n(Lh(as n)=n & t(as n))")
 (use-with "ACListBoole"
	   (make-cterm (pv "n") (pv "a") (pf "Lh a=n & t a")) "?")
 (use "Inf t")
(assume "Exas")
(by-assume "Exas" "as" "ExHyp1")
;; We assert the conclusion of "FanBound" in the form "ex ks ..."
(assert "ex ks all n(n<=ks n & all b,c(Lh b=ks n -> Lh c=ks n -> t b -> t c ->
                                    b bar n=c bar n))")
 (use-with
  "ACNat"
  (make-cterm (pv "n") (pv "k")
	      (pf "n<=k & all b,c(Lh b=k -> Lh c=k -> t b -> t c ->
                                  b bar n=c bar n)")) "?")
 (use "FanBound")
 (use "FanImpPFan")
 (use "Fan")
 (use "Tree t")
 (use "EffUniq t")
(assume "Exks")
(by-assume "Exks" "ks0" "ExHyp2")
;; ?_20:ex f all n t(f fbar n)
;; (pp "Path")
;; all t,ks,as(
;;  Tree t ->
;;  all n n<=ks n ->
;;  all n,b,c(Lh b=ks n -> Lh c=ks n -> t b -> t c -> b bar n=c bar n) ->
;;  all n ks n<=ks(n+1) ->
;;  all n Lh(as n)=n -> all n t(as n) -> ex f all n t(f fbar n))
(use "Path" (pt "Mon ks0") (pt "as"))
(use "Tree t")
(assume "n")
(use "NatLeTrans" (pt "ks0 n"))
(use "ExHyp2")
(use "MonIncr")
(assume "n" "b" "c" "Lh b=Mon ks0 n" "Lh c=Mon ks0 n" "t b" "t c")
(assert "b bar(ks0 n)bar n=b bar n")
 (use "ListBarBarCor")
 (use "ExHyp2")
(assume "EqHyp1")
(simp "<-" "EqHyp1")
(assert "c bar(ks0 n)bar n=c bar n")
 (use "ListBarBarCor")
 (use "ExHyp2")
(assume "EqHyp2")
(simp "<-" "EqHyp2")
(inst-with-to "ExHyp2" (pt "n") 'right "ExH2")
(use "ExH2")
(use "Truth")
(use "Truth")
(add-global-assumption
 "FanImpWKLUAux2"
 "all t,b,n,m(Tree t -> t b -> Lh b=m -> n<=m -> t(b bar n))")
(use "FanImpWKLUAux2" (pt "Mon ks0 n"))
(use "Tree t")
(use "t b")
(use "Lh b=Mon ks0 n")
(use "MonIncr")
(use "FanImpWKLUAux2" (pt "Mon ks0 n"))
(use "Tree t")
(use "t c")
(use "Lh c=Mon ks0 n")
(use "MonIncr")
(use "MonMon")
(assume "n")
(use "ExHyp1")
(assume "n")
(use "ExHyp1")
;; Proof finished.
(save "FanImpWKLU")

(define eterm (proof-to-extracted-term (theorem-name-to-proof "FanImpWKLU")))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [fan,r,as,uniq]
;;  cPath r(Mon(cACNat(cFanBound(cFanImpPFan fan)r uniq)))(cACListBoole as)

;; We can ignore "cACNat" and "cACListBoole", for they are identities.

;; We unfold the contents of the auxiliary propositions:

(animate "FanImpPFan")
(animate "FanBound")
(animate "Path")

(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [fan,r,as,uniq,n]
;;  n thof
;;  cACListBoole as
;;  (Mon
;;   (cACNa
;;    ([n0]
;;      n0 max
;;      fan
;;      ([a]
;;        AllBNat n0
;;        ([n1]
;;          ((n1+n1 thof a)=(Succ(n1+n1)thof a)impb False)impb
;;          r((PairOne boole boole)map Half Lh a unzip a)impb
;;          r((PairTwo boole boole)map Half Lh a unzip a)impb False))
;;      ([f]
;;        [if (AllBNat n0([n1]f(n1+n1)=f(Succ(n1+n1))))
;;          (n0+n0)
;;          (uniq([n1]f(n1+n1))([n1]f(Succ(n1+n1)))n0 max n0+
;;          uniq([n1]f(n1+n1))([n1]f(Succ(n1+n1)))n0 max n0)])max
;;      n0))
;;   (Succ n))bar
;;  Succ n

;; WKL! implies Fan
;; ================

;; prec is the tree ordering on boolean trees, based on True<False.  I
;; suffices to have it work correctly on nodes of the same length only.

(add-program-constant "Prec" (py "list boole=>list boole=>boole"))
(add-infix-display-string "Prec" "prec" 'rel-op)

(add-computation-rules
 "(Nil boole)prec b" "False"
 "(p::a)prec(Nil boole)" "False"
 "(p::a)prec(q::b)" "(a=b impb p impb q)impb a prec b")

;; PrecTotal
(set-goal (rename-variables (term-to-totality-formula (pt "Prec"))))
(assume "a^" "Ta")
(elim "Ta")
(ng #t)
(strip)
(use "TotalBooleFalse")
(assume "p^1" "Tp1" "a^1" "Ta1" "IH"  "b^" "Tb")
(elim "Tb")
(ng #t)
(use "TotalBooleFalse")
(assume "q^1" "Tq1" "b^1" "Tb1" "IHqb1")
(ng #t)
(use "ImpConstTotal")
(use "ImpConstTotal")
(assert
 "allnc a^(TotalList a^ -> allnc b^(TotalList b^ -> TotalBoole(a^ =b^)))")
 (assume "a^2" "Ta2")
 (elim "Ta2")
 (assume "b^2" "Tb2")
 (elim "Tb2")
 (use "TotalBooleTrue")
 (strip)
 (use "TotalBooleFalse")
 (assume "p^3" "Tp3" "a^3" "Ta3" "IHa3" "b^3" "Tb3")
 (elim "Tb3")
 (use "TotalBooleFalse")
 (assume "q^4" "Tq4" "b^4" "Tb4" "IHb4")
 (ng #t)
 (use "AndConstTotal")
 (use "BooleEqTotal")
 (use "Tp3")
 (use "Tq4")
 (use "IHa3")
 (use "Tb4")
(assume "ListEqTotal")
(use "ListEqTotal")
(use "Ta1")
(use "Tb1")
(use "ImpConstTotal")
(use "Tp1")
(use "Tq1")
(use "IH")
(use "Tb1")
;; Proof finished.
(save "PrecTotal")

;; We need some recursive functions:

;; (UL n r) (for "uppermost leftmost"): If n is big (i.e., all a with
;; Lh a=n are in r), it is the uppermost leftmost node not in r.  So
;; all b preceeding (UL n r) (hence of the same length) are in r, bu
;; (UL n r) is not.  Moreover all b of length Lh(UL n r)+1 are in r.
;; If n is not big, UL n r can be arbitrary.

;; LExt a n (for "left extension"): The extension of a by True's up to
;; length n, if Lh a<=n, and an arbitrary node of length n otherwise.

;; BMu n r (for "bounded mu operator"): The least b (w.r.t. prec) of
;; length n such that b is not in r, if there is one, and arbitrary
;; otherwise.

;; Ext r (for "extension"): The extension of the complement of r, tha
;; is, the set of all b such that if b is in r, then b is big and b =
;; LExt(UL(Lh b)r)(Lh b).

;; Up s: The upwards closure of s.

(add-program-constant
 "UL" (py "nat=>(list boole=>boole)=>list boole") t-deg-one)

(add-program-constant "LExt" (py "list boole=>nat=>list boole") t-deg-one)

(add-program-constant
 "BMu" (py "nat=>(list boole=>boole)=>list boole") t-deg-one)

(add-program-constant
 "Ext" (py "(list boole=>boole)=>list boole=>boole") t-deg-one)

(add-program-constant
 "Up" (py "(list boole=>boole)=>list boole=>boole") t-deg-one)

;; Properties

;; UpElim
(add-global-assumption
 "UpElim" "all s,a(Up s a -> exca m(m<Lh a+1 ! s(a bar m)))")

;; UpExtends
(add-global-assumption "UpExtends" "all s,a(s a -> Up s a)")

;; UpUpclosed
(add-global-assumption
  "UpUpclosed" "all s,f,n,m(n<=m -> Up s(f fbar n) -> Up s(f fbar m))")

;; ExtProp
(add-global-assumption
 "ExtProp" "all r,b,m(Ext r b ->  r b -> Lh b=m -> AllBList m r)")

;; ExtTree
(add-global-assumption "ExtTree" "all s Tree(Ext(Up s))")

;; LhLEx
(add-global-assumption "LhLExt" "all a,n Lh(LExt a n)=n")

;; ExtLEx
(add-global-assumption
 "ExtLExt" "all s,n(AllBList n(Up s) -> Ext(Up s)(LExt(UL n(Up s))n))")

;; LhBMu
(add-global-assumption "LhBMu" "all r,n Lh(BMu n r)=n")

;; ExtBMu
(add-global-assumption
 "ExtBMu" "all s,n((AllBList n(Up s) -> F) -> Ext(Up s)(BMu n(Up s)))")

;; ExtUniqLex
(add-global-assumption
 "ExtUniqLext" "all r,b(Ext r b -> r b -> b=LExt(UL(Lh b)r)(Lh b))")

;; ExtUniq
(add-global-assumption
 "ExtUniq" "all r,b,c(Ext r b -> Ext r c -> r b -> r c -> b=c)")

;; ListFbarBar
(add-global-assumption
 "ListFbarBar" "all f,n,m(n<=m -> (f fbar m)bar n=(f fbar n))")

;; ListFbarBarCor
(add-global-assumption
 "ListFbarBarCor"
 "all g,h,n,m(n<=m -> (g fbar m)bar n=(h fbar m)bar n ->
                  (g fbar n)=(h fbar n))")

;; ListBoole=
(add-global-assumption "ListBoole=" "all a^(E a^ -> a^ =a^)")

;; WKLUImpFan
(set-goal "all t(
 Tree t ->
 all n ex a(Lh a=n & t a) ->
 all g,h,n(
  ((g fbar n)=(h fbar n) -> F) -> ex m(t(g fbar m) -> t(h fbar m) -> F)) ->
 ex f all n t(f fbar n)) ->
all s(
 all f ex m s(f fbar m) ->
 ex k all f(all m(m<k+1 -> s(f fbar m) -> F) -> F))")
(assume "WKL!" "s" "Bar s")
;; It suffices to construct big k in (Up s)
(cut "ex k AllBList k(Up s)")
;; (drop "WKL!")
(assume "ExBig")
(by-assume "ExBig" "k" "kBig")
(ex-intro (pt "k"))
(cut "all a(Lh a=k -> exca m(m<Lh a+1 ! s(a bar m)))")
;; This will follow from kBig
(assume "kBigConseq" "f")
(inst-with-to "kBigConseq" (pt "f fbar k") "H")
(inst-with-to "H" "Truth" "H0")
;; (drop "H")
;; (simphyp "H0" (pf "all m(m<k+1 -> ((f fbar k)bar m)=(f fbar m))"))
(assume "H1")
(use "H0")
(assume "m" "m<k+1")
(simp (pf "(f fbar k)bar m=(f fbar m)"))
(use "H1")
(use "m<k+1")
;; (f fbar k)bar m=(f fbar m) from m<k+1
(add-global-assumption
 "WKL!ImpFanAux1" "all f,k,m(m<k+1 -> (f fbar k)bar m=(f fbar m))")
(use "WKL!ImpFanAux1")
(use "m<k+1")
 ;; We now prove the claim cut in above from kBig
(assume "a" "Lh a=k")
(assert "all a(Lh a=k -> Up s a)")
 (use "AllBListElim")
 (use "kBig")
(assume "H1")
(inst-with-to "H1" (pt "a") "Lh a=k" "Up s a")
(use "UpElim")
(use "Up s a")

;; ?_4: ex k AllBList k(Up s).  That is, ex k Big_r k
(inst-with "WKL!" (pt "Ext(Up s)") "?" "?" "?")
(by-assume 3 "f" "fPath")
(inst-with-to "Bar s" (pt "f") "fHit")
;; (drop "WKL!")
;; (drop "Bar s")
(by-assume "fHit" "m" "s(f fbar m)")
;; ...hence it hits (Up s)
(assert "Up s(f fbar m)")
 (use "UpExtends")
 (use "s(f fbar m)")
(assume "Up s(f fbar m)")
;; ...and at this length we have the desired big k
(ex-intro (pt "m"))
(assert "Ext(Up s)(f fbar m)")
 (use "fPath")
(assume "Ext(Up s)(f fbar m)")
(use "ExtProp" (pt "f fbar m"))
(use "Ext(Up s)(f fbar m)")
(use "Up s(f fbar m)")
(use "Truth")

(use "ExtTree")
;; We now prove that Ext(Up s)a is infinite
;; ?_33: all n ex a(Lh a=n & Ext(Up s)a)
(assume "n")
(ex-intro (pt "[if (AllBList n(Up s)) (LExt(UL n(Up s))n) (BMu n(Up s))]"))
(cases (pt "AllBList n(Up s)"))
(assume "Big n")
(ng #t)
(split)
(use "LhLExt")
(use "ExtLExt")
(use "Big n")
(assume "Big n -> F")
(ng #t)
(split)
(use "LhBMu")
(use "ExtBMu")
(use "Big n -> F")

;; We now prove that Ext(Up s)a is infinite
;; ?_34: all g,h,n(
;;        ((g fbar n)=(h fbar n) -> F) ->
;;        ex m(Ext(Up s)(g fbar m) -> Ext(Up s)(h fbar m) -> F))
(assume "g" "h" "n" "ghdiff")
(inst-with-to "Bar s" (pt "g") "gHit")
(by-assume "gHit" "m1" "gBar")
(inst-with-to "Bar s" (pt "h") "hHit")
(by-assume "hHit" "m2" "hBar")
(ex-intro (pt "m1 max m2 max n"))
(assume "gmaxExt" "hmaxExt")
(use "ghdiff")
(assert "Up s(g fbar m1 max m2 max n)")
 (use "UpUpclosed" (pt "m1"))
 (use "NatLeTrans" (pt "m1 max m2"))
 (use "NatMaxUB1")
 (use "NatMaxUB1")
 (use "UpExtends")
 (use "gBar")
(assume "gBarMax")
(assert "Up s(h fbar m1 max m2 max n)")
 (use "UpUpclosed" (pt "m2"))
 (use "NatLeTrans" (pt "m1 max m2"))
 (use "NatMaxUB2")
 (use "NatMaxUB1")
 (use "UpExtends")
 (use "hBar")
(assume "hBarMax")
(assert "(g fbar m1 max m2 max n)=(h fbar m1 max m2 max n)")
 (use "ExtUniq" (pt "Up s"))
 (use "gmaxExt")
 (use "hmaxExt")
 (use "gBarMax")
 (use "hBarMax")
(assume "ghIdMax")
(use "ListFbarBarCor" (pt "m1 max m2 max n"))
(use "NatMaxUB2")
(simp "ghIdMax")
(use "ListBoole=")
(use "Truth")
;; Proof finished.
(save "WKLUImpFan")

(add-var-name
 "wklu"
 (py "(list boole=>boole)=>
       (nat=>list boole)=>
       ((nat=>boole)=>(nat=>boole)=>nat=>nat)=>
       nat=>boole"))

(add-var-name "hit" (py "(nat=>boole)=>nat"))

(define eterm (proof-to-extracted-term (theorem-name-to-proof "WKLUImpFan")))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [wklu,r,hit]
;;  hit
;;  (wklu(Ext(Up r))
;;   ([n][if (AllBList n(Up r)) (LExt(UL n(Up r))n) (BMu n(Up r))])
;;   ([f,f0]NatMax(hit f max hit f0)))

;; We are given a functional wklu realizing WKL!, a bar r and a
;; witness hit that each path hits the bar.  Apply hit to the result
;; of applying wklu to (1) the extension of the complement of the
;; upwards closure of r, (2) a witness for its infinity and (3) a
;; witness for the effective uniqueness of its paths.  For (2), we are
;; given n.  If n is big, take the left extension (by True's) of the
;; uppermost leftmost node in the tree.  If n is not big, take the
;; first node of length n in the tree.  For (3), we are given f and
;; f0.  Take the function mapping n to the max of itself and what the
;; witness for infinity gives at f and f0.

(deanimate "FanImpPFan")
(deanimate "FanBound")
(deanimate "Path")
