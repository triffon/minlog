;; 2017-04-21.  ishihara.scm.

;; Based on seminars/semss13/ishihara.scm and temp/banach.scm.
;; Abstract treatment with (undefined) total program constants in type
;; xi for BanachMinus, BanachTimes and BanachNorm.  Define a partial
;; equivalence relation u~v by norm(u@-v)=0.  BanachMinus, BanachTimes
;; and BanachNorm are compatible with ~.  Instantiation consists in
;; substituting a closed type for xi and total program constants for
;; BanachMinus, BanachTimes and BanachNorm, defined by computation
;; rules.  For BanachZero we can take the generally available Inhab
;; constant, which after instantiation can defined to be the intended
;; one.  The axioms used in the present abstract treatment then need
;; to be proved.

;; 2013-09-22.  examplesanalysisishihara.scm.  Based on
;; seminars/semss13/ishihara.scm and temp/banach.scm.  Abstrac
;; treatment with constants for a partial equivalence relation
;; BanachEqv (written ~) to define the Banach space in type xi and
;; constants BanachZero, BanachPlus, BanachMinus, BanachTimes
;; compatible with ~.  Instantiation consists in substituting a closed
;; type for xi and constants (not necessarily total) for BanachZero
;; BanachPlus etc defined by computation rules.  The axioms used in
;; the present abstract treatment then need to be proved.

;; @TechReport{Ishihara90a,
;;   author = 	 {Hajime Ishihara},
;;   title = 	 {A constructive closed graph theorem},
;;   institution =  {Division of Mathematical and Information Sciences,
;;     Faculty of Integrated Arts and Sciences, Hiroshima University},
;;   year = 	 1990,
;;   note = 	 {ccgt.pdf}}

;; Terminology:

;; x,y for elements of the type rea, with Real x and x===y.  [Plan:
;; rewrite: === a partial equivalence relation on rea with domain Real].
;; u,v,w for elements of a complete normed linear (i.e., Banach) space X,
;; type xi.  BanachEqv written ~.
;; (Inhab xi) for the vector 0
;; @- for vector subtraction in X
;; @* for scalar multiplication in X
;; norm

;; uu,vv for elements of a normed vector space Y, type zeta
;; @@- for vector subtraction in Y
;; @@* for scalar multiplication in Y
;; lnorm

;; (load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(libload "numbers.scm")
(libload "simpreal.scm")
(libload "real.scm")
(set! COMMENT-FLAG #t)

;; From examples/analysis/cont.scm
(add-global-assumption
 "RealLeAntiSym"
 "all x,y(Real x -> Real y -> x<<=y -> y<<=x -> x===y)")

;; To be proved in examples/analysis/cont.scm
(add-global-assumption
 "RealLeCritGen"
 "all x,y(Real x -> Real y -> all k x<<=y+1/2**k -> x<<=y)")

(add-tvar-name "xi" "zeta")
(add-var-name "u" "v" "w" (py "xi"))

;; Scalar multiplication BanachTimes and BanachNorm need to be total,
;; since later in chains of inequalities we need RealLeTrans which is
;; available for total reals only.

(add-program-constant "BanachTimes" (py "rea=>xi=>xi") t-deg-one)

;; (add-infix-display-string "BanachTimes" "@*" 'mul-op)
;; This in inappropriate here since it involves type-match-list which does
;; not raise for instance int into real.  Hence we do this directly.

(add-token
 "@*" 'mul-op
 (lambda (x y)
   (mk-term-in-app-form
    (make-term-in-const-form (pconst-name-to-pconst "BanachTimes")) x y)))

(add-display
 (py "xi")
 (lambda (x)
   (if (term-in-app-form? x)
       (let ((op (term-in-app-form-to-final-op x))
	     (args (term-in-app-form-to-args x)))
	 (if (and (term-in-const-form? op)
		  (string=? "BanachTimes"
			    (const-to-name (term-in-const-form-to-const op)))
		  (= 2 (length args)))
	     (list 'mul-op "@*"
		   (term-to-token-tree (car args))
		   (term-to-token-tree (cadr args)))
	     #f))
       #f)))

(add-global-assumption
 "GABanachTimesTotal"
 "allnc x^(TotalRea x^ -> allnc u^(Total u^ -> Total(x^ @*u^)))")

(add-program-constant "BanachNorm" (py "xi=>rea") t-deg-one)
(add-prefix-display-string "BanachNorm" "norm")

(add-global-assumption "BanachNormReal" "all u Real(norm u)")

(add-global-assumption "BanachNormNNeg" "all u 0<<=norm u")

(add-program-constant "BanachMinus" (py "xi=>xi=>xi") t-deg-one)
(add-infix-display-string "BanachMinus" "@-" 'add-op)

(add-global-assumption "BanachNormZero" "all u,k norm(u@-u)<<=1/2**k")

(add-global-assumption
 "BanachNormZeroMinus"
 "all u,k(norm u<<=1/2**k -> norm((Inhab xi)@-u)<<=1/2**k)")
;; (remove-global-assumption "BanachNormZeroMinus")


;; We introduce BanachEqv by an explicit (formally inductive)
;; predicate.

(add-ids (list (list "BanachEqv" (make-arity (py "xi") (py "xi"))))
	 '("all u,v(norm(u@-v)===0 -> BanachEqv u v)" "InitBanachEqv"))
(add-token "~" 'pred-infix
	   (lambda (u v)
	     (make-predicate-formula
	      (make-idpredconst "BanachEqv" (list (py "xi")) '())
	      u v)))

(add-idpredconst-display "BanachEqv" 'pred-infix "~")

(pp (pf "BanachEqv u v"))
(pp (pf "u~v"))

(add-var-name "us" "vs" (py "nat=>xi"))

(add-global-assumption
 "XCompl"
 "all us,M(all k,n,m(M k<=n -> n<m -> norm(us n@-us m)<<=1/2**k) ->
           ex v all k,n(M k<=n -> norm(v@-us n)<<=1/2**k))")

(add-var-name "f" (py "xi=>zeta"))

(add-var-name "uu" "vv" "ww" (py "zeta"))

(add-program-constant "NormLinTimes" (py "rea=>zeta=>zeta") t-deg-one)

(add-token
 "@@*" 'mul-op
 (lambda (x y)
   (mk-term-in-app-form
    (make-term-in-const-form (pconst-name-to-pconst "NormLinTimes")) x y)))

(add-display
 (py "zeta")
 (lambda (x)
   (if (term-in-app-form? x)
       (let ((op (term-in-app-form-to-final-op x))
	     (args (term-in-app-form-to-args x)))
	 (if (and (term-in-const-form? op)
		  (string=? "NormLinTimes"
			    (const-to-name (term-in-const-form-to-const op)))
		  (= 2 (length args)))
	     (list 'mul-op "@@*"
		   (term-to-token-tree (car args))
		   (term-to-token-tree (cadr args)))
	     #f))
       #f)))

(add-program-constant "NormLinNorm" (py "zeta=>rea") t-deg-one)
(add-prefix-display-string "NormLinNorm" "lnorm")

(add-global-assumption
 "NormLinNormNatTimes"
 "all n,uu n*lnorm uu===lnorm(n@@*uu)")

;; Let f be a linear operator from a Banach space X into a normed
;; linear space Y, and let us be a sequence in X converging to 0 with
;; modulus M.  Then for 0<a<b either a<<=norm(f(us n)) for some n or
;; norm(f(us n))<<=b for all n.

(add-var-name "g" (py "nat=>boole"))
(add-var-name "h" (py "nat=>nat"))

(add-program-constant "Hit" (py "nat=>nat=>nat"))

(add-computation-rules
 "Hit m n" "[if (m<n) (m+2) Zero]")

;; HitTotal
(set-totality-goal "Hit")
(assume "m^" "Tm" "n^" "Tn")
(ng #t)
(use "BooleIfTotal")
(use "NatLtTotal")
(use "Tm")
(use "Tn")
(use "TotalNatSucc")
(use "TotalNatSucc")
(use "Tm")
(use "TotalNatZero")
;; Proof finished.
(save-totality)

(add-program-constant "HitHere" (py "(nat=>boole)=>nat=>nat=>nat"))

(add-computation-rules
 "HitHere g n0 n1" "Hit(NatLeastUp n0 n1 g)n1")

;; HitHereTotal
(set-totality-goal "HitHere")
(assume "g^" "Tg")
(use "AllTotalElim")
(assume "m")
(use "AllTotalElim")
(assume "n")
(use "HitTotal")
(use "BooleIfTotal")
(use "NatLeTotal")
(use "NatTotalVar")
(use "NatTotalVar")
(use "NatPlusTotal")
(use "NatLeastTotal")
(use "NatMinusTotal")
(use "NatTotalVar")
(use "NatTotalVar")
(use "AllTotalElim")
(assume "n1")
(use "Tg")
(use "NatPlusTotal")
(use "NatTotalVar")
(use "NatTotalVar")
(use "NatTotalVar")
(use "TotalNatZero")
(use "NatTotalVar")
;; Proof finished.
(save-totality)

(add-program-constant
 "HitPast" (py "(nat=>boole)=>(int=>nat)=>nat=>nat=>nat"))

(add-computation-rules
 "HitPast g M n0 n" "[if (NatLeast n0 g<n0) (Succ Zero)
                         (HitHere g n0(M(Succ n)))]")

;; HitPastTotal
(set-totality-goal "HitPast")
(assume "g^" "Tg" "M^" "TM")
(use "AllTotalElim")
(assume "n0")
(use "AllTotalElim")
(assume "n")
(use "BooleIfTotal")
(use "NatLtTotal")
(use "NatLeastTotal")
(use "NatTotalVar")
(use "Tg")
(use "NatTotalVar")
(use "TotalNatSucc")
(use "TotalNatZero")
(use "HitHereTotal")
(use "Tg")
(use "NatTotalVar")
(use "TM")
(use "IntSTotal")
(use "NatToIntTotal")
(use "NatTotalVar")
;; Proof finished.
(save-totality)

(add-program-constant "H" (py "(nat=>boole)=>(int=>nat)=>nat=>nat"))

(add-computation-rules
 "H g M n" "HitPast g M(M n)n")

;; HTotal
(set-totality-goal "H")
(assume "g^" "Tg" "M^" "TM")
(use "AllTotalElim")
(assume "n")
(use "HitPastTotal")
(use "Tg")
(use "TM")
(use "TM")
(use "NatToIntTotal")
(use "NatTotalVar")
(use "NatTotalVar")
;; Proof finished.
(save-totality)

;; We prove properties of H that will be needed in the proof of
;; Ishihara's trick.

;; HDef
(set-goal "all g,M,n H g M n=HitPast g M(M n)n")
(strip)
(use "Truth")
;; Proof finished.
(save "HDef")

;; HitPastDef
(set-goal "all g,M,n0,n HitPast g M n0 n=
 [if (NatLeast n0 g<n0) (Succ Zero) (HitHere g n0(M(Succ n)))]")
(strip)
(use "Truth")
;; Proof finished.
(save "HitPastDef")

;; HitPastDef1
(set-goal  "all g,M,n0,n(NatLeast n0 g<n0 -> HitPast g M n0 n=Succ Zero)")
(assume "g" "M" "n0" "n" "m<n")
(ng #t)
(simp "m<n")
(ng #t)
(use "Truth")
;; Proof finished.
(save "HitPastDef1")

;; HitHereDef
(set-goal "all g,n0,n1 HitHere g n0 n1=Hit(NatLeastUp n0 n1 g)n1")
(strip)
(ng #t)
(use "Truth")
;; Proof finished.
(save "HitHereDef")

;; HitDef
(set-goal "all m,n Hit m n=[if (m<n) (m+2) Zero]")
(strip)
(use "Truth")
;; Proof finished.
(save "HitDef")

;; HitPastDef1Cor
(set-goal "all g,M,n0,n(HitPast g M n0 n=Zero -> n0<=NatLeast n0 g)")
(assume "g" "M" "n0" "n" "hn=0")
(use "NatNotLtToLe")
(assume "m<n0")
(assert "HitPast g M n0 n=Succ Zero")
 (use "HitPastDef1")
 (use "m<n0")
(assume "hn=1")
(simphyp-with-to "hn=1" "hn=0" "Absurd")
(use "Absurd")
;; Proof finished.
(save "HitPastDef1Cor")

;; HProp01
(set-goal "all g,M,n(H g M n=Zero -> M n<=NatLeast(M n)g)")
(assume "g" "M" "n")
(simp "HDef")
(assume "hn=0")
(use "HitPastDef1Cor" (pt "M") (pt "n"))
(use "hn=0")
;; Proof finished.
(save "HProp01")

;; HProp01Cor
(set-goal "all g,M,n,m(H g M n=Zero -> m<M n -> g m -> F)")
(assume "g" "M" "n" "m" "hn=0")
(assert "M n=NatLeast(M n)g")
 (use "NatLeAntiSym")
 (use "HProp01")
 (use "hn=0")
 (use "NatLeastBound")
(assume "EqHyp")
(simp "EqHyp")
(assume "m<NatLeast(M n)g" "gm")
(assert "m<m")
 (use "NatLtLeTrans" (pt "NatLeast(M n)g"))
 (use "m<NatLeast(M n)g")
 (use "NatLeastLeIntro")
 (use "gm")
(assume "m<m")
(use "m<m")
;; Proof finished.
(save "HProp01Cor")

;; HProp02
(set-goal "all g,M,n(H g M n=Zero -> M(Succ n)<=NatLeastUp(M n)(M(Succ n))g)")
(assume "g" "M" "n")
(simp "HDef")
(simp "HitPastDef")
(cases (pt "NatLeast(M n)g<M n"))
(assume "Useless")
(ng #t)
(use "Efq")
(simp "HitHereDef")
(simp "HitDef")
(cases (pt "NatLeastUp(M n)(M(Succ n))g<M(Succ n)"))
(assume "Useless1" "Useless2")
(ng #t)
(use "Efq")
(assume "NatLeastUp(M n)(M(Succ n))g<M(Succ n) -> F" "Useless1" "Useless2")
(use "NatNotLtToLe")
(use "NatLeastUp(M n)(M(Succ n))g<M(Succ n) -> F")
;; Proof finished.
(save "HProp02")

;; HProp02Cor
(set-goal "all g,M,n,m(H g M n=Zero -> M n<=m -> m<M(Succ n) -> g m -> F)")
(assume "g" "M" "n" "m" "hn=0")
(assert "M(Succ n)=NatLeastUp(M n)(M(Succ n))g")
 (use "NatLeAntiSym")
 (use "HProp02")
 (use "hn=0")
 (use "NatLeastUpBound")
(assume "EqHyp")
(simp "EqHyp")
(assume "M n<=m" "m<NatLeastUp(M n)(M(Succ n))g" "gm")
(assert "m<m")
 (use "NatLtLeTrans" (pt "NatLeastUp(M n)(M(Succ n))g"))
 (use "m<NatLeastUp(M n)(M(Succ n))g")
 (use "NatLeastUpLeIntro")
 (use "M n<=m")
 (use "gm")
(assume "m<m")
(use "m<m")
;; Proof finished.
(save "HProp02Cor")

;; HProp0Cor
(set-goal "all g,M,n,m(H g M n=Zero -> m<M(Succ n) -> g m -> F)")
(assume "g" "M" "n" "m" "hn=0")
(use "NatLeLtCases" (pt "M n") (pt "m"))
(use "HProp02Cor")
(use "hn=0")
(assume "m<M n" "Useless")
(use "HProp01Cor" (pt "M") (pt "n"))
(use "hn=0")
(use "m<M n")
;; Proof finished.
(save "HProp0Cor")

;; HProp22
(set-goal "all g,M,n,m(H g M n=Succ(Succ m) ->
 NatLeastUp(M n)(M(Succ n))g<M(Succ n))")
(assume "g" "M" "n" "m")
(simp "HDef")
(simp "HitPastDef")
(cases (pt "NatLeast(M n)g<M n"))
(assume "Useless")
(ng #t)
(use "Efq")
(assume "NatLeast(M n)g<M n -> F")
(simp "HitHereDef")
(simp "HitDef")
(cases (pt "NatLeastUp(M n)(M(Succ n))g<M(Succ n)"))
(strip)
(use "Truth")
(assume "NatLeastUp(M n)(M(Succ n))g<M(Succ n) -> F")
(ng #t)
(use "Efq")
;; Proof finished.
(save "HProp22")

;; HProp1
(set-goal "all g,M,n(H g M n=Succ Zero -> NatLeast(M n)g<M n)")
(assume "g" "M" "n")
(simp "HDef")
(simp "HitPastDef")
(cases (pt "NatLeast(M n)g<M n"))
(strip)
(use "Truth")
(assume "NatLeast(M n)g<M n -> F")
(simp "HitHereDef")
(simp "HitDef")
(cases (pt "NatLeastUp(M n)(M(Succ n))g<M(Succ n)"))
(ng #t)
(assume "Useless" "Absurd")
(use "Absurd")
(assume "NatLeastUp(M n)(M(Succ n))g<M(Succ n) -> F")
(ng #t)
(use "Efq")
;; Proof finished.
(save "HProp1")

;; H0Down
(set-goal "all g,M,n,n1(H g M n=Zero -> M n1<=M(Succ n) -> M n1<=M(Succ n1) ->
 M(Succ n1)<=M(Succ n) -> H g M n1=Zero)")
(assume "g" "M" "n" "n1" "hn=0" "M n1<=M(Succ n)" "M n1<=M(Succ n1)"
	"M(Succ n1)<=M(Succ n)")
(cases (pt "H g M n1"))
(strip)
(use "Truth")
(cases) ;6,7
(assume "hn1=1")
(assert "NatLeast(M n1)g<M n1")
 (use "HProp1")
 (use "hn1=1")
(assume "HitLtMn1")
(assert "g(NatLeast(M n1)g)")
 (use "NatLeastLtElim")
 (use "HitLtMn1")
(use "HProp0Cor" (pt "M") (pt "n"))
(use "hn=0")
(use "NatLtLeTrans" (pt "M n1"))
(use "HitLtMn1")
(use "M n1<=M(Succ n)")
;; 7
(assume "m" "hn1=m+2")
(assert "NatLeastUp(M n1)(M(Succ n1))g<M(Succ n1)")
 (use "HProp22" (pt "m"))
 (use "hn1=m+2")
(assume "NatLeastUp(M n1)(M(Succ n1))g<M(Succ n1)")
(assert "g(NatLeastUp(M n1)(M(Succ n1))g)")
 (use "NatLeastUpLtElim")
 (use "NatLeastUpLBound")
 (use "M n1<=M(Succ n1)")
 (use "NatLeastUp(M n1)(M(Succ n1))g<M(Succ n1)")
(use-with "HProp0Cor" (pt "g") (pt "M") (pt "n")
	  (pt "NatLeastUp(M n1)(M(Succ n1))g") "hn=0" "?")
(use "NatLtLeTrans" (pt "M(Succ n1)"))
(use "NatLeastUp(M n1)(M(Succ n1))g<M(Succ n1)")
(use "M(Succ n1)<=M(Succ n)")
;; Proof finished.
(save "H0Down")

;; H0DownMon
(set-goal "all g,M,n,n1(all n,m(n<=m -> M n<=M m) ->
 H g M n=Zero -> n1<=n -> H g M n1=Zero)")
(assume "g" "M" "n" "n1" "MMon" "hn=0" "n1<=n")
(use "H0Down" (pt "n"))
(use "hn=0")
(use "MMon")
(use "NatLeTrans" (pt "n"))
(use "n1<=n")
(use "Truth")
(use "MMon")
(use "Truth")
(use "MMon")
(use "n1<=n")
;; Proof finished.
(save "H0DownMon")

;; H1Down
(set-goal "all g,M,n(H g M(Succ n)=Succ Zero -> H g M n=Zero -> F)")
(assume "g" "M" "n" "h(n+1)=1" "hn=0")
(assert "NatLeast(M(Succ n))g<M(Succ n)")
 (use "HProp1")
 (use "h(n+1)=1")
(assume "NatLeast(M(Succ n))g<M(Succ n)")
(assert "g(NatLeast(M(Succ n))g)")
 (use "NatLeastLtElim")
 (use "NatLeast(M(Succ n))g<M(Succ n)")
 (use-with "HProp0Cor" (pt "g") (pt "M") (pt "n")
	   (pt "NatLeast(M(Succ n))g") "hn=0" "?")
(use "NatLeast(M(Succ n))g<M(Succ n)")
;; Proof finished.
(save "H1Down")

;; HFind
(set-goal "all g,M,n(
 M Zero=Zero -> (H g M n=Zero -> F) -> ex n1,m(n1<=n & H g M n1=m+2))")
(assume "g" "M")
(ind) ;3,4
(assume "M0=0" "0<h0")
(assert "H g M Zero=Succ Zero -> F")
 (assume "h0=1")
 (assert "NatLeast(M Zero)g<M Zero")
  (use "HProp1")
  (use "h0=1")
  (simp "M0=0")
 (assume "Absurd")
 (use "Absurd")
(assume "H g M Zero=Succ Zero -> F")
(ex-intro (pt "Zero"))
(ex-intro (pt "H g M Zero--Succ(Succ Zero)"))
(split)
(use "Truth")
(assert "all n((n=Zero -> F) -> (n=Succ(Zero) -> F) ->
  n=n--Succ(Succ Zero)+Succ(Succ Zero))")
 (cases)
 (assume "Absurd")
 (use "Efq")
 (use "Absurd")
 (use "Truth")
 (cases)
 (assume "Useless" "Absurd")
 (use "Efq")
 (use "Absurd")
 (use "Truth")
 (ng #t)
 (strip)
 (use "Truth")
(assume "Assertion")
(use-with "Assertion" (pt "H g M Zero") "?" "?")
(use "0<h0")
(use "H g M Zero=Succ Zero -> F")
;; 4
(assume "n" "IH" "M0=0" "0<h(n+1)")
(cases (pt "H g M n"))
(assume "hn=0")
(ex-intro (pt "Succ n"))
(ex-intro (pt "H g M(Succ n)--Succ(Succ Zero)"))
(split)
(use "Truth")
(assert "all n((n=Zero -> F) -> (n=Succ(Zero) -> F) ->
  n=n--Succ(Succ Zero)+Succ(Succ Zero))")
 (cases)
 (assume "Absurd")
 (use "Efq")
 (use "Absurd")
 (use "Truth")
 (cases)
 (assume "Useless" "Absurd")
 (use "Efq")
 (use "Absurd")
 (use "Truth")
 (ng #t)
 (strip)
 (use "Truth")
(assume "Assertion")
(use-with "Assertion" (pt "H g M(Succ n)") "?" "?")
(use "0<h(n+1)")
(assume "h(n+1)=1")
(use-with "H1Down" (pt "g") (pt "M") (pt "n") "h(n+1)=1" "hn=0")
;; 38
(assume "n1" "hn=n1+1")
(assert "H g M n=Zero -> F")
(simp "hn=n1+1")
(assume "Absurd")
(use "Absurd")
(assume "0<hn")
(inst-with-to "IH" "M0=0" "0<hn" "IHInst")
(drop "IH")
(by-assume "IHInst" "n0" "n0Prop")
(by-assume "n0Prop" "m" "mProp")
(ex-intro (pt "n0"))
(ex-intro (pt "m"))
(split)
(use "NatLeTrans" (pt "n"))
(use "mProp")
(use "Truth")
(use "mProp")
;; Proof finished.
(save "HFind")

;; Further properties of H.

;; HProp2Cor
(set-goal "all g,M,n,m(H g M n=Succ(Succ m) -> M n<=M(Succ n) ->
 g(NatLeastUp(M n)(M(Succ n))g))")
(assume "g" "M" "n" "m" "hn=m+2" "Mn<=M(n+1)")
(use "NatLeastUpLtElim")
(use "NatLeastUpLBound")
(use "Mn<=M(n+1)")
(use "HProp22" (pt "m"))
(use "hn=m+2")
;; Proof finished.
(save "HProp2Cor")

;; HProp2Val
(set-goal "all g,M,n,m(H g M n=Succ(Succ m) -> NatLeastUp(M n)(M(Succ n))g=m)")
(assume "g" "M" "n" "m")
(simp "HDef")
(simp "HitPastDef")
(simp "HitHereDef")
(cases (pt "NatLeast(M n)g<M n"))
(assume "Useless")
(ng #t)
(use "Efq")
(assume "Useless")
(simp "HitDef")
(cases (pt "(NatLeastUp(M n)(M(Succ n))g<M(Succ n))"))
(assume "Useless1" "Hyp")
(use "Hyp")
(assume "Useless1")
(ng #t)
(use "Efq")
;; Proof finished.
(save "HProp2Val")

;; HProp2gVal
(set-goal "all g,M,n,m(H g M n=Succ(Succ m) -> M n<=M(Succ n) -> g m)")
(assume "g" "M" "n" "m" "hn=m+2" "Mn<=M(n+1)")
(simp "<-" "HProp2Val" (pt "g") (pt "M") (pt "n"))
(use "HProp2Cor" (pt "m"))
(use "hn=m+2")
(use "Mn<=M(n+1)")
(use "hn=m+2")
;; Proof finished.
(save "HProp2gVal")

;; H2Succ
(set-goal "all g,M,n,m(H g M n=Succ(Succ m) -> all n,m(n<=m -> M n<=M m) ->
 H g M(Succ n)=Succ Zero)")
(assume "g" "M" "n" "m" "hn=m+2" "MMon")
(assert "g(NatLeastUp(M n)(M(Succ n))g)")
 (use "HProp2Cor" (pt "m"))
 (use "hn=m+2")
 (use "MMon")
 (use "Truth")
(assume "gInst")
(assert "NatLeastUp Zero(M(Succ n))g<=NatLeastUp(M n)(M(Succ n))g")
 (use "NatLeastUpLeIntro")
 (use "Truth")
 (use "gInst")
 (simp "NatLeastUpZero")
(assume "LeHyp")
(assert "NatLeast(M(Succ n))g<M(Succ n)")
 (use "NatLeLtTrans" (pt "NatLeastUp(M n)(M(Succ n))g"))
 (use "LeHyp")
 (use "HProp22" (pt "m"))
 (use "hn=m+2")
(assume "LtHyp")
(assert "H g M(Succ n)=HitPast g M(M(Succ n))(Succ n)")
 (simp "HDef")
 (use "Truth")
(assume "EqHyp")
(simp "EqHyp")
(use "HitPastDef1")
(use "LtHyp")
;; Proof finished.
(save "H2Succ")

;; H1Succ
(set-goal "all g,M,n(H g M n=Succ Zero -> all n,m(n<=m -> M n<=M m) ->
 H g M(Succ n)=Succ Zero)")
(assume "g" "M" "n" "hn=1" "MMon")
(assert "NatLeast(M n)g<M n")
 (use "HProp1")
 (use "hn=1")
(assume "LtHyp")
(assert "g(NatLeast(M n)g)")
 (use "NatLeastLtElim")
 (use "LtHyp")
(assume "gInst")
(assert "NatLeast(M(Succ n))g<M(Succ n)")
 (use "NatLeLtTrans" (pt "NatLeast(M n)g"))
 (use "NatLeastLeIntro")
 (use "gInst")
 (use "NatLtLeTrans" (pt "M n"))
 (use "LtHyp")
 (use "MMon")
 (use "Truth")
(assume "LtHypSucc")
(assert "H g M(Succ n)=HitPast g M(M(Succ n))(Succ n)")
 (simp "HDef")
 (use "Truth")
(assume "EqHyp")
(simp "EqHyp")
(use "HitPastDef1")
(use "LtHypSucc")
;; Proof finished.
(save "H1Succ")

;; H2Up
(set-goal "all g,M,n,m(
 H g M n=Succ(Succ m) -> all n,m(n<=m -> M n<=M m) ->
 all n1 H g M(Succ(n+n1))=Succ Zero)")
(assume "g" "M" "n" "m" "hn=m+2" "MMon")
(ind)
(use "H2Succ" (pt "m"))
(use "hn=m+2")
(use "MMon")
(assume "n1" "IH")
(use "H1Succ")
(use "IH")
(use "MMon")
;; Proof finished.
(save "H2Up")

;; H2Down
(set-goal "all g,M,n,m(
 H g M(Succ n)=Succ(Succ m) -> all n,m(n<=m -> M n<=M m) -> H g M n=Zero)")
(assume "g" "M" "n" "m" "hSn=SSm" "MMon")
(cases (pt "H g M n"))
(strip)
(use "Truth")
(cases)
(assume "hn=1")
(assert "H g M(Succ n)=Succ Zero")
 (use "H1Succ")
 (use "hn=1")
 (use "MMon")
(simp "hSn=SSm")
(ng #t)
(assume "Absurd")
(use "Absurd")
(assume "m1" "hn=SSm1")
(assert "H g M(Succ n)=Succ Zero")
 (use "H2Succ" (pt "m1"))
 (use "hn=SSm1")
 (use "MMon")
(simp "hSn=SSm")
(ng #t)
(assume "Absurd")
(use "Absurd")
;; Proof finished.
(save "H2Down")

;; (V xi)g M us s is defined via H and the auxiliary function Seq below,
;; by (Seq xi)(H g M)(H g M n)us n.  We define Seq by
;; (Seq xi)h 0 us n = 0
;; (Seq xi)h(Succ(Succ m))us n = n@*(us m)
;; (Seq xi)h(Succ Zero)us Zero = 0
;; (Seq xi)h(Succ Zero)us(Succ n) = (Seq xi)h(h n)us n

(add-global-assumption "InhabBanach" "Total(Inhab xi)")

(add-program-constant "Seq" (py "(nat=>nat)=>nat=>(nat=>xi)=>nat=>xi"))

(add-computation-rules
 "(Seq xi)h Zero us n" "(Inhab xi)"
 "(Seq xi)h(Succ(Succ m))us n" "n@*us m"
 "(Seq xi)h(Succ Zero)us Zero" "(Inhab xi)"
 "(Seq xi)h(Succ Zero)us(Succ n)" "(Seq xi)h(h n)us n")

;; SeqTotal
(set-totality-goal "Seq")
(assume "h^" "Th")
(assert "allnc us^(
      allnc n^0(TotalNat n^0 -> Total(us^ n^0)) ->
      allnc n^0(TotalNat n^0 -> allnc m^(TotalNat m^ ->
                                         Total((Seq xi)h^ m^ us^ n^0))))")
(assume "us^" "Tus")
(use "AllTotalElim")
(ind) ;7-8
;; Base
(use "AllTotalElim")
(cases)
(use "InhabBanach")
(cases)
(use "InhabBanach")
(assume "m")
(ng #t)
(use "GABanachTimesTotal")
(use "TotalReaRealConstr")
(strip)
(ng #t)
(use "TotalRatRatConstr")
(use "TotalIntIntZero")
(use "TotalPosOne")
(strip)
(ng #t)
(use "TotalNatZero")
(use "Tus")
(use "NatTotalVar")
;; Step
(assume "n" "IHn")
(use "AllTotalElim")
(cases)
(use "InhabTotal")
(cases)
(ng #t)
(use "IHn")
(use "Th")
(use "NatTotalVar")
(assume "m")
(ng #t)
(use "GABanachTimesTotal")
(use "TotalReaRealConstr")
(strip)
(ng #t)
(use "TotalRatRatConstr")
(use "IntSTotal")
(use "NatToIntTotal")
(use "NatTotalVar")
(use "TotalPosOne")
(strip)
(ng #t)
(use "TotalNatZero")
(use "Tus")
(use "NatTotalVar")
;; Assertion proved
(assume "SeqTotalAux")
(assume "m^" "Tm" "us^" "Tus" "n^" "Tn")
(use "SeqTotalAux")
(use "Tus")
(use "Tn")
(use "Tm")
;; Proof finished.
(save-totality)

(add-program-constant "V" (py "(nat=>boole)=>(int=>nat)=>(nat=>xi)=>nat=>xi"))

(add-computation-rules "(V xi)g M us n" "(Seq xi)(H g M)(H g M n)us n")

;; VTotal
(set-totality-goal "V")
(assume "g^" "Tg" "M^" "TM" "us^" "Tus")
(use "AllTotalElim")
(assume "n")
(use "SeqTotal") ;5-8
(use "HTotal")
(use "Tg")
(use "TM")
;; 6
(use "HTotal")
(use "Tg")
(use "TM")
(use "NatTotalVar")
;; 7
(use "Tus")
;; 8
(use "NatTotalVar")
;; Proof finished.
(save-totality)

(add-global-assumption
 "BanachCauchyConvMod"
 "all vs,N,k,n(
 all k,n,m(N k<=n -> n<m -> norm(vs n@-vs m)<<=1/2**k) -> N k<=n ->
 norm(vs n@-(cXCompl xi)vs N)<<=1/2**k)")

;; To avoid normalization which leads to unfolding of H (and then
;; HitPast etc) we prove defining equations for V and Seq

;; VDef
(set-goal
 "all g^,M^,us^,n^(V xi)g^ M^ us^ n^ eqd(Seq xi)(H g^ M^)(H g^ M^ n^)us^ n^")
(strip)
(use "InitEqD")
;; Proof finished.
(save "VDef")

;; SeqDef2
(set-goal
 "all h^,m^,us^,n^(Seq xi)h^(Succ(Succ m^))us^ n^ eqd n^ @*us^ m^")
(strip)
(use "InitEqD")
;; Proof finished.
(save "SeqDef2")

;; VIfH0
(set-goal "all g,M,us,n(H g M n=Zero -> (V xi)g M us n eqd(Inhab xi))")
(assume "g" "M" "us" "n" "hn=0")
(simp "VDef")
(simp "hn=0")
(use "InitEqD")
;; Proof finished.
(save "VIfH0")

;; VIfH2
(set-goal "all g,M,us,n,m(
 H g M n=Succ(Succ m) -> (V xi)g M us n eqd n@*us m)")
(assume "g" "M" "us" "n" "m" "hn=m+2")
(simp "VDef")
(simp "hn=m+2")
(simp "SeqDef2")
(use "InitEqD")
;; Proof finished.
(save "VIfH2")

;; VIfH1
(set-goal "all g,M,us,n(
 H g M n=Succ Zero -> (V xi)g M us n eqd(V xi)g M us(Pred n))")
(assume "g" "M" "us")
(cases)
(strip)
(use "InitEqD")
(assume "n" "h(n+1)=1")
(simp "VDef")
(simp "h(n+1)=1")
(simp "VDef")
(use "InitEqD")
;; Proof finished.
(save "VIfH1")

;; VIfH2Up
(set-goal "all g,M,n,m,us(
 H g M n=Succ(Succ m) ->
 all n,m(n<=m -> M n<=M m) ->
 all n1(V xi)g M us(n+n1)eqd n@*us m)")
(assume "g" "M" "n" "m" "us" "hn=m+2" "MMon")
(ind)
(use "VIfH2")
(use "hn=m+2")
(assume "n1" "IH")
(assert "(V xi)g M us(Succ(n+n1)) eqd(V xi)g M us(Pred(Succ(n+n1)))")
 (use "VIfH1")
 (use "H2Up" (pt "m"))
 (use "hn=m+2")
 (use "MMon")
 (assert "Pred(Succ(n+n1))=n+n1")
  (use "Truth")
 (assume "Pred(Succ(n+n1))=n+n1")
 (simp "Pred(Succ(n+n1))=n+n1")
 (simp "IH")
(assume "Hyp")
(use "Hyp")
;; Proof finished.
(save "VIfH2Up")

;; We show from these properties that (v_n) is a Cauchy sequence with
;; modulus N(k) := 2*k+1 max Zero.

;; First we need some general logical facts.

;; StabCases
(set-goal "(((Pvar2 -> F) -> F) -> Pvar2) ->
 (Pvar1 -> Pvar2) -> ((Pvar1 -> F) -> Pvar2) -> Pvar2")
(assume "StabHyp" "PosCase" "NegCase")
(use "StabHyp")
(assume "NotP2")
(use "NotP2")
(use "NegCase")
(assume "P1")
(use "NotP2")
(use "PosCase")
(use "P1")
;; Proof finished.
(save "StabCases")

;; ExcaElim
(set-goal "(((Pvar -> F) -> F) -> Pvar) ->
 (all alpha((Pvar alpha)alpha -> F) -> F) ->
 all alpha((Pvar alpha)alpha -> Pvar) -> Pvar")
(assume "StabHyp" "MainPrem" "SidePrem")
(use "StabHyp")
(assume "NotP")
(use "MainPrem")
(assume "alpha" "Pa")
(use "NotP")
(use "SidePrem" (pt "alpha"))
(use "Pa")
;; Proof finished.
(save "ExcaElim")

;; StabImp
(set-goal "(((Pvar2 -> F) -> F) -> Pvar2) ->
 (((Pvar1 -> Pvar2) -> F) -> F) -> Pvar1 -> Pvar2")
(assume "StabHyp" "NotNotImp" "P1")
(use "StabHyp")
(assume "NotP2")
(use "NotNotImp")
(assume "P1ImpP2")
(use "NotP2")
(use "P1ImpP2")
(use "P1")
;; Proof finished.
(save "StabImp")

;; StabAll
(set-goal "all alpha((((Pvar alpha)alpha -> F) -> F) -> (Pvar alpha)alpha) ->
 ((all alpha(Pvar alpha)alpha -> F) -> F) -> all alpha(Pvar alpha)alpha")
(assume "StabHyp" "NotNotAll" "alpha")
(use "StabHyp")
(assume "NotP")
(use "NotNotAll")
(assume "AllP")
(use "NotP")
(use "AllP")
;; Proof finished.
(save "StabAll")

;; StabAllImp
(set-goal
 "all alpha((((Pvar alpha)_2 alpha -> F) -> F) -> (Pvar alpha)_2 alpha) ->
 ((all alpha((Pvar alpha)_1 alpha -> (Pvar alpha)_2 alpha) -> F) -> F) ->
 all alpha((Pvar alpha)_1 alpha -> (Pvar alpha)_2 alpha)")
(assume "StabHyp" "NotNotAllImp" "alpha" "P1a")
(use "StabHyp")
(assume "NotP2a")
(use "NotNotAllImp")
(assume "AllImp")
(use "NotP2a")
(use "AllImp")
(use "P1a")
;; Proof finished.
(save "StabAllImp")

;; StabAllImpThreeTwo
(set-goal
 "all alpha1,alpha2,alpha3(
  (((Pvar alpha1 alpha2 alpha3)_3 alpha1 alpha2 alpha3 -> F) -> F) ->
    (Pvar alpha1 alpha2 alpha3)_3 alpha1 alpha2 alpha3) ->
 ((all alpha1,alpha2,alpha3(
   (Pvar alpha1 alpha2 alpha3)_1 alpha1 alpha2 alpha3 ->
   (Pvar alpha1 alpha2 alpha3)_2 alpha1 alpha2 alpha3 ->
   (Pvar alpha1 alpha2 alpha3)_3 alpha1 alpha2 alpha3) -> F) -> F) ->
 all alpha1,alpha2,alpha3(
  (Pvar alpha1 alpha2 alpha3)_1 alpha1 alpha2 alpha3 ->
  (Pvar alpha1 alpha2 alpha3)_2 alpha1 alpha2 alpha3 ->
  (Pvar alpha1 alpha2 alpha3)_3 alpha1 alpha2 alpha3)")
(assume "StabHyp" "NotNotAllImp" "alpha1" "alpha2" "alpha3" "P1a" "P2a")
(use "StabHyp")
(assume "NotP3a")
(use "NotNotAllImp")
(assume "AllImp")
(use "NotP3a")
(use "AllImp")
(use "P1a")
(use "P2a")
;; Proof finished.
(save "StabAllImpThreeTwo")

;; StabAtom
(set-goal "all boole(((boole -> F) -> F) -> boole)")
(cases)
(strip)
(use "Truth")
(assume "Hyp")
(use "Hyp")
(assume "Absurd")
(use "Absurd")
;; Proof finished.
(save "StabAtom")

;; StabRealNNeg
(set-goal "all x(((RealNNeg x -> F) -> F) -> RealNNeg x)")
(ind)
(assume "as" "M" "NegNegHyp")
(assert "all k 0<=as(M k)+1/2**k -> RealNNeg(RealConstr as M)")
 (assume "Hyp")
 (intro 0)
 (assume "k")
 (assert "(RealConstr as M)seq((RealConstr as M)mod k)=as(M k)")
  (ng #t)
  (use "Truth")
 (assume "EqHyp")
 (simp "EqHyp")
 (use "Hyp")
(assume "Assertion1")
(use "Assertion1")
(drop "Assertion1")
(assert "((all k 0<=as(M k)+1/2**k -> F) -> F) -> all k 0<=as(M k)+1/2**k")
 (use-with "StabAll" (py "int") (make-cterm (pv "k") (pf "0<=as(M k)+1/2**k"))
	   "?")
 (assume "k")
 (use "StabAtom")
(assume "StabHyp")
(use "StabHyp")
(assume "NotAllHyp")
(use "NegNegHyp")
(assume "RealNNegHyp")
(use "NotAllHyp")
(assert "RealNNeg(RealConstr as M) -> all k 0<=as(M k)+1/2**k")
 (assume "RNNegx" "k")
 (use "RealNNegElimVariant")
 (use "RNNegx")
(assume "Assertion2")
(use "Assertion2")
(drop "Assertion2")
(use "RealNNegHyp")
;; Proof finished.
(save "StabRealNNeg")

;; From StabRealNNeg prove StabRealLe .

;; StabRealLe
(set-goal "all x,y(((x<<=y -> F) -> F) -> x<<=y)")
(assume "x" "y" "StabHyp")
(assert "RealNNeg(y-x) -> x<<=y")
 (assume "RealNNegHyp")
 (intro 0)
 (use "RealNNegHyp")
(assume "Assertion1")
(use "Assertion1")
(drop "Assertion1")
(use "StabRealNNeg")
(assume "NotRealNNHyp")
(use "StabHyp")
(assume "x<<=y")
(use "NotRealNNHyp")
(assert "x<<=y -> RealNNeg(y-x)")
 (elim)
 (assume "x^" "y^" "Hyp")
 (use "Hyp")
(assume "Assertion2")
(use "Assertion2")
(use "x<<=y")
;; Proof finished.
(save "StabRealLe")

;; From StabRealLe together with StabAllImpThreeTwo prove StabCauchy .

;; StabCauchy
(set-goal "all vs,N(
  ((all k,n,m(N k<=n -> n<m -> norm(vs n@-vs m)<<=1/2**k) -> F) -> F) ->
    all k,n,m(N k<=n -> n<m -> norm(vs n@-vs m)<<=1/2**k))")
(assume "vs" "N")
(use "StabAllImpThreeTwo")
(assume "k" "n" "m")
(use "StabRealLe")
;; Proof finished.
(save "StabCauchy")

;; For VCauchy we need some monotonicity properties of our particular
;; modulus N(k) := 2*k+1

(add-global-assumption
 "IntTimesS" "all int1,int2 IntS int1*int2=int1*int2+int2")

;; SZeroPosExp
(set-goal "all n SZero(2**n)=IntPlus(2**n)(2**n)")
 (ind)
 (ng #t)
 (use "Truth")
 (assume "n" "IH")
 (ng #t)
 (use "IH")
;; Proof finished.
(save "SZeroPosExp")

(add-global-assumption
 "IntTimesPlusDistr"
 "all int1,int2,int3 int1*(int2+int3)=int1*int2+int1*int3")

(add-global-assumption
 "IntLeMonPlus"
 "all int1,int2,int3,int4(int1<=int2 -> int3<=int4 -> int1+int3<=int2+int4)")

(add-global-assumption
 "IntLeMonTimes"
 "all int1,int2,pos(int1<=int2 -> int1*pos<=int2*pos)")

;; IntLeTimesIntS
(set-goal "all pos,nat IntP pos<=IntS nat*IntP pos")
(assume "pos")
(ind)
(ng #t)
(use "Truth")
(assume "nat" "IH")
(use "IntLeTrans" (pt "IntS nat*pos"))
(use "IH")
(use "IntLeMonTimes")
(ng #t)
(use "Truth")
;; Proof finished.
(save "IntLeTimesIntS")

;; NMonPropAux
(set-goal "all n (Succ(Succ n))/2**Succ n<=Succ n/2**n")
(assume "n")
(ng #t)
(assert "IntS(IntS n)*2**n=IntS n*2**n+2**n")
 (simp "IntTimesS")
 (use "Truth")
(assume "IntS(IntS n)*2**n=IntS n*2**n+2**n")
(simp "IntS(IntS n)*2**n=IntS n*2**n+2**n")
(simp "SZeroPosExp")
(simp "IntTimesPlusDistr")
(use "IntLeMonPlus")
(ng #t)
(use "Truth")
(use "IntLeTimesIntS")
;; Proof finished.
(save "NMonPropAux")

;; NMonProp
(set-goal "all n,m Succ(n+m)/2**(n+m)<=Succ n/2**n")
(assume "n")
(ind)
(ng #t)
(use "Truth")
(assume "m" "IH")
(use "RatLeTrans" (pt "Succ(n+m)/2**(n+m)"))
(use "NMonPropAux")
(use "IH")
;; Proof finished.
(save "NMonProp")

;; NPos
(set-goal  "all N(N eqd [k]abs((2*k+1)max Zero) -> all p N p=SOne p)")
(assume "N" "NDef" "p")
(simp "NDef")
(ng #t)
(use "Truth")
;; Proof finished.
(save "NPos")

;; PosExpDouble
(set-goal "all n 2**NatDouble n=2**n*2**n")
(ind)
(ng #t)
(use "Truth")
(assume "n" "IH")
(ng #t)
(use "IH")
;; Proof finished.
(save "PosExpDouble")

(add-global-assumption "PosLeExp" "all p 1+p<=2**p")

;; NNeg
(set-goal  "all N(N eqd [k]abs((2*k+1)max Zero) -> all p N(IntN p)=Zero)")
(assume "N" "NDef" "p")
(simp "NDef")
(ng #t)
(use "Truth")
;; Proof finished.
(save "NNeg")

;; NProp
(set-goal
 "all N(N eqd [k]abs((2*k+1)max Zero) -> all k (N k+1)/2**N k<=1/2**k)")
(assume "N" "NDef")
(cases) ;3-5
(assume "p")
(simp "NPos")
(ord-field-simp-bwd)
(ng #t)
(simp "PosExpDouble")
(ord-field-simp-bwd)
(use "PosLeExp")
(use "NDef")
;; 4
(ng #t)
(simp "NDef")
(ng #t)
(use "Truth")
;; 5
(assume "p")
(simp "NNeg")
(ng #t)
(use "Truth")
(use "NDef")
;; Proof finished
(save "NProp")

;; VCauchy
(set-goal "all vs,g,M,us(all n,m(M n<=m -> norm(us m)<<=1/2**n) ->
 M Zero=Zero -> all n,m(n<=m -> M n<=M m) ->
 all n vs n eqd(V xi)g M us n ->
 all N(N eqd [k]abs((2*k+1)max Zero) ->
 all k,n,m(N k<=n -> n<m -> norm(vs n@-vs m)<<=1/2**k)))")
(assume "vs" "g" "M" "us" "MMod" "M0=0" "MMon" "vsDef" "N" "NDef")
(use "StabCases" (make-cterm (pf "all n H g M n=Zero"))) ;3-5
(use "StabCauchy")
;; 4
(assume "all n hn=0")
(assert "all n vs n eqd(Inhab xi)")
 (assume "n1")
 (simp "vsDef")
 (use "VIfH0")
 (use "all n hn=0")
(assume "all n vs n eqd(Inhab xi)" "k" "n" "m" "Nk<=n" "n<m")
(simp "all n vs n eqd(Inhab xi)")
(simp "all n vs n eqd(Inhab xi)")
(use "BanachNormZero")
;; 5
(assume "all n hn=/=0")
(assert "exca n Zero<H g M n")
 (assume "AllHyp")
 (use "all n hn=/=0")
 (assume "n")
 (use "StabAtom")
 (assume "hn=/=0")
 (use "NatLeCases" (pt "Zero") (pt "H g M n"))
 (use "Truth")
 (use "AllHyp")
 (assume "0=hn")
 (use "hn=/=0")
 (use "NatEqSym")
 (use "0=hn")
(assume "ExcaHyp")
(inst-with-to
 "ExcaElim" (py "nat")
 (make-cterm (pf "all k,n,m(N k<=n -> n<m -> norm(vs n@-vs m)<<=1/2**k)"))
 (make-cterm (pv "n") (pf "Zero<H g M n"))
 "ExcaElimInst")
(use "ExcaElimInst")
(drop "ExcaElimInst")
(use "StabCauchy")
(drop "ExcaElimInst")
(use "ExcaHyp")
(drop "ExcaElimInst")
(drop "ExcaHyp")
(drop "all n hn=/=0")
(assume "n0" "0<hn0")
(assert "ex n1,m(n1<=n0 & H g M n1=m+2)")
 (use "HFind")
 (use "M0=0")
 (assume "hn0=0")
 (simphyp-with-to "0<hn0" "hn0=0" "Absurd")
 (use "Absurd")
(assume "ExHyp")
(by-assume "ExHyp" "n" "nProp")
(by-assume "nProp" "m" "mProp")
(assume "k" "n1" "n2" "Nk<=n1" "n1<n2")
(use "NatLeLtCases" (pt "n") (pt "n1")) ;56,57
(assume "n<=n1")
(assert "vs n1 eqd n@*us m")
 (simp "vsDef")
 (assert "n1=n+(n1--n)")
  (simp "NatPlusMinus")
  (ng #t)
  (use "Truth")
  (use "n<=n1")
 (assume "n1=n+(n1--n)")
 (simp "n1=n+(n1--n)")
 (use "VIfH2Up")
 (use "mProp")
 (use "MMon")
(assume "vs n1 eqd n@*us m")
;; Similar with n2 for n1
(assert "vs n2 eqd n@*us m")
 (simp "vsDef")
 (assert "n2=n+(n2--n)")
  (simp "NatPlusMinus")
  (ng #t)
  (use "Truth")
  (use "NatLtToLe")
  (use "NatLeLtTrans" (pt "n1"))
  (use "n<=n1")
  (use "n1<n2")
 (assume "n2=n+(n2--n)")
 (simp "n2=n+(n2--n)")
 (use "VIfH2Up")
 (use "mProp")
 (use "MMon")
(assume "vs n2 eqd n@*us m")
(simp "vs n1 eqd n@*us m")
(simp "vs n2 eqd n@*us m")
(use "BanachNormZero")
;; 57:n1<n -> norm(vs n1@-vs n2)<<=1/2**k
(assume "n1<n")
(use "NatLeLtCases" (pt "n") (pt "n2")) ;91-92
(assume "n<=n2")
(cases (pt "n"))
(assume "n=0")
(use "Efq")
(simphyp-with-to "n1<n" "n=0" "Absurd")
(use "Absurd")
(assume "n3" "n=Sn3")
(assert "H g M n3=Zero")
 (use "H2Down" (pt "m"))
 (simp "<-" "n=Sn3")
 (use "mProp")
 (use "MMon")
(assume "hn3=0")
(assert "n1<=n3")
 (use "NatLtSuccToLe")
 (simp "<-" "n=Sn3")
 (use "n1<n")
(assume "n1<=n3")
(assert "H g M n1=Zero")
 (use "H0DownMon" (pt "n3"))
 (use "MMon")
 (use "hn3=0")
 (use "n1<=n3")
(assume "hn1=0")
(assert "vs n1 eqd(Inhab xi)")
 (simp "vsDef")
 (use "VIfH0")
 (use "hn1=0")
(assume "vs n1 eqd(Inhab xi)")
(simp "vs n1 eqd(Inhab xi)")
(use "BanachNormZeroMinus")
(simp "vsDef")
(assert "n2=n+(n2--n)")
 (simp "NatPlusMinus")
 (ng #t)
 (use "Truth")
 (use "n<=n2")
(assume "n2=n+(n2--n)")
(simp "n2=n+(n2--n)")
(simp "VIfH2Up" (pt "m"))
(assert "norm(us m)<<=1/2**n")
 (use "MMod")
 (assert "NatLeastUp(M n)(M(Succ n))g=m")
  (use "HProp2Val")
  (use "mProp")
 (assume "NatLeastUp(M n)(M(Succ n))g=m")
 (simp "<-" "NatLeastUp(M n)(M(Succ n))g=m")
 (use "NatLeastUpLBound")
 (use "MMon")
 (use "Truth")
(assume "norm(us m)<<=1/2**n")
(assert "norm(n@*us m)<<=Succ n/2**n")
;; (remove-global-assumption "BanachNormTimesNatRat")
(add-global-assumption
 "BanachNormTimesNatRat"
 "all us,m,n,n1(norm(us m)<<=1/2**n1 -> norm(n@*us m)<<=Succ n/2**n1)")

 (use "BanachNormTimesNatRat")
 (use "norm(us m)<<=1/2**n")
(assume "norm(n@*us m)<<=Succ n/2**n")
 (add-global-assumption
  "RealRatLeTrans"
  "all x,a,b(Real x -> x<<=a -> a<=b -> x<<=b)")
(use "RealRatLeTrans" (pt "Succ n/2**n"))
(use "BanachNormReal")
(use "norm(n@*us m)<<=Succ n/2**n")
;; ?_153:Succ n/2**n<=1/2**k
(use "RatLeTrans" (pt "Succ(N k)/2**(N k)"))
;; ?_154:Succ n/2**n<=Succ(N k)/2**N k
(assert "n=N k+(n--N k)")
 (simp "NatPlusMinus")
 (ng #t)
 (use "Truth")
 (use "NatLtToLe")
 (use "NatLeLtTrans" (pt "n1"))
 (use "Nk<=n1")
 (use "n1<n")
(assume "n=N k+(n--N k)")
(simp "n=N k+(n--N k)")
(use "NMonProp")
(use "NProp")
(use "NDef")
(use "MMon")
(use "mProp")
;; ?_92:n2<n -> norm(vs n1@-vs n2)<<=1/2**k
(assume "n2<n")
(assert "all n3(n3<n -> H g M n3=Zero)")
 (assume "n3" "n3<n")
 (cases (pt "n"))
 (assume "n=0")
 (simphyp-with-to "n3<n" "n=0" "Absurd")
 (use "Efq")
 (use "Absurd")
 (assume "n4" "n=n4+1")
 (assert "H g M n4=Zero")
  (use "H2Down" (pt "m"))
  (simp "<-" "n=n4+1")
  (use "mProp")
  (use "MMon")
 (assume "hn4=0")
 (use "H0DownMon" (pt "n4"))
 (use "MMon")
 (use "hn4=0")
 (use "NatLtSuccToLe")
 (simp "<-" "n=n4+1")
 (use "n3<n")
(assume "all n3(n3<n -> H g M n3=Zero)")
(simp "vsDef")
(assert "(V xi)g M us n1 eqd(Inhab xi)")
 (use "VIfH0")
 (use "all n3(n3<n -> H g M n3=Zero)")
 (use "n1<n")
(assume "(V xi)g M us n1 eqd(Inhab xi)")
(simp "(V xi)g M us n1 eqd(Inhab xi)")
(simp "vsDef")
(assert "(V xi)g M us n2 eqd(Inhab xi)")
 (use "VIfH0")
 (use "all n3(n3<n -> H g M n3=Zero)")
 (use "n2<n")
(assume "(V xi)g M us n2 eqd(Inhab xi)")
(simp "(V xi)g M us n2 eqd(Inhab xi)")
(use "BanachNormZero")
;; Proof finished.
(save "VCauchy")

;; H2Compl
(set-goal "all g,M,us,n1,m,v,N,vs(
 all n,m(n<=m -> M n<=M m) ->
 N eqd [k]abs((2*k+1)max Zero) ->
 vs eqd(V xi)g M us ->
 v eqd(cXCompl xi)vs N ->
 all k,n,m(N k<=n -> n<m -> norm(vs n@-vs m)<<=1/2**k) ->
 H g M n1=Succ(Succ m) -> n1@*us m~v)")
(assume "g" "M" "us" "n1" "m" "v" "N" "vs"
	"MMon" "NDef" "vsDef" "vDef" "NMod" "hn1=m+2")
;; We now use the fact that the limit v of the Cauchy sequence (v_n)
;; with modulus N converges with the same modulus to its limit v:
(assert "all k,n(N k<=n -> norm(vs n@-v)<<=1/2**k)")
 (simp "vDef")
 (assume "k" "n")
 (use "BanachCauchyConvMod")
 (use "NMod")
(assume "vsConv")
;; We show that beyond n1 (where hn1=m+2) v_n is constant
(assert "all n(n1<n -> H g M n=Succ Zero)")
 (ind)
 (ng #t)
 (use "Efq")
 (assume "n" "IH" "n1<n+1")
 (use "NatLtSuccCases" (pt "n1") (pt "n"))
 (use "n1<n+1")
 (assume "n1<n")
 (use "H1Succ")
 (use "IH")
 (use "n1<n")
 (use "MMon")
 (assume "n1=n")
 (simp "<-" "n1=n")
 (use "H2Succ" (pt "m"))
 (use "hn1=m+2")
 (use "MMon")
(assume "hn=1")
(assert "all n(n1<n -> vs n1 eqd vs n)")
 (ind)
 (ng #t)
 (use "Efq")
 (assume "n" "IH" "n1<n+1")
 (use "NatLtSuccCases" (pt "n1") (pt "n"))
 (use "n1<n+1")
 (assume "n1<n")
 (assert "vs(Succ n)eqd vs(Pred(Succ n))")
  (simp "vsDef")
  (use "VIfH1")
  (use "H1Succ")
  (use "hn=1")
  (use "n1<n")
  (use "MMon")
  (ng #t)
 (assume "EqHyp")
 (simp "EqHyp")
 (use "IH")
 (use "n1<n")
 (assume "n1=n")
 (simp "<-" "n1=n")
 (assert "vs(Succ n1)eqd vs(Pred(Succ n1))")
  (simp "vsDef")
  (use "VIfH1")
  (use "hn=1")
  (use "Truth")
  (ng #t)
 (assume "EqHyp")
 (simp "EqHyp")
 (use "InitEqD")
(assume "vsConstAux")
(assert "all n(n1<=n -> vs n1 eqd vs n)")
 (assume "n" "n1<=n")
 (use "NatLeCases" (pt "n1") (pt "n"))
 (use "n1<=n")
 (use "vsConstAux")
 (assume "n1=n")
 (simp "n1=n")
 (use "InitEqD")
(assume "vsConst")
(drop "vsConstAux")
(assert "vs n1 eqd n1@*us m")
 (simp "vsDef")
 (use "VIfH2")
 (use "hn1=m+2")
(assume "vs n1 eqd n1@*us m")
(simp "<-" "vs n1 eqd n1@*us m")
(use "InitBanachEqv")
(use "RealLeAntiSym")
(use "BanachNormReal")
(use "RealRat")
(use "RealLeCritGen")
(use "BanachNormReal")
(use "RealRat")
(assume "k")
(ng #t)
(assert "all n(n1<=n -> N k<=n -> vs n1 eqd vs n & norm(vs n@-v)<<=1/2**k)")
 (assume "n" "n1<=n" "Nk<=n")
 (split)
 (use "vsConst")
 (use "n1<=n")
 (use "vsConv")
 (use "Nk<=n")
(assume "Assertion")
(assert "vs n1 eqd vs(n1 max(N k))")
 (use "Assertion")
 (use "NatMaxUB1")
 (use "NatMaxUB2")
(assume "EqHyp")
(simp "EqHyp")
(use "vsConv")
(use "NatMaxUB2")
(use "BanachNormNNeg")
;; Proof finished.
(save "H2Compl")

;; We now aim at IshiharaTrick.  First we list in the order of usage
;; what is needed.

;; AC
(add-global-assumption
 "AC" "all m ex boole (Pvar nat boole)^ m boole ->
       ex g all m (Pvar nat boole)^ m (g m)")

;; ApproxSplitBoole
(set-goal "all x1,x2,x3,k(Real x1 -> Real x2 -> Real x3 ->
                    RealLt x1 x2 k -> ex boole(
                    (boole -> x3<<=x2) andnc ((boole -> F) -> x1<<=x3)))")
(assume "x1" "x2" "x3" "k" "Rx1" "Rx2" "Rx3" "x1<x2")
(assert "x3<<=x2 oru x1<<=x3")
 (use "ApproxSplit" (pt "k"))
 (use "Rx1")
 (use "Rx2")
 (use "Rx3")
 (use "x1<x2")
(assume "Disj")
(elim "Disj")
(drop "Disj")
(assume "x3<=x2")
(ex-intro (pt "True"))
(split)
(assume "Useless")
(use "x3<=x2")
(assume "Absurd")
(use "Efq")
(use "Absurd")
(use "Truth")
;; 11
(assume "x1<=x3")
(ex-intro (pt "False"))
(split)
(assume "Absurd")
(use "Efq")
(use "Absurd")
(assume "Useless")
(use "x1<=x3")
;; Proof finished.
(save "ApproxSplitBoole")
;; (remove-theorem "ApproxSplitBoole")

;; ApproxSplitBooleRat
(set-goal "all a,b,x,k(Real x -> 1/2**k<=b-a -> ex boole(
                    (boole -> x<<=b) andnc ((boole -> F) -> a<<=x)))")
(assume "a" "b" "x" "k" "Rx" "1/2**k<=b-a")
(use "ApproxSplitBoole" (pt "k"))
(use "RealRat")
(use "RealRat")
(use "Rx")
(ng #t)
(use "1/2**k<=b-a")
;; Proof finished.
(save "ApproxSplitBooleRat")
;; (remove-theorem "ApproxSplitBooleRat")

(add-global-assumption "NormLinNormReal" "all uu Real(lnorm uu)")

;; RealPosRatBound
(add-global-assumption
 "RealPosRatBound" "all x,a(Real x -> 0<a -> ex n x<<=n*a)")

(add-global-assumption
 "NatRatRealLeMonTimes"
 "all nat1,nat2,rat,rea(nat1<=nat2 -> rat<<=rea -> nat1*rat<<=nat2*rea)")

(add-global-assumption
 "RealLeCompat"
 "all x1,y1,x2,y2(Real x1 -> Real y1 -> Real x2 -> Real y2 ->
                  x1===x2 -> y1===y2 -> x1<<=y1 -> x2<<=y2)")

(add-global-assumption "RealTimesCorr" "all x,y(Real x -> Real y -> Real(x*y))")

(add-global-assumption "RealEqRefl" "all x(Real x -> x===x)")

(add-global-assumption "BanachEqvCompat"
		       "all u,v,f,x(u~v -> x<<=lnorm(f u) -> x<<=lnorm(f v))")

(add-global-assumption
 "RatLeMonTimes"
 "all rat1,rat2,rat3,rat4(0<=rat3 ->
  rat1<=rat2 -> rat3<=rat4 -> rat1*rat3<=rat2*rat4)")

(add-global-assumption
 "RatLtToLe"
 "all rat1,rat2(rat1<rat2 -> rat1<=rat2)")

(add-global-assumption "IntLeNat" "all n,m(n<=m -> IntLe n m)")

(add-global-assumption
 "RatLtMonTimes1"
 "all rat1,rat2,rat3(0<rat3 -> rat1<rat2 -> rat1*rat3<rat2*rat3)")

(add-global-assumption "RatRealRatLeTrans"
		       "all a,x,b(Real x -> a<<=x -> x<<=b -> a<=b)")

(add-global-assumption
 "RatLtLeTrans"
 "all rat1,rat2,rat3(rat1<rat2 -> rat2<=rat3 -> rat1<rat3)")

(add-global-assumption
 "RatLeLtTrans"
 "all rat1,rat2,rat3(rat1<=rat2 -> rat2<rat3 -> rat1<rat3)")

(add-global-assumption
 "RealLeTransRat"
 "all a,x,b(a<<=x -> x<<=b -> a<=b)")

(add-global-assumption
 "RatLtMonTimesNat"
 "all a,n,m(0<a -> n<m -> n*a<m*a)")

;; IshiharaTrick
(set-goal "all f,us,M,a,b,k(
 all x,u f(x@*u)eqd x@@*f u ->
 all n,m(M n<=m -> norm(us m)<<=1/2**n) ->
 M Zero=Zero ->
 all n,m(n<m -> M n<M m) ->
 0<a -> a<b -> 1/2**k<=b-a ->
 ex m a<<=lnorm(f(us m)) oru all m lnorm(f(us m))<<=b)")
(assume "f" "us" "M" "a" "b" "k"
 "fLin*" "Conv" "M0" "MStrMon" "0<a" "a<b" "1/2**k<=b-a")
(assert "ex g1 all m((g1 m -> lnorm(f(us m))<<=b) andnc
                     ((g1 m -> F) -> a<<=lnorm(f(us m))))")
 (use "AC")
 (assume "m")
 (use "ApproxSplitBooleRat" (pt "k"))
 (use "NormLinNormReal")
 (use "1/2**k<=b-a")
(assume "g1Ex")
(by-assume "g1Ex" "g1" "g1Prop")
(cut "ex g all m((g m -> a<<=lnorm(f(us m))) andnc
                 ((g m -> F) -> lnorm(f(us m))<<=b))")
(use "Id")
(assume "gEx")
(by-assume "gEx" "g" "gProp")
(assert "ex N N eqd([k]abs((2*k+1)max Zero))")
 (ex-intro (pt "([k]abs((2*k+1)max Zero))"))
 (use "InitEqD")
(assume "ex N N eqd([k]abs((2*k+1)max Zero))")
(by-assume "ex N N eqd([k]abs((2*k+1)max Zero))" "N" "NDef")
(assert "ex vs vs eqd(V xi)g M us")
 (ex-intro (pt "(V xi)g M us"))
 (use "InitEqD")
(assume "ex vs vs eqd(V xi)g M us")
(by-assume "ex vs vs eqd(V xi)g M us" "vs" "vsDef")
(assert "ex v v eqd(cXCompl xi)vs N")
 (ex-intro (pt "(cXCompl xi)vs N"))
 (use "InitEqD")
(assume "ex v v eqd(cXCompl xi)vs N")
(by-assume "ex v v eqd(cXCompl xi)vs N" "v" "vDef")
(assert "ex n lnorm(f v)<<=n*a")
 (use "RealPosRatBound")
 (use "NormLinNormReal")
 (use "0<a")
(assume "ex n lnorm(f v)<<=n*a")
(by-assume "ex n lnorm(f v)<<=n*a" "n0" "n0Prop")
;; We prove ordinary monotonicity of M from strict monotonicity.
(assert "all n,m(n<=m -> M n<=M m)")
 (assume "n" "m" "n<=m")
 (use "NatLeCases" (pt "n") (pt "m"))
 (use "n<=m")
 (assume "n<m")
 (use "NatLtToLe")
 (use "MStrMon")
 (use "n<m")
 (assume "n=m")
 (simp "n=m")
 (use "Truth")
(assume "MMon")
;; Now the main case distinction, on hn0=0
(cases (pt "H g M n0")) ;61,62
(assume "hn0=0")
(intro 1)
(assert "all n(n<=n0 -> H g M n=Zero)")
 (assume "n" "n<=n0")
 (use "H0DownMon" (pt "n0"))
 (use "MMon")
 (use "hn0=0")
 (use "n<=n0")
(assume "all n(n<=n0 -> H g M n=Zero)")
(assert "all n(n0<n -> (H g M n=Zero -> F) -> F)")
 (assume "n1" "n0<n1" "H g M n1=Zero -> F")
 (assert "ex n,m(n<=n1 & H g M n=Succ(Succ m))")
  (use "HFind")
  (use "M0")
  (use "H g M n1=Zero -> F")
 (assume "ExHyp")
 (by-assume "ExHyp" "n" "nProp")
 (by-assume "nProp" "m" "mProp")
 (use "NatLeLtCases" (pt "n") (pt "n0")) ;86,87
 (assume "n<=n0")
 (assert "H g M n=Zero")
  (use "H0DownMon" (pt "n0"))
  (use "MMon")
  (use "hn0=0")
  (use "n<=n0")
 (simp "mProp")
 (assume "Absurd")
 (use "Absurd")
;; 87
 (assume "n0<n")
;; Now derive a contradiction as Ishihara did, using H2Compl and HProp2gVal
 (assert "n@*us m~v")
  (use "H2Compl" (pt "g") (pt "M") (pt "N") (pt "vs"))
  (use "MMon")
  (use "NDef")
  (use "vsDef")
  (use "vDef")
  (use "VCauchy" (pt "g") (pt "M") (pt "us"))
  (use "Conv")
  (use "M0")
  (use "MMon")
  (simp "vsDef")
  (assume "n2")
  (use "InitEqD")
  (use "NDef")
  (use "mProp")
 (assume "n@*us m~v")
 (assert "g m")
  (use "HProp2gVal" (pt "M") (pt "n"))
  (use "mProp")
  (use "MMon")
  (use "Truth")
 (assume "gm")
 (assert "a<<=lnorm(f(us m))")
  (use "gProp")
  (use "gm")
 (assume "a<<=lnorm(f(us m))")
 (assert "n*a<<=n*lnorm(f(us m))")
  (use "NatRatRealLeMonTimes")
  (use "Truth")
  (use "a<<=lnorm(f(us m))")
 (assume "n*a<<=n*lnorm(f(us m))")
 (assert "n*a<<=lnorm(n@@*f(us m))")
  (use "RealLeCompat"
      (pt "RealConstr([n1]RatConstr(NatToInt n)One*a)([k]Zero)")
      (pt "n*lnorm(f(us m))"))
  (use "RealRat")
  (use "RealTimesCorr")
  (use "RealRat")
  (use "NormLinNormReal")
  (use "RealRat")
  (use "NormLinNormReal")
  (use "RealEqRefl")
  (use "RealRat")
  (use "NormLinNormNatTimes")
  (use "n*a<<=n*lnorm(f(us m))")
  (simp "<-" "fLin*")
 (assume "n*a<<=lnorm(f(n@*us m))")
 (assert "n*a<<=lnorm(f v)")
  (use "BanachEqvCompat" (pt "(n@*us m)"))
  (use "n@*us m~v")
  (use "n*a<<=lnorm(f(n@*us m))")
 (assume "n*a<<=lnorm(f v)")
;; With lnorm(f v)<<=n0*a we get n*a<=n0*a contradicting n0<n
 (assert "n*a<=n0*a")
  (use "RealLeTransRat" (pt "lnorm(f v)"))
  (use "n*a<<=lnorm(f v)")
  (use "n0Prop")
 (assume "n*a<=n0*a")
 (assert "n0*a<n*a")
  (use "RatLtMonTimesNat")
  (use "0<a")
  (use "n0<n")
 (assume "n0*a<n*a")
 (assert "n*a<n*a")
  (use "RatLeLtTrans" (pt "n0*a"))
  (use "n*a<=n0*a")
  (use "n0*a<n*a")
  (ng #t)
 (assume "Absurd")
 (use "Absurd")
;;?_72:all n(n0<n -> (H g M n=Zero -> F) -> F) -> all m lnorm(f(us m))<<=b
;; Here we need that M is strictly monotonic, to use HProp0Cor
(assume "all n(n0<n -> (H g M n=Zero -> F) -> F)")
(assert "all n H g M n=Zero")
 (assume "n")
 (use "NatLeLtCases" (pt "n") (pt "n0"))
 (use "all n(n<=n0 -> H g M n=Zero)")
 (assume "n0<n")
 (use "StabAtom")
 (use "all n(n0<n -> (H g M n=Zero -> F) -> F)")
 (use "n0<n")
(assume "all n H g M n=Zero" "m")
(use "gProp")
(use "HProp01Cor" (pt "M") (pt "Succ m"))
(use "all n H g M n=Zero")
(assert "all n n<M(Succ n)")
 (ind)
 (use "NatLeLtTrans" (pt "M Zero"))
 (simp "M0")
 (use "Truth")
 (use "MStrMon")
 (use "Truth")
 (assume "n" "IH")
 (use "NatLtLeTrans" (pt "Succ(M(Succ n))"))
 (use "IH")
 (use "NatLtToSuccLe")
 (use "MStrMon")
 (use "Truth")
(assume "all n n<M(Succ n)")
(use "all n n<M(Succ n)")
;; 62
(assume "n" "hn0=n+1")
(intro 0)
(assert "ex n1,m(n1<=n0 & H g M n1=m+2)")
 (use "HFind")
 (use "M0")
 (simp "hn0=n+1")
 (assume "Absurd")
 (use "Absurd")
(assume "ex n,m(n<=n0 & H g M n=m+2)")
(by-assume "ex n,m(n<=n0 & H g M n=m+2)" "n1" "n1Prop")
(by-assume "n1Prop" "m" "mProp")
(ex-intro (pt "m"))
(use "gProp")
(use "HProp2gVal" (pt "M") (pt "n1"))
(use "mProp")
(use "MMon")
(use "Truth")
;; 14 ex g all m(
;; (g m -> a<<=lnorm(f(us m))) andnc ((g m -> F) -> lnorm(f(us m))<<=b))
(ex-intro (pt "[m]negb(g1 m)"))
(ng #t)
(assume "m")
(split)
(assume "negb(g1 m)")
(use "g1Prop")
(cases (pt "g1 m"))
(assume "g1 m" "Useless")
(simphyp-with-to "negb(g1 m)" "g1 m" "Absurd")
(use "Absurd")
(assume "Useless" "Absurd")
(use "Absurd")
(assume "negb(g1 m) -> F")
(use "g1Prop")
(cases (pt "g1 m"))
(strip)
(use "Truth")
(assume "g1 m -> F")
(use "negb(g1 m) -> F")
(simp "g1 m -> F")
(use "Truth")
;; Proof finished.
(save "IshiharaTrick")

(remove-computation-rules-for (pt "H g M n"))
(display-pconst "V")
(remove-computation-rules-for (pt "(V xi)g M us n"))

(ppc (rename-variables
      (nt (proof-to-extracted-term (theorem-name-to-proof "IshiharaTrick")))))

;; [f,us,M,a,a0,k]
;;  [let g
;;    ([n]negb(cAC([n0]cApproxSplitBooleRat a a0 lnorm(f(us n0))k)n))
;;    [case (H g M
;;           (cRealPosRatBound
;;            lnorm(f((cXCompl xi)((V xi)g M us)([k0]abs(IntS(2*k0)max 0))))
;;            a))
;;     (Zero -> False)
;;     (Succ n -> True)]]

(pp "XCompl")
;; all us,M(
;;  all k,n,m(M k<=n -> n<m -> norm(us n@-us m)<<=1/2**k) ->
;;  ex v all k,n(M k<=n -> norm(v@-us n)<<=1/2**k))

(pp "RealPosRatBound")
;; all x,a(Real x -> 0<a -> ex n x<<=n*a)

(pp "ApproxSplitBooleRat")
;; all a,b,x,k(
;;  Real x ->
;;  1/2**k<=b-a -> ex boole((boole -> x<<=b) andnc ((boole -> F) -> a<<=x)))

(pp "AC")
;; all m ex boole (Pvar nat boole)^ m boole ->
;; ex g all m (Pvar nat boole)^ m(g m)

;; 2013-09-22.  Ishihara's trick one with existence: orl instead of
;; oru.  Literally the same proof works.  However, in the extracted
;; term a subterm starting with cRealPosRatBound occurs twice.  We
;; take it out with a second let.

;; IshiharaTrickOneEx
(set-goal "all f,us,M,a,b,k(
 all x,u f(x@*u)eqd x@@*f u ->
 all n,m(M n<=m -> norm(us m)<<=1/2**n) ->
 M Zero=Zero ->
 all n,m(n<m -> M n<M m) ->
 0<a -> a<b -> 1/2**k<=b-a ->
 ex m a<<=lnorm(f(us m)) orl all m lnorm(f(us m))<<=b)")
(assume "f" "us" "M" "a" "b" "k"
 "fLin*" "Conv" "M0" "MStrMon" "0<a" "a<b" "1/2**k<=b-a")
(assert "ex g1 all m((g1 m -> lnorm(f(us m))<<=b) andnc
                     ((g1 m -> F) -> a<<=lnorm(f(us m))))")
 (use "AC")
 (assume "m")
 (use "ApproxSplitBooleRat" (pt "k"))
 (use "NormLinNormReal")
 (use "1/2**k<=b-a")
(assume "g1Ex")
(by-assume "g1Ex" "g1" "g1Prop")
(cut "ex g all m((g m -> a<<=lnorm(f(us m))) andnc
                 ((g m -> F) -> lnorm(f(us m))<<=b))")
(use "Id")
(assume "gEx")
(by-assume "gEx" "g" "gProp")
(assert "ex N N eqd([k]abs((2*k+1)max Zero))")
 (ex-intro (pt "([k]abs((2*k+1)max Zero))"))
 (use "InitEqD")
(assume "ex N N eqd([k]abs((2*k+1)max Zero))")
(by-assume "ex N N eqd([k]abs((2*k+1)max Zero))" "N" "NDef")
(assert "ex vs vs eqd(V xi)g M us")
 (ex-intro (pt "(V xi)g M us"))
 (use "InitEqD")
(assume "ex vs vs eqd(V xi)g M us")
(by-assume "ex vs vs eqd(V xi)g M us" "vs" "vsDef")
(assert "ex v v eqd(cXCompl xi)vs N")
 (ex-intro (pt "(cXCompl xi)vs N"))
 (use "InitEqD")
(assume "ex v v eqd(cXCompl xi)vs N")
(by-assume "ex v v eqd(cXCompl xi)vs N" "v" "vDef")
(cut "ex n lnorm(f v)<<=n*a")
(use "Id")
(assume "ex n lnorm(f v)<<=n*a")
(by-assume "ex n lnorm(f v)<<=n*a" "n0" "n0Prop")
;; We prove ordinary monotonicity of M from strict monotonicity.
(assert "all n,m(n<=m -> M n<=M m)")
 (assume "n" "m" "n<=m")
 (use "NatLeCases" (pt "n") (pt "m"))
 (use "n<=m")
 (assume "n<m")
 (use "NatLtToLe")
 (use "MStrMon")
 (use "n<m")
 (assume "n=m")
 (simp "n=m")
 (use "Truth")
(assume "MMon")
;; Now the main case distinction, on hn0=0
(cases (pt "H g M n0")) ;60,61
(assume "hn0=0")
(intro 1)
(assert "all n(n<=n0 -> H g M n=Zero)")
 (assume "n" "n<=n0")
 (use "H0DownMon" (pt "n0"))
 (use "MMon")
 (use "hn0=0")
 (use "n<=n0")
(assume "all n(n<=n0 -> H g M n=Zero)")
(assert "all n(n0<n -> (H g M n=Zero -> F) -> F)")
 (assume "n1" "n0<n1" "H g M n1=Zero -> F")
 (assert "ex n,m(n<=n1 & H g M n=Succ(Succ m))")
  (use "HFind")
  (use "M0")
  (use "H g M n1=Zero -> F")
 (assume "ExHyp")
 (by-assume "ExHyp" "n" "nProp")
 (by-assume "nProp" "m" "mProp")
 (use "NatLeLtCases" (pt "n") (pt "n0")) ;86,87
 (assume "n<=n0")
 (assert "H g M n=Zero")
  (use "H0DownMon" (pt "n0"))
  (use "MMon")
  (use "hn0=0")
  (use "n<=n0")
 (simp "mProp")
 (assume "Absurd")
 (use "Absurd")
;; 86
 (assume "n0<n")
;; Now derive a contradiction as Ishihara did, using H2Compl and HProp2gVal
 (assert "n@*us m~v")
  (use "H2Compl" (pt "g") (pt "M") (pt "N") (pt "vs"))
  (use "MMon")
  (use "NDef")
  (use "vsDef")
  (use "vDef")
  (use "VCauchy" (pt "g") (pt "M") (pt "us"))
  (use "Conv")
  (use "M0")
  (use "MMon")
  (simp "vsDef")
  (assume "n2")
  (use "InitEqD")
  (use "NDef")
  (use "mProp")
 (assume "n@*us m~v")
 (assert "g m")
  (use "HProp2gVal" (pt "M") (pt "n"))
  (use "mProp")
  (use "MMon")
  (use "Truth")
 (assume "gm")
 (assert "a<<=lnorm(f(us m))")
  (use "gProp")
  (use "gm")
 (assume "a<<=lnorm(f(us m))")
 (assert "n*a<<=n*lnorm(f(us m))")
  (use "NatRatRealLeMonTimes")
  (use "Truth")
  (use "a<<=lnorm(f(us m))")
 (assume "n*a<<=n*lnorm(f(us m))")
 (assert "n*a<<=lnorm(n@@*f(us m))")
  (use "RealLeCompat"
      (pt "RealConstr([n1]RatConstr(NatToInt n)One*a)([k]Zero)")
      (pt "n*lnorm(f(us m))"))
  (use "RealRat")
  (use "RealTimesCorr")
  (use "RealRat")
  (use "NormLinNormReal")
  (use "RealRat")
  (use "NormLinNormReal")
  (use "RealEqRefl")
  (use "RealRat")
  (use "NormLinNormNatTimes")
  (use "n*a<<=n*lnorm(f(us m))")
  (simp "<-" "fLin*")
 (assume "n*a<<=lnorm(f(n@*us m))")
 (assert "n*a<<=lnorm(f v)")
  (use "BanachEqvCompat" (pt "(n@*us m)"))
  (use "n@*us m~v")
  (use "n*a<<=lnorm(f(n@*us m))")
 (assume "n*a<<=lnorm(f v)")
;; With lnorm(f v)<<=n0*a we get n*a<=n0*a contradicting n0<n
 (assert "n*a<=n0*a")
  (use "RealLeTransRat" (pt "lnorm(f v)"))
  (use "n*a<<=lnorm(f v)")
  (use "n0Prop")
 (assume "n*a<=n0*a")
 (assert "n0*a<n*a")
  (use "RatLtMonTimesNat")
  (use "0<a")
  (use "n0<n")
 (assume "n0*a<n*a")
 (assert "n*a<n*a")
  (use "RatLeLtTrans" (pt "n0*a"))
  (use "n*a<=n0*a")
  (use "n0*a<n*a")
  (ng #t)
 (assume "Absurd")
 (use "Absurd")
;;?_71:all n(n0<n -> (H g M n=Zero -> F) -> F) -> all m lnorm(f(us m))<<=b
;; Here we need that M is strictly monotonic, to use HProp0Cor
(assume "all n(n0<n -> (H g M n=Zero -> F) -> F)")
(assert "all n H g M n=Zero")
 (assume "n")
 (use "NatLeLtCases" (pt "n") (pt "n0"))
 (use "all n(n<=n0 -> H g M n=Zero)")
 (assume "n0<n")
 (use "StabAtom")
 (use "all n(n0<n -> (H g M n=Zero -> F) -> F)")
 (use "n0<n")
(assume "all n H g M n=Zero" "m")
(use "gProp")
(use "HProp01Cor" (pt "M") (pt "Succ m"))
(use "all n H g M n=Zero")
(assert "all n n<M(Succ n)")
 (ind)
 (use "NatLeLtTrans" (pt "M Zero"))
 (simp "M0")
 (use "Truth")
 (use "MStrMon")
 (use "Truth")
 (assume "n" "IH")
 (use "NatLtLeTrans" (pt "Succ(M(Succ n))"))
 (use "IH")
 (use "NatLtToSuccLe")
 (use "MStrMon")
 (use "Truth")
(assume "all n n<M(Succ n)")
(use "all n n<M(Succ n)")
;; 61
(assume "n" "hn0=n+1")
(intro 0)
(assert "ex n1,m(n1<=n0 & H g M n1=m+2)")
 (use "HFind")
 (use "M0")
 (simp "hn0=n+1")
 (assume "Absurd")
 (use "Absurd")
(assume "ex n,m(n<=n0 & H g M n=m+2)")
(by-assume "ex n,m(n<=n0 & H g M n=m+2)" "n1" "n1Prop")
(by-assume "n1Prop" "m" "mProp")
(ex-intro (pt "m"))
(use "gProp")
(use "HProp2gVal" (pt "M") (pt "n1"))
(use "mProp")
(use "MMon")
(use "Truth")
;; 42:ex n lnorm(f v)<<=n*a
(use "RealPosRatBound")
(use "NormLinNormReal")
(use "0<a")
;; 14 ex g all m(
;; (g m -> a<<=lnorm(f(us m))) andnc ((g m -> F) -> lnorm(f(us m))<<=b))
(ex-intro (pt "[m]negb(g1 m)"))
(ng #t)
(assume "m")
(split)
(assume "negb(g1 m)")
(use "g1Prop")
(cases (pt "g1 m"))
(assume "g1 m" "Useless")
(simphyp-with-to "negb(g1 m)" "g1 m" "Absurd")
(use "Absurd")
(assume "Useless" "Absurd")
(use "Absurd")
(assume "negb(g1 m) -> F")
(use "g1Prop")
(cases (pt "g1 m"))
(strip)
(use "Truth")
(assume "g1 m -> F")
(use "negb(g1 m) -> F")
(simp "g1 m -> F")
(use "Truth")
;; Proof finished.
(save "IshiharaTrickOneEx")

(remove-computation-rules-for (pt "H g M n"))
(remove-computation-rules-for (pt "(V xi)g M us n"))

(ppc (rename-variables
      (nt (proof-to-extracted-term
	   (theorem-name-to-proof "IshiharaTrickOneEx")))))

;; [f,us,M,a,a0,k]
;;  [let g
;;    ([n]negb(cAC([n0]cApproxSplitBooleRat a a0 lnorm(f(us n0))k)n))
;;    [let n
;;     (cRealPosRatBound
;;     lnorm(f((cXCompl xi)((V xi)g M us)([k0]abs(IntS(2*k0)max 0))))
;;     a)
;;     [case (H g M n)
;;      (Zero -> (DummyR nat))
;;      (Succ n0 -> Inl right(cHFind g M n))]]]

(pp "XCompl")
;; all us,M(
;;  all k,n,m(M k<=n -> n<m -> norm(us n@-us m)<<=1/2**k) ->
;;  ex v all k,n(M k<=n -> norm(v@-us n)<<=1/2**k))

(pp "RealPosRatBound")
;; all x,a(Real x -> 0<a -> ex n x<<=n*a)

(pp "ApproxSplitBooleRat")
;; all a,b,x,k(
;;  Real x ->
;;  1/2**k<=b-a -> ex boole((boole -> x<<=b) andnc ((boole -> F) -> a<<=x)))

(pp "AC")
;; all m ex boole (Pvar nat boole)^ m boole ->
;; ex g all m (Pvar nat boole)^ m(g m)

(pp "HFind")
;; all g,M,n(
;;  M Zero=Zero -> (H g M n=Zero -> F) -> ex n0,m(n0<=n & H g M n0=m+2))
