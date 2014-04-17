;; $Id: real.scm 2648 2013-09-16 07:39:11Z schwicht $

;; (load "~/git/minlog/init.scm")

;; (set! COMMENT-FLAG #f)
;; (libload "nat.scm")
;; (libload "numbers.scm")
;; (libload "simpreal.scm")
;; (set! COMMENT-FLAG #t)

(if (not (member "lib/simpreal.scm" LOADED-FILES))
    (myerror "First load lib/simpreal.scm"))

(display "loading real.scm ...") (newline)

;; Constructive Reals
;; ==================

;; To work with reals, we use a predicate constant Cauchy which takes
;; two arguments, a sequence of rationals and a modulus.

;; We introduce Cauchy as an inductively defined predicate (which may
;; in this case also be called a record).

(add-ids (list (list "Cauchy"
		     (make-arity (py "nat=>rat") (py "int=>nat"))))
	 '("allnc as^,M(all k,n,m(M k<=n -> M k<=m ->
                                  abs(as^ n-as^ m)<=1/2**k) ->
                      Cauchy as^ M)" "CauchyIntro"))

;; (define idpc
;;   (idpredconst-name-and-types-and-cterms-to-idpredconst "Cauchy" '() '()))

;; There are no types, since the clauses do not contain type variables,
;; and no cterms, since the clauses do not contain parameter predicate
;; variables.

;; (define aconst0 (number-and-idpredconst-to-intro-aconst 0 idpc))
;; (pp (aconst-to-formula aconst0))

;; Similarly, we introduce a predicate constant Mon, taking a sequence
;; of positive numbers as argument, to express monotonicity.

(add-ids (list (list "Mon" (make-arity (py "int=>nat"))))
	 '("allnc M(all k,l(k<=l -> M k<=M l) -> Mon M)" "MonIntro"))

;; The meaning of the predicate constants is determined by introduction
;; and elimination axioms:

;; "CauchyElim"
(set-goal
 "all as^,M(Cauchy as^ M ->
            all k,n,m(M k<=n -> M k<=m -> abs(as^ n-as^ m)<=1/2**k))")
(assume "as^" "M")
(elim)
(search)
;; Proof finished.
(save "CauchyElim")

;; "MonElim"
(set-goal "all M(Mon M -> all k,l(k<=l -> M k<=M l))")
(assume "M")
(elim)
(search)
;; Proof finished.
(save "MonElim")

;; We introduce Real as an inductively defined predicate (which in this
;; case may also be called a record).  Then we can prove theorems:

;; RealIntro: all x.Cauchy(x seq)(x mod) -> Mon(x mod) -> Real x
;; RealElim1: all as,M.Real(RealConstr as M) -> Cauchy as M
;; RealElim2: all as,M.Real(RealConstr as M) -> Mon M

;; Alternative formulation (worse, since usability is restricted)
;; RealIntro: all as,M.Cauchy as M -> Mon M -> Real RealConstr as M, 
;; RealElim1: all x.Real x -> Cauchy(x seq)(x mod)
;; RealElim2: all x.Real x -> Mon(x mod)

(add-ids
 (list (list "Real" (make-arity (py "rea"))))
 '("allnc x(Cauchy(x seq)(x mod) -> Mon(x mod) -> Real x)" "RealIntro"))

;; RealElim1"
(set-goal "all x(Real x -> Cauchy(x seq)(x mod))")
(assume "x")
(elim)
(auto)
;; Proof finished.
(save "RealElim1")

;; "RealElim2"
(set-goal "all x(Real x -> Mon(x mod))")
(assume "x")
(elim)
(auto)
;; Proof finished.
(save "RealElim2")

;; The following variants will be more useful, because their heads will
;; be more often of the form of a given goal.

;; "RealElimVariant1"
(set-goal "all as,M(Real(RealConstr as M) -> Cauchy as M)")
(strip)
(use-with "RealElim1" (pt "RealConstr as M") 1)
;; Proof finished.
(save "RealElimVariant1")

;; "RealElimVariant2"
(set-goal "all as,M(Real(RealConstr as M) -> Mon M)")
(strip)
(use-with "RealElim2" (pt "RealConstr as M") 1)
;; Proof finished.
(save "RealElimVariant2")

(set-goal "all x,y(Real x -> Real y -> x+y===y+x)")
(strip)
(ord-field-simp-bwd)
(use 1)
(use 2)
;; Proof finished.

;; (set-goal "all x,y,k,l(Real x -> Real y -> 
;;                RealLt 0(abs x)k -> RealLt 0(abs y)l ->
;;                0<<=x*y*((IntN 1#1)*x+y) ->
;;                1/y<<=1/x)")
;; (strip)
;; (ng)
;; (ord-field-simp-bwd)
;; (auto)
;; Need: ex n417 RealLt 0 abs y n417 
;; Have: RealLt 0 abs y k
;; Probably the creation of the need in ord-field-simp-bwd should be changed

;; To prove transitivity of equality, we need a characterization of
;; equality.

(add-global-assumption
 "RatAbsLe3"
 "all a,b,c,d(abs(a-b)<=abs(a-c)+abs(c-d)+abs(d-b))")

(add-global-assumption
 "RatPlusLe3"
 "all a1,a2,b1,b2,c1,c2(a1<=a2 -> b1<=b2 -> c1<=c2 -> a1+b1+c1<=a2+b2+c2)")

;; (add-global-assumption
;;  "PosLeTrans" "all pos1,pos2,p(pos1<=pos2 -> pos2<=p -> pos1<=p)")
(add-global-assumption "IntLeTrans" "all k,l,i(k<=l -> l<=i -> k<=i)")
(add-global-assumption "RatLeTrans" "all a,b,c(a<=b -> b<=c -> a<=c)")

(add-global-assumption "PosMaxUB1" "all pos1,pos2(pos1<=pos1 max pos2)")
(add-global-assumption "PosMaxUB2" "all pos1,pos2(pos2<=pos1 max pos2)")
(add-global-assumption "IntMaxUB1" "all i,j(i<=i max j)")
(add-global-assumption "IntMaxUB2" "all i,j(j<=i max j)")

;; We now prove one half of the characterization of equality for reals,
;; to be called "RealEqChar1"

;; In the following proof for the first time we benefit from omission
;; of the computation rule pos**(S m) -> pos*pos**m.

;; (display-program-constant "PosExp")

;; Maybe for 2**k with a nat 2 and an int k this is different.
;; (display-program-constant "NatExp")
;; (add-rewrite-rule "2**(k+1)" "2**k+2**k")
;; (add-rewrite-rule "2**(Succ(k+1))" "2**k+2**k+2**k")
;; (add-rewrite-rule "2**k+1" "2**k+2**k")

;; (set-goal "1/2**(Succ(k+1))+1/2**(k+1)+1/2**(Succ(k+1))<=1/2**k")
;; (ng)
;; (assume "k")
;; (ord-field-simp-bwd)

;; leaves open goals IntZero<abs 2  and IntZero<abs(2**k+2**k)

;; RealEqChar1
(set-goal "allnc as all M allnc bs all N(Cauchy as M -> Cauchy bs N ->
      RealConstr as M===RealConstr bs N -> 
      all k ex n1 all n(n1<=n -> abs(as n-bs n)<=1/2**k))")
(strip)
(ex-intro (pt "M(IntS(IntS k))max N(IntS(IntS k))"))
(strip)
(use "RatLeTrans" (pt "1/2**(IntS(IntS k))+1/2**(IntS k)+1/2**(IntS(IntS k))"))

;; ?_5: abs(as n-bs n)<=1/2**(IntS(IntS k))+1/2**(IntS k)+1/2**(IntS(IntS k))
(use "RatLeTrans" (pt "abs(as n-as(M(IntS(IntS k))))+
                       abs(as(M(IntS(IntS k)))-bs(N(IntS(IntS k))))+
                       abs(bs(N(IntS(IntS k)))-bs n)"))

;; ?_7: abs(as n-bs n)<=
;;      abs(as n-as(M(IntS(IntS k))))+abs(as(M(IntS(IntS k)))-bs(N(IntS(IntS k))))+abs(bs(N(IntS(IntS k)))-bs n) 
(use "RatAbsLe3")

;; ?_8: abs(as n-as(M(IntS(IntS k))))+abs(as(M(IntS(IntS k)))-bs(N(IntS(IntS k))))+abs(bs(N(IntS(IntS k)))-bs n)<=
;;      1/2**(IntS(IntS k))+1/2**(IntS k)+1/2**(IntS(IntS k)) 
(use "RatPlusLe3")

;; ?_9: abs(as n-as(M(IntS(IntS k))))<=1/2**(IntS(IntS k))
(use "CauchyElim" (pt "M"))
(use 1)
(use "NatLeTrans" (pt "(M(IntS(IntS k)))max(N(IntS(IntS k)))"))

(use "NatMaxUB1")
(use 4)
(use "Truth")

;; ?_10: abs(as(M(IntS(IntS k)))-bs(N(IntS(IntS k))))<=1/2**(IntS k)
(use "RealEqElimVariant")
(use 3)

;; ?_11: abs(bs(N(IntS(IntS k)))-bs n)<=1/2**(IntS(IntS k))
(use "CauchyElim" (pt "N"))
(use 2)
(use "Truth")
(use "NatLeTrans" (pt "(M(IntS(IntS k)))max(N(IntS(IntS k)))"))
(use "NatMaxUB2")
(use 4)

;; ?_6: 1/2**(IntS(IntS k))+1/2**(IntS k)+1/2**(IntS(IntS k))<=1/2**k from
(ord-field-simp-bwd)
;; Proof finished.
(save "RealEqChar1")

(define RealEqChar1-neterm
  (nt (proof-to-extracted-term (theorem-name-to-proof "RealEqChar1"))))
(pp RealEqChar1-neterm)
;; [M0,M1,k2]M0(IntS(IntS k2))max M1(IntS(IntS k2))

;; (define sproof (proof-to-soundness-proof (current-proof)))
;; (cdp sproof)

;; We now aim at the converse.  For this we need two auxiliary lemmata:

(add-global-assumption "RatLeCrit" "all a(all k 0<=a+1/2**k -> 0<=a)")
(add-global-assumption "RatLeAux1" "all a,b(0<=b-a -> a<=b)")
(add-global-assumption "RatLeAux2" "all a,b,c(a<=b+c -> 0<=b-a+c)")

;; We need this in a slightly generalized form:

;; RatLeCritGen
(set-goal "all a,b(all k a<=b+1/2**k -> a<=b)")
(assume "a" "b" "Est")
(use "RatLeAux1")
(use "RatLeCrit")
(assume "k")
(use "RatLeAux2")
(use "Est")
;; Proof finished.
(save "RatLeCritGen")

;; We now prove the other half of the characterization of equality for
;; reals, to be called "RealEqChar2".

;; RealEqChar2
(set-goal "all as,M,bs,N(Cauchy as M -> Cauchy bs N ->
           all k ex n0 all n(n0<=n -> abs(as n-bs n)<=1/2**k) ->
           RealConstr as M===RealConstr bs N)")
(strip)
(use "RealEqIntro")
(assume "k")
(use "RatLeCritGen")
(assume "l")
(ng #t)

;; ?_7: abs(as(M(IntS k))-bs(N(IntS k)))<=(2**l+2**k)/(2**k*2**l) 
(inst-with-to 3 (pt "l") "InstExHyp")
(drop 3)
(by-assume "InstExHyp" "n0" "InstExHypKernel")

;; We now want to use n as an abbreviation for the complex term
;; ((M(k+1))max(N(k+1)))max n0.  Hence we introduce via cut the
;; formula all n(n=term -> goal)

(cut "all n(n=((M(IntS k))max(N(IntS k)))max n0 ->
      abs(as(M(IntS k))-bs(N(IntS k)))<=
      1/2**k+(1/2**l))")
(assume "allHyp")
(use "allHyp" (pt "((M(IntS k))max(N(IntS k)))max n0"))
(prop)
(assume "n" "nDef")
(inst-with-to "InstExHypKernel" (pt "n") "Mid")
(drop  "InstExHypKernel")
(use "RatLeTrans" (pt "1/2**(IntS k)+
                        (1/2**l)+1/2**(IntS k)"))

;; ?_22: abs(as(M(IntS k))-bs(N(IntS k)))<=1/2**IntS k+1/2**l+1/2**IntS k 
(use "RatLeTrans" (pt "abs(as(M(IntS k))-as n)+abs(as n-bs n)+
                       abs(bs n-bs(N(IntS k)))"))

;; ?_24: abs(as(M(IntS k))-bs(N(IntS k)))<=
;;       abs(as(M(IntS k))-as n)+abs(as n-bs n)+abs(bs n-bs(N(IntS k))) 
(use "RatAbsLe3")

;; ?_25: abs(as(M(IntS k))-as n)+abs(as n-bs n)+abs(bs n-bs(N(IntS k)))<=
;;       1/2**IntS k+1/2**l+1/2**IntS k 
(use "RatPlusLe3")

;; ?_26: abs(as(M(IntS k))-as n)<=1/2**IntS k 
(use "CauchyElim" (pt "M"))
(use 1)
(prop)
(simp "nDef")
(use "NatLeTrans" (pt "NatMax(M(IntS k))(N(IntS k))"))
(use "NatMaxUB1")
(use "NatMaxUB1")
(use "Mid")
(simp "nDef")
(use "NatMaxUB2")

;; ?_28: abs(bs n-bs(N(IntS k)))<=1/2**IntS k 
(use "CauchyElim" (pt "N"))
(use 2)
(use "NatLeTrans" (pt "NatMax(M(IntS k))(N(IntS k))"))
(use "NatMaxUB2")
(simp "nDef")
(use "NatMaxUB1")
(use "Truth")

;; ?_23: 1/2**IntS k+1/2**l+1/2**IntS k<=1/2**k+1/2**l 
(ord-field-simp-bwd)
;; Proof finished.
(save "RealEqChar2")


;; The sum of two Cauchy sequences is a Cauchy sequence:

(add-global-assumption "RatAbsLe2" "all a,b,c abs(a-b)<=abs(a-c)+abs(c-b)")
(add-global-assumption
 "RatLeMonPlus"
 "all a1,a2,b1,b2(a1<=a2 -> b1<=b2 -> a1+b1<=a2+b2)")

(add-global-assumption "RatTimesAbs" "all a,b abs(a*b)==abs a*abs b")
(add-global-assumption "RatTriang2" "all a,b abs(a+b)<=abs a+abs b")
(add-global-assumption "RatEqvLe" "all a,b,c(a==b -> b<=c -> a<=c)")
(add-global-assumption "RatLeEq" "all a,b,c(a<=b -> b==c -> a<=c)")
(add-global-assumption "RatAbsCompat" "all a,b(a==b -> abs a==abs b)")

(set-goal "all as,M,bs,N(Cauchy as M -> Cauchy bs N -> 
           Cauchy ([n]as n+bs n) ([k](M(k+1))max(N(k+1))))")
(strip)
(use "CauchyIntro")
(strip)
(ng #t)

;; ?_5: abs(as n+bs n-(as m+bs m))<=1/2**k
(use "RatLeTrans" (pt "abs(as n-as m)+abs(bs n-bs m)"))

;; ?_6: abs(as n+bs n-(as m+bs m))<=abs(as n-as m)+abs(bs n-bs m)
(use "RatEqvLe" (pt "abs(as n-as m+(bs n-bs m))"))
(use "RatAbsCompat")

;; ?_10: as n+bs n-(as m+bs m)==as n-as m+(bs n-bs m)
(ord-field-simp-bwd)

;; ?_9: abs(as n-as m+(bs n-bs m))<=abs(as n-as m)+abs(bs n-bs m)
(use "RatTriang2")

;; ?_7: abs(as n-as m)+abs(bs n-bs m)<=1/2**k
(use "RatLeTrans" (pt "1/2**(k+1)+1/2**(k+1)"))

;; ?_11: abs(as n-as m)+abs(bs n-bs m)<=1/2**(k+1)+1/2**(k+1)
(use "RatLeMonPlus")

;; ?_13: abs(as n-as m)<=1/2**(k+1)
(use "CauchyElim" (pt "M"))

(use 1)
(use "NatLeTrans" (pt "(M(k+1))max(N(k+1))"))
(use "NatMaxUB1")
(ng)
(use 3)
(use "NatLeTrans" (pt "(M(k+1))max(N(k+1))"))
(use "NatMaxUB1")
(use 4)

;; ?_14: abs(bs n-bs m)<=1/2**(k+1)
(use "CauchyElim" (pt "N"))
(use 2)
(use "NatLeTrans" (pt "(M(k+1))max(N(k+1))"))
(use "NatMaxUB2")
(use 3)
(use "NatLeTrans" (pt "(M(k+1))max(N(k+1))"))
(use "NatMaxUB2")
(use 4)

;; ?_12: (1/2**k+1)+(1/2**k+1)<=1/2**k
(ord-field-simp-bwd)
;; Proof finished.
(save "CauchyPlus")

;; Every real has an upper bound, that is the reals are Archimedian ordered.

(add-global-assumption "RatMaxUB1" "all a,b a<=a max b")
(add-global-assumption "RatMaxUB2" "all a,b b<=a max b")
(add-global-assumption "RatAbsUB1" "all a a<=abs a")

;; We prove an auxiliary lemma.

;; RatSeqFinBound
(set-goal "all as,n ex a all m(m<n -> as m<=a)")
(assume "as")
(ind)
  (ex-intro (pt "IntP One#One"))
  (assume "m" "Absurd")
  (use "Efq")
  (use "Absurd")
(assume "n" "IH")
(by-assume "IH" "a" "H")
(ex-intro (pt "a max as n"))
(assume "m" "m<Succ n")
(use "NatLtSuccCases" (pt "n") (pt "m"))
(use "m<Succ n")
  (assume "m<n")
  (use "RatLeTrans" (pt "a"))
  (use-with "H" (pt "m") "m<n")
  (use "RatMaxUB1")
(assume "m=n")
(simp "m=n")
(use "RatMaxUB2")
;; Proof finished.
(save "RatSeqFinBound")

;; RealBound
(set-goal "all as,M(Cauchy as M -> ex a all n as n<=a)")
(assume "as" "M" "Cauchy as M")
(cut "ex a all m(m<M Zero -> as m<=a)")
(assume "ExHyp")
(by-assume "ExHyp" "a" "FinBound")
(ex-intro (pt "a max(as(M Zero))+1"))

;; ?_9: all n as n<=a max as(M Zero)+1 
(assume "n")
(cases (pt "n<M Zero"))
(assume "n<M Zero")
(use "RatLeTrans" (pt "a"))
(use "FinBound")
(use "n<M Zero")
(use "RatLeTrans" (pt "a max(as(M Zero))"))
(use "RatMaxUB1")
(use "Truth")

;; ?_12: (n<M Zero -> F) -> as n<=a max as(M Zero)+1 
(assume "n<M Zero -> F")
(use "RatLeTrans" (pt "as(M Zero)+(as n-as(M Zero))"))
(ord-field-simp-bwd)

;; ?_21: as(M Zero)+(as n-as(M Zero))<=a max as(M Zero)+1 
(use "RatLeMonPlus")
(use "RatMaxUB2")

;; ?_23: as n-as(M Zero)<=1 
(use "RatLeTrans" (pt "abs(as n-as(M Zero))"))
(use "RatAbsUB1")

;; ?_25: abs(as n-as(M Zero))<=1 
(use "RatLeTrans" (pt "IntP One/2**IntZero"))
(use "CauchyElim" (pt "M"))
(use "Cauchy as M")
(use "NatNotLtToLe")
(use "n<M Zero -> F")
(use "Truth")

(use "Truth")

(use "RatSeqFinBound")
;; Proof finished.
(save "RealBound")

;; (pp (nt (proof-to-extracted-term (theorem-name-to-proof "RealBound"))))
;; [as0,M1]cRatSeqFinBound as0(M1 0)max as0(M1 0)+1

;; The product of two Cauchy sequences is a Cauchy sequence:

(add-global-assumption
 "RatLeAbsTimes"
 "all a,b,a1,b1(abs a<=a1 -> abs b<=b1 -> abs a*abs b<=a1*b1)")

;; CauchyTimes
(set-goal "all as,M,bs,N,k1,k2(
      Cauchy as M -> 
      Cauchy bs N -> 
      Mon M -> 
      Mon N -> 
      all n abs(as n)<=2**k1 -> 
      all n abs(bs n)<=2**k2 -> 
      Cauchy([n]as n*bs n)([k]M(k+1+k2)max N(k+1+k1)))")
(strip)
(use "CauchyIntro")
(strip)
(ng)
(use "RatEqvLe" (pt "abs(as n*(bs n-bs m)+(as n-as m)*bs m)"))
(use "RatAbsCompat")
(ord-field-simp-bwd)

;; ?_7: abs(as n*(bs n-bs m)+(as n-as m)*bs m)<=1/2**k
(use "RatLeTrans" (pt "abs(as n*(bs n-bs m))+abs((as n-as m)*bs m)"))

;; ?_9: abs(as n*(bs n-bs m)+(as n-as m)*bs m)<=
;;      abs(as n*(bs n-bs m))+abs((as n-as m)*bs m) 
(use "RatTriang2")

;; ?_10: abs(as n*(bs n-bs m))+abs((as n-as m)*bs m)<=1/2**k
(use "RatLeTrans" (pt "1/2**(k+1)+1/2**(k+1)"))

;; ?_11: abs(as n*(bs n-bs m))+abs((as n-as m)*bs m)<=
;;       1/2**(k+1)+1/2**(k+1)
(use "RatLeMonPlus")

;; ?_13: abs(as n*(bs n-bs m))<=1/2**(k+1)
(use "RatEqvLe" (pt "abs(as n)*abs(bs n-bs m)"))

;; ?_15: abs(as n*(bs n-bs m))==abs(as n)*abs(bs n-bs m)
(use "RatTimesAbs")

;; ?_16: abs(as n)*abs(bs n-bs m)<=1/2**(k+1)
(use "RatLeTrans" (pt "(2**k1)*(1/2**(k+k1+1))"))

;; ?_17: abs(as n)*abs(bs n-bs m)<=2**k1*(1/2**(k+k1+1))

(use "RatLeAbsTimes")
(use 5)

;; ?_20: abs(bs n-bs m)<=(1/2**(k+k1+1))
(use "CauchyElim" (pt "N"))
(auto 1 '("PosMaxUB2" 1) '("PosLeTrans" 1))
(use "NatLeTrans" (pt "M(IntS(k+k2))max N(IntS(k+k1))"))
(use "NatMaxUB2")
(auto)
(use "NatLeTrans" (pt "M(IntS(k+k2))max N(IntS(k+k1))"))
(use "NatMaxUB2")
(auto)

;; ?_18: 2**k1*(1/2**(k+k1+1))<=(1/2**k+1) 
(ord-field-simp-bwd)

;; ?_14: abs((as n-as m)*bs m)<=1/2**(k+1)
(use "RatEqvLe" (pt "abs(as n-as m)*abs(bs m)"))
(use "RatTimesAbs")

;; ?_29: abs(as n-as m)*abs(bs m)<=1/2**(k+1) 
(use "RatLeTrans" (pt "(1/2**(k+k2+1))*(2**k2)"))

;; ?_41: abs(as n-as m)*abs(bs m)<=(1/2**(k+k2+1))*2**k2
(use "RatLeAbsTimes")

;; ?_43: abs(as n-as m)<=(1/2**(k+k2+1))
(use "CauchyElim" (pt "M"))
(auto 1 '("PosMaxUB1" 1) '("PosLeTrans" 1))
(use "NatLeTrans" (pt "M(IntS(k+k2))max N(IntS(k+k1))"))
(use "NatMaxUB1")
(auto)
(use "NatLeTrans" (pt "M(IntS(k+k2))max N(IntS(k+k1))"))
(use "NatMaxUB1")
(auto)

;; ?_42: (1/2**(k+k2+1))*2**k2<=1/2**(k+1)
(ord-field-simp-bwd)

;; ?_12: 1/2**(k+1)+1/2**(k+1)<=1/2**k
(ord-field-simp-bwd)
;; Proof finished.
(save "CauchyTimes")


;; 2007-09-05 Postponed: The inverse of a positive real is a real.
;; Needs treatment of 1/a for a>0
;; (add-global-assumption "RatLtLe" (pf "all a,b,c(a<b -> b<=c -> a<c)"))

;; (set-goal "all as,M,l(
;;        Cauchy as M -> 
;;        Mon M -> 
;;        all n 0<as n -> 
;;        all n(M(IntS l)<=n -> (1/2**(IntS l))<=as n) -> 
;;        Cauchy([n]1/as n)([k]M((IntS l)max(2*(IntS l)+k))))")
;; (assume "as" "M" "l" "Cauchy as M" "Mon M" "as-is-posseq" "as-pos-l")
;; (use "CauchyIntro")
;; (assume "k" "n" "m" "ModMaxn" "ModMaxm")
;; (ng)

;; ;; As auxiliary lemmata we provide M(IntS l)<=n and M(2*(IntS l)+k)<=n, and
;; ;; similarly for m.

;; (assert (pf "M(IntS l)<=n"))
;;   (use "NatLeTrans" (pt "M(IntS l max(2*IntS l+k))"))
;;   (use "MonElim")
;;   (use "Mon M")
;;   (use "IntMaxUB1")
;;   (use "ModMaxn")
;;   (assume "M(IntS l)<=n")
;; (assert (pf "M(2*(IntS l)+k)<=n"))
;;   (use "NatLeTrans" (pt "M(IntS l max(2*IntS l+k))"))
;;   (use "MonElim")
;;   (use "Mon M")
;;   (use "IntMaxUB2")
;;   (use "ModMaxn")
;;   (assume "M(2*(IntS l)+k)<=n")
;; (assert (pf "M(IntS l)<=m"))
;;   (use "NatLeTrans" (pt "M(IntS l max(2*IntS l+k))"))
;;   (use "MonElim")
;;   (use "Mon M")
;;   (use "IntMaxUB1")
;;   (use "ModMaxm")
;;   (assume "M(IntS l)<=m")
;; (assert (pf "M(2*(IntS l)+k)<=m"))
;;   (use "NatLeTrans" (pt "M(IntS l max(2*IntS l+k))"))
;;   (use "MonElim")
;;   (use "Mon M")
;;   (use "IntMaxUB2")
;;   (use "ModMaxm")
;;   (assume "M(2*(IntS l)+k)<=m")

;; ;; abs((as m-as n)/(as n*as m))<=1/2**k
;; (use "RatEqvLe" (pt "abs((1/as n)*(1/as m)*(as m-as n))")) ;error (undef)

;; ;; abs((as m-as n)/(as n*as m))==abs(1/as n*(1/as m)*(as m-as n))
;; (use "RatAbsCompat")

;; ;; (as m-as n)/(as n*as m)==1/as n*(1/as m)*(as m-as n)
;; (ord-field-simp-bwd)

;; ;; 0<abs(as n)
;; (use "RatLtLe" (pt "as n"))
;; (use "as-is-posseq")
;; (use "RatAbsUB1")

;; ;; 0<abs(as m)
;; (use "RatLtLe" (pt "as m"))
;; (use "as-is-posseq")
;; (use "RatAbsUB1")

;; ;; abs(1/as n*(1/as m)*(as m-as n))<=1/2**k
;; (use "RatLeTrans" (pt "(2**IntS l)*(2**IntS l)*
;;                         (1/2**(2*IntS l+k))"))

;; ;; abs(1/as n*(1/as m)*(as m-as n))<=2**IntS l*2**IntS l*(1/2**(2*IntS l+k))
;; (use "RatEqvLe" (pt "abs(1/as n*(1/as m))*abs(as m-as n)"))
;; (use "RatTimesAbs")

;; ;; abs(1/as n*(1/as m))*abs(as m-as n)<=2**IntS l*2**IntS l*(1/2**(2*IntS l+k))
;; (add-global-assumption
;;  "RatAbsTimes"
;;  (pf "all a^,b^,a^1,b^1
;;        (abs a^ <=a^1 -> abs b^ <=b^1 -> abs a^ *abs b^ <=a^1*b^1)"))
;; (use "RatAbsTimes")

;; ;; abs(1/as n*(1/as m))<=2**IntS l*2**IntS l
;; (use "RatEqvLe" (pt "abs(1/as n)*abs(1/as m)"))
;; (use "RatTimesAbs")
;; (use "RatLeEq" (pt "RatTimes(2**IntS l)(2**IntS l)"))
;; (use "RatAbsTimes")

;; ;; abs(1/as n)<=2**IntS l
;; (add-global-assumption "RatInvRat"
;; 		       (pf "all b^,a^((1/b^)<=a^ -> abs(1/a^)<=b^)"))
;; (use "RatInvRat")
;; (use "as-pos-l")
;; (use "M(IntS l)<=n")

;; ;; abs(1/as m)<=2**(IntS l)
;; (use "RatInvRat")
;; (use "as-pos-l")
;; (use "M(IntS l)<=m")

;; ;; 2**IntS l*2**IntS l==2**IntS l*2**IntS l
;; (use "Truth")

;; ;; abs(as m-as n)<=(1/2**(2*(IntS l)+k))
;; (use "CauchyElim" (pt "M"))
;; (auto 1)

;; ;;  2**IntS l*2**IntS l*(1/2**(2*IntS l+k))<=1/2**k
;; (ord-field-simp-bwd)
;; (ng)
;; (add-global-assumption
;;  "PosExpPlus" (pf "all nat1,nat2 2**(nat1+nat2)=2**nat1*2**nat2"))
;; (simp "PosExpPlus")
;; (simp "PosExpPlus")
;; (use "Truth")
;; ;; Proof finished.
;; (save "CauchyInv")		       

;; We now prove one half of the characterization of positivity for reals,
;; to be called "RealPosChar1"

(add-global-assumption
 "RatAbsLeMinusExp"
 "all rat1,int2(abs rat1<=(IntP One/2**int2) ->
                (IntN One/2**int2)<=rat1)")

;; RealPosChar1
(set-goal "allnc as 
      all M,k(
       Cauchy as M -> 
       RealPos(RealConstr as M)k -> ex l,n0 all n(n0<=n -> (1/2**l)<=as n))")
(strip)
(ex-intro (pt "IntS k"))
(ex-intro (pt "M(IntS k)"))
(strip)

;; (1/2**IntS k)<=as n
(use "RatEqvLe" (pt "(IntN 1/2**IntS k)+1/2**k"))

;; (1/2**IntS k)===((IntN 1/2**IntS k)+1/2**k)
(ord-field-simp-bwd)

;; (IntN 1/2**IntS k)+1/2**k<=as n
(use "RatLeTrans" (pt "as n-as(M(IntS k))+as(M(IntS k))"))
(use "RatLeMonPlus")

;; (IntN 1/2**IntS k)<=as n-as(M(IntS k))
(use "RatAbsLeMinusExp")

;; abs(as n-as(M(IntS k)))<=(1/2**IntS k)
(use "CauchyElim" (pt "M"))
(auto)

;; as n-as(M(IntS k))+as(M(IntS k))<=as n
(ord-field-simp-bwd)
;; Proof finished.
(save "RealPosChar1")

(define eterm (proof-to-extracted-term (theorem-name-to-proof "RealPosChar1")))
(define neterm (nt eterm))
(term-to-expr eterm)
(term-to-expr neterm)
(pp neterm)
;; [M0,k1]IntS k1@M0(IntS k1)

;; We prove that every real can be approximated by a rational "RealApprox"

(add-global-assumption
 "RealApproxAux"
 "all k,l,a1,a2,a3(abs(a1-a2)<=1/2**k -> abs(a2-a3)<=(1/2**l) ->
                   2**k*2**l*abs(a1-a3)<=2**k+2**l)")

;; RealApprox
(set-goal "all x,k(Real x -> ex a abs(a-x)<<=1/2**k)")
(ind)
(assume "as" "M" "k" "Real x")
(ex-intro (pt "as(M k)"))
(use "RealLeIntro")
(use "RealNNegIntro")
(assume "l")
(ng #t)
(ord-field-simp-bwd)

;; 2**k*2**l*abs(as(M k)-as(M(IntS(IntS l))))<=2**k+2**l 
(use "RealApproxAux" (pt "as(M k max M l)"))

;; abs(as(M k)-as(M k max M l))<=1/2**k
(use "CauchyElim" (pt "M"))
(use "RealElimVariant1")
(use "Real x")
(use "Truth")
(use "NatMaxUB1")

;; abs(as(M k max M l)-as(M(IntS(IntS l))))<=(1/2**l)
(use "CauchyElim" (pt "M"))
(use "RealElimVariant1")
(use "Real x")
(use "NatMaxUB2")
(use "MonElim")
(use "RealElimVariant2" (pt "as"))
(use "Real x")
(use "IntLeTrans" (pt "IntS l"))
(use "Truth")
(use "Truth")
;; Proof finished.
(save "RealApprox")

(define RealApprox-eterm
  (proof-to-extracted-term (theorem-name-to-proof "RealApprox")))
(define RealApprox-neterm (nt RealApprox-eterm))
(pp RealApprox-neterm)
;; [x0,k1][if x0 ([as2,M3]as2(M3 k1))]
(ppc RealApprox-neterm)
;; [x0,k1][case x0 (RealConstr as2 M3 -> as2(M3 k1))]

(pp (term-to-type RealApprox-neterm))
;; rea=>int=>rat

;; Example of a real.

(define real1 (pt "RealConstr([n]1-(1/2**n))([k]abs(k+1))"))

(pp (nt (mk-term-in-app-form RealApprox-neterm real1 (pt "2"))))
(pp (nt (mk-term-in-app-form RealApprox-neterm real1 (pt "9"))))
;; 1023#1024

;; Added 2013-08-04.  We now aim at defining RealTimes by computation
;; rules and proving RealTimesTotal.

;; The following should be the key to constructing a modulus for real
;; multiplication:

;; RatTimesDivTwoExp
(set-goal "all int1,int2 1/2**(int1+int2)*2**int2=1/2**int1")
(assume "int1" "int2")
(ord-field-simp-bwd)
;; Proof finished.
(save "RatTimesDivTwoExp")

(pp (nt (proof-to-extracted-term (theorem-name-to-proof "RatSeqFinBound"))))
;; [as0,n1](Rec nat=>rat)n1 1([n2,a3]a3 max as0 n2)

(pp (nt (proof-to-extracted-term (theorem-name-to-proof "RealBound"))))
;; [as0,M1]cRatSeqFinBound as0(M1 0)max as0(M1 0)+1

(animate "RatSeqFinBound")
(pp (nt (proof-to-extracted-term (theorem-name-to-proof "RealBound"))))
;; [as0,M1](Rec nat=>rat)(M1 0)1([n2,a3]a3 max as0 n2)max as0(M1 0)+1
(deanimate "RatSeqFinBound")

(pp "CauchyTimes")
;; all as,M,bs,N,k,k0(
;;  Cauchy as M -> 
;;  Cauchy bs N -> 
;;  Mon M -> 
;;  Mon N -> 
;;  all n abs(as n)<=2**k -> 
;;  all n abs(bs n)<=2**k0 -> Cauchy([n]as n*bs n)([k1]M(k1+1+k0)max N(k1+1+k)))

;; Rules for RealTimes.

(add-computation-rules
 "(RealConstr as M)*(RealConstr bs N)"
 "RealConstr([n]as n*bs n)([k1]M(k1+1+cRatLeAbsBound(cRealBound as M))max
                               N(k1+1+cRatLeAbsBound(cRealBound bs N)))")

(animate "RatLeBound")
(animate "RatSeqFinBound")
(animate "RatLeAbsBound")
(animate "RealBound")

(pp (nt (proof-to-extracted-term (theorem-name-to-proof "RatLeAbsBound"))))
;; uses cRatLeBound
(pp (nt (proof-to-extracted-term (theorem-name-to-proof "RealBound"))))
;; uses cRatSeqFinBound
(pp (nt (proof-to-extracted-term (theorem-name-to-proof "RatLeBound"))))
;; no auxiliary lemmas
(pp (nt (proof-to-extracted-term (theorem-name-to-proof "RatSeqFinBound"))))
;; no auxiliary lemmas

;; RealTimesTotal
(set-goal (rename-variables (term-to-totality-formula (pt "RealTimes"))))
(assume "x^" "Tx")
(elim "Tx")
(assume "as^" "Tas" "M^" "TM" "x^1" "Tx1")
(elim "Tx1")
(assume "bs^" "Tbs" "N^" "TN")
(ng #t)
(use "TotalReaRealConstr")
(assume "n^" "Tn")
(ng #t)
(use "RatTimesTotal")
(use "Tas")
(use "Tn")
(use "Tbs")
(use "Tn")
(assume "k^" "Tk")
(ng #t)
(use "NatMaxTotal")
(use "TM")
(use "IntPlusTotal")
(use "IntSTotal")
(use "Tk")
(use "RatIfTotal")
(use "RatPlusTotal")
(use "RatMaxTotal")
(use "NatRecTotal")
(use "TM")
(use "TotalIntIntZero")
(use "TotalRatRatConstr")
(use "TotalIntIntPos")
(use "TotalPosOne")
(use "TotalPosOne")
(assume "n^" "Tn" "a^" "Ta")
(use "RatMaxTotal")
(use "Ta")
(use "Tas")
(use "Tn")
(use "Tas")
(use "TM")
(use "TotalIntIntZero")
(use "TotalRatRatConstr")
(use "TotalIntIntPos")
(use "TotalPosOne")
(use "TotalPosOne")
(assume "i^" "p^" "Ti" "Tp")
(use "IntIfTotal")
(use "Ti")
(use "TotalIntIntZero")
(assume "q^" "Tq")
(use "IntMinusTotal")
(use "IntSTotal")
(use "NatToIntTotal")
(use "PosLogTotal")
(use "Tq")
(use "NatToIntTotal")
(use "PosLogTotal")
(use "Tp")
(assume "q^" "Tq")
(use "IntMinusTotal")
(use "IntSTotal")
(use "NatToIntTotal")
(use "PosLogTotal")
(use "Tq")
(use "NatToIntTotal")
(use "PosLogTotal")
(use "Tp")
;; 19
(use "TN")
(use "IntPlusTotal")
(use "IntSTotal")
(use "Tk")
(use "RatIfTotal")
(use "RatPlusTotal")
(use "RatMaxTotal")
(use "NatRecTotal")
(use "TN")
(use "TotalIntIntZero")
(use "TotalRatRatConstr")
(use "TotalIntIntPos")
(use "TotalPosOne")
(use "TotalPosOne")
(assume "n^" "Tn" "a^" "Ta")
(use "RatMaxTotal")
(use "Ta")
(use "Tbs")
(use "Tn")
(use "Tbs")
(use "TN")
(use "TotalIntIntZero")
(use "TotalRatRatConstr")
(use "TotalIntIntPos")
(use "TotalPosOne")
(use "TotalPosOne")
(assume "i^" "p^" "Ti" "Tp")
(use "IntIfTotal")
(use "Ti")
(use "TotalIntIntZero")
(assume "q^" "Tq")
(use "IntMinusTotal")
(use "IntSTotal")
(use "NatToIntTotal")
(use "PosLogTotal")
(use "Tq")
(use "NatToIntTotal")
(use "PosLogTotal")
(use "Tp")
(assume "q^" "Tq")
(use "IntMinusTotal")
(use "IntSTotal")
(use "NatToIntTotal")
(use "PosLogTotal")
(use "Tq")
(use "NatToIntTotal")
(use "PosLogTotal")
(use "Tp")
;; Proof finished.
(save "RealTimesTotal")

(deanimate "RatLeAbsBound")
(deanimate "RealBound")
(deanimate "RatSeqFinBound")
(deanimate "RatLeBound")

;; Rules for RealTimes.

(add-rewrite-rule
 "x*(RealConstr([n](RatConstr IntZero One))([k]Zero))"
 "RealConstr([n](RatConstr IntZero One))([k]Zero)")

(add-rewrite-rule
 "(RealConstr([n](RatConstr IntZero One))([k]Zero))*x"
 "RealConstr([n](RatConstr IntZero One))([k]Zero)")

(add-rewrite-rule
 "x*(RealConstr([n](RatConstr(IntP One)One))([k]Zero))" "x")

(add-rewrite-rule
 "(RealConstr([n](RatConstr(IntP One)One))([k]Zero))*x" "x")

(add-rewrite-rule "x1*(x2*x3)" "x1*x2*x3")

;; 2013-09-07.  Totality of pos int rat when lifted to rea

;; TotalReaPos
(set-goal "all pos TotalRea pos")
(use "AllTotalIntro")
(assume "pos^" "Tpos")
(elim "Tpos")
(use "TotalReaRealConstr")
(assume "n^" "Tn")
(ng #t)
(use "TotalRatRatConstr")
(use "TotalIntIntPos")
(use "TotalPosOne")
(use "TotalPosOne")
(assume "int^" "Tint")
(ng #t)
(use "TotalNatZero")
;; 5
(assume "pos^1" "Tpos1" "IHpos1")
(use "TotalReaRealConstr")
(assume "n^" "Tn")
(ng #t)
(use "TotalRatRatConstr")
(use "TotalIntIntPos")
(use "TotalPosSZero")
(use "Tpos1")
(use "TotalPosOne")
(assume "int^" "Tint")
(ng #t)
(use "TotalNatZero")
;; 6
(assume "pos^1" "Tpos1" "IHpos1")
(use "TotalReaRealConstr")
(assume "n^" "Tn")
(ng #t)
(use "TotalRatRatConstr")
(use "TotalIntIntPos")
(use "TotalPosSOne")
(use "Tpos1")
(use "TotalPosOne")
(assume "int^" "Tint")
(ng #t)
(use "TotalNatZero")
;; Proof finished.
(save "TotalReaPos")

(define eterm-reapos
  (proof-to-extracted-term (theorem-name-to-proof "TotalReaPos")))

(define neterm-reapos (rename-variables (nt eterm-reapos)))

(ppc neterm-reapos)
;; [p][case p (1 -> 1) (SZero p0 -> SZero p0) (SOne p0 -> SOne p0)]

;; TotalReaInt
(set-goal "all int TotalRea int")
(use "AllTotalIntro")
(assume "int^" "Tint")
(elim "Tint")
(use "AllTotalElim")
(use "TotalReaPos")
;; 5
(use "TotalReaRealConstr")
(assume "n^" "Tn")
(ng #t)
(use "TotalRatRatConstr")
(use "TotalIntIntZero")
(use "TotalPosOne")
(assume "int^1" "Tint1")
(ng #t)
(use "TotalNatZero")
;; 6
(assume "pos^" "Tpos")
(elim "Tpos")
(drop "Tpos")
(use "TotalReaRealConstr")
(assume "n^" "Tn")
(ng #t)
(use "TotalRatRatConstr")
(use "TotalIntIntNeg")
(use "TotalPosOne")
(use "TotalPosOne")
(assume "int^1" "Tint1")
(ng #t)
(use "TotalNatZero")
;; 18
(assume "pos^1" "Tpos1" "IHpos1")
(use "TotalReaRealConstr")
(assume "n^" "Tn")
(ng #t)
(use "TotalRatRatConstr")
(use "TotalIntIntNeg")
(use "TotalPosSZero")
(use "Tpos1")
(use "TotalPosOne")
(assume "int^1" "Tint1")
(ng #t)
(use "TotalNatZero")
;; 19
(assume "pos^1" "Tpos1" "IHpos1")
(use "TotalReaRealConstr")
(assume "n^" "Tn")
(ng #t)
(use "TotalRatRatConstr")
(use "TotalIntIntNeg")
(use "TotalPosSOne")
(use "Tpos1")
(use "TotalPosOne")
(assume "int^1" "Tint1")
(ng #t)
(use "TotalNatZero")
;; Proof finished.
(save "TotalReaInt")

(define eterm-reaint
  (proof-to-extracted-term (theorem-name-to-proof "TotalReaInt")))

(animate "TotalReaPos")

(define neterm-reaint (rename-variables (nt eterm-reaint)))

(pp neterm-reaint)
'(
[k]
 [case k
   (p -> [case p (1 -> 1) (SZero p0 -> SZero p0) (SOne p0 -> SOne p0)])
   (0 -> 0)
   (IntN p -> 
   [case p
     (1 -> IntN 1)
     (SZero p0 -> IntN(SZero p0))
     (SOne p0 -> IntN(SOne p0))])]
)

(deanimate "TotalReaPos")

;; TotalReaRat
(set-goal "all rat TotalRea rat")
(use "AllTotalIntro")
(assume "rat^" "Trat")
(elim "Trat")
(drop "Trat")
(assume "int^" "Tint")
(elim "Tint") ;6-8
(drop "Tint")
(assume "pos^" "Tpos")
(elim "Tpos")
(drop "Tpos")
(assume "pos^1" "Tpos1")
(use "TotalReaRealConstr")
(assume "n^" "Tn")
(ng #t)
(use "TotalRatRatConstr")
(use "TotalIntIntPos")
(use "TotalPosOne")
(use "Tpos1")
(assume "int^1" "Tint1")
(ng #t)
(use "TotalNatZero")
;; 12
(assume "pos^1" "Tpos1" "IHpos1" "pos^2" "Tpos2")
(use "TotalReaRealConstr")
(assume "n^" "Tn")
(ng #t)
(use "TotalRatRatConstr")
(use "TotalIntIntPos")
(use "TotalPosSZero")
(use "Tpos1")
(use "Tpos2")
(assume "int^1" "Tint1")
(ng #t)
(use "TotalNatZero")
;; 13
(assume "pos^1" "Tpos1" "IHpos1" "pos^2" "Tpos2")
(use "TotalReaRealConstr")
(assume "n^" "Tn")
(ng #t)
(use "TotalRatRatConstr")
(use "TotalIntIntPos")
(use "TotalPosSOne")
(use "Tpos1")
(use "Tpos2")
(assume "int^1" "Tint1")
(ng #t)
(use "TotalNatZero")
;; 7
(assume "pos^" "Tpos")
(elim "Tpos")
(drop "Tpos")
(use "TotalReaRealConstr")
(assume "n^" "Tn")
(ng #t)
(use "TotalRatRatConstr")
(use "TotalIntIntZero")
(use "TotalPosOne")
(assume "int^1" "Tint1")
(ng #t)
(use "TotalNatZero")
;; 49
(assume "pos^1" "Tpos1" "Useless")
(use "TotalReaRealConstr")
(assume "n^" "Tn")
(ng #t)
(use "TotalRatRatConstr")
(use "TotalIntIntZero")
(use "TotalPosSZero")
(use "Tpos1")
(assume "int^1" "Tint1")
(ng #t)
(use "TotalNatZero")
;; 50
(assume "pos^1" "Tpos1" "Useless")
(use "TotalReaRealConstr")
(assume "n^" "Tn")
(ng #t)
(use "TotalRatRatConstr")
(use "TotalIntIntZero")
(use "TotalPosSOne")
(use "Tpos1")
(assume "int^1" "Tint1")
(ng #t)
(use "TotalNatZero")
;; 8
(assume "pos^" "Tpos")
(elim "Tpos")
(drop "Tpos")
(assume "pos^1" "Tpos1")
(use "TotalReaRealConstr")
(assume "n^" "Tn")
(ng #t)
(use "TotalRatRatConstr")
(use "TotalIntIntNeg")
(use "TotalPosOne")
(use "Tpos1")
(assume "int^1" "Tint1")
(ng #t)
(use "TotalNatZero")
;; 82
(assume "pos^1" "Tpos1" "IHpos1" "pos^2" "Tpos2")
(use "TotalReaRealConstr")
(assume "n^" "Tn")
(ng #t)
(use "TotalRatRatConstr")
(use "TotalIntIntNeg")
(use "TotalPosSZero")
(use "Tpos1")
(use "Tpos2")
(assume "int^1" "Tint1")
(ng #t)
(use "TotalNatZero")
;; 83
(assume "pos^1" "Tpos1" "IHpos1" "pos^2" "Tpos2")
(use "TotalReaRealConstr")
(assume "n^" "Tn")
(ng #t)
(use "TotalRatRatConstr")
(use "TotalIntIntNeg")
(use "TotalPosSOne")
(use "Tpos1")
(use "Tpos2")
(assume "int^1" "Tint1")
(ng #t)
(use "TotalNatZero")
;; Proof finished.
(save "TotalReaRat")

(define eterm-rearat
  (proof-to-extracted-term (theorem-name-to-proof "TotalReaRat")))

(define neterm-rearat (rename-variables (nt eterm-rearat)))

(ppc neterm-rearat)

;; [a]
;;  [case a
;;    (k#p -> 
;;    [case k
;;      (p0 -> 
;;      [case p0 (1 -> 1#p) (SZero p1 -> SZero p1#p) (SOne p1 -> SOne p1#p)])
;;      (0 -> [case p (1 -> 0) (SZero p0 -> 0#SZero p0) (SOne p0 -> 0#SOne p0)])
;;      (IntN p0 -> 
;;      [case p0
;;        (1 -> IntN 1#p)
;;        (SZero p1 -> IntN(SZero p1)#p)
;;        (SOne p1 -> IntN(SOne p1)#p)])])]


;; 2013-09-05.  ApproxSplit and its corollaries, together with the
;; used global assumptions, moved here from cont.scm.  We formulate
;; ApproxSplit with oru rather than with ex boole.  The latter version
;; is called ApproxSplitBoole and proved from the present ApproxSplit
;; in cont.scm.

;; We will make use of some lemmata, that can be proved easily:

(add-global-assumption
 "RealLeCrit"
 "all x,y,n0(Real x -> Real y -> all n(n0<=n -> x seq n<=y seq n) -> x<<=y)")

(add-global-assumption
 "CauchyEstPlus"
 "all as,M(Cauchy as M -> all k,n,m(M k<=n -> M k<=m -> as n<=as m+1/2**k))")

(add-global-assumption
 "CauchyEstMinus"
 "all as,M(Cauchy as M -> all k,n,m(M k<=n -> M k<=m -> as n-1/2**k<=as m))")

(add-global-assumption
 "RatMinusLe2"
 "all a1,a2,b1,b2(a1<=a2 -> b2<=b1 -> a1-b1<=a2-b2)")

(add-global-assumption
 "ApproxSplitAux1" "all k 1/2**(k+2)==1/2**k/4")

(add-global-assumption
 "RatDivLe" "all a,b,c,d(a<=b -> 0<d -> d<=c -> a/c<=b/d)")

(add-global-assumption
 "RatLeLin" "all a,b((a<=b -> Pvar) -> (b<=a -> Pvar) -> Pvar)")

(add-var-name "L" (py "int=>nat"))

;; ApproxSplit
(set-goal "all x1,x2,x3,k(
 Real x1 -> Real x2 -> Real x3 -> RealLt x1 x2 k -> x3<<=x2 oru x1<<=x3)")
(ind)
(assume "as" "M")
(ind)
(assume "bs" "N")
(ind)
(assume "cs" "L")
(assume "k" "Rx1" "Rx2" "Rx3" "x1<x2")

;; We introduce a definition N(k+2)max M(k+2)=m
(cut "all m(N(k+2)max M(k+2)=m -> RealConstr cs L<<=RealConstr bs N oru
                                  RealConstr as M<<=RealConstr cs L)")
 (assume "mImp")
 (use "mImp" (pt "N(k+2)max M(k+2)"))
 (use "Truth")
 (assume "m" "mDef")

(cases (pt "cs(m max L(k+2))<=(as m+bs m)/2"))

;; Case cs(m max L(k+2))<=(as m+bs m)/2
(assume "CaseHyp")
(intro 0)
(use "RealLeCrit" (pt "m max L(k+2)"))
(use "Rx3")
(use "Rx2")
(assume "n" "m max L(k+2)<=n")
(cut "RealLt(RealConstr as M)(RealConstr bs N)k")
(drop "x1<x2")
(ng #t)
(simp "mDef")
(assume "Hyp") ;x1<x2
(cut "(1/2**(k+2))<=(bs m-as m)/4")
(assume "Hyp/4")

;; cs n<=bs n
(use "RatLeTrans" (pt "cs(m max L(k+2))+1/2**(k+2)"))

;; cs n<=cs(m max L(k+2))+1/2**(k+2)
(use "CauchyEstPlus" (pt "L"))
(auto 1 '("RealElimVariant1" 1))
(use "NatLeTrans" (pt "m max L(k+2)"))
(use "NatMaxUB2")
(use "m max L(k+2)<=n")
(use "NatMaxUB2")

;; cs(m max L(k+2))+1/2**(k+2)<=bs n
(use "RatLeTrans" (pt "(as m+bs m)/2 + (bs m-as m)/4"))

;; cs(m max L(k+2))+1/2**(k+2)<=(as m+bs m)/2+(bs m-as m)/4
(use "RatLeMonPlus")
(use "CaseHyp")
(use "Hyp/4")

;; (as m+bs m)/2+(bs m-as m)/4<=bs n
(use "RatEqvLe" (pt "bs m-(bs m-as m)/4"))
(ord-field-simp-bwd)

;; bs m-(bs m-as m)/4<=bs n
(use "RatLeTrans" (pt "bs m-1/2**(k+2)"))

;; bs m-(bs m-as m)/4<=bs m-1/2**(k+2)
(use "RatMinusLe2")
(use "Truth")
(use "Hyp/4")

;; bs m-1/2**(k+2)<=bs n
(use "CauchyEstMinus" (pt "N"))
(auto 1 '("RealElimVariant1" 1))
(cut "N(k+2)<=N(k+2)max M(k+2)")
(ng #t)
(simp "mDef")
(prop)
(use "NatMaxUB1")
(use "NatLeTrans" (pt "N(k+2)max M(k+2)"))
(use "NatMaxUB1")
(ng #t)
(simp "mDef")
(use "NatLeTrans" (pt "m max L(k+2)"))
(use "NatMaxUB1")
(use "m max L(k+2)<=n")

;; 1/2**(k+2)<=(bs m-as m)/4
(use "RatEqvLe" (pt "1/2**k/4"))
(use "ApproxSplitAux1")
(use "RatDivLe")
;; 2013-08-20.  The next command (use "Hyp") raised an error
;; Reason: the corrected computation rule for RealLt in libnumbers.scm:
;; (add-computation-rule
;;  "RealLt(RealConstr as M)(RealConstr bs N)k"
;;  "RealPos(RealConstr bs N-RealConstr as M)k")
;; Correction has already been done above.
(use "Hyp")
(use "Truth")
(use "Truth")

;; RealLt(RealConstr as M)(RealConstr bs N)k
(use "x1<x2")

;; (cs(m max L(k+2))<=(as m+bs m)/2 -> F) -> RealConstr as M<<=RealConstr cs L
(assume "CaseHyp")
(intro 1)
(use "RealLeCrit" (pt "m max L(k+2)"))
(auto)
(assume "n" "m max L(k+2)<=n")
(cut "RealLt(RealConstr as M)(RealConstr bs N)k")
(drop "x1<x2")
(ng #t)
(simp "mDef")
(assume "Hyp") ;x1<x2
(cut "1/2**(k+2)<=(bs m-as m)/4")
(assume "Hyp/4")

;; as n<=cs n
(use "RatLeTrans" (pt "as m+1/2**(k+2)"))

;; as n<=as m+1/2**(k+2)
(use "CauchyEstPlus" (pt "M"))
(auto 1 '("RealElimVariant1" 1))
(use "NatLeTrans" (pt "m max L(k+2)"))
(use "NatLeTrans" (pt "N(k+2)max M(k+2)"))
(use "NatMaxUB2")
(simp "mDef")
(use "NatMaxUB1")
(use "m max L(k+2)<=n")
(use "NatLeTrans" (pt "N(k+2)max M(k+2)"))
(use "NatMaxUB2")
(simp "mDef")
(use "Truth")

;: as m+1/2**(k+2)<=cs n
(use "RatLeTrans" (pt "as m+(bs m-as m)/4"))

;; as m+1/2**(k+2)<=as m+(bs m-as m)/4
(use "RatLeMonPlus")
(use "Truth")
(use "Hyp/4")

;; as m+(bs m-as m)/4<=cs n
(use "RatEqvLe" (pt "(as m+bs m)/2-(bs m-as m)/4"))

;; as m+(bs m-as m)/4==(as m+bs m)/2-(bs m-as m)/4
(ord-field-simp-bwd)

;; (as m+bs m)/2-(bs m-as m)/4<=cs n
(use "RatLeTrans" (pt "cs(m max L(k+2))-1/2**(k+2)"))

;; (as m+bs m)/2-(bs m-as m)/4<=cs(m max L(k+2))-1/2**(k+2)
(use "RatMinusLe2")
(use "RatLeLin" (pt "(as m+bs m)/2") (pt "cs(m max L(k+2))"))
 (assume "H1")
 (use "H1")
 (assume "H2")
 (use "Efq")
 (use "CaseHyp")
 (use "H2")
(use "Hyp/4")

;; cs(m max L(k+2))-1/2**(k+2)<=cs n
(use "CauchyEstMinus" (pt "L"))
(auto 1 '("RealElimVariant1" 1))
(use "NatMaxUB2")
(use "NatLeTrans" (pt "m max L(k+2)"))
(use "NatMaxUB2")
(use "m max L(k+2)<=n")

;; 1/2**(k+2)<=(bs m-as m)/4
(use "RatEqvLe" (pt "1/2**k/4"))
(use "ApproxSplitAux1")
(use "RatDivLe")
(use "Hyp")
(use "Truth")
(use "Truth")

;; RealLt(RealConstr as M)(RealConstr bs N)k
(use "x1<x2")
;; Proof finished.
(save "ApproxSplit")

(define ApproxSplit-eterm
  (proof-to-extracted-term (theorem-name-to-proof "ApproxSplit")))
(define ApproxSplit-neterm (rename-variables (nt ApproxSplit-eterm)))

(ppc ApproxSplit-neterm)

;; [x,x0,x1,k]
;;  [case x
;;    (RealConstr as M -> 
;;    [case x0
;;      (RealConstr as0 M0 -> 
;;      [case x1
;;        (RealConstr as1 M1 -> 
;;        as1(M0(IntS(IntS k))max M(IntS(IntS k))max M1(IntS(IntS k)))<=
;;        (as(M0(IntS(IntS k))max M(IntS(IntS k)))+
;;         as0(M0(IntS(IntS k))max M(IntS(IntS k))))/
;;        2)])])]

;; We prove that rationals are reals etc

;; RatLe0
(set-goal "all k 0<=1/2**k")
(ind)
(strip)
(use "Truth")
(use "Truth")
(strip)
(use "Truth")
;; Proof finished.
(save "RatLe0")

;; RealRat
(set-goal "all a Real a")
(assume "a")
(use "RealIntro")
(use "CauchyIntro")
(assume "k" "n" "m" "Useless1" "Useless2")
(ng #t)
(use "RatLe0")
;; ?_4:Mon(a mod)
(use "MonIntro")
(strip)
(use "Truth")
;; Proof finished.
(save "RealRat")

;; ApproxSplitRat
(set-goal "all a,b,x,k(Real x -> 1/2**k<=b-a -> x<<=b oru a<<=x)")
(assume "a" "b" "x" "k" "Rx" "1/2**k<=b-a")
(use "ApproxSplit" (pt "k"))
(use "RealRat")
(use "RealRat")
(use "Rx")
(ng #t)
(use "1/2**k<=b-a")
;; Proof finished.
(save "ApproxSplitRat")

(define ApproxSplitRat-eterm
  (proof-to-extracted-term (theorem-name-to-proof "ApproxSplitRat")))

(animate "ApproxSplit")

(define ApproxSplitRat-neterm (rename-variables (nt ApproxSplitRat-eterm)))

(ppc ApproxSplitRat-neterm)

;; [a,a0,x,k][case x (RealConstr as M -> as(M(IntS(IntS k)))<=(a+a0)/2)]

(deanimate "ApproxSplit")

;; ApproxSplitRatOne
(set-goal
 "all a,b allnc x^(TotalRea x^ -> Real x^ -> 1/2<=b-a -> x^ <<=b oru a<<= x^)")
(assume "a" "b")
(use "AllTotalElim")
(assume "x" "Rx" "1/2<=b-a")
(use "ApproxSplitRat" (pt "IntP One"))
(use "Rx")
(ng #t)
(use "1/2<=b-a")
;; Proof finished.
(save "ApproxSplitRatOne")

(define ApproxSplitRatOne-eterm
  (proof-to-extracted-term (theorem-name-to-proof "ApproxSplitRatOne")))

(animate "ApproxSplitRat")
(animate "ApproxSplit")

(define ApproxSplitRatOne-neterm
  (rename-variables (nt ApproxSplitRatOne-eterm)))

(ppc ApproxSplitRatOne-neterm)

;; [a,a0,x][case x (RealConstr as M -> as(M 3)<=(a+a0)/2)]

(deanimate "ApproxSplit")
(deanimate "ApproxSplitRat")

