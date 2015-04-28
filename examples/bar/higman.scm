;; 2015-04-25.  higman.scm.

(load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(libload "list.scm")
(set! COMMENT-FLAG #t)

(add-var-name "x" (py "alpha"))
(add-var-name "xs" (py "list alpha"))
(add-var-name "xss" (py "list list alpha"))
(add-var-name "yz" (py "alpha1 yprod alpha2"))
(add-var-name "yzs" (py "list(alpha1 yprod alpha2)"))

;; Additions to list.scm

(add-program-constant
 "ListTails" (py "list list alpha=>list list alpha") t-deg-zero)
(add-prefix-display-string "ListTails" "Tails")
(add-computation-rules
 "Tails(Nil list alpha)" "(Nil list alpha)"
 "Tails(xs::(list list alpha))" "Tail xs::Tails(list list alpha)")

(set-totality-goal "ListTails")
(assume "(list list alpha)^" "Txss")
(elim "Txss")
(use "TotalListNil")
(assume "xs^" "Txs" "(list list alpha)^1" "Txss1" "IH")
(ng #t)
(use "TotalListCons")
(use "ListTailTotal")
(use "Txs")
(use "IH")
;; Proof finished.
(save-totality)

;; HeadsAppd
(set-goal "all xss1,xss2 Heads(xss1++xss2)eqd Heads xss1++Heads xss2")
(ind)
(ng)
(assume "xss2")
(use "InitEqD")
(assume "xs1" "xss1" "IH")
(ng)
(assume "xss2")
(simp "IH")
(use "InitEqD")
;; Proof finished.
(save "HeadsAppd")

;; Rhts applied to a list of pairs returns the list of their right
;; hand sides.

(add-program-constant
 "ListRhts" (py "list(alpha1 yprod alpha2)=>list alpha2") t-deg-zero)
(add-prefix-display-string "ListRhts" "Rhts")
(add-computation-rules
 "Rhts(Nil alpha1 yprod alpha2)" "(Nil alpha2)"
 "Rhts(yz::yzs)" "rht yz::Rhts yzs")

(set-totality-goal "ListRhts")
(assume "yzs^" "Tyzs")
(elim "Tyzs")
(use "TotalListNil")
(assume "yz^" "Tyz" "yzs^1" "Tyzs1" "IH")
(ng #t)
(use "TotalListCons")
(use "PairTwoTotal")
(use "Tyz")
(use "IH")
;; Proof finished.
(save-totality)

(add-program-constant
 "ListLfts" (py "list(alpha1 yprod alpha2)=>list alpha1") t-deg-zero)
(add-prefix-display-string "ListLfts" "Lfts")
(add-computation-rules
 "Lfts(Nil alpha1 yprod alpha2)" "(Nil alpha1)"
 "Lfts(yz::yzs)" "lft yz::Lfts yzs")

(set-totality-goal "ListLfts")
(assume "yzs^" "Tyzs")
(elim "Tyzs")
(use "TotalListNil")
(assume "yz^" "Tyz" "yzs^1" "Tyzs1" "IH")
(ng #t)
(use "TotalListCons")
(use "PairOneTotal")
(use "Tyz")
(use "IH")
;; Proof finished.
(save-totality)

;; LhRhts
(set-goal "all yzs Lh Rhts yzs=Lh yzs")
(ind)
(use "Truth")
(assume "yz" "yzs" "IH")
(use "IH")
;; Proof finished.
(save "LhRhts")

;; LhLfts
(set-goal "all yzs Lh Lfts yzs=Lh yzs")
(ind)
(use "Truth")
(assume "yz" "yzs" "IH")
(use "IH")
;; Proof finished.
(save "LhLfts")

;; End of additions to list.scm

(remove-var-name "x" "xs" "xss" "yz" "yzs")

(remove-var-name "n" "m" "k")
(add-var-name "a" "b" "c" "n" "m" "k" "i" "j" (py "nat"))
(add-var-name "v" "w" "u" "as" "bs" "cs" "is" "js" "ks" (py "list nat"))
(add-var-name "ws" "vs" "us" "ass" "bss" (py "list list nat"))
(add-var-name "wss" "vss" (py "list list list nat"))

;; We consider a binary relation wqo (for well-quasiordering) on nat,
;; viewed as a total boolean-valued function.  We assume neither of
;; reflexivity, transitivity and antisymmetry.

(add-var-name "wqo" (py "nat=>nat=>boole"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Definitions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (vs sub ws) means vs is a sublist if ws (abbreviates ListListNatSub)
(add-program-constant
 "ListListNatSub" (py "list list nat=>list list nat=>boole") t-deg-zero)
(add-infix-display-string "ListListNatSub" "sub" 'rel-op)
(add-computation-rules
 "(Nil list nat)sub ws" "True"
 "(v::vs)sub(Nil list nat)" "False"
 "(v::vs)sub(w::ws)" "[if (v=w) (vs sub ws) ((v::vs)sub ws)]")

(set-totality-goal "ListListNatSub")
(use "AllTotalElim")
(ind)
(strip)
(ng)
(use "TotalBooleTrue")
(assume "v" "vs" "IHvs")
(use "AllTotalElim")
(ind)
(ng)
(use "TotalBooleFalse")
(assume "w" "ws" "IHws")
(ng)
(use "BooleIfTotal")
(use "BooleTotalVar")
(use "IHvs")
(use "ListTotalVar")
(use "IHws")
;; Proof finished.
(save-totality)

;; Emb wqo v w means v embeds into w w.r.t. wqo
;; v:  <------------aj----ai-------|
;;              /        /            ai <=_wqo bi, aj <=_wqo bj, i<j
;; w:  <---bj-----------bi---------|
(add-ids (list (list "Emb" (make-arity (py "nat=>nat=>boole")
				       (py "list nat") (py "list nat"))))
	 '("all wqo Emb wqo(Nil nat)(Nil nat)" "InitEmb")
	 '("all wqo,v,w,a(Emb wqo v w -> Emb wqo v(a::w))" "GenEmbInit")
	 '("all wqo,v,w,a,b(wqo a b -> Emb wqo v w -> Emb wqo(a::v)(b::w))"
	   "GenEmbCons"))

;; (LargerW wqo w ws) means that w is larger than (w.r.t. Emb) an
;; element wi of ws.
(add-ids (list (list "LargerW"
		     (make-arity (py "nat=>nat=>boole")
				 (py "list nat") (py "list list nat"))))
	 '("all wqo,w0,w,ws(Emb wqo w0 w -> LargerW wqo w(w0::ws))"
	   "InitLargerW")
	 '("all wqo,w0,w,ws(LargerW wqo w ws -> LargerW wqo w(w0::ws))"
	   "GenLargerW"))

;; GoodW wqo ws means that one v in ws embeds into a larger w in ws to its left.
(add-ids (list (list "GoodW" (make-arity (py "nat=>nat=>boole")
					(py "list list nat"))))
	 '("all wqo,w,ws(LargerW wqo w ws -> GoodW wqo(w::ws))" "InitGoodW")
	 '("all wqo,w,ws(GoodW wqo ws -> GoodW wqo(w::ws))" "GenGoodW"))

;; These are decidable n.c. relations and hence have equivalent
;; recursive versions, i.e., boolean valued functions given by
;; computation rules.  Atomic formulas written with them unfold when
;; normalized.  This can be helpful but can also be unwanted, since
;; one obtains if-terms and hence needs case distinctions.  Therefore
;; we define both versions and prove their equivalence.  Then one can
;; use either intro/elim or unfolding, as appropriate in the situation
;; at hand.

;; For a recursive version EmbR of Emb we need (R wqo a w), the rest
;; after the first the first b>=a (i.e., wqo a b) in w and (I wqo a w),
;; the initial segment of w before the first b>=a in w.

(add-program-constant
 "R" (py "(nat=>nat=>boole)=>nat=>list nat=>list nat") t-deg-zero)
(add-computation-rules
 "R wqo a(Nil nat)" "(Nil nat)"
 "R wqo a(b::w)" "[if (wqo a b) (b::w) (R wqo a w)]")

(set-totality-goal "R")
(assume "wqo^" "Twqo")
(use "AllTotalElim")
(assume "a")
(use "AllTotalElim")
(ind)
(ng)
(use "TotalListNil")
(assume "b" "w" "IHw")
(ng)
(use "BooleIfTotal")
(use "Twqo")
(use "NatTotalVar")
(use "NatTotalVar")
(use "ListTotalVar")
(use "IHw")
;; Proof finished.
(save-totality)

(add-program-constant
 "I" (py "(nat=>nat=>boole)=>nat=>list nat=>list nat") t-deg-zero)
(add-computation-rules
 "I wqo a(Nil nat)" "(Nil nat)"
 "I wqo a(b::w)" "[if (wqo a b) (Nil nat) (b::I wqo a w)]")

(set-totality-goal "I")
(assume "wqo^" "Twqo")
(use "AllTotalElim")
(assume "a")
(use "AllTotalElim")
(ind)
(ng)
(use "TotalListNil")
(assume "b" "w" "IHw")
(ng)
(use "BooleIfTotal")
(use "Twqo")
(use "NatTotalVar")
(use "NatTotalVar")
(use "TotalListNil")
(use "TotalListCons")
(use "NatTotalVar")
(use "IHw")
;; Proof finished.
(save-totality)

;; (L wqo a as) means a is leq an element of as.
(add-program-constant
 "L" (py "(nat=>nat=>boole)=>nat=>list nat=>boole") t-deg-zero)
(add-computation-rules
 "L wqo a(Nil nat)" "False"
 "L wqo a(b::as)" "[if (wqo a b) True (L wqo a as)]")

(set-totality-goal "L")
(assume "wqo^" "Twqo")
(use "AllTotalElim")
(assume "a")
(use "AllTotalElim")
(ind)
(ng)
(use "TotalBooleFalse")
(assume "b" "as" "IH")
(ng)
(use "BooleIfTotal")
(use "Twqo")
(use "NatTotalVar")
(use "NatTotalVar")
(use "TotalBooleTrue")
(use "IH")
;; Proof finished.
(save-totality)

(add-program-constant
 "EmbR" (py "(nat=>nat=>boole)=>list nat=>list nat=>boole") t-deg-zero)
(add-computation-rules
 "EmbR wqo(Nil nat)w" "True"
 "EmbR wqo(a::v)w" "L wqo a w andb EmbR wqo v Tail(R wqo a w)")

(set-totality-goal "EmbR")
(assume "wqo^" "Twqo")
(use "AllTotalElim")
(ind)
(ng)
(strip)
(use "TotalBooleTrue")
(assume "a" "v" "IHv")
(use "AllTotalElim")
;; Ind(w)
(ind)
(ng)
(use "TotalBooleFalse")
(assume "b" "w" "IHw")
(ng)
(use "AndConstTotal")
(use "BooleIfTotal")
(use "Twqo")
(use "NatTotalVar")
(use "NatTotalVar")
(use "TotalBooleTrue")
(use "LTotal")
(use "Twqo")
(use "NatTotalVar")
(use "ListTotalVar")
(use "IHv")
(use "ListTailTotal")
(use "BooleIfTotal")
(use "Twqo")
(use "NatTotalVar")
(use "NatTotalVar")
(use "ListTotalVar")
(use "RTotal")
(use "Twqo")
(use "NatTotalVar")
(use "ListTotalVar")
;; Proof finished.
(save-totality)

(add-program-constant
 "LargerWR" (py "(nat=>nat=>boole)=>list nat=>list list nat=>boole") t-deg-zero)
(add-computation-rules
 "LargerWR wqo v(Nil list nat)" "False"
 "LargerWR wqo v(w::ws)" "[if (EmbR wqo w v) True (LargerWR wqo v ws)]")

(set-totality-goal "LargerWR")
(assume "wqo^" "Twqo")
(use "AllTotalElim")
(assume "v")
(use "AllTotalElim")
(ind)
(ng)
(use "TotalBooleFalse")
(assume "w" "ws" "IHws")
(ng)
(use "BooleIfTotal")
(use "EmbRTotal")
(use "Twqo")
(use "ListTotalVar")
(use "ListTotalVar")
(use "TotalBooleTrue")
(use "IHws")
;; Proof finished.
(save-totality)

(add-program-constant
 "GoodWR" (py "(nat=>nat=>boole)=>list list nat=>boole") t-deg-zero)
(add-computation-rules
 "GoodWR wqo(Nil list nat)" "False"
 "GoodWR wqo(w::ws)" "[if (LargerWR wqo w ws) True (GoodWR wqo ws)]")

(set-totality-goal "GoodWR")
(assume "wqo^" "Twqo")
(use "AllTotalElim")
(ind)
(ng)
(use "TotalBooleFalse")
(assume "v" "ws" "IHws")
(ng)
(use "BooleIfTotal")
(use "LargerWRTotal")
(use "Twqo")
(use "ListTotalVar")
(use "ListTotalVar")
(use "TotalBooleTrue")
(use "IHws")
;; Proof finished.
(save-totality)

(add-program-constant
 "MapCons" (py "list nat=>list list nat=>list list nat") t-deg-zero)
(add-infix-display-string "MapCons" "mapcons" 'pair-op) ;right associative
(add-computation-rules
 "(a::as)mapcons v::vs" "(a::v)::as mapcons vs"
 "(Nil nat)mapcons vs" "(Nil list nat)"
 "as mapcons(Nil list nat)" "(Nil list nat)")

(set-totality-goal "MapCons")
(use "AllTotalElim")
(ind) ;on v
(ng)
(strip)
(use "TotalListNil")
(assume "a" "as" "IHas")
(use "AllTotalElim")
(cases) ;on ws
(ng)
(use "TotalListNil")
(assume "v" "vs")
(ng)
(use "TotalListCons")
(use "ListTotalVar")
(use "IHas")
(use "ListTotalVar")
;; Proof finished.
(save-totality)

;; (LargerAR wqo a as) means that a is larger than (w.r.t. wqo) an
;; element ai of as.
(add-program-constant
 "LargerAR" (py "(nat=>nat=>boole)=>nat=>list nat=>boole") t-deg-zero)
(add-computation-rules
 "LargerAR wqo b(Nil nat)" "False"
 "LargerAR wqo a(a0::as)" "[if (wqo a0 a) True (LargerAR wqo a as)]")

(set-totality-goal "LargerAR")
(assume "wqo^" "Twqo")
(use "AllTotalElim")
(assume "b")
(use "AllTotalElim")
(ind)
(ng)
(use "TotalBooleFalse")
(assume "a" "as" "IH")
(ng)
(use "BooleIfTotal")
(use "Twqo")
(use "NatTotalVar")
(use "NatTotalVar")
(use "TotalBooleTrue")
(use "IH")
;; Proof finished.
(save-totality)

;; (LargerARAll wqo a as) means that a is larger than (w.r.t. wqo) all
;; elements ai of as.
(add-program-constant
 "LargerARAll" (py "(nat=>nat=>boole)=>nat=>list nat=>boole") t-deg-zero)
(add-computation-rules
 "LargerARAll wqo b(Nil nat)" "True"
 "LargerARAll wqo a(a0::as)" "[if (wqo a0 a) (LargerARAll wqo a as) False]")

(set-totality-goal "LargerARAll")
(assume "wqo^" "Twqo")
(use "AllTotalElim")
(assume "a")
(use "AllTotalElim")
(ind)
(ng)
(use "TotalBooleTrue")
(assume "a0" "as" "IH")
(ng)
(use "BooleIfTotal")
(use "Twqo")
(use "NatTotalVar")
(use "NatTotalVar")
(use "IH")
(use "TotalBooleFalse")
;; Proof finished.
(save-totality)

;; LargerARAllConj
(set-goal "all wqo,a,a0,as
 LargerARAll wqo a(a0::as)=
 (wqo a0 a andb LargerARAll wqo a as)")
(assume "wqo" "a" "a0" "as")
(ng)
(simp "IfAndb")
(use "Truth")
;; Proof finished.
(save "LargerARAllConj")

;; (LargerARAllAll wqo a ass) means
;;   all_{i<Lh ass} all_{j<Lh(i thof ass)} wqo(j thof i thof ass)a
(add-program-constant
 "LargerARAllAll" (py "(nat=>nat=>boole)=>nat=>list list nat=>boole")
 t-deg-zero)
(add-computation-rules
 "LargerARAllAll wqo a(Nil list nat)" "True"
 "LargerARAllAll wqo a(as::ass)"
 "[if (LargerARAll wqo a as) (LargerARAllAll wqo a ass) False]")

(set-totality-goal "LargerARAllAll")
(assume "wqo^" "Twqo")
(use "AllTotalElim")
(assume "a")
(use "AllTotalElim")
(ind)
(ng)
(use "TotalBooleTrue")
(assume "as" "ass" "IH")
(ng)
(use "BooleIfTotal")
(use "LargerARAllTotal")
(use "AllTotalElim")
(assume "a1")
(use "AllTotalElim")
(assume "a2")
(use "Twqo")
(use "NatTotalVar")
(use "NatTotalVar")
(use "NatTotalVar")
(use "ListTotalVar")
(use "IH")
(use "TotalBooleFalse")
;; Proof finished.
(save-totality)

(add-program-constant
 "LargerARExAll" (py "(nat=>nat=>boole)=>nat=>list list nat=>boole") t-deg-zero)
(add-computation-rules
 "LargerARExAll wqo a(Nil list nat)" "False"
 "LargerARExAll wqo a(as::ass)"
 "[if (LargerARAll wqo a as) True (LargerARExAll wqo a ass)]")

(set-totality-goal "LargerARExAll")
(assume "wqo^" "Twqo")
(use "AllTotalElim")
(assume "a")
(use "AllTotalElim")
(ind)
(ng)
(use "TotalBooleFalse")
(assume "as" "ass" "IH")
(ng)
(use "BooleIfTotal")
(use "LargerARAllTotal")
(use "AllTotalElim")
(assume "a1")
(use "AllTotalElim")
(assume "a2")
(use "Twqo")
(use "NatTotalVar")
(use "NatTotalVar")
(use "NatTotalVar")
(use "ListTotalVar")
(use "TotalBooleTrue")
(use "IH")
;; Proof finished.
(save-totality)

;; (Incr wqo as) means that each ai is >= every later aj in as.
(add-program-constant
 "Incr" (py "(nat=>nat=>boole)=>list nat=>boole") t-deg-zero)
(add-computation-rules
 "Incr wqo(Nil nat)" "True"
 "Incr wqo(a::as)" "[if (LargerARAll wqo a as) (Incr wqo as) False]")

(set-totality-goal "Incr")
(assume "wqo^" "Twqo")
(use "AllTotalElim")
(ind)
(ng)
(use "TotalBooleTrue")
(assume "a" "as" "IHas")
(simp "Incr1CompRule")
(use "BooleIfTotal")
(use "LargerARAllTotal")
(use "Twqo")
(use "NatTotalVar")
(use "ListTotalVar")
(use "IHas")
(use "TotalBooleFalse")
;; Proof finished.
(save-totality)

;; IncrConj
(set-goal "all wqo,a,as 
 Incr wqo(a::as)=(LargerARAll wqo a as andb Incr wqo as)")
(assume "wqo" "a" "as")
(ng)
(simp "IfAndb")
(use "Truth")
;; Proof finished.
(save "IncrConj")

;; (Adm ws) means that each word in ws has a positive length
(add-program-constant "Adm" (py "list list nat=>boole") t-deg-zero)
(add-computation-rules
 "Adm(Nil list nat)" "True"
 "Adm(v::ws)" "0<Lh v andb Adm ws")

(set-totality-goal "Adm")
(use "AllTotalElim")
(ind)
(ng)
(use "TotalBooleTrue")
(assume "v" "ws" "IH")
(ng)
(use "AndConstTotal")
(use "BooleTotalVar")
(use "IH")
;; Proof finished.
(save-totality)

;; (BSeq wqo as) returns the canonical bad sequence in as, by leaving
;; out each a that would make the sequence good.

(add-program-constant
 "BSeq" (py "(nat=>nat=>boole)=>list nat=>list nat") t-deg-zero)
(add-computation-rules
 "BSeq wqo(Nil nat)" "(Nil nat)"
 "BSeq wqo(a::as)"
 "[if (LargerAR wqo a(BSeq wqo as)) (BSeq wqo as) (a::BSeq wqo as)]")

(set-totality-goal "BSeq")
(assume "wqo^" "Twqo")
(use "AllTotalElim")
(ind)
(use "TotalListNil")
(assume "a" "as" "IHas")
(ng)
(use "BooleIfTotal")
(use "LargerARTotal")
(use "Twqo")
(use "NatTotalVar")
(use "IHas")
(use "IHas")
(use "TotalListCons")
(use "NatTotalVar")
(use "IHas")
;; Proof finished.
(save-totality)

;; (pp (nt (pt "BSeq([n,m]m<=n)(3::0::1::3::2:)")))
;; 0::1::2:

;; A forest is a labelled nested tree (with (vs pair as) as labels).

(add-algs "lntree" 'prefix-typeop
	  '("alpha=>list lntree=>lntree" "LNBranch"))
(add-infix-display-string "LNBranch" "%" 'pair-op) ;right associative
(add-totality "lntree")
(add-rtotality "lntree")

;; (remove-var-name "x" "tx" "txs")
(add-var-name "x" (py "alpha"))
(add-var-name "tx" "sx" (py "lntree alpha"))
(add-var-name "txs" "sxs" (py "list lntree alpha"))

;; LntreeTotalVar
(set-goal "all tx TotalLntree tx")
(use "AllTotalIntro")
(assume "tx^" "Ttx")
(use "Ttx")
;; Proof finished.
(save "LntreeTotalVar")

;; Added 2014-12-23
;; RTotalLntreeToTotalLntree
(set-goal
 "allnc tx^((RTotalLntree (cterm (x^) Total x^))tx^ -> TotalLntree tx^)")
(assume "tx^" "RTtx")
(elim "RTtx")
(assume "x^" "Tx" "txs^" "Ttxs")
(use "TotalLntreeLNBranch")
(use "Tx")
(use "RTotalListMon"
     (make-cterm
      (pv "tx^")
      (pf "(RTotalLntree (cterm (x^) Total x^))tx^ andd TotalLntree tx^")))
(assume "tx^1" "Conj")
(use "Conj")
(use "Ttxs")
;; Proof finished.
(save "RTotalLntreeToTotalLntree")

;; TotalLntreeToRTotalLntree
(set-goal
 "allnc tx^(TotalLntree tx^ -> (RTotalLntree (cterm (x^) Total x^))tx^)")
(assume "tx^" "Ttx")
(elim "Ttx")
(assume "x^" "Tx" "txs^" "Ttxs")
(use "RTotalLntreeLNBranch")
(use "Tx")
(use "RTotalListMon"
     (make-cterm
      (pv "tx^")
      (pf "TotalLntree tx^ andd (RTotalLntree (cterm (x^) Total x^))tx^")))
(assume "tx^1" "Conj")
(use "Conj")
(use "Ttxs")
;; Proof finished.
(save "TotalLntreeToRTotalLntree")

;; Destructors
(add-program-constant "LntreeRoot" (py "lntree alpha=>alpha") t-deg-zero)
(add-prefix-display-string "LntreeRoot" "Root")
(add-computation-rules "Root(x%txs)" "x")

(set-totality-goal "LntreeRoot")
(assume "tx^" "Ttx")
(elim "Ttx")
(assume "x^" "Tx" "txs^" "Ttxs")
(ng)
(use "Tx")
;; Proof finished.
(save-totality)

(add-program-constant
 "LntreeSubtrees" (py "lntree alpha=>list lntree alpha") t-deg-zero)
(add-prefix-display-string "LntreeSubtrees" "Subtrees")
(add-computation-rules "Subtrees(x%txs)" "txs")

(set-unfolded-totality-goal "LntreeSubtrees")
(assume "tx^" "Ttx")
(elim "Ttx")
(assume "x^" "Tx" "txs^" "Ttxs")
(ng)
(use "RTotalListMon"
     (make-cterm (pv "tx^") (pf "(RTotalLntree (cterm (x^) Total x^))
                             tx^ andd 
                             (RTotalList (cterm (tx^) 
                                           (RTotalLntree (cterm (x^) 
                                                           Total x^))
                                           tx^))
                             (Subtrees tx^)")))
(assume "tx^1" "Conj")
(use "Conj")
(use "Ttxs")
;; Proof finished.
(save-totality)

;; (Roots txs) returns the list of roots of txs
(add-program-constant
 "LntreeRoots" (py "list lntree alpha=>list alpha") t-deg-zero)
(add-prefix-display-string "LntreeRoots" "Roots")
(add-computation-rules
 "Roots(Nil lntree alpha)" "(Nil alpha)"
 "Roots(tx::txs)" "Root tx::Roots txs")

(set-unfolded-totality-goal "LntreeRoots")
(assume "txs^" "Ttxs")
(elim "Ttxs")
(ng #t)
(use "RTotalListNil")
(assume "tx^" "Ttx" "txs^1" "Ttxs1" "IH")
(ng #t)
(use "RTotalListCons")
(use "LntreeRootTotal")
(use "RTotalLntreeToTotalLntree")
(use "Ttx")
(use "IH")
;; Proof finished.
(save-totality)

;; RootSubtreesId
(set-goal "all tx (Root tx%Subtrees tx)eqd tx")
(use "AllTotalIntro")
(assume "tx^" "Ttx")
(elim "Ttx")
(strip)
(ng #t)
(use "InitEqD")
;; Proof finished.
(save "RootSubtreesId")

;; LhRoots
(set-goal "all txs Lh Roots txs=Lh txs")
(ind)
(use "Truth")
(assume "tx" "txs" "IH")
(use "IH")
;; Proof finished.
(save "LhRoots")

;; RootsAppd
(set-goal "all txs,sxs Roots(txs++sxs)eqd Roots txs++Roots sxs")
(ind)
(strip)
(use "InitEqD")
(assume "tx" "txs" "IH")
(ng)
(assume "sxs")
(simp "IH")
(use "InitEqD")
;; Proof finished.
(save "RootsAppd")

;; (HtT tx) is the height of tx, and (HtF txs) the successor of the
;; maximum of the heights of its subtrees.
(add-program-constant "LntreeHeightT" (py "lntree alpha=>nat") t-deg-zero)
(add-prefix-display-string "LntreeHeightT" "HtT")

(add-program-constant "LntreeHeightF" (py "list lntree alpha=>nat") t-deg-zero)
(add-prefix-display-string "LntreeHeightF" "HtF")

(add-computation-rules
 "HtT(x%txs)" "Succ HtF txs")

(add-computation-rules
 "HtF(Nil lntree alpha)" "0"
 "HtF(tx::txs)" "Succ HtT tx max Succ HtF txs")

(set-totality-goal "LntreeHeightT" "LntreeHeightF")
(split)
(assume "tx^" "Ttx")
(elim "Ttx")
(assume "x^" "Tx" "txs^" "Ttxs")
(ng #t)
(use "TotalNatSucc")
(elim "Ttxs")
(ng #t)
(use "TotalNatZero")
(assume "tx^1" "Ttx1" "txs^1" "Ttxs1" "IH")
(ng #t)
(use "TotalNatSucc")
(use "NatMaxTotal")
(use "Ttx1")
(use "IH")
;; Case txs
(assume "txs^" "Ttxs")
(elim "Ttxs")
(ng #t)
(use "TotalNatZero")
(assume "tx^" "Ttx" "txs^1" "Ttxs1" "IH")
(ng #t)
(use "TotalNatSucc")
(use "NatMaxTotal")
(elim "Ttx")
(assume "x^" "Tx" "txs^2" "Ttxs2")
(ng #t)
(use "TotalNatSucc")
(elim "Ttxs2")
(ng #t)
(use "TotalNatZero")
(assume "tx^1" "Ttx1" "txs^3" "Ttxs3" "IHtxs3")
(ng #t)
(use "TotalNatSucc")
(use "NatMaxTotal")
(use "Ttx1")
(use "IHtxs3")
(use "IH")
;; Proof finished.
(save-totality)

(add-var-name "t" "s" (py "lntree(list list nat yprod list nat)"))
(add-var-name
 "ts" "ss" "rs" (py "list(lntree(list list nat yprod list nat))"));or x?
(add-var-name "vsas" "usas" (py "list list nat yprod list nat"))
(add-var-name "vsass" (py "list(list list nat yprod list nat)"))

;; Digression: an alternative with general destructors.
;; In src/pconst.scm destructor constants are generally defined and
;; given t-deg-one

;; (pp (pt "(Destr lntree(list list nat yprod list nat))t"))
;; ;; Des t
;; (pp (term-to-type (pt "DesYprod t")))
;; (pp (term-to-type (pt "rht DesYprod t")))
;; (pp (term-to-type (pt "lft lft DesYprod t")))
;; (pp (term-to-type (pt "rht lft DesYprod t")))

;; (pp (nt (pt "(lft lft DesYprod((vs pair as)%ts))")))
;; ;; vs
;; (pp (nt (pt "(rht lft DesYprod((vs pair as)%ts))")))
;; ;; as
;; (pp (nt (pt "(rht DesYprod((vs pair as)%ts))")))
;; ;; ts

;; We will need some EqToEqD theorems (for certain finitary algebras).
;; The presence of the nested algebra lntree makes it necessary to use
;; induction on HtT and HtF in between.

;; YprodListListNatListNatEqToEqD
(set-goal "all vsas_1,vsas_2(vsas_1=vsas_2 -> vsas_1 eqd vsas_2)")
(cases)
(assume "ws1" "w1")
(cases)
(assume "ws2" "w2")
(ng)
(assume "Conj")
(assert "ws1 eqd ws2")
(use "ListListNatEqToEqD")
(use "Conj")
(assume "ws1 eqd ws2")
(simp "ws1 eqd ws2")
(assert "w1 eqd w2")
(use "ListNatEqToEqD")
(use "Conj")
(assume "w1 eqd w2")
(simp "w1 eqd w2")
(use "InitEqD")
;; Proof finished.
(save "YprodListListNatListNatEqToEqD")

;; ListYprodListListNatListNatEqToEqD
(set-goal "all vsass_1,vsass_2(vsass_1=vsass_2 -> vsass_1 eqd vsass_2)")
(ind)
;; Base
(cases)
(assume "Useless")
(use "InitEqD")
(assume "vsas" "vsass" "Nil=vsas::vsass")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "Nil=vsas::vsass")
;; Step
(assume "vsas1" "vsass1" "IH")
(cases)
(assume "vsas1::vsass1=Nil")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "vsas1::vsass1=Nil")
(assume "vsas2" "vsass2" "(vsas1::vsass1)=(vsas2::vsass2)")
(ng "(vsas1::vsass1)=(vsas2::vsass2)")
(assert "vsass1 eqd vsass2")
 (use "IH")
 (use "(vsas1::vsass1)=(vsas2::vsass2)")
(assume "vsass1 eqd vsass2")
(assert "vsas1 eqd vsas2")
 (use "YprodListListNatListNatEqToEqD")
 (use "(vsas1::vsass1)=(vsas2::vsass2)")
(assume "vsas1 eqd vsas2")
(elim "vsass1 eqd vsass2")
(assume "vsass^1")
(elim "vsas1 eqd vsas2")
(assume "vsas^1")
(use "InitEqD")
;; Proof finshed.
(save "ListYprodListListNatListNatEqToEqD")

;; Now we do the same with another finitary algebra instead of nat, namely
;; (list list nat yprod list nat).  Instead of a,b take vsas usas

;; LntreeYprodListListNatListNatEqToEqDAux
(set-goal "all n(all t,s(HtT t<n -> HtT s<n -> t=s -> t eqd s) &
                 all ts,ss(HtF ts<n -> HtF ss<n -> ts=ss -> ts eqd ss))")
(ind)
(split)
(assume "t" "s")
(ng)
(use "Efq")
(assume "ts" "ss")
(ng)
(use "Efq")
(assume "n" "IHn")
(split)
(assume "t" "s")
(assert "(Root t%Subtrees t)eqd t")
 (use "RootSubtreesId")
(assume "(Root t%Subtrees t)eqd t")
(simp "<-" "(Root t%Subtrees t)eqd t")
(ng #t)
(assume "HtF Subtrees t<n")
(assert "(Root s%Subtrees s)eqd s")
 (use "RootSubtreesId")
(assume "(Root s%Subtrees s)eqd s")
(simp "<-" "(Root s%Subtrees s)eqd s")
(ng #t)
(assume "HtF Subtrees s<n" "Conj")
(assert "Root t eqd Root s")
(use "YprodListListNatListNatEqToEqD")
(use "Conj")
(assume "Root t eqd Root s")
(assert "Subtrees t eqd Subtrees s")
(use "IHn")
(use "HtF Subtrees t<n")
(use "HtF Subtrees s<n")
(use "Conj")
(assume "Subtrees t eqd Subtrees s")
(simp "Root t eqd Root s")
(simp "Subtrees t eqd Subtrees s")
(use "InitEqD")
;; all ts,ss(HtF ts<Succ n -> HtF ss<Succ n -> ts=ss -> ts eqd ss)
(cases)
(cases)
(strip)
(use "InitEqD")
(assume "s" "ss" "Useless1" "Useless2")
(ng #t)
(use "Efq")
(assume "t" "ts")
(cases)
(assume "Useless1" "Useless2")
(ng #t)
(use "Efq")
(assume "s" "ss")
(ng #t)
(assume "HtT t max HtF ts<n" "HtT s max HtF ss<n" "Conj")
;; t eqd s
(assert "t eqd s")
(use "IHn")
(use "NatLeLtTrans" (pt "HtT t max HtF ts"))
(use "NatMaxUB1")
(use "HtT t max HtF ts<n")
(use "NatLeLtTrans" (pt "HtT s max HtF ss"))
(use "NatMaxUB1")
(use "HtT s max HtF ss<n")
(use "Conj")
(assume "t eqd s")
;; ts eqd ss
(assert "ts eqd ss")
(use "IHn")
(use "NatLeLtTrans" (pt "HtT t max HtF ts"))
(use "NatMaxUB2")
(use "HtT t max HtF ts<n")
(use "NatLeLtTrans" (pt "HtT s max HtF ss"))
(use "NatMaxUB2")
(use "HtT s max HtF ss<n")
(use "Conj")
(assume "ts eqd ss")
;; Now we are done
(simp "t eqd s")
(simp "ts eqd ss")
(use "InitEqD")
;; Proof finished.
(save "LntreeYprodListListNatListNatEqToEqDAux")

;; LntreeYprodListListNatListNatEqToEqD
(set-goal "all t,s(t=s -> t eqd s)")
(assume "t" "s")
(use-with "LntreeYprodListListNatListNatEqToEqDAux"
	  (pt "Succ(HtT t max HtT s)") 'left (pt "t") (pt "s") "?" "?")
(use "NatLeLtTrans" (pt "HtT t max HtT s"))
(use "NatMaxUB1")
(use "Truth")
(use "NatLeLtTrans" (pt "HtT t max HtT s"))
(use "NatMaxUB2")
(use "Truth")
;; Proof finished.
(save "LntreeYprodListListNatListNatEqToEqD")

;; ListLntreeYprodListListNatListNatEqToEqD
(set-goal "all ts,ss(ts=ss -> ts eqd ss)")
(assume "ts" "ss")
(use-with "LntreeYprodListListNatListNatEqToEqDAux"
	  (pt "Succ(HtF ts max HtF ss)") 'right (pt "ts") (pt "ss") "?" "?")
(use "NatLeLtTrans" (pt "HtF ts max HtF ss"))
(use "NatMaxUB1")
(use "Truth")
(use "NatLeLtTrans" (pt "HtF ts max HtF ss"))
(use "NatMaxUB2")
(use "Truth")
;; Proof finished.
(save "ListLntreeYprodListListNatListNatEqToEqD")

;; (NewTree vsas) returns (vs pair as)%[]
;; (remove-program-constant "NewTree")
(add-program-constant
 "NewTree" (py "list list nat yprod list nat=>
                lntree(list list nat yprod list nat)") t-deg-zero)
(add-computation-rules
 "NewTree(vs pair(Nil nat))"
 "(vs pair(Nil nat))%(Nil lntree(list list nat yprod list nat))"
 "NewTree(vs pair a:)"
 "(vs pair a:)%(Nil lntree(list list nat yprod list nat))"
 "NewTree(vs pair a::b::as)"
 "(vs pair a::b::as)%(Nil lntree(list list nat yprod list nat))")

(set-unfolded-totality-goal "NewTree")
(assume "vsas^" "Tvsas")
(elim "Tvsas")
(assume "ws^" "Tws" "as^" "Tas")
(elim "Tas")
(ng #t)
(use "RTotalLntreeLNBranch")
(use "RTotalYprodPairConstr")
(use "Tws")
(use "RTotalListNil")
(use "RTotalListNil")
(assume "a^" "Ta" "as^1" "Tas1")
(elim "Tas1")
(ng #t)
(assume "Useless")
(use "RTotalLntreeLNBranch")
(use "RTotalYprodPairConstr")
(use "Tws")
(use "RTotalListCons")
(use "Ta")
(use "RTotalListNil")
(use "RTotalListNil")
(assume "a^1" "Ta1" "as^2" "Tas2")
(ng #t)
(assume "Hyp1" "Hyp2")
(use "RTotalLntreeLNBranch")
(use "RTotalYprodPairConstr")
(use "Tws")
(use "RTotalListCons")
(use "Ta")
(use "RTotalListCons")
(use "Ta1")
(use "Tas2")
(use "RTotalListNil")
;; Proof finished.
(save-totality)

;; NewTreeDef
(set-goal "all vsas 
 NewTree vsas=(vsas%(Nil lntree(list list nat yprod list nat)))")
(ind)
(assume "ws")
(cases)
(ng)
(use "Truth")
(assume "a")
(cases)
(ng)
(use "Truth")
(ng)
(strip)
(use "Truth")
;; Proof finished.
(save "NewTreeDef")

;; (InsertT wqo t v a) returns the result of inserting v and a into
;; t, as follows.  Let t be vsas%ts.  If a is not above all elements
;; of the rhs of some root in ts, then extend ts by a new tree
;; consisting of a root only, formed by appending v to (lft vsas) and
;; a to (rht vsas).  Otherwise recursively insert v and a into ts.

;; (remove-program-constant "InsertT" "InsertF")
(add-program-constant
 "InsertT" (py "(nat=>nat=>boole)=>lntree(list list nat yprod list nat)=>
                 list nat=>nat=>lntree(list list nat yprod list nat)")		
 t-deg-zero)

(add-program-constant
 "InsertF"
 (py "(nat=>nat=>boole)=>list lntree(list list nat yprod list nat)=>
      list nat=>nat=>list lntree(list list nat yprod list nat)")
 t-deg-zero)

;; (pp (pt "LargerARExAll wqo a Rhts Roots ts"))

(add-computation-rules
 "InsertT wqo(vsas%ts)v a"
 "vsas%[if (LargerARExAll wqo a Rhts Roots ts)
           (InsertF wqo ts v a)
           (NewTree((v::lft vsas)pair a::rht vsas)::ts)]")

(add-computation-rules
 "InsertF wqo(Nil lntree(list list nat yprod list nat))v a"
 "(Nil lntree(list list nat yprod list nat))"
 "InsertF wqo(t::ts)v a"
 "[if (LargerARAll wqo a rht Root t) (InsertT wqo t v a) t]::
  InsertF wqo ts v a")

(set-totality-goal "InsertT" "InsertF")
(assert "all wqo,a,v,n(
 all t(HtT t<n -> TotalLntree(InsertT wqo t v a)) &
 all ts(HtF ts<n -> TotalList(InsertF wqo ts v a)))")
(assume "wqo" "a" "v")
(ind)
;; Base
(split)
(assume "t")
(ng)
(use "Efq")
(assume "ts")
(ng)
(use "Efq")
(assume "n" "IH")
(split)
;; Case t
(assume "t")
(simp "<-" "RootSubtreesId")
(simp "LntreeHeightT0CompRule")
(assume "HtF Subtrees t<n")
(ng "HtF Subtrees t<n")
(simp "InsertT0CompRule")
(cases (pt "(LargerARExAll wqo a Rhts Roots Subtrees t)"))
;; Case True
(assume "Useless")
(use  "TotalLntreeLNBranch")
(use "YprodTotalVar")
(use "TotalListToRTotalList")
(use "BooleIfTotal")
(use "TotalBooleTrue")
(use "IH")
(use "HtF Subtrees t<n")
(use "ListTotalVar")
;; Case False
(assume "Useless")
(use "LntreeTotalVar")
;; Case ts
;; all ts(HtF ts<Succ n -> TotalList(InsertF wqo ts v a))
(ind)
;; Base
(ng #t)
(assume "Useless")
(use "TotalListNil")
;; Step
(assume "t" "ts" "IHtF" "HtBound")
(ng "HtBound")
(ng #t)
(use "TotalListCons")
(use "BooleIfTotal")
(use "BooleTotalVar")
(use "IH")
(use "NatLeLtTrans" (pt "HtT t max HtF ts"))
(use "NatMaxUB1")
(use "HtBound")
(use "LntreeTotalVar")
(use "IH")
(use "NatLeLtTrans" (pt "HtT t max HtF ts"))
(use "NatMaxUB2")
(use "HtBound")
;; Now the assertion is proved.
(assume "InsertTInsertFTotalAux")
(split)
;; Case t
(use (make-proof-in-aconst-form
      (aconst-substitute
       alltotal-elim-aconst
       (list
	(list (py "alpha") (py "nat=>nat=>boole"))
	(list (make-pvar (make-arity (py "alpha")) -1 h-deg-zero n-deg-zero "")
	      (make-cterm
	       (pv "wqo^")
	       (pf "allnc t^(
      TotalLntree t^ -> 
      allnc v^(
       TotalList v^ -> 
       allnc a^(TotalNat a^ -> TotalLntree(InsertT wqo^ t^ v^ a^))))")))))))
(assume "wqo")
(use "AllTotalElim")
(assume "t")
(use "AllTotalElim")
(assume "v")
(use "AllTotalElim")
(assume "a")
(use "InsertTInsertFTotalAux" (pt "Succ HtT t"))
(use "Truth")
;; Case ts
(use (make-proof-in-aconst-form
      (aconst-substitute
       alltotal-elim-aconst
       (list
	(list (py "alpha") (py "nat=>nat=>boole"))
	(list (make-pvar (make-arity (py "alpha")) -1 h-deg-zero n-deg-zero "")
	      (make-cterm
	       (pv "wqo^")
	       (pf "allnc ts^(
      TotalList ts^ -> 
      allnc v^(
       TotalList v^ -> 
       allnc a^(TotalNat a^ -> TotalList(InsertF wqo^ ts^ v^ a^))))")))))))
(assume "wqo")
(use "AllTotalElim")
(assume "ts")
(use "AllTotalElim")
(assume "v")
(use "AllTotalElim")
(assume "a")
(use "InsertTInsertFTotalAux" (pt "Succ HtF ts"))
(use "Truth")
;; Proof finished.
(save-totality)

;; (Forest wqo ws) returns a list of labeled trees.
(add-program-constant
 "Forest" (py "(nat=>nat=>boole)=>list list nat=>
               list(lntree(list list nat yprod list nat))") t-deg-zero)
(add-computation-rules
 "Forest wqo(Nil list nat)" "(Nil lntree(list list nat yprod list nat))"
 "Forest wqo((Nil nat)::ws)" "Forest wqo ws"
 "Forest wqo((a::v)::ws)"
 "[if (LargerAR wqo a(BSeq wqo Heads ws))
      (InsertF wqo(Forest wqo ws)v a)
      (NewTree((v::ws)pair a:)::Forest wqo ws)]")

(set-totality-goal "Forest")
(use (make-proof-in-aconst-form
      (aconst-substitute
       alltotal-elim-aconst
       (list
	(list (py "alpha") (py "nat=>nat=>boole"))
	(list
	 (make-pvar (make-arity (py "alpha")) -1 h-deg-zero n-deg-zero "")
	 (make-cterm
	  (pv "wqo^")
	  (pf "allnc ws^(TotalList ws^ -> TotalList(Forest wqo^ ws^))")))))))
(assume "wqo")
(use "AllTotalElim")
(ind)
(use "TotalListNil")
(cases)
(assume "ws")
(assume "IHws")
(use "IHws")
(assume "a" "v" "ws" "IHws")
(simp "Forest2CompRule")
(use "BooleIfTotal")
(use "BooleTotalVar")
(use "InsertFTotal")
(use "AllTotalElim")
(assume "a1")
(use "AllTotalElim")
(assume "a2")
(use "BooleTotalVar")
(use "IHws")
(use "ListTotalVar")
(use "NatTotalVar")
(use "TotalListCons")
(use "LntreeTotalVar")
(use "IHws")
;; Proof finished.
(save-totality)

;; ForestConsInsertFDef
(set-goal "all wqo^,a^,ws^,v^(
 LargerAR wqo^ a^(BSeq wqo^ Heads ws^) -> Forest wqo^((a^ ::v^)::ws^)eqd
 InsertF wqo^(Forest wqo^ ws^)v^ a^)")
(assume "wqo^" "a^" "ws^" "v^" "LHyp")
(ng)
(simp "LHyp")
(ng)
(use "InitEqD")
;; Proof finished.
(save "ForestConsInsertFDef")
 
;; ForestConsNewDef
(set-goal "all wqo,a,ws,v((LargerAR wqo a(BSeq wqo Heads ws) -> F) ->
 Forest wqo((a ::v)::ws)=
 (NewTree((v ::ws)pair a :)::Forest wqo ws))")
(assume "wqo" "a" "ws" "v" "NegLHyp")
(ng)
(simp "NegLHyp")
(ng)
(use "Truth")
;; Proof finished.
(save "ForestConsNewDef")

;; (NewATree as) returns as%[]
(add-program-constant "NewATree" (py "list nat=>lntree list nat") t-deg-zero)
(add-computation-rules
 "NewATree(Nil nat)" "(Nil nat)%(Nil lntree list nat)"
 "NewATree(a:)" "a: %(Nil lntree list nat)"
 "NewATree(a::b::as)" "(a::b::as)%(Nil lntree list nat)")

(set-totality-goal "NewATree")
(use "AllTotalElim")
(ind)
(ng)
(use "TotalLntreeLNBranch")
(use "TotalListNil")
(use "RTotalListNil")
(assume "a")
(ind)
(ng)
(assume "Useless")
(use "TotalLntreeLNBranch")
(use "TotalListCons")
(use "NatTotalVar")
(use "TotalListNil")
(use "RTotalListNil")
(assume "b" "as" "Useless1" "Useless2")
(ng)
(use "TotalLntreeLNBranch")
(use "TotalListCons")
(use "NatTotalVar")
(use "TotalListCons")
(use "NatTotalVar")
(use "ListTotalVar")
(use "RTotalListNil")
;; Proof finished.
(save-totality)

;; NewATreeDef
(set-goal "all as NewATree as=(as%(Nil lntree list nat))")
(ind)
(ng)
(use "Truth")
(assume "a")
(cases)
(ng)
(strip)
(use "Truth")
(ng)
(strip)
(use "Truth")
;; Proof finished.
(save "NewATreeDef")

(add-var-name "ta" "sa" (py "lntree list nat"))
(add-var-name "tas" "sas" "ras" (py "list lntree list nat"))

;; We will need ListLntreeEqToEqD theorems.  The presence of the
;; nested algebra lntree makes it necessary to use induction on HtT
;; and HtF in between.

;; Need this for BarFNil.  Variable names:
;; as -> tas
;; bs -> sas
;; a -> ta
;; b -> sa

;; LntreeListNatEqToEqDAux
(set-goal "all n(
 all ta,sa(HtT ta<n -> HtT sa<n -> ta=sa -> ta eqd sa) &
 all tas,sas(HtF tas<n -> HtF sas<n -> tas=sas -> tas eqd sas))")
(ind)
(split)
(assume "ta" "sa")
(ng)
(use "Efq")
(assume "tas" "sas")
(ng)
(use "Efq")
(assume "n" "IHn")
(split)
(assume "ta" "sa")
(assert "(Root ta%Subtrees ta)eqd ta")
 (use "RootSubtreesId")
(assume "(Root ta%Subtrees ta)eqd ta")
(simp "<-" "(Root ta%Subtrees ta)eqd ta")
(ng #t)
(assume "HtF Subtrees ta<n")
(assert "(Root sa%Subtrees sa)eqd sa")
 (use "RootSubtreesId")
(assume "(Root sa%Subtrees sa)eqd sa")
(simp "<-" "(Root sa%Subtrees sa)eqd sa")
(ng #t)
(assume "HtF Subtrees sa<n" "Conj")
(assert "Root ta eqd Root sa")
(use "ListNatEqToEqD")
(use "Conj")
(assume "Root ta eqd Root sa")
(assert "Subtrees ta eqd Subtrees sa")
(use "IHn")
(use "HtF Subtrees ta<n")
(use "HtF Subtrees sa<n")
(use "Conj")
(assume "Subtrees ta eqd Subtrees sa")
(simp "Root ta eqd Root sa")
(simp "Subtrees ta eqd Subtrees sa")
(use "InitEqD")
;; all tas,sas(HtF tas<Succ n -> HtF sas<Succ n -> tas=sas -> tas eqd sas)
(cases)
(cases)
(strip)
(use "InitEqD")
(assume "sa" "sas" "Useless1" "Useless2")
(ng #t)
(use "Efq")
(assume "ta" "tas")
(cases)
(assume "Useless1" "Useless2")
(ng #t)
(use "Efq")
(assume "sa" "sas")
(ng #t)
(assume "HtT ta max HtF tas<n" "HtT sa max HtF sas<n" "Conj")
;; ta eqd sa
(assert "ta eqd sa")
(use "IHn")
(use "NatLeLtTrans" (pt "HtT ta max HtF tas"))
(use "NatMaxUB1")
(use "HtT ta max HtF tas<n")
(use "NatLeLtTrans" (pt "HtT sa max HtF sas"))
(use "NatMaxUB1")
(use "HtT sa max HtF sas<n")
(use "Conj")
(assume "ta eqd sa")
;; tas eqd sas
(assert "tas eqd sas")
(use "IHn")
(use "NatLeLtTrans" (pt "HtT ta max HtF tas"))
(use "NatMaxUB2")
(use "HtT ta max HtF tas<n")
(use "NatLeLtTrans" (pt "HtT sa max HtF sas"))
(use "NatMaxUB2")
(use "HtT sa max HtF sas<n")
(use "Conj")
(assume "tas eqd sas")
;; Now we are done
(simp "ta eqd sa")
(simp "tas eqd sas")
(use "InitEqD")
;; Proof finished.
(save "LntreeListNatEqToEqDAux")

;; LntreeListNatEqToEqD
(set-goal "all ta,sa(ta=sa -> ta eqd sa)")
(assume "ta" "sa")
(use-with "LntreeListNatEqToEqDAux"
	  (pt "Succ(HtT ta max HtT sa)") 'left (pt "ta") (pt "sa") "?" "?")
(use "NatLeLtTrans" (pt "HtT ta max HtT sa"))
(use "NatMaxUB1")
(use "Truth")
(use "NatLeLtTrans" (pt "HtT ta max HtT sa"))
(use "NatMaxUB2")
(use "Truth")
;; Proof finished.
(save "LntreeListNatEqToEqD")

;; ListLntreeListNatEqToEqD
(set-goal "all tas,sas(tas=sas -> tas eqd sas)")
(assume "tas" "sas")
(use-with "LntreeListNatEqToEqDAux"
	  (pt "Succ(HtF tas max HtF sas)") 'right (pt "tas") (pt "sas") "?" "?")
(use "NatLeLtTrans" (pt "HtF tas max HtF sas"))
(use "NatMaxUB1")
(use "Truth")
(use "NatLeLtTrans" (pt "HtF tas max HtF sas"))
(use "NatMaxUB2")
(use "Truth")
;; Proof finished.
(save "ListLntreeListNatEqToEqD")

;; (InsertAT wqo t a) returns the result of inserting a into ta, as
;;   follows.  Let ta be as%tas.  If there is some root in tas such
;;   that a is above all of its elements, then recursively insert a
;;   into tas.  Otherwise extend tas by a new tree consisting of a
;;   root only, formed by appending a to as.

(add-program-constant
 "InsertAT" (py "(nat=>nat=>boole)=>lntree list nat=>nat=>lntree list nat")
 t-deg-zero)

(add-program-constant
 "InsertAF"
 (py "(nat=>nat=>boole)=>list lntree list nat=>nat=>list lntree list nat")
 t-deg-zero)

(add-computation-rules
 "InsertAT wqo(as%tas)a"
 "as%[if (LargerARExAll wqo a Roots tas)
         (InsertAF wqo tas a)
         (NewATree(a::as)::tas)]")

(add-computation-rules
 "InsertAF wqo(Nil lntree list nat)a" "(Nil lntree list nat)"
 "InsertAF wqo(ta::tas)a"
 "[if (LargerARAll wqo a Root ta) (InsertAT wqo ta a) ta]::
  InsertAF wqo tas a")

(set-totality-goal "InsertAT" "InsertAF")
(assert "all wqo,a,n(
 all ta(HtT ta<n -> TotalLntree(InsertAT wqo ta a)) &
 all tas(HtF tas<n -> TotalList(InsertAF wqo tas a)))")
(assume "wqo" "a")
(ind)
;; Base
(split)
(assume "ta")
(ng)
(use "Efq")
(assume "tas")
(ng)
(use "Efq")
(assume "n" "IH")
(split)
;; Case ta
(assume "ta")
(simp "<-" "RootSubtreesId")
(simp "LntreeHeightT0CompRule")
(assume "HtF Subtrees ta<n")
(ng "HtF Subtrees ta<n")
(simp "InsertAT0CompRule")
(cases (pt "(LargerARExAll wqo a Roots Subtrees ta)"))
;; Case True
(assume "Useless")
(use  "TotalLntreeLNBranch")
(use "ListTotalVar")
(use "TotalListToRTotalList")
(use "BooleIfTotal")
(use "TotalBooleTrue")
(use "IH")
(use "HtF Subtrees ta<n")
(use "ListTotalVar")
;; Case False
(assume "Useless")
(use "LntreeTotalVar")
;; Case tas
;; all tas(HtF tas<Succ n -> TotalList(InsertAF wqo tas a))
(ind)
;; Base
(ng #t)
(assume "Useless")
(use "TotalListNil")
;; Step
(assume "ta" "tas" "IHtF" "HtBound")
(ng "HtBound")
(ng #t)
(use "TotalListCons")
(use "BooleIfTotal")
(use "BooleTotalVar")
(use "IH")
(use "NatLeLtTrans" (pt "HtT ta max HtF tas"))
(use "NatMaxUB1")
(use "HtBound")
(use "LntreeTotalVar")
(use "IH")
(use "NatLeLtTrans" (pt "HtT ta max HtF tas"))
(use "NatMaxUB2")
(use "HtBound")
;; Now the assertion is proved.
(assume "InsertATInsertAFTotalAux")
(split)
;; Case ta
(use (make-proof-in-aconst-form
      (aconst-substitute
       alltotal-elim-aconst
       (list
	(list (py "alpha") (py "nat=>nat=>boole"))
	(list (make-pvar (make-arity (py "alpha")) -1 h-deg-zero n-deg-zero "")
	      (make-cterm
	       (pv "wqo^")
	       (pf "allnc ta^(
      TotalLntree ta^ -> 
       allnc a^(TotalNat a^ -> TotalLntree(InsertAT wqo^ ta^ a^)))")))))))
(assume "wqo")
(use "AllTotalElim")
(assume "ta")
(use "AllTotalElim")
(assume "a")
(use "InsertATInsertAFTotalAux" (pt "Succ HtT ta"))
(use "Truth")
;; Case tas
(use (make-proof-in-aconst-form
      (aconst-substitute
       alltotal-elim-aconst
       (list
	(list (py "alpha") (py "nat=>nat=>boole"))
	(list (make-pvar (make-arity (py "alpha")) -1 h-deg-zero n-deg-zero "")
	      (make-cterm
	       (pv "wqo^")
	       (pf "allnc tas^(
      TotalList tas^ -> 
       allnc a^(TotalNat a^ -> TotalList(InsertAF wqo^ tas^ a^)))")))))))
(assume "wqo")
(use "AllTotalElim")
(assume "tas")
(use "AllTotalElim")
(assume "a")
(use "InsertATInsertAFTotalAux" (pt "Succ HtF tas"))
(use "Truth")
;; Proof finished.
(save-totality)

;; GoodA wqo ws means that one b in as is <= some larger a in as to its left.
(add-ids (list (list "GoodA" (make-arity (py "nat=>nat=>boole")
 					 (py "list nat"))))
	 '("all wqo,a,as(LargerAR wqo a as -> GoodA wqo(a::as))" "InitGoodA")
	 '("all wqo,a,as(GoodA wqo as -> GoodA wqo(a::as))" "GenGoodA"))

(add-program-constant
 "GoodAR" (py "(nat=>nat=>boole)=>list nat=>boole") t-deg-zero)
(add-computation-rules
 "GoodAR wqo(Nil nat)" "False"
 "GoodAR wqo(a::as)" "[if (LargerAR wqo a as) True (GoodAR wqo as)]")

(set-totality-goal "GoodAR")
(assume "wqo^" "Twqo")
(use "AllTotalElim")
(ind)
(use "TotalBooleFalse")
(assume "a" "as" "IHas")
(ng)
(use "BooleIfTotal")
(use "LargerARTotal")
(use "Twqo")
(use "NatTotalVar")
(use "ListTotalVar")
(use "TotalBooleTrue")
(use "IHas")
;; Proof finished.
(save-totality)

(add-program-constant
 "GLT" (py "(nat=>nat=>boole)=>lntree(list list nat yprod list nat)=>boole")
 t-deg-zero)
(add-program-constant
 "GLF"
 (py "(nat=>nat=>boole)=>list lntree(list list nat yprod list nat)=>boole")
 t-deg-zero)

(add-computation-rules
 "GLT wqo(usas%(Nil lntree(list list nat yprod list nat)))"
 "GoodWR wqo lft usas"
 "GLT wqo(usas%t::ts)" "[if (GLT wqo t) True (GLF wqo ts)]")

(add-computation-rules
 "GLF wqo(Nil lntree(list list nat yprod list nat))" "False"
 "GLF wqo(t::ts)" "[if (GLT wqo t) True (GLF wqo ts)]")

(set-totality-goal "GLT" "GLF")
(assert "all wqo,n(
 all t(HtT t<n -> TotalBoole(GLT wqo t))&
 all ts(HtF ts<n -> TotalBoole(GLF wqo ts)))")
(assume "wqo")
(ind)
;; Base
(split)
(assume "t")
(ng)
(use "Efq")
(assume "ts")
(ng)
(use "Efq")
(assume "n" "IH")
(split)
;; Case t
(assume "t")
(simp "<-" "RootSubtreesId")
(simp "LntreeHeightT0CompRule")
(cases (pt "Subtrees t"))
(ng)
(strip)
(use "BooleTotalVar")
(ng)
(assume "t1" "ts" "Useless" "HtBound")
(use "BooleIfTotal")
(use "IH")
(use "NatLtTrans" (pt "Succ(HtT t1 max HtF ts)"))
(use "NatLeLtTrans" (pt "HtT t1 max HtF ts"))
(use "NatMaxUB1")
(use "Truth")
(use "HtBound")
(use "TotalBooleTrue")
(use "IH")
(use "NatLtTrans" (pt "Succ(HtT t1 max HtF ts)"))
(use "NatLeLtTrans" (pt "HtT t1 max HtF ts"))
(use "NatMaxUB2")
(use "Truth")
(use "HtBound")
;; Case ts
;; all ts(HtF ts<Succ n -> TotalBoole(GLF wqo ts))
(ind)
(ng)
(assume "Useless")
(use "TotalBooleFalse")
(assume "t" "ts" "IHts" "HtBound")
(ng)
(use "BooleIfTotal")
(use "IH")
(use "NatLeLtTrans" (pt "HtT t max HtF ts"))
(use "NatMaxUB1")
(use "HtBound")
(use "TotalBooleTrue")
(use "IH")
(use "NatLeLtTrans" (pt "HtT t max HtF ts"))
(use "NatMaxUB2")
(use "HtBound")
(assume "GLTGLFTotalAux")
(split)
(assume "wqo^" "Twqo")
(use "AllTotalElim")
(assume "t")
(use (make-proof-in-aconst-form
      (aconst-substitute
       alltotal-elim-aconst
       (list
	(list (py "alpha") (py "nat=>nat=>boole"))
	(list (make-pvar (make-arity (py "alpha")) -1 h-deg-zero n-deg-zero "")
	      (make-cterm
	       (pv "wqo^")
	       (pf "allnc t^(
      TotalLntree t^ -> TotalBoole(GLT wqo^ t^))")))))))
(assume "wqo")
(use "AllTotalElim")
(assume "t1")
(use "GLTGLFTotalAux" (pt "Succ HtT t1"))
(use "Truth")
(use "Twqo")
(use "LntreeTotalVar")
(assume "wqo^" "Twqo")
(use "AllTotalElim")
(assume "ts")
(use (make-proof-in-aconst-form
      (aconst-substitute
       alltotal-elim-aconst
       (list
	(list (py "alpha") (py "nat=>nat=>boole"))
	(list (make-pvar (make-arity (py "alpha")) -1 h-deg-zero n-deg-zero "")
	      (make-cterm
	       (pv "wqo^")
	       (pf "allnc ts^(
      TotalList ts^ -> TotalBoole(GLF wqo^ ts^))")))))))
(assume "wqo")
(use "AllTotalElim")
(assume "ts1")
(use "GLTGLFTotalAux" (pt "Succ HtF ts1"))
(use "Truth")
(use "Twqo")
(use "ListTotalVar")
;; Proof finished.
(save-totality)

;; An A-tree at is a labelled nested tree with labels in A.

;; (Proj t) projects out each head of the rhs of a label in t.
;; (ProjF ts) does the same thing recursively for forests.

(add-program-constant
 "ProjT" (py "lntree(list list nat yprod list nat)=>lntree list nat")
 t-deg-zero)
(add-program-constant
 "ProjF" (py "list lntree(list list nat yprod list nat)=>list lntree list nat")
 t-deg-zero)
(add-computation-rules
 "ProjT(vsas%ts)" "rht vsas%ProjF ts")
(add-computation-rules
 "ProjF(Nil lntree(list list nat yprod list nat))" "(Nil lntree list nat)"
 "ProjF(t::ts)" "ProjT t::ProjF ts")

;; Example

;; (pp (nt (pt
;;  "ProjF(Forest NatLe((5::2:)::(2::8:)::(4::2::1:)::(6::9:)::(3::5:):))")))

;; (2%(5%(Nil lntree nat)):)::
;; (3%(4%(5%(Nil lntree nat)):)::(6%(Nil lntree nat)):):

;;     5
;;     -
;; 5   4   6
;; -   -----
;; 2     3

;; The heads of [[5 2] [2 8] [4 2 1] [6 9] [3 5]] are [5 2 4 6 3].
;; Its maximal decreasing sublists are [5 2], [5 4 3] and [6 3], the
;; branches of the projection of Forest[[5 2] [2 8] [4 2 1] [6 9] [3 5]].

(set-totality-goal "ProjT" "ProjF")
(assert "all n(
 all t(HtT t<n -> TotalLntree(ProjT t)) &
 all ts(HtF ts<n -> TotalList(ProjF ts)))")
(ind)
;; Base
(split)
(assume "t")
(ng)
(use "Efq")
(assume "ts")
(ng)
(use "Efq")
(assume "n" "IH")
(split)
;; Case t
(assume "t")
(simp "<-" "RootSubtreesId")
(simp "LntreeHeightT0CompRule")
(assume "HtF Subtrees t<n")
(ng "HtF Subtrees t<n")
(simp "ProjT0CompRule")
(use  "TotalLntreeLNBranch")
(use "ListTotalVar")
(use "TotalListToRTotalList")
(use "IH")
(use "HtF Subtrees t<n")
;; Case ts
;; all ts(HtF ts<Succ n -> TotalList(ProjF ts))
(ind)
;; Base
(ng #t)
(assume "Useless")
(use "TotalListNil")
;; Step
(assume "t" "ts" "IHtF" "HtBound")
(ng "HtBound")
(ng #t)
(use "TotalListCons")
(use "IH")
(use "NatLeLtTrans" (pt "HtT t max HtF ts"))
(use "NatMaxUB1")
(use "HtBound")
(use "IH")
(use "NatLeLtTrans" (pt "HtT t max HtF ts"))
(use "NatMaxUB2")
(use "HtBound")
;; Now the assertion is proved.
(assume "ProjTProjFTotalAux")
(split)
;; Case t
(use "AllTotalElim")
(assume "t")
(use "ProjTProjFTotalAux" (pt "Succ HtT t"))
(use "Truth")
;; Case ts
(use "AllTotalElim")
(assume "ts")
(use "ProjTProjFTotalAux" (pt "Succ HtF ts"))
(use "Truth")
;; Proof finished.
(save-totality)

(add-ids
 (list
  (list "BarA" (make-arity (py "nat=>nat=>boole") (py "list nat")) "treeA"))
 '("allnc as(GoodAR wqo as -> BarA wqo as)" "InitBarA")
 '("allnc as(all a BarA wqo(a::as) -> BarA wqo as)" "GenBarA"))

;; (ESeqA as ass) means that ass has the form (a1::as ... an::as).
(add-program-constant "ESeqA" (py "list nat=>list list nat=>boole") t-deg-zero)
(add-computation-rules
 "ESeqA as(Nil list nat)" "True"
 "ESeqA as(as0::ass)" "as0=(Head as0::as)andb ESeqA as ass")

(set-totality-goal "ESeqA")
(use "AllTotalElim")
(assume "as")
(use "AllTotalElim")
(ind)
;; Base
(ng)
(use "TotalBooleTrue")
;; Step
(assume "as0" "ass" "IH")
(ng)
(use "AndConstTotal")
(use "BooleTotalVar")
(use "IH")
;; Proof finished.
(save-totality)

(add-program-constant "ExtAT" (py "lntree list nat=>boole") t-deg-zero)
(add-program-constant "ExtAF" (py "list lntree list nat=>boole") t-deg-zero)
(add-computation-rules
 "ExtAT(as%tas)" "ESeqA as Roots tas andb ExtAF tas")

(add-computation-rules
 "ExtAF(Nil lntree list nat)" "True"
 "ExtAF(ta::tas)" "ExtAT ta andb ExtAF tas")

(set-totality-goal "ExtAT" "ExtAF")
(assert "all n(
 all ta(HtT ta<n -> TotalBoole(ExtAT ta))&
 all tas(HtF tas<n -> TotalBoole(ExtAF tas)))")
(ind)
;; Base
(split)
(assume "ta")
(ng)
(use "Efq")
(assume "tas")
(ng)
(use "Efq")
(assume "n" "IH")
(split)
;; Case ta
(assume "ta")
(simp "<-" "RootSubtreesId")
(simp "LntreeHeightT0CompRule")
(cases (pt "Subtrees ta"))
(ng)
(strip)
(use "BooleTotalVar")
(ng)
(assume "ta1" "tas" "Useless" "HtBound")
(use "AndConstTotal")
(use "BooleTotalVar")
(use "AndConstTotal")
(use "IH")
(use "NatLtTrans" (pt "Succ(HtT ta1 max HtF tas)"))
(use "NatLeLtTrans" (pt "HtT ta1 max HtF tas"))
(use "NatMaxUB1")
(use "Truth")
(use "HtBound")
(use "IH")
(use "NatLtTrans" (pt "Succ(HtT ta1 max HtF tas)"))
(use "NatLeLtTrans" (pt "HtT ta1 max HtF tas"))
(use "NatMaxUB2")
(use "Truth")
(use "HtBound")
;; Case tas
;; all tas(HtF tas<Succ n -> TotalBoole(ExtAF tas))
(ind)
(ng)
(assume "Useless")
(use "TotalBooleTrue")
(assume "ta" "tas" "IHtas" "HtBound")
(ng)
(use "AndConstTotal")
(use "IH")
(use "NatLeLtTrans" (pt "HtT ta max HtF tas"))
(use "NatMaxUB1")
(use "HtBound")
(use "IH")
(use "NatLeLtTrans" (pt "HtT ta max HtF tas"))
(use "NatMaxUB2")
(use "HtBound")
;; Now the assertion is proved
(assume "ExtATExtAFTotalAux")
(split)
;; Case ta
(use "AllTotalElim")
(assume "ta")
(use "ExtATExtAFTotalAux" (pt "Succ HtT ta"))
(use "Truth")
;; Case tas
(use "AllTotalElim")
(assume "tas")
(use "ExtATExtAFTotalAux" (pt "Succ HtF tas"))
(use "Truth")
;; Proof finished.
(save-totality)

;; Predecessors of (BarF wqo ts) are all (InsertAF tas v a) where a
;; is inserted inside (i.e., not appended to the final as because
;; a::as is bad)
(add-ids
 (list
  (list "BarF" (make-arity (py "nat=>nat=>boole")
   			    (py "list lntree(list list nat yprod list nat)"))
	     "treeF"))
 '("allnc ts,i(i<Lh ts -> GLT wqo(i thof ts) -> BarF wqo ts)" "InitBarF")
 '("allnc ts(all tas,a,v(tas=ProjF ts -> ExtAF tas ->
                         LargerARExAll wqo a Roots tas -> 
                         BarF wqo(InsertF wqo ts v a)) ->
             BarF wqo ts)"
 "GenBarF"))

(add-ids (list (list "BarW" (make-arity (py "nat=>nat=>boole")
				       (py "list list nat")) "treeW"))
	 '("allnc vs(GoodW wqo vs -> BarW wqo vs)" "InitBarW")
	 '("allnc vs(all v BarW wqo(v::vs) -> BarW wqo vs)" "GenBarW"))

;; (ESeq vsas vsass) means that vsass has the form (a1::vsas ... an::vsas).
(add-program-constant "ESeq" (py "list list nat yprod list nat=>
                                  list(list list nat yprod list nat)=>boole")
		      t-deg-zero)
(add-computation-rules
 "ESeq vsas(Nil list list nat yprod list nat)" "True"
 "ESeq vsas(vsas0::vsass)"
 "lft vsas0=(Head lft vsas0::lft vsas)andb
  rht vsas0=(Head rht vsas0::rht vsas)andb ESeq vsas vsass")

(set-totality-goal "ESeq")
(use "AllTotalElim")
(assume "vsas")
(use "AllTotalElim")
(ind)
;; Base
(ng)
(use "BooleTotalVar")
;; Step
(assume "vsas0" "vsass" "IH")
(ng)
(use "AndConstTotal")
(use "BooleTotalVar")
(use "AndConstTotal")
(use "BooleTotalVar")
(use "IH")
;; Proof finished.
(save-totality)

;; (CorrT wqo ws t) means t is correct w.r.t. wqo and ws
(add-program-constant
 "CorrT" (py "(nat=>nat=>boole)=>list list nat=>
               lntree(list list nat yprod list nat)=>boole") t-deg-zero)

;; (CorrF wqo ws ts) means t_i is correct w.r.t. wqo and ws for each i
(add-program-constant
 "CorrF" (py "(nat=>nat=>boole)=>list list nat=>
               list lntree(list list nat yprod list nat)=>boole") t-deg-zero)

(add-computation-rules
 "CorrT wqo ws(usas%ts)"
 "Lh rht usas<=Lh lft usas andb
  0<Lh rht usas andb
  Incr wqo rht usas andb
  ESeq usas Roots ts andb
  (rht usas mapcons Lh rht usas init lft usas)++(Lh rht usas rest lft usas)
   sub ws andb
  CorrF wqo ws ts")

(add-computation-rules
 "CorrF wqo ws(Nil lntree(list list nat yprod list nat))" "True"
 "CorrF wqo ws(t::ts)" "CorrT wqo ws t andb CorrF wqo ws ts")

(set-totality-goal "CorrT" "CorrF")
(assert "all wqo,ws,n(
 all t(HtT t<n -> TotalBoole(CorrT wqo ws t))&
 all ts(HtF ts<n -> TotalBoole(CorrF wqo ws ts)))")
(assume "wqo" "ws")
(ind)
;; Base
(split)
(assume "t")
(ng)
(use "Efq")
(assume "ts")
(ng)
(use "Efq")
(assume "n" "IH")
(split)
;; Case t
(assume "t")
(simp "<-" "RootSubtreesId")
(simp "LntreeHeightT0CompRule")
(cases (pt "Subtrees t"))
(ng)
(strip)
(use "BooleTotalVar")
(ng)
(assume "t1" "ts" "Useless" "HtBound")
(use "AndConstTotal")
(use "BooleTotalVar")
(use "AndConstTotal")
(use "BooleTotalVar")
(use "AndConstTotal")
(use "BooleTotalVar")
(use "AndConstTotal")
(use "BooleTotalVar")
(use "AndConstTotal")
(use "BooleTotalVar")
(use "AndConstTotal")
(use "IH")
(use "NatLtTrans" (pt "Succ(HtT t1 max HtF ts)"))
(use "NatLeLtTrans" (pt "HtT t1 max HtF ts"))
(use "NatMaxUB1")
(use "Truth")
(use "HtBound")
(use "IH")
(use "NatLtTrans" (pt "Succ(HtT t1 max HtF ts)"))
(use "NatLeLtTrans" (pt "HtT t1 max HtF ts"))
(use "NatMaxUB2")
(use "Truth")
(use "HtBound")
;; Case ts
;; all ts(HtF ts<Succ n -> TotalBoole(CorrF wqo ws ts))
(ind)
(ng)
(assume "Useless")
(use "TotalBooleTrue")
(assume "t" "ts" "IHts" "HtBound")
(ng)
(use "AndConstTotal")
(use "IH")
(use "NatLeLtTrans" (pt "HtT t max HtF ts"))
(use "NatMaxUB1")
(use "HtBound")
(use "IH")
(use "NatLeLtTrans" (pt "HtT t max HtF ts"))
(use "NatMaxUB2")
(use "HtBound")
;; Now the assertion is proved
(assume "CorrTCorrFTotalAux")
(split)
;; Case t
(assume "wqo^" "Twqo")
(use "AllTotalElim")
(assume "ws")
(use "AllTotalElim")
(assume "t")
(use (make-proof-in-aconst-form
      (aconst-substitute
       alltotal-elim-aconst
       (list
	(list (py "alpha") (py "nat=>nat=>boole"))
	(list (make-pvar (make-arity (py "alpha")) -1 h-deg-zero n-deg-zero "")
	      (make-cterm
	       (pv "wqo^")
	       (pf "allnc ws^(TotalList ws^ ->
                    allnc t^(TotalLntree t^ ->
                             TotalBoole(CorrT wqo^ ws^ t^)))")))))))
(assume "wqo")
(use "AllTotalElim")
(assume "ws1")
(use "AllTotalElim")
(assume "t1")
(use "CorrTCorrFTotalAux" (pt "Succ HtT t1"))
(use "Truth")
(use "Twqo")
(use "ListTotalVar")
(use "LntreeTotalVar")
;; Case ts
(assume "wqo^" "Twqo")
(use "AllTotalElim")
(assume "ws")
(use "AllTotalElim")
(assume "ts")
(use (make-proof-in-aconst-form
      (aconst-substitute
       alltotal-elim-aconst
       (list
	(list (py "alpha") (py "nat=>nat=>boole"))
	(list (make-pvar (make-arity (py "alpha")) -1 h-deg-zero n-deg-zero "")
	      (make-cterm
	       (pv "wqo^")
	       (pf "allnc ws^(TotalList ws^ ->
                    allnc ts^(TotalList ts^ ->
                             TotalBoole(CorrF wqo^ ws^ ts^)))")))))))
(assume "wqo")
(use "AllTotalElim")
(assume "ws1")
(use "AllTotalElim")
(assume "ts1")
(use "CorrTCorrFTotalAux" (pt "Succ HtF ts1"))
(use "Truth")
(use "Twqo")
(use "ListTotalVar")
(use "ListTotalVar")
;; Proof finished.
(save-totality)

;; (CorrAT wqo ta) means ta is correct w.r.t. wqo
(add-program-constant
 "CorrAT" (py "(nat=>nat=>boole)=>lntree list nat=>boole") t-deg-zero)

;; (CorrAF wqo tas) means tas_i is correct w.r.t. wqo for each i
(add-program-constant
 "CorrAF" (py "(nat=>nat=>boole)=>list lntree list nat=>boole") t-deg-zero)

(add-computation-rules
 "CorrAT wqo(as%tas)"
 "0<Lh as andb Incr wqo as andb ESeqA as Roots tas andb CorrAF wqo tas")

(add-computation-rules
 "CorrAF wqo(Nil lntree list nat)" "True"
 "CorrAF wqo(ta::tas)" "CorrAT wqo ta andb CorrAF wqo tas")

(set-totality-goal "CorrAT" "CorrAF")
(assert "all wqo,n(
 all ta(HtT ta<n -> TotalBoole(CorrAT wqo ta)) &
 all tas(HtF tas<n -> TotalBoole(CorrAF wqo tas)))")
(assume "wqo")
(ind)
;; Base
(split)
(assume "ta")
(ng)
(use "Efq")
(assume "tas")
(ng)
(use "Efq")
(assume "n" "IH")
(split)
;; Case ta
(assume "ta")
(simp "<-" "RootSubtreesId")
(simp "LntreeHeightT0CompRule")
(assume "HtF Subtrees ta<n")
(ng "HtF Subtrees ta<n")
(simp "CorrAT0CompRule")
(use "AndConstTotal")
(use "BooleTotalVar")
(use "AndConstTotal")
(use "BooleTotalVar")
(use "AndConstTotal")
(use "BooleTotalVar")
(use "IH")
(use "HtF Subtrees ta<n")
;; Case tas
;; all tas(HtF tas<Succ n -> TotalBoole(CorrAF wqo tas))
(ind)
;; Base
(ng #t)
(assume "Useless")
(use "TotalBooleTrue")
;; Step
(assume "ta" "tas" "IHtF" "HtBound")
(ng "HtBound")
(ng #t)
(use "AndConstTotal")
(use "IH")
(use "NatLeLtTrans" (pt "HtT ta max HtF tas"))
(use "NatMaxUB1")
(use "HtBound")
(use "IH")
(use "NatLeLtTrans" (pt "HtT ta max HtF tas"))
(use "NatMaxUB2")
(use "HtBound")
;; Now the assertion is proved.
(assume "CorrATCorrAFTotalAux")
(split)
;; Case ta
(use (make-proof-in-aconst-form
      (aconst-substitute
       alltotal-elim-aconst
       (list
	(list (py "alpha") (py "nat=>nat=>boole"))
	(list (make-pvar (make-arity (py "alpha")) -1 h-deg-zero n-deg-zero "")
	      (make-cterm
	       (pv "wqo^")
	       (pf "allnc ta^(
      TotalLntree ta^ -> TotalBoole(CorrAT wqo^ ta^))")))))))
(assume "wqo")
(use "AllTotalElim")
(assume "ta")
(use "CorrATCorrAFTotalAux" (pt "Succ HtT ta"))
(use "Truth")
;; Case tas
(use (make-proof-in-aconst-form
      (aconst-substitute
       alltotal-elim-aconst
       (list
	(list (py "alpha") (py "nat=>nat=>boole"))
	(list (make-pvar (make-arity (py "alpha")) -1 h-deg-zero n-deg-zero "")
	      (make-cterm
	       (pv "wqo^")
	       (pf "allnc tas^(
      TotalList tas^ -> TotalBoole(CorrAF wqo^ tas^))")))))))
(assume "wqo")
(use "AllTotalElim")
(assume "tas")
(use "CorrATCorrAFTotalAux" (pt "Succ HtF tas"))
(use "Truth")
;; Proof finished.
(save-totality)

;; CorrATDef
(set-goal "all wqo,ta CorrAT wqo ta=
 (0<Lh Root ta andb
  Incr wqo Root ta andb
  ESeqA Root ta Roots Subtrees ta andb
  CorrAF wqo Subtrees ta)")
(assume "wqo" "ta")
(assert "ta=(Root ta%Subtrees ta)")
 (simp "RootSubtreesId")
 (use "Truth")
(assume "ta=(Root ta%Subtrees ta)")
(simp "ta=(Root ta%Subtrees ta)")
(drop "ta=(Root ta%Subtrees ta)")
(ng)
(use "Truth")
;; Proof finished.
(save "CorrATDef")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Auxiliary propositions (n.c.)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Elementary properties of the defined functions and relations

;; (vs sub ws) means vs is a sublist if ws (abbreviates ListListNatSub)
;; (Emb v w) means v embeds into w
;; (LargerW v ws) means v embeds into one word from ws
;; (GoodW ws) means that one v in ws embeds into a larger w in ws to its left
;; (R a w) rest after the first a in w
;; (I a w) initial segment of w before the first a
;; (L wqo a as) means a is leq an element of as
;; EmbR
;; LargerWR
;; GoodWR
;; (as mapcons vs) binary form of map for Cons
;; (LargerAR wqo a as) a is wqo an element of as
;; (LargerARAll wqo a as) means that a is larger than (w.r.t. wqo) all
;;   elements ai of as.
;; (Incr wqo as) means that each ai is >= every later aj in as.
;; (Adm ws) means that each word in ws has a positive length
;; (BSeq wqo as) canonical bad sequence in as
;; Root prefix display for LntreeRoot
;; Subtrees prefix display for LntreeSubtrees
;; Roots prefix display for LntreeRoots, list of roots of txs
;; HtT prefix display for LntreeHeight, height of tx
;; HtF prefix display for LntreeHeightF, successor of the maximum of the
;;   heights of its Subtrees
;; (NewTree vsas) returns (vs pair as)%[]
;; (InsertT wqo t v a) returns the result of inserting v and a into
;;   t, as follows.  Let t be vsas%ts.  If a is not above all elements
;;   of the rhs of some root in ts, then extend ts by a new tree
;;   consisting of a root only, formed by appending v to (lft vsas) and
;;   a to (rht vsas).  Otherwise recursively insert v and a into ts.
;; (InsertF wqo ts v a) recursively inserts v and a into ts
;; (Forest wqo ws) returns a list of labeled trees.
;; (NewATree as) returns a%[]
;; (InsertAT wqo ta a) returns the result of inserting a into ta, as
;;   follows.  Let ta be as%tas.  If a is not above some head of a root
;;   in tas, then extend tas by a new tree consisting of a root only,
;;   formed by appending a to as.  Otherwise recursively insert a into
;;   tas.
;; (InsertAF wqo tas a) recursively inserts a into tas
;; GoodA wqo ws means that one b in as is <= some larger a in as to its left.
;; GoodAR
;; GLT (for GoodLeafT)
;; GLF (GoodLeafF)
;; (ProjT t) projects out each head of the rhs of a label in t
;; (ProjF ts) does the same thing recursively for forests.
;; BarA
;; Predecessors of (BarF wqo ts) are all (InsertAF tas v a) with
;;   tas=ProjF ts which are different from tas.  This means that a is
;;   inserted inside (i.e., not appended to the final as because a::as
;;   is bad)
;; BarW
;; (ESeq vsas vsass) means that each component of (vsass)_i
;;   extends the corresponding component of vsas by one element.
;; (CorrT wqo ws t) means t is correct w.r.t. wqo and ws
;; (CorrF wqo ws ts) means t_i is correct w.r.t. wqo and ws for each i
;; (ESeqA as ass) means that each (ass)_i extends as by one element.
;; (CorrAT wqo ta) means ta is correct w.r.t. wqo
;; (CorrAF wqo tas) means tas_i is correct w.r.t. wqo for each i

;; SubRefl
;; SubCons
;; SubTrans
;; IRSplit
;; LToZeroLtLhR
;; EmbRAppdRight
;; GenEmbRCons
;; GenEmbRInit
;; EmbToEmbR
;; EmbRToEmb
;; EmbAppdRight
;; LargerWRToLargerW
;; LargerWToLargerWR
;; LargerWRNil
;; LargerWRSub
;; LargerWElim
;; LargerWCons
;; LargerWSub
;; LargerWAppdCases
;; LargerWAppdLeft
;; LargerWAppdRight
;; LargerWMapcons
;; GoodWElim
;; GoodWNotNil
;; GoodWAppdLeft
;; GoodWSub
;; GoodWToGoodWR
;; GoodWRToGoodW
;; GoodWAppdMapcons
;; LargerARAllHeadTail
;; LargerARAllHead
;; LargerARAllTail
;; LargerARAllAllConj
;; LargerARExAllIntro
;; LargerARExAllAppdCases
;; LhInsertAF
;; LhInsertF
;; InsertFAppd
;; InsertAFAppd
;; InsertFId
;; InsertAFId
;; RootProj
;; RootsProjF
;; InsertFAppdRight
;; InsertFEqInsertT
;; InsertAFEqInsertAT
;; RootInsert
;; RootsInsert
;; RootInsertA
;; RootsInsertA
;; LAllAllTailsRhtsRootsForest
;; NilTailsRhtsRootsForest
;; ATreeNeqAppdCases
;; NotGoodARBSeq
;; GLFAppd
;; GLFAppdLeft
;; GenIndGLT
;; ExGLTToGLF
;; RootProjF
;; ProjFIf
;; ProjFAppd
;; LhProjF
;; ProjNewTreeEqNewATree
;; InsertAProjEqProjInsertAux
;; InsertATProjEqProjInsertT
;; InsertAFProjFEqProjFInsertF
;; ESeqToESeqA
;; ESeqToESeqAProj
;; ESeqALAllLAllAllTails
;; CorrProjTToLhPos
;; CorrToLhPos
;; CorrConsAux
;; CorrTCons
;; CorrFCons
;; CorrInsertAux
;; CorrTInsertT
;; CorrFInsertF

;; SubRefl
(set-goal "all ws ws sub ws")
(ind)
(use "Truth")
(assume "w" "ws" "IH")
(ng)
(use "IH")
;; Proof finished.
(save "SubRefl")
(add-rewrite-rule (pt "ws sub ws") (pt "True"))

;; SubCons
(set-goal "all ws,w ws sub(w::ws)")
(ind)
(ng)
(assume "w")
(use "Truth")
(assume "w0" "ws" "IH")
(assume "w")
(ng)
(cases (pt "w0=w"))
(assume "Useless")
(use "IH")
(assume "Useless")
(use "Truth")
;; Proof finished.
(save "SubCons")
(add-rewrite-rule (pt "ws sub(w::ws)") (pt "True"))

;; SubTrans
(set-goal "all ws,us,vs(us sub vs -> vs sub ws -> us sub ws)")
(ind)
(cases)
(strip)
(use "Truth")
(assume "w" "ws")
(cases)
(assume "Absurd")
(use "Efq")
(use "Absurd")
(assume "v" "vs" "Useless" "Absurd")
(use "Absurd")
(assume "w" "ws" "IH")
(cases)
(strip)
(use "Truth")
(assume "u" "us")
(cases)
(assume "Absurd")
(use "Efq")
(use "Absurd")
(assume "v" "vs")
;;   ws4160  w  ws  IH:all us,vs(us sub vs -> vs sub ws -> us sub ws)
;;   us4189  u  us  vs4196  v  vs
;; -----------------------------------------------------------------------------
;; ?_22:(u::us)sub(v::vs) -> (v::vs)sub(w::ws) -> (u::us)sub(w::ws)
(cases (pt "u=v"))
(assume "u=v")
(simp "u=v")
(cases (pt "v=w"))
(assume "v=w")
(simp "v=w")
(ng #t)
(use "IH")
(assume "v=w -> F")
(ng)
(simp "v=w -> F")
(ng)
(assume "ussubvs")
(use "IH")
(ng)
(use "ussubvs")
;; Case u=v -> F
(assume "u=v -> F" "uussubvvs")
(simphyp-with-to "uussubvvs" "u=v -> F" "uussubvs")
(ng "uussubvs")
(drop "uussubvvs")
(cases (pt "v=w"))
(assume "v=w")
(simp "v=w")
(assume "vssubws")
(simphyp-with-to "u=v -> F" "v=w" "u=w -> F")
(ng #t)
(simp "u=w -> F")
(ng #t)
(use "IH" (pt "vs"))
(use "uussubvs")
(use "vssubws")
;; Case v=w -> F
(assume "v=w -> F" "vvssubwws")
(ng "vvssubwws")
(simphyp-with-to "vvssubwws" "v=w -> F" "vvssubws")
(ng "vvssubws")
(drop "vvssubwws")
(cases (pt "u=w"))
(assume "u=w")
(simp "u=w")
(ng #t)
(assert "vs sub ws")
 (use "IH" (pt "v::vs"))
 (use "Truth")
 (use "vvssubws")
(assume "vssubws")
(assert "(u::us)sub ws")
 (use "IH" (pt "vs"))
 (use "uussubvs")
 (use "vssubws")
(assume "uussubws")
(use "IH" (pt "u::us"))
(use "Truth")
(use "uussubws")
;; Case u=w -> F
(assume "u=w -> F")
(ng #t)
(simp "u=w -> F")
(ng #t)
(assert "vs sub ws")
 (use "IH" (pt "v::vs"))
 (use "Truth")
 (use "vvssubws")
(assume "vssubws")
(use "IH" (pt "vs"))
(use "uussubvs")
(use "vssubws")
;; Proof finished.
(save "SubTrans")

;; IRSplit
(set-goal "all wqo,a,w(
     L wqo a w -> wqo a Head(R wqo a w) andb w=I wqo a w++R wqo a w)")
(assume "wqo" "a")
(ind)
(ng)
(use "Efq")
(assume "b" "w" "IH")
(ng)
(cases (pt "wqo a b"))
(assume "wqo a b")
(ng)
(assume "Useless")
(use "wqo a b")
(assume "wqo a b -> F")
(ng)
(assume "Law")
(use "IH")
(use "Law")
;; Proof finished.
(save "IRSplit")

;; LToZeroLtLhR
(set-goal "all wqo,a,w(L wqo a w -> 0<Lh(R wqo a w))")
(assume "wqo" "a")
(ind) ;on w
(ng)
(assume "Absurd")
(use "Absurd")
(assume "b" "w" "IHw")
(ng)
(cases (pt "wqo a b"))
(assume "wqo a b")
(ng)
(strip)
(use "Truth")
(assume "wqo a b -> F")
(ng)
(use "IHw")
;; Proof finished.
(save "LToZeroLtLhR")

;; EmbRAppdRight
(set-goal "all wqo,v,u,w(EmbR wqo v w -> EmbR wqo v(u++w))")
(assume "wqo")
(ind) ;on v
(ng)
(assume "w" "u" "ENilw")
(use "ENilw")
(assume "a" "v" "IHv")
(ng)
(ind) ;on u
(ng)
(assume "w" "Hyp")
(use "Hyp")
(assume "c" "u" "IHu" "w")
(ng)
(assume "Conj")
(inst-with-to "Conj" 'left "Law")
(inst-with-to "Conj" 'right "EmbR wqo v Tail(R wqo a w)")
(drop "Conj")
(cases (pt "wqo a c"))
;; Case 1
(assume "wqo a c")
(ng)
(assert "wqo a Head(R wqo a w) andb w=I wqo a w++R wqo a w")
 (use "IRSplit")
 (use "Law")
(assume "wqo a Head(R wqo a w) andb w=I wqo a w++R wqo a w")
(inst-with-to "wqo a Head(R wqo a w) andb w=I wqo a w++R wqo a w" 'left
	      "wqo a Head(R wqo a w)")
(inst-with-to "wqo a Head(R wqo a w) andb w=I wqo a w++R wqo a w" 'right
	      "w=I wqo a w++R wqo a w")
(drop "wqo a Head(R wqo a w) andb w=I wqo a w++R wqo a w")
(simp "w=I wqo a w++R wqo a w")
(use "IHv")
(assert "R wqo a w=(Head(R wqo a w)::Tail(R wqo a w))")
 (simp "ZeroLtLhToHeadTailId")
 (use "Truth")
 (use "LToZeroLtLhR")
 (use "Law")
(assume "R wqo a w=(Head(R wqo a w)::Tail(R wqo a w))")
(simp "R wqo a w=(Head(R wqo a w)::Tail(R wqo a w))")
(drop "R wqo a w=(Head(R wqo a w)::Tail(R wqo a w))")
(simp "<-" "ListAppd0RewRule")
(use "IHv")
(use "EmbR wqo v Tail(R wqo a w)")
;; Case 2
(assume "wqo a c -> F")
(ng #t)
(use "IHu")
(split)
(use "Law")
(use "EmbR wqo v Tail(R wqo a w)")
;; Proof finished.
(save "EmbRAppdRight")

;; GenEmbRCons
(set-goal "all wqo,v,w,a,b(wqo a b -> EmbR wqo v w -> EmbR wqo(a::v)(b::w))")
(ng)
(assume "wqo" "v" "w" "a" "b" "wqo a b" "Evw")
(simp "wqo a b")
(ng)
(use "Evw")
;; Proof finished.
(save "GenEmbRCons")

;; GenEmbRInit
(set-goal "all wqo,v,a,w(EmbR wqo v w -> EmbR wqo v(a::w))")
(assume "wqo" "v" "a" "w" "Evw")
(assert "(a::w)=a: ++w")
 (ng)
 (use "Truth")
(assume "(a::w)=a: ++w")
(simp "(a::w)=a: ++w")
(use "EmbRAppdRight")
(use "Evw")
;; Proof finished.
(save "GenEmbRInit")

;; Conversely:

;; EmbAppdRight
(set-goal "all wqo,v,w,u(Emb wqo v w -> Emb wqo v(u++w))")
(assume "wqo" "v" "w")
(ind)
(assume "Evw")
(use "Evw")
(assume "c" "u" "IHu" "Evw")
(ng)
(use "GenEmbInit")
(use-with "IHu" "Evw")
;; Proof finished.
(save "EmbAppdRight")

;; Hence EmbR satisfies the clauses of Emb, i.e., EmbToEmbR.

;; EmbToEmbR
(set-goal "all wqo,v,w(Emb wqo v w -> EmbR wqo v w)")
(assume "wqo" "v" "w" "Evw")
(elim "Evw")
(assume "wqo1")
(use "Truth")
(assume "wqo1" "v1" "w1" "a" "Ev1w1")
(use "GenEmbRInit")
(assume "wqo1" "v1" "w1" "a" "b" "wqo1 a b" "Ev1w1")
(use "GenEmbRCons")
(use "wqo1 a b")
;; Proof finished.
(save "EmbToEmbR")

;; EmbRToEmb
(set-goal "all wqo,v,w(EmbR wqo v w -> Emb wqo v w)")
(assume "wqo")
(ind) ;on v
(ng)
(ind)
(assume "Useless")
(use "InitEmb")
(assume "b" "w" "IHw" "Useless")
(use "GenEmbInit")
(use-with "IHw" "Truth")
(assume "a" "v" "IHv" "w")
(ng #t)
(assume "Conj")
(inst-with-to "Conj" 'left "Law")
(inst-with-to "Conj" 'right "EmbR wqo v Tail(R wqo a w)")
(drop "Conj")
(assert "wqo a Head(R wqo a w) andb w=I wqo a w++R wqo a w")
 (use "IRSplit")
 (use "Law")
(assume "wqo a Head(R wqo a w) andb w=I wqo a w++R wqo a w")
(inst-with-to "wqo a Head(R wqo a w) andb w=I wqo a w++R wqo a w" 'left
	      "wqo a Head(R wqo a w)")
(inst-with-to "wqo a Head(R wqo a w) andb w=I wqo a w++R wqo a w" 'right
	      "w=I wqo a w++R wqo a w")
(drop "wqo a Head(R wqo a w) andb w=I wqo a w++R wqo a w")
(simp "w=I wqo a w++R wqo a w")
(assert "R wqo a w=(Head(R wqo a w)::Tail(R wqo a w))")
 (simp "ZeroLtLhToHeadTailId")
 (use "Truth")
 (use "LToZeroLtLhR")
 (use "Law")
(assume "R wqo a w=(Head(R wqo a w)::Tail(R wqo a w))")
(simp "R wqo a w=(Head(R wqo a w)::Tail(R wqo a w))")
(drop "R wqo a w=(Head(R wqo a w)::Tail(R wqo a w))")
(use "EmbAppdRight")
(use "GenEmbCons")
(use "wqo a Head(R wqo a w)")
(use "IHv")
(use "EmbR wqo v Tail(R wqo a w)")
;; Proof finished.
(save "EmbRToEmb")

;; LargerWRToLargerW
(set-goal "all wqo,w,vs(LargerWR wqo w vs -> LargerW wqo w vs)")
(assume "wqo" "w")
(ind)
(ng)
(use "Efq")
(assume "v" "vs" "IHvs")
(ng)
(cases (pt "EmbR wqo v w"))
(ng)
(assume "Evw" "Useless")
(use "InitLargerW")
(use "EmbRToEmb")
(use "Evw")
(assume "Emb wqo w v -> F" "Lvws")
(use "GenLargerW")
(use-with "IHvs" "Lvws")
;; Proof finished.
(save "LargerWRToLargerW")

;; LargerWToLargerWR
(set-goal "all wqo,v,ws(LargerW wqo v ws -> LargerWR wqo v ws)")
(assume "wqo" "v1" "ws1" "LIv1ws1")
(elim "LIv1ws1")
(assume "wqo1" "v" "w" "ws" "Evw")
(ng)
(assert "EmbR wqo1 v w")
 (use "EmbToEmbR")
 (use "Evw")
(assume "EmbR wqo1 v w")
(simp "EmbR wqo1 v w")
(use "Truth")
(assume "wqo1" "v" "w" "vs" "Lwvs" "LRwvs")
(ng)
(cases (pt "EmbR wqo1 v w"))
(strip)
(use "Truth")
(assume "Useless")
(use "LRwvs")
;; Proof finished.
(save "LargerWToLargerWR")

;; LargerWRNil
(set-goal "all wqo,w(LargerWR wqo w(Nil list nat) -> F)")
(ng)
(assume "wqo" "w" "Absurd")
(use "Absurd")
;; Proof finished.
(save "LargerWRNil")

;; LargerWRSub
(set-goal
 "all wqo,ws,vs,w(vs sub ws -> LargerWR wqo w vs -> LargerWR wqo w ws)")
(assume "wqo")
(ind)
(ng)
(cases)
(ng)
(assume "w" "Useless" "Absurd")
(use "Absurd")
(ng)
(assume "v" "vs" "w")
(use "Efq")
(assume "w" "ws" "IHws")
(cases)
(ng)
(assume "w1" "Useless")
(use "Efq")
(assume "v" "vs")

;;   wqo  ws12089  w  ws  IHws:
;;     all vs,w(vs sub ws -> LargerWR wqo w vs -> LargerWR wqo w ws)
;;   vs12141  v  vs
;; -----------------------------------------------------------------------------
;; ?_17:all w0((v::vs)sub(w::ws) -> LargerWR wqo w0(v::vs) ->
;;             LargerWR wqo w0(w::ws))

;; Case v::vs sub ws.  Use IHws for v::vs and w0.  Have L w0(v::vs).  Hence
;; L w0 ws.  Hence L w0(w::ws) (unfold).

;; Case v=w and vs sub ws.  Have L w0(w::vs).  Goal L w0(w::ws).
;; Unfold L and do cases on Emb w w0.  If Emb w w0 -> F use IHws.

(assume "w1" "vvssubwws")
(ng "vvssubwws")
(cases (pt "v=w"))
;; Case v=w
(assume "v=w")
(simp "v=w")
(simphyp-with-to "vvssubwws" "v=w" "vssubws")
(ng "vssubws")
(drop "vvssubwws")
(ng #t)
(cases (pt "EmbR wqo w w1"))
(strip)
(use "Truth")
(ng #t)
(assume "Useless")
(use "IHws")
(use "vssubws")
;; Case v=w -> F
(assume "v=w -> F")
(simphyp-with-to "vvssubwws" "v=w -> F" "vvssubws")
(ng "vvssubws")
(drop "vvssubwws")
(assume "Lw1vvs")
(assert "LargerWR wqo w1 ws")
(use "IHws" (pt "v::vs"))
(use "vvssubws")
(use "Lw1vvs")
(ng #t)
(cases (pt "EmbR wqo w w1"))
(strip)
(use "Truth")
(assume "Useless" "Lw1ws")
(use "Lw1ws")
;; Proof finished.
(save "LargerWRSub")

;; LargerWElim
(set-goal "all wqo,w,v,vs(
 LargerW wqo w(v::vs) ->
 (Emb wqo v w -> Pvar^) -> (LargerW wqo w vs -> Pvar^) ->
 Pvar^)")
(assume "wqo" "w" "v" "vs" "Lwvvs")
(inversion "Lwvvs")
(ng)
(assume "wqo1" "v1" "w1" "vs1" "Ev1w1" "WqoHyp" "w=w1" "Conj" "EHyp" "Useless")
(inst-with-to "Conj" 'left "v=v1")
(use "EHyp")
(simp "WqoHyp")
(simp "v=v1")
(simp "w=w1")
(use "Ev1w1")
(ng)
(assume "wqo1" "v1" "w1" "vs1" "Lw1vs1" "Useless1" "WqoHyp""w=w1" "Conj"
	"Useless2" "LHyp")
(inst-with-to "Conj" 'right "vs=vs1")
(use "LHyp")
(simp "WqoHyp")
(simp "w=w1")
(simp "vs=vs1")
(use "Lw1vs1")
;; Proof finished.
(save "LargerWElim")

;; LargerWCons
(set-goal "all wqo,w,vs,a(LargerW wqo w vs -> LargerW wqo(a::w)vs)")
(assume "wqo" "w" "vs" "a" "Lwvs")
(elim "Lwvs")
(assume "wqo1" "v1" "w1" "vs1" "Ev1w1")
(use "InitLargerW")
(use "GenEmbInit")
(use  "Ev1w1")
(assume "wqo1" "v1" "w1" "vs1" "Lw1vs1")
(use "GenLargerW")
;; Proof finished.
(save "LargerWCons")

;; LargerWSub
(set-goal "all wqo,ws,vs,w(vs sub ws -> LargerW wqo w vs -> LargerW wqo w ws)")
(assume "wqo" "ws" "vs" "w" "vs sub ws" "Lwvs")
(use "LargerWRToLargerW")
(use "LargerWRSub" (pt "vs"))
(use "vs sub ws")
(use "LargerWToLargerWR")
(use "Lwvs")
;; Proof finished.
(save "LargerWSub")

;; LargerWAppdCases
(set-goal "all wqo,w,vs,us(LargerW wqo w(vs++us) ->
 (LargerW wqo w vs -> Pvar^) -> (LargerW wqo w us -> Pvar^) -> Pvar^) ")
(assume "wqo" "w")
(ind)
(ng)
(assume "us" "Lwus" "Useless" "Hyp")
(use-with "Hyp" "Lwus")
(ng)
(assume "v" "ws" "IHvs" "us" "Lwvwsus" "EHyp" "LHyp")
(use "LargerWElim" (pt "wqo") (pt "w") (pt "v") (pt "ws++us"))
(use  "Lwvwsus")
;; Emb wqo v w -> Pvar^
(assume "Evw")
(use "EHyp")
(use "InitLargerW")
(use "Evw")
;; LargerW wqo w(ws++us) -> Pvar^
(assume "Lwwsus")
(assert "LargerW wqo w ws -> Pvar^")
(assume "Lwws")
(use "EHyp")
(use "GenLargerW")
(use "Lwws")
(assume "LargerW wqo w ws -> Pvar^")
(use-with "IHvs" (pt "us") "Lwwsus" "LargerW wqo w ws -> Pvar^" "LHyp")
;; Proof finished.
(save "LargerWAppdCases")

;; LargerWAppdLeft
(set-goal "all wqo,w,vs,us(LargerW wqo w vs -> LargerW wqo w(vs++us))")
(assume "wqo" "w")
(ind)
(ng)
(assume "us" "LwNil")
(assert "LargerWR wqo w(Nil list nat)")
(use "LargerWToLargerWR")
(use "LwNil")
(ng)
(use "Efq")
(assume "v" "vs" "IHvs" "us" "Lwvvs")
(ng)
(use "LargerWElim" (pt "wqo") (pt "w") (pt "v") (pt "vs"))
(use "Lwvvs")
;; Emb wqo v w -> LargerW wqo w(v::vs++us)
(assume "Evw")
(use "InitLargerW")
(use "Evw")
;; LargerW wqo w vs -> LargerW wqo w(v::vs++us)
(assume "Lwvs")
(use "GenLargerW")
(use "IHvs")
(use "Lwvs")
;; Proof finished.
(save "LargerWAppdLeft")

;; LargerWAppdRight
(set-goal "all wqo,w,vs,us(LargerW wqo w us -> LargerW wqo w(vs++us))")
(assume "wqo" "w")
(ind)
(ng)
(assume "us" "Lwus")
(use "Lwus")
(assume "v" "vs" "IHvs" "us" "Lwus")
(ng)
(use "GenLargerW")
(use "IHvs")
(use "Lwus")
;; Proof finished.
(save "LargerWAppdRight")

;; LargerWMapcons
(set-goal "all wqo,vs,as,v,a(
 Incr wqo(a::as) -> Lh as=Lh vs -> LargerW wqo v vs ->
 LargerW wqo(a::v)(as mapcons vs))")
(assume "wqo")
(ind) ;on vs
(ng)
(assume "as" "v" "a" "IncrHyp" "LhHyp" "LvNil")
(assert "LargerWR wqo v(Nil list nat)")
 (use "LargerWToLargerWR")
(use "LvNil")
(ng)
(use "Efq")
;; Step
(assume "v" "vs" "IHvs")
(cases) ;on as
(ng)
(assume "as" "a" "Useless")
(use "Efq")
(assume "a" "as" "w" "a1")
(simp "IncrConj")
(simp "LargerARAllConj")
(assume "IncrHyp" "LhHyp" "Lwvvs")
(use "LargerWElim" (pt "wqo") (pt "w") (pt "v") (pt "vs"))
(use "Lwvvs")
;; Emb wqo v w -> LargerW wqo(a1::w)((a::as)mapcons v::vs)
(assume "Evw")
(use "InitLargerW")
(use "GenEmbCons")
(use "IncrHyp")
(use "Evw")
;;   wqo  vs15869  v  vs  IHvs:
;;     all as,v,a(
;;      Incr wqo(a::as) -> 
;;      Lh as=Lh vs -> LargerW wqo v vs -> LargerW wqo(a::v)(as mapcons vs))
;;   as15897  a  as  w  a1  IncrHyp:
;;     Incr wqo(a1::a::as)
;;   LhHyp:Lh(a::as)=Lh(v::vs)
;;   Lwvvs:LargerW wqo w(v::vs)
;; -----------------------------------------------------------------------------
;; ?_20:LargerW wqo w vs -> LargerW wqo(a1::w)((a::as)mapcons v::vs)
(assume "Lvws")
(use "GenLargerW")
(use "IHvs")
(simp "IncrConj")
(split)
(use "IncrHyp")
(assert "Incr wqo(a::as)")
 (use "IncrHyp")
(simp "IncrConj")
(assume "Conj")
(use "Conj")
(use "LhHyp")
(use "Lvws")
;; Proof finished.
(save "LargerWMapcons")

;; GoodWElim
(set-goal "all wqo,w,ws(
 GoodW wqo(w::ws) -> (GoodW wqo ws -> Pvar^) -> (LargerW wqo w ws -> Pvar^) ->
 Pvar^)")
(assume "wqo" "w" "ws" "Gwws")
(inversion "Gwws")
(ng)
(assume "wqo1" "w1" "ws1" "Lw1ws1" "WqoEq")
(simp "WqoEq")
(assume "Conj" "Useless" "LHyp")
(inst-with-to "Conj" 'left "w=w1")
(inst-with-to "Conj" 'right "ws=ws1")
(drop "Conj")
(simphyp-with-to "LHyp" "w=w1" "SLHyp")
(simphyp-with-to "SLHyp" "ws=ws1" "SSLHyp")
(use-with "SSLHyp" "Lw1ws1")
(ng)
(assume "wqo1" "w1" "ws1" "Gws1" "Useless1" "WqoEq")
(simp "WqoEq")
(assume "Conj" "GHyp" "Useless2")
(inst-with-to "Conj" 'right "ws=ws1")
(drop "Conj")
(simphyp-with-to "GHyp" "ws=ws1" "SGHyp")
(use-with "SGHyp" "Gws1")
;; Proof finished.
(save "GoodWElim")

;; GoodWNotNil
(set-goal "all wqo(GoodW wqo(Nil list nat) -> F)")
(assume "wqo" "GHyp")
(inversion "GHyp")
;; Proof finished.
(save "GoodWNotNil")

;; GoodWAppdLeft
(set-goal "all wqo,vs,us(GoodW wqo vs -> GoodW wqo(vs++us))")
(assume "wqo")
(ind) ;on vs
(ng)
(assume "us" "GNil")
(use "Efq")
(use "GoodWNotNil" (pt "wqo"))
(use "GNil")
(assume "v" "vs" "IHvs" "us" "Gvvs")
(use "GoodWElim" (pt "wqo") (pt "v") (pt "vs"))
(use "Gvvs")
;; GoodW wqo vs -> GoodW wqo((v::vs)++us)
(assume "Gvs")
(ng)
(use "GenGoodW")
(use "IHvs")
(use "Gvs")
;; LargerW wqo v vs -> GoodW wqo((v::vs)++us)
(assume "Lvvs")
(ng)
(use "InitGoodW")
(use "LargerWAppdLeft")
(use "Lvvs")
;; Proof finished.
(save "GoodWAppdLeft")

;; GoodWSub
(set-goal "all wqo,ws,vs(vs sub ws -> GoodW wqo vs -> GoodW wqo ws)")
(assume "wqo")
(ind)
(ng)
(cases)
(assume "Useless" "GNil")
(use "GNil")
(ng)
(assume "v" "vs")
(use "Efq")
(assume "w" "ws" "IHws")
(cases)
(assume "Useless" "GNil")
(use "Efq")
(use "GoodWNotNil" (pt "wqo"))
(use "GNil")
(assume "v" "vs")
;; (v::vs)sub(w::ws) -> GoodW wqo(v::vs) -> GoodW wqo(w::ws)
(ng)
(cases (pt "v=w"))
;; Case 1
(assume "v=w")
(ng)
(assume "vs sub ws" "Gvvs")
(use "GoodWElim" (pt "wqo") (pt "v") (pt "vs"))
(use "Gvvs")
;; GoodW wqo vs -> GoodW wqo(w::ws)
(assume "Gvs")
(use "GenGoodW")
(use "IHws" (pt "vs"))
(use "vs sub ws")
(use "Gvs")
;; LargerW wqo v vs -> GoodW wqo(w::ws)
(assume "Lvvs")
(use "InitGoodW")
(simp "<-" "v=w")
(use "LargerWSub" (pt "vs"))
(use "vs sub ws")
(use "Lvvs")
;; Case 2
(assume "v=w -> F")
(ng)
(assume "vvs sub ws" "Gvvs")
(use "GenGoodW")
(use "IHws" (pt "v::vs"))
(use "vvs sub ws")
(use "Gvvs")
;; Proof finished.
(save "GoodWSub")

;; GoodWToGoodWR
(set-goal "all wqo,ws(GoodW wqo ws -> GoodWR wqo ws)")
(assume "wqo" "ws" "Gws")
(elim "Gws")
(assume "wqo1" "v" "ws1" "Lvws1")
(ng)
(assert "LargerWR wqo1 v ws1")
 (use "LargerWToLargerWR")
 (use "Lvws1")
(assume "LRvws1")
(simp "LRvws1")
(use "Truth")
(assume "wqo1" "v" "ws1" "Useless" "GRws1")
(ng)
(simp "GRws1")
(ng)
(use "Truth")
;; Proof finished.
(save "GoodWToGoodWR")

;; GoodWRToGoodW
(set-goal "all wqo,ws(GoodWR wqo ws -> GoodW wqo ws)")
(assume "wqo")
(ind)
(ng)
(use "Efq")
(assume "v" "ws" "IHws")
(ng)
(cases (pt "LargerWR wqo v ws"))
(ng)
(assume "LRvws" "Useless")
(use "InitGoodW")
(use "LargerWRToLargerW")
(use "LRvws")
(assume "Useless" "GRws")
(use "GenGoodW")
(use-with "IHws" "GRws")
;; Proof finished.
(save "GoodWRToGoodW")

;; GoodWAppdMapcons
(set-goal "all wqo,ws,as,vs(Incr wqo as -> Lh as=Lh vs -> GoodW wqo(vs++ws) ->
  GoodW wqo((as mapcons vs)++ws))")
(assume "wqo" "ws")
(ind)
(cases)
(assume "Useless1" "Useless2")
(ng #t)
(assume "Gws")
(use "Gws")
(assume "v" "vs" "Useless")
(ng #t)
(use "Efq")
(assume "a" "as" "IHas")
(cases) ;on vs
(assume "Useless")
(ng #t)
(use "Efq")
(assume "v" "vs")
(simp "IncrConj")
(assume "IncrHyp" "LhHyp")
(ng "LhHyp")
(ng #t)
(assume "Gvvsws")
(use "GoodWElim" (pt "wqo") (pt "v") (pt "vs++ws"))
(use "Gvvsws")
(assume "Gvsws")
(use "GenGoodW")
(use "IHas")
(use "IncrHyp")
(use "LhHyp")
(use "Gvsws")
;; LargerW wqo v(vs++ws) -> GoodW wqo((a::v)::(as mapcons vs)++ws)
(assume "Lvvsws")
(use "LargerWAppdCases" (pt "wqo") (pt "v") (pt "vs") (pt "ws"))
(use "Lvvsws")
;; LargerW wqo v vs -> GoodW wqo((a::v)::(as mapcons vs)++ws)
(assume "Lvvs")
(simp "<-" "ListAppd1CompRule")
(use "GoodWAppdLeft")
(use "InitGoodW")
;;   vs17791  v  vs  IncrHyp:
;;     LargerARAll wqo a as andb Incr wqo as
;;   LhHyp:Lh as=Lh vs
;;   Gvvsws:GoodW wqo(v::vs++ws)
;;   Lvvsws:LargerW wqo v(vs++ws)
;;   Lvvs:LargerW wqo v vs
;; -----------------------------------------------------------------------------
;; ?_38:LargerW wqo(a::v)(as mapcons vs)
(use "LargerWMapcons")
(simp "IncrConj")
(use "IncrHyp")
(use "LhHyp")
(use "Lvvs")
;; LargerW wqo v ws -> GoodW wqo((a::v)::(as mapcons vs)++ws) 
(assume "Lvws")
(simp "<-" "ListAppd1CompRule")
(use "InitGoodW")
(use "LargerWAppdRight")
(use "LargerWCons")
(use "Lvws")
;; Proof finished.
(save "GoodWAppdMapcons")

;; LargerARAllHeadTail
(set-goal "all wqo,a,as(
 wqo Head as a -> LargerARAll wqo a Tail as -> LargerARAll wqo a as)")
(assume "wqo" "a")
(cases)
(ng)
(strip)
(use "Truth")
(assume "a0" "as")
(ng)
(assume "a>=a0")
(simp "a>=a0")
(assume "LAllHyp")
(use "LAllHyp")
;; Proof finished.
(save "LargerARAllHeadTail")

;; Since we do not want to assume that wqo has a least element we need
;; to assume 0<Lh as

;; LargerARAllHead
(set-goal "all wqo,a,as(0<Lh as -> LargerARAll wqo a as -> wqo Head as a)")
(assume "wqo" "a")
(cases)
(ng)
(use "Efq")
(ng #t)
(assume "a0" "as" "Useless")
(simp "IfAndb")
(assume "Conj")
(use "Conj")
;; Proof finished.
(save "LargerARAllHead")

;; LargerARAllTail
(set-goal "all wqo,a,as(0<Lh as ->
 LargerARAll wqo a as -> LargerARAll wqo a Tail as)")
(assume "wqo" "a")
(cases)
(ng)
(use "Efq")
(assume "a0" "as" "Useless")
(ng)
(simp "IfAndb")
(assume "Conj")
(use "Conj")
;; Proof finished.
(save "LargerARAllTail")

;; LargerARAllAllConj
(set-goal "all wqo,a,as,ass
 LargerARAllAll wqo a(as::ass)=
 (LargerARAll wqo a as andb LargerARAllAll wqo a ass)")
(assume "wqo" "a" "as" "ass")
(ng)
(simp "IfAndb")
(use "Truth")
;; Proof finished.
(save "LargerARAllAllConj")

;; LargerARExAllIntro
(set-goal "all wqo,a,as,ass(ESeqA as ass -> 
 LargerAR wqo a Heads ass -> LargerARAll wqo a as -> LargerARExAll wqo a ass)")
(assume "wqo" "a" "as")
(ind)
(ng)
(assume "Useless1" "Absurd" "Useless2")
(use "Absurd")
(assume "as0" "ass" "IH" "ESeqHyp")
(ng "ESeqHyp")
(inst-with-to "ESeqHyp" 'left "as0Char")
(simp "as0Char")
(ng)
(cases (pt "wqo Head as0 a"))
;; Case 1.
(ng)
(assume "Useless1" "Useless2" "LAllHyp")
(simp "LAllHyp")
(use "Truth")
;; Case 2.
(ng)
(assume "Useless")
(use "IH")
(use "ESeqHyp")
;; Proof finished.
(save "LargerARExAllIntro")

;; LargerARExAllAppdCases
(set-goal "all wqo,a,ass,bss(LargerARExAll wqo a(ass++bss) ->
 (LargerARExAll wqo a ass -> Pvar) ->
 (LargerARExAll wqo a bss -> Pvar) -> Pvar)")
(assume "wqo" "a")
(ind)
(ng)
(assume "bss" "a>=bss" "Useless" "Hyp")
(use-with "Hyp" "a>=bss")
(assume "as1" "vs" "IH" "bss")
(ng #t)
(cases (pt "(LargerARAll wqo a as1)"))
(ng)
(assume "Useless1" "THyp" "Hyp" "Useless2")
(use-with "Hyp" "THyp")
(ng)
(assume "Useless")
(use "IH")
;; Proof finished.
(save "LargerARExAllAppdCases")

;; LargerARAppdCases
(set-goal "all wqo,a,as,bs(
 LargerAR wqo a(as++bs) ->
 (LargerAR wqo a as -> Pvar) -> (LargerAR wqo a bs -> Pvar) -> Pvar)")
(assume "wqo" "a")
(ind)
(ng)
(assume "bs" "a>=bs" "Useless" "Hyp")
(use-with "Hyp" "a>=bs")
(assume "a1" "v" "IH" "bs")
(ng #t)
(cases (pt "wqo a1 a"))
(ng)
(assume "Useless1" "THyp" "Hyp" "Useless2")
(use-with "Hyp" "THyp")
(ng)
(assume "Useless")
(use "IH")
;; Proof finished.
(save "LargerARAppdCases")

;; LhInsertAF
(set-goal "all wqo,tas,a Lh(InsertAF wqo tas a)=Lh tas")
(assume "wqo")
(ind)
(ng)
(assume "a")
(use "Truth")
(assume "ta" "tas" "IH")
(ng)
(use "IH")
;; Proof finished.
(save "LhInsertAF")

(display-pconst "InsertF")

;; LhInsertF
(set-goal "all wqo,ts,v,a Lh(InsertF wqo ts v a)=Lh ts")
(assume "wqo")
(ind)
(ng)
(strip)
(use "Truth")
(assume "t" "ts" "IH")
(ng)
(use "IH")
;; Proof finished.
(save "LhInsertF")

;; InsertFAppd
(set-goal "all wqo,a,v,ss,ts
 InsertF wqo(ts++ss)v a=InsertF wqo ts v a++InsertF wqo ss v a")
(assume "wqo" "a" "v" "ss")
(ind)
(ng)
(use "Truth")
(assume "t" "ts" "IH")
(ng #t)
(use "IH")
;; Proof finished.
(save "InsertFAppd")

;; InsertAFAppd
(set-goal "all wqo,a,sas,tas
 InsertAF wqo(tas++sas)a=InsertAF wqo tas a++InsertAF wqo sas a")
(assume "wqo" "a" "sas")
(ind)
(ng)
(use "Truth")
(assume "ta" "tas" "IH")
(ng #t)
(use "IH")
;; Proof finished.
(save "InsertAFAppd")

;; InsertFId
(set-goal "all wqo,a,v,ts(
 (LargerARExAll wqo a Rhts Roots ts -> F) -> InsertF wqo ts v a=ts)")
(assume "wqo" "a" "v")
(ind)
(ng)
(strip)
(use "Truth")
(assume "t" "ts" "IH")
(ng)
(cases (pt "LargerARAll wqo a rht Root t"))
;; Case 1
(ng)
(assume "Useless" "Absurd")
(use "Efq")
(use-with "Absurd" "Truth")
;; Case 2
(ng)
(assume "LAllHyp")
(use "IH")
;; Proof finished.
(save "InsertFId")

;; InsertAFId
(set-goal "all wqo,a,tas(
 (LargerARExAll wqo a Roots tas -> F) -> InsertAF wqo tas a=tas)")
(assume "wqo" "a")
(ind)
(ng)
(strip)
(use "Truth")
(assume "ta" "tas" "IH")
(ng)
(cases (pt "LargerARAll wqo a Root ta"))
;; Case 1
(ng)
(assume "Useless" "Absurd")
(use "Efq")
(use-with "Absurd" "Truth")
;; Case 2
(ng)
(assume "LAllHyp")
(use "IH")
;; Proof finished.
(save "InsertAFId")

;; RootProj
(set-goal "all t rht Root t=Root(ProjT t)")
(assume "t")
(assert "(Root t%Subtrees t)eqd t")
 (use "RootSubtreesId")
(assume "(Root t%Subtrees t)eqd t")
(simp "<-" "(Root t%Subtrees t)eqd t")
(drop "(Root t%Subtrees t)eqd t")
(ng)
(use "Truth")
;; Proof finished.
(save "RootProj")

;; RootsProjF
(set-goal "all ts Rhts Roots ts=Roots(ProjF ts)")
(ind)
(ng)
(use "Truth")
(assume "t" "ts" "IH")
(ng)
(split)
(use "RootProj")
(use "IH")
;; Proof finished.
(save "RootsProjF")

;; InsertFAppdRight
(set-goal
 "all wqo,a,v,ss,ts(
 (LargerARExAll wqo a Rhts Roots ts -> F) -> 
 InsertF wqo(ts++ss)v a=ts++InsertF wqo ss v a)")
(assume "wqo" "a" "v" "ss" "ts" "NegLExAllHyp")
(simp "InsertFAppd")
(assert "InsertF wqo ts v a=ts")
 (use "InsertFId")
 (use "NegLExAllHyp")
(assume "InsertF wqo ts v a=ts")
(simp "InsertF wqo ts v a=ts")
(use "Truth")
;; Proof finished.
(save "InsertFAppdRight")

;; InsertFEqInsertT
(set-goal "all wqo,a,t,v(
 LargerARAll wqo a rht Root t -> InsertF wqo t:v a=(InsertT wqo t v a):)")
(assume "wqo" "a" "t" "v" "LAllHyp")
(ng)
(simp "LAllHyp")
(use "Truth")
;; Proof finished.
(save "InsertFEqInsertT")

;; InsertAFEqInsertAT
(set-goal "all wqo,a,ta(LargerARAll wqo a Root ta ->
 InsertAF wqo ta:a=(InsertAT wqo ta a):)")
(assume "wqo" "a" "ta" "LAllHyp")
(ng)
(simp "LAllHyp")
(use "Truth")
;; Proof finished.
(save "InsertAFEqInsertAT")

;; RootInsert
(set-goal "all wqo,t,v,a Root(InsertT wqo t v a)=Root t")
(assume "wqo" "t" "v" "a")
(assert "t=(Root t%Subtrees t)")
 (simp "RootSubtreesId")
 (use "Truth")
(assume "t=(Root t%Subtrees t)")
(simp "t=(Root t%Subtrees t)")
(drop "t=(Root t%Subtrees t)")
(ng)
(use "Truth")
;; Proof finished.
(save "RootInsert")

;; RootsInsert
(set-goal "all wqo,v,a,ts Roots(InsertF wqo ts v a)=Roots ts")
(assume "wqo" "v" "a")
(ind)
(ng)
(use "Truth")
(assume "t" "ts" "IH")
(ng)
(split)
(cases (pt "(LargerARAll wqo a rht Root t)"))
;; Case 1.
(assume "Useless")
(ng)
(use "RootInsert")
;; Case 2.
(assume "Useless")
(use "Truth")
(use "IH")
;; Proof finished.
(save "RootsInsert")

;; RootInsertA
(set-goal "all wqo,ta,a Root(InsertAT wqo ta a)=Root ta")
(assume "wqo" "ta" "a")
(assert "ta=(Root ta%Subtrees ta)")
 (simp "RootSubtreesId")
 (use "Truth")
(assume "ta=(Root ta%Subtrees ta)")
(simp "ta=(Root ta%Subtrees ta)")
(drop "ta=(Root ta%Subtrees ta)")
(ng)
(use "Truth")
;; Proof finished.
(save "RootInsertA")

;; RootsInsertA
(set-goal "all wqo,a,tas Roots(InsertAF wqo tas a)=Roots tas")
(assume "wqo" "a")
(ind)
(ng)
(use "Truth")
(assume "ta" "tas" "IH")
(ng)
(split)
(cases (pt "(LargerARAll wqo a Root ta)"))
;; Case 1.
(assume "Useless")
(ng)
(use "RootInsertA")
;; Case 2.
(assume "Useless")
(use "Truth")
(use "IH")
;; Proof finished.
(save "RootsInsertA")

;; LAllAllTailsRhtsRootsForest
(set-goal "all wqo,a,ws(
 LargerARAllAll wqo a Tails Rhts Roots(Forest wqo ws))")
(assume "wqo" "a")
(ind)
(ng)
(use "Truth")
(cases)
(ng)
(assume "ws" "Hyp")
(use "Hyp")
(assume "a0" "v" "ws" "IH")
(ng #t)
(cases (pt "LargerAR wqo a0(BSeq wqo Heads ws)"))
;; Case 1.
(assume "Useless")
(ng #t)
(simp "RootsInsert")
(use "IH")
;; Case 2.
(assume "Useless")
(ng #t)
(use "IH")
;; Proof finished.
(save "LAllAllTailsRhtsRootsForest")

;; NilTailsRhtsRootsForest
(set-goal "all wqo,a,ws,i(i<Lh(Forest wqo ws) ->
 Lh(i thof Tails Rhts Roots(Forest wqo ws))=0)")
(assume "wqo" "a")
(ind)
(ng)
(assume "i")
(use "Efq")
(cases)
(ng)
(assume "ws" "Hyp")
(use "Hyp")
(assume "a0" "v" "ws" "IH")
(ind)
(ng #t)
(cases (pt "LargerAR wqo a0(BSeq wqo Heads ws)"))
;; Case 1.
(assume "Useless")
(ng #t)
(simp "RootsInsert")
(simp "LhInsertF")
(use "IH")
;; Case 2.
(assume "Useless")
(ng #t)
(strip)
(use "Truth")
(assume "i" "IHi")
(ng #t)
(cases (pt "LargerAR wqo a0(BSeq wqo Heads ws)"))
;; Case 1.
(ng #t)
(simp "RootsInsert")
(simp "LhInsertF")
(assume "Useless")
(use "IH")
;; Case 2.
(assume "Useless")
(ng #t)
(use "IH")
;; Proof finished.
(save "NilTailsRhtsRootsForest")

;; ATreeNeqAppdCases
(set-goal "all tas1,tas2,sas1,sas2(Lh tas1=Lh tas2 ->
 Lh sas1=Lh sas2 ->
 (tas1++sas1=tas2++sas2)=False -> 
 ((tas1=tas2)=False -> Pvar) ->
 (tas1=tas2 -> (sas1=sas2)=False -> Pvar) -> Pvar)")
(ind)
(ng)
(cases)
(ng)
(assume "sas1" "sas2" "Useless1" "Useless2" "sas1=/=sas2" "Useless3" "Hyp")
(use-with "Hyp" "Truth" "sas1=/=sas2")
(ng)
(assume "sa1" "sas1" "sas2" "sas3")
(use "Efq")
(assume "ta1" "tas1" "IHtas1")
(cases)
(ng)
(assume "sas1" "sas2")
(use "Efq")
(assume "ta2" "tas2" "sas1" "sas2")
(ng)
(cases (pt "ta1=ta2"))
;; Case 1.
(ng)
(assume "EqHyp")
(use "IHtas1")
;; Case 2.
(ng)
(assume "Useless1" "Useless2" "Useless3" "Useless4" "Hyp" "Useless5")
(use-with "Hyp" "Truth")
;; Proof finished.
(save "ATreeNeqAppdCases")

;; GoodARConsBad
(set-goal
 "all wqo,a,as(GoodAR wqo(a::as) -> (GoodAR wqo as -> F) -> LargerAR wqo a as)")
(assume "wqo" "a" "as")
(ng #t)
(cases (pt "LargerAR wqo a as"))
(strip)
(use "Truth")
(ng #t)
(assume "Useless" "Gas" "Bas")
(use-with "Bas" "Gas")
;; Proof finished.
(save "GoodARConsBad")

;; NotGoodARBSeq
(set-goal "all wqo,as(GoodAR wqo(BSeq wqo as) -> F)")
(assume "wqo")
(ind)
(ng)
(assume "Absurd")
(use "Absurd")
(assume "a" "as" "IHas")
(ng)
(cases (pt "LargerAR wqo a(BSeq wqo as)"))
(assume "LHyp")
(ng #t)
(use "IHas")
(assume "NegLHyp")
(ng #t)
(simp "NegLHyp")
(ng #t)
(use "IHas")
;; Proof finished.
(save "NotGoodARBSeq")

;; GLFAppd
(set-goal "all wqo,ts,ss(GLF wqo ts -> GLF wqo(ts++ss))")
(assume "wqo")
(ind)
(ng)
(assume "ss")
(use "Efq")
(assume "t" "ts" "IH")
(ng)
(assume "ss")
(cases (pt "GLT wqo t"))
(ng)
(strip)
(use "Truth")
(assume "Useless")
(ng)
(use "IH")
;; Proof finished.
(save "GLFAppd")

;; GLFAppdLeft
(set-goal "all wqo,ts,ss(GLF wqo ss -> GLF wqo(ts++ss))")
(assume "wqo")
(ind)
(ng)
(assume "ss")
(assume "GLFHyp")
(use "GLFHyp")
(assume "t" "ts" "IH")
(ng)
(assume "ss")
(cases (pt "GLT wqo t"))
(ng)
(strip)
(use "Truth")
(assume "Useless")
(ng)
(use "IH")
;; Proof finished.
(save "GLFAppdLeft")

;; GenIndGLT
(set-goal "all wqo,ts,vsas(GLF wqo ts -> GLT wqo(vsas%ts))")
(assume "wqo")
(cases)
(ng)
(assume "vsas")
(use "Efq")
(assume "t" "ts" "vsas")
(ng)
(assume "Hyp")
(use "Hyp")
;; Proof finished.
(save "GenIndGLT")

;; ExGLTToGLF
(set-goal "all wqo,ts,i(i<Lh ts -> GLT wqo(i thof ts) -> GLF wqo ts)")
(assume "wqo")
;; Induction on ts
(ind)
(ng)
(assume "i")
(use "Efq")
(assume "t" "ts" "IHts")
(cases)
(ng)
(assume "Useless" "GLTt")
(simp "GLTt")
(use "Truth")
(assume "i")
(ng)
(cases (pt "GLT wqo t"))
(strip)
(use "Truth")
(assume "Useless")
(use "IHts")
;; Proof finished.
(save "ExGLTToGLF")

;; ProjFIf
(set-goal "all ts,ss,boole
 ProjF[if boole ts ss]=[if boole (ProjF ts) (ProjF ss)]")
(assume "ts" "ss")
(cases)
(ng #t)
(use "Truth")
(ng #t)
(use "Truth")
;; Proof finished.
(save "ProjFIf")

;; ProjFAppd
(set-goal "all ts,ss(ProjF(ts++ss)=ProjF ts++ProjF ss)")
(ind)
(ng)
(assume "ss")
(use "Truth")
(assume "t" "ts" "IH" "ss")
(ng #t)
(use "IH")
;; Proof finished.
(save "ProjFAppd")

;; LhProjF
(set-goal "all ts Lh(ProjF ts)=Lh ts")
(ind)
(use "Truth")
(assume "t" "ts" "IH")
(ng)
(use "IH")
;; Proof finished.
(save "LhProjF")

;; ProjNewTreeEqNewATree
(set-goal "all vsas ProjT(NewTree vsas)=NewATree rht vsas")
(assume "vsas")
(simp "NewTreeDef")
(simp "NewATreeDef")
(ng)
(use "Truth")
;; Proof finished.
(save "ProjNewTreeEqNewATree")

;; InsertAProjEqProjInsertAux
(set-goal "all wqo,a,v,n(
 all t(
 HtT t<n -> InsertAT wqo(ProjT t)a=ProjT(InsertT wqo t v a)) &
 all ts(
  HtF ts<n -> InsertAF wqo(ProjF ts) a=ProjF(InsertF wqo ts v a)))")
(assume "wqo" "a" "v")
(ind)
(split)
(assume "t")
(ng #t)
(use "Efq")
(assume "ts")
(ng #t)
(use "Efq")
;; Step
(assume "n" "IH")
(split)
(assume "t")
(simp "<-" "RootSubtreesId")
(assert "HtT(Root t%Subtrees t)=Succ HtF Subtrees t")
 (use "Truth")
(assume "HtT(Root t%Subtrees t)=Succ HtF Subtrees t")
(simp "HtT(Root t%Subtrees t)=Succ HtF Subtrees t")
(drop "HtT(Root t%Subtrees t)=Succ HtF Subtrees t")
(assume "HtF Subtrees t<n")
(ng "HtF Subtrees t<n")
(simp "ProjT0CompRule")
(simp "InsertAT0CompRule")
(simp "InsertT0CompRule")
(simp "ProjT0CompRule")
(simp "IH")
(simp "RootsProjF")
(cases (pt "(LargerARExAll wqo a Roots(ProjF Subtrees t))"))
;; Case 1.
(ng #t)
(strip)
(use "Truth")
;; Case 2.
(ng #t)
(simp "ProjNewTreeEqNewATree")
(ng #t)
(strip)
(use "Truth")
(use "HtF Subtrees t<n")
;; Case ts
;; all ts(HtF ts<Succ n -> InsertAF wqo(ProjF ts)a=ProjF(InsertF wqo ts v a))
(ind)
(ng #t)
(assume "Trivial")
(use "Trivial")
(assume "t" "ts" "IHtF" "HtBound")
(ng "HtBound")
(simp "ProjF1CompRule")
(simp "InsertAF1CompRule")
(simp "InsertF1CompRule")
(simp "RootProj")
(cases (pt "LargerARAll wqo a Root(ProjT t)"))
;; Case 1.
(ng #t)
(assume "LAllHyp")
(split)
(use "IH")
(use "NatLeLtTrans" (pt "HtT t max HtF ts"))
(use "NatMaxUB1")
(use "HtBound")
(use "IH")
(use "NatLeLtTrans" (pt "HtT t max HtF ts"))
(use "NatMaxUB2")
(use "HtBound")
;; Case 2.
(ng #t)
(assume "NeqLAllHyp")
(use "IH")
(use "NatLeLtTrans" (pt "HtT t max HtF ts"))
(use "NatMaxUB2")
(use "HtBound")
;; Proof finished.
(save "InsertAProjEqProjInsertAux")

;; InsertATProjEqProjInsertT
(set-goal "all wqo,a,v,t InsertAT wqo(ProjT t)a=ProjT(InsertT wqo t v a)")
(assume "wqo" "a" "v" "t")
(use "InsertAProjEqProjInsertAux" (pt "Succ HtT t"))
(use "Truth")
;; Proof finished.
(save "InsertATProjEqProjInsertT")

;; InsertAFProjFEqProjFInsertF
(set-goal "all wqo,a,v,ts InsertAF wqo(ProjF ts)a=ProjF(InsertF wqo ts v a)")
(assume "wqo" "a" "v" "ts")
(use "InsertAProjEqProjInsertAux" (pt "Succ HtF ts"))
(use "Truth")
;; Proof finished.
(save "InsertAFProjFEqProjFInsertF")

;; ESeqToESeqA
(set-goal "all vsas,vsass(
 ESeq vsas vsass -> ESeqA rht vsas Rhts vsass)")
(assume "vsas")
(ind)
(ng)
(strip)
(use "Truth")
(assume "vsas0" "vsass" "IH")
(ng)
(assume "Conj")
(split)
(use "Conj")
(use "IH")
(use "Conj")
;; Proof finished.
(save "ESeqToESeqA")

;; ESeqToESeqAProj
(set-goal "all vsas,ts(
 ESeq vsas Roots ts -> ESeqA rht vsas Roots(ProjF ts))")
(assume "vsas")
(ind)
(ng)
(assume "Hyp")
(use "Hyp")
(assume "t" "ts" "IH")
(ng)
(assume "Conj")
(split)
(simp "<-" "RootProj")
(use "Conj")
(use "IH")
(use "Conj")
;; Proof finished.
(save "ESeqToESeqAProj")

;; ESeqALAllLAllAllTails
(set-goal "all wqo,a,as,ass(
 ESeqA as ass ->
 LargerARAll wqo a as -> LargerARAllAll wqo a Tails ass)")
(assume "wqo" "a" "as")
(ind)
(ng)
(strip)
(use "Truth")
(assume "as1" "ass" "IH")
(ng #t)
(simp "IfAndb")
(assume "Conj")
(inst-with-to "Conj" 'left "asProp")
(simp "asProp")
(assume "LAllHyp")
(split)
(use "LAllHyp")
(use "IH")
(use "Conj")
(use "LAllHyp")
;; Proof finished.
(save "ESeqALAllLAllAllTails")

;; CorrProjTToLhPos
(set-goal "all wqo,t(CorrAT wqo(ProjT t) -> 0<Lh rht Root t)")
(assume "wqo" "t")
(assert "t=(Root t%Subtrees t)")
 (simp "RootSubtreesId")
 (use "Truth")
(assume "tProp")
(simp "tProp")
(ng)
(assume "Conj")
(use "Conj")
;; Proof finished.
(save "CorrProjTToLhPos")

;; CorrToLhPos
(set-goal "all wqo,ta(CorrAT wqo ta -> 0<Lh Root ta)")
(assume "wqo" "ta")
(assert "ta=(Root ta%Subtrees ta)")
 (simp "RootSubtreesId")
 (use "Truth")
(assume "taProp")
(simp "taProp")
(ng)
(assume "Conj")
(use "Conj")
;; Proof finished.
(save "CorrToLhPos")

;; CorrConsAux
(set-goal "all wqo,ws,w,n(
 all t(HtT t<n -> CorrT wqo ws t -> CorrT wqo(w::ws)t) &
 all ts(HtF ts<n -> CorrF wqo ws ts -> CorrF wqo(w::ws)ts))")
(assume "wqo" "ws" "w")
(ind)
(split)
(assume "t")
(ng)
(use "Efq")
(assume "ts")
(ng)
(use "Efq")
(assume "n" "IH")
(split)
;; Case t
(assume "t")
(assert "(Root t%Subtrees t)eqd t")
 (use "RootSubtreesId")
(assume "(Root t%Subtrees t)eqd t")
(simp "<-" "(Root t%Subtrees t)eqd t")
(drop "(Root t%Subtrees t)eqd t")
(assert "HtT(Root t%Subtrees t)=Succ HtF Subtrees t")
 (use "Truth")
(assume "HtT(Root t%Subtrees t)=Succ HtF Subtrees t")
(simp "HtT(Root t%Subtrees t)=Succ HtF Subtrees t")
(drop "HtT(Root t%Subtrees t)=Succ HtF Subtrees t")
(assume "HtF Subtrees t<n")
(ng)
(assume "CorrHyp")
(split)
(use "CorrHyp")
(split)
(use "CorrHyp")
(split)
(use "CorrHyp")
(split)
(use "CorrHyp")
(split)
(use "SubTrans" (pt "ws"))
(use "CorrHyp")
(use "Truth")
(use "IH")
(use "HtF Subtrees t<n")
(use "CorrHyp")
;; Case ts
(ind)
(ng #t)
(strip)
(use "Truth")
(assume "t" "ts" "IHts" "HtBound" "CorrHyp")
(ng "HtBound")
(ng "CorrHyp")
(ng #t)
(split)
(use "IH")
(use "NatLeLtTrans" (pt "HtT t max HtF ts"))
(use "NatMaxUB1")
(use "HtBound")
(use "CorrHyp")
(use "IHts")
(use "NatLtTrans" (pt "n"))
(use "NatLeLtTrans" (pt "HtT t max HtF ts"))
(use "NatMaxUB2")
(use "HtBound")
(use "Truth")
(use "CorrHyp")
;; Proof finished.
(save "CorrConsAux")

;; CorrTCons
(set-goal "all wqo,ws,w,t(CorrT wqo ws t -> CorrT wqo(w::ws)t)")
(assume "wqo" "ws" "w" "t" "CorrTHyp")
(use "CorrConsAux" (pt "Succ HtT t"))
(use "Truth")
(use "CorrTHyp")
;; Proof finished.
(save "CorrTCons")

;; CorrFCons
(set-goal "all wqo,ws,w,ts(CorrF wqo ws ts -> CorrF wqo(w::ws)ts)")
(assume "wqo" "ws" "w" "ts" "CorrFHyp")
(use "CorrConsAux" (pt "Succ HtF ts"))
(use "Truth")
(use "CorrFHyp")
;; Proof finished.
(save "CorrFCons")

;; CorrInsertAux
(set-goal "all wqo,ws,a,v,n(
 all t(HtT t<n -> CorrT wqo ws t -> LargerARAll wqo a rht Root t -> 
      CorrT wqo((a::v)::ws)(InsertT wqo t v a))&
 all ts(HtF ts<n -> CorrF wqo ws ts ->
      CorrF wqo((a::v)::ws)(InsertF wqo ts v a)))")
(assume "wqo" "ws" "a" "v")
(ind)
(split)
(assume "t")
(ng)
(use "Efq")
(assume "ts")
(ng)
(use "Efq")
(assume "n" "IH")
(split)
;; Case t
(assume "t")
(assert "(Root t%Subtrees t)eqd t")
 (use "RootSubtreesId")
(assume "(Root t%Subtrees t)eqd t")
(simp "<-" "(Root t%Subtrees t)eqd t")
(drop "(Root t%Subtrees t)eqd t")
(assert "HtT(Root t%Subtrees t)=Succ HtF Subtrees t")
 (use "Truth")
(assume "HtT(Root t%Subtrees t)=Succ HtF Subtrees t")
(simp "HtT(Root t%Subtrees t)=Succ HtF Subtrees t")
(drop "HtT(Root t%Subtrees t)=Succ HtF Subtrees t")
(assume "HtF Subtrees t<n")
(ng "HtF Subtrees t<n")
(assume "CorrHyp")
(ng "CorrHyp")
(assume "LAllHyp")
(ng "LAllHyp")
(simp "InsertT0CompRule")
(cases (pt "(LargerARExAll wqo a Rhts Roots Subtrees t)"))
;; Case True
(assume "LExAllHyp")
(ng #t)
(msplit)
;; ?_45:CorrF wqo((a::v)::ws)(InsertF wqo Subtrees t v a)
(use "IH")
(use "HtF Subtrees t<n")
(use "CorrHyp")
;; ?_44:(rht Root t mapcons Lh rht Root t init lft Root t)++
;;      (Lh rht Root t rest lft Root t)sub
;;      ((a::v)::ws)
(use "SubTrans" (pt "ws"))
(use "CorrHyp")
(use "Truth")
;; ?_42:ESeq Root t Roots(InsertF wqo Subtrees t v a)
(simp "RootsInsert")
(use "CorrHyp")
;; ?_40:Incr wqo rht Root t
(use "CorrHyp")
;; ?_38:0<Lh rht Root t
(use "CorrHyp")
;; ?_36:Lh rht Root t<=Lh lft Root t
(use "CorrHyp")
;; Case False
(assume "NotLExAllHyp")
(ng #t)
(msplit)
;; ?_64:CorrF wqo((a::v)::ws)Subtrees t
(use "CorrFCons")
(use "CorrHyp")
;; ?_63:CorrT wqo((a::v)::ws)(NewTree((v::lft Root t)pair a::rht Root t))
(simp "NewTreeDef")
(ng #t)
(msplit)
;; ?_71:(rht Root t mapcons Lh rht Root t init lft Root t)++
;;      (Lh rht Root t rest lft Root t)sub 
;;      ws
(use "CorrHyp")
;; ?_70:[if (LargerARAll wqo a rht Root t) (Incr wqo rht Root t) False]
(simp "LAllHyp")
(use "CorrHyp")
;; ?_68:Lh rht Root t<=Lh lft Root t
(use "CorrHyp")
;; ?_61:(rht Root t mapcons Lh rht Root t init lft Root t)++
;;      (Lh rht Root t rest lft Root t)sub
;;      ((a::v)::ws)
(use "SubTrans" (pt "ws"))
(use "CorrHyp")
(use "Truth")
;; ?_59:Tail lft Root(NewTree((v::lft Root t)pair a::rht Root t))=lft Root t andb 
;;      Tail rht Root(NewTree((v::lft Root t)pair a::rht Root t))=rht Root t andb 
;;      ESeq Root t Roots Subtrees t
(simp "NewTreeDef")
(ng #t)
(use "CorrHyp")
;; ?_57:Incr wqo rht Root t
(use "CorrHyp")
;; ?_55:0<Lh rht Root t
(use "CorrHyp")
;; ?_53:Lh rht Root t<=Lh lft Root t
(use "CorrHyp")
;; Case ts
(ind)
(ng #t)
(strip)
(use "Truth")
(assume "t" "ts" "IHts" "HtBound" "CorrHyp")
(ng "HtBound")
(ng "CorrHyp")
(simp "InsertF1CompRule")
(cases (pt "LargerARAll wqo a rht Root t"))
;; Case 1
(assume "LargerARAll wqo a rht Root t")
(ng #t)
(split)
(use "IH")
(use "NatLeLtTrans" (pt "HtT t max HtF ts"))
(use "NatMaxUB1")
(use "HtBound")
(use "CorrHyp")
(use "LargerARAll wqo a rht Root t")
(use "IH")
(use "NatLeLtTrans" (pt "HtT t max HtF ts"))
(use "NatMaxUB2")
(use "HtBound")
(use "CorrHyp")
;; Case 2
(assume "LargerARAll wqo a rht Root t -> F")
(ng #t)
(split)
(use "CorrTCons")
(use "CorrHyp")
(use "IH")
(use "NatLeLtTrans" (pt "HtT t max HtF ts"))
(use "NatMaxUB2")
(use "HtBound")
(use "CorrHyp")
;; Proof finished.
(save "CorrInsertAux")

;; CorrTInsertT
(set-goal "all wqo,ws,t,a,v(CorrT wqo ws t -> LargerARAll wqo a rht Root t -> 
      CorrT wqo((a::v)::ws)(InsertT wqo t v a))")
(assume "wqo" "ws" "t" "a" "v")
(use "CorrInsertAux" (pt "Succ HtT t"))
(use "Truth")
;; Proof finished.
(save "CorrTInsertT")

;; CorrFInsertF
(set-goal "all wqo,ws,ts,a,v(CorrF wqo ws ts ->
      CorrF wqo((a::v)::ws)(InsertF wqo ts v a))")
(assume "wqo" "ws" "ts" "a" "v")
(use "CorrInsertAux" (pt "Succ HtF ts"))
(use "Truth")
;; Proof finished.
(save "CorrFInsertF")

;; ExtAInsertAux
(set-goal "all wqo,a,n(
 all ta(HtT ta<n -> ExtAT ta -> ExtAT(InsertAT wqo ta a)) &
 all tas(HtF tas<n -> ExtAF tas -> ExtAF(InsertAF wqo tas a)))")
(assume "wqo" "a")
(ind)
(split)
(assume "ta")
(ng)
(use "Efq")
(assume "tas")
(ng)
(use "Efq")
(assume "n" "IH")
(split)
;; Case ta
(assume "ta")
(assert "(Root ta%Subtrees ta)eqd ta")
 (use "RootSubtreesId")
(assume "(Root ta%Subtrees ta)eqd ta")
(simp "<-" "(Root ta%Subtrees ta)eqd ta")
(drop "(Root ta%Subtrees ta)eqd ta")
(ng #t)
(assume "HtBound" "ExtHyp")
(cases (pt "(LargerARExAll wqo a Roots Subtrees ta)"))
;; Case True
(assume "LExAllHyp")
(ng #t)
(split)
(simp "RootsInsertA")
(use "ExtHyp")
(use "IH")
(use "HtBound")
(use "ExtHyp")
;; Case False
(assume "NotLargerExAllHyp")
(ng #t)
(simp "NewATreeDef")
(ng #t)
(use "ExtHyp")
;; Case tas
(ind)
(ng #t)
(strip)
(use "Truth")
(assume "ta" "tas" "IHtas")
(ng #t)
(assume "HtBound" "ExtHyp")
(split)
(cases (pt "LargerARAll wqo a Root ta"))
;; Case 1.
(assume "LAllHyp")
(ng #t)
(use "IH")
(use "NatLeLtTrans" (pt "HtT ta max HtF tas"))
(use "NatMaxUB1")
(use "HtBound")
(use "ExtHyp")
;; Case 2
(assume "Useless")
(ng #t)
(use "ExtHyp")
(use "IH")
(use "NatLeLtTrans" (pt "HtT ta max HtF tas"))
(use "NatMaxUB2")
(use "HtBound")
(use "ExtHyp")
;; Proof finished.
(save "ExtAInsertAux")

;; ExtATInsertAT
(set-goal "all wqo,a,ta(ExtAT ta -> ExtAT(InsertAT wqo ta a))")
(assume "wqo" "a" "ta")
(use "ExtAInsertAux" (pt "Succ HtT ta"))
(use "Truth")
;; Proof finished.
(save "ExtATInsertAT")

;; ExtAFInsertAF
(set-goal "all wqo,a,tas(ExtAF tas -> ExtAF(InsertAF wqo tas a))")
(assume "wqo" "a" "tas")
(use "ExtAInsertAux" (pt "Succ HtF tas"))
(use "Truth")
;; Proof finished.
(save "ExtAFInsertAF")

;; ExtAFAppdLeft
(set-goal "all tas,sas(ExtAF(tas++sas) -> ExtAF tas)")
(ind)
(ng)
(strip)
(use "Truth")
(assume "ta" "tas" "IH")
(ng)
(assume "sas" "Conj")
(split)
(use "Conj")
(use "IH" (pt "sas"))
(use "Conj")
;; Proof finished.
(save "ExtAFAppdLeft")

;; ExtAFAppdRight
(set-goal "all tas,sas(ExtAF(tas++sas) -> ExtAF sas)")
(ind)
(ng)
(assume "sas" "ExtHyp")
(use "ExtHyp")
(assume "ta" "tas" "IH")
(ng)
(assume "sas" "Conj")
(use "IH")
(use "Conj")
;; Proof finished.
(save "ExtAFAppdRight")

;; CorrGoodWAux
(set-goal"all wqo,ws,n(
 all t(HtT t<n -> CorrT wqo ws t -> GLT wqo t -> GoodW wqo ws) &
 all ts(HtF ts<n -> CorrF wqo ws ts -> GLF wqo ts -> GoodW wqo ws))")
(assume "wqo" "ws")
;; Induction on n
(ind) 
;; Base
(split)
(ng)
(assume "t")
(use "Efq")
(ng)
(assume "ts")
(use "Efq")
;; Step
(assume "n" "IH")
(split)
;; Case t
(assume "t")
(simp "<-" "RootSubtreesId")
(assert "ex us us=lft Root t")
 (ex-intro "lft Root t")
 (use "Truth")
(assume "ex us us=lft Root t")
(by-assume "ex us us=lft Root t" "us" "usDef")
(assert "ex as as=rht Root t")
 (ex-intro "rht Root t")
 (use "Truth")
(assume "ex as as=rht Root t")
(by-assume "ex as as=rht Root t" "as" "asDef")
(assert "ex ts ts=Subtrees t")
 (ex-intro "Subtrees t")
 (use "Truth")
(assume "ex ts ts=Subtrees t")
(by-assume "ex ts ts=Subtrees t" "ts" "tsDef")
(ng #t)
(simp "<-" "usDef")
(simp "<-" "asDef")
(simp "<-" "tsDef")
(cases (pt "ts"))
;; Case Nil
(assume "tsNil")
(ng #t)
(simp "<-" "usDef")
(assert "ex vs vs=Lh as init us")
(ex-intro "Lh as init us")
 (use "Truth")
(assume "ex vs vs=Lh as init us")
(by-assume "ex vs vs=Lh as init us" "vs" "vsDef")
(simp "<-" "vsDef")
(assert "ex ws0 ws0=Lh as rest us")
 (ex-intro "Lh as rest us")
 (use "Truth")
(assume "ex ws0 ws0=Lh as rest us")
(by-assume "ex ws0 ws0=Lh as rest us" "ws0" "ws0Def")
(simp "<-" "ws0Def")
(assert "us=vs++ws0")
 (simp "vsDef")
 (simp "ws0Def")
 (simp "<-" "ListAppdInitRest")
 (use "Truth")
(assume "us=vs++ws0")
(simp "us=vs++ws0")
;; ?_68:0<n -> 
;;      Lh as<=Lh(vs++ws0)andb 
;;      0<Lh as andb Incr wqo as andb(as mapcons vs)++ws0 sub ws -> 
;;      GoodWR wqo(vs++ws0) -> GoodW wqo ws
(assume "0<n" "Conj" "GRvsws0")
(use "GoodWSub" (pt "(as mapcons vs)++ws0"))
(use "Conj")
;;   Conj:Lh as<=Lh(vs++ws0)andb Incr wqo as andb(as mapcons vs)++ws0 sub ws
;;   GRvsws0:GoodWR wqo(vs++ws0)
;; -----------------------------------------------------------------------------
;; ?_71:GoodW wqo((as mapcons vs)++ws0)
(use "GoodWAppdMapcons")
(use "Conj")
(assert "Lh as<=Lh us")
 (simp "us=vs++ws0")
 (use "Conj")
(assume "Lh as<=Lh us")
(simp "vsDef")
(simp "ListLhInit")
(use "Truth")
(use "Lh as<=Lh us")
(use "GoodWRToGoodW")
(use "GRvsws0")
;; ?_42:all t0,ts0(
;;       ts=(t0::ts0) -> 
;;       HtF(t0::ts0)<n -> 
;;       Lh as<=Lh us andb 
;;       0<Lh as andb 
;;       Incr wqo as andb 
;;       ESeq Root t Roots(t0::ts0) andb
;;       (as mapcons Lh as init us)++(Lh as rest us)sub ws andb 
;;       CorrF wqo ws(t0::ts0) -> 
;;       GLT wqo(Root t%t0::ts0) -> GoodW wqo ws)
(assume "t1" "ts1" "tsProp" "HtBound" "Conj" "GLTHyp")
(use-with "IH" 'right (pt "ts") "?" "?" "?")
(simp "tsProp")
(use "HtBound")
(simp "tsProp")
(use "Conj")
(simp "tsProp")
(ng "GLTHyp")
(use "GLTHyp")
;; Case ts
;; all ts(HtF ts<Succ n -> CorrF wqo ws ts -> GLF wqo ts -> GoodW wqo ws)
(cases)
(ng #t)
(assume "Useless1" "Useless2")
(use "Efq")
(assume "t" "ts")
(ng #t)
(assume "HtBound" "Conj")
(cases (pt "GLT wqo t"))
(assume "GLTt" "Useless")
(use "IH" (pt "t") 'left)
(use "NatLeLtTrans" (pt "HtT t max HtF ts"))
(use "NatMaxUB1")
(use "HtBound")
(use "Conj")
(use "GLTt")
(assume "Useless")
(use "IH")
(use "NatLeLtTrans" (pt "HtT t max HtF ts"))
(use "NatMaxUB2")
(use "HtBound")
(use "Conj")
;; Proof finished.
(save "CorrGoodWAux")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Main propositions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; BarWConsNil (Prop1)
(set-goal "allnc wqo,ws BarW wqo((Nil nat)::ws)")
(assume "wqo" "ws")
(use "GenBarW")
(assume "w")
(use "InitBarW")
(use "InitGoodW")
(use "InitLargerW")
(use "EmbRToEmb")
(ng)
(use "Truth")
;; Proof finished.
(save "BarWConsNil")

;; CorrFForest
(set-goal "all wqo,ws CorrF wqo ws(Forest wqo ws)")
(assume "wqo")
(ind)
(ng)
(use "Truth")
(cases)
(ng)
(assume "ws" "CorrFHyp")
(use "CorrFCons")
(use "CorrFHyp")
(assume "a" "v" "ws" "IHws")
(cases (pt "LargerAR wqo a(BSeq wqo Heads ws)"))
;; Case 1.
(assume "LHyp")
(simp "ForestConsInsertFDef")
;; CorrF wqo((a::v)::ws)(InsertF wqo(Forest wqo ws)v a)
(use "CorrFInsertF")
(use "IHws")
(use "LHyp")
(assume "NegLHyp")
(simp "ForestConsNewDef")
;; CorrF wqo((a::v)::ws)(NewTree((v::ws)pair a:)::Forest wqo ws)
(ng)
(use "CorrFCons")
(use "IHws")
(use "NegLHyp")
;; Proof finished.
(save "CorrFForest")

;; GoodWForestToGoodW (for Lemma 5.1i)
(set-goal  "all wqo,ws(GLF wqo(Forest wqo ws) -> GoodW wqo ws)")
(assume "wqo" "ws")
(use "CorrGoodWAux" (pt "Succ HtF(Forest wqo ws)"))
(use "Truth")
(use "CorrFForest")
;; Proof finished.
(save "GoodWForestToGoodW")

;; GoodWProjForestToGoodW
(set-goal  "all wqo,ws,i(
 i<Lh(Forest wqo ws) -> GLT wqo(i thof(Forest wqo ws)) -> GoodW wqo ws)")
(assume "wqo" "ws" "i" "LhHyp" "GLTHyp")
(use "GoodWForestToGoodW")
(use "ExGLTToGLF" (pt "i"))
(use "LhHyp")
(use "GLTHyp")
;; Proof finished.
(save "GoodWProjForestToGoodW")

;; Lemma 2.20(i) (~ BSeqHeadEqRhtsRootsForest (Lemma 5.1ii) in higwqo)
;; BSeqHeadsEqHeadsRhtsRootsForest
(set-goal "all wqo,ws(Adm ws ->
 BSeq wqo Heads ws=Heads Rhts Roots(Forest wqo ws))")
(assume "wqo")
(ind)
(ng)
(strip)
(use "Truth")
(cases)
(ng)
(assume "ws" "Useless")
(use "Efq")
(assume "a" "v" "ws" "IH" "AdmHyp")
(ng "AdmHyp")
;;   wqo  ws11135  v11142  a  v  ws  IH:
;;     Adm ws -> BSeq wqo Heads ws=Heads Rhts Roots(Forest wqo ws)
;;   AdmHyp:Adm ws
;; -----------------------------------------------------------------------------
;; ?_12:BSeq wqo Heads((a::v)::ws)=Heads Rhts Roots(Forest wqo((a::v)::ws))

;; (pp (nt (pt "BSeq wqo Heads((a::v)::ws)")))
;; [if (LargerAR wqo a(BSeq wqo Heads ws))
;;   (BSeq wqo Heads ws)
;;   (a::BSeq wqo Heads ws)]

(ng)
;;   wqo  ws11135  v11142  a  v  ws  IH:
;;     Adm ws -> BSeq wqo Heads ws=Heads Rhts Roots(Forest wqo ws)
;;   AdmHyp:Adm ws
;; -----------------------------------------------------------------------------
;; ?_13:[if (LargerAR wqo a(BSeq wqo Heads ws))
;;        (BSeq wqo Heads ws)
;;        (a::BSeq wqo Heads ws)]=
;;      Heads Rhts Roots[if (LargerAR wqo a(BSeq wqo Heads ws))
;;                        (InsertF wqo(Forest wqo ws)v a)
;;                        ((((v::ws)pair a:)%
;;                         (Nil lntree(list list nat yprod list nat)))::
;;                        Forest wqo ws)]

(cases (pt "(LargerAR wqo a(BSeq wqo Heads ws))"))
;; Case 1
(assume "LBSeqHyp")
(ng)
(simp "RootsInsert")
(use "IH")
(use "AdmHyp")
;; Case 2.
(assume "NegLBSeqHyp")
(ng)
(use "IH")
(use "AdmHyp")
;; Proof finished.
(save "BSeqHeadsEqHeadsRhtsRootsForest")

;; ESeqANilRhtsRootsForest
(set-goal "all wqo,ws ESeqA(Nil nat)Rhts Roots(Forest wqo ws)")
(assume "wqo")
(ind)
(ng)
(use "Truth")
(cases)
(ng)
(assume "ws" "Hyp")
(use "Hyp")
(assume "a0" "v" "ws" "IH")
(ng #t)
(cases (pt "LargerAR wqo a0(BSeq wqo Heads ws)"))
;; Case 1.
(assume "Useless")
(ng #t)
(simp "RootsInsert")
(use "IH")
;; Case 2.
(assume "Useless")
(ng #t)
(use "IH")
;; Proof finished.
(save "ESeqANilRhtsRootsForest")

;; CorrProjAux
(set-goal "all wqo,ws,n(
 all t(HtT t<n -> CorrT wqo ws t -> CorrAT wqo(ProjT t)) &
 all ts(HtF ts<n -> CorrF wqo ws ts -> CorrAF wqo(ProjF ts)))")
(assume "wqo" "ws")
(ind)
(ng)
(split)
(assume "t")
(use "Efq")
(assume "ts")
(use "Efq")
(assume "n" "IH")
(split)
;; Case t.
(assume "t")
(assert "ex vsas,ts t=(vsas%ts)")
 (ex-intro "Root t")
 (ex-intro "Subtrees t")
 (simp "RootSubtreesId")
 (use "Truth")
(assume "ExHyp")
(by-assume "ExHyp" "vsas" "vsasProp")
(by-assume "vsasProp" "ts" "vsastsProp")
(simp "vsastsProp")
(ng #t)
(assume "HtBound" "CorrHyp")
(split)
(use "CorrHyp")
(split)
(use "CorrHyp")
(split)
;;   HtBound:HtF ts<n
;;   CorrHyp:Lh rht vsas<=Lh lft vsas andb 
;;           Incr wqo rht vsas andb 
;;           ESeq vsas Roots ts andb
;;           (rht vsas mapcons Lh rht vsas init lft vsas)++
;;           (Lh rht vsas rest lft vsas)sub 
;;           ws andb 
;;           CorrF wqo ws ts
;; -----------------------------------------------------------------------------
;; ?_33:ESeqA rht vsas Roots(ProjF ts)
(use "ESeqToESeqAProj")
(use "CorrHyp")
(use "IH")
(use "HtBound")
(use "CorrHyp")
;; Case ts.
(ind)
(ng)
(strip)
(use "Truth")
(assume "t" "ts" "IHts")
(ng #t)
(assume "HtBound" "Conj")
(split)
(use "IH")
(use "NatLeLtTrans" (pt "HtT t max HtF ts"))
(use "NatMaxUB1")
(use "HtBound")
(use "Conj")
(use "IH")
(use "NatLeLtTrans" (pt "HtT t max HtF ts"))
(use "NatMaxUB2")
(use "HtBound")
(use "Conj")
;; Proof finished.
(save "CorrProjAux")

;; CorrFProj
(set-goal "all wqo,ws,ts(CorrF wqo ws ts -> CorrAF wqo(ProjF ts))")
(assume "wqo" "ws" "ts")
(use "CorrProjAux" (pt "Succ HtF ts"))
(use "Truth")
;; Proof finished.
(save "CorrFProj")

;; CorrTProj
(set-goal "all wqo,ws,t(CorrT wqo ws t -> CorrAT wqo(ProjT t))")
(assume "wqo" "ws" "t")
(use "CorrProjAux" (pt "Succ HtT t"))
(use "Truth")
;; Proof finished.
(save "CorrTProj")

;; Lemma 2.21(i) (~ BarFNil (Lemma 5.2i) in higwqo)
;; BarFNil
(set-goal "allnc wqo BarF wqo(Nil lntree(list list nat yprod list nat))")
(assume "wqo")
(use "GenBarF")
(ng)
(assume "tas" "a" "v" "tas=[]" "Useless")
(simp "tas=[]")
(ng)
(use "Efq")
;; Proof finished.
(save "BarFNil")

(define eterm (proof-to-extracted-term (theorem-name-to-proof "BarFNil")))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; CGenBarF([tas,a,v]CInitBarF)

;; Lemma 2.21(ii) (~ BarFAppdAux in higwqo)
;; BarFAppdAux
(set-goal "all wqo allnc ts(
 BarF wqo ts ->
 allnc ss(
 BarF wqo ss ->
 all m(m=Lh ss -> BarF wqo(ts++ss))))")
(assume "wqo" "ts" "BFts")
(elim "BFts")
(assume "ts1" "i" "iHyp" "GHyp" "ss" "BFss" "m" "mDef")
(use "InitBarF" (pt "i"))
(simp "LhAppd")
(use "NatLtLeTrans" (pt "Lh ts1"))
(use "iHyp")
(ng #t)
(use "Truth")
(simp "ListProjAppdLeft")
(use "GHyp")
(use "iHyp")
;; Step
(assume "ts1" "IHtFa" "IHtFb" "ss" "BFss")
(elim "BFss")
;; StepBase
(assume "ss1" "i" "iHyp" "GHyp" "m" "mDef")
(use "InitBarF" (pt "Lh ts1+i"))
(simp "LhAppd")
(use "NatLtMonPlus2")
(use "Truth")
(use "iHyp")
(simp "ListProjAppdRight")
(use "GHyp")
(use "iHyp")
;; StepStep
(assume "ss1" "IHssa" "IHssb" "m" "mDef")
(use "GenBarF")
(assume "ras" "a" "v")
(simp "ProjFAppd")
(assume "rasDef")
(assert "ex tas tas=(Lh ras--m)init ras")
 (ex-intro (pt "(Lh ras--m)init ras"))
 (use "Truth")
(assume "tasEx")
(by-assume "tasEx" "tas" "tasDef")
(assert "ex sas sas=(Lh ras--m)rest ras")
 (ex-intro (pt "(Lh ras--m)rest ras"))
 (use "Truth")
(assume "sasEx")
(by-assume "sasEx" "sas" "sasDef")
(simp "rasDef")
(simp "RootsAppd")
(assert "tas=ProjF ts1")
 (simp "tasDef")
 (simp "mDef")
 (simp "rasDef")
 (simp "LhAppd")
 (simp "LhProjF")
 (simp "LhProjF")
 (ng #t)
 (simp "<-" "LhProjF")
 (simp "ListInitAppd")
 (use "Truth")
(assume "tasProp")
(assert "sas=ProjF ss1")
 (simp "sasDef")
 (simp "mDef")
 (simp "rasDef")
 (simp "LhAppd")
 (simp "LhProjF")
 (simp "LhProjF")
 (ng #t)
 (simp "<-" "LhProjF")
 (simp "ListRestAppd")
 (use "Truth")
(assume "sasProp")
(simp "<-" "tasProp")
(simp "<-" "sasProp")
(assume "ExtAFras" "LargerARExAllras")
;; Cases on LargerARExAll wqo a Roots tas.  If so, then ts1 is changed.
(cases (pt "LargerARExAll wqo a Roots tas"))
;; Case 2.  ts1 changed.
(assume "LargerARExAlltas")
(simp "InsertFAppd")
(use "IHtFb" (pt "tas") (pt "m"))
(use "tasProp")
(use "ExtAFAppdLeft" (pt "sas"))
(use "ExtAFras")
(use "LargerARExAlltas")
;; Cases on whether ss1 changes
(cases (pt "LargerARExAll wqo a Roots sas"))
;; Case ss1 changes
(assume "LargerARExAllsas")
(use "IHssa" (pt "sas"))
(use "sasProp")
(use "ExtAFAppdRight" (pt "tas"))
(use "ExtAFras")
(use "LargerARExAllsas")
;; Case ss1 does not change
(assume "LargerARExAllsas -> F")
(simp "InsertFId")
(use "GenBarF")
(use "IHssa")
(simp "RootsProjF")
(simp "<-" "sasProp")
(use "LargerARExAllsas -> F")
(simp "LhInsertF")
(use "mDef")
;; Case 1.  ts1 does not change.
(assume "LargerARExAlltas -> F")
(simp "InsertFAppdRight")
(use "IHssb" (pt "sas") (pt "m"))
(use "sasProp")
(use "ExtAFAppdRight" (pt "tas"))
(use "ExtAFras")
(use "LargerARExAllAppdCases"
     (pt "wqo") (pt "a") (pt "Roots tas") (pt "Roots sas")
     "?" "?" "?")
(use "LargerARExAllras")
(assume "LargerARExAlltas")
(use "Efq")
(use-with "LargerARExAlltas -> F" "LargerARExAlltas")
(assume "LargerARExAllsas")
(use "LargerARExAllsas")
;; ?_99:m=Lh(InsertF wqo ss1 v a)
(simp "LhInsertF")
(use "mDef")
;; ?_96:LargerAR wqo a Heads Roots(ProjF ts1) -> F
(simp "RootsProjF")
(simp "<-" "tasProp")
(use "LargerARExAlltas -> F")
;; Proof finished.
(save "BarFAppdAux")

(define eterm
  (proof-to-extracted-term (theorem-name-to-proof "BarFAppdAux")))

;; (remove-var-name "g" "htat" "hat")
(add-var-name "g" (py "(list lntree list nat=>nat=>list nat=>treeF)"))
(add-var-name
 "htat" (py "(list lntree list nat=>nat=>list nat=>treeF=>nat=>treeF)"))
(add-var-name "hat" (py "(list lntree list nat=>nat=>list nat=>nat=>treeF)"))

(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [wqo,treeF]
;;  (Rec treeF=>treeF=>nat=>treeF)treeF([treeF0,a]CInitBarF)
;;  ([g,htat,treeF0]
;;    (Rec treeF=>nat=>treeF)treeF0([a]CInitBarF)
;;    ([g0,hat,a]
;;      CGenBarF
;;      ([tas,a0,v]
;;        [if (LargerARExAll wqo a0 Roots((Lh tas--a)init tas))
;;          (htat((Lh tas--a)init tas)a0 v
;;          [if (LargerARExAll wqo a0 Roots((Lh tas--a)rest tas))
;;            (g0((Lh tas--a)rest tas)a0 v)
;;            (CGenBarF g0)]
;;          a)
;;          (hat((Lh tas--a)rest tas)a0 v a)])))

;; Explanation.  The recursion operator on treeF with value type alpha
;; has type

(pp (term-to-type (pt "(Rec treeF=>alpha)")))

;; treeF=>alpha=>
;; ((list lntree list nat=>nat=>list nat=>treeF)=>
;;  (list lntree list nat=>nat=>list nat=>alpha)=>alpha)=>alpha

;; Let CInitBarF and CGenBarF be the constructors of treeF:

(display-alg "treeF")

;; CInitBarF:	treeF
;; CGenBarF:	(list lntree list nat=>nat=>list nat=>treeF)=>treeF

;; Then Phi := (Rec treeF=>alpha) is given by the recursion equations

;; Phi(CInitBarF) = G,
;; Phi(CGenBarF(g)) = H(g, lambda_v Phi(g(v)))

;; Here the value type of the first recursion is treeF=>nat=>treeF, and

;; G(treeF,a) = CInitBarF
;; H(g,htat,treeF0) = K(g, htat, treeF0)

;; with K(g, htat, treeF0) given by

;; (Rec treeF=>nat=>treeF)treeF0([a]CInitBarF)
;; ([g0,hat,a]
;;   CGenBarF
;;   ([tas,a0,v]
;;     [if (LargerARExAll wqo a0 Roots((Lh tas--a)init tas))
;;    (htat((Lh tas--a)init tas)a0 v
;;       [if (LargerARExAll wqo a0 Roots((Lh tas--a)rest tas))
;;         (g0((Lh tas--a)rest tas)a0 v)
;;         (CGenBarF g0)]
;;       a)
;;       (hat((Lh tas--a)rest tas)a0 v a)]))

;; The inner recursion is on treeF again, with value type nat=>treeF, and

;; G1(a) = CInitBarF
;; H1(g0, hat, a) = CGenBarF ...

;; BarFAppd (Lemma 5.2ii)
(set-goal "all wqo allnc t(BarF wqo(t:) ->
     allnc ss(BarF wqo ss -> all m(m=Lh ss -> BarF wqo(t::ss))))")
(assume "wqo" "t" "BFts" "ss" "BFss" "m" "mDef")
(assert "(t::ss)=t: ++ss")
 (ng)
 (use "Truth")
(assume "(t::ss)=t: ++ss")
(simp "(t::ss)=t: ++ss")
(use "BarFAppdAux" (pt "m"))
(use "BFts")
(use "BFss")
(use "mDef")
;; Proof finished.
(save "BarFAppd")

(animate "BarFAppdAux")
(define eterm (proof-to-extracted-term (theorem-name-to-proof "BarFAppd")))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [wqo,treeF]
;;  (Rec treeF=>treeF=>nat=>treeF)treeF([treeF0,a]CInitBarF)
;;  ([g,htat,treeF0]
;;    (Rec treeF=>nat=>treeF)treeF0([a]CInitBarF)
;;    ([g0,hat,a]
;;      CGenBarF
;;      ([tas,a0,v]
;;        [if (LargerARExAll wqo a0 Roots((Lh tas--a)init tas))
;;          (htat((Lh tas--a)init tas)a0 v
;;          [if (LargerARExAll wqo a0 Roots((Lh tas--a)rest tas))
;;            (g0((Lh tas--a)rest tas)a0 v)
;;            (CGenBarF g0)]
;;          a)
;;          (hat((Lh tas--a)rest tas)a0 v a)])))

;; Lemma 2.22 (~ BarFNew (Lemma 5.3) in higwqo)
;; BarFNew
(set-goal "all wqo(BarA wqo(Nil nat) ->
  allnc ws(BarW wqo ws -> 
  all as BarF wqo((NewTree(ws pair as)):)))")
(assume "wqo" "BarANil" "ws0" "Bws0")
;; Ind(BarW)
(elim "Bws0")
;; 1.1
(assume "vs" "Gvs" "as0")
(use "InitBarF" (pt "0"))
(use "Truth")
(ng)
(simp "NewTreeDef")
(ng)
(use "GoodWToGoodWR")
(use "Gvs")
;; 1.2
(assume "ws" "BHyp" "IH1" "as0")
;;   IH1:all v,as BarF wqo((NewTree((v::ws)pair as)):)
;;   as0
;; -----------------------------------------------------------------------------
;; ?_12:BarF wqo((NewTree(ws pair as0)):)

;; We show more generally
(assert "allnc as(
 BarA wqo as -> 
 (GoodAR wqo as -> F) -> 
 allnc ts(
  BarF wqo ts -> 
  as=Heads Rhts Roots ts -> BarF wqo(((ws pair as0)%ts):)))")
(assume "as" "Bas")
(elim "Bas")
;; 2.1
(assume "as1" "GHyp" "NGHyp")
(use "Efq")
(use-with "NGHyp" "GHyp")
;; 2.2
(assume "as1" "IH2a" "IH2b" "Bas1" "ts" "BSts")
;; Ind(BarF)
(elim "BSts")
;; 3.1
(assume "ts1" "i" "i<Lh ts1" "GHyp" "as1Def")
(use "InitBarF" (pt "0"))
(use "Truth")
(ng #t)
(use "GenIndGLT")
(use "ExGLTToGLF" (pt "i"))
(use "i<Lh ts1")
(use "GHyp")
;; 3.2
(assume "ts1" "IH3a" "IH3b" "as1Def")
(use "GenBarF")
(assume "tas" "a" "v" "tasDef")
(ng "tasDef")
;; ?_33:ExtAF tas -> 
;;      LargerARExAll wqo a Roots tas -> 
;;      BarF wqo(InsertF wqo((ws pair as0)%ts1):v a)
(simp "tasDef")
(assume "ExtAFtasHyp")
(ng "ExtAFtasHyp")
(assume "LAllHyp")
(ng "LAllHyp")
(simp "InsertFEqInsertT")
;; ?_39:BarF wqo((InsertT wqo((ws pair as0)%ts1)v a):)
(assert "as1=Heads Roots Subtrees Head tas")
 (simp "as1Def")
 (simp "tasDef")
 (ng #t)
 (simp "RootsProjF")
 (use "Truth")
(assume "as1Char")
;; Now case distinction on the definition of InsertT, avoiding ts1, as1
(cases (pt "LargerARExAll wqo a Roots Subtrees Head tas"))
;; Case 1.
(assume "LExAllHyp")
(assert "all vsas,ts,v,a(LargerARExAll wqo a Rhts Roots ts ->
 InsertT wqo(vsas%ts)v a=(vsas%InsertF wqo ts v a))")
 (assume "vsas" "ts2" "v2" "a2" "LHyp")
 (ng #t)
 (simp "LHyp")
 (ng #t)
 (use "Truth")
(assume "Assertion")
(simp "Assertion")
(drop "Assertion")
(use "IH3b" (pt "Subtrees Head tas"))
(simp "tasDef")
(use "Truth")
(assert "ProjF ts1=Subtrees Head tas")
 (simp "tasDef")
 (use "Truth")
(assume "ProjF ts1=Subtrees Head tas")
(simp "<-" "ProjF ts1=Subtrees Head tas")
(use "ExtAFtasHyp")
(use "LExAllHyp")
;; ?_64:as1=Heads Rhts Roots(InsertF wqo ts1 v a)
(simp "RootsInsert")
(simp "as1Def")
(use "Truth")
;; ?_59:LargerARExAll wqo a Rhts Roots ts1
(drop "Assertion")
(simp "RootsProjF")
(assert "ProjF ts1=Subtrees Head tas")
 (simp "tasDef")
 (use "Truth")
(assume "ProjF ts1=Subtrees Head tas")
(simp "ProjF ts1=Subtrees Head tas")
(use "LExAllHyp")
;; Case 2.
;; ?_49:(LargerARExAll wqo a Roots Subtrees Head tas -> F) -> 
;;      BarF wqo((InsertT wqo((ws pair as0)%ts1)v a):)
(ng #t)
(assert "Rhts Roots ts1=Roots Subtrees Head tas")
 (simp "tasDef")
 (ng #t)
 (simp "RootsProjF")
 (use "Truth")
(assume "Rhts Roots ts1=Roots Subtrees Head tas")
(simp "Rhts Roots ts1=Roots Subtrees Head tas")
(drop "Rhts Roots ts1=Roots Subtrees Head tas")
(assume "NegLExAllHyp")
(simp "NegLExAllHyp")
(ng #t)
(use "IH2b" (pt "a"))
(assume "Gaas1")
(use "NegLExAllHyp")
;;   ExtHyp:ExtAF(ProjF ts1)
;;   as1Def:as1=Heads Rhts Roots ts1
;;   tas  a  v  tasDef:tas=(as0%ProjF ts1):
;;   LAllHyp:LargerARAll wqo a as0
;;   as1Char:as1=Heads Roots Subtrees Head tas
;;   NegLExAllHyp:LargerARExAll wqo a Roots Subtrees Head tas -> F
;;   Gaas1:GoodAR wqo(a::as1)
;; -----------------------------------------------------------------------------
;; ?_96:LargerARExAll wqo a Roots Subtrees Head tas
(simp "tasDef")
(ng #t)
(use "LargerARExAllIntro" (pt "as0"))
(use "ExtAFtasHyp")
(assert "Heads Roots(ProjF ts1)=as1")
 (simp "as1Def")
 (simp "RootsProjF")
 (use "Truth")
(assume "Heads Roots(ProjF ts1)=as1")
(simp "Heads Roots(ProjF ts1)=as1")
(drop "Heads Roots(ProjF ts1)=as1")
(use "GoodARConsBad")
(use "Gaas1")
(use "Bas1")
(use "LAllHyp")
;; ?_93:BarF wqo(NewTree((v::ws)pair a::as0)::ts1)
;; Use BarFAppd
(assert "BarF wqo ts1")
 (use "GenBarF")
 (use "IH3a")
(assume "BarF wqo ts1")
(assert "BarF wqo((NewTree((v::ws)pair a::as0)):)")
 (use "IH1")
(assume "BarF wqo((NewTree((v::ws)pair a::as0)):)")
;; Now we can use BarFAppd
(use "BarFAppd" (pt "Lh Subtrees Head tas"))
(use "BarF wqo((NewTree((v::ws)pair a::as0)):)")
(drop "BarF wqo((NewTree((v::ws)pair a::as0)):)")
(use "BarF wqo ts1")
;; ?_120:Lh Subtrees Head tas=Lh ts1
(simp "tasDef")
(ng #t)
(use "LhProjF")
(ng #t)
(simp "NewTreeDef")
(ng #t)
(use "as1Def")
;; ?_40:LargerARAll wqo a rht Root((ws pair as0)%ts1)
(ng #t)
(use "LAllHyp")
;; Now the assertion above is proved
(assume "Assertion")
(simp "NewTreeDef")
(use "Assertion" (pt "(Nil nat)"))
(use "BarANil")
(ng #t)
(assume "Absurd")
(use "Absurd")
(use "BarFNil")
(ng #t)
(use "Truth")
;; Proof finished.
(save "BarFNew")

(define eterm (proof-to-extracted-term (theorem-name-to-proof "BarFNew")))
(animate "BarFNil")

;; (display-default-varnames)

;; hat: 	list lntree list nat=>nat=>list nat=>nat=>treeF
;; htat: 	list lntree list nat=>nat=>list nat=>treeF=>nat=>treeF
;; g: 	list lntree list nat=>nat=>list nat=>treeF
;; tas: 	list lntree list nat
;; ta: 	lntree list nat
;; vsass: 	list(list list nat yprod list nat)
;; vsas: 	list list nat yprod list nat
;; ts: 	list lntree(list list nat yprod list nat)
;; t: 	lntree(list list nat yprod list nat)
;; txs: 	list lntree alpha
;; tx: 	lntree alpha
;; x: 	alpha
;; wqo: 	nat=>nat=>boole
;; wss: 	list list list nat
;; ws: 	list list nat
;; v: 	list nat
;; a: 	nat

(add-var-name "gw" (py "(list nat=>treeW)"))
(add-var-name "hw" (py "list nat=>list nat=>treeF"))
(add-var-name "ga" (py "nat=>treeA")) 
(add-var-name "hatt" (py "nat=>treeF=>treeF"))

(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [wqo,treeA,treeW]
;;  (Rec treeW=>list nat=>treeF)treeW([v]CInitBarF)
;;  ([gw,hw,v]
;;    (Rec treeA=>treeF=>treeF)treeA([treeF]CInitBarF)
;;    ([ga,hatt,treeF]
;;      (Rec treeF=>treeF)treeF CInitBarF
;;      ([g,g0]
;;        CGenBarF
;;        ([tas,a,v0]
;;          [if (LargerARExAll wqo a Roots Subtrees Head tas)
;;            (g0 Subtrees Head tas a v0)
;;            (hatt a
;;            (cBarFAppd wqo(hw v0(a::v))
;; 		      (CGenBarF g)Lh Subtrees Head tas))])))
;;    (CGenBarF([tas,a,v0]CInitBarF)))

;; This time we have three nested recursions: an outer one
;; on treeW with value type list nat=>treeF, then
;; on treeA with value type treeF=>treeF, and innermost
;; on treeF with value type treeF.
;; This corresponds to the elimination axioms used in the proof.  

;; Notice that the computational content cBarFAppd of the theorem
;; BarFAppd appears as a constant inside the present neterm.

;; Satz 2.23 (~ HigmanAux (Lemma 5.4) in higwqo)
(set-goal "all wqo(BarA wqo(Nil nat) ->
  allnc as(BarA wqo as ->
  allnc ts(BarF wqo ts -> 
  all ws(Adm ws -> BSeq wqo Heads ws=as ->
  all tas(tas=ProjF ts -> ExtAF tas ->
  Forest wqo ws=ts -> BarW wqo ws)))))")
(assume "wqo" "BarANil" "as0" "Bas0")
(elim "Bas0")

;; 1.1
(assume "as" "Gas" "ts" "Bts" "ws" "Adm ws" "BHws=as" "tas" "tasDef" "ExtHyp")
(use "Efq")
;;   wqo  BarANil:BarA wqo(Nil nat)
;;   {as0}  Bas0:BarA wqo as0
;;   {as}  Gas:GoodAR wqo as
;;   {ts}  Bts:BarF wqo ts
;;   ws  Adm ws:Adm ws
;;   BHws=as:BSeq wqo Heads ws=as
;;   tas  tasDef:tas=ProjF ts
;; -----------------------------------------------------------------------------
;; ?_6:F

(use "NotGoodARBSeq" (pt "wqo") (pt "Heads ws"))
(simp "BHws=as")
(use "Gas")

;; 1.2
(assume "as" "IH1a" "IH1b" "ts0" "Bts0")
(drop "IH1a")

;;   {ts0}  Bts0:BarF wqo ts0
;; -----------------------------------------------------------------------------
;; ?_10:all ws(
;;      Adm ws -> 
;;      BSeq wqo Heads ws=as -> 
;;      all tas(tas=ProjF ts0 -> Forest wqo ws=ts0 -> BarW wqo ws))

;; Ind(BarF)
(elim "Bts0")

;; 2.1
(assume "ts" "i" "i<Lts" "GHyp"
	"ws" "Adm ws" "BHws=as" "tas" "tasDef" "ExtHyp" "Fws=ts")
(use "InitBarW")
(use "GoodWProjForestToGoodW" (pt "i"))
(simp "Fws=ts")
(use "i<Lts")
(simp "Fws=ts")
(use "GHyp")
;; 2.2
(assume "ts" "IH2a" "IH2b"
	"ws" "Adm ws" "BHws=as" "tas" "tasDef" "ExtHyp" "Fws=ts")
(use "GenBarW")

;; Ind(v)
(ind)

;; 3.1
(use "BarWConsNil")

;; 3.2
(assume "a" "v" "IH3")

;; BarW((a::v)::ws)

;; (cases (pt "LargerAR wqo a as"))
;; Warning: nc-intro with cvar(s) as

(cases (pt "LargerAR wqo a(BSeq wqo Heads ws)"))
;; Case 1.
(simp "BSeqHeadsEqHeadsRhtsRootsForest")
(assume "LHyp")
(use "IH2b" (pt "tas") (pt "a") (pt "v")  (pt "InsertAF wqo tas a"))
(use "tasDef")
(use "ExtHyp")
;;   tas  tasDef:tas=ProjF ts
;;   ExtHyp:ExtAF tas
;;   Fws=ts:Forest wqo ws=ts
;;   v20694  a  v  IH3:BarW wqo(v::ws)
;;   LHyp:LargerAR wqo a Heads Rhts Roots(Forest wqo ws)
;; -----------------------------------------------------------------------------
;; ?_31:LargerARExAll wqo a Roots tas

(simp "tasDef")
(use "LargerARExAllIntro" (pt "(Nil nat)"))
(simp "<-" "RootsProjF")
(simp "<-" "Fws=ts")
(use "ESeqANilRhtsRootsForest")
;; ?_39:LargerAR wqo a Heads Roots(ProjF ts)
(simp "<-" "RootsProjF")
(simp "<-" "Fws=ts")
(use "LHyp")
;; ?_40:LargerARAll wqo a(Nil nat)
(ng #t)
(use "Truth")
;; ?_32:Adm((a::v)::ws)
(ng #t)
(use "Adm ws")
;; ?_33:BSeq wqo Heads((a::v)::ws)=as
(ng #t)
(assert "LargerAR wqo a(BSeq wqo Heads ws)")
 (simp "BSeqHeadsEqHeadsRhtsRootsForest")
 (use "LHyp")
 (use "Adm ws")
(assume "LargerAR wqo a(BSeq wqo Heads ws)")
(simp "LargerAR wqo a(BSeq wqo Heads ws)")
(drop "LargerAR wqo a(BSeq wqo Heads ws)")
(ng #t)
(use  "BHws=as")
;; ?_34:InsertAF wqo tas a=ProjF(InsertF wqo ts v a)
(simp "tasDef")
(use "InsertAFProjFEqProjFInsertF")
;; ?_35:ExtAF(InsertAF wqo tas a)
(use "ExtAFInsertAF")
(use "ExtHyp")
;; ?_36:Forest wqo((a::v)::ws)=InsertF wqo ts v a
(ng #t)
(assert "LargerAR wqo a(BSeq wqo Heads ws)")
 (simp "BSeqHeadsEqHeadsRhtsRootsForest")
 (use "LHyp")
 (use "Adm ws")
(assume "LargerAR wqo a(BSeq wqo Heads ws)")
(simp "LargerAR wqo a(BSeq wqo Heads ws)")
(drop "LargerAR wqo a(BSeq wqo Heads ws)")
(ng #t)
(simp "Fws=ts")
(use "Truth")
(use "Adm ws")
;; ?_25:(LargerAR wqo a(BSeq wqo Heads ws) -> F) -> BarW wqo((a::v)::ws)
;; Case 2.
(assume "NegLHyp")
(assert "BarF wqo ts")
(use "GenBarF")
(use "IH2a")
(assume "BarF wqo ts")
(use "IH1b" (pt "a") (pt "NewTree((v::ws)pair a:)::ts")
     (pt "(NewATree a:)::tas"))
(use "BarFAppd" (pt "Lh tas"))
(use "BarFNew")
(use "BarANil")
(use "IH3")
(use "BarF wqo ts")
;; Lh tas=Lh ts
(simp "tasDef")
(use "LhProjF")
(ng #t)
(use "Adm ws")
;; BSeq wqo Heads((a::v)::ws)=(a::as)
(ng #t)
(simp "NegLHyp")
(ng #t)
(use "BHws=as")
;; (NewATree a: ::tas)=ProjF(NewTree((v::ws)pair a:)::ts)
(simp "tasDef")
(ng #t)
(use "Truth")
;; ?_77:ExtAF(NewATree a: ::tas)
(ng #t)
(use "ExtHyp")
;; Forest wqo((a::v)::ws)=(NewTree((v::ws)pair a:)::ts)
(ng #t)
(simp "NegLHyp")
(ng #t)
(use "Fws=ts")
;; Proof finished.
(save "HigmanAux")

(define eterm (proof-to-extracted-term (theorem-name-to-proof "HigmanAux")))
(animate "BarWConsNil")

(add-var-name
 "ha" (py "(nat=>treeF=>list list nat=>list lntree list nat=>treeW)"))

(add-var-name
 "h" (py "(list lntree list nat=>
           nat=>list nat=>list list nat=>list lntree list nat=>treeW)"))

(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [wqo,treeA,treeA0]
;;  (Rec treeA=>treeF=>list list nat=>list lntree list nat=>treeW)treeA0
;;  ([treeF,ws,tas]CInitBarW)
;;  ([ga,ha,treeF]
;;    (Rec treeF=>list list nat=>list lntree list nat=>treeW)treeF
;;    ([ws,tas]CInitBarW)
;;    ([g,h,ws,tas]
;;      CGenBarW
;;      ([v]
;;        (Rec list nat=>treeW)v(CGenBarW([v0]CInitBarW))
;;        ([a,v0,treeW]
;;          [if (LargerAR wqo a(BSeq wqo Heads ws))
;;            (h tas a v0((a::v0)::ws)(InsertAF wqo tas a))
;;            (ha a
;;            (cBarFAppd wqo(cBarFNew wqo treeA treeW a:)(CGenBarF g)Lh tas)
;;            ((a::v0)::ws)
;;            ((a: %(Nil lntree list nat))::tas))]))))

;; Again we have tree nested recursions, on treeA, then treeF and
;; innermost on list nat.  This corresponds to the elimination axioms
;; used in the proof.  Notice again that the computational content
;; cBarFAppd, cBarFNew of the theorems BarFAppd, BarFNew appear as
;; constants inside the present neterm.

;; Higmans Lemma (~ Higman in higwqo)
;; Higman
(set-goal "all wqo(BarA wqo(Nil nat) -> BarW wqo(Nil list nat))")
(assume "wqo" "BarANil")
(use "HigmanAux"
     (pt "(Nil nat)")
     (pt "(Nil lntree(list list nat yprod list nat))")
     (pt "(Nil lntree list nat)"))
(use "BarANil")
(use "BarANil")
(use "BarFNil")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
;; Proof finished.
(save "Higman")

(define eterm (proof-to-extracted-term (theorem-name-to-proof "Higman")))
(animate "HigmanAux")

(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [wqo,treeA]
;;  (Rec treeA=>treeF=>list list nat=>list lntree list nat=>treeW)
;;  treeA
;;  ([treeF,ws,tas]CInitBarW)
;;  ([ga,ha,treeF]
;;    (Rec treeF=>list list nat=>list lntree list nat=>treeW)treeF
;;    ([ws,tas]CInitBarW)
;;    ([g,h,ws,tas]
;;     CGenBarW
;;     ([v](Rec list nat=>treeW)v(CGenBarW([v0]CInitBarW))
;;      ([a,v0,treeW]
;;       [if (LargerAR wqo a(BSeq wqo Heads ws))
;; 	  (h tas a v0((a::v0)::ws)(InsertAF wqo tas a))
;; 	  (ha a (cBarFAppd wqo(cBarFNew wqo treeA treeW a:)
;; 			   (CGenBarF g)Lh tas)
;; 	      ((a::v0)::ws)
;; 	      ((a: %(Nil lntree list nat))::tas))]))))
;;  (CGenBarF([tas,a,v]CInitBarF))
;;  (Nil list nat)
;;  (Nil lntree list nat)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Experiments
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; We are interested getting a program that for any sequence of words
;; yields witnesses that this sequence is good.  To this end we prove
;; that BarW Nil implies that every infinite sequence of words has a good
;; initial segment.

(add-var-name "f" (py "nat=>list nat"))

;; BarWToGoodInit
(set-goal "allnc wqo,ws(BarW wqo ws -> all f,n(Rev(f fbar n)=ws ->
 ex m GoodW wqo(Rev(f fbar m))))")
(assume "wqo" "vs" "Bvs")

;; Ind(BarW)
(elim "Bvs")

;; 1.  GoodW ws
(assume "ws" "Gws" "f" "n" "Ifnws")
(ex-intro "n")
(simp "Ifnws")
(use "Gws")

;; 2.  all w BarW(w::ws)
(assume "ws" "all w BarW(w::ws)" "IH" "f" "n" "Ifnws")
(use-with "IH" (pt "f n") (pt "f") (pt "Succ n") "?")

;; Rev(f fbar Succ n)=(f n::ws)
(simp "<-" "Ifnws")
(simp "ListRevFBarSucc")
(use "Truth")
;; Proof finished.
(save "BarWToGoodInit")

(define eterm
  (proof-to-extracted-term (theorem-name-to-proof "BarWToGoodInit")))
(add-var-name "hwfa" (py "list nat=>(nat=>list nat)=>nat=>nat"))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [treeW]
;;  (Rec treeW=>(nat=>list nat)=>nat=>nat)treeW([f,a]a)
;;  ([gw,hwfa,f,a]hwfa(f a)f(Succ a))

;; The recursion operator on treeW with value type alpha has type

(pp (term-to-type (pt "(Rec treeW=>alpha)")))
;; treeW=>alpha=>((list nat=>treeW)=>(list nat=>alpha)=>alpha)=>alpha

;; Let Leaf: treeW and Branch: (list nat=>treeW)=>treeW be the
;; constructors of treeW.  Then Phi := (Rec treeW=>alpha) is given by
;; the recursion equations

;; Phi(Leaf) = G,
;; Phi(Branch(g)) = H(g, lambda_v Phi(g(v)))

;; Here the value type alpha is (nat=>list nat)=>nat=>nat, and

;; G = lambda_f,a a
;; H(gw,hwfa) = lambda_f,a hwfa(f(a), f, a+1)

;; Let wqo be NatLe.  We need some additional lemmas on LargerAR GoodAR
;; and BarA.

;; LargerARAppdLeft
(set-goal "all wqo,a,as,bs(LargerAR wqo a as -> LargerAR wqo a(as++bs))")
(assume "wqo" "b")
(ind)
(ng)
(assume "bs")
(use "Efq")
(assume "a" "as" "IHas" "bs")
(ng)
(cases (pt "wqo a b"))
(strip)
(use "Truth")
(assume "Useless")
(ng)
(use "IHas")
;; Proof finished.
(save "LargerARAppdLeft")

;; GoodARAppdRight
(set-goal "all wqo,as,bs(GoodAR wqo bs -> GoodAR wqo(as++bs))")
(assume "wqo")
(ind)
(ng)
(assume "bs" "Gbs")
(use "Gbs")
(assume "a" "as" "IHas" "bs" "Gbs")
(ng)
(cases (pt "(LargerAR wqo a(as++bs))"))
(assume "Useless")
(use "Truth")
(assume "Useless")
(ng)
(use "IHas")
(use "Gbs")
;; Proof finished.
(save "GoodARAppdRight")

;; GoodARElim
(set-goal "all wqo,a,as(
 GoodAR wqo(a::as) -> 
 (GoodAR wqo as -> Pvar^) -> (LargerAR wqo a as -> Pvar^) -> Pvar^)")
(assume "wqo" "a" "as")
(ng)
(cases (pt "LargerAR wqo a as"))
(assume "Laas" "Useless1" "Useless2" "Hyp")
(use "Hyp")
(use "Truth")
(assume "NotLaas" "Gas" "Hyp" "Useless")
(use "Hyp")
(use "Gas")
;; Proof finished.
(save "GoodARElim")

;; InitGoodAR
(set-goal "all wqo,a,as(LargerAR wqo a as -> GoodAR wqo(a::as))")
(assume "wqo" "a" "as" "Laas")
(ng)
(simp "Laas")
(use "Truth")
;; Proof finished.
(save "InitGoodAR")

;; GenGoodAR
(set-goal "all wqo,a,as(GoodAR wqo as -> GoodAR wqo(a::as))")
(assume "wqo" "a" "as" "Gas")
(ng)
(simp "Gas")
(use "Truth")
;; Proof finished.
(save "GenGoodAR")

;; GoodARAppdLeft
(set-goal "all wqo,as,bs(GoodAR wqo as -> GoodAR wqo(as++bs))")
(assume "wqo")
(ind)
(ng)
(assume "bs")
(use "Efq")
(assume "a" "as" "IHas" "bs" "Gaas")
(assert "(a::as)++bs=(a::as++bs)")
 (use "Truth")
(assume "(a::as)++bs=(a::as++bs)")
(simp "(a::as)++bs=(a::as++bs)")
(use "GoodARElim" (pt "wqo") (pt "a") (pt "as"))
(use "Gaas")
(assume "Gas")
(use "GenGoodAR")
(use "IHas")
(use "Gas")
(assume "Laas")
(use "InitGoodAR")
(use "LargerARAppdLeft")
(use "Laas")
;; Proof finished.
(save "GoodARAppdLeft")

;; For GoodANatLeAppdOne we need ZeroLtLhToMainLastId.

;; (pp "ZeroLtLhToMainLastId")
;; "all xs(0<Lh xs -> Main xs++(Last xs):eqd xs)"")

;; We do cases on Last as<n.  If Last as<n, then Last as<=m since n<=m+1.
;; By IHm for Last as and Main as we have GoodAR NatLe(Main as++(Last as):)
;; hence GoodAR NatLe as.  By GoodARAppdLeft we have GoodAR NatLe(as++n:)
;; If Last as>=n, then GoodAR NatLe(First as++(Last as): ++ n:) and hence
;; by GoodARAppdRight we have GoodAR NatLe(as++n:)

;; GoodANatLeAppdOne
(set-goal "all m,n,as(n<=m -> Lh as=Succ m -> GoodAR NatLe(as++n:))")
(ind)
;; Base
(ng)
(assume "n" "as" "n=0")
(simp "n=0")
(cases (pt "as"))
(ng)
(assume "Useless" "Absurd")
(use "Absurd")
(assume "a")
(cases)
(strip)
(use "Truth")
(assume "b" "bs" "Useless" "Absurd")
(use "Efq")
(use "Absurd")
;; Step
(assume "m" "IHm" "n" "as" "n<=m+1" "Lh as=m+2")
(assert "Main as++(Last as): eqd as")
 (use "ZeroLtLhToMainLastId")
 (simp "Lh as=m+2")
 (use "Truth")
(assume "Main as++(Last as): eqd as")
(simp "<-" "Main as++(Last as): eqd as")
(cases (pt "n<=Last as"))
(assume "n<=Last as")
(ng #t)
(use "GoodARAppdRight")
(ng #t)
(use "n<=Last as")
(assume "n<=Last as -> F")
(assert "Last as<n")
 (use "NatNotLeToLt")
 (use "n<=Last as -> F")
(assume "Last as<n")
(assert "GoodAR NatLe(Main as++(Last as):)")
 (use "IHm")
 (use "NatLtSuccToLe")
 (use "NatLtLeTrans" (pt "n"))
 (use "Last as<n")
 (use "n<=m+1")
 (cut "Lh(Main as++(Last as):)=Succ(Succ m)")
  (ng #t)
  (assume "Hyp")
  (use "Hyp")
 (simp "ZeroLtLhToMainLastId")
 (use "Lh as=m+2")
 (simp "Lh as=m+2")
 (use "Truth")
(assume "Assertion")
(use "GoodARAppdLeft")
(use "Assertion")
;; Proof finished.
(save "GoodANatLeAppdOne")

;; BarNatLeAppdOne
(set-goal "all i,m,as(i+Lh as=Succ m -> BarA NatLe(as++m:))")
(ind)
(assume "m" "as" "LhBound")
(use "InitBarA")
(use "GoodANatLeAppdOne" (pt "m"))
(use "Truth")
(use "LhBound")
;; Step
(assume "i" "IHi")
(assume "m" "as" "i+Lh as=m")
(use "GenBarA")
(assume "a")
(assert "(a::as++m:)=(a::as)++m:")
 (use "Truth")
(assume "Assertion")
(simp "Assertion")
(use "IHi")
(ng #t)
(use "i+Lh as=m")
;; Proof finished.
(save "BarNatLeAppdOne")

;; BarANilNatLe
(set-goal "BarA NatLe(Nil nat)")
(use "GenBarA")
(assume "m")
(assert "m: =(Nil nat)++m:")
 (use "Truth")
(assume "m: =(Nil nat)++m:")
(simp "m: =(Nil nat)++m:")
(use "BarNatLeAppdOne" (pt "Succ m"))
(use "Truth")
;; Proof finished.
(save "BarANilNatLe")

;; HigmanNatLe
(set-goal "BarW NatLe(Nil list nat)")
(use "Higman")
(use "BarANilNatLe")
;; Proof finished.
(save "HigmanNatLe")

;; GoodWInitNatLe
(set-goal "all f ex n GoodW NatLe(Rev(f fbar n))")
(assume "f")
(use "BarWToGoodInit" (pt "(Nil list nat)") (pt "0"))
(use "HigmanNatLe")
(use "Truth")
;; Proof finished.
(save "GoodWInitNatLe")

(define eterm
  (proof-to-extracted-term (theorem-name-to-proof "GoodWInitNatLe")))
(animate "BarWToGoodInit")
(animate "HigmanNatLe")
(animate "Higman")
(animate "BarANilNatLe")
(animate "BarNatLeAppdOne")
(animate "BarFAppd")
(animate "BarFNew")

(define neterm (rename-variables (nt eterm)))
;; (pp (nt neterm))
(pp (term-to-type neterm))
;; (nat=>list nat)=>nat

(define (run-higman infseq) (pp (nt (mk-term-in-app-form neterm infseq))))

;; a.  [0 0], [1 1 0], [0 1 0 1], [0], [0], ...
(add-program-constant "SeqOne" (py "nat=>list nat") t-deg-zero)
(add-computation-rules
 "SeqOne 0" "0::0:"
 "SeqOne 1" "1::1::0:"
 "SeqOne 2" "0::1::0::1:"
 "SeqOne(Succ(Succ(Succ n)))" "0:")
(run-higman (pt "SeqOne"))
;; 2

;; b.  [0 0], [1], [1 0], [], [], ...
(add-program-constant "SeqTwo" (py "nat=>list nat") t-deg-zero)
(add-computation-rules
 "SeqTwo 0" "0::0:"
 "SeqTwo 1" "1::1::0:"
 "SeqTwo 2" "0::1::0::1:"
 "SeqTwo(Succ(Succ(Succ n)))" "(Nil nat)")
(run-higman (pt "SeqTwo"))
;; 2

(add-program-constant "Seq" (py "nat=>list nat"))
(add-computation-rules
 "Seq 0" "5::2:"
 "Seq 1" "2::8:"
 "Seq 2" "4::2::1:"
 "Seq 3" "6::9:"
 "Seq 4" "3::5:"
 "Seq(Succ(Succ(Succ(Succ(Succ n)))))" "0:")
(pp (nt (mk-term-in-app-form neterm (pt "Seq"))))
;; 4

;; We aim at a more systematic example generation

(define (seqterm-and-term-to-shifted-seqterm seqterm term)
  (let* ((var (type-to-new-var (py "nat"))))
    (make-term-in-abst-form
     var (make-term-in-if-form
	  (make-=-term (make-term-in-var-form var)
		       (make-numeric-term 0))
	  (list term
		(make-term-in-app-form
		 seqterm (make-term-in-app-form
			  (pt "Pred")
			  (make-term-in-var-form var))))))))

(pp (nt (seqterm-and-term-to-shifted-seqterm (pt "[n](Nil nat)") (pt "2:"))))
;; [a0][if (a0=0) 2: (Nil nat)]

;; Here we should have (2:).  Probably after the next make (with the
;; new token-tree-tag-to-precedence) this will be ok.

;; (pp (pt "[a0][if (a0=0) 2: (Nil nat)]"))

;; PARSE ERROR : unexpected token
;; postfix-op 

;; [a0][if (a0=0) 2: (Nil nat)]

(pp (nt (seqterm-and-term-to-shifted-seqterm (pt "[n](Nil nat)") (pt "3::2:"))))
;; [a0][if (a0=0) (3::2:) (Nil nat)]

(define (terms-and-final-term-to-seqterm terms final-term)
  (if (null? terms)
      (let ((var (type-to-new-var (py "nat"))))
	(make-term-in-abst-form var final-term))
      (seqterm-and-term-to-shifted-seqterm
       (terms-and-final-term-to-seqterm (cdr terms) final-term)
       (car terms))))
      
(pp (nt (terms-and-final-term-to-seqterm
	 (list (pt "(1::3:)")
	       (pt "(2::2:)")
	       (pt "(0::0::4::2::2:)")
	       (pt "(2::0::4::2::2::2:)"))
	 (pt "3::2:"))))

;; [a0]
;;  [if (a0=0)
;;    (1::3:)
;;    [if (Pred a0=0)
;;     (2::2:)
;;     [if (Pred(Pred a0)=0)
;;      (0::0::4::2::2:)
;;      [if (Pred(Pred(Pred a0))=0) (2::0::4::2::2::2:) (3::2:)]]]]

;; (generate-seq n items final-item) generates a list of (length
;; items)^n infinite sequences starting with all possible variations
;; of n objects taken from items and continuing with final-item.

(define (generate-seq n items final-item)
  (if (= n 0)
      (list (lambda (n) final-item))
      (foldr (lambda (f l)
	       (let ((shifted-ls(map (lambda (w)
				       (lambda (n)
					 (if (= n 0) w (f (- n 1)))))
				     items)))
		 (append shifted-ls l)))
	     '()
	     (generate-seq (- n 1) items final-item))))

;; (first f n) returns a list of (f 0),(f 1),...,(f n-1).

(define (first f n)
  (if (= n 0)
      '()
       (cons (f 0)
	     (first (lambda (n) (f (+ n 1))) (- n 1)))))

(define (list-to-term ns)
  (if (null? ns)
      (pt "(Nil nat)")
      (mk-term-in-app-form
       (make-term-in-const-form	 
	(const-substitute
	 (constr-name-to-constr "Cons")
	 (list (list (py "alpha") (py "nat")))
	 #t))
       (make-numeric-term (car ns))
       (list-to-term (cdr ns)))))

;; (pp (list-to-term '(1 2 7 4)))
;; 1::2::7::4:

(define (test-neterm neterm vs n final-v)
  (let ((l (+ (length vs) n)))
    (map (lambda (seq)
	   (display (term-to-string
		     (nt (mk-term-in-app-form
			  neterm
			  (terms-and-final-term-to-seqterm
			   (map list-to-term (first seq (- l 1)))
			   (list-to-term (seq l)))))))
	   (display " gives good initial segment of ")
	   (display (first seq l))
	   (newline))
	 (generate-seq n vs final-v))
    *the-non-printing-object*))

;; a. [0 0], [1 1 0], [0 1 0 1], [0], ...
(test-neterm neterm '((0 0) (1 1 0) (0 1 0 1)) 3 '(0))

;; 2 gives good initial segment of ((0 1 0 1) (0 1 0 1) (0 1 0 1) (0) (0) (0))
;; 3 gives good initial segment of ((1 1 0) (0 1 0 1) (0 1 0 1) (0) (0) (0))
;; 2 gives good initial segment of ((0 0) (0 1 0 1) (0 1 0 1) (0) (0) (0))
;; 3 gives good initial segment of ((0 1 0 1) (1 1 0) (0 1 0 1) (0) (0) (0))
;; 2 gives good initial segment of ((1 1 0) (1 1 0) (0 1 0 1) (0) (0) (0))
;; 2 gives good initial segment of ((0 0) (1 1 0) (0 1 0 1) (0) (0) (0))
;; 3 gives good initial segment of ((0 1 0 1) (0 0) (0 1 0 1) (0) (0) (0))
;; 3 gives good initial segment of ((1 1 0) (0 0) (0 1 0 1) (0) (0) (0))
;; 2 gives good initial segment of ((0 0) (0 0) (0 1 0 1) (0) (0) (0))
;; 2 gives good initial segment of ((0 1 0 1) (0 1 0 1) (1 1 0) (0) (0) (0))
;; 3 gives good initial segment of ((1 1 0) (0 1 0 1) (1 1 0) (0) (0) (0))
;; 2 gives good initial segment of ((0 0) (0 1 0 1) (1 1 0) (0) (0) (0))
;; 3 gives good initial segment of ((0 1 0 1) (1 1 0) (1 1 0) (0) (0) (0))
;; 2 gives good initial segment of ((1 1 0) (1 1 0) (1 1 0) (0) (0) (0))
;; 2 gives good initial segment of ((0 0) (1 1 0) (1 1 0) (0) (0) (0))
;; 3 gives good initial segment of ((0 1 0 1) (0 0) (1 1 0) (0) (0) (0))
;; 3 gives good initial segment of ((1 1 0) (0 0) (1 1 0) (0) (0) (0))
;; 2 gives good initial segment of ((0 0) (0 0) (1 1 0) (0) (0) (0))
;; 2 gives good initial segment of ((0 1 0 1) (0 1 0 1) (0 0) (0) (0) (0))
;; 5 gives good initial segment of ((1 1 0) (0 1 0 1) (0 0) (0) (0) (0))
;; 2 gives good initial segment of ((0 0) (0 1 0 1) (0 0) (0) (0) (0))
;; 5 gives good initial segment of ((0 1 0 1) (1 1 0) (0 0) (0) (0) (0))
;; 2 gives good initial segment of ((1 1 0) (1 1 0) (0 0) (0) (0) (0))
;; 2 gives good initial segment of ((0 0) (1 1 0) (0 0) (0) (0) (0))
;; 3 gives good initial segment of ((0 1 0 1) (0 0) (0 0) (0) (0) (0))
;; 3 gives good initial segment of ((1 1 0) (0 0) (0 0) (0) (0) (0))
;; 2 gives good initial segment of ((0 0) (0 0) (0 0) (0) (0) (0))

(test-neterm neterm '((4 1) (3 3 0) (0 4 0 1)) 3 '())

;; 2 gives good initial segment of ((0 4 0 1) (0 4 0 1) (0 4 0 1) () () ())
;; 3 gives good initial segment of ((3 3 0) (0 4 0 1) (0 4 0 1) () () ())
;; 2 gives good initial segment of ((4 1) (0 4 0 1) (0 4 0 1) () () ())
;; 3 gives good initial segment of ((0 4 0 1) (3 3 0) (0 4 0 1) () () ())
;; 2 gives good initial segment of ((3 3 0) (3 3 0) (0 4 0 1) () () ())
;; 3 gives good initial segment of ((4 1) (3 3 0) (0 4 0 1) () () ())
;; 3 gives good initial segment of ((0 4 0 1) (4 1) (0 4 0 1) () () ())
;; 3 gives good initial segment of ((3 3 0) (4 1) (0 4 0 1) () () ())
;; 2 gives good initial segment of ((4 1) (4 1) (0 4 0 1) () () ())
;; 2 gives good initial segment of ((0 4 0 1) (0 4 0 1) (3 3 0) () () ())
;; 3 gives good initial segment of ((3 3 0) (0 4 0 1) (3 3 0) () () ())
;; 2 gives good initial segment of ((4 1) (0 4 0 1) (3 3 0) () () ())
;; 3 gives good initial segment of ((0 4 0 1) (3 3 0) (3 3 0) () () ())
;; 2 gives good initial segment of ((3 3 0) (3 3 0) (3 3 0) () () ())
;; 3 gives good initial segment of ((4 1) (3 3 0) (3 3 0) () () ())
;; 5 gives good initial segment of ((0 4 0 1) (4 1) (3 3 0) () () ())
;; 3 gives good initial segment of ((3 3 0) (4 1) (3 3 0) () () ())
;; 2 gives good initial segment of ((4 1) (4 1) (3 3 0) () () ())
;; 2 gives good initial segment of ((0 4 0 1) (0 4 0 1) (4 1) () () ())
;; 5 gives good initial segment of ((3 3 0) (0 4 0 1) (4 1) () () ())
;; 2 gives good initial segment of ((4 1) (0 4 0 1) (4 1) () () ())
;; 5 gives good initial segment of ((0 4 0 1) (3 3 0) (4 1) () () ())
;; 2 gives good initial segment of ((3 3 0) (3 3 0) (4 1) () () ())
;; 3 gives good initial segment of ((4 1) (3 3 0) (4 1) () () ())
;; 3 gives good initial segment of ((0 4 0 1) (4 1) (4 1) () () ())
;; 3 gives good initial segment of ((3 3 0) (4 1) (4 1) () () ())
;; 2 gives good initial segment of ((4 1) (4 1) (4 1) () () ())
