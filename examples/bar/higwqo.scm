;; higwqo.scm.  2014-10-27

;; (load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(libload "list.scm")
(set! COMMENT-FLAG #t)

(remove-var-name "n" "m" "k" (py "nat"))
(add-var-name "a" "b" "c" "n" "m" "k" "i" "j" (py "nat"))
(add-var-name "v" "w" "u" "as" "bs" "cs" "is" "js" "ks" (py "list nat"))
(add-var-name "ws" "vs" "us" (py "list list nat"))
(add-var-name "wss" "vss" (py "list list list nat"))

(add-var-name "f" (py "nat=>list nat"))

;; We are given a well quasi ordering wqo on nat, viewed as variable.
;; We may assume reflexivity, transitivity and antisymmetry.

(add-var-name "wqo" (py "nat=>nat=>boole"))

;; WqoRefl
(pp (pf "all a wqo a a"))

;; WqoTrans
(pp (pf "all a,b,c(wqo a b -> wqo b c -> wqo a c)"))

;; WqoAntiSym
(pp (pf "all a,b(wqo a b -> wqo b a -> a=b)"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Definitions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(add-program-constant
 "ListListNatSub" (py "list list nat=>list list nat=>boole") t-deg-zero)
(add-infix-display-string "ListListNatSub" "sub" 'rel-op)
(add-computation-rules
 "(Nil list nat)sub ws" "True"
 "(v::vs)sub(Nil list nat)" "False"
 "(v::vs)sub(w::ws)" "[if (v=w) (vs sub ws) ((v::vs)sub ws)]")

;; ListListNatSubTotal
(set-goal (rename-variables (term-to-totality-formula (pt "ListListNatSub"))))
(use "AllTotalElim")
(ind)
(ng)
(strip)
(use "TotalBooleTrue")
(assume "v" "vs" "IH")
(use "AllTotalElim")
(ind)
(use "TotalBooleFalse")
(assume "w" "ws" "IHws")
(ng)
(use "BooleIfTotal")
(use "BooleTotalVar")
(use "IH")
(use "ListTotalVar")
(use "IHws")
;; Proof finished.
(save "ListListNatSubTotal")

;; (Incr wqo as) means that as is an inhabited increasing sequence.
(add-program-constant
 "Incr" (py "(nat=>nat=>boole)=>list nat=>boole") t-deg-zero)
(add-computation-rules
 "Incr wqo(Nil nat)" "True"
 "Incr wqo(a:)" "True"
 "Incr wqo(a0::a1::as)" "wqo a1 a0 andb Incr wqo(a1::as)")

;; IncrTotal
(set-goal (rename-variables (term-to-totality-formula (pt "Incr"))))
(assume "wqo^" "Twqo")
(use "AllTotalElim")
(ind)
(ng)
(use "TotalBooleTrue")
(assume "a" "as" "IHas")
(cases (pt "as"))
(assume "Useless")
(use "TotalBooleTrue")
(assume "b" "bs" "as=bbs")
(ng #t)
(use "AndConstTotal")
(use "Twqo")
(use "NatTotalVar")
(use "NatTotalVar")
(simp "<-" "as=bbs")
(use "IHas")
;; Proof finished.
(save "IncrTotal")

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

;; RTotal
(set-goal (rename-variables (term-to-totality-formula (pt "R"))))
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
(save "RTotal")

(add-program-constant
 "I" (py "(nat=>nat=>boole)=>nat=>list nat=>list nat") t-deg-zero)
(add-computation-rules
 "I wqo a(Nil nat)" "(Nil nat)"
 "I wqo a(b::w)" "[if (wqo a b) (Nil nat) (b::I wqo a w)]")

;; ITotal
(set-goal (rename-variables (term-to-totality-formula (pt "I"))))
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
(save "ITotal")

;; (L wqo a as) means a is leq an element of as.
(add-program-constant
 "L" (py "(nat=>nat=>boole)=>nat=>list nat=>boole") t-deg-zero)
(add-computation-rules
 "L wqo a(Nil nat)" "False"
 "L wqo a(b::as)" "[if (wqo a b) True (L wqo a as)]")

(set-goal (rename-variables (term-to-totality-formula (pt "L"))))
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
(save "LTotal")

(add-program-constant
 "EmbR" (py "(nat=>nat=>boole)=>list nat=>list nat=>boole") t-deg-zero)
(add-computation-rules
 "EmbR wqo(Nil nat)w" "True"
 "EmbR wqo(a::v)w" "L wqo a w andb EmbR wqo v Tail(R wqo a w)")

;; EmbRTotal
(set-goal (rename-variables (term-to-totality-formula (pt "EmbR"))))
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
(save "EmbRTotal")

(add-program-constant
 "LargerWR" (py "(nat=>nat=>boole)=>list nat=>list list nat=>boole") t-deg-zero)
(add-computation-rules
 "LargerWR wqo v(Nil list nat)" "False"
 "LargerWR wqo v(w::ws)" "[if (EmbR wqo w v) True (LargerWR wqo v ws)]")

;; LargerWRTotal
(set-goal (rename-variables (term-to-totality-formula (pt "LargerWR"))))
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
(save "LargerWRTotal")

(add-program-constant
 "GoodWR" (py "(nat=>nat=>boole)=>list list nat=>boole") t-deg-zero)
(add-computation-rules
 "GoodWR wqo(Nil list nat)" "False"
 "GoodWR wqo(w::ws)" "[if (LargerWR wqo w ws) True (GoodWR wqo ws)]")

;; (add-computation-rules
;;  "GoodWR wqo(Nil list nat)" "False"
;;  "GoodWR wqo(w::ws)" "LargerWR wqo w ws orb GoodWR wqo ws")

;; GoodWRTotal
(set-goal (rename-variables (term-to-totality-formula (pt "GoodWR"))))
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
(save "GoodWRTotal")

(add-program-constant
 "MapCons" (py "list nat=>list list nat=>list list nat") t-deg-zero)
(add-infix-display-string "MapCons" "mapcons" 'pair-op) ;right associative
(add-computation-rules
 "(a::as)mapcons v::vs" "(a::v)::as mapcons vs"
 "(Nil nat)mapcons vs" "(Nil list nat)"
 "as mapcons(Nil list nat)" "(Nil list nat)")

;; MapConsTotal
(set-goal (rename-variables (term-to-totality-formula (pt "MapCons"))))
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
(save "MapConsTotal")

;; (LargerAR wqo a as) means that a is larger than (w.r.t. wqo) an
;; element ai of as.
(add-program-constant
 "LargerAR" (py "(nat=>nat=>boole)=>nat=>list nat=>boole") t-deg-zero)
(add-computation-rules
 "LargerAR wqo b(Nil nat)" "False"
 "LargerAR wqo a(a0::as)" "[if (wqo a0 a) True (LargerAR wqo a as)]")

(set-goal (rename-variables (term-to-totality-formula (pt "LargerAR"))))
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
(save "LargerARTotal")

;; (set-goal (rename-variables (term-to-totality-formula (pt "G"))))
;; (assume "wqo^" "Twqo")
;; (use "AllTotalElim")
;; (assume "a")
;; (use "AllTotalElim")
;; (ind)
;; (ng)
;; (use "TotalBooleFalse")
;; (assume "a1" "as" "IH")
;; (ng)
;; (use "BooleIfTotal")
;; (use "Twqo")
;; (use "NatTotalVar")
;; (use "NatTotalVar")
;; (use "TotalBooleTrue")
;; (use "IH")
;; ;; Proof finished.
;; (save "GTotal")

;; (H wqo a ws) means a is larger than (w.r.t. wqo) the head of a word in ws.
(add-program-constant
 "H" (py "(nat=>nat=>boole)=>nat=>list list nat=>boole") t-deg-zero)
(add-computation-rules
 "H wqo a(Nil list nat)" "False"
 "H wqo a((Nil nat)::ws)" "H wqo a ws"
 "H wqo a((b::v)::ws)" "[if (wqo b a) True (H wqo a ws)]")

(set-goal (rename-variables (term-to-totality-formula (pt "H"))))
(assume "wqo^" "Twqo")
(use "AllTotalElim")
(assume "a")
(use "AllTotalElim")
(ind)
(ng)
(use "TotalBooleFalse")
(cases) ;on v
(ng)
(assume "ws" "THws")
(use "THws")
(assume "b" "v" "ws" "IH")
(ng)
(use "BooleIfTotal")
(use "Twqo")
(use "NatTotalVar")
(use "NatTotalVar")
(use "TotalBooleTrue")
(use "IH")
;; Proof finished.
(save "HTotal")

;; (Adm ws) means that each word in ws has a positive length
(add-program-constant "Adm" (py "list list nat=>boole") t-deg-zero)
(add-computation-rules
 "Adm(Nil list nat)" "True"
 "Adm(v::ws)" "0<Lh v andb Adm ws")

;; AdmTotal
(set-goal (rename-variables (term-to-totality-formula (pt "Adm"))))
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
(save "AdmTotal")

;; (BSeq wqo as) returns the canonical bad sequence in as, by leaving
;; out each a that would make the sequence good.

(add-program-constant
 "BSeq" (py "(nat=>nat=>boole)=>list nat=>list nat") t-deg-zero)
(add-computation-rules
 "BSeq wqo(Nil nat)" "(Nil nat)"
 "BSeq wqo(a::as)"
 "[if (LargerAR wqo a as) (BSeq wqo as) (a::BSeq wqo as)]")

;; BSeqTotal
(set-goal (rename-variables (term-to-totality-formula (pt "BSeq"))))
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
(use "ListTotalVar")
(use "IHas")
(use "TotalListCons")
(use "NatTotalVar")
(use "IHas")
;; Proof finished.
(save "BSeqTotal")

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

;; Destructors
(add-program-constant "LntreeRoot" (py "lntree alpha=>alpha") t-deg-zero)
(add-prefix-display-string "LntreeRoot" "Root")
(add-computation-rules "Root(x%txs)" "x")

(add-program-constant
 "LntreeSubtrees" (py "lntree alpha=>list(lntree alpha)") t-deg-zero)
(add-prefix-display-string "LntreeSubtrees" "Subtrees")
(add-computation-rules "Subtrees(x%txs)" "txs")

;; LntreeRootTotal
(set-goal
 (rename-variables (term-to-totality-formula (pt "(LntreeRoot alpha)"))))
(assume "tx^" "Ttx")
(elim "Ttx")
(assume "x^" "Tx" "txs^" "Ttxs")
(ng)
(use "Tx")
;; Proof finished.
(save "LntreeRootTotal")

;; LntreeSubtreesTotal
(set-goal
 (rename-variables
  (term-to-unfolded-totality-formula (pt "(LntreeSubtrees alpha)"))))
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
(save "LntreeSubtreesTotal")

;; (Roots txs) returns the list of roots of txs
(add-program-constant
 "LntreeRoots" (py "list lntree alpha=>list alpha") t-deg-zero)
(add-prefix-display-string "LntreeRoots" "Roots")
(add-computation-rules
 "Roots(Nil lntree alpha)" "(Nil alpha)"
 "Roots(tx::txs)" "Root tx::Roots txs")

;; LntreeRootsTotal
(set-goal
 (rename-variables (term-to-totality-formula (pt "(LntreeRoots alpha)"))))
(assume "txs^" "Ttxs")
(elim "Ttxs")
(use "TotalListNil")
(assume "tx^" "Ttx" "txs^1" "Ttxs1" "IH")
(ng #t)
(use "TotalListCons")
(use "LntreeRootTotal")
(use "Ttx")
(use "IH")
;; Proof finished.
(save "LntreeRootsTotal")

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

;; LntreeHeightTTotal
(set-goal "allnc tx^(TotalLntree tx^ -> TotalNat(HtT tx^))")
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
;; Proof finished.
(save "LntreeHeightTTotal")

;; LntreeHeightFTotal
(set-goal "allnc txs^(TotalList txs^ -> TotalNat(HtF txs^))")
(assume "txs^" "Ttxs")
(elim "Ttxs")
(ng #t)
(use "TotalNatZero")
(assume "tx^" "Ttx" "txs^1" "Ttxs1" "IH")
(ng #t)
(use "TotalNatSucc")
(use "NatMaxTotal")
(use "LntreeHeightTTotal")
(use "Ttx")
(use "IH")
;; Proof finished.
(save "LntreeHeightFTotal")

(add-var-name "t" "s" (py "lntree(list list nat yprod list nat)"))
(add-var-name
 "ts" "ss" "rs" (py "list(lntree(list list nat yprod list nat))"));or x?
(pp (pt "(vs pair as)%ts"))
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

;; Rhts applied to a list of pairs vsas returns the list of their
;; right hand sides.
;; (remove-program-constant "Rhts")
(add-program-constant
 "Rhts" (py "list(list list nat yprod list nat)=>list list nat") t-deg-zero)
(add-computation-rules "Rhts vsass" "([vsas]rht vsas)map vsass")

;; RhtsTotal
(set-goal (rename-variables (term-to-totality-formula (pt "Rhts"))))
(use "AllTotalElim")
(ng)
(assume "vsass")
(use "ListMapTotal")
(use "AllTotalElim")
(assume "vsas")
(use "ListTotalVar")
(use "ListTotalVar")
;; Proof finished.
(save "RhtsTotal")

;; (NewTree vs as) returns (vs pair as)%[]
(add-program-constant
 "NewTree" (py "list list nat yprod list nat=>
                lntree(list list nat yprod list nat)") t-deg-zero)
(add-computation-rules
 "NewTree vsas" "vsas%(Nil lntree(list list nat yprod list nat))")

;; NewTreeTotal
(set-goal (rename-variables (term-to-totality-formula (pt "NewTree"))))
(use "AllTotalElim")
(assume "vsas")
(ng)
(use "TotalLntreeLNBranch")
(use "YprodTotalVar")
(use "RTotalListNil")
;; Proof finished.
(save "NewTreeTotal")

;; (InsertT wqo t v a) returns the result of inserting v and a into t,
;; as follows.  Let t be vsas%ts.  If a is not above the rhs of some
;; root in ts, then extend ts by a new tree consisting of a root only,
;; formed by appending v to (lft vsas) and a to (rht vsas).  Otherwise
;; recursively insert v and a into ts.

(add-program-constant
 "InsertT" (py "(nat=>nat=>boole)=>lntree(list list nat yprod list nat)=>
               list nat=>nat=>lntree(list list nat yprod list nat)")
 t-deg-zero)

(add-program-constant
 "InsertF"
 (py "(nat=>nat=>boole)=>list(lntree(list list nat yprod list nat))=>
      list nat=>nat=>list(lntree(list list nat yprod list nat))")
 t-deg-zero)

(add-computation-rules
 "InsertT wqo(vsas%ts)v a"
 "vsas%[if (LargerAR wqo a(Heads(Rhts Roots ts)))
           (InsertF wqo ts v a)
           (NewTree((v::lft vsas)pair a::rht vsas)::ts)]")

(add-computation-rules
 "InsertF wqo ts v a"
 "([t][if (wqo Head rht Root t a) (InsertT wqo t v a) t])map ts")

(search-about 'all "InsertT")

;; InsertTInsertFTotalAux
(set-goal "all wqo,a,v,n(
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
(cases (pt "(LargerAR wqo a Heads(Rhts Roots Subtrees t))"))
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
(assume "Trivial")
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
;; Proof finished.
(save "InsertTInsertFTotalAux")

;; InsertTTotal
(set-goal (rename-variables (term-to-totality-formula (pt "InsertT"))))
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
;; Proof finished.
(save "InsertTTotal")

;; Difficulties when trying to use AllTotalElim directly
;; InsertTTotal
;; (set-goal (rename-variables (term-to-totality-formula (pt "InsertT"))))
;; (use "AllTotalElim" (pt "wqo^"))
;; more terms expected, to be substituted for
;; alpha^
;; (use "AllTotalElim" (pt "wqo^"))
;; types don't fit for all-elim
;; alpha
;; nat=>nat=>boole
;; originating from all-formula
;; (use-with "AllTotalElim" (py "nat=>nat=>boole"))
;; inadmissible substitution
;; ((alpha nat=>nat=>boole))

;; InsertFTotal
(set-goal (rename-variables (term-to-totality-formula (pt "InsertF"))))
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
(save "InsertFTotal")

;; InsertFCons
(set-goal "all wqo,t,ts,v,a
     InsertF wqo(t::ts)v a=
     [if (wqo Head rht Root t a)
       (InsertT wqo t v a::InsertF wqo ts v a)
       (t::InsertF wqo ts v a)]")
(assume "wqo" "t" "ts" "v" "a")
(ng)
(cases (pt "wqo Head rht Root t a"))
(assume "Useless")
(ng #t)
(use "Truth")
(assume "Useless")
(ng #t)
(use "Truth")
;; Proof finished.
(save "InsertFCons")

;; (Forest wqo ws) returns a list of labeled trees.
;; (remove-program-constant "Forest")
(add-program-constant
 "Forest" (py "(nat=>nat=>boole)=>list list nat=>
               list(lntree(list list nat yprod list nat))") t-deg-zero)
(add-computation-rules
 "Forest wqo(Nil list nat)" "(Nil lntree(list list nat yprod list nat))"
 "Forest wqo((Nil nat)::ws)" "Forest wqo ws"
 "Forest wqo ((a::v)::ws)"
 "[if (H wqo a ws)
      (InsertF wqo(Forest wqo ws)v a)
      (NewTree((v::ws)pair a:)::Forest wqo ws)]")

;; Examples for NatLe
;; The forest of [35].
;; (pp (nt (pt "Forest NatLe(3::5:):")))

;; ((5: :pair 3:)%(Nil lntree(list list nat yprod list nat))):

;; ([[5]],[3])

;; The forest of [69] [35].
;; (pp (nt (pt "Forest NatLe((6::9:)::(3::5:):)")))

;; ((5: :pair 3:)%
;;  (((9: ::5: :)pair 6::3:)%(Nil lntree(list list nat yprod list nat))):):

;; ([[9] [5]],[6 3])
;; -----------------
;;     ([[5]],[3])

;; The forest of [421] [69] [35].
;; (pp (nt (pt "Forest NatLe((4::2::1:)::(6::9:)::(3::5:):)")))

;; ((5: :pair 3:)%
;;  ((((2::1:)::5: :)pair 4::3:)%(Nil lntree(list list nat yprod list nat)))::
;;  (((9: ::5: :)pair 6::3:)%(Nil lntree(list list nat yprod list nat))):):

;; ([[2 1] [5]],[4 2])   ([[9] [5]],[6 3])
;; ---------------------------------------
;;               ([[5]],[3])

;; The forest of [28] [421] [69] [35].
;; (pp (nt (pt "Forest NatLe((2::8:)::(4::2::1:)::(6::9:)::(3::5:):)")))

;; (((8: ::(4::2::1:)::(6::9:)::(3::5:):)pair 2:)%
;;  (Nil lntree(list list nat yprod list nat)))::
;; ((5: :pair 3:)%
;;  ((((2::1:)::5: :)pair 4::3:)%(Nil lntree(list list nat yprod list nat)))::
;;  (((9: ::5: :)pair 6::3:)%(Nil lntree(list list nat yprod list nat))):):

;;                               ([[21] [5]],[43])   ([[9] [5]],[63])
;;                               ------------------------------------
;; ([[8] [421] [69] [35]],[2])               ([[5]],[3])

;; The forest of [52] [28] [421] [69] [35].
;;(pp (nt (pt "Forest NatLe((5::2:)::(2::8:)::(4::2::1:)::(6::9:)::(3::5:):)")))

;; (((8: ::(4::2::1:)::(6::9:)::(3::5:):)pair 2:)%
;;  (((2: ::8: ::(4::2::1:)::(6::9:)::(3::5:):)pair 5::2:)%
;;   (Nil lntree(list list nat yprod list nat))):)::
;; ((5: :pair 3:)%
;;  ((((2::1:)::5: :)pair 4::3:)%
;;   (((2: ::(2::1:)::5: :)pair 5::4::3:)%
;;    (Nil lntree(list list nat yprod list nat))):)::
;;  (((9: ::5: :)pair 6::3:)%(Nil lntree(list list nat yprod list nat))):):

;;                                      ([[2] [21] [5]],[543])
;;                                      ----------------------
;; ([[2] [8] [421] [69] [35]],[52])         ([[21] [5]],[43])   ([[9] [5]],[63])
;; --------------------------------         ------------------------------------
;;     ([[8] [421] [69] [35]],[2])                      ([[5]],[3])

;; The left-hand-side of each leaf consists of the sequence
;; [v_{\kappa_i},\dots,v_{\kappa_0},w_{\kappa_0-1},\dots,w_0],and its
;; right-hand-side is the maximal descending subsequence
;; [a_{\kappa_i},\dots,a_{\kappa_0}] of [a_n,\dots,a_0].  In the
;; example the leaf ([[2] [8] [421] [69] [35]],[52]) has exactly this
;; form: [52] is a maximal descending subsequence of [52463], and 
;; [52] [28] [421] [69] [35] = 5*[2] 2*[8] [421] [69] [35].

(search-about 'all "Forest")

;; ForestDefCons is obsolete.  Use Forest2CompRule instead
;; (set-goal "all wqo^,a^,v^,ws^
;;      Forest wqo^((a^ ::v^)::ws^) eqd
;;      [if (H wqo^ a^ ws^)
;;          (InsertF wqo^(Forest wqo^ ws^)v^ a^)
;;          (NewTree((v^ ::ws^)pair a^ :)::Forest wqo^ ws^)]")
;; (assume "wqo^" "a^" "v^" "ws^")
;; (use "InitEqD")
;; ;; Proof finished.
;; (save "ForestDefCons")

;; ForestTotal
(set-goal (rename-variables (term-to-totality-formula (pt "Forest"))))
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
(save "ForestTotal")

;; ForestConsInsertFDef
(set-goal "all wqo^,a^,ws^,v^(
 H wqo^ a^ ws^ -> Forest wqo^((a^ ::v^)::ws^)eqd
 InsertF wqo^(Forest wqo^ ws^)v^ a^)")
(assume "wqo^" "a^" "ws^" "v^" "HHyp")
(ng)
(simp "HHyp")
(ng)
(use "InitEqD")
;; Proof finished.
(save "ForestConsInsertFDef")
 
;; ForestConsNewDef
(set-goal "all wqo,a,ws,v((H wqo a ws -> F) ->
 Forest wqo((a ::v)::ws)=
 (NewTree((v ::ws)pair a:)::Forest wqo ws))")
(assume "wqo" "a" "ws" "v" "HHyp")
(ng)
(simp "HHyp")
(ng)
(use "Truth")
;; Proof finished.
(save "ForestConsNewDef")

;; (NewATree a) returns a%[]
(add-program-constant "NewATree"(py "nat=>lntree nat") t-deg-zero)
(add-computation-rules "NewATree a" "a%(Nil lntree nat)")

(add-var-name "ta" "sa" (py "lntree nat"))
(add-var-name "tas" "sas" "ras" (py "list lntree nat"))

;; We will need ListLntreeEqToEqD theorems.  The presence of the
;; nested algebra lntree makes it necessary to use induction on HtT
;; and HtF in between.

;; Need this for BarFNil.  Variable names:
;; as -> tas
;; bs -> sas
;; a -> ta
;; b -> sa

;; 2014-09-21.  Done up to this point

;; LntreeNatEqToEqDAux
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
(use "NatEqToEqD")
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
(save "LntreeNatEqToEqDAux")

;; LntreeNatEqToEqD
(set-goal "all ta,sa(ta=sa -> ta eqd sa)")
(assume "ta" "sa")
(use-with "LntreeNatEqToEqDAux"
	  (pt "Succ(HtT ta max HtT sa)") 'left (pt "ta") (pt "sa") "?" "?")
(use "NatLeLtTrans" (pt "HtT ta max HtT sa"))
(use "NatMaxUB1")
(use "Truth")
(use "NatLeLtTrans" (pt "HtT ta max HtT sa"))
(use "NatMaxUB2")
(use "Truth")
;; Proof finished.
(save "LntreeNatEqToEqD")

;; ListLntreeNatEqToEqD
(set-goal "all tas,sas(tas=sas -> tas eqd sas)")
(assume "tas" "sas")
(use-with "LntreeNatEqToEqDAux"
	  (pt "Succ(HtF tas max HtF sas)") 'right (pt "tas") (pt "sas") "?" "?")
(use "NatLeLtTrans" (pt "HtF tas max HtF sas"))
(use "NatMaxUB1")
(use "Truth")
(use "NatLeLtTrans" (pt "HtF tas max HtF sas"))
(use "NatMaxUB2")
(use "Truth")
;; Proof finished.
(save "ListLntreeNatEqToEqD")

;; NewATreeTotal
(set-goal (rename-variables (term-to-totality-formula (pt "NewATree"))))
(use "AllTotalElim")
(assume "a")
(ng)
(use "TotalLntreeLNBranch")
(use "NatTotalVar")
(use "RTotalListNil")
;; Proof finished.
(save "NewATreeTotal")

;; (InsertAT wqo ta a) inserts a into ta=a%tas, by cases on the term
;; LargerAR wqo a Roots tas.
;; (InsertAF wqo ts a) recursively inserts a into tas

(add-program-constant
 "InsertAT" (py "(nat=>nat=>boole)=>lntree nat=>nat=>lntree nat") t-deg-zero)

(add-program-constant
 "InsertAF"
 (py "(nat=>nat=>boole)=>list lntree nat=>nat=>list lntree nat") t-deg-zero)

(add-computation-rules
 "InsertAT wqo(a0%tas)a"
 "a0%[if (LargerAR wqo a Roots tas)
         (InsertAF wqo tas a)
         (NewATree a::tas)]")

(add-computation-rules
 "InsertAF wqo tas a"
 "([ta][if (wqo Root ta a) (InsertAT wqo ta a) ta])map tas")

;; InsertATInsertAFTotalAux
(set-goal "all wqo,a,n(
 all ta(HtT ta<n -> TotalLntree(InsertAT wqo ta a))&
 all tas(HtF tas<n -> TotalList(InsertAF wqo tas a)))")
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
(simp "<-" "RootSubtreesId")
(assert "HtT(Root ta%Subtrees ta)=Succ HtF Subtrees ta")
 (use "Truth")
(assume "HtT(Root ta%Subtrees ta)=Succ HtF Subtrees ta")
(simp "HtT(Root ta%Subtrees ta)=Succ HtF Subtrees ta")
(drop "HtT(Root ta%Subtrees ta)=Succ HtF Subtrees ta")
(assume "HtF Subtrees ta<n")
(ng "HtF Subtrees ta<n")
(simp "InsertAT0CompRule")
(cases (pt "(LargerAR wqo a Roots Subtrees ta)"))
;; Case True
(assume "Useless")
(use  "TotalLntreeLNBranch")
(use "NatTotalVar")
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
(ng #t)
(assume "Trivial")
(use "TotalListNil")
(assume "ta" "tas" "IHtas" "HtBound")
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
;; Proof finished.
(save "InsertATInsertAFTotalAux")

;; InsertATTotal
(set-goal (rename-variables (term-to-totality-formula (pt "InsertAT"))))
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
;; Proof finished.
(save "InsertATTotal")

;; InsertAFTotal
(set-goal (rename-variables (term-to-totality-formula (pt "InsertAF"))))
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
(save "InsertAFTotal")

;; InsertAFCons
(set-goal "all wqo,ta,tas,a
     InsertAF wqo(ta::tas)a=
     [if (wqo Root ta a)
       (InsertAT wqo ta a::InsertAF wqo tas a)
       (ta::InsertAF wqo tas a)]")
(assume "wqo" "ta" "tas" "a")
(ng)
(cases (pt "wqo Root ta a"))
(assume "Useless")
(ng #t)
(use "Truth")
(assume "Useless")
(ng #t)
(use "Truth")
;; Proof finished.
(save "InsertAFCons")

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

;; GoodARTotal
(set-goal (rename-variables (term-to-totality-formula (pt "GoodAR"))))
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
(save "GoodARTotal")

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

;; GLTGLFTotalAux
(set-goal "all wqo,n(
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
;; Proof finished.
(save "GLTGLFTotalAux")

;; GLTTotal
(set-goal (rename-variables (term-to-totality-formula (pt "GLT"))))
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
;; Proof finished.
(save "GLTTotal")

;; GLFTotal
(set-goal (rename-variables (term-to-totality-formula (pt "GLF"))))
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
(save "GLFTotal")

;; An A-tree at is a labelled nested tree with labels in A.

;; (Proj t) projects out each head of the rhs of a label in t.
;; (ProjF ts) does the same thing recursively for forests.

(add-program-constant
 "Proj" (py "lntree(list list nat yprod list nat)=>lntree nat") t-deg-zero)
(add-program-constant
 "ProjF" (py "list lntree(list list nat yprod list nat)=>list lntree nat")
 t-deg-zero)
(add-computation-rules
 "Proj(vsas%ts)" "Head rht vsas%ProjF ts")
(add-computation-rules
 "ProjF(Nil lntree(list list nat yprod list nat))" "(Nil lntree nat)"
 "ProjF(t::ts)" "Proj t::ProjF ts")

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

;; When we want to use the defining equation of Proj in a context
;; where normalization is unwanted we may use simp with ProjDef instead.

(search-about 'all "Proj")

;; ProjDef is obsolete.  Use Proj0CompRule
;; (set-goal "all vsas^,ts^ Proj(vsas^ %ts^)eqd(Head rht vsas^ %ProjF ts^)")
;; (assume "vsas^" "ts^")
;; (use "InitEqD")
;; ;; Proof finished.
;; (save "ProjDef")

;; ProjTotal
(set-goal (rename-variables (term-to-totality-formula (pt "Proj"))))
(assume "t^" "Tt")
(elim "Tt")
(use "AllTotalElim")
(assume "vsas")
(assume "ts^" "Tts")
(ng #t)
(use "TotalLntreeLNBranch")
(use "NatTotalVar")
(elim "Tts")
(ng #t)
(use "RTotalListNil")
(assume "t^1" "Tt1" "ts^1" "Tts1" "IH")
(ng #t)
(use "RTotalListCons")
(use "Tt1")
(use "IH")
;; Proof finished.
(save "ProjTotal")

;; ProjFTotal
(set-goal (rename-variables (term-to-totality-formula (pt "ProjF"))))
(assume "ts^" "Tts")
(elim "Tts")
(ng #t)
(use "TotalListNil")
(assume "t^" "Tt" "ts^1" "Tts1" "IH")
(ng #t)
(use "TotalListCons")
(use "ProjTotal")
(use "Tt")
(use "IH")
;; Proof finished.
(save "ProjFTotal")

;; Predecessors of (BarF wqo ts) are all tas where a is inserted
;; inside (i.e., not appended to the final as because a::as is bad)

(add-ids
 (list
  (list "BarA" (make-arity (py "nat=>nat=>boole") (py "list nat")) "treeA"))
 '("allnc as(GoodAR wqo as -> BarA wqo as)" "InitBarA")
 '("allnc as(all a BarA wqo(a::as) -> BarA wqo as)" "GenBarA"))

(add-ids
 (list
  (list "BarF" (make-arity (py "nat=>nat=>boole")
			   (py "list lntree(list list nat yprod list nat)"))
	     "treeF"))
 '("allnc ts,i(i<Lh ts -> GLT wqo(i thof ts) -> BarF wqo ts)" "InitBarF")
 '("allnc ts(
 all tas,a,v(tas=ProjF ts -> LargerAR wqo a Roots tas ->
 BarF wqo(InsertF wqo ts v a)) ->
 BarF wqo ts)"
  "GenBarF"))

;; "allnc ts(GLF ts -> BarF wqo ts)" would be better.

;; (display-alg "treeA" "treeF")
;; treeA
;; 	CInitBarA:	treeA
;; 	CGenBarA:	(nat=>treeA)=>treeA
;; treeF
;; 	CInitBarF:	treeF
;; 	CGenBarF:	(list lntree nat=>nat=>list nat=>treeF)=>treeF

(add-ids (list (list "BarW" (make-arity (py "nat=>nat=>boole")
				       (py "list list nat")) "treeW"))
	 '("allnc vs(GoodW wqo vs -> BarW wqo vs)" "InitBarW")
	 '("allnc vs(all v BarW wqo(v::vs) -> BarW wqo vs)" "GenBarW"))

;; (IncrExt wqo vsas1 vsas) means vs_i is v_i::vs and as_i is a_i::as
;; and a_i >= Head v_i, for all i.
(add-program-constant
 "IncrExt" (py "(nat=>nat=>boole)=>list list nat yprod list nat=>
                list list nat yprod list nat=>boole")
 t-deg-zero)

(add-computation-rules
 "IncrExt wqo vsas1 vsas"
 "Tail lft vsas1=lft vsas andb Tail rht vsas1=rht vsas andb
  wqo Head rht vsas Head rht vsas1")

;; IncrExtTotal
(set-goal (rename-variables (term-to-totality-formula (pt "IncrExt"))))
(assume "wqo^" "Twqo")
(use "AllTotalElim")
(assume "vsas1")
(use "AllTotalElim")
(assume "vsas2")
(ng)
(use "AndConstTotal")
(use "BooleTotalVar")
(use "AndConstTotal")
(use "BooleTotalVar")
(use "Twqo")
(use "NatTotalVar")
(use "NatTotalVar")
;; Proof finished.
(save "IncrExtTotal")

(add-program-constant
 "IncrExts" (py "(nat=>nat=>boole)=>list(list list nat yprod list nat)=>
                 list list nat yprod list nat=>boole")
 t-deg-zero)

(add-computation-rules
 "IncrExts wqo(Nil list list nat yprod list nat)vsas" "True"
 "IncrExts wqo(vsas1::vsass)vsas"
 "IncrExt wqo vsas1 vsas andb IncrExts wqo vsass vsas")

;; IncrExtsTotal
(set-goal (rename-variables (term-to-totality-formula (pt "IncrExts"))))
(assume "wqo^" "Twqo")
(use "AllTotalElim")
(ind)
(ng)
(strip)
(use "TotalBooleTrue")
(assume "vsas" "vsass" "IH")
(use "AllTotalElim")
(assume "vsas1")
(simp "IncrExts1CompRule")
(use "AndConstTotal")
(use "IncrExtTotal")
(use "Twqo")
(use "YprodTotalVar")
(use "YprodTotalVar")
(use "IH")
(use "YprodTotalVar")
;; Proof finished.
(save "IncrExtsTotal")

(add-program-constant
 "CorrT" (py "(nat=>nat=>boole)=>list list nat=>
              lntree(list list nat yprod list nat)=>boole") t-deg-zero)

(add-program-constant
 "CorrF" (py "(nat=>nat=>boole)=>list list nat=>
              list lntree(list list nat yprod list nat)=>boole") t-deg-zero)

(add-computation-rules
 "CorrT wqo ws(usas%ts)"
 "Lh rht usas<=Lh lft usas andb
  Incr wqo rht usas andb
  IncrExts wqo Roots ts usas andb
  (rht usas mapcons Lh rht usas init lft usas)++(Lh rht usas rest lft usas)
   sub ws andb
  CorrF wqo ws ts")

(add-computation-rules
 "CorrF wqo ws(Nil lntree(list list nat yprod list nat))" "True"
 "CorrF wqo ws(t::ts)" "CorrT wqo ws t andb CorrF wqo ws ts")

;; CorrTCorrFTotalAux
(set-goal "all wqo,ws,n(
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
(simp "CorrF1CompRule")
(use "AndConstTotal")
(use "IH")
(use "NatLeLtTrans" (pt "HtT t max HtF ts"))
(use "NatMaxUB1")
(use "HtBound")
(use "IH")
(use "NatLeLtTrans" (pt "HtT t max HtF ts"))
(use "NatMaxUB2")
(use "HtBound")
;; Proof finished.
(save "CorrTCorrFTotalAux")

;; CorrTTotal
(set-goal (rename-variables (term-to-totality-formula (pt "CorrT"))))
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
	       (pf "allnc ws^(TotalList ws^ -> allnc t^(
      TotalLntree t^ -> TotalBoole(CorrT wqo^ ws^ t^)))")))))))
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
;; Proof finished.
(save "CorrTTotal")

;; CorrFTotal
(set-goal (rename-variables (term-to-totality-formula (pt "CorrF"))))
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
	       (pf "allnc ws^(TotalList ws^ -> allnc ts^(
      TotalList ts^ -> TotalBoole(CorrF wqo^ ws^ ts^)))")))))))
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
(save "CorrFTotal")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Auxiliary propositions (n.c.)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Elementary properties of the defined functions and relations

;; (vs sub ws) means vs is a sublist if ws (abbreviates ListListNatSub)
;; (Incr wqo as) means that as is an inhabited increasing sequence
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
;; (H wqo a ws) means a is wqo the head of a word in ws
;; (Adm ws) means that each word in ws has a positive length
;; (BSeq wqo as) canonical bad sequence in as
;; Root prefix display for LntreeRoot
;; Subtrees prefix display for LntreeSubtrees
;; Roots prefix display for LntreeRoots, list of roots of txs
;; HtT prefix display for LntreeHeight, height of tx
;; HtF prefix display for LntreeHeightF, successor of the maximum of the
;;   heights of its subtrees
;; (Rhts vsas) returns the list of the right hand sides of vsas
;; (NewTree vs as) returns (vs pair as)%[]
;; (InsertT wqo t v a) inserts v and a into t=vsas%ts, by cases on
;;   LargerAR wqo a(Heads(Rhts Roots ts))
;; (InsertF wqo ts v a) recursively inserts v and a into ts
;; (Forest wqo ws) returns a list of labeled trees
;; (NewATree a) returns a%[]
;; (InsertAT wqo ta a) inserts a into ta=a%tas, by cases on LargerAR wqo a Roots tas
;; (InsertAF wqo ts a) recursively inserts a into tas
;; GoodAR
;; GoodLeafT (replaced by GLT)
;; GoodLeafF (replaced by GLF)
;; GLT
;; GLF
;; (Proj t) projects out each head of the rhs of a label in t
;; ProjF
;; (IncrExt wqo vsass vsas) means vs_i is v_i::vs and as_i is a_i::as
;;   and a_i >= Head as, for all i.
;; (IncrExts wqo vsas1 vsas) means (IncrExt wqo vasa_i vsas) for each i
;; (CorrT wqo ws t) means t is correct w.r.t. wqo and ws
;; (CorrF wqo ws ts) means t_i is correct w.r.t. wqo and ws for each i

;; Proposed order.

;; ListListNatSub: SubRefl SubCons SubTrans SubConsToSub

;; Incr: IncrCons IncrConsInv WqoIncr

;; I,R: IRSplit 

;; L: LToZeroLtLhR

;; Emb, LargerW, EmbR, LargerWR MapCons: EmbRAppdRight EmbToEmbR
;; EmbAppdRight EmbRToEmb LargerWRToLargerW LargerWToLargerWR LargerWRNil
;; LargerWRSub LargerWElim LargerWCons LargerWSub LargerWAppdCases
;; LargerWAppdLeft LargerWAppdRight LargerWMapcons

;; GoodW, GoodWR: GoodWElim GoodWNotNil GoodWAppdLeft GoodWSub GoodWToGoodWR
;; GoodWRToGoodW GoodWAppdMapcons

;; LargerAR, H: LargerARTrans LargerARAppdCases LargerARProj HAdm LargerARHeadsEqH

;; BSeq: BSeqDefCons LargerARBSeqToLargerAR LargerARToLargerARBSeq 

;; Rhts: LhRhts 

;; Roots: LhRoots RootsAppd

;; InsertT, InsertF: LhInsertF InsertFAppd InsertFId InsertFAppdRight
;; InsertFEqInsertT RootInsertTEqRoot RootsInsertFEqRoots

;; Forest: ForestConsInsertF ForestConsNewDef LhForest
;; GoodWProjForestToGoodW BSeqHeadsEqRhtsRootsForest

;; GLT, GLF: GLFToExGLT ExGLTToGLF InitIndGLT GenIndGLT InitIndGLF
;; GenIndGLF (clauses of the inductive variants GoodWLeafT GoodWLeafF)

;; Proj, ProjF: GoodWLeafFProj RootProjEqHeadRhtRoot
;; RootsProjFEqHeadsRhtsRoots ProjFAppd LhProjF

;; GoodAR: GoodARConsBad NotGoodARBSeq GoodARProj GoodARToGoodA GoodAToGoodAR

;; CorrT, CorrF: CorrConsAux CorrTCons CorrFCons CorrInsertAux
;; CorrTInsertT CorrFInsertF CorrFForest

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

;; SubConsToSub
(set-goal "all v,w,vs,ws((v::vs)sub(w::ws) -> vs sub ws)")
(assume "v" "w" "vs" "ws")
(ng)
(cases (pt "v=w"))
(assume "v=w")
(ng)
(assume "vs sub ws")
(use "vs sub ws")
(assume "v=w -> F")
(ng)
(use "SubTrans")
(use "SubCons")
;; Proof finished.
(save "SubConsToSub")

;; IncrCons
(set-goal "all wqo,a,as(wqo Head as a -> Incr wqo as -> Incr wqo(a::as))")
(assume "wqo" "a")
(ind)
(ng)
(strip)
(use "Truth")
(assume "a1" "as" "IH")
(ng)
(assume "a>=a1" "IncrHyp")
(split)
(use "a>=a1")
(use "IncrHyp")
;; Proof finished.
(save "IncrCons")

;; ;; IncrCons
;; (set-goal "all wqo,a,as(wqo a Head as -> Incr wqo as -> Incr wqo(a::as))")
;; (assume "wqo" "a")
;; (ind)
;; (ng)
;; (strip)
;; (use "Truth")
;; (assume "a1" "as" "IH")
;; (ng)
;; (assume "a>=a1" "IncrHyp")
;; (split)
;; (use "a>=a1")
;; (use "IncrHyp")
;; ;; Proof finished.
;; (save "IncrCons")

;; IncrConsInv
(set-goal "all wqo,a,as(Incr wqo(a::as) -> Incr wqo as)")
(assume "wqo" "a")
(ind)
(ng)
(strip)
(use "Truth")
(assume "a1" "as" "IH")
(ng)
(assume "Conj")
(use "Conj")
;; Proof finished.
(save "IncrConsInv")

;; WqoIncr
(set-goal "all wqo(all a,b,c(wqo a b -> wqo b c -> wqo a c) ->
 all b,a,as(wqo a b -> Incr wqo(a::as) -> Incr wqo(b::as)))")
(assume "wqo" "Trans" "b" "a")
(ind) ;on as
(strip)
(use "Truth")
(assume "c" "as" "IHas")
(ng)
(assume "wqo a b" "Conj")
(split)
(use "Trans" (pt "a"))
(use "Conj")
(use "wqo a b")
(use "Conj")
;; Proof finished.
(save "WqoIncr")

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
(set-goal "all wqo(all a,b,c(wqo a b -> wqo b c -> wqo a c) -> all vs,as,v,a(
 Incr wqo(a::as) -> Lh as=Lh vs -> LargerW wqo v vs ->
 LargerW wqo(a::v)(as mapcons vs)))")
(assume "wqo" "Trans")
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
(ng #t)
(assume "Conj" "LhHyp" "Lwvvs")
(use "LargerWElim" (pt "wqo") (pt "w") (pt "v") (pt "vs"))
(use "Lwvvs")
;; Emb wqo v w -> LargerW wqo(a1::w)((a::v)::as mapcons vs)
(assume "Evw")
(use "InitLargerW")
(use "GenEmbCons")
(use "Conj")
(use "Evw")
;;   wqo  vs10270  v  vs  IHvs:
;;     all as,v,a(
;;      Incr wqo(a::as) -> 
;;      Lh as=Lh vs -> LargerW wqo v vs -> LargerW wqo(a::v)(as mapcons vs))
;;   as10298  a  as  w  a1  Conj:
;;     wqo a1 a andb Incr wqo(a::as)
;;   LhHyp:Lh as=Lh vs
;;   Lwvvs:LargerW wqo w(v::vs)
;; -----------------------------------------------------------------------------
;; LargerW wqo w vs -> LargerW wqo(a1::w)((a::v)::as mapcons vs)
(assume "Lvws")
(use "GenLargerW")
(use "IHvs")
(use "WqoIncr" (pt "a"))
(use "Trans")
(use "Conj")
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

;; If the lhs us of a (long) usas is is good (because of GLT) and the
;; rhs as of usas is increasing then also
;; (as mapcons Lh as init us)++(Lh rht usas rest lft usas) is good.
;; This (as mapcons Lh as init us)++(Lh rht usas rest lft usas) is sub
;; ws (because of CorrT).  Hence ws is good.

;; (display-pconst "GoodWR")
;; (display-idpc "GoodW")
;; (pp "GoodWElim") ;exists in examplesbarhigfin.scm.
;; ;; GoodW(w::ws) -> (GoodW ws -> Pvar^) -> (LargerW w ws -> Pvar^) -> Pvar^
;; ;; Also there: LargerWMapCons
;; ;; "all w,vs,a(LargerW w vs -> LargerW(a::w)((Cons nat)a map vs))")
;; ;; This has been transferred to mapcons

;; GoodWAppdMapcons
(set-goal "all wqo(all a,b,c(wqo a b -> wqo b c -> wqo a c) -> all ws,as,vs(
 Incr wqo as -> Lh as=Lh vs ->
 GoodW wqo(vs++ws) -> GoodW wqo((as mapcons vs)++ws)))")
(assume "wqo" "Trans" "ws")
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
(assume "v" "vs" "IncrHyp" "LhHyp")
(ng "LhHyp")
(ng #t)
(assume "Gvvsws")
(use "GoodWElim" (pt "wqo") (pt "v") (pt "vs++ws"))
(use "Gvvsws")
(assume "Gvsws")
(use "GenGoodW")
(use "IHas")
(use "IncrConsInv" (pt "a"))
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
(use "LargerWMapcons")
(use "Trans")
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

;; LargerARTrans
(set-goal "all wqo(all a,b,c(wqo a b -> wqo b c -> wqo a c) -> 
 all as,a1,a(wqo a a1 -> LargerAR wqo a as -> LargerAR wqo a1 as))")
(assume "wqo" "Trans")
(ind)
(ng)
(assume "a" "a1" "Useless" "Absurd")
(use "Absurd")
(assume "a" "as" "IH" "a1" "a2")
(assume "a1>=a2")
(ng)
(cases (pt "wqo a a2"))
(ng)
(assume "a2>=a" "Useless")
(assert "wqo a a1")
(use "Trans" (pt "a2"))
(use "a2>=a")
(use "a1>=a2")
(assume "a1>=a")
(simp "a1>=a")
(use "Truth")
(assume "a2>=a -> F")
(ng)
(cases (pt "wqo a a1"))
(strip)
(use "Truth")
(assume "a1>=a -> F" "a2>=as")
(ng)
(use "IH" (pt "a2"))
(use "a1>=a2")
(use "a2>=as")
;; Proof finished.
(save "LargerARTrans")

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

;; LargerARProj
(set-goal "all wqo,a,as,i(i<Lh as -> wqo(i thof as)a -> LargerAR wqo a as)")
(assume "wqo" "a")
(ind)
(ng)
(assume "i" "Absurd" "Useless")
(use "Absurd")
(assume "b" "as" "IH")
(ng)
(cases)
(ng)
(assume "Useless" "a<=b")
(simp "a<=b")
(use "Truth")
(assume "i")
(ng)
(assume "i<Lh as" "as_i<=a")
(cases (pt "wqo b a"))
(strip)
(use "Truth")
(strip)
(use "IH" (pt "i"))
(use "i<Lh as")
(use "as_i<=a")
;; Proof finished.
(save "LargerARProj")

;; HAdm
(set-goal "all wqo,a,v,ws(
 0<Lh v -> H wqo a(v::ws)=[if (wqo Head v a) True (H wqo a ws)])")
(assume "wqo" "a")
(cases)
(assume "ws")
(ng)
(use "Efq")
(assume "b" "v" "ws" "Useless")
(ng)
(use "Truth")
;; Proof finished.
(save "HAdm")

;; LargerARHeadsEqH
(set-goal "all wqo,a,ws(Adm ws -> (LargerAR wqo a Heads ws)=(H wqo a ws))")
(assume "wqo" "a")
(ind)
(ng)
(assume "Trivial")
(use "Trivial")
(assume "v" "ws" "IH")
(ng)
(assume "Conj")
(simp "HAdm")
(simp "IH")
(use "Truth")
(use "Conj")
(use "Conj")
;; Proof finished.
(save "LargerARHeadsEqH")

;; BSeqDefCons
(set-goal "all wqo^,a^,as^
 BSeq wqo^(a^ ::as^)eqd
 [if (LargerAR wqo^ a^ as^) (BSeq wqo^ as^) (a^ ::BSeq wqo^ as^)]")
(assume "wqo^" "a^" "as^")
(use "InitEqD")
;; Proof finished.
(save "BSeqDefCons")

;; LargerARBSeqToLargerAR
(set-goal "all wqo,as,a(LargerAR wqo a(BSeq wqo as) -> LargerAR wqo a as)")
(assume "wqo")
(ind)
(assume "a" "Hyp")
(use "Hyp")
(assume "a" "as" "IH" "a1")
(ng)
(cases (pt "wqo a a1"))
(strip)
(use "Truth")
(assume "wqo a a1 -> F")
(cases (pt "LargerAR wqo a as"))
(ng)
(assume "Useless")
(use "IH")
;; Case LargerAR wqo a as -> F
(assume "LargerAR wqo a as -> F")
(ng)
(simp "wqo a a1 -> F")
(ng)
(use "IH")
;; Proof finished.
(save "LargerARBSeqToLargerAR")

;; LargerARToLargerARBSeq
(set-goal "all wqo(all a,b,c(wqo a b -> wqo b c -> wqo a c) -> 
 all as,a(LargerAR wqo a as -> LargerAR wqo a(BSeq wqo as)))")
(assume "wqo" "Trans")
(ind)
(assume "a" "Hyp")
(use "Hyp")
(assume "a" "as" "IH" "a1")
(ng)
(cases (pt "wqo a a1"))
(ng)
(cases (pt "LargerAR wqo a as"))
(ng)
(assume "LargerAR wqo a as" "a1>=a" "Useless")
(use "IH")
(use "LargerARTrans" (pt "a"))
(use "Trans")
(use "a1>=a")
(use "LargerAR wqo a as")
(assume "a>=as -> F" "a1>=a" "Useless")
(ng)
(simp "a1>=a")
(use "Truth")
(assume "a1>=a -> F")
(ng)
(assume "a1>=as")
(cases (pt "LargerAR wqo a as"))
(assume "a>=as")
(ng)
(use "IH")
(use "a1>=as")
(assume "a>=as -> F")
(ng)
(simp "a1>=a -> F")
(ng)
(use "IH")
(use "a1>=as")
;; Proof finished.
(save "LargerARToLargerARBSeq")

;; LhRhts
(set-goal "all vsass Lh(Rhts vsass)=Lh vsass")
(ind)
(use "Truth")
(assume "vsas" "vsass" "IH")
(ng)
(simp "LhMap")
(use "Truth")
;; Proof finished.
(save "LhRhts")

;; LhRoots
(set-goal "all ts Lh(Roots ts)=Lh ts")
(ind)
(use "Truth")
(assume "t" "ts" "IH")
(ng)
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

(remove-var-name "x" "tx" "txs")

;; LhInsertF
(set-goal "all wqo,ts,v,a Lh(InsertF wqo ts v a)=Lh ts")
(assume "wqo")
(ind)
(ng)
(assume "v" "a")
(use "Truth")
(assume "t" "ts" "IH")
(ng #t)
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
(simp "MapAppd")
(use "Truth")
;; Proof finished.
(save "InsertFAppd")

;; InsertFId
(set-goal "all wqo,a,v,ts(
 (LargerAR wqo a(Heads(Rhts Roots ts)) -> F) -> InsertF wqo ts v a=ts)")
(assume "wqo" "a" "v")
(ind)
(ng)
(strip)
(use "Truth")
(assume "t" "ts" "IH")
(ng)
(cases (pt "wqo Head rht Root t a"))
(ng)
(assume "Useless" "Absurd")
(use "Efq")
(use-with "Absurd" "Truth")
(ng)
(assume "Useless")
(use "IH")
;; Proof finished.
(save "InsertFId")

;; InsertFAppdRight
(set-goal
 "all wqo,a,v,ss,ts((LargerAR wqo a(Heads(Rhts Roots ts)) -> F) ->
   InsertF wqo(ts++ss)v a=ts++InsertF wqo ss v a)")
(assume "wqo" "a" "v" "ss" "ts" "LargerARHyp")
(simp "InsertFAppd")
(assert "InsertF wqo ts v a=ts")
(use "InsertFId")
(use "LargerARHyp")
(assume "EqHyp")
(simp "EqHyp") ;needs "ListLntreeYprodListListNatListNatEqToEqD"
(use "Truth")
;; Proof finished.
(save "InsertFAppdRight")

;; InsertFAppd
(set-goal "all wqo,a,v,ss,ts
 InsertF wqo(ts++ss)v a eqd InsertF wqo ts v a++InsertF wqo ss v a")
(assume "wqo" "a" "v" "ss")
(ind)
(ng)
(use "InitEqD")
(assume "t" "ts" "IH")
(ng #t)
(simp "MapAppd")
(use "InitEqD")
;; Proof finished.
(save "InsertFAppdEqD")

;; InsertFEqInsertT
(set-goal "all wqo,a,t,v(
 wqo Head rht Root t a -> InsertF wqo(t:)v a=(InsertT wqo t v a):)")
(assume "wqo" "a" "t" "v" "WqoHyp")
(ng)
(simp "WqoHyp")
(use "Truth")
;; Proof finished.
(save "InsertFEqInsertT")

;; RootInsertTEqRoot
(set-goal "all wqo,v,a,t Root(InsertT wqo t v a)eqd Root t")
(assume "wqo" "v" "a")
(use "AllTotalIntro")
(assume "t^" "Tt")
(elim "Tt")
(ng #t)
(strip)
(use "InitEqD")
;; Proof finished.
(save "RootInsertTEqRoot")

;; RootsInsertFEqRoots
(set-goal "all wqo,v,a,ts Roots(InsertF wqo ts v a)eqd Roots ts")
(assume "wqo" "v" "a")
(ind)
(ng #t)
(use "InitEqD")
(assume "t" "ts" "IH")
(ng #t)
(cases (pt "wqo Head rht Root t a"))
(ng #t)
(simp "IH")
(simp "RootInsertTEqRoot")
(strip)
(use "InitEqD")
(ng #t)
(simp "IH")
(strip)
(use "InitEqD")
;; Proof finished.
(save "RootsInsertFEqRoots")

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
 all t(HtT t<n -> CorrT wqo ws t -> wqo Head rht Root t a -> 
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
(assume "WqoHyp")
(ng "WqoHyp")
(simp "InsertT0CompRule")
(cases (pt "(LargerAR wqo a Heads(Rhts Roots Subtrees t))"))
;; Case True
(assume "LargerARHyp")
(assert "[if True
        (InsertF wqo Subtrees t v a)
        (NewTree((v::lft Root t)pair a::rht Root t)::Subtrees t)]eqd
        (InsertF wqo Subtrees t v a)")
 (use "InitEqD")
(assume "Assertion")
(simp "Assertion")
(drop "Assertion")
(simp "CorrT0CompRule")
(split)
;; Lh rht Root t<=Lh lft Root t
(use "CorrHyp")
(split)
;; Incr wqo rht Root t
(use "CorrHyp")
(split)
;; IncrExts wqo Roots(InsertF wqo Subtrees t v a)Root t
(simp "RootsInsertFEqRoots")
(use "CorrHyp")
(split)
;; (rht Root t mapcons Lh rht Root t init lft Root t)++
;;      (Lh rht Root t rest lft Root t)sub
;;      ((a::v)::ws)
(use "SubTrans" (pt "ws"))
(use "CorrHyp")
(use "Truth")
;; CorrF wqo((a::v)::ws)(InsertF wqo Subtrees t v a)
(use "IH")
(use "HtF Subtrees t<n")
(use "CorrHyp")
;; Case False
(assume "NotLargerARHyp")
(ng #t)
(split)
;; Lh rht Root t<=Lh lft Root t
(use "CorrHyp")
(split)
;; Incr wqo rht Root t
(use "CorrHyp")
(split)
(split)
;; wqo Head rht Root t a
(use "WqoHyp")
;; IncrExts wqo Roots Subtrees t Root t
(use "CorrHyp")
(split)
;; (rht Root t mapcons Lh rht Root t init lft Root t)++
;;      (Lh rht Root t rest lft Root t)sub
;;      ((a::v)::ws)
(use "SubTrans" (pt "ws"))
(use "CorrHyp")
(use "Truth")
(split)
(split)
;; Lh rht Root t<=Lh lft Root t
(use "CorrHyp")
(split)
;; Incr wqo(a::rht Root t)
(use "IncrCons")
(use "WqoHyp")
(use "CorrHyp")
;; (rht Root t mapcons Lh rht Root t init lft Root t)++
;;      (Lh rht Root t rest lft Root t)sub 
;;      ws
(use "CorrHyp")
;; CorrF wqo((a::v)::ws)Subtrees t
(use "CorrFCons")
(use "CorrHyp")
;; Case ts
(ind)
(ng #t)
(strip)
(use "Truth")
(assume "t" "ts" "IHts" "HtBound" "CorrHyp")
(ng "HtBound")
(ng "CorrHyp")
(simp "InsertFCons")
(cases (pt "(wqo Head rht Root t a)"))
;; Case 1
(assume "wqo Head rht Root t a")
(ng #t)
(split)
(use "IH")
(use "NatLeLtTrans" (pt "HtT t max HtF ts"))
(use "NatMaxUB1")
(use "HtBound")
(use "CorrHyp")
(use "wqo Head rht Root t a")
;; CorrF wqo((a::v)::ws)
;;      (([t][if (wqo Head rht Root t a) (InsertT wqo t v a) t])map ts)
(use "IH")
(use "NatLeLtTrans" (pt "HtT t max HtF ts"))
(use "NatMaxUB2")
(use "HtBound")
(use "CorrHyp")
;; Case 2
(assume "wqo Head rht Root t a -> F")
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
(set-goal "all wqo,ws,t,a,v(CorrT wqo ws t -> wqo Head rht Root t a -> 
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
(cases (pt "H wqo a ws"))
(assume "H wqo a ws")
(simp "ForestConsInsertFDef")
;; CorrF wqo((a::v)::ws)(InsertF wqo(Forest wqo ws)v a)
(use "CorrFInsertF")
(use "IHws")
(use "H wqo a ws")
(assume "H wqo a ws -> F")
(simp "ForestConsNewDef")
;; CorrF wqo((a::v)::ws)(NewTree((v::ws)pair a:)::Forest wqo ws)
(ng)
(use "CorrFCons")
(use "IHws")
(use "H wqo a ws -> F")
;; Proof finished.
(save "CorrFForest")

;; CorrGoodWAux
(set-goal"all wqo,ws(all a,b,c(wqo a b -> wqo b c -> wqo a c) -> all n(
 all t(HtT t<n -> CorrT wqo ws t -> GLT wqo t -> GoodW wqo ws) &
 all ts(HtF ts<n -> CorrF wqo ws ts -> GLF wqo ts -> GoodW wqo ws)))")
(assume "wqo" "ws" "Trans")
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
;; 0<n -> 
;;      Lh as<=Lh(vs++ws0)andb Incr wqo as andb(as mapcons vs)++ws0 sub ws -> 
;;      GoodWR wqo(vs++ws0) -> GoodW wqo ws
(assume "0<n" "Conj" "GRvsws0")
(use "GoodWSub" (pt "(as mapcons vs)++ws0"))
(use "Conj")
(use "GoodWAppdMapcons")
(use "Trans")
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
;; all t0,ts0(
;;       ts=(t0::ts0) -> 
;;       HtF(t0::ts0)<n -> 
;;       Lh as<=Lh us andb 
;;       Incr wqo as andb 
;;       IncrExts wqo Roots(t0::ts0)Root t andb
;;       (as mapcons Lh as init us)++(Lh as rest us)sub ws andb 
;;       CorrF wqo ws(t0::ts0) -> 
;;       GLT wqo(Root t%t0::ts0) -> GoodW wqo ws)
(assume "t1" "ts1" "tsProp" "HtBound" "Conj""GLTHyp")
(use-with "IH" 'right (pt "ts") "?" "?" "?")
(simp "tsProp")
(use "HtBound")
(simp "tsProp")
(use "Conj")
(simp "tsProp")
(ng "GLTHyp")
(use "GLTHyp")
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

;; GoodWForestToGoodW (for Lemma 5.1i)
(set-goal  "all wqo,ws(all a,b,c(wqo a b -> wqo b c -> wqo a c) -> 
 GLF wqo(Forest wqo ws) -> GoodW wqo ws)")
(assume "wqo" "ws" "Trans")
(use "CorrGoodWAux" (pt "Succ HtF(Forest wqo ws)"))
(use "Trans")
(use "Truth")
(use "CorrFForest")
;; Proof finished.
(save "GoodWForestToGoodW")

;; GLFToExGLT
(set-goal "all wqo,ts(GLF wqo ts -> ex i(i<Lh ts & GLT wqo(i thof ts)))")
(assume "wqo")
;; Induction on ts
(ind)
(ng)
(use "Efq")
(assume "t" "ts" "IHts")
(ng)
(cases (pt "GLT wqo t"))
(assume "GLTt" "Useless")
(ex-intro "0")
(ng)
(split)
(use "Truth")
(use "GLTt")
(assume "Useless" "GLFHyp")
(inst-with-to "IHts" "GLFHyp" "InstIH")
(by-assume "InstIH" "i" "iProp")
(ex-intro "Succ i")
(ng)
(use "iProp")
;; Proof finished.
(save "GLFToExGLT")

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

;; InitIndGLT
(set-goal "all wqo,vs,as(GoodW wqo vs -> GLT wqo(NewTree(vs pair as)))")
(assume "wqo" "vs" "as" "Gvs")
(ng)
(use "GoodWToGoodWR")
(use "Gvs")
;; Proof finished.
(save "InitIndGLT")

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

;; InitIndGLF
(set-goal "all wqo,t,ts(GLT wqo t -> GLF wqo(t::ts))")
(assume "wqo" "t" "ts")
(ng)
(assume "GLTt")
(simp "GLTt")
(use "Truth")
;; Proof finished.
(save "InitIndGLF")

;; GenIndGLF
(set-goal "all wqo,t,ts(GLF wqo ts -> GLF wqo(t::ts))")
(assume "wqo" "t" "ts")
(ng)
(assume "GLFts")
(simp "GLFts")
(use "Truth")
;; Proof finished.
(save "GenIndGLF")

;; GoodWProjForestToGoodW (Lemma 5.1i)
(set-goal  "all wqo,ws(all a,b,c(wqo a b -> wqo b c -> wqo a c) -> 
 all i(i<Lh(Forest wqo ws) -> GLT wqo(i thof(Forest wqo ws)) -> GoodW wqo ws))")
(assume "wqo" "ws" "Trans" "i" "LhHyp" "GLTHyp")
(use "GoodWForestToGoodW")
(use "Trans")
(use "ExGLTToGLF" (pt "i"))
(use "LhHyp")
(use "GLTHyp")
;; Proof finished.
(save "GoodWProjForestToGoodW")

;; LhForest
(set-goal "all wqo,a,v,ws Lh(Forest wqo((a::v)::ws))=
 [if (H wqo a ws) (Lh(Forest wqo ws)) (Succ Lh(Forest wqo ws))]")
(assume "wqo" "a" "v" "ws")
(ng)
(cases (pt "(H wqo a ws)"))
(ng)
(assume "Useless")
(use "LhInsertF")
(ng)
(strip)
(use "Truth")
;; Proof finished.
(save "LhForest")

;; BSeqHeadsEqRhtsRootsForest (Lemma 5.1ii)
(set-goal "all wqo,ws(Adm ws ->
 BSeq wqo Heads ws=Heads(Rhts Roots(Forest wqo ws)))")
(assume "wqo")
(ind)
(ng)
(assume "Trivial")
(use "Trivial")
(cases) ;on v
(ng #t)
(assume "ws" "Useless")
(use "Efq")
(assume "a" "v" "ws" "IH" "Adm ws")
(ng "Adm ws")
;; BSeq wqo Heads((a::v)::ws)=Heads(Rhts Roots(Forest wqo((a::v)::ws)))
(assert "Heads((a::v)::ws)=(a::Heads ws)")
 (use "Truth")
(assume "Heads((a::v)::ws)=(a::Heads ws)")
(simp "Heads((a::v)::ws)=(a::Heads ws)")
(drop "Heads((a::v)::ws)=(a::Heads ws)")
;; BSeq wqo(a::Heads ws)=Heads(Rhts Roots(Forest wqo((a::v)::ws)))
(cases (pt "H wqo a ws"))
;; Case "H wqo a ws"
(assume "H wqo a ws")
(simp "BSeqDefCons")
(simp "LargerARHeadsEqH")
(simp "H wqo a ws")
(simp "ForestConsInsertFDef")
(simp "RootsInsertFEqRoots")
(use "IH")
(use "Adm ws")
(use "H wqo a ws")
(use "Adm ws")
;; Case "H wqo a ws -> F"
(assume "H wqo a ws -> F")
(simp "BSeqDefCons")
(simp "LargerARHeadsEqH")
(simp "H wqo a ws -> F")
(simp "ForestConsNewDef")
(use "IH")
(use "Adm ws")
(use "H wqo a ws -> F")
(use "Adm ws")
;; Proof finished.
(save "BSeqHeadsEqRhtsRootsForest")

;; RootProjEqHeadRhtRoot
(set-goal "all t Root(Proj t)=Head rht Root t")
(use "AllTotalIntro")
(assume "t^" "Tt")
(elim "Tt")
(use "AllTotalElim")
(ng)
(strip)
(use "Truth")
;; Proof finished.
(save "RootProjEqHeadRhtRoot")

;; RootsProjFEqHeadsRhtsRoots
(set-goal "all ts Roots(ProjF ts)=Heads(Rhts Roots ts)")
(ind)
(ng)
(use "Truth")
(assume "t" "ts" "IH")
(ng)
(split)
(use "RootProjEqHeadRhtRoot")
(use "IH")
;; Proof finished.
(save "RootsProjFEqHeadsRhtsRoots")

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
(cases (pt "LargerAR wqo a as"))
(assume "a>=as")
(ng #t)
(use "IHas")
(assume "a>=as -> F")
(ng #t)
(assert "LargerAR wqo a(BSeq wqo as) -> F")
(assume "a>=BSeq as")
(use "a>=as -> F")
(use "LargerARBSeqToLargerAR")
(use "a>=BSeq as")
(assume "a>=BSeq as -> F")
(simp "a>=BSeq as -> F")
(ng)
(use "IHas")
;; Proof finished.
(save "NotGoodARBSeq")

;; GoodARProj
(set-goal "all wqo,as,i,j(
 i<j -> j<Lh as -> wqo(j thof as)(i thof as) -> GoodAR wqo as)")
(assume "wqo")
(ind)
(ng)
(assume "i" "j" "i<j" "Absurd" "Useless")
(use "Absurd")
(assume "a" "as" "IH")
(cases)
(ng)
(cases)
(ng)
(use "Efq")
(assume "j")
(ng)
(assume "Useless" "j<Lh as" "a>=as_j")
(assert "LargerAR wqo a as")
 (use "LargerARProj" (pt "j"))
 (use "j<Lh as")
 (use "a>=as_j")
(assume "LargerAR wqo a as")
(simp "LargerAR wqo a as")
(use "Truth")
(assume "i")
(cases)
(ng)
(use "Efq")
(assume "j")
(ng)
(assume "i<j" "j<Lh as" "as_i>=as_j")
(cases (pt "LargerAR wqo a as"))
(strip)
(use "Truth")
(strip)
(ng)
(use "IH" (pt "i") (pt "j"))
(use "i<j")
(use "j<Lh as")
(use "as_i>=as_j")
;; Proof finished.
(save "GoodARProj")

;; GoodAToGoodAR
(set-goal "all wqo,as(GoodA wqo as -> GoodAR wqo as)")
(assume "wqo" "as" "Gas")
(elim "Gas")
(assume "wqo1" "a" "as1" "Laas1")
(ng)
(simp "Laas1")
(use "Truth")
(assume "wqo1" "a" "as1" "Useless" "GRas1")
(ng)
(simp "GRas1")
(ng)
(use "Truth")
;; Proof finished.
(save "GoodAToGoodAR")

;; GoodARToGoodA
(set-goal "all wqo,as(GoodAR wqo as -> GoodA wqo as)")
(assume "wqo")
(ind)
(ng)
(use "Efq")
(assume "a" "as" "IHas")
(ng)
(cases (pt "LargerAR wqo a as"))
(ng)
(assume "LRaas" "Useless")
(use "InitGoodA")
(use "LRaas")
(assume "Useless" "GRas")
(use "GenGoodA")
(use-with "IHas" "GRas")
;; Proof finished.
(save "GoodARToGoodA")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Main propositions (c.r.)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
;; BarWToGoodInit
(set-goal
 "allnc wqo,ws(BarW wqo ws -> all f,n(Rev(f fbar n)=ws ->
 ex m GoodW wqo(Rev(f fbar m))))")
(assume "wqo" "vs" "Bvs")

;; Ind(BarW)
(elim "Bvs")

;; 1.  GoodW ws
(assume "ws" "Gws" "f" "n" "Ifnws")
(ex-intro (pt "n"))
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

(add-var-name "gw" (py "list nat=>treeW"))
(add-var-name "hwfa" (py "list nat=>(nat=>list nat)=>nat=>nat"))

(define eterm (proof-to-extracted-term (theorem-name-to-proof "BarWToGoodInit")))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [treeW]
;;  (Rec treeW=>(nat=>list nat)=>nat=>nat)treeW([f,a]a)
;;  ([gw,hwfa,f,a]hwfa(f a)f(Succ a))

;; Explanation.  The recursion operator on treeW with value type alpha
;; has type

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

;; BarFNil (Lemma 5.2i)
(set-goal "allnc wqo BarF wqo(Nil lntree(list list nat yprod list nat))")
(assume "wqo")
(use "GenBarF")
(ng)
(assume "tas" "a" "v" "tas=[]")
(simp "tas=[]")
(ng)
(use "Efq")
;; Proof finished.
(save "BarFNil")

(define eterm (proof-to-extracted-term (theorem-name-to-proof "BarFNil")))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; CGenBarF([tas,a,v]CInitBarF)

;; BarFAppdAux
(set-goal "all wqo allnc ts(BarF wqo ts ->
     allnc ss(BarF wqo ss ->
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
(assume "LargerARras")
;; Cases on LargerAR wqo a Roots tas.  If so, then ts1 is changed.
(cases (pt "LargerAR wqo a Roots tas"))
;; Case 2.  ts1 changed.
(assume "LargerARtas")
(simp "InsertFAppd")
(use "IHtFb" (pt "tas") (pt "m"))
(use "tasProp")
(use "LargerARtas")
;; Cases on whether ss1 changes
(cases (pt "LargerAR wqo a Roots sas"))
;; Case ss1 changes
(assume "LargerARsas")
(use "IHssa" (pt "sas"))
(use "sasProp")
(use "LargerARsas")
;; Case ss1 does not change
(assume "LargerARsas -> F")
(simp "InsertFId")
(use "GenBarF")
(use "IHssa")
(simp "<-" "RootsProjFEqHeadsRhtsRoots")
(simp "<-" "sasProp")
(use "LargerARsas -> F")
(simp "LhInsertF")
(use "mDef")
;; Case 1.  ts1 does not change.
(assume "LargerARtas -> F")
(simp "InsertFAppdRight")
(use "IHssb" (pt "sas") (pt "m"))
(use "sasProp")
(use "LargerARAppdCases" (pt "wqo") (pt "a") (pt "Roots tas") (pt "Roots sas")
     "?" "?" "?")
(use "LargerARras")
(assume "LargerARtas")
(use "Efq")
(use-with "LargerARtas -> F" "LargerARtas")
(assume "LargerARsas")
(use "LargerARsas")

(simp "LhInsertF")
(use "mDef")

(simp "<-" "RootsProjFEqHeadsRhtsRoots")
(simp "<-" "tasProp")
(use "LargerARtas -> F")
;; Proof finished.
(save "BarFAppdAux")

(define eterm
  (proof-to-extracted-term (theorem-name-to-proof "BarFAppdAux")))

(add-var-name "g" (py "list lntree nat=>nat=>list nat=>treeF"))
(add-var-name "htat" (py "list lntree nat=>nat=>list nat=>treeF=>nat=>treeF"))
(add-var-name "hat" (py "list lntree nat=>nat=>list nat=>nat=>treeF"))

(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [wqo,treeF]
;;  (Rec treeF=>treeF=>nat=>treeF)treeF([treeF0,a]CInitBarF)
;;  ([g,htat,treeF0]
;;    (Rec treeF=>nat=>treeF)treeF0([a]CInitBarF)
;;    ([g0,hat,a]
;;      CGenBarF
;;      ([tas,a0,v]
;;        [if (LargerAR wqo a0 Roots((Lh tas--a)init tas))
;;          (htat((Lh tas--a)init tas)a0 v
;;          [if (LargerAR wqo a0 Roots((Lh tas--a)rest tas))
;;            (g0((Lh tas--a)rest tas)a0 v)
;;            (CGenBarF g0)]
;;          a)
;;          (hat((Lh tas--a)rest tas)a0 v a)])))

;; Explanation.  The recursion operator on treeF with value type alpha
;; has type

(pp (term-to-type (pt "(Rec treeF=>alpha)")))

;; treeF=>alpha=>((list lntree nat=>nat=>list nat=>treeF)=>
;;                (list lntree nat=>nat=>list nat=>alpha)=>alpha)=>alpha

;; Let CInitBarF: treeF and CGenBarF: (list nat=>treeF)=>treeF be the
;; constructors of treeF.  Then Phi := (Rec treeF=>alpha) is given by
;; the recursion equations

;; Phi(CInitBarF) = G,
;; Phi(CGenBarF(g)) = H(g, lambda_v Phi(g(v)))

;; Here the value type of the first recursion is treeF=>nat=>treeF, and

;; G = lambda_treeF,a CInitBarF
;; H(g,htat) = lambda_treeF0 K(g, htat, treeF0)

;; with K(g, htat, treeF0) given by

;;    ([g0,hat,a]
;;      CGenBarF
;;      ([tas,a0,v]
;;        [if (LargerAR wqo a0 Roots((Lh tas--a)init tas))
;;          (htat((Lh tas--a)init tas)a0 v
;;          [if (LargerAR wqo a0 Roots((Lh tas--a)rest tas))
;;            (g0((Lh tas--a)rest tas)a0 v)
;;            (CGenBarF g0)]
;;          a)
;;          (hat((Lh tas--a)rest tas)a0 v a)]))

;; The inner recursion is on treeF again, with value type nat=>treeF, and

;; G1 = lambda_a CInitBarF
;; H1(g0, hat) = lambda_a CGenBarF ...

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
;;        [if (LargerAR wqo a0 Roots((Lh tas--a)init tas))
;;          (htat((Lh tas--a)init tas)a0 v
;;          [if (LargerAR wqo a0 Roots((Lh tas--a)rest tas))
;;            (g0((Lh tas--a)rest tas)a0 v)
;;            (CGenBarF g0)]
;;          a)
;;          (hat((Lh tas--a)rest tas)a0 v a)])))

;; BarFNew (Lemma 5.3)
(set-goal
 "all wqo(BarA wqo(Nil nat) ->
  allnc ws(BarW wqo ws -> 
  all as BarF wqo((NewTree(ws pair as)):)))")
(assume "wqo" "BarANil" "ws0" "Bws0")
;; Ind(BarA)
(elim "Bws0")
;; 1.1
(assume "vs" "Gvs" "as0")
(use "InitBarF" (pt "0"))
(use "Truth")
(ng)
(use "GoodWToGoodWR")
(use "Gvs")
;; 1.2
(assume "ws" "BHyp" "IH1" "as0")
;; We show more generally
(assert "allnc as(
 BarA wqo as -> 
 (GoodAR wqo as -> F) -> 
 allnc ts(
  BarF wqo ts -> 
  as=Heads(Rhts Roots ts) -> BarF wqo(((ws pair as0)%ts):)))")
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
(simp "tasDef")
(assume "GHyp")
(ng "GHyp")
(simp "InsertFEqInsertT")
;;   as1Def:as1=Heads(Rhts Roots ts1)
;;   tas  a  {v}  tasDef:tas=(Head as0%ProjF ts1):
;;   GHyp:wqo a Head as0
;; -----------------------------------------------------------------------------
;; ?_35:BarF wqo((InsertT wqo((ws pair as0)%ts1)v a):)

(assert "as1=Roots(Subtrees Head tas)")
 (simp "as1Def")
 (simp "tasDef")
 (ng #t)
 (simp "RootsProjFEqHeadsRhtsRoots")
 (ng #t)
 (use "Truth")
(assume "as1Char")
;; Now case distinction on the definition of InsertT
(cases (pt "LargerAR wqo a Roots(Subtrees Head tas)"))
;; Case 1.
(simp "<-" "as1Char")
(assume "a>=as1")
(assert "all vsas,ts,v,a(LargerAR wqo a(Heads(Rhts Roots ts)) ->
 InsertT wqo(vsas%ts)v a = (vsas%InsertF wqo ts v a))")
 (strip)
 (ng #t)
 (simp 17)
 (ng #t)
 (use "Truth")
(assume "Assertion")
(simp "Assertion")
(get 57)
(simp "<-" "as1Def")
(use "a>=as1")
(use "IH3b" (pt "Subtrees Head tas"))
(simp "tasDef")
(ng #t)
(use "Truth")
(simp "<-" "as1Char")
(use "a>=as1")
(simp "as1Def")
(simp "RootsInsertFEqRoots")
(use "Truth")
;; Case 2.
(simp "<-" "as1Char")
(assume "a>=as1 -> F")
(assert "all vsas,ts,v,a((LargerAR wqo a(Heads(Rhts Roots ts)) -> F) ->
 InsertT wqo(vsas%ts)v a = (vsas%NewTree((v::lft vsas)pair a::rht vsas)::ts))")
 (strip)
 (ng #t)
 (simp 17)
 (ng #t)
 (use "Truth")
(assume "Assertion")
(simp "Assertion")
(get 77)
(simp "<-" "as1Def")
(use "a>=as1 -> F")
(use "IH2b" (pt "a"))
(assume "Gaas1")
(use "a>=as1 -> F")
(use "GoodARConsBad")
(use "Gaas1")
(use "Bas1")
;; BarF wqo(NewTree((v::lft(ws pair as0))pair a::rht(ws pair as0))::ts1)
;; Use BarFAppd
(assert "BarF wqo ts1")
 (use "GenBarF")
 (use "IH3a")
(assume "BarF wqo ts1")
(assert "BarF wqo((NewTree((v::lft(ws pair as0))pair a::rht(ws pair as0))):)")
(use "IH1")
(assume "BarF wqo((NewTree((v::lft(ws pair as0))pair a::rht(ws pair as0))):)")
;; Now we can use 5.2
(use "BarFAppd" (pt "Lh Subtrees Head tas"))
(use "BarF wqo((NewTree((v::lft(ws pair as0))pair a::rht(ws pair as0))):)")
(use "BarF wqo ts1")
(simp "tasDef")
(ng #t)
(use "LhProjF")
(ng #t)
(simp "as1Def")
(ng #t)
(use "Truth")
(ng #t)
(use "GHyp")
;; Now the assertion above is proved
(assume "Assertion")
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

;; (display-default-varnames)

(add-var-name "hw" (py "list nat=>list nat=>treeF"))
(add-var-name "ga" (py "nat=>treeA")) 
(add-var-name "hatt" (py "nat=>treeF=>treeF"))

(animate "BarFNil")

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
;;          [if (LargerAR wqo a Roots Subtrees Head tas)
;;            (g0 Subtrees Head tas a v0)
;;            (hatt a
;;            (cBarFAppd wqo(hw v0(a::v))(CGenBarF g)Lh Subtrees Head tas))])))
;;    (CGenBarF([tas,a,v0]CInitBarF)))

;; This time we have three nested recursions: an outer one
;; on treeW with value type list nat=>treeF, then
;; on treeA with value type treeF=>treeF, and innermost
;; on treeF with value type treeF.
;; This corresponds to the elimination axioms used in the proof.  

;; Notice that the computational content cBarFAppd of the theorem
;; BarFAppd appears as a constant inside the present neterm.

;; Idea: prove commutation of Insert and Proj by induction on the
;; height of the nested tree.

;; ProjFDefCons
(set-goal "all t^,ts^ ProjF(t^ ::ts^)eqd(Proj t^ ::ProjF ts^)")
(assume "t^" "ts^")
(use "InitEqD")
;; Proof finished.
(save "ProjFDefCons")

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

;; ProjNewTreeEqNewATreeHead
(set-goal "all vsas^ Proj(NewTree vsas^)eqd(NewATree(Head rht vsas^))")
(assume "vsas^")
(use "InitEqD")
;; Proof finished.
(save "ProjNewTreeEqNewATreeHead")

;; InsertAProjEqProjInsertAux
(set-goal "all wqo,a,v,n(
 all t(
 HtT t<n -> InsertAT wqo(Proj t)a=Proj(InsertT wqo t v a)) &
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
(simp "Proj0CompRule")
(simp "InsertAT0CompRule")
(simp "InsertT0CompRule")
(simp "Proj0CompRule")
(simp "IH")
(simp "RootsProjFEqHeadsRhtsRoots")
;; (simp "ProjFIf")
;; simp does not work.  Check.  But there is a workaround:
(assert "(ProjF
      [if (LargerAR wqo a Heads(Rhts Roots Subtrees t))
        (InsertF wqo Subtrees t v a)
        (NewTree((v::lft Root t)pair a::rht Root t)::Subtrees t)])=
      ([if (LargerAR wqo a Heads(Rhts Roots Subtrees t))
        (ProjF(InsertF wqo Subtrees t v a))
        (ProjF(NewTree((v::lft Root t)pair a::rht Root t)::Subtrees t))])")
 (simp "ProjFIf") ;simp works
 (use "Truth")
(assume "Assertion")
(simp "Assertion")
(simp "ProjFDefCons")
(simp "ProjNewTreeEqNewATreeHead")
(ng #t)
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
(simp "ProjFDefCons")
(simp "InsertAFCons")
(simp "InsertFCons")
(simp "RootProjEqHeadRhtRoot")
(simp "ProjFIf")
(simp "ProjFDefCons")
(simp "ProjFDefCons")
(simp "IH")
(simp "IH")
(use "Truth")
(use "NatLeLtTrans" (pt "HtT t max HtF ts"))
(use "NatMaxUB2")
(use "HtBound")
(use "NatLeLtTrans" (pt "HtT t max HtF ts"))
(use "NatMaxUB1")
(use "HtBound")
;; Proof finished.
(save "InsertAProjEqProjInsertAux")

;; InsertATProjEqProjInsertT
(set-goal "all wqo,a,v,t InsertAT wqo(Proj t)a=Proj(InsertT wqo t v a)")
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

;; HigmanAux (Lemma 5.4)
(set-goal "all wqo(all a,b,c(wqo a b -> wqo b c -> wqo a c) -> 
  BarA wqo(Nil nat) ->
  allnc as(BarA wqo as ->
  allnc ts(BarF wqo ts ->
  all ws(Adm ws -> BSeq wqo(Heads ws)=as ->
  all tas(tas=ProjF ts ->
  Forest wqo ws=ts -> BarW wqo ws)))))")
(assume "wqo" "Trans" "BarANil" "as0" "Bas0")
(elim "Bas0")

;; 1.1
(assume "as" "Gas" "ts" "Bts" "ws" "Adm ws" "BHws=as" "tas" "tasDef")
(use "Efq")
(use "NotGoodARBSeq" (pt "wqo") (pt "Heads ws"))
(simp "BHws=as")
(use "Gas")

;; 1.2
(assume "as" "IH1a" "IH1b" "ts0" "Bts0")
(drop "IH1a")

;; Ind(BarF)
(elim "Bts0")

;; 2.1
(assume "ts" "i" "i<Lts" "GHyp" "ws" "Adm ws" "BHws=as" "tas" "tasDef" "Fws=ts")
(use "InitBarW")
(use "GoodWProjForestToGoodW" (pt "i"))
(use "Trans")
(simp "Fws=ts")
(use "i<Lts")
(simp "Fws=ts")
(use "GHyp")

;; 2.2
(assume "ts" "IH2a" "IH2b" "ws" "Adm ws" "BHws=as" "tas" "tasDef" "Fws=ts")
(use "GenBarW")

;; Ind(v)
(ind)

;; 3.1
(use "BarWConsNil")

;; 3.2
(assume "a" "v" "IH3")

;; BarW((a::v)::ws)

(cases (pt "H wqo a ws"))
;; Case 1.  H wqo a ws
(assume "H wqo a ws")
(use "IH2b" (pt "tas") (pt "a") (pt "v")  (pt "InsertAF wqo tas a"))
(use "tasDef")
(simp "tasDef")
(simp "RootsProjFEqHeadsRhtsRoots")
(simp "<-" "Fws=ts")
(simp "<-" "BSeqHeadsEqRhtsRootsForest")
(use "LargerARToLargerARBSeq")
(use "Trans")
;; LargerAR wqo a Heads ws
(simp "LargerARHeadsEqH")
(use "H wqo a ws")
(use "Adm ws")
(use "Adm ws")
(ng #t)
(use "Adm ws")
;; BSeq wqo Heads((a::v)::ws)=as
(ng #t)
(simp "BHws=as")
(simp "LargerARHeadsEqH")
(simp "H wqo a ws")
(use "Truth")
(use "Adm ws")
;; InsertAF wqo tas a=ProjF(InsertF wqo ts v a)
(simp "tasDef")
(use "InsertAFProjFEqProjFInsertF")
;; Forest wqo((a::v)::ws)=InsertF wqo ts v a
(simp "ForestConsInsertFDef")
(simp "Fws=ts")
(use "Truth")
(use "H wqo a ws")
;; Case 2.  H wqo a ws -> F
(assume "H wqo a ws -> F")
(assert "BarF wqo ts")
(use "GenBarF")
(use "IH2a")
(assume "BarF wqo ts")
(use "IH1b" (pt "a") (pt "NewTree((v::ws)pair a:)::ts")
     (pt "(NewATree a)::tas"))
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
;; BSeq wqo(Heads((a::v)::ws))=(a::as)
(ng #t)
(simp "BHws=as")
(simp "LargerARHeadsEqH")
(simp "H wqo a ws -> F")
(use "Truth")
(use "Adm ws")
;; (NewATree a::tas)=ProjF(NewTree((v::ws)pair a:)::ts)
(simp "tasDef")
(ng #t)
(use "Truth")
(ng #t)
(simp "H wqo a ws -> F")
(ng #t)
(use "Fws=ts")
;; Proof finished.
(save "HigmanAux")
;; (cdp) ;ok

(define eterm (proof-to-extracted-term (theorem-name-to-proof "HigmanAux")))

(add-var-name
 "h"
 (py "list lntree nat=>nat=>list nat=>list list nat=>list lntree nat=>treeW"))

(add-var-name "ha" (py "nat=>treeF=>list list nat=>list lntree nat=>treeW"))

(animate "BarWConsNil")

(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [wqo,treeA,treeA0]
;;  (Rec treeA=>treeF=>list list nat=>list lntree nat=>treeW)treeA0
;;  ([treeF,ws,tas]CInitBarW)
;;  ([ga,ha,treeF]
;;    (Rec treeF=>list list nat=>list lntree nat=>treeW)treeF
;;    ([ws,tas]CInitBarW)
;;    ([g,h,ws,tas]
;;      CGenBarW
;;      ([v] (Rec list nat=>treeW)v(CGenBarW([v0]CInitBarW))
;;        ([a,v0,treeW]
;;          [if (H wqo a ws)
;;            (h tas a v0((a::v0)::ws)
;;            (([ta][if (wqo a Root ta) (InsertAT wqo ta a) ta])map tas))
;;            (ha a
;;            (cBarFAppd wqo(cBarFNew wqo treeA treeW a:)(CGenBarF g)Lh tas)
;;            ((a::v0)::ws)
;;            ((a%(Nil lntree nat))::tas))]))))

;; Again we have tree nested recursions, on treeA, then treeF and
;; innermost on list nat.  This corresponds to the elimination axioms
;; used in the proof.  Notice again that the computational content
;; cBarFAppd, cBarFNew of the theorems BarFAppd,BarFNew appear as
;; constants inside the present neterm.

;; Higman
(set-goal "all wqo(all a,b,c(wqo a b -> wqo b c -> wqo a c) -> 
  BarA wqo(Nil nat) -> BarW wqo(Nil list nat))")
(assume "wqo" "Trans" "BarANil")
(use "HigmanAux"
     (pt "(Nil nat)")
     (pt "(Nil lntree(list list nat yprod list nat))")
     (pt "(Nil lntree nat)"))
(use "Trans")
(use "BarANil")
(use "BarANil")
(use "BarFNil")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
;; Proof finished.
(save "Higman")

(define eterm (proof-to-extracted-term (theorem-name-to-proof "Higman")))

(animate "HigmanAux")
(animate "BarWConsNil")

(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [wqo,treeA]
;;  (Rec treeA=>treeF=>list list nat=>list lntree nat=>treeW)treeA
;;  ([treeF,ws,tas]CInitBarW)
;;  ([ga,ha,treeF]
;;    (Rec treeF=>list list nat=>list lntree nat=>treeW)treeF
;;    ([ws,tas]CInitBarW)
;;    ([g,h,ws,tas]
;;      CGenBarW
;;      ([v](Rec list nat=>treeW)v(CGenBarW([v0]CInitBarW))
;;        ([a,v0,treeW]
;;          [if (H wqo a ws)
;;            (h tas a v0((a::v0)::ws)
;;             (([ta][if (wqo Root ta a) (InsertAT wqo ta a) ta])map tas))
;;            (ha a
;;             (cBarFAppd wqo(cBarFNew wqo treeA treeW a:)(CGenBarF g)Lh tas)
;;             ((a::v0)::ws)
;;             ((a%(Nil lntree nat))::tas))]))))
;;  (CGenBarF([tas,a,v]CInitBarF))
;;  (Nil list nat)
;;  (Nil lntree nat)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; We consider two well quasi orderings on the natural numbers:
;; equality modulo m, and the ordinary less-than-or-equal relation.

(add-var-name "p" (py "nat@@nat"))

(add-program-constant "Quot" (py "nat=>nat=>nat") t-deg-zero)
(add-program-constant "Rem" (py "nat=>nat=>nat") t-deg-zero)
(add-program-constant "QuotRem" (py "nat=>nat=>nat@@nat") t-deg-zero)
(add-program-constant "QuotRemPair" (py "nat=>nat@@nat=>nat@@nat") t-deg-zero)

(add-computation-rules
 "QuotRemPair m p"
 "[if (Succ right p<m) (left p@Succ right p) (Succ left p@0)]")

;; QuotRemPairTotal
(set-goal (rename-variables (term-to-totality-formula (pt "QuotRemPair"))))
(assume "m^" "Tm" "p^" "Tp")
(ng #t)
(split)
(use "BooleIfTotal")
(use "NatLtTotal")
(use "TotalNatSucc")
(use "Tp")
(use "Tm")
(use "Tp")
(use "TotalNatSucc")
(use "Tp")
(use "BooleIfTotal")
(use "NatLtTotal")
(use "TotalNatSucc")
(use "Tp")
(use "Tm")
(use "TotalNatSucc")
(use "Tp")
(use "TotalNatZero")
;; Proof finished.
(save "QuotRemPairTotal")

(add-computation-rules
 "QuotRem 0 m" "0@0"
 "QuotRem(Succ n)m" "QuotRemPair m(QuotRem n m)")

;; QuotRemTotal
(set-goal (rename-variables (term-to-totality-formula (pt "QuotRem"))))
(assume "n^" "Tn" "m^" "Tm")
(elim "Tn")
(ng #t)
(split)
(use "TotalNatZero")
(use "TotalNatZero")
(assume "n^1" "Tn1" "IH")
(assert (pf "QuotRem(Succ n^1)m^ eqd QuotRemPair m^(QuotRem n^1 m^)"))
 (use "InitEqD")
(assume "EqdHyp")
(simp "EqdHyp")
(drop "EqdHyp")
(use "QuotRemPairTotal")
(use "Tm")
(use "IH")
;; Proof finished.
(save "QuotRemTotal")

(add-computation-rules "Quot n m" "left(QuotRem n m)")

;; QuotTotal
(set-goal (rename-variables (term-to-totality-formula (pt "Quot"))))
(assume "n^" "Tn" "m^" "Tm")
(ng)
(use "QuotRemTotal")
(use "Tn")
(use "Tm")
;; Proof finished.
(save "QuotTotal")

(add-computation-rules "Rem n m" "right(QuotRem n m)")

;; RemTotal
(set-goal (rename-variables (term-to-totality-formula (pt "Rem"))))
(assume "n^" "Tn" "m^" "Tm")
(ng)
(use "QuotRemTotal")
(use "Tn")
(use "Tm")
;; Proof finished.
(save "RemTotal")

;; (pp (nt (pt "QuotRem 777 13")))

;; QuotRemCorrect
(set-goal "all m,n(0<m -> n=(Quot n m)*m+Rem n m & Rem n m<m)")
(assume "m")
(ind)
(ng)
(assume "0<m")
(split)
(use "Truth")
(use "0<m")
(assume "n" "IH" "0<m")
(use "NatLeCases" (pt "Succ(Rem n m)") (pt "m"))
(use "NatLtToSuccLe")
(use "IH")
(use "0<m")
(assume "Sr<m")
(split)
(ng)
(simp "Sr<m")
(ng)
(use-with "IH" "0<m" 'left)
(ng)
(simp "Sr<m")
(ng)
(use "Sr<m")
(assume "Sr=m")
(split)
(ng)
(simp "Sr=m")
(ng)
(assert "Succ n=left(QuotRem n m)*m+Succ right(QuotRem n m)")
  (use "IH")
  (use "0<m")
(simp "Sr=m")
(assume "Hyp")
(use "Hyp")
(ng)
(simp "Sr=m")
(use "0<m")
;; Proof finished.
(save "QuotRemCorrect")

;; LQ
(set-goal "all a,b(0<b -> a=Quot a b*b+Rem a b)")
(assume "a" "b" "0<b")
(use "QuotRemCorrect")
(use "0<b")
;; Proof finished.
(save "LQ")

;; LR
(set-goal "all a,b(0<b -> Rem a b<b)")
(assume "a" "b" "0<b")
(use "QuotRemCorrect")
(use "0<b")
;; Proof finished.
(save "LR")

;; QuotRemOne
(set-goal "all a QuotRem a 1 eqd(a@0)")
(ind)
(ng)
(use "InitEqD")
(assume "a" "IH")
(ng)
(simp "IH")
(ng)
(use "InitEqD")
;; Proof finished.
(save "QuotRemOne")

;; RemOne
(set-goal "all a Rem a 1=0")
(assume "a")
(ng)
(simp "QuotRemOne")
(use "Truth")
;; Proof finished.
(save "RemOne")

(add-program-constant "EqMod" (py "nat=>nat=>nat=>boole") t-deg-zero)
(add-computation-rules "EqMod m a b" "Rem a m=Rem b m")

;; EqModTotal
(set-goal (rename-variables (term-to-totality-formula (pt "EqMod"))))
(use "AllTotalElim")
(assume "m")
(use "AllTotalElim")
(assume "a")
(use "AllTotalElim")
(assume "b")
(ng)
(use "BooleTotalVar")
;; Proof finished.
(save "EqModTotal")

;; We prove that [a,b]EqMod m a b is a well quasi ordering.

;; EqModRefl
(set-goal "all m,a EqMod m a a")
(assume "m" "a")
(ng)
(use "Truth")
;; Proof finished.
(save "EqModRefl")

;; EqModTrans
(set-goal "all m,a,b,c(EqMod m a b -> EqMod m b c -> EqMod m a c)")
(assume "m" "a" "b" "c")
(ng)
(use "NatEqTrans")
;; Proof finished.
(save "EqModTrans")

(add-global-assumption
 "FPH" "all m,(nat=>nat)(all i(i<=Succ m -> (nat=>nat)i<=m) ->
        ex i,j(i<j & j<=Succ m & (nat=>nat)i=(nat=>nat)j))")
;; This is proved in examples/arith/fph.scm.  Its computational
;; content is irrelevant here, since it is only used in the
;; n.c. GoodAREqMod

;; GoodAREqMod
(set-goal "all as,m(Lh as=m+2 -> GoodAR([a,b]EqMod(Succ m)a b)as)")

;; Proof.  Apply FPH to s := [i]Rem(i thof as)(Succ m).  Then we
;; always have s i<=m.  Hence there are i<j<=Succ m with s i=s j.  By
;; GoodARProj with wqo := ([a,b]EqMod(Succ m)a b) the claim follows.

(assume "as" "m" "LhBound")
(assert "ex i,j(i<j & j<=Succ m &
                Rem(i thof as)(Succ m)=Rem(j thof as)(Succ m))")
 (use "FPH")
 (ng #t)
 (assume "i" "i<m+1")
 (use "NatLtSuccToLe")
 (use "LR")
 (use "Truth")
(assume "ExHyp")
(by-assume "ExHyp" "i" "iProp")
(by-assume "iProp" "j" "ijProp")
(use "GoodARProj" (pt "i") (pt "j"))
(use "ijProp")
(simp "LhBound")
(use "NatLeToLtSucc")
(use "ijProp")
(ng #t)
(simp "ijProp")
(use "Truth")
;; Proof finished.
(save "GoodAREqMod")

;; BarANilEqMod
(set-goal "all m BarA([a,b]EqMod(Succ m)a b)(Nil nat)")
(assume "m")

;; Proof.  By FPH: Given a sequence s of numbers with s_0..s_{m+1}<=m.
;; Then among s_0..s_{m+1} two are equal.  Hence modulo m+1
;; s_0..s_{m+1} is good (w.r.t =_m+1).  Therefore BarA s_{m+1}...s_0.
;; Now prove BarA s_{m+1-i}...s_0 by induction on i, using GenBarA in
;; the step.  For i=m+2 we obtain BarA Nil.

(assert "all i,as(i+Lh as=m+2 -> BarA([a,b]EqMod(Succ m)a b)as)")
 (ind)
 (assume "as" "Lh as=m+2")
 (use "InitBarA")
 (use "GoodAREqMod")
 (simp "ListLengthRev")
 (use "Lh as=m+2")
 (assume "i" "IH" "as" "LhHyp")
 (use "GenBarA")
 (assume "a")
 (use "IH")
 (ng #t)
 (ng "LhHyp")
 (use "LhHyp")
(assume "Assertion")
(use "Assertion" (pt "m+2"))
(use "Truth")
;; Proof finished.
(save "BarANilEqMod")

;; HigmanEqMod
(set-goal "all m BarW([a,b]EqMod(Succ m)a b)(Nil list nat)")
(assume "m")
(use "Higman")
(use "EqModTrans")
(use "BarANilEqMod")
;; Proof finished.
(save "HigmanEqMod")

;; GoodWInitEqMod
(set-goal "all m,f ex n GoodW([a,b]EqMod(Succ m)a b)(Rev(f fbar n))")
(assume "m" "f")
(use "BarWToGoodInit" (pt "(Nil list nat)") (pt "0"))
(use "HigmanEqMod")
(use "Truth")
;; Proof finished.
(save "GoodWInitEqMod")

;; Animate theorems
(animate "BarWToGoodInit")
(animate "HigmanEqMod")
(animate "BarANilEqMod")
(animate "Higman")
(animate "BarFAppd")
(animate "BarFNew")

;; (animate "BarWConsNil")
;; (animate "BarFNil")

(define eterm
  (proof-to-extracted-term (theorem-name-to-proof "GoodWInitEqMod")))
(define neterm (nt eterm))
;; (pp neterm)
(pp (term-to-type neterm))

(define (run-higman m infseq)
  (pp (nt (mk-term-in-app-form neterm (make-numeric-term m) infseq))))

;; a.  [0 0], [1 1 0], [0 1 0 1], [0], [0], ...
(add-program-constant "SeqOne" (py "nat=>list nat") t-deg-zero)
(add-computation-rules
 "SeqOne 0" "0::0:"
 "SeqOne 1" "1::1::0:"
 "SeqOne 2" "0::1::0::1:"
 "SeqOne(Succ(Succ(Succ n)))" "0:")
(run-higman 2 (pt "SeqOne"))
;; 3

;; b.  [0 0], [1], [1 0], [], [], ...
(add-program-constant "SeqTwo" (py "nat=>list nat") t-deg-zero)
(add-computation-rules
 "SeqTwo 0" "0::0:"
 "SeqTwo 1" "1::1::0:"
 "SeqTwo 2" "0::1::0::1:"
 "SeqTwo(Succ(Succ(Succ n)))" "(Nil nat)")
(run-higman 2 (pt "SeqTwo"))
;; 3

;; Note that in the proof of HigmanAux we have used = on A* which in
;; general is not compatible with the equivalence relation generated
;; by preceq.  Therefore we can only expect our results to be correct
;; if we only work on a subset of nat where preceq in antisymmetric.

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

;; (pp (nt (seqterm-and-term-to-shifted-seqterm (pt "[n](Nil nat)") (pt "2:"))))

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

(run-higman 2 (terms-and-final-term-to-seqterm
	       (list (pt "(1::3:)")
		     (pt "(2::2:)")
		     (pt "(0::0::4::2::2:)")
		     (pt "(2::0::4::2::2::2:)"))
	       (pt "3::2:")))
;; 6

(run-higman 2 (terms-and-final-term-to-seqterm
	       (list (pt "(0::0:)")
		     (pt "(1::1::0:)")
		     (pt "(0::1::0::1:)"))
	       (pt "0:")))
;; 3

;; More systematic test.

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

(define (test-neterm neterm m vs n final-v)
  (let ((l (+ (length vs) n)))
    (map (lambda (seq)
	   (display (term-to-string
		     (nt (mk-term-in-app-form
			  neterm
			  (make-numeric-term m)
			  (terms-and-final-term-to-seqterm
			   (map list-to-term (first seq (- l 1)))
			   (list-to-term (seq l)))))))
	   (display " gives good initial segment of ")
	   (display (first seq l))
	   (newline))
	 (generate-seq n vs final-v))
    *the-non-printing-object*))

;; a. [0 0], [1 1 0], [0 1 0 1], [0], ...
(test-neterm neterm 2 '((0 0) (1 1 0) (0 1 0 1)) 3 '(0))

;; 2 gives good initial segment of ((0 1 0 1) (0 1 0 1) (0 1 0 1) (0) (0) (0))
;; 3 gives good initial segment of ((1 1 0) (0 1 0 1) (0 1 0 1) (0) (0) (0))
;; 2 gives good initial segment of ((0 0) (0 1 0 1) (0 1 0 1) (0) (0) (0))
;; 3 gives good initial segment of ((0 1 0 1) (1 1 0) (0 1 0 1) (0) (0) (0))
;; 2 gives good initial segment of ((1 1 0) (1 1 0) (0 1 0 1) (0) (0) (0))
;; 3 gives good initial segment of ((0 0) (1 1 0) (0 1 0 1) (0) (0) (0))
;; 3 gives good initial segment of ((0 1 0 1) (0 0) (0 1 0 1) (0) (0) (0))
;; 5 gives good initial segment of ((1 1 0) (0 0) (0 1 0 1) (0) (0) (0))
;; 2 gives good initial segment of ((0 0) (0 0) (0 1 0 1) (0) (0) (0))
;; 2 gives good initial segment of ((0 1 0 1) (0 1 0 1) (1 1 0) (0) (0) (0))
;; 3 gives good initial segment of ((1 1 0) (0 1 0 1) (1 1 0) (0) (0) (0))
;; 2 gives good initial segment of ((0 0) (0 1 0 1) (1 1 0) (0) (0) (0))
;; 3 gives good initial segment of ((0 1 0 1) (1 1 0) (1 1 0) (0) (0) (0))
;; 2 gives good initial segment of ((1 1 0) (1 1 0) (1 1 0) (0) (0) (0))
;; 3 gives good initial segment of ((0 0) (1 1 0) (1 1 0) (0) (0) (0))
;; 5 gives good initial segment of ((0 1 0 1) (0 0) (1 1 0) (0) (0) (0))
;; 3 gives good initial segment of ((1 1 0) (0 0) (1 1 0) (0) (0) (0))
;; 2 gives good initial segment of ((0 0) (0 0) (1 1 0) (0) (0) (0))
;; 2 gives good initial segment of ((0 1 0 1) (0 1 0 1) (0 0) (0) (0) (0))
;; 5 gives good initial segment of ((1 1 0) (0 1 0 1) (0 0) (0) (0) (0))
;; 2 gives good initial segment of ((0 0) (0 1 0 1) (0 0) (0) (0) (0))
;; 5 gives good initial segment of ((0 1 0 1) (1 1 0) (0 0) (0) (0) (0))
;; 2 gives good initial segment of ((1 1 0) (1 1 0) (0 0) (0) (0) (0))
;; 3 gives good initial segment of ((0 0) (1 1 0) (0 0) (0) (0) (0))
;; 3 gives good initial segment of ((0 1 0 1) (0 0) (0 0) (0) (0) (0))
;; 3 gives good initial segment of ((1 1 0) (0 0) (0 0) (0) (0) (0))
;; 2 gives good initial segment of ((0 0) (0 0) (0 0) (0) (0) (0))

(test-neterm neterm 5 '((4 1) (3 3 0) (0 4 0 1)) 3 '())

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

;; Next we consider NatLe.  We need some additional lemmas on LargerAR
;; GoodAR and BarA.

;; LargerARAppdRight (not used)
(set-goal "all wqo,b,as,bs(LargerAR wqo b bs -> LargerAR wqo b(as++bs))")
(assume "wqo" "b")
(ind)
(ng)
(assume "bs" "Lbbs")
(use "Lbbs")
(assume "a" "as" "IHas" "bs" "Lbbs")
(ng)
(cases (pt "wqo a b"))
(assume "Useless")
(use "Truth")
(assume "Useless")
(ng)
(use "IHas")
(use "Lbbs")
;; Proof finished.
(save "LargerARAppdRight")

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
(use "NatLeTrans")
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

;; Animate new theorems (for NatLe)
;; (animate "BarWToGoodInit")
(animate "HigmanNatLe")
(animate "BarANilNatLe")
;; (animate "HigmanAux")
;; (animate "BarFAppd")
;; (animate "BarFNew")
(animate "BarNatLeAppdOne")

(define eterm
  (proof-to-extracted-term (theorem-name-to-proof "GoodWInitNatLe")))
(define neterm (rename-variables (nt eterm)))
;; (pp (nt neterm))
(pp (term-to-type neterm))

(define (run-higman infseq) (pp (nt (mk-term-in-app-form neterm infseq))))

;; a. [0 0], [1 1 0], [0 1 0 1], [0], ...
(run-higman (pt "SeqOne"))
;; 2

(run-higman (terms-and-final-term-to-seqterm
	     (list (pt "(0::0:)")
		   (pt "(1::1::0:)")
		   (pt "(0::1::0::1:)"))
	     (pt "0:")))
;; 2

(run-higman (terms-and-final-term-to-seqterm
	     (list (pt "(1::3:)")
		   (pt "(2::2:)")
		   (pt "(0::0::4::2::2:)")
		   (pt "(2::0::4::2::2::2:)"))
	     (pt "3::2:")))
;; 3

;; b. [5 2], [2 8], [4 2 1], [6 9], [3 5], [0], ...

(run-higman (terms-and-final-term-to-seqterm
	     (list (pt "(5::2:)")
		   (pt "(2::8:)")
		   (pt "(4::2::1:)")
		   (pt "(6::9:)")
		   (pt "(3::5:)"))
	     (pt "0:")))
;; 4

;; General lemmas (all to be animated):
;; ===================================

;; BarFAppdAux
;; "all wqo allnc ts(BarF wqo ts ->
;;      allnc ss(BarF wqo ss ->
;;      all m(m=Lh ss -> BarF wqo(ts++ss))))"

;; BarFNil        "allnc wqo BarF wqo(Nil lntree(list list nat yprod list nat))"

;; BarWConsNil    "allnc wqo,ws BarW wqo((Nil nat)::ws)"

;; HigmanAux
;; "all wqo(all a,b,c(wqo a b -> wqo b c -> wqo a c) -> 
;;   BarA wqo(Nil nat) ->
;;   allnc as(BarA wqo as ->
;;   allnc ts(BarF wqo ts ->
;;   all ws(Adm ws -> BSeq wqo(Heads ws)=as ->
;;   all tas(tas=ProjF ts ->
;;   Forest wqo ws=ts -> BarW wqo ws)))))"

;; Higman
;; "all wqo(all a,b,c(wqo a b -> wqo b c -> wqo a c) -> 
;;   BarA wqo(Nil nat) -> BarW wqo(Nil list nat))"

;; BarFAppd
;; "all wqo allnc t(BarF wqo(t:) ->
;;      allnc ss(BarF wqo ss -> all m(m=Lh ss -> BarF wqo(t::ss))))"

;; BarFNew
;; "all wqo(BarA wqo(Nil nat) ->
;;   allnc ws(BarW wqo ws -> 0<Lh ws ->
;;   all as(Incr wqo as ->  BarF wqo((NewTree(ws pair as)):))))"

;; BarWToGoodInit   "allnc wqo,ws(BarW wqo ws -> all f,n(Rev(f fbar n)=ws ->
;;                   ex m GoodW wqo(Rev(f fbar m))))"

;; Auxiliary lemmas special for NatLe:
;; ==================================

;; HigmanNatLe      "BarW NatLe(Nil list nat)"

;; BarANilNatLe     "BarA NatLe(Nil nat)"

;; BarNatLeAppdOne  "all i,m,as(i+Lh as=Succ m -> BarA NatLe(as++m:))"

;; The final proposition whose proof is extracted:
;; ==============================================

;; GoodWInitNatLe   "all f ex n GoodW NatLe(Rev(f fbar n))"

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

