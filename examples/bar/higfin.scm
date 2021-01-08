;; higfin.scm 2014-10-10

;; (load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(libload "list.scm")
(set! COMMENT-FLAG #t)

(remove-var-name "n" "m" "k" (py "nat"))
(add-var-name "a" "b" "c" "n" "m" "k" "i" "j" (py "nat"))
(add-var-name "v" "w" "u" "as" "bs" "cs" (py "list nat"))
(add-var-name "ws" "vs" "us" (py "list list nat"))
(add-var-name "wss" "vss" (py "list list list nat"))

(add-var-name "f" (py "nat=>list nat"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Definitions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Occs a w counts the number of occurrences of a in w
(add-program-constant "Occs" (py "nat=>list nat=>nat"))
(add-computation-rules
 "Occs a(Nil nat)" "0"
 "Occs a(b::w)" "[if (a=b) (Succ(Occs a w)) (Occs a w)]")

;; (pp (nt (pt "Occs 2(2::3::2::3::4::3::4:)")))
;; 2

(add-program-constant
 "ListListNatSub" (py "list list nat=>list list nat=>boole"))
(add-infix-display-string "ListListNatSub" "sub" 'rel-op)

(add-computation-rules
 "(Nil list nat)sub ws" "True"
 "(v::vs)sub(Nil list nat)" "False"
 "(v::vs)sub(w::ws)" "[if (v=w) (vs sub ws) ((v::vs)sub ws)]")

;; Emb v w means v embeds into w.
(add-ids (list (list "Emb" (make-arity (py "list nat") (py "list nat"))))
	 '("Emb(Nil nat)(Nil nat)" "InitEmb")
	 '("all v,w,a(Emb v w -> Emb v(a::w))" "GenEmbInit")
         '("all v,w,a(Emb v w -> Emb(a::v)(a::w))" "GenEmbCons"))

;; Larger v ws means v embeds into one word from ws.
(add-ids (list (list "Larger"
		     (make-arity (py "list nat") (py "list list nat"))))
	 '("all v,w,vs(Emb v w -> Larger w(v::vs))" "InitLarger")
	 '("all v,w,vs(Larger w vs -> Larger w(v::vs))" "GenLarger"))

;; Good ws means that one v in ws embeds into a larger w in ws to its left.
(add-ids (list (list "Good" (make-arity (py "list list nat"))))
	 '("all w,ws(Larger w ws -> Good(w::ws))" "InitGood")
	 '("all w,ws(Good ws -> Good(w::ws))" "GenGood"))

;; They are decidable n.c. relations and hence have equivalent
;; recursive versions, i.e., boolean valued functions given by
;; computation rules.  Atomic formulas written with them unfold when
;; normalized.  This can be helpful but can also be unwanted, since
;; one obtains if-terms and hence needs case distinctions.  Therefore
;; we define both versions and prove their equivalence.  Then one can
;; use either intro/elim or unfolding, as appropriate in the situation
;; at hand.

;; For a recursive version EmbR of Emb we need R a w (rest after the
;; first a in w) and I a w (initial segment of w before the first a.

(add-program-constant "R" (py "nat=>list nat=>list nat"))
(add-computation-rules
 "R a(Nil nat)" "(Nil nat)"
 "R a(b::w)" "[if (a=b) w (R a w)]")

(add-program-constant "I" (py "nat=>list nat=>list nat"))
(add-computation-rules
 "I a(Nil nat)" "(Nil nat)"
 "I a(b::w)" "[if (a=b) (Nil nat) (b::I a w)]")

(add-program-constant "EmbR" (py "list nat=>list nat=>boole"))
(add-computation-rules
 "EmbR(Nil nat)w" "True"
 "EmbR(a::v)w" "(a in w)andb EmbR v(R a w)")

(add-program-constant "LargerR" (py "list nat=>list list nat=>boole"))
(add-computation-rules
 "LargerR v(Nil list nat)" "False"
 "LargerR v(w::ws)" "[if (EmbR w v) True (LargerR v ws)]")

;; H a ws means that a is the head of a word in ws.
;; (In the wqo case use a>=b instead of a=b)
(add-program-constant "H" (py "nat=>list list nat=>boole"))
(add-computation-rules
 "H a(Nil list nat)" "False"
 "H a((Nil nat)::ws)" "H a ws"
 "H a((b::v)::ws)" "[if (a=b) True (H a ws)]")

;; MemB a bs assumes a in bs and that bs consists of distinct numbers
;; (i.e., is bad).  It returns the position of a in bs counted from
;; the right.

(add-program-constant "MemB" (py "nat=>list nat=>nat"))
(add-computation-rules
 "MemB a(Nil nat)" "0"
 "MemB a(b::bs)" "[if (a=b) (Lh bs) (MemB a bs)]")

;; (pp (nt (pt "MemB 2(3::2::4::9:)")))
;; 2
;; (pp (nt (pt "MemB 5(3::2::4::9:)")))
;; 0
;; (pp (nt (pt "MemB 9(3::2::4::9:)")))
;; 0

;; BSeq as (first bad sequence in as, viewed from the right)

;; (remove-program-constant "BSeq")
(add-program-constant "BSeq" (py "list nat=>list nat"))
(add-computation-rules
 "BSeq(Nil nat)" "(Nil nat)"
 "BSeq(a::as)" "[if (a in as) (BSeq as) (a::BSeq as)]")

;; (pp (nt (pt "BSeq(3::2::1::1::2:)")))
;; 3::1::2:

;; (add-program-constant "Heads" (py "list list nat=>list nat"))
;; (add-computation-rules
;;  "Heads(Nil list nat)" "(Nil nat)"
;;  "Heads((Nil nat)::ws)" "Heads ws"
;;  "Heads((a::v)::ws)" "a::Heads ws")

(add-program-constant
 "Insert" (py "list list list nat=>list nat=>nat=>list list list nat"))

(add-computation-rules
 "Insert(Nil list list nat)v i" "(Nil list list nat)"
 "Insert(vs::vss)v i" "[if (i=Lh vss)
                           ((v::vs)::vss)
                           (vs::(Insert vss v i))]")

;; (pp (nt (pt "Insert(vs0:)v 0")))
;; (v::vs0):
;; (pp (nt (pt "Insert(vs0::vs1:)v 0")))
;; vs0::(v::vs1):
;; (pp (nt (pt "Insert(vs0::vs1:)v 1")))
;; (v::vs0)::vs1:

;; (pp (nt (pt "Insert(vs0::vs1::vs2:)v 0")))
;; vs0::vs1::(v::vs2):
;; (pp (nt (pt "Insert(vs0::vs1::vs2:)v 1")))
;; vs0::(v::vs1)::vs2:
;; (pp (nt (pt "Insert(vs0::vs1::vs2:)v 2")))
;; (v::vs0)::vs1::vs2:
;; (pp (nt (pt "Insert(vs0::vs1::vs2:)v 3")))
;; (Inhab list list list nat)

;; (pp (nt (pt "Insert(vs0::vs1::vs2::vs3:)v 0")))
;; vs0::vs1::vs2::(v::vs3):
;; (pp (nt (pt "Insert(vs0::vs1::vs2::vs3:)v 1")))
;; vs0::vs1::(v::vs2)::vs3:
;; (pp (nt (pt "Insert(vs0::vs1::vs2::vs3:)v 2")))
;; vs0::(v::vs1)::vs2::vs3:
;; (pp (nt (pt "Insert(vs0::vs1::vs2::vs3:)v 3")))
;; (v::vs0)::vs1::vs2::vs3:

(add-program-constant "Folder" (py "list list nat=>list list list nat"))
(add-computation-rules
 "Folder(Nil list nat)" "(Nil list list nat)"
 "Folder((Nil nat)::ws)" "Folder ws"
 "Folder((a::v)::ws)" "[if (H a ws)
                           (Insert(Folder ws)v(MemB a(BSeq(PHeads ws))))
                           ((v::ws)::Folder ws)]")

;; Example

(define ws
  (pt "((10::4::2:)::(11::3:)::(10::6:)::(17::0:)::(18::1:)::(17::2:):)"))

(pp ws)
(pp
 (nt
  (pt "Folder((10::4::2:)::(11::3:)::(10::6:)::(17::0:)::(18::1:)::(17::2:):)")))

;; (3: ::(10::6:)::(17::0:)::(18::1:)::(17::2:):)::
;; ((4::2:)::6: ::(17::0:)::(18::1:)::(17::2:):)::
;; (1: ::(17::2:):)::
;; (0: ::2: :):

(pp (nt (make-term-in-app-form (pt "(ListPHeads nat)") ws)))
;; 10::11::10::17::18::17:

(pp (nt (make-term-in-app-form
	 (pt "BSeq") (make-term-in-app-form (pt "(ListPHeads nat)") ws))))
;; 11::10::18::17:

(pp (nt (mk-term-in-app-form
	 (pt "MemB") (pt "10")
	 (make-term-in-app-form
	  (pt "BSeq") (make-term-in-app-form (pt "(ListPHeads nat)") ws)))))
;; 2

(add-program-constant "GoodA" (py "list nat=>boole"))
(add-computation-rules
 "GoodA(Nil nat)" "False"
 "GoodA(a::as)" "[if (a in as) True (GoodA as)]")

(add-ids (list (list "BarA" (make-arity (py "list nat")) "treeA"))
	 '("allnc as(GoodA as -> BarA as)" "InitBarA")
	 '("allnc as(all a BarA(a::as) -> BarA as)" "GenBarA"))

(add-ids
 (list (list "BarS" (make-arity (py "list list list nat")) "treeS"))
 '("allnc vss,i(i<Lh vss -> Good(i thof vss) -> BarS vss)" "InitBarS")
 '("allnc vss(all v,i,n(n=Lh vss -> i<n -> BarS(Insert vss v i)) -> BarS vss)"
   "GenBarS"))

(add-ids (list (list "Bar" (make-arity (py "list list nat")) "tree"))
	 '("allnc vs(Good vs -> Bar vs)" "InitBar")
	 '("allnc vs(all v Bar(v::vs) -> Bar vs)" "GenBar"))

(add-program-constant "InitRev" (py "(nat=>list nat)=>nat=>list list nat"))
(add-computation-rules
 "InitRev f 0" "(Nil list nat)"
 "InitRev f(Succ n)" "f n::InitRev f n")

;; (pp (nt (pt "InitRev([n]((n*n):))5")))
;; 16: ::9: ::4: ::1: ::0: :

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Totality proofs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; OccsTotal
(set-goal (rename-variables (term-to-totality-formula (pt "Occs"))))
(use "AllTotalElim")
(assume "a")
(use "AllTotalElim")
(ind)
(use "TotalNatZero")
(assume "b" "w" "IHw")
(ng)
(use "BooleIfTotal")
(use "BooleTotalVar")
(use "TotalNatSucc")
(use "IHw")
(use "IHw")
;; Proof finished.
(save "OccsTotal")

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

;; RTotal
(set-goal (rename-variables (term-to-totality-formula (pt "R"))))
(use "AllTotalElim")
(assume "a")
(use "AllTotalElim")
(ind)
(ng)
(use "TotalListNil")
(assume "b" "w" "IHw")
(ng)
(cases (pt "a=b"))
(assume "a=b")
(use "ListTotalVar")
(assume "a=b -> F")
(ng)
(use "IHw")
;; Proof finished.
(save "RTotal")

;; ITotal
(set-goal (rename-variables (term-to-totality-formula (pt "I"))))
(use "AllTotalElim")
(assume "a")
(use "AllTotalElim")
(ind)
(ng)
(use "TotalListNil")
(assume "b" "w" "IHw")
(ng)
(cases (pt "a=b"))
(assume "a=b")
(use "TotalListNil")
(assume "a=b -> F")
(ng)
(use "TotalListCons")
(use "NatTotalVar")
(use "IHw")
;; Proof finished.
(save "ITotal")

;; EmbRTotal
(set-goal (rename-variables (term-to-totality-formula (pt "EmbR"))))
(use "AllTotalElim")
(ind)
(ng)
(strip)
(use "TotalBooleTrue")
(assume "a" "v" "IHv")
(ng)
(use "AllTotalElim")
(assume "w")
(use "AndConstTotal")
(use "BooleTotalVar")
(use "IHv")
(use "ListTotalVar")
;; Proof finshed.
(save "EmbRTotal")

;; LargerRTotal
(set-goal (rename-variables (term-to-totality-formula (pt "LargerR"))))
(use "AllTotalElim")
(assume "v")
(use "AllTotalElim")
(ind)
(ng)
(use "TotalBooleFalse")
(assume "w" "ws" "IHws")
(ng)
(use "BooleIfTotal")
(use "BooleTotalVar")
(use "TotalBooleTrue")
(use "IHws")
;; Proof finished.
(save "LargerRTotal")

;; HTotal
(set-goal (rename-variables (term-to-totality-formula (pt "H"))))
(use "AllTotalElim")
(assume "a")
(use "AllTotalElim")
(ind)
(use "TotalBooleFalse")
(cases)
(assume "ws" "IHws")
(use "IHws")
(assume "b" "v" "ws" "IHws")
(ng)
(cases (pt "a=b"))
(assume "a=b")
(use "TotalBooleTrue")
(assume "a=b -> F")
(use "IHws")
;; Proof finished.
(save "HTotal")

;; MemBTotal
(set-goal (rename-variables (term-to-totality-formula (pt "MemB"))))
(use "AllTotalElim")
(assume "a")
(use "AllTotalElim")
(ind)
(use "TotalNatZero")
(assume "b" "bs" "IHbs")
(ng)
(use "BooleIfTotal")
(use "NatEqTotal")
(use "NatTotalVar")
(use "NatTotalVar")
(use "ListLengthTotal")
(use "ListTotalVar")
(use "IHbs")
;; Proof finished.
(save "MemBTotal")

;; BSeqTotal
(set-goal (rename-variables (term-to-totality-formula (pt "BSeq"))))
(use "AllTotalElim")
(ind)
(use "TotalListNil")
(assume "a" "as" "IHas")
(ng)
(use "BooleIfTotal")
(use "ListNatInTotal")
(use "NatTotalVar")
(use "ListTotalVar")
(use "IHas")
(use "TotalListCons")
(use "NatTotalVar")
(use "IHas")
;; Proof finished.
(save "BSeqTotal")

;; InsertTotal
(set-goal (rename-variables (term-to-totality-formula (pt "Insert"))))
(assert "allnc v^(TotalList v^ -> allnc i^(TotalNat i^ -> allnc vss^(
          TotalList vss^ -> TotalList(Insert vss^ v^ i^))))")
(use "AllTotalElim")
(assume "v")
(use "AllTotalElim")
(assume "i")
(use "AllTotalElim")
(ind)
(ng)
(use "TotalListNil")
(assume "vs" "vss" "IHvss")
(ng)
(use "BooleIfTotal")
(use "BooleTotalVar")
(use "ListTotalVar")
(use "TotalListCons")
(use "ListTotalVar")
(use "IHvss")
(assume "Assertion" "vss^" "Tvss" "v^" "Tv" "i^" "Ti")
(use "Assertion")
(use "Tv")
(use "Ti")
(use "Tvss")
;; Proof finished.
(save "InsertTotal")

;; FolderTotal
(set-goal (rename-variables (term-to-totality-formula (pt "Folder"))))
(use "AllTotalElim")
(ind)
(ng)
(use "TotalListNil")
(ind)
(ng)
(assume "ws" "TFws")
(use "TFws")
(assume "a" "v" "IHv" "ws" "TFws")
(ng)
(cases (pt "H a ws"))
(ng)
(assume "Useless")
(use "InsertTotal")
(use "TFws")
(use "ListTotalVar")
(use "NatTotalVar")
;; Case H a ws -> F
(ng)
(assume "Useless")
(use "TotalListCons")
(use "ListTotalVar")
(use "TFws")
;; Proof finished.
(save "FolderTotal")

;; GoodATotal
(set-goal (rename-variables (term-to-totality-formula (pt "GoodA"))))
(use "AllTotalElim")
(ind)
(use "TotalBooleFalse")
(assume "a" "as" "IHas")
(ng)
(use "BooleIfTotal")
(use "BooleTotalVar")
(use "TotalBooleTrue")
(use "IHas")
;; Proof finished.
(save "GoodATotal")

;; InitRevTotal
(set-goal (rename-variables (term-to-totality-formula (pt "InitRev"))))
(assume "f^" "Tf")
(use "AllTotalElim")
(ind)
(use "TotalListNil")
(assume "n" "IHn")
(ng)
(use "TotalListCons")
(use "Tf")
(use "NatTotalVar")
(use "IHn")
;; Proof finished.
(save "InitRevTotal")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Auxiliary propositions (n.c.)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Elementary properties of the defined functions and relations
;; Occs
;; ListListNatSub
;; Emb
;; Larger
;; Good
;; R
;; I
;; EmbR
;; LargerR
;; H
;; MemB
;; BSeq
;; PHeads
;; Insert
;; Folder
;; GoodA

;; Proposed order.

;; nat: SuccPredMinus SuccMinus PredMinusLt PredMinusInvol.  This
;; might go into nat.scm

;; Occs: OccsZero

;; ListListNatSub: SubRefl SubCons SubTrans SubAppd

;; Emb, Larger, EmbR, LargerR: IaRSplit EmbRAppdRight GenEmbRCons
;; GenEmbRInit EmbToEmbR EmbAppdRight EmbRToEmb LargerRToLarger
;; LargerToLargerR LargerRNil LargerRSub LargerElim LargerComposed
;; LargerCons LargerSub LargerAppdCases LargerAppdLeft LargerMapCons

;; Good: GoodElim

;; MemB: LtMemBLh

;; BSeq: InBSeq BSeqDistinct

;; ;; PHeads: PHeadsH

;; Insert: LhInsert InsertCons InsertLemmaAux InsertLemma
;; InsertLemmaDiffAux InsertLemmaDiff

;; Folder: LhFolder FolderSub

;; GoodA: NotGoodABSeq

;; SuccPredMinus
(set-goal "all nat1,nat2(nat1<nat2 -> nat2--nat1=Succ(Pred(nat2--nat1)))")
(ind)
(cases)
(assume "Absurd")
(use "Absurd")
(assume "nat2" "Hyp")
(use "Hyp")
(assume "nat1" "IHnat1")
(cases)
(assume "Absurd")
(use "Absurd")
(use "IHnat1")
;; Proof finished.
(save "SuccPredMinus")

;; SuccMinus
(set-goal "all nat2,nat1(nat1<Succ nat2 -> Succ nat2--nat1=Succ(nat2--nat1))")
(assume "nat2")
(cases)
(assume "Trivial")
(use "Trivial")
(ng)
(assume "nat1")
(use "SuccPredMinus")
;; Proof finished.
(save "SuccMinus")

;; PredMinusLt
(set-goal "all nat1,nat2(nat2<nat1 -> Pred(nat1--nat2)<nat1)")
(ind)
(ng)
(assume "nat2" "Absurd")
(use "Absurd")
(assume "nat1" "IHnat1")
(cases)
(ng)
(assume "Trivial")
(use "Trivial")
(ng)
(assume "nat2" "nat2<nat1")
(use "NatLtTrans" (pt "nat1"))
(use "IHnat1")
(use "nat2<nat1")
(use "Truth")
;; Proof finished.
(save "PredMinusLt")

;; PredMinusInvol
(set-goal "all nat2,nat1(nat2<nat1 -> Pred(nat1--Pred(nat1--nat2))=nat2)")
(ind)
(ng)
(cases)
(ng)
(strip)
(use "Truth")
(ng)
(strip)
(use "Truth")
(assume "nat2" "IHnat2")
(cases)
(ng)
(assume "Absurd")
(use "Absurd")
(ng)
(assume "nat1" "nat2<nat1")
(assert "nat1--Pred(nat1--nat2)=Succ(Pred(nat1--Pred(nat1--nat2)))")
 (use "SuccPredMinus")
 (use "PredMinusLt")
 (use "nat2<nat1")
(assume "nat1--Pred(nat1--nat2)=Succ(Pred(nat1--Pred(nat1--nat2)))")
(simp "nat1--Pred(nat1--nat2)=Succ(Pred(nat1--Pred(nat1--nat2)))")
(ng)
(use "IHnat2")
(use "nat2<nat1")
;; Proof finished.
(save "PredMinusInvol")

;; OccsZero
(set-goal "all a,w((a in w -> F) -> Occs a w=0)")
(assume "a")
(ind)
(ng)
(strip)
(use "Truth")
(assume "b" "w" "IHw")
(ng)
(cases (pt "a=b"))
(ng)
(assume "Useless" "Absurd")
(use "Absurd")
(use "Truth")
(ng)
(assume "Useless")
(use "IHw")
;; Proof finished.
(save "OccsZero")

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

;; SubAppd
(set-goal "all vs,ws ws sub vs++ws")
(ind)
(ng)
(strip)
(use "Truth")
(assume "v" "vs" "IHvs")
(cases)
(ng)
(use "Truth")
(assume "w" "ws")
(ng)
(cases (pt "w=v"))
(assume "w=v")
(ng)
(inst-with-to "IHvs" (pt "w::ws") "IHvsInst")
(use "SubTrans" (pt "w::ws"))
(use "Truth")
(use "IHvsInst")
(assume "w=v -> F")
(ng)
(use "IHvs")
;; Proof finished.
(save "SubAppd")

;; IaRSplit
(set-goal "all a,w(a in w -> w=I a w++(a::R a w))")
(assume "a")
(ind)
(ng)
(use "Efq")
(assume "b" "w" "IH")
(ng)
(cases (pt "a=b"))
(assume "a=b")
(ng)
(assume "Useless")
(use "NatEqSym")
(use "a=b")
(assume "a=b -> F")
(ng)
(use "IH")
;; Proof finished.
(save "IaRSplit")

;; EmbRAppdRight
(set-goal "all v,u,w(EmbR v w -> EmbR v(u++w))")
(ind)
(ng)
(assume "u" "w" "Hyp")
(use "Hyp")
(assume "a" "v" "IHv")
(ng)
(ind)
(ng)
(assume "w" "Hyp")
(use "Hyp")
(assume "c" "u" "IHu" "w")
(ng)
(assume "Conj")
(inst-with-to "Conj" 'left "a in w")
(inst-with-to "Conj" 'right "EmbR v(R a w)")
(drop "Conj")
(cases (pt "a=c"))
(assume "a=c")
(ng)
(assert "w=I a w++(a::R a w)")
 (use "IaRSplit")
 (use "a in w")
(assume "w=I a w++(a::R a w)")
(simp "w=I a w++(a::R a w)")
(use "IHv")
(assert "I a w++(a::R a w)=I a w++a: ++R a w")
 (use "Truth")
(assume "I a w++(a::R a w)=I a w++a: ++R a w")
(simp "I a w++(a::R a w)=I a w++a: ++R a w")
(use "IHv")
(use "EmbR v(R a w)")
(assume "a=c -> F")
(ng #t)
(use "IHu")
(split)
(use "a in w")
(use "EmbR v(R a w)")
;; Proof finished.
(save "EmbRAppdRight")

;; GenEmbRCons
(set-goal "all v,w,a(EmbR v w -> EmbR(a::v)(a::w))")
(ng)
(assume "v" "w" "a" "Evw")
(use "Evw")
;; Proof finished.
(save "GenEmbRCons")

;; GenEmbRInit
(set-goal "all v,a,w(EmbR v w -> EmbR v(a::w))")
(assume "v" "a" "w" "Evw")
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
(set-goal "all v,w(Emb v w -> EmbR v w)")
(assume "v" "w" "Evw")
(elim "Evw")
(use "Truth")
(assume "v1" "w1" "a" "Ev1w1")
(use "GenEmbRInit")
(assume "v1" "w1" "a" "Ev1w1")
(use "GenEmbRCons")
;; Proof finished.
(save "EmbToEmbR")

;; Conversely:

;; EmbAppdRight
(set-goal "all v,w,u(Emb v w -> Emb v(u++w))")
(assume "v" "w")
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
(set-goal "all v,w(EmbR v w -> Emb v w)")
(ind)
(ng)
(ind)
(assume "Useless")
(use "InitEmb")
(ng)
(assume "b" "w" "IHw" "Useless")
(use "GenEmbInit")
(use-with "IHw" "Truth")
(assume "a" "v" "IHv")
(ind)
(ng)
(use "Efq")
(assume "b" "w" "IHw")
(ng #t)
(cases (pt "a=b"))
(assume "a=b")
(ng #t)
(assume "Evw")
(simp "<-" "a=b")
(use "GenEmbCons")
(use "IHv")
(use "Evw")
(assume "a=b -> F")
(ng)
(assume "Conj")
(inst-with-to "Conj" 'left "a in w")
(inst-with-to "Conj" 'right "EmbR v(R a w)")
(drop "Conj")
(assert "w=I a w++(a::R a w)")
 (use "IaRSplit")
 (use "a in w")
(assume "w=I a w++(a::R a w)")
(simp "w=I a w++(a::R a w)")
(drop "w=I a w++(a::R a w)")
(assert "(b::I a w++(a::R a w))=(b::I a w)++(a::R a w)")
 (use "Truth")
(assume "(b::I a w++(a::R a w))=(b::I a w)++(a::R a w)")
(simp "(b::I a w++(a::R a w))=(b::I a w)++(a::R a w)")
(use "EmbAppdRight")
(use "GenEmbCons")
(use "IHv")
(use "EmbR v(R a w)")
;; Proof finished.
(save "EmbRToEmb")

;; LargerRToLarger
(set-goal "all w,vs(LargerR w vs -> Larger w vs)")
(assume "w")
(ind)
(ng)
(use "Efq")
(assume "v" "vs" "IHvs")
(ng)
(cases (pt "EmbR v w"))
(ng)
(assume "Evw" "Useless")
(use "InitLarger")
(use "EmbRToEmb")
(use "Evw")
(assume "Emb w v -> F" "Lvws")
(use "GenLarger")
(use-with "IHvs" "Lvws")
;; Proof finished.
(save "LargerRToLarger")

;; LargerToLargerR
(set-goal "all v,ws(Larger v ws -> LargerR v ws)")
(assume "v1" "ws1" "LIv1ws1")
(elim "LIv1ws1")
(assume "v" "w" "ws" "Evw")
(ng)
(assert "EmbR v w")
 (use "EmbToEmbR")
 (use "Evw")
(assume "EmbR v w")
(simp "EmbR v w")
(use "Truth")
(assume "v" "w" "vs" "Lwvs" "LRwvs")
(ng)
(cases (pt "EmbR v w"))
(strip)
(use "Truth")
(assume "Useless")
(use "LRwvs")
;; Proof finished.
(save "LargerToLargerR")

;; LargerRNil
(set-goal "all w(LargerR w(Nil list nat) -> F)")
(ng)
(assume "w" "Absurd")
(use "Absurd")
;; Proof finished.
(save "LargerRNil")

;; LargerRSub
(set-goal "all ws,vs,w(vs sub ws -> LargerR w vs -> LargerR w ws)")
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

;; ws4002  w  ws  IHws:all vs,w(vs sub ws -> LargerR w vs -> LargerR w ws)
;; vs4017  v  vs
;; -----------------------------------------------------------------------------
;; ?_15:all w0((v::vs)sub(w::ws) -> LargerR w0(v::vs) -> LargerR w0(w::ws))

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
(cases (pt "EmbR w w1"))
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
(assert "LargerR w1 ws")
(use "IHws" (pt "v::vs"))
(use "vvssubws")
(use "Lw1vvs")
(ng #t)
(cases (pt "EmbR w w1"))
(strip)
(use "Truth")
(assume "Useless" "Lw1ws")
(use "Lw1ws")
;; Proof finished.
(save "LargerRSub")

;; LargerElim
(set-goal "all w,v,vs(
 Larger w(v::vs) -> (Emb v w -> Pvar^) -> (Larger w vs -> Pvar^) -> Pvar^)")
(assume "w" "v" "vs" "Lwvvs")
(inversion "Lwvvs")
(ng)
(assume "v1" "w1" "vs1" "Ev1w1" "w=w1" "Conj" "EHyp" "Useless")
(inst-with-to "Conj" 'left "v=v1")
(use "EHyp")
(simp "v=v1")
(simp "w=w1")
(use "Ev1w1")
(ng)
(assume "v1" "w1" "vs1" "Lw1vs1" "Useless1" "w=w1" "Conj" "Useless2" "LHyp")
(inst-with-to "Conj" 'right "vs=vs1")
(use "LHyp")
(simp "w=w1")
(simp "vs=vs1")
(use "Lw1vs1")
;; Proof finished.
(save "LargerElim")

;; LargerComposed 
(set-goal "all w,vs(Larger w vs -> vs=(Head vs::Tail vs))")
(assume "w" "vs" "Lwvs")
(elim "Lwvs")
(ng)
(strip)
(use "Truth")
(ng)
(strip)
(use "Truth")
;; Proof finished.
(save "LargerComposed")

;; LargerCons
(set-goal "all w,vs,a(Larger w vs -> Larger(a::w)vs)")
(assume "w" "vs" "a" "Lwvs")
(elim "Lwvs")
(assume "v1" "w1" "vs1" "Ev1w1")
(use "InitLarger")
(use "GenEmbInit")
(use  "Ev1w1")
(assume "v1" "w1" "vs1" "Lw1vs1")
(use "GenLarger")
;; Proof finished.
(save "LargerCons")

;; LargerSub
(set-goal "all ws,vs,w(vs sub ws -> Larger w vs -> Larger w ws)")
(assume "ws" "vs" "w" "vs sub ws" "Lwvs")
(use "LargerRToLarger")
(use "LargerRSub" (pt "vs"))
(use "vs sub ws")
(use "LargerToLargerR")
(use "Lwvs")
;; Proof finished.
(save "LargerSub")

;; LargerAppdCases
(set-goal "all w,vs,us(Larger w(vs++us) ->
 (Larger w vs -> Pvar^) -> (Larger w us -> Pvar^) -> Pvar^) ")
(assume "w")
(ind)
(ng)
(assume "us" "Lwus" "Useless" "Hyp")
(use-with "Hyp" "Lwus")
(ng)
(assume "v" "ws" "IHvs" "us" "Lwvwsus" "EHyp" "LHyp")
(use "LargerElim" (pt "w") (pt "v") (pt "ws++us"))
(use  "Lwvwsus")
;; Emb v w -> Pvar^
(assume "Evw")
(use "EHyp")
(use "InitLarger")
(use "Evw")
;; Larger w(ws++us) -> Pvar^
(assume "Lwwsus")
(assert "Larger w ws -> Pvar^")
(assume "Lwws")
(use "EHyp")
(use "GenLarger")
(use "Lwws")
(assume "Larger w ws -> Pvar^")
(use-with "IHvs" (pt "us") "Lwwsus" "Larger w ws -> Pvar^" "LHyp")
;; Proof finished.
(save "LargerAppdCases")

;; LargerAppdLeft
(set-goal "all w,vs,us(Larger w vs -> Larger w(vs++us))")
(assume "w")
(ind)
(ng)
(assume "us" "LwNil")
(assert "LargerR w(Nil list nat)")
(use "LargerToLargerR")
(use "LwNil")
(ng)
(use "Efq")
(assume "v" "vs" "IHvs" "us" "Lwvvs")
(ng)
(use "LargerElim" (pt "w") (pt "v") (pt "vs"))
(use "Lwvvs")
;; Emb v w -> Larger w(v::vs++us)
(assume "Evw")
(use "InitLarger")
(use "Evw")
;; Larger w vs -> Larger w(v::vs++us)
(assume "Lwvs")
(use "GenLarger")
(use "IHvs")
(use "Lwvs")
;; Proof finished.
(save "LargerAppdLeft")

;; LargerMapCons
(set-goal "all w,vs,a(Larger w vs -> Larger(a::w)((Cons nat)a map vs))")
(assume "w")
(ind)
(ng)
(assume "a" "LwNil")
(assert "LargerR w(Nil list nat)")
(use "LargerToLargerR")
(use "LwNil")
(ng)
(use "Efq")
(assume "v" "vs" "IHvs" "a" "Lwvvs")
(ng)
(use "LargerElim" (pt "w") (pt "v") (pt "vs"))
(use "Lwvvs")
;; Emb v w -> Larger(a::w)((a::v)::(Cons nat)a map vs)
(assume "Evw")
(use "InitLarger")
(use "GenEmbCons")
(use "Evw")
;; Larger w vs -> Larger(a::w)((a::v)::(Cons nat)a map vs)
(assume "Lwvs")
(use "GenLarger")
(use "IHvs")
(use "Lwvs")
;; Proof finished.
(save "LargerMapCons")

;; GoodElim
(set-goal "all w,ws(
 Good(w::ws) -> (Good ws -> Pvar^) -> (Larger w ws -> Pvar^) -> Pvar^)")
(assume "w" "ws" "Gwws")
(inversion "Gwws")
(ng)
(assume "w1" "ws1" "Lw1ws1" "Conj" "Useless" "LHyp")
(inst-with-to "Conj" 'left "w=w1")
(inst-with-to "Conj" 'right "ws=ws1")
(drop "Conj")
(simphyp-with-to "LHyp" "w=w1" "SLHyp")
(simphyp-with-to "SLHyp" "ws=ws1" "SSLHyp")
(use-with "SSLHyp" "Lw1ws1")
(ng)
(assume "w1" "ws1" "Gws1" "Useless1" "Conj" "GHyp" "Useless2")
(inst-with-to "Conj" 'right "ws=ws1")
(drop "Conj")
(simphyp-with-to "GHyp" "ws=ws1" "SGHyp")
(use-with "SGHyp" "Gws1")
;; Proof finished.
(save "GoodElim")

;; LtMemBLh
(set-goal "all a,as( a in as -> MemB a(BSeq as)<Lh(BSeq as))")
(assume "a")
(ind)
(ng)
(assume "Absurd")
(use "Absurd")
(assume "a0" "as" "IHas")
(ng)
(cases (pt "a=a0"))
(ng #t)
(assume "a=a0" "Useless")
(simp "<-" "a=a0")
(cases (pt "a in as"))
(ng)
(use "IHas")
(ng #t)
(strip)
(use "Truth")
;; Case a=a0 -> F
(ng #t)
(assume "a=a0 -> F")
(assume "a in as")
(cases (pt "a0 in as"))
(ng #t)
(assume "a0 in as")
(use-with "IHas" "a in as")
(ng #t)
(simp "a=a0 -> F")
(ng #t)
(assume "a0 in as -> F")
(use "NatLtTrans" (pt "Lh(BSeq as)"))
(use-with "IHas" "a in as")
(use "Truth")
;; Proof finished.
(save "LtMemBLh")

;; InBSeq
(set-goal "all as,a (a in BSeq as)=(a in as)")
(ind)
(assume "a")
(use "Truth")
(assume "a" "as" "IH" "a1")
(ng)
(cases (pt "a1=a"))
(assume "a1=a")
(simp "a1=a")
(ng)
(cases (pt "a in as"))
(assume "a in as")
(ng)
(simp "IH")
(simp "a in as")
(use "Truth")
(assume "a in as -> F")
(ng)
(use "Truth")
(assume "a1=a -> F")
(ng)
(cases (pt "a in as"))
(assume "a in as")
(ng)
(use "IH")
(assume "a in as -> F")
(ng)
(simp "a1=a -> F")
(use "IH")
;; Proof finished.
(save "InBSeq")

;; BSeqDistinct
(set-goal "all a,b,cs(
 a in cs -> b in cs -> MemB a(BSeq cs)=MemB b(BSeq cs) -> a=b)")
(assume "a" "b")
(ind)
(assume "Absurd")
(use "Efq")
(use "Absurd")
(assume "c" "cs" "IHcs")
(ng)
(cases (pt "c in cs"))
(ng)
(assume "c in cs")
(cases (pt "a=c"))
(assume "a=c" "Useless1")
(simphyp-with-to "c in cs" "<-" "a=c" "a in cs")
(cases (pt "b=c"))
(assume "b=c" "Useless2")
(simphyp-with-to "c in cs" "<-" "b=c" "b in cs")
(use-with "IHcs" "a in cs" "b in cs")
(assume "b=c -> F")
(ng)
(use-with "IHcs" "a in cs")
(assume "a=c -> F")
(ng)
(cases (pt "b=c"))
(assume "b=c" "a in cs" "Useless")
(simphyp-with-to "c in cs" "<-" "b=c" "b in cs")
(use-with "IHcs" "a in cs" "b in cs")
(assume "b=c -> F")
(ng)
(use "IHcs")
(assume "c in cs -> F")
(ng)
;; a=c and b=c have claim
;; a=c and b=c -> F.  Then Lh(BSeq cs)=MemB b(BSeq cs).  Also
;;                    b in cs, hence MemB b(BSeq cs)<Lh(BSeq cs) by LtMemBLh
;; a=c -> F and b=c.  Symmetric.
;; a=c -> F and b=c -> F.  Use "IHcs
(cases (pt "a=c"))
(assume "a=c")
(ng)
(cases (pt "b=c"))
(assume "b=c")
(strip)
(simp "a=c")
(simp "b=c")
(use "Truth")
(assume "b=c -> F")
(ng)
(assume "Useless" "b in cs" "Lh(BSeq cs)=MemB b(BSeq cs)")
(assert "MemB b(BSeq cs)<Lh(BSeq cs)")
 (use "LtMemBLh")
 (use "b in cs")
(simp "Lh(BSeq cs)=MemB b(BSeq cs)")
(assume "Absurd")
(use "Efq")
(use "Absurd")
(assume "a=c -> F")
(ng)
(cases (pt "b=c"))
(assume "b=c")
(ng)
(assume "a in cs" "Useless" "MemB a(BSeq cs)=Lh(BSeq cs)")
(assert "MemB a(BSeq cs)<Lh(BSeq cs)")
 (use "LtMemBLh")
 (use "a in cs")
(simp "MemB a(BSeq cs)=Lh(BSeq cs)")
(assume "Absurd")
(use "Efq")
(use "Absurd")
(assume "b=c -> F")
(ng)
(use "IHcs")
;; Proof finished.
(save "BSeqDistinct")

;; PHeadsH
(set-goal "all a,ws (a in PHeads ws)=H a ws")
(assume "a")
(ind)
(use "Truth")
(cases)
(ng)
(assume "ws" "Hyp")
(use "Hyp")
(assume "b" "v" "ws" "IHws")
(ng)
(cases (pt "a=b"))
(strip)
(use "Truth")
(strip)
(use "IHws")
;; Proof finished
(save "PHeadsH")

;; LhInsert
(set-goal "all vss,w,i Lh(Insert vss w i)=Lh vss")
(ind)
(strip)
(ng)
(use "Truth")
(assume "ws" "vss" "IH" "w" "i")
(ng)
(cases (pt "i=Lh vss"))
(assume "Useless")
(ng #t)
(use "Truth")
(assume "Useless")
(ng)
(use "IH")
;; Proof finished.
(save "LhInsert")

;; InsertCons
(set-goal "all w,ws,vss,i(i<Lh vss -> 
 (Insert(ws::vss)w i)=(ws::Insert vss w i))")
(assume "w" "ws" "vss" "i" "i<Lh vss")
(ng)
(assert "i=Lh vss -> F")
 (assume "i=Lh vss")
 (simphyp-with-to "i<Lh vss" "i=Lh vss" "Absurd")
 (use "Absurd")
(assume "i=Lh vss -> F")
(simp "i=Lh vss -> F")
(ng #t)
(simp "i<Lh vss")
(ng #t)
(use "Truth")
;; Proof finished.
(save "InsertCons")

;; InsertLemmaAux
(set-goal "all w,vss,ws,i(i<=Lh vss ->
 (Lh vss--i thof Insert(ws::vss)w i)=(w::Lh vss--i thof ws::vss))")
(assume "w")
(ind)
;; Base
(ng)
(assume "ws" "i" "i=0")
(simp "i=0")
(use "Truth")
;; Step
(assume "ws" "vss" "IH" "ws0" "i" "i<=Succ Lh vss")
(ng #t)
(use "NatLeCases" (pt "i") (pt "Succ Lh vss"))
(use "i<=Succ Lh vss")
(assume "i<Succ Lh vss")
(assert "i=Succ Lh vss -> F")
 (assume "i=Succ Lh vss")
 (simphyp-with-to "i<Succ Lh vss" "i=Succ Lh vss" "Absurd")
 (use "Absurd")
(assume "i=Succ Lh vss -> F")
(simp "i=Succ Lh vss -> F")
(ng #t)
(assert "i<=Lh vss")
 (use "NatLtSuccToLe")
 (use "i<Succ Lh vss")
(assume "i<=Lh vss")
(use "NatLeCases" (pt "i") (pt "Lh vss"))
(use "i<=Lh vss")
(assume "i<Lh vss")
(assert "i=Lh vss -> F")
 (assume "i=Lh vss")
 (simphyp-with-to "i<Lh vss" "i=Lh vss" "Absurd")
 (use "Absurd")
(assume "i=Lh vss -> F")
(simp "i=Lh vss -> F")
(ng #t)
(assert "Succ Lh vss--i=Succ(Lh vss--i)")
 (use "SuccMinus")
 (use "i<Succ Lh vss")
(assume "Succ Lh vss--i=Succ(Lh vss--i)")
(simp "Succ Lh vss--i=Succ(Lh vss--i)")
(ng #t)
(simp "<-" "InsertCons")
(use "IH")
(use "i<=Lh vss")
(use "i<Lh vss")
(assume "i=Lh vss")
(simp "<-" "i=Lh vss")
(ng #t)
(assert "Succ Lh vss--i=Succ(Lh vss--i)")
 (use "SuccMinus")
 (use "i<Succ Lh vss")
(assume "Succ Lh vss--i=Succ(Lh vss--i)")
(simp "Succ Lh vss--i=Succ(Lh vss--i)")
(ng #t)
(simp "<-" "i=Lh vss")
(ng #t)
(use "Truth")
(assume "i=Succ Lh vss")
(simp "<-" "i=Succ Lh vss")
(ng #t)
(simp "<-" "i=Succ Lh vss")
(ng #t)
(use "Truth")
;; Proof finished.
(save "InsertLemmaAux")

;; InsertLemma
(set-goal "all wss,w,i(
 i<Lh wss -> 
 (Pred(Lh wss--i)thof Insert wss w i)=(w::Pred(Lh wss--i)thof wss))")
(ind)
(ng)
(assume "w" "i" "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "ws" "vss" "IH" "w" "i" "i<Succ Lh vss")
(use "InsertLemmaAux")
(use "NatLtSuccToLe")
(use "i<Succ Lh vss")
;; Proof finished.
(save "InsertLemma")

(remove-computation-rules-for (pt "(Inhab list alpha)"))

(add-computation-rules
 "(Inhab list list nat)" "(Nil list nat)")

;; InsertLemmaDiffAux
(set-goal "all w,vss,ws,i,j(i<=Lh vss -> j<=Lh vss -> (i=j -> F) ->
 (Lh vss--i thof Insert(ws::vss)w j)=(Lh vss--i thof ws::vss))")
(assume "w")
(ind)
;; Base
(ng)
(assume "ws" "i" "j" "i=0")
(simp "i=0")
(assume "j=0")
(simp "j=0")
(simp "j=0")
(assume "Absurd")
(use "Efq")
(use-with "Absurd" "Truth")
;; Step
(assume "ws" "vss" "IH" "ws0" "i" "j" "i<=Succ Lh vss" "j<=Succ Lh vss"
	"i=j -> F")
(ng #t)
(use "NatLeCases" (pt "j") (pt "Succ Lh vss"))
(use "j<=Succ Lh vss")
(assume "j<Succ Lh vss")
(assert "j=Succ Lh vss -> F")
 (assume "j=Succ Lh vss")
 (simphyp-with-to "j<Succ Lh vss" "j=Succ Lh vss" "Absurd")
 (use "Absurd")
(assume "j=Succ Lh vss -> F")
(simp "j=Succ Lh vss -> F")
(ng #t)
(assert "j<=Lh vss")
 (use "NatLtSuccToLe")
 (use "j<Succ Lh vss")
(assume "j<=Lh vss")
(use "NatLeCases" (pt "j") (pt "Lh vss"))
(use "j<=Lh vss")
(assume "j<Lh vss")
(assert "j=Lh vss -> F")
 (assume "j=Lh vss")
 (simphyp-with-to "j<Lh vss" "j=Lh vss" "Absurd")
 (use "Absurd")
(assume "j=Lh vss -> F")
(simp "j=Lh vss -> F")
(ng #t)
(use "NatLeCases" (pt "i") (pt "Succ Lh vss"))
(use "i<=Succ Lh vss")
(assume "i<Succ Lh vss")
(assert "Succ Lh vss--i=Succ(Lh vss--i)")
 (use "SuccMinus")
 (use "i<Succ Lh vss")
(assume "Succ Lh vss--i=Succ(Lh vss--i)")
(simp "Succ Lh vss--i=Succ(Lh vss--i)")
(ng #t)
(simp "<-" "InsertCons")
(use "IH")
(use "NatLtSuccToLe")
(use "i<Succ Lh vss")
(use "j<=Lh vss")
(use "i=j -> F")
(use "j<Lh vss")
(assume "i=Succ Lh vss")
(simp "<-" "i=Succ Lh vss")
(ng #t)
(use "Truth")
(assume "j=Lh vss")
(simp "j=Lh vss")
(ng #t)
(use "NatLeCases" (pt "i") (pt "Succ Lh vss"))
(use "i<=Succ Lh vss")
(assume "i<Succ Lh vss")
(assert "Succ Lh vss--i=Succ(Lh vss--i)")
 (use "SuccMinus")
 (use "i<Succ Lh vss")
(assume "Succ Lh vss--i=Succ(Lh vss--i)")
(simp "Succ Lh vss--i=Succ(Lh vss--i)")
(ng #t)
(use "NatLeCases" (pt "i") (pt "Lh vss"))
(use "NatLtSuccToLe")
(use "i<Succ Lh vss")
(assume "i<Lh vss")
(assert "Lh vss--i=Succ(Pred(Lh vss--i))")
 (use "SuccPredMinus")
 (use "i<Lh vss")
(assume "Lh vss--i=Succ(Pred(Lh vss--i))")
(simp "Lh vss--i=Succ(Pred(Lh vss--i))")
(ng #t)
(use "Truth")
(assume "i=Lh vss")
(use "Efq")
(use "i=j -> F")
(simp "i=Lh vss")
(simp "j=Lh vss")
(use "Truth")
(assume "i=Succ Lh vss")
(simp "<-" "i=Succ Lh vss")
(use "Truth")
(assume "j=Succ Lh vss")
(simp "j=Succ Lh vss")
(ng #t)
(use "NatLeCases" (pt "i") (pt "Succ Lh vss"))
(use "i<=Succ Lh vss")
(assume "i<Succ Lh vss")
(assert "Succ Lh vss--i=Succ(Lh vss--i)")
 (use "SuccMinus")
 (use "i<Succ Lh vss")
(assume "Succ Lh vss--i=Succ(Lh vss--i)")
(simp "Succ Lh vss--i=Succ(Lh vss--i)")
(ng #t)
(use "Truth")
(assume "i=Succ Lh vss")
(use "Efq")
(use "i=j -> F")
(simp "i=Succ Lh vss")
(simp "j=Succ Lh vss")
(use "Truth")
;; Proof finished.
(save "InsertLemmaDiffAux")

;; InsertLemmaDiff
(set-goal "all wss,w,i,j(
 i<Lh wss -> j<Lh wss -> (i=j -> F) ->
 (Pred(Lh wss--i)thof Insert wss w j)=(Pred(Lh wss--i)thof wss))")
(ind)
(ng)
(strip)
(use "Truth")
(assume "ws" "vss" "IH" "w" "i" "j" "i<Succ Lh vss"  "j<Succ Lh vss" "i=j -> F")
(use "InsertLemmaDiffAux")
(use "NatLtSuccToLe")
(use "i<Succ Lh vss")
(use "NatLtSuccToLe")
(use "j<Succ Lh vss")
(use  "i=j -> F")
;; Proof finished.
(save "InsertLemmaDiff")

;; LhFolder
(set-goal "all ws Lh(BSeq(PHeads ws))=Lh(Folder ws)")
(ind)
(ng)
(use "Truth")
(cases)
(ng)
(assume "ws" "IHws")
(use "IHws")
(assume "a" "v" "ws" "IHws")
(ng #t)
(simp "PHeadsH")
(cases (pt "H a ws"))
(assume "H a ws")
(ng #t)
(simp "LhInsert")
(use "IHws")
(assume "H a ws -> F")
(ng #t)
(use "IHws")
;; Proof finished.
(save "LhFolder")

;; FolderSub
(set-goal "all a,ws,m,i,vs,n,vs0,ws0(H a ws -> 
 m=MemB a(BSeq(PHeads ws)) -> 
 i=Pred(Lh(Folder ws)--m) -> 
 vs=(i thof Folder ws) -> 
 n=Occs a(PHeads ws) -> 
 vs0=n init vs -> ws0=n rest vs -> ((Cons nat)a map vs0)++ws0 sub ws)")
(assume "a")
(ind)
(ng)
(assume "m" "i" "vs" "n" "vs0" "ws0")
(use "Efq")
(cases) ;on v
(ng)
(assume "ws" "IHws" "m" "i" "vs" "n" "vs0" "ws0" "Haws" "mDef" "iDef" "vsDef"
	"nDef" "vs0Def" "ws0Def")
(use "SubTrans" (pt "ws"))
(use-with "IHws" (pt "m") (pt "i") (pt "vs") (pt "n") (pt "vs0") (pt "ws0")
	  "Haws" "mDef" "iDef" "vsDef" "nDef" "vs0Def" "ws0Def")
(use "SubCons")
(assume "b" "v" "ws" "IHws" "m" "i" "vs1" "n1" "vs10" "ws10")
(cases (pt "a=b"))
(assume "a=b")
(simp "<-" "a=b")
(ng)
(simp "PHeadsH")
(cases (pt "H a ws"))
(assume "H a ws")
(ng)
(assume "Useless" "mDef")
(simp "<-" "mDef")
(simp "LhInsert")
(assume "iDef")
(simp "iDef")
(simp "InsertLemma")
(simp "<-" "iDef")
(assume "vs1Def")
(simp "vs1Def")
(assume "n1Def")
(simp "n1Def")
(ng)
(assert "ex vs vs=(i thof Folder ws)")
 (ex-intro (pt "(i thof Folder ws)"))
 (use "Truth")
(assume "ex vs vs=(i thof Folder ws)")
(by-assume "ex vs vs=(i thof Folder ws)" "vs" "vsDef")
(simp "<-" "vsDef")
(assert "ex n n=Occs a(PHeads ws)")
 (ex-intro (pt "Occs a(PHeads ws)"))
 (use "Truth")
(assume "ex n n=Occs a(PHeads ws)")
(by-assume "ex n n=Occs a(PHeads ws)" "n" "nDef")
(simp "<-" "nDef")
(assert "ex vs0 vs0=n init vs")
 (ex-intro (pt "n init vs"))
 (use "Truth")
(assume "ex vs0 vs0=n init vs")
(by-assume "ex vs0 vs0=n init vs" "vs0" "vs0Def")
(simp "<-" "vs0Def")
(assume "vs10Def")
(simp "vs10Def")
(ng)
(use "IHws" (pt "m") (pt "i"))
(use "H a ws")
(use "mDef")
(use "iDef")
(use "vsDef")
(use "nDef")
(use "vs0Def")
;; m<Lh(Folder ws)
(simp "<-" "LhFolder")
(simp "mDef")
(use "LtMemBLh")
;; a in PHeads ws
(simp "PHeadsH")
(use "H a ws")
;; Case H a ws -> F
(ng)
(assume "H a ws -> F" "Trivial")
(simp "LhFolder")
(assume "mDef")
(simp "mDef")
(ng)
(assume "i=0")
(simp "i=0")
(ng)
(simp "OccsZero")
(assume "vs1Def")
(simp "vs1Def")
(assume "n1=1")
(simp "n1=1")
(ng)
(assume "vs10Def")
(simp "vs10Def")
(assume "ws10Def")
(simp "ws10Def")
(ng)
(use "Truth")
(simp "PHeadsH")
(use "H a ws -> F")
;; Case a=b -> F
(assume "a=b -> F")
(ng)
(simp "a=b -> F")
(ng)
(simp "PHeadsH")
(assume "H a ws")
(cases (pt "H b ws"))
(ng)
(assume "H b ws")
(simp "LhInsert")
(assume "mDef" "iDef")
(assert "ex n n=MemB b(BSeq(PHeads ws))")
 (ex-intro (pt "MemB b(BSeq(PHeads ws))"))
 (use "Truth")
(assume "ex n n=MemB b(BSeq(PHeads ws))")
(by-assume "ex n n=MemB b(BSeq(PHeads ws))" "n" "nDef")
(simp "<-" "nDef")
(simp "iDef")
(simp "InsertLemmaDiff")
(simp "<-" "iDef")
(assume "vs1Def" "n1Def" "vs10Def" "ws10Def")
(use "SubTrans" (pt "ws"))
(use "IHws" (pt "m") (pt "i") (pt "vs1") (pt "n1"))
(use "H a ws")
(use "mDef")
(use "iDef")
(use "vs1Def")
(use "n1Def")
(use "vs10Def")
(use "ws10Def")
(use "SubCons")
(assume "m=n")
(use "a=b -> F")
(use "BSeqDistinct" (pt "PHeads ws"))
(simp "PHeadsH")
(use "H a ws")
(simp "PHeadsH")
(use "H b ws")
(simp "<-" "mDef")
(simp "<-" "nDef")
(use "m=n")
(simp "nDef")
(simp "<-" "LhFolder")
(use "LtMemBLh")
(simp "PHeadsH")
(use "H b ws")
(simp "mDef")
(simp "<-" "LhFolder")
(use "LtMemBLh")
(simp "PHeadsH")
(use "H a ws")
;; Case "H b ws -> F"
(assume "H b ws -> F")
(ng)
(simp "a=b -> F")
(ng)
(assume "mDef")
(assert "m<Lh(Folder ws)")
 (simp "mDef")
 (simp "<-" "LhFolder")
 (use "LtMemBLh")
 (simp "PHeadsH")
 (use "H a ws")
(assume "m<Lh(Folder ws)")
(assert "ex i1 i1=Pred(Lh(Folder ws)--m)")
 (ex-intro (pt "Pred(Lh(Folder ws)--m)"))
 (use "Truth")
(assume "ex i1 i1=Pred(Lh(Folder ws)--m)")
(by-assume "ex i1 i1=Pred(Lh(Folder ws)--m)" "i1" "i1Def")
(assert "Lh(Folder ws)--m=Succ(Pred(Lh(Folder ws)--m))")
 (use "SuccPredMinus")
 (use "m<Lh(Folder ws)")
 (simp "<-" "i1Def")
(assume "Lh(Folder ws)--m=Succ i1")
(simp "Lh(Folder ws)--m=Succ i1")
(assume "iDef")
(simp "iDef")
(ng)
(assume "vs1Def" "n1Def" "vs10Def" "ws10Def")
(use "SubTrans" (pt "ws"))
(use "IHws" (pt "m") (pt "i1") (pt "vs1") (pt "n1"))
(use "H a ws")
(use "mDef")
(use "i1Def")
(use "vs1Def")
(use "n1Def")
(use "vs10Def")
(use "ws10Def")
(use "SubCons")
;; Proof finished.
(save "FolderSub")

;; NotGoodABSeq
(set-goal "all as(GoodA(BSeq as) -> F)")
(ind)
(ng)
(assume "Absurd")
(use "Absurd")
(assume "a" "as" "IHas")
(ng)
(cases (pt "a in as"))
(assume "a in as")
(ng)
(use "IHas")
(assume "a in as -> F")
(ng)
(simp "InBSeq")
(simp "a in as -> F")
(ng)
(use "IHas")
;; Proof finished.
(save "NotGoodABSeq")

;; Idea for the proof of GoodProjFolderToGood at (a::v)::ws with H a ws.
;; Let vs be the entry in Folder ws at the a-position m := MemB
;; a(BSeq(PHeads ws)).  Then v::vs is the entry in Folder((a::v)::ws) at
;; the a-position.  Assume Good(v::vs).  Goal Good((a::v)::ws).  Case
;; Larger v vs.  Let n=Occs a(PHeads ws).  Split vs into vs1++ws1 with
;; vs1=n init vs and ws1=n rest vs.  By LargerAppdCases it suffices to prove
;; Larger v vs1 -> Good((a::v)::ws) and Larger v ws1 -> Good((a::v)::ws).

;; Subcase Larger v vs1.  Obtain goal Good((a::v)::ws) from
;; Larger(a::v)ws by InitGood
;; Larger(a::v)(((Cons nat)a map vs1)++ws1) by LargerSub and FolderSub
;; Larger(a::v)((Cons nat)a map vs1) by LargerAppdLeft
;; Larger v vs1 by LargerMapCons

;; Subcase Larger v ws1.  Obtain goal Good((a::v)::ws) from
;; Larger(a::v)ws by InitGood
;; Larger v ws by LargerCons
;; Larger v ws1 by LargerSub since ws1 sub ((Cons nat)a map vs1)++ws1 sub ws

;; GoodProjFolderToGood (was Lemma1)
(set-goal "all ws,i(i<Lh(Folder ws) -> Good(i thof(Folder ws)) -> Good ws)")
(ind) ;on ws
;; Base
(ng)
(assume "i")
(use "Efq")
;; Step
(cases)
;; Nil case
(ng)
(assume "ws" "IHws" "i" "i<LFsw" "GHyp")
(use "GenGood")
(use "IHws" (pt "i"))
(use "i<LFsw")
(use "GHyp")
;; Cons case
(assume "a" "v" "ws" "IHws" "i")
(ng)
(assert "ex m m=MemB a(BSeq(PHeads ws))")
 (ex-intro (pt "MemB a(BSeq(PHeads ws))"))
 (use "Truth")
(assume "ex m m=MemB a(BSeq(PHeads ws))")
(by-assume "ex m m=MemB a(BSeq(PHeads ws))" "m" "mDef")
(simp "<-" "mDef")
(cases (pt "H a ws"))
(assume "H a ws")
(ng)
(simp "LhInsert")
(assume "i<LhFws")
(cases (pt "i=Pred(Lh(Folder ws)--m)"))
(assume "iDef")
(simp "iDef")
(simp "InsertLemma")
(simp "<-" "iDef")
(assert "ex vs vs=(i thof Folder ws)")
 (ex-intro (pt "i thof Folder ws"))
 (use "Truth")
(assume "ex vs vs=(i thof Folder ws)")
(by-assume "ex vs vs=(i thof Folder ws)" "vs" "vsDef")
(simp "<-" "vsDef")
(assume "Gvvs")
(use "GoodElim" (pt "v") (pt "vs"))
(use "Gvvs")
;; Case GenGood
(assume "Gvs")
(use "GenGood")
(use "IHws" (pt "i"))
(use "i<LhFws")
(simp "<-" "vsDef")
(use "Gvs")
;; Larger v vs -> Good((a::v)::ws)
(assume "Lvvs")
(assert "ex n n=Occs a(PHeads ws)")
 (ex-intro (pt "Occs a(PHeads ws)"))
 (use "Truth")
(assume "ex n n=Occs a(PHeads ws)")
(by-assume "ex n n=Occs a(PHeads ws)" "n" "nDef")
(assert "vs eqd(n init vs)++(n rest vs)")
 (use "ListAppdInitRest")
(assert "ex vs1 vs1=n init vs")
 (ex-intro (pt "n init vs"))
 (use "Truth")
(assume "ex vs1 vs1=n init vs")
(by-assume "ex vs1 vs1=n init vs" "vs1" "vs1Def")
(simp "<-" "vs1Def")
(assert "ex ws1 ws1=n rest vs")
 (ex-intro (pt "n rest vs"))
 (use "Truth")
(assume "ex ws1 ws1=n rest vs")
(by-assume "ex ws1 ws1=n rest vs" "ws1" "ws1Def")
(simp "<-" "ws1Def")
(assume "vs=vs1++ws1")
(use "LargerAppdCases" (pt "v") (pt "vs1") (pt "ws1"))
(simp "<-" "vs=vs1++ws1")
(use "Lvvs")
(assume "Lvvs1")
(use "InitGood")
(use "LargerSub" (pt "(((Cons nat)a map vs1)++ws1)"))
(use "FolderSub" (pt "m") (pt "i") (pt "vs") (pt "n"))
(use "H a ws")
(use "mDef")
(use "iDef")
(use "vsDef")
(use "nDef")
(use "vs1Def")
(use "ws1Def")
(use "LargerAppdLeft")
(use "LargerMapCons")
(use "Lvvs1")
;; Larger v ws1 -> Good((a::v)::ws)
(assume "Lvws1")
(use "InitGood")
(use "LargerCons")
(use "LargerSub" (pt "ws1"))
(use "SubTrans" (pt "((Cons nat)a map vs1)++ws1"))
(use "SubAppd")
(use "FolderSub" (pt "m") (pt "i") (pt "vs") (pt "n"))
(use "H a ws")
(use "mDef")
(use "iDef")
(use "vsDef")
(use "nDef")
(use "vs1Def")
(use "ws1Def")
(use "Lvws1")
;; m<Lh(Folder ws)
(simp "mDef")
(simp "<-" "LhFolder")
(use "LtMemBLh")
(simp "PHeadsH")
(use "H a ws")
;; ?_30:(i=Pred(Lh(Folder ws)--m) -> F) -> 
;;      Good(i thof Insert(Folder ws)v m) -> Good((a::v)::ws)
(assume "i=j -> F")
(inst-with-to
 "InsertLemmaDiff"
 (pt "Folder ws") (pt "v") (pt "Pred(Lh(Folder ws)--i)") (pt "m")
 "ILDInst")
(assert "(Pred(Lh(Folder ws)--Pred(Lh(Folder ws)--i)))=i")
 (use "PredMinusInvol")
 (use "i<LhFws")
(assume "iDef")
(simphyp-with-to "ILDInst" "iDef" "IInst")
(drop "ILDInst")
(simp "IInst")
(assume "GHyp")
(use "GenGood")
(use "IHws" (pt "i"))
(use "i<LhFws")
(use "GHyp")
(assume "Pred(Lh(Folder ws)--i)=m")
(use "i=j -> F")
(simp "<-" "Pred(Lh(Folder ws)--i)=m")
(simp "PredMinusInvol")
(use "Truth")
(use "i<LhFws")
(simp "<-" "LhFolder")
(simp "mDef")
(use "LtMemBLh")
(simp "PHeadsH")
(use "H a ws")
(use "PredMinusLt")
(use "i<LhFws")
(assume "H a ws -> F")
(ng)
(cases (pt "i"))
(ng)
(assume "i=0" "Trivial" "Gvws")
(use "GoodElim" (pt "v") (pt "ws"))
(use "Gvws")
(use "GenGood")
(assume "Lvws")
(use "InitGood")
(use "LargerCons")
(use "Lvws")
(assume "j" "i=Sj" "j<LhFws" "GFws")
(use "GenGood")
(use "IHws" (pt "j"))
(use  "j<LhFws")
(use "GFws")
;; Proof finished.
(save "GoodProjFolderToGood")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Main propositions (c.r.)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; BarThm
(set-goal
 "allnc ws(Bar ws -> all f,n(InitRev f n=ws -> ex m Good(InitRev f m)))")
(assume "vs" "Bvs")

;; Ind(Bar)
(elim "Bvs")

;; 1.  Good ws
(assume "ws" "Gws" "f" "n" "Ifnws")
(ex-intro (pt "n"))
(simp "Ifnws")
(use "Gws")

;; 2.  all w Bar(w::ws)
(assume "ws" "all w Bar(w::ws)" "IH" "f" "n" "Ifnws")
(use-with "IH" (pt "f n") (pt "f") (pt "Succ n") "?")

;; InitRev f(Succ n)=(f n::ws)
(ng)
(use "Ifnws")
;; Proof finished.
(save "BarThm")

(add-var-name "t" (py "tree"))
(add-var-name "ha" (py "list nat=>tree"))
(add-var-name "hb" (py "list nat=>(nat=>list nat)=>nat=>nat"))

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [t]
;;  (Rec tree=>(nat=>list nat)=>nat=>nat)t([f,a]a)([ha,hb,f,a]hb(f a)f(Succ a))

;; BarConsNil (was Prop1)
(set-goal "allnc ws Bar((Nil nat)::ws)")
(assume "ws")
(use "GenBar")
(assume "w")
(use "InitBar")
(use "InitGood")
(use "InitLarger")
(use "EmbRToEmb")
(ng)
(use "Truth")
;; Proof finished.
(save "BarConsNil")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; CGenBar([v]CInitBar)

;; BarSNil (was Lemma2i, or Lemma 5.8i)
(set-goal "BarS(Nil list list nat)")
(use "GenBarS")
(ng)
(assume "w" "i" "n" "n=0")
(simp "n=0")
(ng)
(use "Efq")
;; Proof finished.
(save "BarSNil")

;; BarSCons (was Lemma2ii or Lemma 5.8ii)
(set-goal "allnc vs(Bar vs -> allnc vss(BarS vss -> BarS(vs::vss)))")
(assume "ws" "Bws")

;; 1. Ind(Bar).
(elim "Bws")

;; 1.1
(assume "vs" "Gvs" "vss" "Useless")
(use "InitBarS" (pt "0"))
(use "Truth")
(use "Gvs")

;; 1.2
(assume "vs" "IH1a" "IH1b" "vss0" "Bvss0")
(drop "IH1a")

;; 2. Ind(BarS).
(elim "Bvss0")

;; 2.1
(assume "vss" "i" "iHyp" "GHyp")
(use "InitBarS" (pt "Succ i"))
(use "iHyp")
(use "GHyp")

;; 2.2
(assume "vss" "IH2a" "IH2b")
(use "GenBarS")
(assume "v" "i" "n" "nDef")
(simp "nDef")
(ng)
(assume "i<SLhvss")

;; i<Succ Lh vss, hence either i=Lh vss or i<Lh vss.  Instead of cases
;; on i=Lh vss, which is not allowed since vss is n.c., we do cases on
;; i+1=n (recall n=Succ Lh vss).

(cases (pt "i+1=n"))

;; Case1: i=Lh vss
(simp "nDef")
(ng)
(assume "i=Lh vss")
(simp "i=Lh vss")
(ng)
(use "IH1b")
(use "GenBarS")
(use "IH2a")

;; Case2: i<Lh vss (=n--1)
(simp "nDef")
(ng)
(assume "i=Lh vss -> F")
(simp "i=Lh vss -> F")
(ng)
(use "IH2b" (pt "n--1"))
(simp "nDef")
(use "Truth")
(simp "nDef")
(ng)
(use "NatLtSuccCases" (pt "i") (pt "Lh vss"))
(use "i<SLhvss")
(assume "Hyp")
(use "Hyp")
(assume "i=Lh vss")
(use "Efq")
(use-with "i=Lh vss -> F" "i=Lh vss")
;; Proof finished.
(save "BarSCons")

(add-var-name "ts" (py "treeS"))
(add-var-name "gb" (py "list nat=>tree"))
(add-var-name "gc" (py "list nat=>treeS=>treeS"))
(add-var-name "gd" (py "list nat=>nat=>nat=>treeS"))

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [t]
;;  (Rec tree=>treeS=>treeS)t([ts]CInitBarS)
;;  ([gb,gc,ts]
;;    (Rec treeS=>treeS)ts CInitBarS
;;    ([gd,gd0]
;;      CGenBarS
;;      ([v,a,a0][if (Succ a=a0) (gc v(CGenBarS gd)) (gd0 v a(Pred a0))])))

;; HigmanAux
(set-goal
 "allnc as(BarA as -> allnc vss(BarS vss -> all ws(BSeq(PHeads ws)=as ->
  Folder ws=vss -> Bar ws)))")
(assume "as0" "Bas0")
(elim "Bas0")

;; 1.1
(assume "as" "Gas" "vss" "Bvss" "ws" "BHws=as")
(use "Efq")
(use "NotGoodABSeq" (pt "PHeads ws"))
(simp "BHws=as")
(use "Gas")

;; 1.2
(assume "as" "IH1a" "IH1b" "vss0" "Bvss0")
(drop "IH1a")

;; Ind(BarS)
(elim "Bvss0")

;; 2.1
(assume "vss" "i" "i<Lvss" "GHyp" "ws" "BHws=as" "Fws=vss")
(use "InitBar")
(use "GoodProjFolderToGood" (pt "i"))
(simp "Fws=vss")
(use "i<Lvss")
(simp "Fws=vss")
(use "GHyp")

;; 2.2
(assume "vss" "IH2a" "IH2b" "ws" "BHws=as" "Fws=vss")
(use "GenBar")

;; Ind(w)
(ind)

;; 3.1
(use "BarConsNil")

;; 3.2
(assume "a" "v" "IH3")

;; Bar((a::v)::ws)

(assert "ex bs bs=BSeq(PHeads ws)")
 (ex-intro (pt "BSeq(PHeads ws)"))
 (use "Truth")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "ExHyp")
(by-assume "ExHyp" "bs" "bsDef")

(cases (pt "a in bs"))

(assume "a in bs")
(assert "a in PHeads ws")
 (simp "<-" "InBSeq")
 (simp "<-" "bsDef")
 (use "a in bs")
(assume "a in PHeads ws")
(assert "Lh bs=Lh vss")
 (simp "bsDef")
 (simp "<-" "Fws=vss")
 (use "LhFolder")
(assume "LhHyp")
(use "IH2b" (pt "v") (pt "MemB a bs") (pt "Lh bs"))
(use "LhHyp")
(simp "bsDef")
(use "LtMemBLh")
(use "a in PHeads ws")

;; BSeq(PHeads((a::v)::ws))=as
(ng)
(simp "a in PHeads ws")
(ng)
(use "BHws=as")

;; Folder((a::v)::ws)=Insert vss v(MemB a bs)
(ng)
(simp "<-" "PHeadsH")
(simp "a in PHeads ws")
(ng)
(simp "Fws=vss")
(simp "bsDef")
(use "Truth")

;; Case 2: a in bs -> F
(assume "a in bs -> F")
(assert "a in PHeads ws -> F")
 (simp "<-" "InBSeq")
 (simp "<-" "bsDef")
 (use "a in bs -> F")
(assume "a in PHeads ws -> F")
(drop "a in bs -> F")
(assert "H a ws -> F")
 (simp "<-" "PHeadsH")
 (use "a in PHeads ws -> F")
(assume "H a ws -> F")

(use "IH1b" (pt "a") (pt "((v::ws)::vss)"))
(use "BarSCons")

;; Bar(v::ws)
(use "IH3")

;; BarS vss
(use "GenBarS")
(use "IH2a")

;; BSeq(PHeads((a::v)::ws))=(a::as)
(ng)
(simp "a in PHeads ws -> F")
(ng)
(use "BHws=as")

;; Folder((a::v)::ws)=((v::ws)::vss)
(ng)
(simp "H a ws -> F")
(ng)
(use "Fws=vss")
;; Proof finished.
(save "HigmanAux")

(add-var-name "ge" (py "nat=>treeA"))
(add-var-name "gf" (py "nat=>treeS=>list list nat=>tree"))
(add-var-name "gg" (py "list nat=>nat=>nat=>list list nat=>tree"))

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [treeA]
;;  (Rec treeA=>treeS=>list list nat=>tree)treeA([ts,ws]CInitBar)
;;  ([ge,gf,ts]
;;    (Rec treeS=>list list nat=>tree)ts([ws]CInitBar)
;;    ([gd,gg,ws]
;;      CGenBar
;;      ([v]
;;        (Rec list nat=>tree)v cBarConsNil
;;        ([a,v0,t]
;;          [let v1
;;            (BSeq(PHeads ws))
;;            [if (a in v1)
;;             (gg v0(MemB a v1)Lh v1((a::v0)::ws))
;;             (gf a(cBarSCons t(CGenBarS gd))((a::v0)::ws))]]))))

(add-global-assumption "AlphabetOfFive" "all as(5<Lh as -> GoodA as)")

;; BarANilFive
(set-goal "BarA(Nil nat)")
(use "GenBarA")
(assume "a0")
(use "GenBarA")
(assume "a1")
(use "GenBarA")
(assume "a2")
(use "GenBarA")
(assume "a3")
(use "GenBarA")
(assume "a4")
(use "GenBarA")
(assume "a5")
(use "InitBarA")
(use "AlphabetOfFive")
(use "Truth")
;; Proof finished.
(save "BarANilFive")

;; HigmanFive
(set-goal "Bar(Nil list nat)")
(use "HigmanAux" (pt "(Nil nat)") (pt "(Nil list list nat)"))
(use "BarANilFive")
(use "BarSNil")
(use "Truth")
(use "Truth")
;; Proof finished.
(save "HigmanFive")

(display-pconst "GoodA")
(display-idpc "BarA")

;; GoodInitFive
(set-goal "all f ex m Good(InitRev f m)")
(assume "f")
(use "BarThm" (pt "(Nil list nat)" ) (pt "0"))
(use "HigmanFive")
(use "Truth")
;; Proof finished.
(save "GoodInitFive")

(animate "HigmanFive")
(animate "BarANilFive")
(animate "HigmanAux")
(animate "BarThm")
(animate "BarSNil")
(animate "BarSCons")
(animate "BarConsNil")
(animate "Id")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

(define (run-higman infseq)
  (term-to-string (nt (mk-term-in-app-form neterm infseq))))

(add-program-constant "Seq" (py "nat=>list nat"))
(add-computation-rules
 "Seq 0" "1::4:"
 "Seq 1" "0::3::3:"
 "Seq 2" "1::0::4::0:"
 "Seq(Succ(Succ(Succ n)))" "2:")

(run-higman (pt "Seq"))
;; 3

(add-program-constant "Interesting" (py "nat=>list nat"))
(add-computation-rules
 "Interesting 0" "0::0:"
 "Interesting 1" "1:"
 "Interesting 2" "0::1:"
 "Interesting(Succ(Succ(Succ n)))" "(Nil nat)")

(run-higman (pt "Interesting"))
;; 5

(add-program-constant "SixElements" (py "nat=>list nat"))
(add-computation-rules
 "SixElements 0" "1:"
 "SixElements 1" "3:"
 "SixElements 2" "5:"
 "SixElements 3" "7:"
 "SixElements 4" "9:"
 "SixElements(Succ(Succ(Succ(Succ(Succ n)))))" "0:")

(run-higman (pt "SixElements"))
;; 6
