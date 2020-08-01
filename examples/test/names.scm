;; 2020-07-15.  names.scm

;; (load "~/git/minlog/init.scm")

;; Initially load lib/nat.scm and lib/list.scm

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(libload "list.scm")

;; Introduce variable names for all test files.  In contrast to usual
;; developments in the test files many different contexts will be
;; considered.  However, the var and pvar names below will be kept
;; fixed and not removed.  This allows for more readable clauses.

(add-var-name "x" "y" "z" (py "alpha"))
(add-var-name "xs" "ys" "zs" (py "list alpha"))

(add-var-name "p" (py "boole"))
;; (add-var-name "q" (py "alpha=>boole"))
(add-var-name "rel" (py "alpha=>alpha=>boole"))

(add-pvar-name "A" "B" "C" (make-arity))
(add-pvar-name "Q" (make-arity (py "alpha")))
(add-pvar-name "R" (make-arity (py "alpha") (py "alpha")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Examples for algebras.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Nullary constructors are not required.
(add-algs "inf" '("Gen" "inf=>inf"))

;; Zero and successor labelled natural numbers.

(add-algs "zsnat"
	  '("alpha=>zsnat" "ZsnatZero")
	  '("beta=>zsnat=>zsnat" "ZsnatSucc"))
(add-rtotality "zsnat")
;; (display-idpc "RTotalZsnat")

;; Labelled natural numbers.

(add-algs "lnat"
	  '("alpha=>lnat" "LnatZero")
	  '("alpha=>lnat=>lnat" "LnatSucc"))
(add-rtotality "lnat")
;; (display-idpc "RTotalLnat")

;; Zero labelled natural numbers.

(add-algs "znat"
	  '("alpha=>znat" "ZnatZero")
	  '("znat=>znat" "ZnatSucc"))
(add-rtotality "znat")
;; (display-idpc "RTotalZnat")

;; (Successor) labelled natural numbers, or lists
;; In lib/list.scm
'(
(add-algs "list" 'prefix-typeop
	  '("list" "Nil")
	  '("alpha=>list=>list" "Cons"))
(add-rtotality "list")
)
;; (display-idpc "RTotalList")

;; Natural numbers.

;; In lib/nat.scm
'(
(add-algs "nat" '("nat" "Zero") '("nat=>nat" "Succ"))
)

;; Nil and branch labelled binary trees

(add-algs "nbbin"
	  '("alpha=>nbbin" "NbbinNil")
	  '("beta=>nbbin=>nbbin=>nbbin" "NbbinBranch"))
(add-rtotality "nbbin")
;; (display-idpc "RTotalNbbin")

;; Labelled binary trees

(add-algs "lbin"
	  '("alpha=>lbin" "LbinNil")
	  '("alpha=>lbin=>lbin=>lbin" "LbinBranch"))
(add-rtotality "lbin")
;; (display-idpc "RTotalLbin")

;; Nil labelled binary trees

(add-algs "nbin"
	  '("alpha=>nbin" "NbinNil")
	  '("nbin=>nbin=>nbin" "NbinBranch"))
(add-rtotality "nbin")
;; (display-idpc "RTotalNbin")

;; Branch labelled binary trees

(add-algs "bbin"
	  '("bbin" "BbinNil")
	  '("alpha=>bbin=>bbin=>bbin" "BbinBranch"))
(add-rtotality "bbin")
;; (display-idpc "RTotalBbin")

;; Binary trees, or derivations

(add-algs "bin"
	  '("bin" "BinNil")
	  '("bin=>bin=>bin" "BinBranch"))

;; Standard intervals

(add-algs "intv"
	  '("intv" "CInt")
	  '("intv=>intv" "CIntN")
	  '("intv=>intv" "CIntZ")
	  '("intv=>intv" "CIntP"))

;; Ordinals

(add-algs "ordl"
	  '("ordl" "OrdZero")
	  '("ordl=>ordl" "OrdSucc")
	  '("(nat=>ordl)=>ordl" "OrdSup"))

;; Infinite trees.  The parameter alpha is not strictly positive.

(add-algs "itree" 'prefix-typeop
	  '("itree" "ItreeInit")
	  '("(alpha=>itree)=>itree" "ItreeSup"))

;; Simultaneously defined tree lists and trees

(add-algs (list "tlist" "tree")
	  '("tlist" "Empty")
	  '("tree=>tlist=>tlist" "Tcons")
	  '("tree" "Leaf")
	  '("tlist=>tree" "Branch"))

;; Simultaneously defined tree lists and trees with labels on leafs

(add-algs (list "ltlist" "ltree") 'prefix-typeop
	  '("ltlist" "LEmpty")
	  '("ltree=>ltlist=>ltlist" "LTcons")
	  '("alpha=>ltree" "LLeaf")
	  '("ltlist=>ltree" "LBranch"))
(add-rtotality "ltlist")
;; ok, inductively defined predicate constant RTotalLtlist added
;; ok, inductively defined predicate constant RTotalLtree added

;; Three simultaneously defined algebras: an ordinal notation scheme
;; (W. Buchholz)

(add-algs (list "hterm" "htlist" "oterm")
	  '("hterm")
	  '("nat=>oterm=>hterm")
	  '("htlist")
	  '("hterm=>htlist=>htlist")
	  '("htlist=>oterm"))

;; Simultaneously defined infinite tree lists and trees with labels on leafs

(add-algs (list "infltlist" "infltree") 'prefix-typeop
          '("infltlist" "InfLEmpty")
          '("infltree=>infltlist=>infltlist" "InfLTcons")
	  '("alpha=>infltree" "InfLLeaf")
          '("infltlist=>infltree" "InfLBranch")
          '("(nat=>infltree)=>infltree" "InfLLim"))

;; Nested definition of tree lists and trees

(add-algs "ntree" '("list ntree=>ntree" "NBranch"))

;; Simultaneously defined even and odd trees.

(add-algs (list "evtree" "odtree")
	  '("list odtree=>evtree" "EvGen")
	  '("list evtree=>odtree" "OdGen"))

;; Positive propositional logic

(add-algs (list "disj" "conj") 'prefix-typeop
	  '("alpha=>disj" "Lit")
	  '("list conj=>disj" "Disjunction")
	  '("list disj=>conj" "Conjunction"))

;; Read and write (U. Berger, to represent continuous functions)

(add-alg "sd" '("sd" "Lft") '("sd" "Mid") '("sd" "Rht")) ;signed digits

(add-algs "read"
	  '("sd=>alpha=>read" "Put")
	  '("read=>read=>read=>read" "Get"))

(add-algs "write"
	  '("write" "Stop")
	  '("read write=>write" "Cont"))

;; A twice nested definition

(add-algs "nptree" 'prefix-typeop
	  '("list(alpha ysum nptree)=>nptree" "Cnptree"))

(define testalgs
  (list
   ;; algs in boole.scm, lib/nat.scm, lib/list.scm
   (py "unit")
   (py "boole")
   (py "alpha yprod beta")
   (py "alpha ysum beta")
   (py "uysum alpha")
   (py "alpha ysumu")
   (py "nat")
   (py "list alpha")
   ;; defined algs
   (py "inf")
   (py "zsnat alpha beta")
   (py "lnat alpha")
   (py "znat alpha")
   (py "nbbin alpha beta")
   (py "lbin alpha")
   (py "nbin alpha")
   (py "bin")
   (py "intv")
   (py "ordl")
   (py "itree alpha")
   (py "tlist")
   (py "tree")
   (py "ltlist alpha")
   (py "ltree alpha")
   (py "hterm")
   (pf "htlist")
   (py "oterm")
   (py "infltlist alpha")
   (py "infltree alpha")
   (py "ntree")
   (py "evtree")
   (py "odtree")
   (py "disj alpha")
   (py "conj alpha")
   (py "sd")
   (py "read alpha")
   (py "write")
   (py "nptree alpha")
   ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Examples of idpredconsts.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; We distinguish nullary / non-nullary ones, and those with no /
;; nullary / non-nullary parameter predicates.  For the last item, a
;; special case is that parameter predicates {x|P x} (with a total
;; variable x) are expected (ExDT).

(add-ids (list (list "Even" (make-arity (py "nat")) "nat"))
	 '("Even 0" "InitEven")
	 '("allnc n^(Even n^ -> Even(n^ +2))" "GenEven"))

(add-ids (list (list "Ev" (make-arity (py "nat")) "algEv")
	       (list "Od" (make-arity (py "nat")) "algOd"))
	 '("Ev 0" "InitEv")
	 '("allnc n^(Od n^ -> Ev(n^ +1))" "GenEv")
	 '("allnc n^(Ev n^ -> Od(n^ +1))" "GenOd"))

;; PiOne stands for projection on the first component.  PiOne is
;; definable from ExD, since (PiOne (cterm (x^ ,y^) R x^ y^))x^ is
;; equivalent to (ExD (cterm (x^) R x^ y^))

(add-ids (list (list "PiOne" (make-arity (py "alpha")) "identity"))
	 '("allnc x^,y^(R x^ y^ -> PiOne x^)" "InitPiOne"))

;; The transitive closure of a relation.

(add-ids (list (list "TrCl" (make-arity (py "alpha") (py "alpha")) "lnat"))
	 '("allnc x^,y^(R x^ y^ -> TrCl x^ y^)" "InitTrCl")
	 '("allnc x^,y^,z^(R x^ y^ -> TrCl y^ z^ -> TrCl x^ z^)" "GenTrCl"))

;; The n.c. transitive closure of a relation.

(add-ids
 (list (list "TrClNc" (make-arity (py "alpha") (py "alpha")) "nat"))
 '("allnc x^,y^(R^ x^ y^ -> TrClNc x^ y^)" "InitTrClNc")
 '("allnc x^,y^,z^(R^ x^ y^ -> TrClNc y^ z^ -> TrClNc x^ z^)" "GenTrClNc"))

;; The reflexive transitive closure of a relation.

(add-ids (list (list "RTrCl" (make-arity (py "alpha") (py "alpha")) "list"))
	 '("allnc x^ RTrCl x^ x^" "InitRTrCl")
	 '("allnc x^,y^,z^(R x^ y^ -> RTrCl y^ z^ -> RTrCl x^ z^)" "GenRTrCl"))

;; Code discarded 2020-07-14: impnc replaced by switching off predicates.
;; ;; Another form of reflexive transitive closure with R used c.r. and n.c.

;; (add-ids (list (list "RTC" (make-arity (py "alpha") (py "alpha")) "algRTC"))
;; 	 '("allnc x^,y^(R x^ y^ -> RTC x^ y^)" "InitRTC")
;; 	 '("allnc x^,y^(R x^ y^ --> RTC x^ x^)" "LInitRTC")
;; 	 '("allnc x^,y^(R x^ y^ --> RTC y^ y^)" "RInitRTC")
;; 	 '("allnc x^,y^,z^(R x^ y^ -> RTC y^ z^ -> RTC x^ z^)" "GenRTC"))

;; Code discarded 2020-07-14: add-ids is restricted to finitary algebras.
;; We define accessibility w.r.t. a relation given by a boolean-valued
;; function r.

;;(add-ids (list (list "Acc" (make-arity (py "alpha=>alpha=>boole") (py "alpha"))
;; 		     "itree"))
;; 	 '("allnc rel^,x^(F -> Acc rel^ x^)" "EfqAcc")
;; 	 '("allnc rel^,x^(all y^(rel^ y^ x^ -> Acc rel^ y^) -> Acc rel^ x^)"
;; 	   "GenAccSup"))

(add-ids (list (list "Cup" (make-arity (py "alpha")) "ysum"))
	 '("allnc x^(Q1 x^ -> Cup x^)" "InlCup")
	 '("allnc x^(Q2 x^ -> Cup x^)" "InrCup"))

(add-ids (list (list "Cap" (make-arity (py "alpha")) "yprod"))
	 '("allnc x^(Q1 x^ -> Q2 x^ -> Cap x^)" "InitCap"))

;; There are many variants: -> and/or all may be non-computational, we
;; may use a total variable x instead of x^, and have xs rather than x.

(set! COMMENT-FLAG #t)
