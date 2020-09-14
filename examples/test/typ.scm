;; (load "~/git/minlog/init.scm")
(load "names.scm")

;; 1. Preliminaries
;; ================
;; (list.scm and gen-app.scm)


;; 2. Types
;; ========
;; (typ.scm)

;; Tests for compose-substitutions

(define tsubst1 (list (list (py "alpha") (py "beta=>beta"))))
(define tsubst2 (list (list (py "beta") (py "alpha"))))

(pp-subst tsubst1)
(pp-subst tsubst2)

(pp-subst (compose-substitutions tsubst1 tsubst2))
;;   alpha -> alpha=>alpha
;;   beta -> alpha

(define tsubst1 (list (list (py "alpha") (py "gamma"))))
(define tsubst2 (list (list (py "alpha") (py "beta"))
		      (list (py "gamma") (py "alpha"))))

(pp-subst tsubst1)
(pp-subst tsubst2)

(pp-subst (compose-substitutions tsubst1 tsubst2))
;;   gamma -> alpha

(add-var-name "b" "w" (py "beta"))
(add-var-name "f" (py "beta=>gamma"))
(add-var-name "g" (py "gamma=>gamma"))
(add-pvar-name "P" (make-arity (py "beta") (py "beta")))
(add-pvar-name "S" (make-arity (py "gamma") (py "gamma")))
(add-var-name "v" (py "gamma"))

(define topsubst1
  (list (list (make-pvar (make-arity (py "beta") (py "beta")) -1 0 0 "P")
	      (make-cterm (pv "b^") (pv "w^") (pf "S(f^ b^)(f^ w^)")))))

(define topsubst2
  (list (list (py "beta") (py "gamma"))
	(list (pv "f^") (pt "g^"))))

(pp-subst (compose-substitutions topsubst1 topsubst2))
;;   P ->  (cterm (v^81,v^82) S(g^ v^81)(g^ v^82))
;;   beta -> gamma
;;   f^ -> g^

(remove-var-name "b" "w" "f" "g" "v")
(remove-pvar-name "P" "S")

;; Type unification.  Notice that our algorithm does not yield
;; idempotent unifiers (as opposed to the Martelli-Montanari algorithm
;; in modules/type-inf.scm):

(pp-subst
 (type-unify (py "alpha1=>alpha2=>boole") (py "alpha2=>alpha1=>alpha1")))

;;   alpha2 -> boole
;;   alpha1 -> alpha2

(for-each display-alg (map alg-form-to-name testalgs))

;; unit
;; 	Dummy:	unit
;; boole
;; 	True:	boole
;; 	False:	boole
;; yprod
;; 	PairConstr:	alpha1=>alpha2=>alpha1 yprod alpha2
;; ysum
;; 	InL:	alpha1=>alpha1 ysum alpha2
;; 	InR:	alpha2=>alpha1 ysum alpha2
;; uysum
;; 	DummyL:	uysum alpha1
;; 	InrUysum:	alpha1=>uysum alpha1
;; ysumu
;; 	InlYsumu:	alpha1=>alpha1 ysumu
;; 	DummyR:	alpha1 ysumu
;; nat
;; 	Zero:	nat
;; 	Succ:	nat=>nat
;; list
;; 	Nil:	list alpha
;; 	Cons:	alpha=>list alpha=>list alpha
;; inf
;; 	Gen:	inf=>inf
;; zsnat
;; 	ZsnatZero:	alpha=>zsnat alpha beta
;; 	ZsnatSucc:	beta=>zsnat alpha beta=>zsnat alpha beta
;; lnat
;; 	LnatZero:	alpha=>lnat alpha
;; 	LnatSucc:	alpha=>lnat alpha=>lnat alpha
;; znat
;; 	ZnatZero:	alpha=>znat alpha
;; 	ZnatSucc:	znat alpha=>znat alpha
;; nbbin
;; 	NbbinNil:	alpha=>nbbin alpha beta
;; 	NbbinBranch:	beta=>nbbin alpha beta=>nbbin alpha beta=>nbbin alpha beta
;; lbin
;; 	LbinNil:	alpha=>lbin alpha
;; 	LbinBranch:	alpha=>lbin alpha=>lbin alpha=>lbin alpha
;; nbin
;; 	NbinNil:	alpha=>nbin alpha
;; 	NbinBranch:	nbin alpha=>nbin alpha=>nbin alpha
;; bin
;; 	BinNil:	bin
;; 	BinBranch:	bin=>bin=>bin
;; intv
;; 	CInt:	intv
;; 	CIntN:	intv=>intv
;; 	CIntZ:	intv=>intv
;; 	CIntP:	intv=>intv
;; ordl
;; 	OrdZero:	ordl
;; 	OrdSucc:	ordl=>ordl
;; 	OrdSup:	(nat=>ordl)=>ordl
;; itree
;; 	ItreeInit:	itree alpha
;; 	ItreeSup:	(alpha=>itree alpha)=>itree alpha
;; tlist
;; 	Empty:	tlist
;; 	Tcons:	tree=>tlist=>tlist
;; tree
;; 	Leaf:	tree
;; 	Branch:	tlist=>tree
;; ltlist
;; 	LEmpty:	ltlist alpha
;; 	LTcons:	ltree alpha=>ltlist alpha=>ltlist alpha
;; ltree
;; 	LLeaf:	alpha=>ltree alpha
;; 	LBranch:	ltlist alpha=>ltree alpha
;; hterm
;; 	HtermZero:	hterm
;; 	HtermOne:	nat=>oterm=>hterm
;; oterm
;; 	OtermZero:	htlist=>oterm
;; infltlist
;; 	InfLEmpty:	infltlist alpha
;; 	InfLTcons:	infltree alpha=>infltlist alpha=>infltlist alpha
;; infltree
;; 	InfLLeaf:	alpha=>infltree alpha
;; 	InfLBranch:	infltlist alpha=>infltree alpha
;; 	InfLLim:	(nat=>infltree alpha)=>infltree alpha
;; ntree
;; 	NBranch:	list ntree=>ntree
;; evtree
;; 	EvGen:	list odtree=>evtree
;; odtree
;; 	OdGen:	list evtree=>odtree
;; disj
;; 	Lit:	alpha=>disj alpha
;; 	Disj:	list conj alpha=>disj alpha
;; conj
;; 	Conj:	list disj alpha=>conj alpha
;; sd
;; 	Lft:	sd
;; 	Mid:	sd
;; 	Rht:	sd
;; read
;; 	Put:	sd=>alpha=>read alpha
;; 	Get:	read alpha=>read alpha=>read alpha=>read alpha
;; write
;; 	Stop:	write
;; 	Cont:	read write=>write
;; nptree
;; 	Cnptree:	list(alpha ysum nptree alpha)=>nptree alpha

;; unit
;; 	Dummy:	unit
;; boole
;; 	True:	boole
;; 	False:	boole
;; yprod
;; 	PairConstr:	alpha1=>alpha2=>alpha1 yprod alpha2
;; ysum
;; 	InL:	alpha1=>alpha1 ysum alpha2
;; 	InR:	alpha2=>alpha1 ysum alpha2
;; uysum
;; 	DummyL:	uysum alpha1
;; 	InrUysum:	alpha1=>uysum alpha1
;; ysumu
;; 	InlYsumu:	alpha1=>alpha1 ysumu
;; 	DummyR:	alpha1 ysumu
;; nat
;; 	Zero:	nat
;; 	Succ:	nat=>nat
;; list
;; 	Nil:	list alpha
;; 	Cons:	alpha=>list alpha=>list alpha
;; lnat
;; 	LnatZero:	alpha=>lnat alpha
;; 	LnatOne:	alpha=>lnat alpha=>lnat alpha
;; bin
;; 	BinZero:	bin
;; 	BinOne:	bin=>bin=>bin
;; intv
;; 	CInt:	intv
;; 	CIntN:	intv=>intv
;; 	CIntZ:	intv=>intv
;; 	CIntP:	intv=>intv
;; lbin
;; 	LbinZero:	alpha=>lbin alpha
;; 	LbinOne:	lbin alpha=>lbin alpha=>lbin alpha
;; ordl
;; 	OrdZero:	ordl
;; 	OrdSucc:	ordl=>ordl
;; 	OrdSup:	(nat=>ordl)=>ordl
;; itree
;; 	ItreeInit:	itree alpha
;; 	ItreeSup:	(alpha=>itree alpha)=>itree alpha
;; tlist
;; 	Empty:	tlist
;; 	Tcons:	tree=>tlist=>tlist
;; tree
;; 	Leaf:	tree
;; 	Branch:	tlist=>tree
;; ltlist
;; 	LEmpty:	ltlist alpha
;; 	LTcons:	ltree alpha=>ltlist alpha=>ltlist alpha
;; ltree
;; 	LLeaf:	alpha=>ltree alpha
;; 	LBranch:	ltlist alpha=>ltree alpha
;; hterm
;; 	HtermZero:	hterm
;; 	HtermOne:	nat=>oterm=>hterm
;; oterm
;; 	OtermZero:	htlist=>oterm
;; infltlist
;; 	InfLEmpty:	infltlist alpha
;; 	InfLTcons:	infltree alpha=>infltlist alpha=>infltlist alpha
;; infltree
;; 	InfLLeaf:	alpha=>infltree alpha
;; 	InfLBranch:	infltlist alpha=>infltree alpha
;; 	InfLLim:	(nat=>infltree alpha)=>infltree alpha
;; ntree
;; 	NBranch:	list ntree=>ntree
;; evtree
;; 	EvGen:	list odtree=>evtree
;; odtree
;; 	OdGen:	list evtree=>odtree
;; disj
;; 	Lit:	alpha=>disj alpha
;; 	Disj:	list conj alpha=>disj alpha
;; conj
;; 	Conj:	list disj alpha=>conj alpha
;; read
;; 	WriteL:	alpha=>read alpha
;; 	WriteM:	alpha=>read alpha
;; 	WriteR:	alpha=>read alpha
;; 	Read:	read alpha=>read alpha=>read alpha=>read alpha
;; write
;; 	Stop:	write
;; 	ContRead:	read write=>write
;; nptree
;; 	Cnptree:	list(alpha ysum nptree alpha)=>nptree alpha

(finalg? (py "nat")) ;#t
(finalg? (py "ordl")) ;#f
(finalg? (py "ordl") (py "nat=>ordl")) ;#t
(finalg? (py "list nat")) ;#t
(finalg? (py "list alpha")) ;#f
(finalg? (py "list(list nat)")) ;#t
(finalg? (py "list(list alpha)")) ;#f
(finalg? (py "nat yprod boole")) ;#t
(finalg? (py "nat yprod alpha")) ;#f
(finalg? (py "alpha yprod beta") (py "alpha") (py "beta")) ;#t
(finalg? (py "alpha") (py "alpha yprod beta")) ;#f
(finalg? (py "nat ysum boole")) ;#t
(finalg? (py "nat ysum alpha")) ;#f
(finalg? (py "tlist")) ;#t
(finalg? (py "tree")) ;#t
(finalg? (py "ltlist nat")) ;#t
(finalg? (py "ltree nat")) ;#t
(finalg? (py "ltlist alpha")) ;#f
(finalg? (py "ltree alpha")) ;#f
(finalg? (py "ltree alpha") (py "alpha")) ;#t
(finalg? (py "hterm")) ;#t
(finalg? (py "infltlist nat")) ;#f
(finalg? (py "infltree nat")) ;#f

(sfinalg? (py "list alpha")) ;#t
(sfinalg? (py "ordl")) ;#f
(sfinalg? (py "nat yprod alpha")) ;#t
(sfinalg? (py "nat ysum alpha")) ;#t
(sfinalg? (py "ltree alpha")) ;#t
(sfinalg? (py "ltlist alpha")) ;#t
(sfinalg? (py "infltlist nat")) ;#f
(sfinalg? (py "infltree nat")) ;#f

;; Tests for type-to-canonical-inhabitant

(pp (type-to-canonical-inhabitant (py "alpha")))
;; (Inhab alpha)

(pp (type-to-canonical-inhabitant (py "alpha yprod beta")))
;; (Inhab alpha)pair(Inhab beta)

(pp (alg-to-canonical-inhabitant (py "boole yprod nat")))
;; True pair 0

(pp (type-to-canonical-inhabitant (py "alpha ysum beta")))
;; (InL alpha beta)(Inhab alpha)

(pp (alg-to-canonical-inhabitant (py "boole ysum nat")))
;; (InL boole nat)True

(pp (alg-to-canonical-inhabitant (py "alpha ysum nat")))
;; (InL alpha nat)(Inhab alpha)

(pp (alg-to-canonical-inhabitant (py "nat")))
;; 0
	
(add-algs (list "alga" "algb")
	  '("algb=>alga" "Cba")
	  '("algb=>alga=>alga" "Cbaa")
	  '("nat=>alga=>algb=>algb" "Cnabb")
	  '("nat=>algb" "Cnb"))

(pp (alg-to-canonical-inhabitant (py "alga")))
;; Cba(Cnb 0)

(remove-alg-name "alga" "algb")
	
(add-algs (list "ap" "bp")
	  '("alpha=>bp=>ap" "Cbap")
	  '("bp=>ap=>ap" "Cbaap")
	  '("nat=>ap=>bp=>bp" "Cnabbp")
	  '("list alpha=>bp" "Clbp"))

(display-alg "ap" "bp")

(pp (rename-variables (nt (alg-to-canonical-inhabitant (py "ap alpha")))))

;; (Cbap alpha)(Inhab alpha)((Clbp alpha)(Nil alpha))

(pp (term-to-type (pt "(Cbap alpha)alpha((Clbp alpha)(Nil alpha))")))
;; ap alpha

(remove-alg-name "ap" "bp")

(add-algs (list "alga")
	  '("(nat=>boole)=>alga" "Inita"))

(pp (rename-variables (alg-to-canonical-inhabitant (py "alga"))))
;; Inita([n]True)

(remove-alg-name "alga")

(pp (alg-to-canonical-inhabitant (make-alg "algEv")))
;; CInitEv
(pp (alg-to-canonical-inhabitant (make-alg "algOd")))
;; CGenOd CInitEv

