;; 2014-10-18.  train.scm

;; (load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(set! COMMENT-FLAG #t)

;; We decribe movements of trains on a track system.  Trains are given
;; by train numbers, where zero means no train.  The track system is
;; viewed as consisting of blocks b (= nodes in graph) with different
;; tracks e connecting to it (edges of the node).  At each point t in
;; time exactly one block and exactly one track connecting to it is
;; active.  It is then checked whether the neighbouring block b' along
;; this active edge is empty.  If so, at time t+1 the train which
;; occupied block b at time t has moved to block b', and block became
;; empty.  Otherwise no movement happens.

;; For simplicity we take the natural numbers as track system, i.e.,
;; blocks are n in N and edges connect n with n+1.  Hoewever, the
;; modelling used below will also work for arbitrary graphs.

;; As an example we formally prove a safety property of this system.
;; For simplicity we have picked a trivial one, namely that no train
;; can ever pass another one.  However, it is possible to demonstrate a
;; number of points in this example, which hopefully make it clear that
;; in a similar way one can deal with more complex (and more realistic)
;; situations.

;; We model this nondeterministic system using a choice function as
;; parameter.  This choice function determines for each point in time
;; which action is to be taken.  Hence the behaviour of the system is
;; uniquely determined once the choice function is given.  It is
;; convenient to split the choice function into two: a boolean valued
;; function f for the choice of the direction (i.e., left or right,
;; with true taken to mean left), and a block-valued function g giving
;; the block active at time t.

(add-var-name "t" (py "nat")) ;time
;; n,m will be used for train numbers
(add-var-name "b" "c" (py "nat")) ;blocks
(add-var-name "f" (py "nat=>boole")) ;choice of direction.  True=left
(add-var-name "g" (py "nat=>nat")) ;choice of block
(add-var-name "ib" (py "nat=>nat")) ;(ib n) initial block of train n
(add-var-name "in" (py "nat=>nat")) ;(in b) initial train in block b

;; N in f g t b (short: N t b) is the train in block b at time t.
;; The value 0 means that the block is empty.

;; B in ib f g t n (short: B t n) is the block of train n at time t.

(add-program-constant
 "N" (py "(nat=>nat)=>(nat=>boole)=>(nat=>nat)=>nat=>nat=>nat"))

(add-program-constant
 "B" (py "(nat=>nat)=>(nat=>nat)=>(nat=>boole)=>(nat=>nat)=>nat=>nat=>nat"))

(add-computation-rules
 "N in f g 0 b" "in b"

 "N in f g(Succ t)b"
 "[if b
      [if (f t)
	  [if (g t=1)
	      [if (N in f g t 0=0)
		  (N in f g t 1)
		  (N in f g t 0)]
	      (N in f g t 0)]
	  [if (g t=0)
	      [if (N in f g t 1=0)
		  0
		  (N in f g t 0)]
	      (N in f g t 0)]]
      ([c][if (f t)
	      [if (g t=Succ(Succ c))
		  [if (N in f g t(Succ c)=0)
		      (N in f g t(Succ(Succ c)))
		      (N in f g t(Succ c))]
		  [if (g t=Succ c)
		      [if (N in f g t c=0)
			  0
			  (N in f g t(Succ c))]
		      (N in f g t(Succ c))]]
	      [if (g t=Succ c)
		  [if (N in f g t(Succ(Succ c))=0)
		      0
		      (N in f g t(Succ c))]
		  [if (g t=c)
		      [if (N in f g t(Succ c)=0)
			  (N in f g t c)
			  (N in f g t(Succ c))]
		      (N in f g t(Succ c))]]])]")
	
(add-computation-rules
 "B in ib f g 0 n" "ib n"

 "B in ib f g(Succ t)n"
 "[if (f t)
      [if (g t)
	  (B in ib f g t n)
	  ([c][if (g t=B in ib f g t n)
		  [if (N in f g t c=0) c (Succ c)]
		  (B in ib f g t n)])]
      [if (g t=B in ib f g t n)
	  [if (N in f g t(Succ(g t))=0) (Succ(g t)) (g t)]
	  (B in ib f g t n)]]")


;; We now prove totality of N and then of B, using search.  Since
;; search does not use type substitutions we first provide an instance
;; of BooleIfTotal.

;; BooleIfTotalNat
(set-goal "allnc boole^(
 TotalBoole boole^ ->
 allnc n^0,n^1(
  Total n^0 -> Total n^1 -> Total[if boole^ n^0 n^1]))")
(assume "boole^" "Tboole" "n^0" "n^1" "Tn0" "Tn1")
(use "BooleIfTotal")
(auto)
;; Proof finished.
(save "BooleIfTotalNat")

;; "NTotal"
(set-goal (rename-variables (term-to-totality-formula (pt "N"))))
(assume "in^" "Tin" "f^" "Tf" "g^" "Tg" "t^" "Tt")
(elim "Tt")
(ng #t)
(use "Tin")
;; Step
(assume "t^1" "Tt1" "IHt1")
(ng #t)
(assume "n^" "Tn")
(elim "Tn")
;; Case Zero
(ng #t)
(search 3
	'("NatEqTotal" 3)
	'("BooleIfTotalNat" 3)
	'("TotalNatSucc" 3)
	'("TotalNatZero" 3))
;; Case Succ
(assume "n^1" "Tn1" "Useless1")
(drop "Useless1")
(use "NatIfTotal")
(search 1 '("TotalNatSucc" 1))
(search 3
	'("NatEqTotal" 3)
	'("BooleIfTotalNat" 3)
	'("TotalNatSucc" 3)
	'("TotalNatZero" 3))
(assume "n^2" "Tn2")
(ng #t)
(search 4
	'("NatEqTotal" 4)
	'("BooleIfTotalNat" 4)
	'("TotalNatSucc" 4)
	'("TotalNatZero" 4))
;; Proof finished.
(save "NTotal")

;; BTotal
(set-goal (rename-variables (term-to-totality-formula (pt "B"))))
(assume "in^" "Tin" "ib^" "Tib" "f^" "Tf" "g^" "Tg" "t^" "Tt")
(elim "Tt")
(ng #t)
(use "Tib")
;; Step
(assume "t^1" "Tt1" "IHt1")
(ng #t)
(assume "n^" "Tn")
(elim "Tn")
;; Case Zero
(ng #t)
(use "BooleIfTotal")
(search)
(use "NatIfTotal")
(search)
(search 3
	'("NatEqTotal" 3)
	'("BooleIfTotalNat" 3)
	'("TotalNatSucc" 3)
	'("TotalNatZero" 3))
(search 4
	'("NTotal" 4)
	'("NatEqTotal" 4)
	'("BooleIfTotalNat" 4)
	'("TotalNatSucc" 4)
	'("TotalNatZero" 4))
(search 4
	'("NTotal" 4)
	'("NatEqTotal" 4)
	'("BooleIfTotalNat" 4)
	'("TotalNatSucc" 4)
	'("TotalNatZero" 4))
;; Case Succ
(assume "n^1" "Tn1" "Useless1")
(drop "Useless1")
(use "BooleIfTotal")
(search)
(use "NatIfTotal")
(search)
(search 1 '("TotalNatSucc" 1))
(assume "n^2" "Tn2")
(ng #t)
(search 4
	'("NTotal" 4)
	'("NatEqTotal" 4)
	'("BooleIfTotalNat" 4)
	'("TotalNatSucc" 4)
	'("TotalNatZero" 4))
(search 4
	'("NTotal" 4)
	'("NatEqTotal" 4)
	'("BooleIfTotalNat" 4)
	'("TotalNatSucc" 4)
	'("TotalNatZero" 4))
;; Proof finished.
(save "BTotal")

;; We describe the definitions of N and B by lemmata.

;; "NLeftNextFull"
(set-goal "all in,ib,f,g,t,b(
 f t -> g t=Succ b -> (N in f g t b=0 -> F) ->
 N in f g(Succ t)b=N in f g t b)")
(assume "in" "ib" "f" "g" "t" "b" "Left" "Next" "Full")
(ng #t)
(simp "Left")
(ng #t)
(cases (pt "b"))
;; b=0
(ng #t)
(assume "b=0")
(simphyp-with-to "Next" "b=0" "g t=1")
(drop "Next")
(simphyp-with-to "Full" "b=0" "Nt0=/=0")
(drop "Full")
(simp "g t=1")
(ng #t)
(simp "Nt0=/=0")
(use "Truth")
;; b positive
(assume "c" "b=c+1")
(ng #t)
(simphyp-with-to "Next" "b=c+1" "g t=c+2")
(drop "Next")
(simphyp-with-to "Full" "b=c+1" "Nt(c+1)=/=0")
(drop "Full")
(simp "g t=c+2")
(ng #t)
(simp "Nt(c+1)=/=0")
(use "Truth")
;; Proof finished"
(save "NLeftNextFull")

;; NLeftNextEmpty
(set-goal "all in,ib,f,g,t,b(
 f t -> g t=Succ b -> N in f g t b=0 ->
 N in f g(Succ t)b=N in f g t(Succ b))")
(assume "in" "ib" "f" "g" "t" "b" "Left" "Next" "Empty")
(ng #t)
(simp "Left")
(ng #t)
(cases (pt "b"))
;; b=0
(ng #t)
(assume "b=0")
(simphyp-with-to "Next" "b=0" "g t=1")
(drop "Next")
(simphyp-with-to "Empty" "b=0" "Nt0=0")
(drop "Empty")
(simp "g t=1")
(ng #t)
(simp "Nt0=0")
(use "Truth")
;; b positive
(assume "c" "b=c+1")
(ng #t)
(simphyp-with-to "Next" "b=c+1" "g t=c+2")
(drop "Next")
(simphyp-with-to "Empty" "b=c+1" "Nt(c+1)=0")
(drop "Empty")
(simp "g t=c+2")
(ng #t)
(simp "Nt(c+1)=0")
(use "Truth")
;; Proof finished"
(save "NLeftNextEmpty")

;; NLeftPresentFull
(set-goal "all in,ib,f,g,t,b(
 f t -> g t=Succ b -> (N in f g t b=0 -> F) ->
 N in f g(Succ t)(Succ b)=N in f g t(Succ b))")
(assume "in" "ib" "f" "g" "t" "b" "Left" "Present" "Full")
(ng #t)
(simp "Left")
(ng #t)
(simp "Present")
(simp "Present")
(ng #t)
(simp "Full")
(use "Truth")
;; Proof finished.
(save "NLeftPresentFull")

;; NLeftPresentEmpty
(set-goal "all in,ib,f,g,t,b(
 f t -> g t=b -> N in f g t(Pred b)=0 -> N in f g(Succ t)b=0)")
(assume "in" "ib" "f" "g" "t" "b" "Left" "Present" "Empty")
(ng #t)
(simp "Left")
(ng #t)
(cases (pt "b"))
;; b=0
(ng #t)
(assume "b=0")
(simphyp-with-to "Present" "b=0" "g t=0")
(simphyp-with-to "Empty" "b=0" "Nt0=0")
(simp "g t=0")
(ng #t)
(use "Nt0=0")
;; b positive
(assume "c" "b=c+1")
(ng #t)
(simphyp-with-to "Present" "b=c+1" "g t=c+1")
(simphyp-with-to "Empty" "b=c+1" "Ntc=0")
(simp "g t=c+1")
(simp "g t=c+1")
(ng #t)
(simp "Ntc=0")
(use "Truth")
;; Proof finished.
(save "NLeftPresentEmpty")

;; NLeftElse
(set-goal "all in,ib,f,g,t,b(
 f t -> (g t=Succ b -> F) -> (g t=b -> F) ->
 N in f g(Succ t)b=N in f g t b)")
(assume "in" "ib" "f" "g" "t" "b" "Left" "NotNext" "NotPresent")
(ng #t)
(simp "Left")
(ng #t)
(cases (pt "b"))
;; b=0
(ng #t)
(assume "b=0")
(simphyp-with-to "NotNext" "b=0" "g t=/=1")
(simp "g t=/=1")
(use "Truth")
;; b positive
(assume "c" "b=c+1")
(ng #t)
(simphyp-with-to "NotPresent" "b=c+1" "g t=/=c+1")
(simphyp-with-to "NotNext" "b=c+1" "g t=/=c+2")
(simp "g t=/=c+1")
(simp "g t=/=c+2")
(use "Truth")
;; Proof finished.
(save "NLeftElse")

;; There are similar properties for NRight.

;; BLeftZero
(set-goal "all in,ib,f,g,t,n(
 f t -> g t=0 -> B in ib f g(Succ t)n=B in ib f g t n)")
(assume "in" "ib" "f" "g" "t" "n" "Left" "g t=0")
(ng #t)
(simp "Left")
(ng #t)
(simp "g t=0")
(use "Truth")
;; Proof finished.
(save "BLeftZero")

;; BLeftSuccActiveFull
(set-goal "all in,ib,f,g,t,b,n(
 f t -> g t=Succ b -> g t=B in ib f g t n -> (N in f g t b=0 -> F) ->
 B in ib f g(Succ t)n=B in ib f g t n)")
(assume "in" "ib" "f" "g" "t" "b" "n" "Left" "g t=b+1" "Active" "Full")
(ng #t)
(simp "Left")
(ng #t)
(simp "g t=b+1")
(ng #t)
(simp "Full")
(ng #t)
(simp "<-" "g t=b+1")
(simp "Active")
(ng #t)
(use "Active")
;; Proof finished.
(save "BLeftSuccActiveFull")

;; BLeftSuccActiveEmpty
(set-goal "all in,ib,f,g,t,b,n(
 f t -> g t=Succ b -> Succ b=B in ib f g t n -> N in f g t b=0 ->
 B in ib f g(Succ t)n=b)")
(assume "in" "ib" "f" "g" "t" "b" "n" "Left" "g t=b+1" "Active" "Empty")
(ng #t)
(simp "Left")
(ng #t)
(simp "g t=b+1")
(ng #t)
(simp "Empty")
(ng #t)
(simp "Active")
(use "Truth")
;; Proof finished.
(save "BLeftSuccActiveEmpty")

;; There are similar properties for BRight

;; BPassive
(set-goal "all in,ib,f,g,n,t(
 (g t=B in ib f g t n -> F) -> B in ib f g(Succ t)n=B in ib f g t n)")
(assume "in" "ib" "f" "g" "n" "t" "Pass")
(ng #t)
(cases (pt "f t"))
;; Lef
(assume "Left")
(ng #t)
(cases (pt "g t"))
(assume "Useless")
(use "Truth")
(assume "b" "g t=b+1")
(ng #t)
(simp "<-" "g t=b+1")
(simp "Pass")
(use "Truth")
;; Righ
(assume "Right")
(ng #t)
(simp "Pass")
(use "Truth")
;; Proof finished.
(save "BPassive")

;; We prove a correctness statement: for a proper train n, if b is its
;; block at time t, then the number N t b of the train occupying block
;; b at time t is n again.

;; NB
(set-goal "all in,ib,f,g,n((n=0 -> F) -> in(ib n)=n ->
 all t N in f g t(B in ib f g t n)=n)")
(assume "in" "ib" "f" "g" "n" "n=/=0" "InitHyp")
(ind)
;; Base
(ng #t)
(use "InitHyp")
;; Step
(assume "t" "IHt")
(drop "InitHyp")
(cases (pt "f t")) ;takes a while
;; Lef
(assume "Left")
(cases (pt "g t"))
;; g t=0
(assume "g t=0")
(simp "BLeftZero") ;takes a while
(ng #t)
(simp "Left")
(ng #t)
(simp "g t=0")
(ng #t)
(cases (pt "B in ib f g t n"))
(assume "Btn=0")
(ng #t)
(simphyp-with-to "IHt" "Btn=0" "SimpIHt")
(use "SimpIHt")
(assume "b" "Btn=b+1")
(ng #t)
(simphyp-with-to "IHt" "Btn=b+1" "SimpIHt")
(use "SimpIHt")
(use "g t=0")
(use "Left")
;; g t=b+1
(assume "b" "g t=b+1")
(cases (pt "b=B in ib f g t n")) ;takes a while
;; Case next block chosen
(assume "b=Btn")
(assert "B in ib f g(Succ t)n=B in ib f g t n")
 (use "BPassive")
 (simp "<-" "b=Btn")
 (simp "g t=b+1")
 (assume "Absurd")
 (use "Absurd")
(assume "B(t+1)n=Btn")
(simp "B(t+1)n=Btn") ;takes a while
(assert "N in f g(Succ t)(B in ib f g t n)=N in f g t(B in ib f g t n)")
 (use "NLeftNextFull" (pt "ib"))
 (use "Left")
 (simp "g t=b+1")
 (use "b=Btn")
 (simp "IHt")
 (use "n=/=0")
(assume "N(t+1)(Btn)=Nt(Btn)")
(simp "N(t+1)(Btn)=Nt(Btn)")
(use "IHt")
;; Case not next block chosen
(assume "b=/=Btn")
(cases (pt "Succ b=B in ib f g t n")) ;takes a while
;; SCase present block chosen
(assume "b+1=Btn")
(cases (pt "N in f g t b=0")) ;takes a while
;; SSCase previous block empty
(assume "Ntb=0")
(assert "B in ib f g(Succ t)n=b")
 (use "BLeftSuccActiveEmpty")
 (use "Left")
 (use "g t=b+1")
 (use "b+1=Btn")
 (use "Ntb=0")
(assume "B(t+1)n=b")
(assert "N in f g(Succ t)b=N in f g t(Succ b)")
 (use "NLeftNextEmpty" (pt "ib"))
 (use "Left")
 (use "g t=b+1")
 (use "Ntb=0")
(assume "N(t+1)b=Nt(b+1)")
(simp "B(t+1)n=b") ;takes a while
(simp "N(t+1)b=Nt(b+1)")
(simp "b+1=Btn")
(use "IHt")
;; SSCase previous block full
(assume "Ntb=/=0")
(assert "B in ib f g(Succ t)n=B in ib f g t n")
 (use "BLeftSuccActiveFull" (pt "b"))
 (use "Left")
 (use "g t=b+1")
 (simp "g t=b+1")
 (use "b+1=Btn")
 (use "Ntb=/=0")
(assume "B(t+1)n=Btn")
(assert "N in f g(Succ t)(Succ b)=N in f g t(Succ b)")
 (use "NLeftPresentFull" (pt "ib"))
 (use "Left")
 (use "g t=b+1")
 (use "Ntb=/=0")
(assume "N(t+1)(b+1)=Nt(b+1)")
(simp "B(t+1)n=Btn") ;takes a while
(simp "<-" "b+1=Btn")
(simp "N(t+1)(b+1)=Nt(b+1)")
(simp "b+1=Btn")
(use "IHt")
;; SCase not present block chosen
(assume "b+1=/=Btn")
(assert "B in ib f g(Succ t)n=B in ib f g t n")
 (use "BPassive")
 (simp "g t=b+1")
 (use "b+1=/=Btn")
(assume "B(t+1)n=Btn")
(assert "N in f g(Succ t)(B in ib f g t n)=N in f g t(B in ib f g t n)")
 (use "NLeftElse" (pt "ib"))
 (use "Left")
 (simp "g t=b+1")
 (use "b=/=Btn")
 (simp "g t=b+1")
 (use "b+1=/=Btn")
(assume "N(t+1)(Btn)=Nt(Btn)")
(simp "B(t+1)n=Btn") ;takes a while
(simp "N(t+1)(Btn)=Nt(Btn)")
(use "IHt")
;; ?_9:(f t -> F) -> N in f g(Succ t)(B in ib f g(Succ t)n)=n
;; This case for Right is similar, but simpler
(admit)
;; Proof finished.
(save "NB")

;; To prove our safety property we need some mor lemmata.

;; ActiveLeftFull
(set-goal "all in,ib,f,g,t,n(
 f t -> g t=B in ib f g t n ->
 (N in f g t(Pred(B in ib f g t n))=0 -> F) ->
 B in ib f g(Succ t)n=B in ib f g t n)")
(assume "in" "ib" "f" "g" "t" "n" "Left" "Active" "Full")
(ng #t)
(simp "Left")
(ng #t)
(cases (pt "g t"))
(assume "g t=0")
(use "Truth")
(assume "b" "g t=b+1")
(ng #t)
(assert "B in ib f g t n=g t")
 (simp "Active")
 (use "Truth")
(assume "Btn=g t")
(simphyp-with-to "Full" "Btn=g t" "SimpFull")
(simphyp-with-to "SimpFull" "g t=b+1" "SimpSimpFull")
(simp "SimpSimpFull")
(ng #t)
(cases 'auto)
(assume "b+1=Btn")
(use "b+1=Btn")
(assume "Useless")
(use "Truth")
;; Proof finished.
(save "ActiveLeftFull")

;; LowerBdMove
(set-goal "all in,ib,f,g,t,n B in ib f g t n<=Succ(B in ib f g(Succ t)n)")
(assume "in" "ib" "f" "g" "t" "n")
(ng #t)
(cases (pt "f t"))
(assume "Left")
(ng #t)
(cases (pt "g t=B in ib f g t n"))
(assume "g t=Btn")
(ng #t)
(simp "<-" "g t=Btn")
(cases (pt "g t"))
(assume "Useless")
(use "Truth")
(assume "b" "g t=b+1")
(ng #t)
(cases 'auto)
(assume "Useless")
(use "Truth")
(assume "Useless")
(use "Truth")
(assume "g t=/=Btn")
(use "Truth")
;; Right
(assume "Right")
(ng #t)
(cases (pt "g t=B in ib f g t n"))
(assume "g t=Btn")
(ng #t)
(simp "<-" "g t=Btn")
(cases 'auto)
(assume "Useless1")
(ng #t)
(use "NatLeTrans" (pt "Succ(g t)"))
(use "Truth")
(use "Truth")
(assume "Useless1")
(use "Truth")
(assume "Useless")
(ng #t)
(use "Truth")
;; Proof finished.
(save "LowerBdMove")

;; LeftLe
(set-goal "all in,ib,f,g,n,t(
 f t -> B in ib f g(Succ t)n<=B in ib f g t n)")
(assume "in" "ib" "f" "g" "n" "t" "Left")
(ng #t)
(simp "Left")
(ng #t)
(cases 'auto)
(assume "g t=Btn")
(ng #t)
(simp "<-" "g t=Btn")
(cases (pt "g t"))
(assume "g t=0")
(use "Truth")
(assume "b" "g t=b+1")
(ng #t)
(cases 'auto)
(assume "Useless")
(use "Truth")
(assume "Useless")
(use "Truth")
(assume "Useless")
(use "Truth")
;; Proof finished.
(save "LeftLe")

;; We can now prove our safety property, namely that no train can ever
;; pass another one.

;; NoPassing
(set-goal "all in,ib,n,m,f,g((n=0 -> F) -> (m=0 -> F) ->
 in(ib n)=n -> in(ib m)=m -> ib n<ib m ->
 all t B in ib f g t n<B in ib f g t m)")
(assume "in" "ib" "n" "m" "f" "g" "n=/=0" "m=/=0" "Hn" "Hm" "BaseHyp")
(ind)
;; Base
(ng #t)
(use "BaseHyp")
;; Step
(assume "t" "IHt")
(cases (pt "f t"))
;; Left
(assume "Left")
(cases (pt "g t=B in ib f g t n"))
;; True
(assume "g t=Btn")
;; Idea: B(t+1)n <= Btn < Btm = B(t+1)m
(assert "B in ib f g(Succ t)m=B in ib f g t m")
 (use "BPassive")
 (simp "g t=Btn")
 (assume "Btn=Btm")
 (simphyp-with-to "IHt" "Btn=Btm" "Absurd")
 (use "Absurd")
(assume "B(t+1)m=Btm")
(simp "B(t+1)m=Btm")
(use "NatLeLtTrans" (pt "B in ib f g t n"))
(use "LeftLe")
(use "Left")
(use "IHt")
;; False
(assume "g t=/=Btn")
;; Now we need to distinguish cases whether g t=Btm
(cases (pt "g t=B in ib f g t m"))
;; True
(assume "g t=Btm")
(assert "B in ib f g(Succ t)n=B in ib f g t n")
 (use "BPassive")
 (use "g t=/=Btn")
(assume "B(t+1)n=Btn")
(simp "B(t+1)n=Btn")

;; Idea: prove Btn < B(t+1)m by cases, using IHt: Btn < Btm.  In case
;; Btn+1 < Btm use LowerBdMove: Btm <= B(t+1)m+1 to get Btn < B(t+1)m.
;; In case Btn+1 = Btm train m has its left block full (for n>0).

(assert "Succ(B in ib f g t n)<=B in ib f g t m")
 (use "NatLtSuccToLe")
 (use "IHt")
(assume "Btn+1<=Btm")
(use "NatLeCases" (pt "Succ(B in ib f g t n)") (pt "B in ib f g t m"))
(use "Btn+1<=Btm")

(assume "Btn+1<Btm")
(assert "Succ(B in ib f g t n)<Succ(B in ib f g(Succ t)m)")
 (use "NatLtLeTrans" (pt "B in ib f g t m"))
 (use "Btn+1<Btm")
 (use "LowerBdMove")
(assume "Btn+1<B(t+1)m+1")
(use "Btn+1<B(t+1)m+1")

(assume "Btn+1=Btm")
;; Now use "ActiveLeftFull"
(assert "B in ib f g(Succ t)m=B in ib f g t m")
 (use "ActiveLeftFull")
 (use "Left")
 (simp "<-" "Btn+1=Btm")
 (simp "Btn+1=Btm")
 (use "g t=Btm")
 (simp "<-" "Btn+1=Btm")
 (ng #t)
 (assert "N in f g t(B in ib f g t n)=n")
  (use "NB")
  (use "n=/=0")
  (use "Hn")
 (assume "Nt(Btn)=n")
 (simp "Nt(Btn)=n")
 (use "n=/=0")
(assume "B(t+1)m=Btm")
(simp "B(t+1)m=Btm")
(use "IHt")
;; False
(assume "g t=/=Btm")
(assert "B in ib f g(Succ t)m=B in ib f g t m")
 (use "BPassive")
 (use "g t=/=Btm")
(assume "B(t+1)m=Btm")
(simp "B(t+1)m=Btm")
(assert "B in ib f g(Succ t)n=B in ib f g t n")
 (use "BPassive")
 (use "g t=/=Btn")
(assume "B(t+1)n=Btn")
(simp "B(t+1)n=Btn")
(use "IHt")
;; Right
(admit)
;; Proof finished.
(save "NoPassing")

