; $Id: wf.scm 2577 2012-12-26 23:52:48Z miyamoto $

; We prove the well-foundedness of the natural numbers plus an infinite
; object, in the sense that every sequence d with a finite starting
; point, which is strictly decreasing on positive numbers, has a first
; member where it is zero.

; (add-var-name "d" (py "nat=>nat yplus unit"))

; First we prove some auxiliary claims.

; "NatinfLtSuccElim"
(set-goal (pf "all k,x.x<Inl(Succ k) -> (x<Inl k -> Pvar) -> 
                                        (x=Inl k -> Pvar) -> Pvar"))
(assume "k" "x" "x<Inl(Succ k)" "Case<" "Case=")
(cases (pt "x<Inl k"))
(prop)
(aga "NatinfLtSuccImpEq"
     (pf "all x,k.x<Inl(Succ k) -> (x<Inl k -> F) -> x=Inl k"))
(assume "x<Inl k -> F")
(use "Case=")
(use "NatinfLtSuccImpEq")
(use "x<Inl(Succ k)")
(prop)
(save "NatinfLtSuccElim")

(define neterm (nt (proof-to-extracted-term
		    (theorem-name-to-proof "NatinfLtSuccElim"))))

; (pp neterm)
; [n0,x1,(alpha5)_2,(alpha5)_3][if (x1<=Inl n0) (alpha5)_2 (alpha5)_3]

; "NatinfLeInfElim"
(set-goal
 (pf "all x.(x<(DummyR nat)-> Pvar) -> (x=(DummyR nat)-> Pvar) -> Pvar"))
(cases)

; Case nat
(assume "n" "T -> Pvar" "F -> Pvar")
(use "T -> Pvar")
(use "Truth-Axiom")

; Case unit
;(cases)
(assume "F -> Pvar" "T -> Pvar")
(use "T -> Pvar")
(use "Truth-Axiom")
(save "NatinfLeInfElim")

; "NatinfBound"
(set-goal (pf "all x,y.x<y -> ex k x<Inl(Succ k)"))
(cases)

; Case nat
(assume "n" "y" "Inl n<y")
(ex-intro (pt "n"))
(use "Truth-Axiom")

; Case unit
(assume "y" "F")
(ex-intro (pt "0"))
(use "F")
(save "NatinfBound")

(define neterm
  (nt (proof-to-extracted-term (theorem-name-to-proof "NatinfBound"))))

(pp (nt neterm))
; "[x0,x1][if x0 ([n2]n2) 0]"

; "LeastAuxExThm"
(set-goal (pf "all k,d.d 0<Inl(Succ k) -> (all n.Inl 0<d n -> d(Succ n)<d n) ->
                 ex n.d n=Inl 0 & all m(m<<n -> Inl 0<d m)"))
(ind)

; Base
(assume "d" "d-0-Bound" "d-Decreases")
(ex-intro (pt "0"))
(split)
(aga "Inl-Lt-1-imp-0" (pf "all x.x<Inl 1 -> x=Inl 0"))
(use "Inl-Lt-1-imp-0")
(use "d-0-Bound")
(assume "m")
(prop)

; Step
(assume "k" "IH" "d" "d-0-Bound" "d-Decreases")
(use "NatinfLtSuccElim" (pt "Succ k") (pt "d 0"))
(use "d-0-Bound")

; Case d 0<Inl(Succ k)
(assume "d 0<Inl(Succ k)")
(use "IH")
(use "d 0<Inl(Succ k)")
(use "d-Decreases")

; Case d 0=Inl(Succ k)
(assume "d 0=Inl(Succ k)")
(cut (pf "d 1<Inl(Succ k)"))
(assume "d 1<Inl(Succ k)")
(inst-with-to "IH" (pt "[n]d(Succ n)") "IH-for-[n]d(Succ n)")
(drop "IH")
(ng)
(cut (pf "ex n.d(Succ n)=Inl 0 & (all m.m<<n -> Inl 0<d(Succ m))"))
(assume "ExHyp")
(by-assume-with "ExHyp" "n1" "n1Hyp")
; (ex-elim "ExHyp")
; (assume "n1" "n1Hyp")
; (drop "ExHyp")
(ex-intro (pt "Succ n1"))
(drop "IH-for-[n]d(Succ n)")
(split)
(use "n1Hyp")
(cases)

; Case m=0
(simp "d 0=Inl(Succ k)")
(assume "Triv")
(aga "<-Ax13" (pf "all x1,x2.x1<x2 -> Inl 0<x2"))
(use "<-Ax13" (pt "d 1"))
(use "d 1<Inl(Succ k)")

; Case m successor
(use "n1Hyp")

(use "IH-for-[n]d(Succ n)")
(prop)

(assume "n")
(use "d-Decreases")

; d 1<Inl(Succ k)
(cut (pf "d 1<d 0"))
(simp "d 0=Inl(Succ k)")
(prop)
(use "d-Decreases")
(simp "d 0=Inl(Succ k)")
(use "Truth-Axiom")
(save "LeastAuxExThm")

; proves "all k,d.d 0<Inl(Succ k) -> (all n.Inl 0<d n -> d(Succ n)<d n) ->
;                  ex n.d n=Inl 0 & all m.m<<n -> Inl 0<d m"

(add-var-name "D" (py "(nat=>nat ysumu)=>nat"))

(define neterm
  (nt (proof-to-extracted-term (theorem-name-to-proof "LeastAuxExThm"))))
; (pp neterm)

(animate "NatinfLtSuccElim")

(define neterm
  (nt (proof-to-extracted-term (theorem-name-to-proof "LeastAuxExThm"))))
; (pp neterm)

; (Rec nat=>(nat=>nat yplus unit)=>nat)([d2]0)
; ([n2,D3,d4][if (d4 0<Inl(Succ n2)) (D3 d4) (Succ(D3([n5]d4(Succ n5))))])

(define soundness-proof (proof-to-soundness-proof
			 (theorem-name-to-proof "LeastAuxExThm")))
; (pp (rename-variables (nf (proof-to-formula soundness-proof))))

; We introduce "LeastAux" as an abbreviation for eterm.

(add-program-constant
 "LeastAux" (py "nat=>(nat=>nat ysumu)=>nat") t-deg-one)

(aga "LeastAuxDef" (make-eq (pt "LeastAux") neterm))

; "LeastAuxThm"
(set-goal
 (pf "all n1,d.d 0<Inl(Succ n1) -> (all n.Inl 0<d n -> d(Succ n)<d n) ->
        d(LeastAux n1 d)=Inl 0 & (all m.m<<LeastAux n1 d -> Inl 0<d m)"))
(simp "LeastAuxDef")
(use-with soundness-proof)
(save "LeastAuxThm")

; (pp (proof-to-formula (theorem-name-to-proof "LeastAuxThm")))


; "LeastExThm"
(set-goal (pf "all d.(all n.Inl 0<d n -> d(Succ n)<d n) ->
                     ex n.d n=Inl 0 & all m(m<<n -> Inl 0<d m)"))
(assume "d" "d-Decreases")
(use "NatinfLeInfElim" (pt "d 0"))

; Case d 0<Inr Dummy
(assume "d 0<Inr Dummy")
(cut (pf "ex k d 0<Inl(Succ k)"))
(assume "ex k d 0<Inl(Succ k)")
(by-assume-with "ex k d 0<Inl(Succ k)" "k" "d 0<Inl(Succ k)")
(use "LeastAuxExThm" (pt "k"))
(use "d 0<Inl(Succ k)")
(use "d-Decreases")
(use "NatinfBound" (pt "(DummyR nat)"))
(use "d 0<Inr Dummy")

; Case d 0=Inr Dummy
(assume "d 0=Inr Dummy")
(cut (pf "ex k d 1<Inl(Succ k)"))
(assume "ex k d 1<Inl(Succ k)")
(by-assume-with "ex k d 1<Inl(Succ k)" "k" "d 1<Inl(Succ k)")
(cut (pf "ex n.d(Succ n)=Inl 0 & (all m.m<<n -> Inl 0<d(Succ m))"))
(assume "Shifted-Goal")
(by-assume-with "Shifted-Goal" "n" "Kernel-for-n")
(ex-intro (pt "Succ n"))
(split)
(use "Kernel-for-n")
(cases)

; Case 0
(assume "T")
(simp "d 0=Inr Dummy")
(use "Truth-Axiom")

; Case Succ m
(assume "m" "m<<n")
(use "Kernel-for-n")
(use "m<<n")

; Now the shifted goal
(use-with "LeastAuxExThm" (pt "k") (pt "[k]d(Succ k)")
	  DEFAULT-GOAL-NAME DEFAULT-GOAL-NAME) 
; Notice: use does not work here, because it uses first order matching only

(ng)
(use "d 1<Inl(Succ k)")
(ng)
(assume "n")
(use "d-Decreases")
(use "NatinfBound" (pt "(DummyR nat)"))
(cut (pf "d 1<d 0"))
(simp "d 0=Inr Dummy")
(prop)
(use "d-Decreases")
(simp "d 0=Inr Dummy")
(use "Truth-Axiom")
(save "LeastExThm")

; proves all d.(all n.Inl 0<d n -> d(Succ n)<d n) ->
;              ex n.d n=Inl 0 & all m.m<<n -> Inl 0<d m

(define neterm
  (nt (proof-to-extracted-term (theorem-name-to-proof "LeastExThm"))))
; (pp neterm)

; [d0](cLeqXxInfXxElim nat)
;  (d0 0)
;  (cLeastXxAuxXxExXxThm(cNatinfXxBound(d0 0)Inr Dummy)d0)
;  (Succ(cLeastXxAuxXxExXxThm(cNatinfXxBound(d0 1)Inr Dummy)([n1]d0(Succ n1))))

(animate "NatinfLeInfElim")
(animate "LeastAuxExThm")
(animate "NatinfBound")

(define neterm
  (nt (proof-to-extracted-term (theorem-name-to-proof "LeastExThm"))))
; (pp neterm)

; Notice that (term-to-t-deg neterm) evaluates to 1.  The reason is that
; neterm will give a value for every d, but it will be the least zero only
; if d satisfies the assumptions.

(define soundness-proof1 (proof-to-soundness-proof
			  (theorem-name-to-proof "LeastExThm")))
; (pp (nf (proof-to-formula soundness-proof1)))
; (cdp soundness-proof1)

; We introduce an "Least" as an abbreviation for neterm.

(add-program-constant "Least" (py "(nat=>nat ysumu)=>nat") t-deg-one)

(aga "LeastDef" (make-eq (pt "Least") neterm))

; "LeastThm"
(set-goal
 (pf "all d.(all n.Inl 0<d n -> d(Succ n)<d n) ->
               d(Least d)=Inl 0 & all m(m<<Least d -> Inl 0<d m)"))
(simp "LeastDef")
(use-with soundness-proof1)
(save "LeastThm")

; (pp (proof-to-formula (theorem-name-to-proof "LeastThm")))
