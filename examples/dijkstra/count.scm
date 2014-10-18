; $Id: count.scm 2577 2012-12-26 23:52:48Z miyamoto $

; (load "~/minlog/init.scm")
(set! DOT-NOTATION #t)
; Load the material about natural numbers plus an infinite object 
(libload "natinf.scm")

; The variable cp is used for subsets of the graph.

(add-var-name "cp" (py "nat=>boole"))

(add-program-constant "Adjoin" (py "(nat=>boole)=>nat=>nat=>boole") t-deg-one)
(add-computation-rule (pt "Adjoin cp m n") (pt "[if (n=m) True (cp n)]"))

; Notice that [if (n=m) True (cp n)] means (n=m) or (cp n).  However,
; using an if-term and not an or-constant has the advantage that the
; arguments are evaluated lazily.

; Card yields for cp and n the number of m<n such that (cp m)
(add-program-constant "Card" (py "(nat=>boole)=>nat=>nat") t-deg-one)

(add-computation-rule (pt "Card cp 0") (pt "0"))
(add-computation-rule (pt "Card cp(Succ n)")
		      (pt "Card cp n+++[if (cp n) 1 0]"))

; We prove Card-Bound: Card cp n<<Succ n ;(8) in [BS99]

; "CardBound"
(set-goal (pf "Card cp n<<Succ n"))
(assume "cp")
(ind)

; Base
(ng)
(use "Truth-Axiom")

;Step
(assume "n" "IH")
(ng)
(cases (pt "cp n"))

; Case "cp n"
(assume "cp n")
(ng)
(use "IH")

; Case "cp n -> F"
(assume "cp n -> F")
(ng)
(aga "Trans-<<" (pf "all n1,n2,n3(n1<<n2 -> n2<<n3 -> n1<<n3)"))
(use "Trans-<<" (pt "Succ n") )
(use "IH")
(use "Truth-Axiom")
(save "CardBound") ;was CountAx0

; We prove CardMaxImpAll: Card cp n=n -> m<<n -> cp m ;(9) in [BS99]

; "CardMaxImpAll"
(set-goal (pf "all cp,n,m(Card cp n=n -> m<<n -> cp m)"))
(assume "cp")
(ind)

; Base
(ng)
(strip)
(prop)

;Step
(assume "n" "IH" "m")
(ng)
(cases (pt "cp n"))

; Case "cp n"
(assume "cp n")
; (simp "cp n")
(ng)
(assume "Card cp n=n" "m<<Succ n")
(aga "NatLtSuccElim"
     (pf "all m,n(m<<Succ n -> (m<<n -> Pvar) -> (m=n -> Pvar) -> Pvar)"))
(use "NatLtSuccElim" (pt "m") (pt "n"))
(use "m<<Succ n")
(use "IH")
(use "Card cp n=n")
(assume "m=n")
(simp "m=n")
(use "cp n")

; Case "cp n -> F"
(assume "cp n -> F")
; (simp "cp n -> F")
(ng)
(assume "Card cp n=Succ n")
(cut (pf "Card cp n<<Succ n"))
(simp "Card cp n=Succ n")
(prop)
(use "CardBound")
(save "CardMaxImpAll") ;was CountAx2

; We prove CountExtern:SSS
; n<<Succ m -> Card(Adjoin cp m)n=Card cp n ;(10) in [BS99]

; "CountExtern"
(set-goal (pf "all cp,m,n(n<<Succ m -> Card(Adjoin cp m)n=Card cp n)"))
(assume "cp" "m")
(ind)

; Base
(ng)
(prop)

; Step
(assume "n" "IH")
(ng)
(cases (pt "cp n"))

; Case "cp n"
(assume "cp n")
(ng)
(assume "n<<m")
(use "IH")
(use "Trans-<<" (pt "m"))
(use "n<<m")
(use "Truth-Axiom")

; Case "cp n -> F"
(assume "cp n -> F")
(cases (pt "n=m"))

; Case "n=m"
(assume "n=m")
(simp "n=m")
(ng)
(prop)

; Case "n=m -> F"
(assume "n=m -> F")
(ng)
(assume "n<<m")
(use "IH")
(use "Trans-<<" (pt "m"))
(use "n<<m")
(use "Truth-Axiom")
(save "CountExtern") ;(10) in [BS99]

; We prove CountIntern ;(11) in [BS99]

; CountIntern
(set-goal (pf "all cp,m((cp m -> F) -> all n(m<<n -> 
                                       Card(Adjoin cp m)n=Succ(Card cp n)))"))
(assume "cp" "m" "cp m -> F")
(ind)

; Base
(prop)

; Step
(assume "n" "IH")
(assume "m<<Succ n")
(ng)
(cases (pt "n=m"))

; Case "n=m"
(assume "n=m")
(simp "n=m")
(ng)
; (simp "n=m")
(simp "cp m -> F")
(ng)
(use "CountExtern")
(use "Truth-Axiom")

; Case "n=m -> F"
(assume "n=m -> F")
(ng)
(cases (pt "cp n"))

; Case "cp n"
(assume "cp n")
; (simp "cp n")
(ng)
(use "IH")
(aga "Succ-Lemma" (pf "all m,n(m<<Succ n -> (n=m -> F) -> m<<n)"))
(use "Succ-Lemma")
(use "m<<Succ n")
(use "n=m -> F")

; Case "cp n -> F"
(assume "cp n -> F")
(ng)
(use "IH")
(use "Succ-Lemma")
(use "m<<Succ n")
(use "n=m -> F")
(save "CountIntern") ;(11) in [BS99]

; We prove all m(m<<n -> cp m) -> Card cp n=n ;(12) in [BS99]

; "CardAllImpMax"
(set-goal (pf "all cp,n(all m(m<<n -> cp m) -> Card cp n=n)"))
(assume "cp")
(ind)

; Base
(ng)
(strip)
(use "Truth-Axiom")

; Step
(assume "n" "IH")
(ng)
(cases (pt "cp n"))

; Case "cp n"
(assume "cp n")
(ng)
(assume "all m(m<<Succ n -> cp m)")
(use "IH")
(assume "m" "m<<n")
(use "all m(m<<Succ n -> cp m)")
(use "Trans-<<" (pt "n"))
(use "m<<n")
(use "Truth-Axiom")

; Case "cp n -> F"
(assume "cp n -> F")
(ng)
(assume "all m(m<<Succ n -> cp m)")
(cut (pf "cp n"))
(prop)
(use "all m(m<<Succ n -> cp m)")
(use "Truth-Axiom")
(save "CardAllImpMax") ;(12) in [BS99]
