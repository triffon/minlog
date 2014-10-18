; $Id: pick.scm 2577 2012-12-26 23:52:48Z miyamoto $

; (load "~/minlog/init.scm")

; We need some basic notions of the Dijkstra algorithm.

(add-var-name "a" "c" (py "nat"))
(add-var-name "d" (py "nat=>nat ysumu"))
(add-program-constant "N" (py "nat") t-deg-one)

; We have used

; (aga "PickAx" (pf "all cp,d(
;  Card cp N<<N -> 
;  Pick cp d<<N & 
;  (cp(Pick cp d) -> F) & all a(a<<N -> d a<d(Pick cp d) -> cp a))"))

; To justify this global assumption, we prove

; "PickExThmGen"
(set-goal (pf "all cp,d,n 
 ex c(
  d N=(DummyR nat) -> 
  (Card cp n<<n -> c<<n & (cp c -> F) & all a(a<<n -> d a<d c -> cp a)) & 
  (Card cp n=n -> c=N))"))
(assume "cp" "d")
(ind)

; Base
(ex-intro (pt "N"))
(assume "d N=(DummyR nat)")
(split)
(assume "Absurd")
(use "Efq")
(use "Absurd")
(assume "Useless")
(use "Truth-Axiom")

; Step
(assume "n" "IH1")
(by-assume-with "IH1" "c" "IH")

(cases (pt "[if (cp n) True (d c<d n)]"))

; Case 1: (cp n) or (d c<d n)
(assume "(cp n) or (d c<d n)")
(ex-intro (pt "c"))
(assume "d N=(DummyR nat)")
(split)

; Card cp(Succ n)<<Succ n
(assume "Card cp(Succ n)<<Succ n")
(cases (pt "Card cp n<<n"))

; Case 1.1: Card cp n<<n
(assume "Card cp n<<n")
(split)

; c<<Succ n
(aga "Lt-Succ" (pf "all m,n(m<<n -> m<<Succ n)"))
(search 1 '("Lt-Succ" 1))
(split)

; cp c -> F
(search 1)

; all a(a<<Succ n -> d a<d c -> cp a)
(assume "a")
(cases (pt "a<<n"))

; Case 1.1.1: a<<n
(search 1)

; Case 1.1.2: a<<n -> F
(aga "<<-Ax10" (pf "all m,n(m<<Succ n -> (m<<n -> F) -> m=n)"))
(assume "a<<n -> F" "a<<Succ n")
(inst-with-to "<<-Ax10" (pt "a") (pt "n") "a<<Succ n" "a<<n -> F" "a=n")
(simp "a=n")
(assume "d n<d c")
(aga "<-Ax11" (pf "all x1,x2(x1<x2 -> x2<x1 -> F)"))
(inst-with-to "<-Ax11" (pt "d n") (pt "d c") "d n<d c" "d c<d n -> F")
(cut (pf "[if (cp n) True (d c<d n)]"))
(simp "d c<d n -> F")
(ng)
(prop)
(prop)

; Case 1.2: Card cp n<<n -> F
(assume "Card cp n<<n -> F")
(cut (pf "Card cp(Succ n)<<Succ n"))
(cut (pf "Card cp(Succ n)=Succ n"))
(assume "Card cp(Succ n)=Succ n")
(simp "Card cp(Succ n)=Succ n")
(prop)
(use "CardAllImpMax")
(assume "m" "m<<Succ n")
(use "NatLtSuccElim" (pt "m") (pt "n"))
(use "m<<Succ n")
(use "CardMaxImpAll")
(use "<<-Ax10")
(use "CardBound")
(use "Card cp n<<n -> F")
(assume "m=n")
(simp "m=n")
(cut (pf "[if (cp n) True (d c<d n)]"))
(cut (pf "c=N"))
(assume "c=N")
(simp "c=N")
(simp "d N=(DummyR nat)")
(prop)
(use "IH")
(use "d N=(DummyR nat)")
(use "<<-Ax10")
(use "CardBound")
(use "Card cp n<<n -> F")
(use "(cp n) or (d c<d n)")
(use "Card cp(Succ n)<<Succ n")
(assume "Card cp(Succ n)=Succ n")
(use "IH")
(use "d N=(DummyR nat)")
(use "CardAllImpMax")
(assume "m" "m<<n")
(use "CardMaxImpAll" (pt "Succ n"))
(use "Card cp(Succ n)=Succ n")
(use "Lt-Succ")
(use "m<<n")

; Case 2: Neither cp n nor d c<d n
(assume "[if (cp n) True (d c<d n)] -> F")
(ex-intro (pt "n"))
(assume "d N=(DummyR nat)")
(split)

; Card cp(Succ n)<<Succ n
(assume "Card cp(Succ n)<<Succ n")
(split)

; n<<Succ n
(ng)
(use "Truth-Axiom")
(split)

; cp n -> F
(assume "cp n")
(cut (pf "[if (cp n) True (d c<d n)] -> F"))
(simp "cp n")
(ng)
(prop)
(prop)

; all a(a<<Succ n -> d a<d n -> cp a)
(assume "a" "a<<Succ n" "d a<d n")
(cases (pt "a<<n"))

; Case 2.1: a<<n
(cases (pt "Card cp n<<n"))

; Case 2.1.1: Card cp n<<n
(aga "<-Ax6" (pf "all x1,x2,x3(x1<x2 -> x2<=x3 -> x1<x3)"))
(aga "OrConst-<-Ax"
     (pf "all cp,n,x,d(([if (cp n) True (x<d n)] -> F) -> d n<=x)"))
; (search 1 '("<-Ax6" 1) '("OrConst-<-Ax" 1)) ;reason: non-pattern encountered
(assume "Card cp n<<n" "a<<n")
(use "IH")
(prop)
(prop)
(prop)
(use "<-Ax6" (pt "d n"))
(prop)
(use "OrConst-<-Ax" (pt "cp"))
(prop)

; Case 2.1.2: (Card cp n<<n -> F)
; (aga "CountAx3" (pf "all cp,n((Card cp n<<n -> F) -> all a(a<<n -> cp a))"))
; (search 1 '("CountAx3" 1))
; sorry, no proof found ;reason: non-pattern encountered
(assume "Card cp n<<n -> F")
(use "CardMaxImpAll")
(use "<<-Ax10")
(use "CardBound")
(use "Card cp n<<n -> F")

; Case 2.2: a<<n -> F
(assume "a<<n -> F")
; (pp "<<-Ax10")
; all m,n(m<<Succ n -> (m<<n -> F) -> m=n)
(inst-with-to "<<-Ax10" (pt "a") (pt "n") "a<<Succ n" "a<<n -> F" "a=n")
(cut (pf "d a<d n"))
(simp "a=n")
(prop)
(prop)

; Card cp(Succ n)=Succ n -> n=N
(assume "Card cp(Succ n)=Succ n")
(cut (pf "cp n"))
(assume "cp n")
(cut (pf "[if (cp n) True (d c<d n)] -> F"))
(simp "cp n")
(ng)
(prop)
(prop)
(use "CardMaxImpAll" (pt "Succ n"))
(prop)
(prop)
; Proof finished.
(save "PickExThmGen")
(remove-theorem "PickExThm")

; (pp "PickExThmGen")

;; all cp,d,n 
;;  ex c(
;;   d N=(DummyR nat) -> 
;;   (Card cp n<<n -> c<<n & (cp c -> F) & all a(a<<n -> d a<d c -> cp a)) & 
;;   (Card cp n=n -> c=N))


(define neterm
  (nt (proof-to-extracted-term (theorem-name-to-proof "PickExThmGen"))))
; (pp neterm)

;; [cp0,d1,n2]
;;  (Rec nat=>nat)n2 N([n3,n4][if [if (cp0 n3) True (d1 n4<d1 n3)] n4 n3])

(define soundness-proof
  (proof-to-soundness-proof (theorem-name-to-proof "PickExThmGen")))

;(pp (rename-variables (nf (proof-to-formula soundness-proof))))

;; all cp,d,n(
;;  d N=(DummyR nat) -> 
;;  (Card cp n<<n -> 
;;   (Rec nat=>nat)n N([n0,n1][if (cp n0) n1 [if (d n1<d n0) n1 n0]])<<n & 
;;   (cp((Rec nat=>nat)n N([n0,n1][if (cp n0) n1 [if (d n1<d n0) n1 n0]])) -> F) &
;;   all a(
;;    a<<n -> 
;;    d a<d((Rec nat=>nat)n N([n0,n1][if (cp n0) n1 [if (d n1<d n0) n1 n0]])) -> 
;;    cp a)) & 
;;  (Card cp n=n -> 
;;   (Rec nat=>nat)n N([n0,n1][if (cp n0) n1 [if (d n1<d n0) n1 n0]])=N))

; The special case we are interested in is

; "PickExThm"
(set-goal (pf "all cp,d ex c(d N=(DummyR nat) -> Card cp N<<N -> 
                              c<<N & 
                              (cp c -> F) & 
                              all a(a<<N -> d a<d c -> cp a))"))
(assume "cp" "d")
(inst-with "PickExThmGen" (pt "cp") (pt "d") (pt "N"))
(by-assume-with 1 "c" "Kernel")
(ex-intro (pt "c"))
(prop)
; Proof finished.
(save "PickExThm")

(define neterm
  (nt (proof-to-extracted-term (theorem-name-to-proof "PickExThm"))))
; (pp neterm)

; [cp0,d1]cPickExThmGen cp0 d1 N

(animate "PickExThmGen")

(define neterm
  (nt (proof-to-extracted-term (theorem-name-to-proof "PickExThm"))))
; (pp neterm)

; [cp0,d1](Rec nat=>nat)N N([n2,n3][if (cp0 n2) n3 [if (d1 n3<d1 n2) n3 n2]])

(define soundness-proof1
  (proof-to-soundness-proof (np (theorem-name-to-proof "PickExThm"))))

; We introduce "Pick" as an abbreviation for neterm

(add-program-constant
 "Pick" (py "(nat=>boole)=>(nat=>nat ysumu)=>nat") t-deg-one)

(aga "PickDef" (make-eq (pt "Pick") neterm))

; "PickThm"
(set-goal (pf "all cp,d(
 d N=(DummyR nat) -> 
 Card cp N<<N -> 
 Pick cp d<<N & 
 (cp(Pick cp d) -> F) & all a(a<<N -> d a<d(Pick cp d) -> cp a))"))
(simp "PickDef")
(use-with soundness-proof1)
; Proof finished.
(save "PickThm")

; (cdp soundness-proof1)

