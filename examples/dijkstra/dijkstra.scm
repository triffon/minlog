;; $Id: dijkstra.scm 2581 2012-12-27 02:01:15Z miyamoto $

;; (load "~/git/minlog/init.scm")

;; Based on
;; @InProceedings{BenlSchwichtenberg99,
;;   author = 	 {Holger Benl and Helmut Schwichtenberg},
;;   title = 	 {{Formal correctness proofs of functional programs:
;;                   Dijkstra's algorithm, a case study}},
;;   booktitle = 	 {Computational Logic},
;;   editor =	 {U. Berger and H. Schwichtenberg},
;;   volume =	 {165},
;;   series =	 {Series F: Computer and Systems Sciences},
;;   year =	 {1999},
;;   publisher =	 sv,
;;   organization = {Proceedings of the NATO Advanced Study Institute on
;;                   Computational Logic, held in Marktoberdorf,
;;                   Germany,  July 29 -- August 10, 1997},
;;   pages =	 {113--126}}


;; Load count.scm pick.scm wf.scm
;; count.scm provides material about natural numbers plus an infinite object.
;; This can also be loaded separately: (libload "natinf.scm")
(set! COMMENT-FLAG #f)
(exload "dijkstra/count.scm")
(exload "dijkstra/pick.scm")
(exload "dijkstra/wf.scm")
(set! COMMENT-FLAG #t)

;; The basic notions for the Dijkstra algorithm

;; (add-var-name "a" "b" "c" "i" "j" (py "nat"))
(add-var-name "b" "i" "j" (py "nat"))
(add-var-name "f" "g" "h" (py "nat=>nat"))
(add-var-name "s" (py "nat ysumu"))
;; (add-var-name "cp" (py "nat=>boole"))
(add-var-name "nxt" (py "nat=>nat"))
;; (add-var-name "d" (py "nat=>nat ysumu"))

;; Number of nodes
;; (add-program-constant "N" (py "nat") t-deg-one)

;; The weight function
(add-program-constant "W" (py "nat=>nat=>nat ysumu") t-deg-one)

(add-computation-rule "W 0 0" "Inl 0")
(add-global-assumption "W-Zero" "all a,b(W a b=Inl 0 -> a=b)")
(add-global-assumption "W-N" "all a(a<<N -> W a N=(DummyR nat))")
;; (add-computation-rule (pt "W(Succ i)0") (pt "W 0(Succ i)"))
;; (add-rewrite-rule (pt "W i i") (pt "Inl 0"))

;; The sum of weights
(add-program-constant "S" (py "(nat=>nat)=>nat=>nat ysumu") t-deg-one)

(add-computation-rules
 "S f 0" "Inl 0"
 "S f(Succ m)" "S f m+W(f m)(f(Succ m))")


;; 1.  The final statemen
;; =======================

;; First we need some auxiliary arguments (for to prove h n=0 later)
;; Proof of "h n=0"

;; d-Zero
(set-goal "all nxt,d(all a(0<<a -> nxt a=a -> F) ->
                              all a d a=d(nxt a)+W(nxt a)a ->
                              all a(d a=Inl 0 -> a=0))")
(assume "nxt" "d" "(2)" "(4)" "a" "d a=Inl 0")
(add-global-assumption "<<-Ax13" "all n((0<<n -> F) -> n=0)")
(use "<<-Ax13")
(assume "0<<a")
(use-with "(2)" (pt "a") "0<<a" "?")
(use "W-Zero")
(cut "d a=d(nxt a)+W(nxt a)a")
(simp "d a=Inl 0")
(add-global-assumption "+-Property" "all x,y(Inl 0=x+y -> y=Inl 0)")
(use "+-Property")
(use "(4)")
;; Proof finished.
(save "d-Zero")

;; To increase readability, we introduce a constant It to write It nxt a
;; for (Rec nat=>nat)a([n]nxt), with the following computation rules:

(add-program-constant "It" (py "(nat=>nat)=>nat=>nat=>nat") t-deg-one)

(add-computation-rules
 "It nxt a 0" "a"
 "It nxt a(Succ n)" "nxt(It nxt a n)")

;; h n=0
(set-goal "all nxt,d,a(d 0=Inl 0 ->
                              all a(0<<a -> nxt a=a -> F) ->
                              all a d(nxt a)<(DummyR nat) ->
                              all a d a=d(nxt a)+W(nxt a)a ->
                              It nxt a(Least([j]d(It nxt a j)))=0)")
(assume "nxt" "d" "a" "(1)" "(2)" "(3)" "(4)")
(use "d-Zero" (pt "nxt") (pt "d"))
(use "(2)")
(use "(4)")
(use-with "LeastThm" (pt "[j]d(It nxt a j)") "?" 'left)
;; use does not work here: it only applies first order unification
(ng)
(assume "n" "Inl 0<d(It nxt a n)")
(add-global-assumption "<-Ax15"
  "all x,y,z(x=y+z -> y<(DummyR nat) -> (z=Inl 0 -> F) -> y<x)")
(use "<-Ax15" (pt "W(nxt(It nxt a n))(It nxt a n)"))
(use "(4)")
(use "(3)")
(assume "W(nxt(It nxt a n))(It nxt a n)=Inl 0")
(cut "nxt(It nxt a n)=It nxt a n")
(use "(2)")
(add-global-assumption "<<-Ax14" "all n((n=0 -> F) -> 0<<n)")
(use "<<-Ax14")
(assume "It nxt a n=0")
(cut "Inl 0<d(It nxt a n)")
(simp "It nxt a n=0")
(simp "(1)")
(prop)
(use "Inl 0<d(It nxt a n)")
(use "W-Zero")
(use "W(nxt(It nxt a n))(It nxt a n)=Inl 0")
;; Proof finished.
(save "h n=0")

;; We now prove the final auxiliary statement.

;; In the lecture notes we also had n<<N in the conclusion.  This is
;; correct, but does not add anything to the meaning of the theorem.
;; For simplicity it is omitted here.

;;  FinalAuxTheorem
(set-goal
 "all nxt,d(d 0=Inl 0 ->
                all a(0<<a -> nxt a=a ->F) ->
                all a d(nxt a)<(DummyR nat) ->
                all a d a=d(nxt a)+W(nxt a)a ->
                all a,b(b<<N -> d a<=d b+W b a) ->
                all a(a<<N -> ex s((ex g,n.g 0=0 & g n=a & S g n=s) &
                                   all f,m(all i f i<<N ->
                                           f 0=0 -> f m=a -> s<=S f m))))")

;; Proof idea.  Let s:=d a.  Form h by iterating nxt, starting with a.
;; This decreases in the sense of measure d.  Let n be least with h n=0.
;; Set g i:=h(n-i).

;; To construct this least n, use Least([j]d(h j)).  Recall
(pp "LeastThm")

;; all d(
;;  all n(Inl 0<d n -> d(Succ n)<d n) ->
;;  d(Least d)=Inl 0 & all m(m<<Least d -> Inl 0<d m))

(assume "nxt" "d" "(1)" "(2)" "(3)" "(4)" "(5)" "a" "a<<N")
(ex-intro (pt "d a"))
(split)

;; We introduce g as [i]h(n-i) with n=Least([i]d(It nxt a i))

(ex-intro (pt "[i]It nxt a(Least([j]d(It nxt a j))-i)"))
;; g
(ex-intro (pt "Least([j]d(It nxt a j))"))
;; n

(split)
(ng)

;; ?_10: It nxt a(Least([j]d(It nxt a j)))=0 ;h n=0
(use "h n=0")
(use "(1)")
(use "(2)")
(use "(3)")
(use "(4)")
(split)

;; ?_15: ([i]It nxt a(Least([j]d(It nxt a j))-i))(Least([j]d(It nxt a j)))=a
(ng)
(use "Truth")

;; ?_16: S([i]It nxt a(Least([j]d(It nxt a j))-i))(Least([j]d(It nxt a j)))=d a
;; S g n=d a

(cut "all j(j<<Succ(Least([j]d(It nxt a j))) ->
           S([i]It nxt a(Least([j]d(It nxt a j))-i))j=
           d(It nxt a(Least([j]d(It nxt a j))-j)))")
(assume "Sum-Property")
(use-with "Sum-Property" (pt "Least([j]d(It nxt a j))") "?")
(ng)
(use "Truth")

(ind)

;; Base
(assume "Triv")
(drop "Triv")
(ng)

(cut "It nxt a(Least([j]d(It nxt a j)))=0")
(assume "h n=0-Hyp")
(simp "h n=0-Hyp")
(simp "(1)")
(use "Truth")

(use "h n=0")
(use "(1)")
(use "(2)")
(use "(3)")
(use "(4)")

;; Step
(assume "j" "IH")
(ng)
(assume "j<<n")
(cut "S([n0]It nxt a(Least([j]d(It nxt a j))-n0))j=
          d(It nxt a(Least([j]d(It nxt a j))-j))")
(assume "S(g,j)=d(h(n-j))")
(simp "S(g,j)=d(h(n-j))")
(drop "S(g,j)=d(h(n-j))")

(cut "Least([j]d(It nxt a j))-j=Succ(Pred(Least([j]d(It nxt a j))-j))")
(assume "n-j=Succ(Pred(n-j))")
(simp "n-j=Succ(Pred(n-j))")
(drop "n-j=Succ(Pred(n-j))")
(ng)
(inst-with "(4)" (pt "It nxt a(Pred(Least([j]d(It nxt a j))-j))"))
(simp 11)
(drop 11)
(ng)
(use "Truth")

;; ?_46: Least([j]d(It nxt a j))-j=Succ(Pred(Least([j]d(It nxt a j))-j))
(add-global-assumption "Succ-Pred" "all j,n(j<<n -> n-j=Succ(Pred(n-j)))")
(use "Succ-Pred")
(use "j<<n")

;; ?_41: S([n0]It nxt a(Least([j]d(It nxt a j))-n0))j=
;; d(It nxt a(Least([j]d(It nxt a j))-j))
(use "IH")
(add-global-assumption "Lt-Succ" "all j,n(j<<n -> j<<Succ n)")
(use "Lt-Succ")
(use "j<<n")

;; ?_5: all f,m(all i f i<<N -> f 0=0 -> f m=a -> d a<=S f m)

(assume "f" "m" "f-in-V" "f 0=0" "f m=a")
(cut "all m d(f m)<=S f m")
(assume "all m d(f m)<=S f m")
(add-global-assumption "Symm-=-nat" "all a,b(a=b -> b=a)")
(cut "a=f m")
(assume "a=f m")
(simp "a=f m")
(use "all m d(f m)<=S f m")
(use "Symm-=-nat")
(use "f m=a")

;; ?_60: all m d(f m)<=S f m
(ind)

;; Base
(simp "f 0=0")
(ng)
(simp "(1)")
(ng)
(use "Truth")

;; Step
(assume "i" "IH")
(ng)
(add-global-assumption "Trans-<=" "all x,y,z(x<=y -> y<=z -> x<=z)")
(use "Trans-<=" (pt "d(f i)+W(f i)(f(Succ i))"))
(use "(5)")
(use "f-in-V")
(add-global-assumption "<=-Mon-+-1" "all x1,x2,y(x1<=x2 -> x1+y<=x2+y)")
(use "<=-Mon-+-1")
(use "IH")
;; Proof finished.
(save "FinalAuxTheorem")

(define neterm
  (rename-variables
   (nt (proof-to-extracted-term (theorem-name-to-proof "FinalAuxTheorem")))))
;; (pp neterm)
;; [f,d,n]d n@([n0]It f n(Least([n1]d(It f n n1))-n0))@Least([n0]d(It f n n0))

;; i.e., with f -> nxt, n -> a, n0 -> i, n1 -> j

;; "[nxt,d,a]d a@
;;           ([i]It nxt a(Least([j]d(It nxt a j))-i))@
;;           Least([i]d(It nxt a i))"


;; 2.  Construction of nxt and d
;; =============================

;; We now construct functions nxt,d such that (1)-(5) hold.

;; (add-program-constant "Count" (py "(nat=>boole)=>nat") t-deg-one)

(add-program-constant "Newcp" (py "(nat=>boole)=>nat=>nat=>boole") t-deg-one)
(add-program-constant "Newnxt"
		      (py "(nat=>nat)=>(nat=>nat ysumu)=>nat=>nat=>nat")
		      t-deg-one)
(add-program-constant "Newd"
		      (py "(nat=>nat ysumu)=>nat=>nat=>nat ysumu")
		      t-deg-one)

(set-goal
 "all n(n<<N -> ex cp,nxt,d(
                      d N=(DummyR nat) &
                      Card cp N=Succ n &
                      d 0=Inl 0 &
                      all a(0<<a -> nxt a=a -> F) &
                      all a cp(nxt a) &
                      all a d(nxt a)<(DummyR nat) &
                      all a d a=d(nxt a)+W(nxt a)a &
                      all a,b(cp b -> d a<=d b+W b a) &
                      all a,b(cp b -> a<<N -> d a<d b -> cp a)))")

(ind)

;; Base

(assume "0<<N")
(ex-intro (pt "[a]a=0"))
(ex-intro (pt "[a]0"))
(ex-intro (pt "[a]W 0 a"))
(ng)
(add-global-assumption "Count-Base" "Card([n]n=0)N=1")
(split)
(use "W-N")
(use "0<<N")
(split)
(use "Count-Base")
(split)
(use "Truth")
(split)
(assume "a" "0<<a" "0=a")
(add-global-assumption "<-Ax16" "all n(0<<n -> 0=n -> F)")
(use "<-Ax16" (pt "a"))
(use "0<<a")
(use "0=a")
(split)
(assume "a")
(use "Truth")
(split)
(assume "a")
(use "Truth")
(split)
(assume "a")
(use "Truth")
(split)
(assume "a" "b" "b=0")
(simp "b=0")
(use "Truth")
(assume "a" "b" "b=0")
(simp "b=0")
(ng)
(assume "a<<N" "F")
(use "Efq")
(use "F")

;; Step
(assume "n" "IH1" "Succ n<<N")

;; First we make the IH usable: Let cp,d,nxt have the assumed properties

(ex-elim
 (pf "ex cp,nxt,d(d N=(DummyR nat) & Card cp N=Succ n &
                      d 0=Inl 0 &
                      all a(0<<a -> nxt a=a -> F) &
                      all a cp(nxt a) &
                      all a d(nxt a)<(DummyR nat) &
                      all a d a=d(nxt a)+W(nxt a)a &
                      all a,b(cp b -> d a<=d b+W b a) &
                      all a,b(cp b -> a<<N -> d a<d b -> cp a))"))
(use-with "IH1" DEFAULT-GOAL-NAME)
(add-global-assumption "<<-Ax1" "all m,n(Succ m<<n -> m<<n)")
(use "<<-Ax1")
(use "Succ n<<N")

(assume "cp" "IH2")
(by-assume "IH2" "nxt" "IH3")
(by-assume "IH3" "d" "IH")
(drop "IH1")

;; Lemma: There is a least non-computed node c
(cut "ex c(c<<N & (cp c -> F) & all a(a<<N -> d a<d c -> cp a))")

(assume "ExLeastc")
;; Let such c be given
(by-assume "ExLeastc" "c" "Pick-Prop")

;; The new cp-, nxt- and d-functions
(ex-intro (pt "Newcp cp c"))
(ex-intro (pt "Newnxt nxt d c"))
(ex-intro (pt "Newd d c"))
(split)

;; Newd d c N=(DummyR nat)
(add-global-assumption "Newd-Inf" "all d,c(d N=(DummyR nat) ->
                             c<<N ->
                             Newd d c N=(DummyR nat))")
(use "Newd-Inf")
(use "IH")
(use "Pick-Prop")
(split)

;; Card(Newcp cp c)N=Succ(Succ n)
(add-global-assumption "New15" "all cp,n,c(Succ n<<N ->
                             Card cp N=Succ n ->
                             c<<N ->
                             (cp c -> F) ->
                             Card(Newcp cp c)N=Succ(Succ n))")
(use "New15")
(use "Succ n<<N")
(use "IH")
(use "Pick-Prop")
(use "Pick-Prop")
(split)

;; Newd d c 0=Inl 0
(add-global-assumption "New16" "all d,c(d 0=Inl 0 -> Newd d c 0=Inl 0)")
(use "New16")
(use "IH")
(split)

;; all a(0<<a -> Newnxt nxt d c a=a -> F)
(add-global-assumption "New17" "all cp,nxt,d,c,a(
                         (0<<a -> nxt a=a -> F) ->
                         0<<a -> Newnxt nxt d c a=a -> F)")
(assume "a")
(use "New17" (pt "cp"))
(use "IH")
(split)

;; all a Newcp cp c(Newnxt nxt d c a)
(add-global-assumption "New18"
     "all cp,nxt,d,a,c(cp(nxt a) -> Newcp cp c(Newnxt nxt d c a))")
(assume "a")
(use "New18")
(use "IH")
(split)

;; all a Newd d c(Newnxt nxt d c a)<(DummyR nat)
(add-global-assumption "New19" "all cp,nxt,d,c,a(c<<N ->
                         (cp c -> F) ->
                         all a,b(cp b -> a<<N -> d a<d b -> cp a) ->
                         all a cp(nxt a) ->
                         d(nxt a)<(DummyR nat) ->
                         Newd d c(Newnxt nxt d c a)<(DummyR nat))")
(assume "a")
(use "New19" (pt "cp"))
(use "Pick-Prop")
(use "Pick-Prop")
(use "IH")
(use "IH")
(use "IH")
(split)

;; all a Newd d c a=Newd d c(Newnxt nxt d c a)+W(Newnxt nxt d c a)a
(add-global-assumption "New20"
     "all cp,nxt,d,c,a(
                         c<<N ->
                         (cp c -> F) ->
                         all a(a<<N -> d a<d c -> cp a) ->
                         all a,b(cp b -> a<<N -> d a<d b -> cp a) ->
                         all a cp(nxt a) ->
                         all a d a=d(nxt a)+W(nxt a)a ->
                         Newd d c a=
                         Newd d c(Newnxt nxt d c a)+W(Newnxt nxt d c a)a)")
(assume "a")
(use "New20"(pt "cp"))
(use "Pick-Prop")
(use "Pick-Prop")
(use "Pick-Prop")
(use "IH")
(use "IH")
(use "IH")
(split)

;; all a,b(Newcp cp c b -> Newd d c a<=Newd d c b+W b a)
(add-global-assumption "New21"
     "all cp,nxt,d,c,a,b(
                         c<<N ->
                         (cp c -> F) ->
                         all a(a<<N -> d a<d c -> cp a) ->
                         all a,b(cp b -> a<<N -> d a<d b -> cp a) ->
                         all a cp(nxt a) ->
                         all a d a=d(nxt a)+W(nxt a)a ->
                         all a,b(cp b -> d a<=d b+W b a) ->
                         all a,b(cp b -> a<<N -> d a<d b -> cp a) ->
                         Newcp cp c b -> Newd d c a<=Newd d c b+W b a)")
(assume "a" "b")
(use "New21" (pt "nxt"))
(use "Pick-Prop")
(use "Pick-Prop")
(use "Pick-Prop")
(use "IH")
(use "IH")
(use "IH")
(use "IH")
(use "IH")

;; all a,b(Newcp cp c b -> a<<N -> Newd d c a<Newd d c b -> Newcp cp c a)
(add-global-assumption "New22"
     "all cp,nxt,d,c,a,b(
                         c<<N ->
                         (cp c -> F) ->
                         all a(a<<N -> d a<d c -> cp a) ->
                         all a,b(cp b -> a<<N -> d a<d b -> cp a) ->
                         all a cp(nxt a) ->
                         all a d a=d(nxt a)+W(nxt a)a ->
                         all a,b(cp b -> d a<=d b+W b a) ->
                         all a,b(cp b -> a<<N -> d a<d b -> cp a) ->
                         Newcp cp c b ->
                         a<<N ->
                         Newd d c a<Newd d c b ->
                         Newcp cp c a)")
(assume "a" "b")
(use "New22" (pt "nxt"))
(use "Pick-Prop")
(use "Pick-Prop")
(use "Pick-Prop")
(use "IH")
(use "IH")
(use "IH")
(use "IH")
(use "IH")

;; ex c(c<<N & (cp c -> F) & all a(a<<N -> d a<d c -> cp a))
;; (pp "PickThm")

;; all cp,d(
;;  d N=(DummyR nat) ->
;;  Card cp N<<N ->
;;  Pick cp d<<N &
;;  (cp(Pick cp d) -> F) & all a(a<<N -> d a<d(Pick cp d) -> cp a))

(ex-intro (pt "Pick cp d"))
(split)

(add-global-assumption "Comp<<with=1" "all n1,n2,m(n1=n2 -> n2<<m -> n1<<m)")
(cut "Card cp N<<N")
(assume "Countcp<<N")

(use "PickThm")
(use "IH")
(use "Countcp<<N")
(use "Comp<<with=1" (pt "Succ n"))
(use "IH")
(use "Succ n<<N")
(split)

(use "PickThm")
(use "IH")
(use "Comp<<with=1" (pt "Succ n"))
(use "IH")
(use "Succ n<<N")

;; all a(a<<N -> d a<d(Pick cp d) -> cp a)
(use "PickThm")
(use "IH")
(use "Comp<<with=1" (pt "Succ n"))
(use "IH")
(use "Succ n<<N")
;; Proof finished.

(add-var-name "t" (py "(nat=>boole)@@((nat=>nat)@@(nat=>nat ysumu))"))
(define neterm
  (rename-variables (nt (proof-to-extracted-term (current-proof)))))

;; (pp neterm)

;; [n]
;;  (Rec nat=>(nat=>boole)@@(nat=>nat)@@(nat=>nat ysumu))n
;;  (([n0]n0=0)@([n0]0)@W 0)
;;  ([n0,t]
;;    Newcp left t(Pick left t right right t)@
;;    Newnxt left right t right right t(Pick left t right right t)@
;;    Newd right right t(Pick left t right right t))

;; So the extracted algorithm is very obvious: it iteratively constructs
;; triples (cp,nxt,d), where in the step, with c:=Pick cp d, one forms the
;; new triple (Newcp cp c, Newnxt nxt d c, Newd d c).

;; Clearly, an optimization is possible/necessary here: let c=Pick cp d ...

;; Next, one proves the properties New15 etc.  This - for the first time -
;; involves the definitions of Newnxt, Newd.  In fact, adding their
;; computation rules earlier would have messed up the terms when
;; normalizing goals.

(add-computation-rules
 "Newd d c a" "(d c+W c a)min d a")

;; We begin with Newd-Inf.

(set-goal "all d,c(d N=(DummyR nat) ->
                             c<<N ->
                             Newd d c N=(DummyR nat))")
(assume "d" "c" "d N=(DummyR nat)" "c<<N")
(ng)
(cut "W c N=(DummyR nat)")
(assume "W c N=(DummyR nat)")
(simp "W c N=(DummyR nat)")
(simp "d N=(DummyR nat)")
(ng)
(use "Truth")
(use "W-N")
(use "c<<N")
;; Proof finished.

(add-global-assumption "Newcp-Def" "all cp,c Newcp cp c eqd Adjoin cp c")

;; We show New15: this follows rather immediately from CountIntern
;; in count.scm (i.e. from (11) in [BS99])

(set-goal "all cp,n,c(Succ n<<N ->
                             Card cp N=Succ n ->
                             c<<N ->
                             (cp c -> F) ->
                             Card(Newcp cp c)N=Succ(Succ n))")
(assume "cp" "n" "c" 1 2 3 4)
(cut "Card(Adjoin cp c)N=Succ(Card cp N)")
(simp 2)
(inst-with-to "Newcp-Def" (pt "cp") (pt "c") "Newcp-Def-Inst")
(simp "Newcp-Def-Inst")
(prop)
(drop 2)
(use "CountIntern")
(prop)
(prop)
;; Proof finished.

;; New16 is also immediate from the definition of Newd as minimum.

(set-goal "all d,c(d 0=Inl 0 -> Newd d c 0=Inl 0)")
(assume "d" "c" "d 0=Inl 0")
(ng)
(simp "d 0=Inl 0")
(ng)
(use "Truth")
;; Proof finished.

;; New17: 0<<a -> Newnxt nxt d c a \ne a.  We can assume
;; d c+W c a<d a (otherwise the claim follows from the IH).  Goal: c \ne a.
;; So assume c=a.  Then d a+W a a<d a, which follows from x+y<x -> F.

(add-computation-rules
 "Newnxt nxt d c a" "[if (d c+W c a<d a) c (nxt a)]")

(set-goal "all cp,nxt,d,c,a(
                         (0<<a -> nxt a=a -> F) ->
                         0<<a -> Newnxt nxt d c a=a -> F)")
(assume "cp" "nxt" "d" "c" "a" "IH" "0<<a" "Newnxt nxt d c a=a")
(ng)
(cases (pt "d c+W c a<d a"))

;; Case d c+W c a<d a
(assume "d c+W c a<d a")
(cut "[if (d c+W c a<d a) c (nxt a)]=a")
(simp "d c+W c a<d a")
(ng)
(assume "c=a")
(cut "d c+W c a<d a")
(simp "c=a")
(ng)
(prop)
(use  "d c+W c a<d a")
(use "Newnxt nxt d c a=a")

;; Case d c+W c a<d a -> F
(assume "d c+W c a<d a -> F")
(use "IH")
(use "0<<a")
(cut "[if (d c+W c a<d a) c (nxt a)]=a")
(simp "d c+W c a<d a -> F")
(ng)
(prop)
(use "Newnxt nxt d c a=a")
;; Proof finished.

;; New18:  cp(nxt a) -> Newcp cp c(Newnxt nxt d c a)
;; We can assume c \ne Newnxt nxt d c a.  Then Newnxt nxt d c a = nxt a,
;; hence the claim is immediate.

(set-goal "all cp,nxt,d,a,c(cp(nxt a) -> Newcp cp c(Newnxt nxt d c a))")
(assume "cp" "nxt" "d" "a" "c" "cp(nxt a)")
(inst-with-to "Newcp-Def" (pt "cp") (pt "c") "Newcp-Def-Inst")
(simp "Newcp-Def-Inst")
(ng)
(cases (pt "d c+W c a<d a"))
(assume "d c+W c a<d a")
;; (simp "d c+W c a<d a")
(ng)
(use "Truth")
(assume "d c+W c a<d a -> F")
;; (simp "d c+W c a<d a -> F")
(ng)
(simp "cp(nxt a)")
(ng)
(use "Truth")
;; Proof finished.

;; The auxiliary claim (23)

;; "AuxClaim23"
(set-goal "all cp,c,d,a(c<<N ->
               (cp c -> F) ->
               all a,b(cp b -> a<<N -> d a<d b -> cp a) ->
               cp a ->
               Newd d c a=d a)")
(assume "cp" "c" "d" "a" "c<<N" "not cp c" "IH22" "cp a")
(ng)
(add-global-assumption "Min-right-neg" "all x,y((x<y -> F) -> x min y=y)")
(use "Min-right-neg")
(assume "d c+W c a<d a")
(cut "d c<d a")
(search)
(add-global-assumption "<-Ax5a" "all x1,x2,x3(x1+x2<x3 -> x1<x3)")
(use "<-Ax5a" (pt "W c a"))
(use "d c+W c a<d a")
;; Proof finished.
(save "AuxClaim23")

;; New19: Newd d c(Newnxt nxt d c a)<(DummyR nat)
;; In case d c+W c a<d a we have Newd d c a=d c+W c a<(DummyR nat), hence also
;; Newd d c a(Newnxt nxt d c a)=Newd d c c=d c<(DummyR nat).  Otherwise we have
;; Newnxt nxt d c a=nxt a, hence by AuxClaim23 and cp(nxt a) (IH18) also
;; Newd d c(Newnxt nxt d c a)=d(Newnxt nxt d c a)=d(nxt a)<(DummyR nat),
;; using the IH.

(set-goal "all cp,nxt,d,c,a(c<<N ->
                         (cp c -> F) ->
                         all a,b(cp b -> a<<N -> d a<d b -> cp a) ->
                         all a cp(nxt a) ->
                         d(nxt a)<(DummyR nat) ->
                         Newd d c(Newnxt nxt d c a)<(DummyR nat))")
(assume "cp" "nxt" "d" "c" "a" "c<<N" "not cp c" "IH22"
	"all a cp(nxt a)" "d(nxt a)<(DummyR nat)")
(cases (pt "d c+W c a<d a"))

;; Case d c+W c a<d a
(assume "d c+W c a<d a")
(ng)
(simp "d c+W c a<d a")
(ng)
(add-global-assumption "Trans-<=-<" "all x1,x2,x3(x1<=x2 -> x2<x3 -> x1<x3)")
(use "Trans-<=-<" (pt "d c+W c a"))
(ng)
(use "Truth")
(add-global-assumption "Trans-<-<=" "all x1,x2,x3(x1<x2 -> x2<=x3 -> x1<x3)")
(use "Trans-<-<=" (pt "d a"))
(use "d c+W c a<d a")
(ng)
(use "Truth")

;; Case "d c+W c a<d a -> F"
(assume "d c+W c a<d a -> F")
(cut "Newnxt nxt d c a=nxt a")
(assume "Newnxt nxt d c a=nxt a")
(simp "Newnxt nxt d c a=nxt a")
(cut "Newd d c(nxt a)=d(nxt a)")
(assume "Newd d c(nxt a)=d(nxt a)")
(simp "Newd d c(nxt a)=d(nxt a)")
(use "d(nxt a)<(DummyR nat)")
(use "AuxClaim23" (pt "cp"))
(use "c<<N")
(use "not cp c")
(use "IH22")
(use "all a cp(nxt a)")
(ng)
(simp "d c+W c a<d a -> F")
(ng)
(use "Truth")
;; Proof finished.

;; Now New20

(set-goal "all cp,nxt,d,c,a(
                         c<<N ->
                         (cp c -> F) ->
                         all a(a<<N -> d a<d c -> cp a) ->
                         all a,b(cp b -> a<<N -> d a<d b -> cp a) ->
                         all a cp(nxt a) ->
                         all a d a=d(nxt a)+W(nxt a)a ->
                         Newd d c a=
                         Newd d c(Newnxt nxt d c a)+W(Newnxt nxt d c a)a)")
(strip)
(cases (pt "d c+W c a<d a"))

;; Case d c+W c a<d a
(ng)
(assume "d c+W c a<d a")
(simp "d c+W c a<d a")
(ng)
(add-global-assumption "Min-left-<" "all x,y(x<y -> x min y=x)")
(use "Min-left-<")
(use  "d c+W c a<d a")

;; Case(pt "d c+W c a<d a -> F")
(assume "d c+W c a<d a -> F")
(cut "Newd d c a=d a")
(assume "Newd d c a=d a")
(simp "Newd d c a=d a")
(cut "Newnxt nxt d c a=nxt a")
(assume "Newnxt nxt d c a=nxt a")
(simp "Newnxt nxt d c a=nxt a")
(cut "Newd d c(nxt a)=d(nxt a)")
(assume "Newd d c(nxt a)=d(nxt a)")
(simp "Newd d c(nxt a)=d(nxt a)")
(use 6)
(use "AuxClaim23" (pt "cp"))
(use 1)
(use 2)
(use 4)
(use 5)
(ng)
(simp "d c+W c a<d a -> F")
(ng)
(use "Truth")
(ng)
(use "Min-right-neg")
(use "d c+W c a<d a -> F")
;; Proof finished.

;; ;; A simple auxiliary lemma on Newd

;; (set-goal (pf "all d,c,a Newd d c a<=d a"))
;; (strip)
;; (ng)
;; (cases (pt "d c+W c a<d a"))
;; (assume 1)
;; (simp 1)
;; (ng)
;; (add-global-assumption "<-Ax14" (pf "all x1,x2(x1<x2 -> x1<=x2)"))
;; (use "<-Ax14")
;; (prop)

;; ;; Case (d c+W c a<d a -> F)
;; (assume 1)
;; (simp 1)
;; (ng)
;; (use "Truth")

;; (save "Newd-Min1")
;; Use d c+W c a min d a<=d a instead

;; New21:

(set-goal "all cp,nxt,d,c,a,b(
                         c<<N ->
                         (cp c -> F) ->
                         all a(a<<N -> d a<d c -> cp a) ->
                         all a,b(cp b -> a<<N -> d a<d b -> cp a) ->
                         all a cp(nxt a) ->
                         all a d a=d(nxt a)+W(nxt a)a ->
                         all a,b(cp b -> d a<=d b+W b a) ->
                         all a,b(cp b -> a<<N -> d a<d b -> cp a) ->
                         Newcp cp c b -> Newd d c a<=Newd d c b+W b a)")
(assume "cp" "nxt" "d" "c" "a" "b" 1 2 3 4 5 6 7 8) ;"Newcp cp c b")
(inst-with-to "Newcp-Def" (pt "cp") (pt "c") "Newcp-Def-Inst")
(simp "Newcp-Def-Inst")
(cases (pt "b=c"))

;; Case b=c
(assume "b=c")
(ng)
(simp "b=c") ;here the boolean term b=c is replaced by True
(simp "b=c") ;now b is replaced by c
(ng)
(assume "T")
(use "Truth")

;; Case b=c -> F
(assume "b=c -> F" "Adjoin cp c b")
(cut "cp b")
(assume "cp b")
(cut "Newd d c b=d b")
(assume "Newd d c b=d b")
(simp "Newd d c b=d b")
(use "Trans-<=" (pt "d a"))
(ng)
(use "Truth")
(use 7)
(use "cp b")
(use "AuxClaim23" (pt "cp"))
(use 1)
(use 2)
(use 8)
(use "cp b")
(cut "Adjoin cp c b")
(ng)
(simp "b=c -> F")
(ng)
(prop)
(use "Adjoin cp c b")
;; Proof finished.

;; For New22 first some useful or-Lemmata

;; "NewcpElim"
(set-goal "all cp,c,b(Newcp cp c b -> (b=c -> Pvar) ->
                                          (cp b -> Pvar) -> Pvar)")
(assume "cp" "c" "b")
(cases (pt "b=c"))
(prop)
(inst-with-to "Newcp-Def" (pt "cp") (pt "c") "Newcp-Def-Inst")
(simp "Newcp-Def-Inst")
(ng)
(assume "b=c -> F")
(simp "b=c -> F")
(prop)
;; Proof finished.
(save "NewcpElim")

(add-global-assumption "MinOrLt"
  "all x,y,z(x min y<z -> (x<z -> Pvar) -> (y<z -> Pvar) -> Pvar)")

;; The following is not necessary any more, by def of Newd
;; (set-goal (pf "all d,c,a,x(Newd d c a<x -> (d c+W c a<x -> Pvar) ->
;;                                            (d a<x -> Pvar) -> Pvar)"))
;; (assume "d" "c" "a" "x")
;; (cases (pt "d c+W c a<d a"))
;; (ng)
;; (assume 1)
;; (simp 1)
;; (ng)
;; (prop)

;; ;; Case d c+W c a<d a -> F
;; (ng)
;; (assume 1)
;; (simp 1)
;; (ng)
;; (prop)

;; (save "Newd-Elim-<")

;; Now New22

(set-goal "all cp,nxt,d,c,a,b(
                         c<<N ->
                         (cp c -> F) ->
                         all a(a<<N -> d a<d c -> cp a) ->
                         all a,b(cp b -> a<<N -> d a<d b -> cp a) ->
                         all a cp(nxt a) ->
                         all a d a=d(nxt a)+W(nxt a)a ->
                         all a,b(cp b -> d a<=d b+W b a) ->
                         all a,b(cp b -> a<<N -> d a<d b -> cp a) ->
                         Newcp cp c b ->
                         a<<N ->
                         Newd d c a<Newd d c b ->
                         Newcp cp c a)")
(assume "cp" "nxt" "d" "c" "a" "b" 1 2 3 4 5 6 7 8 9 10)
(use "NewcpElim" (pt "cp") (pt "c") (pt "b"))
(prop)
(assume "b=c")
(simp "b=c")
;; We now need that Newd d c a rewrites to d c+W c a min d a
(ng)
(assume 12)
(use "MinOrLt" (pt "d c+W c a") (pt "d a") (pt "d c"))
(prop)
(prop)
(assume "d a<d c")
(cut "cp a")
(inst-with-to "Newcp-Def" (pt "cp") (pt "c") "Newcp-Def-Inst")
(simp "Newcp-Def-Inst")
(ng)
(add-global-assumption
 "or-intro-2" "all boole1, boole2(boole2 -> [if boole1 True boole2])")
(use "or-intro-2")
(use 3)
(prop)
(prop)

;; Case cp b
(assume "cp b")
(cut "Newd d c b=d b")
(assume "Newd d c b=d b")
(simp "Newd d c b=d b")
(ng)
(assume 12)
(use "MinOrLt" (pt "d c+W c a") (pt "d a") (pt "d b"))
(prop)
(assume "d c+W c a<d b")
(cut "d c<d b")
(assume "d c<d b")
(cut "F")
(prop)
(use 2)
(use 8 (pt "b"))
(use "cp b")
(use 1)
(use "d c<d b")
;; (add-global-assumption "<-Ax5a" (pf "all x1,x2,x3(x1+x2<x3 -> x1<x3)"))
(use "<-Ax5a" (pt "W c a"))
(use "d c+W c a<d b")

;; Now for d a<d b -> [if (a=c) True (cp a)]
(inst-with-to "Newcp-Def" (pt "cp") (pt "c") "Newcp-Def-Inst")
(simp "Newcp-Def-Inst")
(ng)
(assume "d a<d b")
(cut "cp a")
(use "or-intro-2")
(use 8 (pt "b"))
(use "cp b")
(use 10)
(use "d a<d b")
(use "AuxClaim23" (pt "cp"))
(use 1)
(use 2)
(use 8)
(use "cp b")
;; Proof finished.

;; 3.  Proof of (1) - (5) for Comp, Next, Dis
;; ============================================

;; From the proof of the Main Theorem we had the eterm

;; (pp neterm)

;; [n0]
;;  (Rec nat=>(nat=>boole)@@(nat=>nat)@@(nat=>nat ysumu))n0
;;  (([n2]n2=0)@([n2]0)@W 0)
;;  ([n2,t3]
;;    Newcp left t3(Pick left t3 right right t3)@
;;    Newnxt left right t3 right right t3(Pick left t3 right right t3)@
;;    Newd right right t3(Pick left t3 right right t3))

;; Generally we could (and probably should) automatize the generation of
;; a correctness proof concerning the extracted term.  Here we just use
;; this proposition as a global assumption.

(add-program-constant
 "Newt"
 (py "(nat=>boole)@@((nat=>nat)@@(nat=>nat ysumu))=>nat=>
      (nat=>boole)@@((nat=>nat)@@(nat=>nat ysumu))"))

(add-global-assumption "NewtDef"
		       (make-eqd (pt "Newt")
				 (pt "[t,c]Newcp left t c@
                        Newnxt left right t right right t c@
                        Newd right right t c")))

(add-var-name "tt" (py "(nat=>boole)@@((nat=>nat)@@(nat=>nat ysumu))=>
                        (nat=>boole)@@((nat=>nat)@@(nat=>nat ysumu))"))

(add-program-constant
 "ItTriple"
 (py "((nat=>boole)@@((nat=>nat)@@(nat=>nat ysumu))=>
       (nat=>boole)@@((nat=>nat)@@(nat=>nat ysumu)))=>
      (nat=>boole)@@((nat=>nat)@@(nat=>nat ysumu))=>
      nat=>
      (nat=>boole)@@((nat=>nat)@@(nat=>nat ysumu))"))

(add-computation-rules
 "ItTriple tt t 0" "t"
 "ItTriple tt t(Succ n)" "tt(ItTriple tt t n)")

(add-program-constant "Comp" (py "nat=>nat=>boole") 1)
(add-program-constant "Next" (py "nat=>nat=>nat") 1)
(add-program-constant "Dist" (py "nat=>nat=>nat ysumu") 1)

(add-global-assumption
 "CompDef"
 (make-eqd (pt "Comp")
	   (pt "[n](left (ItTriple([t]Newt t(Pick left t right right t))
                                     (([n]n=0)@([n]0)@W 0)
                                     n))")))

(add-global-assumption
 "NextDef"
 (make-eqd
  (pt "Next")
  (pt "[n](left right (ItTriple([t]Newt t(Pick left t right right t))
                                   (([n]n=0)@([n]0)@W 0)
                                   n))")))

(add-global-assumption
 "DistDef"
 (make-eqd
  (pt "Dist")
  (pt "[n](right right (ItTriple([t]Newt t(Pick left t right right t))
                                    (([n]n=0)@([n]0)@W 0)
                                    n))")))

;; So by the main lemma just proved we have

(add-global-assumption "MainLemmaCorrect"
     "all n(n<<N ->
       Card(Comp n)N=Succ n &
       Dist n 0=Inl 0 &
       all a(0<<a -> Next n a=a -> F) &
       all a Comp n(Next n a) &
       all a Dist n(Next n a)<(DummyR nat) &
       all a Dist n a=Dist n(Next n a)+W(Next n a)a &
       all a,b(Comp n b -> Dist n a<=Dist n b+W b a) &
       all a,b(Comp n b -> a<<N -> Dist n a<Dist n b -> Comp n a))")

;; The extracted term of the final-aux proof was
;; "[nxt,d,a]d a@
;;           ([i]It nxt a(Least([j]d(It nxt a j))-i))@
;;           Least([i]d(It nxt a i))"
;; of type
;; "(nat=>nat)=>(nat=>nat ysumu)=>nat=>(nat ysumu)@@((nat=>nat)@@nat)"

;; Generally we could (and probably should) automatize the generation of
;; a correctness proof concerning the extracted term.  Here we just use
;; this proposition as a global assumption.

(define final-aux-eterm
  (pt "[nxt,d,a]d a@
                ([i]It nxt a(Least([j]d(It nxt a j))-i))@
                Least([i]d(It nxt a i))"))

(add-var-name "sgn" (term-to-type final-aux-eterm))

(define final-aux-formula
  (pf "all nxt,d(d 0=Inl 0 ->
        all a(0<<a -> nxt a=a -> F) ->
        all a d(nxt a)<(DummyR nat) ->
        all a d a=d(nxt a)+W(nxt a)a ->
        all a,b(b<<N -> d a<=d b+W b a) ->
        all a(a<<N ->
         left right(sgn nxt d a)0=0 &
         left right(sgn nxt d a)right right(sgn nxt d a)=a &
         S left right(sgn nxt d a)right right(sgn nxt d a)=
          left(sgn nxt d a) &
         all f,m(all i f i<<N ->
                  f 0=0 -> f m=a -> left(sgn nxt d a)<=S f m)))"))

;; (remove-global-assumption "Final-Aux-Correct")
(add-global-assumption
 "FinalAuxCorrect"
 (formula-subst final-aux-formula (pv "sgn") final-aux-eterm))

;; (map var-to-string (formula-to-free final-aux-formula))
;; (pp final-aux-formula)
;; (pp (nf (aconst-to-formula (global-assumption-name-to-aconst "FinalAuxCorrect"))))

;; all nxt,d(
;;  d 0=Inl 0 ->
;;  all a(0<<a -> nxt a=a -> F) ->
;;  all a d(nxt a)<(DummyR nat) ->
;;  all a d a=d(nxt a)+W(nxt a)a ->
;;  all a,b(b<<N -> d a<=d b+W b a) ->
;;  all a(
;;    a<<N ->
;;    It nxt a(Least([n0]d(It nxt a n0)))=0 & T &
;;    S([n0]It nxt a(Least([n1]d(It nxt a n1))-n0))(Least([n0]d(It nxt a n0)))=
;;    d a &
;;    all f,m(all i f i<<N -> f 0=0 -> f m=a -> d a<=S f m)))

;; Here we must substitute
;; nxt -> Next(Pred N)
;; d   -> Dist(Pred N)
;; and for the five premises, our proofs of (1)-(5).
;; This gives us FinalAuxCorrectInst:

;; "FinalAuxCorrectInst"
(set-goal
 "all a(a<<N ->
   It(Next(Pred N))a(Least([n0](Dist(Pred N))(It(Next(Pred N))a n0)))=0 &
   T &
   S([n0]It(Next(Pred N))a(Least([n1](Dist(Pred N))(It(Next(Pred N))a n1))-n0))
    (Least([n0](Dist(Pred N))(It(Next(Pred N))a n0)))=(Dist(Pred N))a &
   all f,m(all i f i<<N -> f 0=0 -> f m=a -> (Dist(Pred N))a<=S f m))")
(use "FinalAuxCorrect")

(use "MainLemmaCorrect")
(add-global-assumption "<<-Ax15" "all n(0<<n -> Pred n<<n)")
(use "<<-Ax15")
(add-global-assumption "GraphNotEmpty" "0<<N")
(use "GraphNotEmpty")

(use "MainLemmaCorrect")
(use "<<-Ax15")
(use "GraphNotEmpty")

(use "MainLemmaCorrect")
(use "<<-Ax15")
(use "GraphNotEmpty")

(use "MainLemmaCorrect")
(use "<<-Ax15")
(use "GraphNotEmpty")

(assume "a1" "b" "b<<N")
(use "MainLemmaCorrect")
(use "<<-Ax15")
(use "GraphNotEmpty")
(use "CardMaxImpAll" (pt "N"))
(add-global-assumption "Trans-=" "all n1,n2,n3(n1=n2 -> n2=n3 -> n1=n3)")
(use "Trans-=" (pt "Succ(Pred N)"))
(use "MainLemmaCorrect")
(use "<<-Ax15")
(use "GraphNotEmpty")
(add-global-assumption "<<-Ax16" "all n(0<<n -> Succ(Pred n)=n)")
(use "<<-Ax16")
(use "GraphNotEmpty")
(use "b<<N")
;; Proof finished.
(save "FinalAuxCorrectInst")

;; We now prove the final theorem

;; "FinalTheorem"
(set-goal
 "all a(a<<N -> ex s(ex g,n(g 0=0 & g n=a & S g n=s) &
                         all f,m(all i f i<<N ->
                                  f 0=0 -> f m=a -> s<=S f m)))")
(assume "a" "a<<N")
(ex-intro (pt "Dist(Pred N)a"))
(split)

(ex-intro (pt "[n0]It(Next(Pred N))a
                   (Least([n1]Dist(Pred N)(It (Next(Pred N))a n1))-n0)"))
(ex-intro (pt "Least([i]Dist(Pred N)(It (Next(Pred N))a i))"))
(ng)
(split)
(use "FinalAuxCorrectInst")
(use "a<<N")
(split)
(use "Truth")

(use "FinalAuxCorrectInst")
(use "a<<N")

(use "FinalAuxCorrectInst")
(use "a<<N")
;; Proof finished.
(save "FinalTheorem")

(define eterm (proof-to-extracted-term
	       (theorem-name-to-proof "FinalTheorem")))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [n]
;;  Dist(Pred N)n@
;;  ([n0]It(Next(Pred N))n(Least([n1]Dist(Pred N)(It(Next(Pred N))n n1))-n0))@
;;  Least([n0]Dist(Pred N)(It(Next(Pred N))n n0))

