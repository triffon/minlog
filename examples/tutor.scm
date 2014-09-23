;; $Id: tutor.scm 2451 2011-03-29 21:32:09Z schwicht $

;; This file contains the examples of the Tutorial for Minlog version 5.0

;; (load "~/git/minlog/init.scm")

(set! COQ-GOAL-DISPLAY #f)

(add-pvar-name "A" "B" "C" (make-arity))

(set-goal "(A -> B -> C) -> (A -> B) -> A -> C")

(assume 1)
(assume 2)
(assume 3)
;; alternatively: (assume 1 2 3)
(use 1)
(use 3)
(use 2)
(use 3)
;; alternatively: (use-with 2 3)

(display-proof)
(proof-to-expr)
(proof-to-expr-with-formulas)


;; Conjunction

;; (add-predvar-name "A" "B" (make-arity))
(set-goal "A & B -> B & A")
(assume 1)
(split)
(use 1)
(use 1)

;; Examples to try on your own:
(set-goal "A -> B -> A")
(set-goal "(A -> B -> C) -> B -> A -> C")
(set-goal "(A -> B) -> (B -> C) -> A -> C")
(set-goal "(A -> B -> C) -> A & B -> C")

;; Peirce law

(display-global-assumptions)
(display-global-assumptions "EfqLog")
(display-global-assumptions "StabLog")

;; (add-pvar-name "A" "B" (make-arity))

(set-goal "((A -> B) -> A) -> A")
(assume 1)
(use "StabLog")
(assume 2)
(use 2)
(use 1)
(assume 3)
(use "EfqLog")
(use 2)
(use 3)

;; PREDICATE CALCULUS
;; A first example with quantifiers:

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(set! COMMENT-FLAG #t)

;; n, m, k are variables of type nat

(add-pvar-name "P" "Q" (make-arity (py "nat")))

(set-goal "all n(P n -> Q n) -> all n P n -> all n Q n")
(assume 1 2)
(assume "n")
;; alternatively (assume 1 2 "n")
(use 1)
(use 2)


(set-goal "all n (P n -> Q n) -> ex n P n -> ex n Q n")
(assume 1 2)
(by-assume 2 "n0" "P_n0")

;; alternatively
;; (undo) ;undo the last command
;; (ex-elim 2)
;; (assume "n0" "P_n0")
;; (drop 2)

(ex-intro (pt "n0"))
(use-with 1 (pt "n0") "P_n0")

(add-pvar-name "R" (make-arity (py "nat") (py "nat")))

(define Sym (pf "all n,m(R n m  -> R m n)"))
(define Trans (pf "all n,m,k(R n m -> R m k -> R n k)"))

(set-goal (mk-imp Sym Trans (pf "all n,m(R n m -> R n n)")))

(assume "Sym" "Trans" "n" "m" 3)
(use "Trans" (pt "m"))
(use 3)
(use "Sym")
(use 3)

;; More elaborate - same example - original goal.

;; (libload "nat.scm")
;; (add-predconst-name "R" (make-arity (py "nat") (py "nat")))

(set-goal "all n,m(R n m  -> R m n)
	   & all n,m,k(R n m & R m k -> R n k)
	   -> all n(ex m R n m -> R n n)")
(assume 1)
(inst-with 1 'left)
(inst-with 1 'right)
(drop 1)
(name-hyp 2 "Sym")
(name-hyp 3 "Trans")
(assume "n" 4)
(ex-elim 4)
(assume "m" 5)
(cut "R m n")
(assume 6)
(use-with "Trans" (pt "n") (pt "m") (pt "n") "?")
(drop "Sym" "Trans" 4)
(split)
(use 5)
(use 6)
(use-with "Sym" (pt "n") (pt "m") 5)

;; Examples to prove on your own.

(set-goal "all m, n R m n -> all n, m R m n")
(set-goal "all m, n R m n -> all n R n n")
(set-goal "ex m all n R m n  -> all n ex n R m n")

;; An example which involves a function f.
(av "f" (py "nat=>nat"))
(set-goal "all f(all n(P(f n) -> Q n) -> all n P n -> all n Q n)")
(set-goal "all f(all n(P n -> Q (f n)) -> ex n P n -> ex n Q n)")

;; (add-pvar-name "Q" (make-arity (py "nat")))
;; (add-pvar-name "A" (make-arity))

(set-goal "all n(Q n -> A) -> (ex n Q n -> A)")
(set-goal "ex n(Q n -> A) -> all n Q n -> A")

;; We prove the inverse of the last exercise (in classical logic)
;; whereby we generalise the statement to an arbitrary type.

(remove-pvar-name "Q" "P")
(add-pvar-name "Q" "P" (make-arity (py "alpha")))
(av "x" "y" (py "alpha"))

(set-goal "(all x Q x -> A) -> excl x(Q x -> A)")
(assume 1 2)
(use 2 (pt "(Inhab alpha)"))
(assume 3)
(use 1)
(assume "x")

(use "StabLog")
(assume 4)
(use 2 (pt "x"))
(assume 5)
(use 1)
(assume "y")
(use "EfqLog")
(use-with 4 5)
(save "Lemma")

;; Using this Lemma we will prove the drinker formula by substituting
;; A by all x Q (and Q by Q)

(set-goal "excl x(Q x -> all x Q x)")
(use-with "Lemma"
	  (make-cterm (pv "x") (pf "Q x"))
	  (make-cterm (pf "all x Q x"))
	  "?")
(assume 1)
(use 1)

;; Equality reasoning

;; (av "f" (py "nat=>nat"))

(set-goal "all f,n(f n=n -> f(f n)=n)")
(assume "f" "n" 1)
(simp 1)
(use 1)

;; In case we want the replace the rhs by the lhs of the equation:

(set-goal "all f,n(n=f n ->  n=f(f n))")
(assume "f" "n" 1)
(simp "<-" 1)
(use 1)

(remove-var-name "f")

;; Automatic proof search.

(set-goal "(A -> B -> C) -> (A -> B) -> A -> C")
(prop)

(set-goal "((A -> B) -> A) -> A")
(prop)

(set-goal "all x(P x -> Q x) -> all x P x -> all x Q x")
(search)

;; A more complex example with search.

;; (add-var-name "x" "y" (py "alpha"))
(add-tvar-name "beta")
(add-var-name "u" "v" "w" (py "beta"))
(add-program-constant "In" (py "alpha=>beta=>boole"))
(add-infix-display-string "In" "in" 'rel-op)
(add-var-name "f" (py "alpha=>alpha"))

(set-goal "all f(
 all x,v(f x in v -> excl u(x in u & all y(y in u -> f y in v))) ->
 all x,w(f(f x)in w -> excl u(x in u & all y(y in u -> f(f y)in w))))")
(search)

(remove-var-name "x" "y" "f" "u" "v" "w")

;; Datatypes and inductively defined predicates

;; (set! COMMENT-FLAG #f)
;; (libload "nat.scm")
;; (set! COMMENT-FLAG #t)

(set! COQ-GOAL-DISPLAY #t)

(display-alg "nat")
(display-pconst "NatPlus")

;; Normalizing, apply term rewriting rules.
(pp (nt (pt "3+4")))
(pp (nt (pt "Succ n+Succ m+0")))

;; Defining program constants.

(add-program-constant "Double" (py "nat=>nat"))
(add-computation-rule (pt "Double 0") (pt "0"))
(add-computation-rule (pt "Double(Succ n)")
                      (pt "Succ(Succ(Double n))"))

;; Alternatively:
;; (add-computation-rules
;;  "Double 0" "0"
;;  "Double(Succ n)" "Succ(Succ(Double n))")

;; Normalizing, apply term rewriting rules.
(pp (nt (pt "Double 3")))
(pp (nt (pt "Double (n+2)")))

;; Proof by induction, apply term-rewriting-rules.

(set-goal "all n Double n=n+n")
(ind)

;; base
(ng)
(use "Truth")

;; step
(assume "n" "IH")
(ng) ;term rewriting rules for Double and + are applied.
(use "IH")

(add-program-constant "DoubleN" (py "nat=>nat"))
(add-computation-rule (pt "DoubleN n") (pt "n+n"))

;; Exercise: The reader is encouraged to prove that the two definitions
;; for doubling a number are equivalent.

(set-goal "all n Double n=DoubleN n")

(add-rewrite-rule (pt "Double n") (pt "DoubleN n"))

;; Another exercise:

(set-goal "all n,m n+m=m+n")

;; Another example

;; (libload "nat.scm")

;; Simultaneous definition of Even/Odd.  The datatype boole is
;; predefined.

(add-program-constant "Odd" (py "nat=>boole"))
(add-program-constant "Even" (py "nat=>boole"))

(add-computation-rules
 "Odd 0" "False"
 "Even 0" "True"
 "Odd(Succ n)" "Even n"
 "Even(Succ n)" "Odd n")

(set-goal "all n Even(Double n)")
(ind)
(prop)
(search)

;; Case distinction on the booleans

(av "p" (py "boole"))
(set-goal "all p((p=False -> F) -> p=True)")
(cases)
(prop)
(prop)

;; Lists over \alpha

;; (libload "nat.scm")
(set! COMMENT-FLAG #f)
(libload "list.scm")
(set! COMMENT-FLAG #t)

(add-var-name "x" "a" "b" "c" "d" (py "alpha"))
(add-var-name "xs" "ys" "v" "w" "u" (py "list alpha"))

(add-program-constant "ListRv" (py "list alpha=>list alpha") t-deg-one)
(add-prefix-display-string "ListRv" "Rv")
(add-computation-rules
 "Rv(Nil alpha)" "(Nil alpha)"
 "Rv(x::xs)" "Rv xs++x:")
;; (add-computation-rule (pt "Rv(Nil alpha)") (pt "(Nil alpha)"))
;; (add-computation-rule (pt "Rv(x::xs)") (pt "Rv xs++x:"))

(display-pconst "ListAppd")

;; ListAppd
;;   comprules
;; 	(Nil alpha)++xs2	xs2
;; 	(x1::xs1)++xs2	x1::xs1++xs2
;;   rewrules
;; 	xs++(Nil alpha)	xs
;; 	xs1++x2: ++xs2	xs1++(x2::xs2)

(set-goal "all v,w Rv(v++w)eqd Rv w++Rv v")
(ind)
;; Base
(ng)
(assume "w")
(use "InitEqD")
;; Step
(assume "a" "v" "IHw" "w")
(ng)
(simp "IHw")
(simp "ListAppdAssoc")
(use "InitEqD")
;; Proof finished.

;; Exercises:
(av "f" (py "alpha=>alpha"))

(set-goal "all f,ys,xs (f map (xs++ys) eqd(f map xs)++(f map ys))")
(set-goal "all f,xs (f map (Rv xs) eqd Rv (f map xs))")
(assume "f")
(ind)
(ng)
(use "InitEqD")
(assume "x" "xs" "IHxs")
(ng #t)
(simp "MapAppd")
(simp "IHxs")
(use "InitEqD")

(remove-var-name "f")

;; Defining algebras: Binary trees.

(add-algs "bintree"
	  '("bintree" "Null")
	  '("bintree=>nat=>bintree=>bintree" "Con"))

(av "ltree" "rtree" (py "bintree"))

;; Could also be an exercise:
(apc "Flatten" (py "bintree=>list nat"))
(add-computation-rules
 "Flatten(Null)" "(Nil nat)"
 "Flatten(Con ltree n rtree)" "n: ++Flatten ltree++Flatten rtree")
;; (add-computation-rule (pt "Flatten(Null)")
;;                       (pt "(Nil nat)"))
;; (add-computation-rule (pt "Flatten(Con ltree n rtree)")
;;                       (pt "n: ++Flatten ltree++Flatten rtree"))

(pp (nt (pt "Flatten(Con(Con Null 4 Null)
                        1
                        (Con Null 5(Con Null 7 Null)))")))

;; Inductively defined predicates

(add-ids (list (list "EvenI" (make-arity (py "nat")) "algEvenI"))
	 '("EvenI 0" "InitEvenI")
	 '("allnc n(EvenI n -> EvenI(n+2))" "GenEvenI"))

;; Proof using the closure axioms for Even: (intro command)
(set-goal "all n EvenI(n+n)")
(ind)
(ng)
;; Apply first closure axiom of EvenI
(intro 0)
(assume "n" "IH")
(ng)
(intro 1)
(use "IH")

;; Proof using induction on the predicate Even:

(set-goal "all n(EvenI n -> ex m m+m=n)")
(assume "n" "En"))
(elim "En")

(ex-intro (pt "0"))
(use "Truth")

(assume "n1" "En1" "IH")
(by-assume "IH" "m0" "m0Prop")
(ex-intro (pt "m0+1"))
(simp "<-" "m0Prop")
(use "Truth")

;; Totality of program constants

(display-idpc "TotalNat")

;; TotalNat
;; 	TotalNatZero:	TotalNat 0
;; 	TotalNatSucc:	allnc nat^(TotalNat nat^ -> TotalNat(Succ nat^))

;; DoubleTotal
(set-goal (rename-variables (term-to-totality-formula (pt "Double"))))
(assume "nat^" "Tnat")
(elim "Tnat")
(use "TotalNatZero")
(assume "nat^1" "Tnat1" "IH")
(ng #t)
(use "TotalNatSucc")
(use "TotalNatSucc")
(use "IH")
;; Proof finished.
(save "DoubleTotal")

;; Program extraction from proofs

;; (add-var-name "x" "a" "b" "c" "d" (py "alpha"))
;; (add-var-name "xs" "v" "w" "u" (py "list alpha"))

(add-ids (list (list "RevI"
                     (make-arity (py "list alpha") (py "list alpha"))))
         '("RevI(Nil alpha)(Nil alpha)" "InitRevI")
         '("all a,v,w(RevI v w  -> RevI(v++a:)(a::w))" "GenRevI"))

;; RevIConsAppd
(set-goal "all a,v,w(RevI v w  -> RevI(a::v)(w++a:))")
(assume "a" "v" "w" "Rvw")
(elim "Rvw")
(ng)
;; RevI(a:)(a:)
(use-with "GenRevI" (pt "a") (pt "(Nil alpha)") (pt "(Nil alpha)") "InitRevI")
(assume "a1" "v1" "w1" "Rv1w1" "Hyp")
(assert "(a::v1++a1:)eqd(a::v1)++a1:")
 (ng #t)
 (use "InitEqD")
(assume "Assertion1")
(simp "Assertion1")
(assert "(a1::w1)++a:eqd(a1::w1++a:)")
 (ng #t)
 (use "InitEqD")
(assume "Assertion2")
(simp "Assertion2")
(use "GenRevI")
(use "Hyp")
;; Proof finished.
(save "RevIConsAppd")

;; (display-pconst "ListAppd")

;; Better: instead of the assertions simplify with ListAppdCompOne
;; (Called ListAppdDef in higwqo.scm; rename there)
;; (set-goal "all x^1,xs^1,xs^2 (x^1::xs^1)++xs^2 eqd(x^1::xs^1++xs^2)")
;; (assume "x^1" "xs^1" "xs^2")
;; (ng)
;; (use "InitEqD")
;; ;; Proof finished.
;; (save "ListAppdDef")

;; RevISym
(set-goal "all v,w(RevI v w -> RevI w v)")
(assume "v" "w" "Rvw")
(elim "Rvw")
(use "InitRevI")
(assume "a" "v1" "w1" "Rv1w1" "Rw1v1")
(use "RevIConsAppd")
(use "Rw1v1")
;; Proof finished.
(save "RevISym")

(set-goal "all v ex w RevI v w")
(ind)
(ex-intro (pt "(Nil alpha)"))
(intro 0)
;; Step
(assume "a" "v" "IH")
(by-assume "IH" "w" "wProp")
(ex-intro (pt "w++a:"))
(use "RevISym")
(intro 1)
(use "RevISym")
(use "wProp")
;; Proof finished.

(define constr-proof (current-proof))

(define eterm (proof-to-extracted-term constr-proof))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [xs](Rec list alpha=>list alpha)xs(Nil alpha)([x,xs0,xs1]xs1++x:)

(term-to-scheme-expr neterm)

(pp (nt (make-term-in-app-form
	 neterm (pt "a::b::c::d:"))))

;; Recall
;; (add-ids (list (list "EvenI" (make-arity (py "nat")) "algEvenI"))
;;          '("EvenII 0" "InitEvenI")
;;          '("allnc n(EvenI n -> EvenI(n+2))" "GenEvenI"))

(set-goal "allnc n(EvenI n -> ex m m+m=n)")
(assume "n")
(elim)
(ex-intro (pt "0"))
(use "Truth")
(assume "n1" 2 3)
(by-assume 3 "m0" 4)
(ex-intro (pt "m0+1"))
(simp "<-" 4)
(use "Truth")

(define eterm (proof-to-extracted-term (current-proof)))
(define neterm (rename-variables (nt eterm)))

(pp neterm)

;; Exercise: compare the above extracted program with a program from
;; a proof where Even/Odd are program constants with computation rules.

;; Inductive Definition of Even, without computational content

(add-ids (list (list "EvenNC" (make-arity (py "nat"))))
	 '("EvenNC 0" "InitEvenNC")
	 '("allnc n(EvenNC n -> EvenNC(n+2))" "GenEvenNC"))

;; Exercise: Prove the following statement
(set-goal "allnc n(EvenNC n -> exu m m+m=n)")
(assume "n" "En")
(elim "En")
(intro 0 (pt "0"))
(use "Truth")
(assume "n1" "En1" "IH")
(by-assume "IH" "m0" "m0Prop")
(intro 0 (pt "m0+1"))
(simp "<-" "m0Prop")
(use "Truth")

;; Parsing example

(remove-pvar-name "B" "R" "P")
(remove-var-name "x" "a")

(add-algs "bin"
	  '("bin" "O")
	  '("bin=>bin=>bin" "BinBranch"))

(add-infix-display-string "BinBranch" "B" 'pair-op) ;right associative

;; (set! COMMENT-FLAG #f)
;; (libload "nat.scm")
;; (libload "list.scm")
;; (set! COMMENT-FLAG #t)

(add-algs "par" '("L" "par") '("R" "par"))
(add-totality "par")

;; (add-var-name "p" (py "boole"))
(add-var-name "x" "y" "z" (py "list par"))

;; Inductively define a predicate (grammar) U over list par, by clauses

(add-ids (list (list "U" (make-arity (py "list par")) "bin"))
	 '("U(Nil par)" "InitU")
	 '("allnc x,y(U x -> U y -> U(x++L: ++y++R:))" "GenU"))

;; LP

(add-program-constant "LP" (py "nat=>list par=>boole"))

(add-computation-rules
 "LP 0(Nil par)"       "True"
 "LP(Succ n)(Nil par)" "False"
 "LP n(L::x)"          "LP(Succ n)x"
 "LP 0(R::x)"          "False"
 "LP(Succ n)(R::x)"    "LP n x")

;; LPTotal
(set-goal (rename-variables (term-to-totality-formula (pt "LP"))))
(assert
 "allnc x^(TotalList x^ -> allnc n^(TotalNat n^ -> TotalBoole(LP n^ x^)))")
 (assume "x^" "Tx")
 (elim "Tx")
 (assume "n^" "Tn")
 (elim "Tn")
 (use "TotalBooleTrue")
 (assume "n^1" "Useless1" "Useless2")
 (use "TotalBooleFalse")
 (assume "par^" "Tpar")
 (elim "Tpar")
 (assume "x^1" "Tx1" "IHx1" "n^" "Tn")
 (ng #t)
 (use "IHx1")
 (use "TotalNatSucc")
 (use "Tn")
 (assume "x^1" "Tx1" "IHx1" "n^" "Tn")
 (elim "Tn")
 (use "TotalBooleFalse")
 (assume "n^1" "Tn1" "Useless")
 (ng #t)
 (use "IHx1")
 (use "Tn1")
(assume "LPTotalAux" "n^" "Tn" "x^" "Tx")
(use "LPTotalAux")
(use "Tx")
(use "Tn")
;; Proof finished.
(save "LPTotal")

;; LPProp
(set-goal "all x,y,n,m(LP n x -> LP m y -> LP(n+m)(x++y))")
(ind)
(ind)
(cases)
(cases)
(auto)
(ng)
(cases)
(assume "y" "IHy")
(ng)
(assume "n" "m" "Hyp1" "Hyp2")
(use-with "IHy" (pt "n") (pt "Succ m") "Hyp1" "Hyp2")
(assume "y" "IHy" "n")
(cases)
(assume "Hyp1" "Absurd")
(use "Efq")
(use "Absurd")
(ng)
(use "IHy")

(cases)
(assume "x" "IHx")
(ng)
(assume "y" "n" "m" "Hyp1" "Hyp2")
(use-with "IHx" (pt "y") (pt "Succ n") (pt "m") "Hyp1" "Hyp2")
(assume "x" "IHx" "y")
(cases)
(assume "m" "Absurd" "Hyp1")
(use "Efq")
(use "Absurd")
(use "IHx")
;; Proof finished.
(save "LPProp")

;; RP (with a parameter predicate to be substituted by U)

(add-pvar-name "P" (make-arity (py "list par")))

(add-ids
 (list (list "RP" (make-arity (py "nat") (py "list par")) "list"))
 '("RP 0(Nil par)" "InitRP")
 '("allnc n,x,z(P z -> RP n x -> RP(Succ n)(x++z++L:))" "GenRP"))

;; ClosureU
(set-goal
 "all y allnc n,x,z((RP (cterm (x^) U x^))n x -> U z -> LP n y -> U(x++z++y))")
(ind)

;; Base.  Case y=(Nil par)
(assume "n" "x" "z" "RP n x")
(elim "RP n x")

;; InitRP
(ng #t)
(auto)

;; GenRP
(ng #t)
(assume "n1" "x1" "z1" "Useless1" "Useless2" "Useless3" "Useless4" "Absurd")
(use "Efq")
(use "Absurd")

;; Step
(cases)
;; Case L.  Use IHy for n+1
(ng #t)
(assume "y" "IHy" "n" "x" "z" "RP n x" "U z" "LP(Succ n)y")
(use-with "IHy" (pt "Succ n") (pt "x++z++L:") (pt "(Nil par)") "?" "?" "?")
(use "GenRP")
(use "U z")
(use "RP n x")
(use "InitU")
(use "LP(Succ n)y")

;; Case R
(assume "y" "IHy" "n" "x" "z" "RP n x")
(elim "RP n x")

;; First RP clause
(ng #t)
(assume "U z" "Absurd")
(use "Efq")
(use "Absurd")

;; Second RP clause.  Uses IHy, GenU and equality arguments.
(assume "n1" "x1" "z1" "U z1" "RP n1 x1" "IH" "U z")
(ng #t)
(simp (pf "x1++z1++(L::z)++(R::y)=x1++z1++(L::z)++R: ++y"))
(simp (pf "x1++z1++(L::z)=x1++(z1++(L::z))"))
(simp (pf "x1++(z1++(L::z))++R: =x1++(z1++(L::z)++R:)"))
(use "IHy")
(use "RP n1 x1")
(use-with "GenU" (pt "z1") (pt "z") "U z1" "U z")
(simp "ListAppdAssoc")
(simp "ListAppdAssoc")
(simp "ListAppdAssoc")
(use "Truth")
(simp "ListAppdAssoc")
(use "Truth")
(ng #t)
(use "Truth")
;; Proof finished
(save "ClosureU")

;; Soundness
(set-goal "allnc y(U y -> LP 0 y)")
(assume "z" "IdHyp")
(elim "IdHyp")
(use "Truth")
(assume "x" "y" "U x" "LP 0 x" "U y" "LP 0 y")
(simp "<-" "ListAppdAssoc")
(use-with "LPProp" (pt "x") (pt "L::y++R:") (pt "0") (pt "0")
	  "LP 0 x" "?")
(ng #t)
(use-with "LPProp" (pt "y") (pt "R:") (pt "0") (pt "1")
	  "LP 0 y" "Truth")
;; Proof finished.
(save "Soundness")

;; Completeness
(set-goal "all y(LP 0 y -> U y)")
(assume "y" "LP 0 y")
(use-with "ClosureU" (pt "y") (pt "0") (pt "(Nil par)")  (pt "(Nil par)")
	  "?" "InitU" "LP 0 y")
(use "InitRP")
;; Proof finished.
(save "Completeness")

;; ParseLemma
(set-goal "all y ex p((p -> U y) & ((p -> F) -> U y -> F))")
(assume "y")
(ex-intro (pt "LP 0 y"))
(split)
(use "Completeness")
(assume "LP 0 y -> F" "U y")
(use "LP 0 y -> F")
(use "Soundness")
(use "U y")
;; Proof finished.
(save "ParseLemma")

(animate "ClosureU")
(animate "Completeness")

(add-var-name "a" (py "bin"))
(add-var-name "as" (py "list bin"))
(add-var-name "f" (py "list bin=>bin=>bin"))

(define eterm (proof-to-extracted-term (theorem-name-to-proof "ParseLemma")))
(define parser-term (rename-variables (nt eterm)))
(ppc parser-term)

;; [x]
;;  LP 0 x@
;;  (Rec list par=>list bin=>bin=>bin)x
;;  ([as,a][case as ((Nil bin) -> a)
;;                   (a0::as0 -> O)])
;;  ([par,x0,f,as,a]
;;    [case par
;;      (L -> f(a::as)O)
;;      (R -> [case as ((Nil bin) -> O)
;;                      (a0::as0 -> f as0(a0 B a))])])
;;  (Nil bin)
;;  O

;; Since this term involves the recursion operator it is not easy to
;; read.  To grasp its meaning we rewrite it.  In case LP 0 x the
;; result is obtained by applying g to [],O with g recursively defined
;; by

;;   g([],as,a) = a if as=[]
;;                O else
;; g(L::x,as,a) = g(x,a::as,[])
;; g(R::x,as,a) = O               if as=[]
;;                g(x,as0,a0 B a) if as=a0::as0

;; Test of parser-term of type list par=>boole@bin on a list of
;; lists of pars.

;; (generate-seq n) generates a list of 2^n infinite sequences starting
;; with all possible variations of n digits and continuing with 0.

(define (generate-seq n)
  (if (= n 0)
      (list (lambda (n) 0))
      (foldr (lambda (f l)
	       (cons (lambda (n) (if (= n 0) 0 (f (- n 1))))
		     (cons (lambda (n) (if (= n 0) 1 (f (- n 1))))
			   l)))
	     '()
	     (generate-seq (- n 1)))))

;; (length (generate-seq 4))
;; 16

;; (first f n) returns a list of (f 0),(f 1),...,(f n-1).

(define (first f n)
  (if (= n 0)
      '()
       (cons (f 0)
	     (first (lambda (n) (f (+ n 1))) (- n 1)))))

;; (for-each (lambda (x) (display (first x 7)) (newline)) (generate-seq 4))

;; (0 0 0 0 0 0 0)
;; (1 0 0 0 0 0 0)
;; (0 1 0 0 0 0 0)
;; (1 1 0 0 0 0 0)
;; (0 0 1 0 0 0 0)
;; (1 0 1 0 0 0 0)
;; (0 1 1 0 0 0 0)
;; (1 1 1 0 0 0 0)
;; (0 0 0 1 0 0 0)
;; (1 0 0 1 0 0 0)
;; (0 1 0 1 0 0 0)
;; (1 1 0 1 0 0 0)
;; (0 0 1 1 0 0 0)
;; (1 0 1 1 0 0 0)
;; (0 1 1 1 0 0 0)
;; (1 1 1 1 0 0 0)

(define (blist-to-lpar-term blist)
  (if (null? blist)
      (pt "(Nil par)")
      (mk-term-in-app-form
       (pt "(Cons par)")
       (if (zero? (car blist)) (pt "L") (pt "R"))
       (blist-to-lpar-term (cdr blist)))))

(pp (blist-to-lpar-term '(0 1 0)))
;; L::R::L:

(define (generate-lpar-terms n)
  (let* ((seq (generate-seq n))
	 (01lists (map (lambda (f) (first f n)) seq))
	 (reduced-01lists
	  (list-transform-positive 01lists
	    (lambda (l)
	      (and (zero? (car l))
		   (not (zero? (car (last-pair l)))))))))
    (map blist-to-lpar-term reduced-01lists)))

(for-each pp (generate-lpar-terms 6))
;; L::L::L::L::L::R:
;; L::R::L::L::L::R:
;; L::L::R::L::L::R:
;; L::R::R::L::L::R:
;; L::L::L::R::L::R:
;; L::R::L::R::L::R:
;; L::L::R::R::L::R:
;; L::R::R::R::L::R:
;; L::L::L::L::R::R:
;; L::R::L::L::R::R:
;; L::L::R::L::R::R:
;; L::R::R::L::R::R:
;; L::L::L::R::R::R:
;; L::R::L::R::R::R:
;; L::L::R::R::R::R:
;; L::R::R::R::R::R:

;; Test parser-term on all lpar-terms of length l.

(define (test-parser-term parser-term . l)
  (let ((len (if (null? l) 4 (car l))))
    (map (lambda (lpar-term)
	   (display "Testing on ")
	   (display (term-to-string lpar-term))
	   (let* ((pairterm (nt (make-term-in-app-form parser-term lpar-term)))
		  (lterm (term-in-pair-form-to-left pairterm))
		  (rterm (term-in-pair-form-to-right pairterm)))
	     (if (and (term-in-const-form? lterm)
		      (string=? "True" (const-to-name
					(term-in-const-form-to-const lterm))))
		 (begin (display " Parse tree: ")
			(display (term-to-string rterm)))
		 (display " No"))
	     (newline)))
	 (generate-lpar-terms len)))
    *the-non-printing-object*)

(test-parser-term parser-term 6)

;; Testing on L::R::R::R::R::R: No
;; Testing on L::L::R::R::R::R: No
;; Testing on L::R::L::R::R::R: No
;; Testing on L::L::L::R::R::R: Parse tree: O B O B O B O
;; Testing on L::R::R::L::R::R: No
;; Testing on L::L::R::L::R::R: Parse tree: O B(O B O)B O
;; Testing on L::R::L::L::R::R: Parse tree: (O B O)B O B O
;; Testing on L::L::L::L::R::R: No
;; Testing on L::R::R::R::L::R: No
;; Testing on L::L::R::R::L::R: Parse tree: (O B O B O)B O
;; Testing on L::R::L::R::L::R: Parse tree: ((O B O)B O)B O
;; Testing on L::L::L::R::L::R: No
;; Testing on L::R::R::L::L::R: No
;; Testing on L::L::R::L::L::R: No
;; Testing on L::R::L::L::L::R: No
;; Testing on L::L::L::L::L::R: No

(remove-var-name "a")

;; Program extraction from classical proofs

(add-var-name "a"  (py "alpha"))

;; Following tutor.tex

(set-goal "all v excl w RevI v w")
(assume "v0" "AllNegHyp")
(cut "all u allnc v(v++u eqd v0 ->
                    all w(RevI v w -> bot))")
(assume "claim")
(use "claim"
     (pt "v0") (pt "(Nil alpha)") (pt "(Nil alpha)"))
(ng)
(use "InitEqD")
(intro 0)
(ind)
;; Base
(assume "v")
(ng)
(assume "v=v0" "w")
(simp "v=v0")
(use "AllNegHyp")
;; Step
(assume "a" "u" "IH" "v" "EqDHyp" "w" "RHyp")
(use "IH" (pt "v++a:") (pt "a::w"))
(ng)
(use "EqDHyp")
(intro 1)
(use "RHyp")
;; Proof finished.
(define class-proof (np (current-proof)))

(av "g" (py "list alpha=>list alpha"))

(define eterm
  (atr-min-excl-proof-to-structured-extracted-term class-proof))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [xs]
;;  (Rec list alpha=>list alpha=>list alpha)xs([xs0]xs0)
;;  ([a,xs0,g,xs1]g(a::xs1))
;;  (Nil alpha)

(pp (nt (make-term-in-app-form neterm (pt "a::b::c:"))))

;; We first need to prove totality of Even and Odd

;; NatEvenOddTotal
(set-goal "allnc n^(TotalNat n^ -> TotalBoole(Even n^) & TotalBoole(Odd n^))")
(assume "n^" "Tn")
(elim "Tn")
(split)
(use "TotalBooleTrue")
(use "TotalBooleFalse")
(assume "n^1" "Tn1" "IHn1")
(split)
(ng #t)
(use "IHn1")
(ng #t)
(use "IHn1")
;; Proof finished.
(save "NatEvenOddTotal")

;; EvenTotal
(set-goal (rename-variables (term-to-totality-formula (pt "Even"))))
(assume "n^" "Tn")
(use "NatEvenOddTotal")
(use "Tn")
;; Proof finished.
(save "EvenTotal")

;; OddTotal
(set-goal (rename-variables (term-to-totality-formula (pt "Odd"))))
(assume "n^" "Tn")
(use "NatEvenOddTotal")
(use "Tn")
;; Proof finished.
(save "OddTotal")

;; NatEvenOddDisjunct
(set-goal "all n(Even n -> Odd n -> F)")
(ind)
;; Base
(ng)
(assume "Useless" "Absurd")
(use "Absurd")
;; Step
(assume "n" "IHn" "E(n+1)" "O(n+1)")
(use-with "IHn" "O(n+1)" "E(n+1)")
;; Proof finished.
(save "NatEvenOddDisjunct")

(set-goal "all n ex m((Even n -> 2*m=n) & (Odd n -> 2*m+1=n))")
(ind)
;; Base
(ex-intro "0")
(split)
(assume "Useless")
(use "Truth")
(assume "Absurd")
(use "Absurd")
;; Step
(assume "n" "IHn")
(by-assume "IHn" "m" "mProp")
(ex-intro "[if (Even n) m (Succ m)]")
(split)
;; Case Odd n
(assume "E(n+1)")
(assert "Even n -> F")
 (assume "En")
 (use "NatEvenOddDisjunct" (pt "n"))
 (use "En")
 (use "E(n+1)")
(assume "Even n -> F")
(simp "Even n -> F")
(ng #t)
(use "mProp")
(use "E(n+1)")
;; Case Even n
(assume "O(n+1)")
(simp "O(n+1)")
(ng #t)
(use "mProp")
(use "O(n+1)")
;; Proof finished.

(define eterm (proof-to-extracted-term (current-proof)))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [n](Rec nat=>nat)n 0([n0,n1][if (Even n0) n1 (Succ n1)])

;; The parsing example is in git/minlog/examples/parsing/parens.scm
