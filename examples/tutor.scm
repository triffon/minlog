;; $Id: tutor.scm 2451 2011-03-29 21:32:09Z schwicht $

;; This file contains the examples of the Tutorial for Minlog version 5.0

;; (load "~/minlog/init.scm")

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
(add-var-name "U" "V" "W" (py "beta"))
(add-program-constant "In" (py "alpha=>beta=>boole"))
(add-infix-display-string "In" "in" 'rel-op)
(add-var-name "f" (py "alpha=>alpha"))

(set-goal "all f(
 all x,V(f x in V -> excl U(x in U & all y(y in U -> f y in V))) ->
 all x,W(f(f x)in W -> excl U(x in U & all y(y in U -> f(f y)in W))))")
(search)
(dnp)

(remove-var-name "x" "y" "f" "U" "V" "W")

;; Datatypes and inductively defined predicates

;; (set! COMMENT-FLAG #f)
;; (libload "nat.scm")
;; (set! COMMENT-FLAG #t)

(display-alg "nat")
(display-pconst "NatPlus")

;; Normalizing, apply term rewriting rules.
(pp (nt (pt "3+4")))
(pp (nt (pt "Succ n+Succ m+0")))

;; Defining program constants.

(add-program-constant  "Double" (py "nat=>nat"))
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

(add-program-constant "ListRev" (py "list alpha=>list alpha") t-deg-one)
(add-prefix-display-string "ListRev" "Rev")
(add-computation-rules
 "Rev(Nil alpha)" "(Nil alpha)"
 "Rev(x::xs)" "Rev xs++x:")
;; (add-computation-rule (pt "Rev(Nil alpha)") (pt "(Nil alpha)"))
;; (add-computation-rule (pt "Rev(x::xs)") (pt "Rev xs++x:"))

(display-pconst "ListAppd")

;; ListAppd
;;   comprules
;; 	(Nil alpha)++xs2	xs2
;; 	(x1::xs1)++xs2	x1::xs1++xs2
;;   rewrules
;; 	xs++(Nil alpha)	xs
;; 	xs1++x2: ++xs2	xs1++(x2::xs2)

(set-goal "all v,w Rev(v++w)eqd Rev w++Rev v")
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
(av "fun" (py "alpha=>alpha"))

(set-goal "all fun,ys,xs (fun map (xs++ys) eqd(fun map xs)++(fun map ys))")
(set-goal "all fun,xs (fun map (Rev xs) eqd Rev (fun map xs))")

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
(assume "n")
(elim)

(ex-intro (pt "0"))
(prop)

(assume "n1" 2 3)
(by-assume 3 "m0" 4)
(ex-intro (pt "m0+1"))
(simp "<-" 4)
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
         '("RevI(Nil alpha)(Nil alpha)" "InitRev")
         '("all a,v,w(RevI v w  -> RevI(v++a:)(a::w))" "GenRev"))

(aga "RevSym" "all v,w(RevI v w -> RevI w v)")

(set-goal "all v ex w RevI v w")
(ind)
(ex-intro (pt "(Nil alpha)"))
(intro 0)
;; Step
(assume "a" "v" 1)
(by-assume 1 "w" 2)
(ex-intro (pt "w++a:"))
(use "RevSym")
(intro 1)
(use "RevSym")
(use 2)
;; Proof finished.

(define constr-proof (current-proof))

(define eterm (proof-to-extracted-term constr-proof))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

(term-to-expr neterm)

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
(prop)
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

(set-goal (pf "all n ex m ((Even n -> 2*m = n) & (Odd n -> 2*m+1=n))"))

;; Inductive Definition of Even, without computational content

(add-ids (list (list "EvenNC" (make-arity (py "nat"))))
	 '("EvenNC 0" "InitEvenNC")
	 '("allnc n(EvenNC n -> EvenNC(n+2))" "GenEvenNC"))

;; Exercise: Prove the following statement, using exnc-intro.

(set-goal "allnc n(EvenNC n -> exnc m m+m=n)")

;; Program extraction from classical proofs

(set-goal "all v excl w RevI v w")

(assume "v0" 1)
(cut "all u allnc v(v++u eqd v0 -> all w(RevI v w -> bot))")

(assume "claim")
(use "claim" (pt "v0") (pt "(Nil alpha)") (pt "(Nil alpha)"))
(ng)
(use "InitEqD")
(intro 0)
(ind)
;; Base
(assume "v")
(ng)
(assume 2 "w")
(simp 2)
(use 1)
;; Step
(assume "a" "u" "IH" "v" 3 "w" 4)
(use "IH" (pt "v++a:") (pt "a::w"))
(ng)
(use 3)
(intro 1)
(use 4)

(define class-proof (np (current-proof)))

(av "g" (py "list alpha=>list alpha"))

(define eterm
  (atr-min-excl-proof-to-structured-extracted-term class-proof))
(define neterm (rename-variables (nt eterm)))

(pp neterm)

;; [xs]
;;  (Rec list alpha=>list alpha=>list alpha)xs([xs0]xs0)
;;  ([x,xs0,g,xs1]g(x::xs1))

(pp (nt (make-term-in-app-form neterm (pt "a::b::c:"))))

;; Was
;; #|
;; [v0]
;;  (Rec list alpha=>list alpha=>list alpha)v0(cEqDCompatRev list alpha)
;;  ([a1,v2,g3,v4]g3(a1::v4))
;;  (Nil alpha)
;; |#

;; (animate "EqDCompatRev")

;; (pp (nt program))

;; (pp (nt (make-term-in-app-form program (pt "a::b::c:"))))
