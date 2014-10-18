;; 2014-10-13.  prop.scm

;; (load "~/git/minlog/init.scm")

;; Some example formulas from propositional logic.

(add-predconst-name "A" "B" "C" (make-arity))

(define stab-imp
  (pf "(((A2 -> B) -> B) -> A2)
    -> (((A1 -> A2) -> B) -> B) -> A1 -> A2"))

;; To automatically search for a proof, proceed as follows.
(set-goal stab-imp)
(prop)
;; (dnp)

;; Alternatively we can search for a proof in minimal logic with
(set-goal stab-imp)
(search)
;; (dnp)

(define peirce (pf "((A -> B) -> A) -> A"))
(set-goal peirce)
(prop)
;; (dnp)

;; (set-goal peirce)
;; (search) 
;; proof not found: classical logic needed

;; We can use search to find out how much of classical logic is needed
(define stab-and-efq-to-peirce
  (pf "(((A1 -> B) -> B) -> A1)
    -> (B -> A2)
    -> ((A1 -> A2) -> A1) -> A1"))
(set-goal stab-and-efq-to-peirce)
(search)
;; (dnp)
;; Indeed, it suffices to use efq for A2 only.

(define peirce-and-efq-to-stab
  (pf "(((A -> B) -> A) -> A)
    -> (B -> A)
    -> ((A -> B) -> B) -> A"))
(set-goal peirce-and-efq-to-stab)
(search)
;; (dnp)

(define peirce-imp1
  (pf "(((A2 -> B) -> A2) -> A2)
    -> (((A1 -> A2) -> B) -> A1 -> A2) -> A1 -> A2"))
(set-goal peirce-imp1)
(search)
;; (dnp)

(define peirce-imp2
  (pf "(((A -> B2) -> A) -> A)
    -> ((A -> B1 -> B2) -> A) -> A"))
(set-goal peirce-imp2)
(search)
;; (dnp)

(define peirce-and1
  (pf "(((A1 -> B) -> A1) -> A1)
    -> (((A2 -> B) -> A2) -> A2)
    -> (((A1 & A2) -> B) -> A1 & A2) -> A1 & A2"))
(set-goal peirce-and1)
(search)
;; (dnp)

(define peirce-and2
  (pf "(((A -> B1) -> A) -> A)
    -> (((A -> B2) -> A) -> A)
    -> ((A -> B1 & B2) -> A) -> A"))
(set-goal peirce-and2)
(search)
;; (dnp)

(define mints (pf "((((A -> B) -> A) -> A) -> B) -> B"))
(set-goal mints)
(prop)
;; (dnp)

(set-goal mints)
(search)
;; (dnp)

(define kuroda-imp
  (pf "(F -> B)
       -> (((A -> F) -> F) -> ((B -> F) -> F))
       -> ((A -> B) -> F) -> F"))
(set-goal kuroda-imp)
(search)
;; (dnp)

(define mints-c 
  (pf "((((A1 -> A2) -> A1) -> A1) -> A3) -> A3"))
(set-goal mints-c)
(search)
;; unprovable by automated search with given multiplicities
(prop)
;; Not provable in minimal propositional logic.
;; No bot or F outside quantifiers, hence also 
;; not provable in intuitionistic propositional logic.
;; ok, ?_1 is proved in classical propositional logic.  Proof finished.
;; (dnp)

(define mints-solovev
  (pf "(A1 -> (A -> B) -> A)
    -> ((A1 -> A) -> B)
    -> B"))
(set-goal mints-solovev)
(search)
;; (dnp)

(define tatsuta
  (pf "(((A7 -> A1) -> A10) -> A4 -> A5)
    -> (((A8 -> A2) -> A9) -> A3 -> A10)
    -> (A1 -> A8)
    -> A6
    -> A7
    -> (((A3 -> A2) -> A9) -> A4)
    -> (A1 -> A3)
    -> (((A6 -> A1) -> A2) -> A9)
    -> A5"))
(set-goal tatsuta)
(search)
;; (dnp)

(set-goal tatsuta)
(prop)
;; (dnp)

(define tatsuta1
  (pf "(((A8 -> A2) -> A9) -> A3 -> A10)
    -> (((A3 -> A2) -> A9) -> A4)
    -> (((A6 -> A1) -> A2) -> A9)
    -> (((A7 -> A1) -> A10) -> A4 -> A5)
    -> (A1 -> A3)
    -> (A1 -> A8)
    -> A6
    -> A7
    -> A5"))
(set-goal tatsuta1)
(search)
;; (dnp)

(set-goal tatsuta1)
(prop)
;; (dnp)

;; Yet another Tatsuta-formula (Seyfried, JSL94? or 93?)

(define tatsuta2
  (pf "(A9 -> A5 -> A0)
    -> (A8 -> A2 -> A1)
    -> (A7 -> A10 -> A1)
    -> (A11 -> A6 -> A0)
    -> ((A11 -> A13) -> A3 -> A4)
    -> ((A7 -> A12) -> A2 -> A13)
    -> (A0 -> A10)
    -> A5
    -> A6
    -> ((A8 -> A12) -> A3)
    -> (A0 -> A2)
    -> ((A9 -> A1) -> A12)
    -> A4"))
(set-goal tatsuta2)
(prop)
;; (dnp)

(define franzen
  (pf "((A1 -> A1 & A2 & A3) -> F)
    -> ((A2 -> A1 & A2 & A3) -> F)
    -> ((A3 -> A1 & A2 & A3) -> F)
    -> F"))
(set-goal franzen)
;; (search) 
;; unprovable by automated search with given multiplicities

(prop)
;; (dnp)

;; Every negated formula derivable classically is also derivable
;; intuitionistically.  For the proof one needs derivations in minimal
;; logic of
;; ~~~A -> ~A (clear) and of
;; not-not-stab: (F -> A) -> ~~(~~A -> A)
;; not-not-imp:  ~~(A -> B) -> ~~A -> ~~B

(set-goal (pf "((((A -> F) -> F) -> A) -> F) -> F"))
(prop)
;; Not provable in minimal propositional logic.
;; ok, ?_1 is proved in intuitionistic propositional logic.  Proof finished.
;; (dnp)

(define not-not-stab
  (pf "(F -> A) -> ((((A -> F) -> F) -> A) -> F) -> F"))
(set-goal not-not-stab)
(search)
;; (dnp)

(define not-not-imp
  (pf "(((A -> B) -> F) -> F) -> ((A -> F) -> F) -> (B -> F) -> F"))
(set-goal not-not-imp)
(prop)
;; (dnp)

(define debruijn
  (pf "((A -> B) -> (B -> A) -> A & B & C) 
    -> ((B -> C) -> (C -> B) -> A & B & C) 
    -> ((C -> A) -> (A -> C) -> A & B & C) 
    -> A & B & C"))
(set-goal debruijn)
;; (search) takes impossibly long time
(prop)
;; (dnp) ;normalization needs about 30 sec

;; Proof in minimal logic:
;; Assume A and B.  Then C by (0).  Hence A -> B -> C. 
;; By symmetry A -> C -> B. 
;; Hence A -> B by (1)
;; By symmetry B -> A.
;; Hence A & B & C by (0)

(define debruijn-without-and
  (pf "((A -> B) -> (B -> A) -> A)
    -> ((A -> B) -> (B -> A) -> B)
    -> ((A -> B) -> (B -> A) -> C)
    -> ((B -> C) -> (C -> B) -> A)
    -> ((B -> C) -> (C -> B) -> B)
    -> ((B -> C) -> (C -> B) -> C)
    -> ((C -> A) -> (A -> C) -> A)
    -> ((C -> A) -> (A -> C) -> B)
    -> ((C -> A) -> (A -> C) -> C)
    -> B"))
(set-goal debruijn-without-and)
;; (search) takes impossibly long time
;; (prop) ;can do it, but with a very long proof
;; (dp)
;; (dnp) takes impossibly long time

;; Plaisted noted in a talk in Munich (1994) that 
;; ((A <-> B) <-> A) -> B is underivable in intuitionistic logic.
;; Classically one can see the validity by cases on A.  The
;; intuitionistic validity reduces to

(define plaisted
  (pf "((A -> B) -> (B -> A) -> A) -> (A -> B) -> B"))
(set-goal plaisted)
(prop)
;; (dnp)

;; Jan Ekman noted in his thesis (and in a talk in Turin in February 1994)
;; that the second pruning step in a beta-normal derivation of
;; ((A -> B) -> A) -> (A -> A -> B) -> B leads to a beta-convertible
;; derivation that converts to the original one.  Note that the formula
;; can be seen as ~(A <-> ~A) with falsum replaced by B,

(define ekman (pf "((A -> B) -> A) -> (A -> A -> B) -> B"))
(set-goal ekman)
(prop)
;; (dnp)

;; Jan Lukasiewicz proved in `The shortest axiom of the implicational
;; calculus of propositions' (Proceedings of the Royal Irish Academy,
;; Sect. A, Vol 52, 1948) that

(define lukasiewicz (pf "((A1 -> A2) -> A3) -> ((A3 -> A1) -> (A4 -> A1))"))
(set-goal lukasiewicz)
(prop)
;; Not provable in minimal propositional logic.
;; No bot or F outside quantifiers, hence also 
;; not provable in intuitionistic propositional logic.
;; ok, ?_1 is proved in classical propositional logic.  Proof finished.
;; (dnp)

;; is the shortest such axiom for classical implicational logic.  Gordeev
;; found short proofs how from the Lukasiewicz axiom (by substitution and
;; modus ponens) one can obtain the so-called Tarski-Bernays axioms, i.e.

(define law-of-simplification (pf "A -> (B -> A)"))
(define peirce (pf "((A -> B) -> A) -> A"))
(define law-of-hypothetical-syllogism
  (pf "(A1 -> A2) -> ((A2 -> A3) -> (A1 -> A3))"))

(remove-predconst-name "A" "B" "C")
