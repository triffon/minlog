;; 2014-10-13.  quant.scm

;; (load "~/git/minlog/init.scm")

(add-var-name "x" "y" "z" (py "alpha"))
(add-pvar-name "P" (make-arity))
(add-pvar-name "Q" (make-arity (py "alpha")))
(add-pvar-name "R" (make-arity (py "alpha") (py "alpha")))

;; AllImp
(set-goal "all x(Q1 x -> Q2 x) -> all x Q1 x -> all x Q2 x")
(assume 1 2 "x")
(use 1)
(use 2)
;; Proof finished.

(set-goal "all x(Q1 x -> Q2 x) -> all x Q1 x -> all x Q2 x")
(search)
;; Proof finished.

;; AllAndOne
(set-goal "all x(Q1 x & Q2 x) -> all x Q1 x & all x Q2 x")
(assume 1)
(split)
(assume "x")
(use 1)
(assume "x")
(use 1)
;; Proof finished.

(set-goal "all x(Q1 x & Q2 x) -> all x Q1 x & all x Q2 x")
(search)
;; Proof finished.

;; AllAndTwo
(set-goal "all x Q1 x & all x Q2 x -> all x(Q1 x & Q2 x)")
(assume 1 "x")
(split)
(use 1)
(use 1)
;; Proof finished.

(set-goal "all x Q1 x & all x Q2 x -> all x(Q1 x & Q2 x)")
(search)
;; Proof finished.

;; AllExca
(set-goal "all x Q x -> exca x Q x")
(assume 1 2)
(use 2 (pt "(Inhab alpha)"))
(use 1)
;; Proof finished.

(set-goal "all x Q x -> exca x Q x")
(search)
;; Proof finished.

(set-goal "all x,y(R x y -> R y x) ->
           all x,y,z(R x y -> R y z -> R x z) ->
           all x,y(R x y -> R x x)")
(assume "Sym" "Trans" "x" "y" 1)
(use "Trans" (pt "y"))
(use 3)
(use "Sym")
(use 3)
;; Proof finished.

(set-goal "all x,y(R x y -> R y x) ->
           all x,y,z(R x y -> R y z -> R x z) ->
           all x,y(R x y -> R x x)")
(search)
;; Proof finished.

;; Now we treat somewhat systematically how in classical logic one can
;; deal with quantifiers in implications.  - Below we shall do the same
;; for the constructive existential quantifier.

;; qf1m is obtained from the formula (all x Q x -> P) -> ex x(Q x -> P)
;; by translating "ex" into "not all not" and adding stability of Q:

(define qf1m (pf "all x(((Q x -> F) -> F) -> Q x) 
               -> (all x Q x -> P) 
               -> all x((Q x -> P) -> F)
               -> F"))
(set-goal qf1m)
(assume 1 2 3)
(use 3 (pt "x"))
(assume 4)
(use 2)
(assume "x1")
(use 1)
(assume 5)
(use 3 (pt "x1"))
(assume 6)
(use 2)
(assume "x2")
(use 1)
(assume 7)
(use 5)
(use 6)
;; Proof finished.

(set-goal qf1m)
(search)
;; Proof finished.

(define qf2 (pf "(P -> all y Q y) -> all y(P -> Q y)"))
(set-goal qf2)
(assume 1 "y" 2)
(use 1)
(use 2)
;; Proof finished.

(set-goal qf2)
(search)
;; Proof finished.

;; qf3 is obtained from the formula (ex x Q x -> P) -> all x(Q x -> P)
;; by translating "ex" into "not all not":

(define qf3 (pf "((all x(Q x -> F) -> F) -> P) -> all x(Q x -> P)"))
(set-goal qf3)
(assume 1 "x" 2)
(use 1)
(assume 3)
(use 3 (pt "x"))
(use 2)
;; Proof finished.

(set-goal qf3)
(search)
;; Proof finished.

;; qf4m is obtained from the formula (P -> ex y Q y) -> ex y(P -> Q y)
;; by translating "ex" into "not all not" and adding ef-falso for Q:

(define qf4m (pf "all y(F -> Q y)
               -> (P -> all y(Q y -> F) -> F)
               -> all y((P -> Q y) -> F) 
               -> F"))
(set-goal qf4m)
(assume 1 2 3)
(use 3 (pt "y"))
(assume 4)
(use 1)
(use 2)
(use 4)
(assume "y1" 5)
(use 3 (pt "y1"))
(assume 6)
(use 5)
;; Proof finished.

(set-goal qf4m)
(search)
;; Proof finished.

;; qf5m is obtained from the formula ex x(Q x -> P) -> all x Q x -> P
;; by translating "ex" into "not all not" and adding stability of P:

(define qf5m (pf "(((P -> F) -> F) -> P)
               -> (all x((Q x -> P) -> F) -> F)
               -> all x Q x
               -> P"))
(set-goal qf5m)
(assume 1 2 3)
(use 1)
(assume 4)
(use 2)
(assume "x" 5)
(use 4)
(use 5)
(use 3)
;; Proof finished.

(set-goal qf5m)
(search)
;; Proof finished.

(define qf6 (pf "all y( P -> Q y) -> P -> all y Q y"))
(set-goal qf6)
(assume 1 2 "y")
(use 1)
(use 2)
;; Proof finished.

(set-goal qf6)
(search)
;; Proof finished.

;; qf7m is obtained from the formula all x(Q x -> P) -> ex x Q x -> P
;; by translating "ex" into "not all not" and adding stability of P:

(define qf7m (pf "(((P -> F) -> F) -> P)
               -> all x(Q x -> P) 
               -> (all x(Q x -> F) -> F) 
               -> P"))
(set-goal qf7m)
(assume 1 2 3)
(use 1)
(assume 4)
(use 3)
(assume "x" 5)
(use 4)
(use 2 (pt "x"))
(use 5)
;; Proof finished.

(set-goal qf7m)
(search)
;; Proof finished.

;; qf8 is obtained from the formula ex y(P -> Q y) -> P -> ex y Q y
;; by translating "ex" into "not all not":

(define qf8 (pf "(all y((P -> Q y) -> F) -> F)
              -> P 
              -> all y(Q y -> F)
              -> F"))
(set-goal qf8)
(assume 1 2 3)
(use 1)
(assume "y" 4)
(use 3 (pt "y"))
(use 4)
(use 2)
;; Proof finished.

(set-goal qf8)
(search)
;; Proof finished.

;; Some more examples involving classical existence

;; Drinker
(set-goal "all y(((Q y -> F) -> F) -> Q y) -> exca x(Q x -> all y Q y)")
(assume 1 2)
(use 2 (pt "(Inhab alpha)"))
(assume 3 "y")
(use 1)
(assume 4)
(use 2 (pt "y"))
(assume 5 "z")
(use 1)
(assume 6)
(use 4)
(use 5)
;; Proof finished.

(set-goal "all y(((Q y -> F) -> F) -> Q y) -> exca x(Q x -> all y Q y)")
(search)
;; Proof finished.

;; Now we treat the constructive existential quantifier

;; ExAndOne
(set-goal "ex x(Q1 x & Q2 x) -> ex x Q1 x & ex x Q2 x")
(assume 1)
(split)
(ex-elim 1)
(assume "x" 2)
(ex-intro (pt "x"))
(use 2)
(ex-elim 1)
(assume "x" 2)
(ex-intro (pt "x"))
(use 2)
;; Proof finished.

(set-goal "ex x(Q^1 x & Q^2 x) -> ex x Q^1 x & ex x Q^2 x")
(search)
;; Proof finished.

;; Normalized extracted term:
(dnet) ;"[x0]x0@x0"

;; ExAndTwo
(set-goal "ex x Q x & P -> ex x(Q x & P)")
(assume 1)
(inst-with 1 'left)
(ex-elim 2)
(assume "x" 3)
(ex-intro (pt "x"))
(split)
(use 3)
(use 1)
;; Proof finished.

(set-goal "ex x Q^ x & P^ -> ex x(Q^ x & P^)")
(search)
;; Proof finished.

;; Normalized extracted term:
(dnet) ;"[x0]x0"

;; AllEx
(set-goal "all x Q^ x -> ex x Q^ x")
(assume 1)
(ex-intro (pt "(Inhab alpha)"))
(use 1)
;; Proof finished.

;; Normalized extracted term:
(dnet) ;"(Inhab alpha)"

(set-goal "all x Q^ x -> ex x Q^ x")
(search)
;; Proof finished.

;; Normalized extracted term:
(dnet) ;"x"

;; qf1 is the formula (all x Q x -> P) -> ex x(Q x -> P)
;; It is not provable in minimal logic.

;; (define qf2 (pf "(P -> all y Q y) -> all y(P -> Q y)")) see above

(define qf3 (pf "(ex x Q x -> P) -> all x(Q x -> P)"))
(set-goal qf3)
(assume 1 "x" 2)
(use 1)
(ex-intro (pt "x"))
(use 2)
;; Proof finished.

(set-goal qf3)
(search)
;; Proof finished.

;; qf4 is the formula (P -> ex y Q y) -> ex y(P -> Q y)
;; It is not provable in minimal logic.

(define qf5 (pf "ex x(Q x -> P) -> all x Q x -> P"))
(set-goal qf5)
(assume 1 2)
(ex-elim 1)
(assume "x" 3)
(use 3)
(use 2)
;; Proof finished.

(set-goal qf5)
(assume 1 2)
(ex-elim 1)
(search)
;; Proof finished.

;; (define qf6 (pf "all y(P -> Q y) -> P -> all y Q y")) see above

(define qf7 (pf "all x(Q x -> P) -> ex x Q x -> P"))
(set-goal qf7)
(assume 1 2)
(ex-elim 2)
(use 1)
;; Proof finished.

(set-goal qf7)
(assume 1 2)
(ex-elim 2)
(search)
;; Proof finished.

(define qf8 (pf "ex y(P^ -> Q^ y) -> P^ -> ex y Q^ y"))
(set-goal qf8)
(assume 1 2)
(ex-elim 1)
(assume "x" 3)
(ex-intro (pt "x"))
(use 3)
(use 2)
;; Proof finished.

(set-goal qf8)
(search)
;; Proof finished.

;; Normalized extracted term:
(dnet) ;"[x0]x0"
