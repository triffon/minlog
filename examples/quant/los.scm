;; 2014-10-13.  los.scm

;; A problem due to Los: Let P,Q be transitive, Q symmetric, and assume
;; P union Q = D^2.  Then either P=D^2 or Q=D^2.

;; Proof idea: Write the goal as
;; all a,b,c,d((P a b -> bot) -> (Q c d -> bot) -> bot).
;; First prove a lemma: all a,b,c((P a b -> bot) -> (Q b c -> bot) -> bot)
;; using PorQ at a and c.  Then prove the goal by first using the lemma
;; at abc to obtain Q b c, and second at abd to obtain Q b d.

;; (load "~/git/minlog/init.scm")

(add-pvar-name "P" "Q" (make-arity (py "alpha") (py "alpha")))
(add-var-name "x" "y" "z" "a" "b" "c" "d" (py "alpha"))

;; Lemma
(set-goal
     "all x,y,z(P x y -> P y z -> P x z) -> 
      all x,y,z(Q x y -> Q y z -> Q x z) -> 
      all x,y(Q x y -> Q y x) -> 
      all x,y((P x y -> F) -> Q x y) -> 
      all x,y((Q x y -> F) -> P x y) -> 
      all x,y((P x y -> F) -> (Q x y -> F) -> F) -> 
      all a,b,c((P a b -> F) -> (Q b c -> F) -> F)")
(assume "TransP" "TransQ" "SymQ" "NotPImpQ" "NotQImpP" "PorQ"
	"a" "b" "c" "NotPab" "NotQbc")
(use "PorQ" (pt "a") (pt "c"))
;; (1) Goal P a c -> F
(assume "Pac")
(use "NotPab")
(use "TransP" (pt "c"))
(use "Pac")
(use "NotQImpP")
(assume "Qcb")
(use "NotQbc")
(use "SymQ")
(use "Qcb")
;; (2) Goal Q a c -> F
(assume "Qac")
(use "NotQbc")
(use "TransQ" (pt "a"))
(use "SymQ")
(use "NotPImpQ")
(use "NotPab")
(use "Qac")
;; Proof finished.
(save "Lemma")

;; Los
(set-goal
     "all x,y,z(P x y -> P y z -> P x z) -> 
      all x,y,z(Q x y -> Q y z -> Q x z) -> 
      all x,y(Q x y -> Q y x) -> 
      all x,y((P x y -> F) -> Q x y) -> 
      all x,y((Q x y -> F) -> P x y) -> 
      all x,y((P x y -> F) -> (Q x y -> F) -> F) -> 
      all a,b,c,d((P a b -> F) -> (Q c d -> F) -> F)")
(assume "TransP" "TransQ" "SymQ" "NotPImpQ" "NotQImpP" "PorQ")
(assume "a" "b" "c" "d" "NotPab" "NotQcd")
(use-with "Lemma" "TransP" "TransQ" "SymQ" "NotPImpQ" "NotQImpP" "PorQ"
	  (pt "a") (pt "b") (pt "c") "NotPab" "?")
(assume "Q b c")
(use-with "Lemma" "TransP" "TransQ" "SymQ" "NotPImpQ" "NotQImpP" "PorQ"
	  (pt "a") (pt "b") (pt "d") "NotPab" "?")
(assume "Q b d")
(use "NotQcd")
(use "TransQ" (pt "b"))
(use "SymQ")
(use "Q b c")
(use "Q b d")
;; Proof finished.
(save "Los")
