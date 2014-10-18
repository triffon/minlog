;; $Id: bar.scm 2581 2012-12-27 02:01:15Z miyamoto $

;; Based on Monika Seisenberger's Thesis "On the Constructive Content
;; of Proofs", LMU 2003

;; This file contains the definition of the inductive predicate Bar and
;; examples for the use of the introduction and elimination axioms.

;; We prove 
;; - Bar [] implies that every infinite sequence has a good initial segment.
;; - Bar ws*[].

;; We will make use of these two Lemmas in higman-finite.scm.
;; Therefore, we prove the statements for an alphabet consisting of
;; natural numbers.

;; 1. Definitions
;; ==============

;; (load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(libload "list.scm")
(set! COMMENT-FLAG #t)

;; list.scm introduces the algebra of lists with the constructors Nil
;; and Cons.  (Cons w ws) is displayed as w::ws.  The length of a list
;; is denoted by Lh.

(define boole (py "boole"))
(define nat (py "nat"))
(define word (py "list nat"))
(define seq (py "list list nat"))

(remove-var-name "n" "k" "m")
(add-var-name "a" "b" "c" "i" "j" "k" "m" "n" nat)
(add-var-name "w" "u" "v" "x" "y" "z" "as" "bs" word)
(add-var-name "ws" "vs" "xs" "ys" "zs" seq)

(add-var-name "f" (make-arrow nat word))

;; (add-program-constant "Init" (mk-arrow (mk-arrow nat word) nat seq) 1)
;; (add-computation-rule (pt "Init f 0") (pt "(Nil list nat)"))
;; (add-computation-rule (pt "Init f(Succ n)") (pt "Init f n::f n"))

;; list.scm provides (f fbar n) for (Init f n)

;; Emb, L, Good are inductive definitions without computational content.

(add-ids (list (list "Emb" (make-arity word word)))
	 '("Emb(Nil nat)(Nil nat)" "InitEmb")
	 '("all v^,w^,a^(Emb v^ w^ -> Emb v^(a^ ::w^))" "GenEmbInit")
         '("all v^,w^,a^(Emb v^ w^ -> Emb(a^ ::v^)(a^ ::w^))" "GenEmbCons"))

;; EmbNil
(set-goal "all w Emb(Nil nat)w")
(ind)
(use "InitEmb")
(assume "a" "w" "IHw")
(use "GenEmbInit")
(use "IHw")
;; Proof finished.
(save "EmbNil")

;; L v ws means that v embeds into one w from ws.
(add-ids (list (list "L" (make-arity word seq)))
	 '("all v^,w^,ws^(Emb v^ w^ -> L v^(w^ ::ws^))" "InitL")
	 '("all v^,ws^,w^(L v^ ws^  -> L v^(w^ ::ws^))" "GenL"))

;; Good ws means that one w from ws embeds into a later one.
(add-ids (list (list "Good" (make-arity seq)))
	 '("all v^,ws^(L v^ ws^ -> Good(v^ ::ws^))" "InitGood")
	 '("all ws^,w^(Good ws^ -> Good(w^ ::ws^))" "GenGood"))

;; GoodAppd
(set-goal "all ws2(Good ws2 -> all ws1 Good(ws1++ws2))")
(assume "ws2" "Gws2")
(ind)
(ng #t)
(use "Gws2")
(assume "w" "ws" "Hyp")
(ng #t)
(use "GenGood")
(use "Hyp")
;; Proof finished.
(save "GoodAppd")

;; Bar is an inductive predicate with computational content, whose
;; clauses are called Leaf and Branch.  The type of Bar is algBar (or
;; tree) with the constructors CLeaf and CBranch.

(add-ids (list (list "Bar" (make-arity seq) "algBar"))
	 '("allnc ws(Good ws -> Bar ws)" "Leaf")
	 '("allnc ws(all w Bar(ws ++w :) -> Bar ws)" "Branch"))

;; 2. The interactive proof
;; ========================

;; BarThm
(set-goal
 "allnc ws(Bar ws -> all f,n((f fbar n)=ws -> ex m Good(f fbar m)))")
(assume "vs" "Bvs")

;; Ind(Bar).
(elim "Bvs")

;; 1. Good ws
(assume "ws" "Good ws" "f" "n" "(f fbar n)=ws")
(ex-intro (pt "n"))
(simp "(f fbar n)=ws")
(use "Good ws")

;; 2. all w Bar(ws++w:) 
(assume "ws" "all w Bar(ws++w:)" "IH" "f" "n" "(f fbar n)=ws")
(use-with "IH" (pt "f n") (pt "f") (pt "Succ n") "?")

;; (f fbar n+1)=ws++(f n):
(inst-with-to
 "FBarAppdLast" (py "list nat") (pt "n") (pt "f") "FBarAppdLastInst")
(simp "FBarAppdLastInst")
(simp "(f fbar n)=ws")
(ng #t)
(use "Truth")
;; Proof finished.
(save "BarThm")

;; 3. The extracted program 
;; ========================

(add-var-name "ga" (py "list nat=>algBar"))
(add-var-name "gb" (py "list nat=>(nat=>list nat)=>nat=>nat"))

(define eterm (proof-to-extracted-term (theorem-name-to-proof "BarThm")))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [algBar]
;;  (Rec algBar=>(nat=>list nat)=>nat=>nat)algBar([f,a]a)
;;  ([ga,gb,f,a]gb(f a)f(Succ a))

;; 4. A second example to demonstrate the use of the clauses
;; =========================================================

;; Prop1
(set-goal "allnc ws Bar(ws++(Nil nat):)")
(assume "ws")
(use "Branch")
(assume "w")
;; ?_4: Bar(ws++(Nil nat): ++w:)
(use "Leaf")
;; ?_5: Good(ws++(Nil nat): ++w:)
(simp "<-" "ListAppdAssoc")
;; ?_6: Good(ws++((Nil nat): ++w:))
(use "GoodAppd")
(use "InitGood")
(use "InitL")
(use "EmbNil")
;; Proof finished.
(save "Prop1")

(pp (proof-to-extracted-term (theorem-name-to-proof "Prop1")))
;; CBranch([w]CLeaf)
