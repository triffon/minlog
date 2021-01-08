;; 2014-10-13.  dc-first.scm

;; Demofile for the example - Every infinite subsequence of 0 and 1s
;; has a subsequence which is constant 0 or 1 - (plus corollary)
;; discussed in Seisenberger, On the constructive content of proofs,
;; 2003, section 3.3.

;; This is an example for program extraction from classical proofs
;; using the axiom of classical dependent choice; A-translation is done
;; by adding a realizer for the A-translated axiom; demonstrates that
;; using strong axioms, here DC, not necessarily leads to bad programs.

;; The example was first suggested by Stolzenberg as an example for
;; program extraction from classical proofs; here we do slightly
;; different proof, using DC.

;; (load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(libload "list.scm")
(set! COMMENT-FLAG #t)

;; 1. Declarations
;; ===============

(add-var-name "a" "b" "c" (py "boole"))
(add-var-name "i" "j" "k" (py "nat"))
(add-var-name "e"  (py "nat=>nat")) 
(add-var-name "h"  (py "nat=>boole"))

(add-global-assumption "<-lemma" "all n,m(n<m+n+1)")
(add-global-assumption "=-lemma" (pf "all a,b,c(a=b -> c=b -> a=c)"))

;; OnlyTwo
(set-goal "all a((a=False -> bot) -> (a=True -> bot) -> bot)")
(ind)
(ng)
(assume 1 2)
(use 2)
(use "Truth")
(ng)
(assume 1 2)
(use 1)
(use "Truth")
;; Proof finished.
(save "OnlyTwo")

(define dc-inst
  (pf "all h(
       all n excl m((n<m -> h m=False -> bot) -> bot) -> 
       excl e(e 0=0 ! all k((e k<e(k+1) -> h(e(k+1))=False -> bot) -> bot)))"))

;; 2. Interactive proofs
;; =====================

;; Using DC we prove the lemma saying that every function h:nat=>boole has 
;; an infinite constant subsequence.

;; ConstantSubSequence
(set-goal
 (mk-imp
  dc-inst 
  (pf "all h excl a,e all k((e k<e(k+1) -> h(e(k+1))=a -> bot) -> bot)")))
(assume "dc-inst" "h" 2)
(use-with "dc-inst" (pt "h") "?" "?")

;; all n excl m((n<m -> h m=False -> bot) -> bot)
(assume "n" 3)
(use-with 2 (pt "True") (pt "[m]m+n") "?")
(assume "k")
(ng)
(strip)
(drop "dc-inst" 2)

(use-with "OnlyTwo" (pt "h(Succ(k+n))") "?" "?")

(assume 5)
(use-with 3 (pt "Succ(k+n)") "?")
(strip)
(use 6)
(use "<-lemma")
(use 5)

(use 4)
(use "Truth")

;; all e(e 0=0 -> excl k(e k<e(k+1) -> h(e(k+1))=False -> bot))
(assume "e" 3)
(use 2)
;; Proof finished.
(save "ConstantSubSequence")

;; Finally, we apply A-translation to the corollary

;; Cor
(set-goal (mk-all (pv "h")
                  (mk-imp dc-inst 
                          (pf "excl i,j(i<j ! h i=h j)"))))
(assume  "h" "dc-inst" 2)
(use-with "ConstantSubSequence" "dc-inst" (pt "h") "?")
(assume "a" "e" 3)
(use-with 3 (pt "0") "?")
(strip)
(use-with 3 (pt "1") "?")
(strip)
(use 2 (pt "e 1") (pt "e 2"))
;; e 1<e 2
(use 6)
;; h(e 1)=h(e 2)
(use "=-lemma" (pt "a"))
(use 5)
(use 7)
;; Proof finished.
(save "Cor")

(define min-excl-proof (np (expand-theorems (theorem-name-to-proof "Cor"))))

;; 3. Realizing classical dependent choice
;; =======================================

;; The following definitions and notations refer to section 3.2.

(define rho (py "nat"))
(define nu (py "nat yprod nat"))
(define sigma (mk-arrow nu nu))
(define type-of-G (mk-arrow rho (mk-arrow rho sigma nu) nu))
(define type-of-Y (mk-arrow (mk-arrow (py "nat") rho)
			    (mk-arrow (py "nat") sigma)
			    nu))
(add-var-name "x" rho)
(add-var-name "z" sigma)
(add-var-name "G" type-of-G)
(add-var-name "Y" type-of-Y)
(define type-of-list (py "list (nat yprod (nat yprod nat=>nat yprod nat))"))
(add-var-name "t" type-of-list)

;; [G,Y]Psi G Y Lin is a realizer for DC^X:
(add-program-constant "Psi" (mk-arrow type-of-G type-of-Y type-of-list nu))

;; 4. A-translation
;; ================

(define program
  (atr-min-excl-proof-to-structured-extracted-term
   min-excl-proof
   (pt "[h,G,Y]Psi G Y (Nil (nat yprod (nat yprod nat=>nat yprod nat)))")))

;; For a better display we add some additional variable names:

(add-var-name "f" (py "nat=>(nat yprod nat=>nat yprod nat)=>nat yprod nat"))
(add-var-name "g" (py "nat=>nat yprod nat=>nat yprod nat"))
(add-var-name "p"(py "nat yprod nat"))

(define nprogram (rename-variables (nt program)))
(pp nprogram)

;; [h]
;;  Psi
;;  ([n,f]
;;    [if (h(Succ n))
;;        [if (h(Succ(Succ n)))
;; 	   (Succ n pair Succ(Succ n))
;; 	   (f(Succ(Succ n))([p]p))]
;;      (f(Succ n)([p]p))])
;;  ([e,g]g 0(g 1(e 1 pair e 2)))
;;  (Nil nat yprod(nat yprod nat=>nat yprod nat))

;; Note: depends on Psi as it is not animated yet.

;; 5. Animation of Psi
;; ===================

(define type-of-beta (mk-arrow (py "nat") (make-yprod rho sigma)))
(add-var-name "varbeta" type-of-beta)

(define type-of-Tilde (mk-arrow type-of-Y type-of-beta nu))

(add-program-constant "Tilde" type-of-Tilde)

(add-computation-rules
 "Tilde Y varbeta"
 "Y([n][if (n=0) 0 (lft(varbeta(Pred n)))])([n]rht(varbeta n))")

;; H is a realizer for an instance of the efq-axiom.  Here the instance
;; is bot -> (bot -> bot).

(add-program-constant "H" (mk-arrow nu nu nu))
(add-computation-rules "H p1 p2" "p1")

(add-computation-rules
 "Psi G Y t"
 "Tilde Y
      ([n]
        [if (n<Lh t)
            (n thof t)
            (0 pair H(G[if (Lh t=0)
                      0
                      (lft(Pred Lh t thof t))]
        ([x,z]Psi G Y(t++(x pair z):))))])")

(define nprogram (rename-variables (nt program)))
(pp nprogram)

;; [h]
;;  [if (h 1)
;;    [if (h 2) (1 pair 2) [if (h 3) ([if (h 4) 3 2] pair 4) (2 pair 3)]]
;;    [if (h 2) ([if (h 3) 2 1] pair 3) (1 pair 2)]]

;; 6. Running the extracted program
;; ================================

(add-program-constant "Constsequence" (py "nat=>boole"))
(add-computation-rules "Constsequence n" "False")
(pp (nt (mk-term-in-app-form nprogram (pt "Constsequence"))))
;; ==> "1 pair 2"

;; Note that the 0th element is not found, the reason being h \circ e is
;; only constant for inputs n>0.

(add-program-constant "Sequence" (py "nat=>boole"))
(add-computation-rules
 "Sequence 0" "True"
 "Sequence 1" "True"
 "Sequence 2" "False"
 "Sequence 3" "True"
 "Sequence 4" "False")

(pp (nt (mk-term-in-app-form nprogram (pt "Sequence"))))
;; ==> "2 pair 4"

(add-program-constant "Dualsequence" (py "nat=>boole"))
(add-computation-rules
 "Dualsequence 0" "False"
 "Dualsequence 1" "False"
 "Dualsequence 2" "True"
 "Dualsequence 3" "False"
 "Dualsequence 4" "True")

(pp (nt (mk-term-in-app-form nprogram (pt "Dualsequence"))))
;; ==> "1 pair 3"

(add-program-constant "Interesting" (py "nat=>boole"))
(add-computation-rules
 "Interesting 0" "False"
 "Interesting 1" "True"
 "Interesting 2" "False"
 "Interesting 3" "True"
 "Interesting 4" "True")

(pp (nt (mk-term-in-app-form nprogram (pt "Interesting"))))
;; ==> "3 pair 4"

