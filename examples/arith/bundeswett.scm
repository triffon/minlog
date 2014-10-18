;; $Id: bundeswett.scm 2156 2008-01-25 13:25:12Z schimans $

;; (load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(set! COMMENT-FLAG #t)

(add-var-name "f" (py "nat=>nat"))

;; Final goal: "all f(all n f(f n)<f(n+1) -> all n f n=n)"..  First:

;; NatMon
(set-goal "all f(all n f n<f(n+1) -> all n,m(n<m -> f n<f m))")
(assume "f" "StrictIncr" "n")
(ind)
;; Base
(ng)
(use "Efq")
 ;; Step
(assume "m" "IHm" "n<m+1")
(use "NatLeCases" (pt "m") (pt "n"))
(use "NatLtSuccToLe")
(use "n<m+1")
(assume "n<m")
(use "NatLtTrans" (pt "f m"))
(use-with "IHm" "n<m")
(use "StrictIncr")
(assume "n=m")
(simp "n=m")
(use "StrictIncr")
;; Proof finished.
(save "NatMon")

;; NatMonLe
(set-goal "all f(all n f n<f(n+1) -> all n,m(n<=m -> f n<=f m))")
(assume "f" "StrictIncr" "n" "m" "n<=m")
(use "NatLeCases" (pt "m") (pt "n"))
(use "n<=m")
(assume "n<m")
(use "NatLtToLe")
(use "NatMon")
(use "StrictIncr")
(use "n<m")
(assume "n=m")
(simp "n=m")
(use "Truth")
;; Proof finished.
(save "NatMonLe")

;; Recall the goal "all f(all n f(f n)<f(n+1) -> all n f n=n)".
;; Let Hyp: "all n f(f n)<f(n+1)".

;; Lemma1: "all n,k(n<=k -> n<=f k)"
;; Proof.  Induction on n.  Step: From S n<=k we have k=k1+1, hence n<=k1.
;; By IHn n<=f k1, and again by IHn n<=f(f k1), so by Hyp n<f(k1+1)=f k.

;; Lemma1
(set-goal "all f(all n f(f n)<f(n+1) -> all n,k(n<=k -> n<=f k))")
(assume "f" "Hyp")
(ind)
;; Base
(assume "k" "Useless")
(use "Truth")
;; Step
(assume "n" "IHn")
(cases)
;; Case k=0
(ng #t)
(use "Efq")
;; Case k+1
(assume "k" "n<=k")
(use "NatLtToSuccLe")
(use "NatLeLtTrans" (pt "f(f k)"))
(use "IHn")
(use "IHn")
(use "n<=k")
(use "Hyp")
;; Proof finished.
(save "Lemma1")

;; Lemma2: "all n n<=f n"
(set-goal "all f(all n f(f n)<f(n+1) -> all n n<=f n)")
(assume "f" "Hyp" "n")
(use "Lemma1")
(use "Hyp")
(use "Truth")
;; Proof finished.
(save "Lemma2")

;; Lemma3: "all n f n<f(n+1)"
(set-goal "all f(all n f(f n)<f(n+1) -> all n f n<f(n+1))")
(assume "f" "Hyp" "n")
(use "NatLeLtTrans" (pt "f(f n)"))
(use "Lemma2")
(use "Hyp")
(use "Hyp")
;; Proof finished.
(save "Lemma3")

;; Lemma4: "all n f n<n+1"
(set-goal "all f(all n f(f n)<f(n+1) -> all n f n<n+1)")
(assume "f" "Hyp" "n")
(use "NatNotLeToLt")
(assume "n+1<=f n")
(use-with "NatLeLtTrans" (pt "f(n+1)") (pt "f(f n)") (pt "f(n+1)") "?" "?")
(use "NatMonLe")
(use "Lemma3")
(use "Hyp")
(use "n+1<=f n")
(use "Hyp")
;; Proof finished.
(save "Lemma4")

;; Theorem: "all n n=f n"
(set-goal "all f(all n f(f n)<f(n+1) -> all n n=f n)")
(assume "f" "Hyp" "n")
(use "NatLeAntiSym")
(use "Lemma2")
(use "Hyp")
(use "NatLtSuccToLe")
(use "Lemma4")
(use "Hyp")
;; Proof finished.
(save "Theorem")
