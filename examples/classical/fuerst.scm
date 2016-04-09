;; 2016-04-09.  fuerstenberg.scm.  Based on temp/fuerstenberg.scm.

;; Extraction of computational content from Fuerstenberg's topological
;; proof of the existence of infinitely many primes.  This is the
;; fifth of "Six proofs of the infinity of primes", Problem 1 in
;; M. Aigner and G. Ziegler, Proofs from THE BOOK, Springer 1998.
;; Original reference: H. Fuerstenberg, On the infinitude of primes,
;; Amer. Math. Monthly 62 (1955), 353.

(load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(set! COMMENT-FLAG #t)

;; X open:           all_{x in X} ex_{b>0} all_n x+bn in X
;; X uniformly open: ex_{b>0} all_{x in X} all_n x+bn in X
;; Y (uniformly) closed := ~Y (uniformly) open.

;; mPrimesDontSuffice
;; Given p_l>1 (l<m).  Then there is x>1 not divisible by any p_l,
;; i.e., x in ~U_{l<m}Np_l.

;; Proof ignoring witnesses.  Np_l closed, hence U_{l<m}Np_l closed,
;; hence ~U_{l<m}Np_l open, hence infinite, hence has an element.

;; Constructive proof.  U_{l<m}Np_l uniformly closed, hence
;; ~U_{l<m}Np_l uniformly open.  Witness b := p_0*...*p_{m-1}.
;; Since p_l>1 we have 1 in ~U_{l<m}Np_l.  Thus 1+b in ~U_{l<m}Np_l.

;; The extracted term will be [p,n]Succ(Prod n p)

(add-var-name "l" "b" "x" (py "nat"))
(add-var-name "p" (py "nat=>nat")) ;primes

(add-program-constant "Prod" (py "nat=>(nat=>nat)=> nat"))
(add-computation-rules
 "Prod 0 p" "1"
 "Prod(Succ l)p" "(Prod l p)*(p l)")

(set-totality-goal "Prod")
(use "AllTotalElim")
(ind)
;; Base
(strip)
(use "NatTotalVar")
;; Step
(assume "n" "IH")
(assume "p^" "Tp")
(ng)
(use "NatTimesTotal")
(use "IH")
(use "Tp")
(use "Tp")
(use "NatTotalVar")
;; Proof finished.
(save-totality)

;; ProdPerm
(set-goal "all p,m,l(l<m -> exl k p l*k=Prod m p)")
(assume "p")
(ind)
;; Base
(assume "l")
(ng)
(use "Efq")
;; Step
(assume "m" "IH" "l" "l<m+1")
(ng)
(use "NatLtSuccCases" (pt "l") (pt "m"))
(use "l<m+1")
;; Case l<m
(assume "l<m")
(inst-with-to "IH" (pt "l") "l<m" "IHInst")
(drop "IH")
(by-assume "IHInst" "k1" "k1Prop")
(intro 0 (pt "k1*p m"))
(ng)
(simp "k1Prop")
(use "Truth")
;; Case l=m
(assume "l=m")
(intro 0 (pt "Prod m p"))
(simp "l=m")
(use "NatTimesComm")
;; Proof finished.
(save "ProdPerm")

;; NatLeOneProd
(set-goal "all p,m(all l(l<m -> 1<=p l) -> 1<=Prod m p)")
(assume "p")
(ind)
;; Base
(strip)
(use "Truth")
;; Step
(assume "m" "IH" "1<=ps")
(ng)
(assert "1*1<=Prod m p*p m")
 (use "NatLeMonTimes")
 (use "IH")
 (assume "l" "l<m")
 (use "1<=ps")
 (use "NatLtTrans" (pt "m"))
 (use "l<m")
 (use "Truth")
 (use "1<=ps")
 (use "Truth")
(assume "Assertion")
(use "Assertion")
;; Proof finished.
(save "NatLeOneProd")
 
;; PrimeProdNotOne
(set-goal "all p,m(all l(l<m -> 1<p l) -> all l,k(l<m -> 1=p l*k -> F))")
(assume "p" "m" "1<ps" "l")
(cases)
;; k=0
(assume "l<m" "Absurd")
(use "Absurd")
;; Successor
(ng)
(assert "all k(l<m -> 1+1<=p l*k+p l)")
 (cases)
 ;; k=0
 (assume "l<m")
 (ng)
 (use "NatLtToSuccLe")
 (use "1<ps")
 (use "l<m")
 ;; Successor
 (assume "k" "l<m")
 (use "NatLeMonPlus")
 (ng)
 (use "NatLeTrans" (pt "p l"))
 (use "NatLtToLe")
 (use "1<ps")
 (use "l<m")
 (use "Truth")
 (use "NatLtToLe")
 (use "1<ps")
 (use "l<m")
(assume "Assertion" "k" "l<m" "EqHyp")
(assert "1+1<=p l*k+p l")
 (use "Assertion")
 (use "l<m")
 (simp "<-" "EqHyp")
(assume "Absurd")
(use "Absurd")
;; Proof finished.
(save "PrimeProdNotOne")

;; UnionNpsUnifClosed
;; all m exl b(0<b andu all x(x in ~U_{l<m}Np_l -> all n x+b*n in ~U_{l<m}Np_l))
;; where x in ~U_{l<m}Np_l means all_{l<m} all k(x=p l*k -> F)

(set-goal "all p,m(all l(l<m -> 1<=p l) -> exl b(1<=b andu all x(
 all l,k(l<m -> x=p l*k -> F) ->
 all n,l,k(l<m -> x+b*n=p l*k -> F))))")
(assume "p" "m" "1<=ps")
(intro 0 (pt "Prod m p"))
(split)
(use "NatLeOneProd")
(use "1<=ps")
(assume "x" "xnotinU" "n" "l" "k" "l<m")
(inst-with-to "ProdPerm" (pt "p") (pt "m") (pt "l") "l<m" "ProPermInst")
(by-assume "ProPermInst" "k1" "k1Prop")
(simp "<-" "k1Prop")
(inst-with-to "xnotinU" (pt "l") (pt "k--k1*n") "l<m" "xnotinUInst")
(drop "xnotinU")
(assume "EqHyp")
(use "xnotinUInst")
(ng)
(simp "<-" "EqHyp")
(use "Truth")
;; Proof finished.
(save "UnionNpsUnifClosed")

;; mPrimesDontSuffice
;; Assuming 1<p l (l<m) there is an x with x in ~U_{l<m}Np_l
(set-goal "all p,m(all l(l<m -> 1<p l) -> exl x all l,k(l<m -> x=p l*k -> F))")
(assume "p" "m" "1<ps")
;; First show 1notinU
(assert "all l,k(l<m -> 1=p l*k -> F)")
 (use "PrimeProdNotOne")
 (use "1<ps")
(assume "1notinU")
(assert "all l(l<m -> 1<=p l)")
 (assume "l" "l<m")
 (use "NatLtToLe")
 (use "1<ps")
 (use "l<m")
(assume "1<=ps")
(inst-with-to "UnionNpsUnifClosed" (pt "p") (pt "m") "1<=ps" "bEx")
(by-assume "bEx" "b" "bProp")
(intro 0 (pt "1+b"))
(assume "l" "k" "l<m" "EqHyp")
(elim "bProp")
(assume "Useless" "bPropRight")
(drop "bProp" "Useless")
(use "bPropRight" (pt "1") (pt "1") (pt "l") (pt "k"))
(use "1notinU")
(use "l<m")
(use "EqHyp")
;; Proof finished.
(save "mPrimesDontSuffice")

(define proof (current-proof))
(define eterm (proof-to-extracted-term proof))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [p,n]Succ(cUnionNpsUnifClosed p n)

(animate "UnionNpsUnifClosed")
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [p,n]Succ(Prod n p)
