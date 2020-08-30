;; 2016-06-09.  fuerst.scm.  Based on temp/fuerstenberg.scm.
;; Incorporatimg some simplifications from Dominique Larchey-Wendling
;; in his Coq-proof in archive/larchey/fuerst.v

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

(add-var-name "b" "x" (py "nat"))
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
(set-goal "all p,m,l(l<m -> exl n p l*n=Prod m p)")
(assume "p")
(ind)
;; Base
(assume "l")
(ng)
(assume "Absurd")
(intro 0 (pt "0"))
(use "EfAtom")
(use "Absurd")
;; Step
(assume "m" "IH" "l" "l<m+1")
(ng)
(use "NatLtSuccCases" (pt "l") (pt "m"))
(use "l<m+1")
;; Case l<m
(assume "l<m")
(inst-with-to "IH" (pt "l") "l<m" "IHInst")
(drop "IH")
(by-assume "IHInst" "n1" "n1Prop")
(intro 0 (pt "n1*p m"))
(ng)
(simp "n1Prop")
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
(set-goal "all x,n(1<x -> 1=x*n -> F)")
(assume "x")
(cases)
(assume "1<x" "Absurd")
(use "Absurd")
(assume "n" "1<x")
(ng)
(assume "1=x*n+x")
(simphyp-with-to "1<x" "1=x*n+x" "HypSimp")
(assert "0+x<x")
 (use "NatLeLtTrans" (pt "x*n+x"))
 (use "NatLeMonPlus")
 (use "Truth")
 (use "Truth")
 (use "HypSimp")
(assume "Absurd")
(use "Absurd")
;; Proof finished.
(save "PrimeProdNotOne")

;; UnionNpsUnifClosed
(set-goal "all p,m(all l(l<m -> 1<=p l) -> exl b(all x(
 all l,n1(l<m -> x=p l*n1 -> F) ->
 all n,l,n1(l<m -> x+b*n=p l*n1 -> F))))")
(assume "p" "m" "1<=ps")
(intro 0 (pt "Prod m p"))
(assume "x" "xnotinU" "n" "l" "n1" "l<m")
(inst-with-to "ProdPerm" (pt "p") (pt "m") (pt "l") "l<m" "ProPermInst")
(by-assume "ProPermInst" "n2" "n2Prop")
(simp "<-" "n2Prop")
(inst-with-to "xnotinU" (pt "l") (pt "n1--n2*n") "l<m" "xnotinUInst")
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
(set-goal "all p,m(all l(l<m -> 1<p l) -> exl x all l,n(l<m -> x=p l*n -> F))")
(assume "p" "m" "1<ps")
;; First show 1notinU
(assert "all l,n(l<m -> 1=p l*n -> F)")
 (assume "l" "n" "l<m")
 (use "PrimeProdNotOne")
 (use "1<ps")
 (use "l<m")
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
(assume "l" "n" "l<m" "EqHyp")
(use "bProp" (pt "1") (pt "1") (pt "l") (pt "n"))
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

;; Soundness proof

(define proof (theorem-name-to-proof "ProdPerm"))
(define sproof (proof-to-soundness-proof proof))
;; (cdp sproof) ;ok

;; ProdPermSound
(set-goal(rename-variables (nf (proof-to-formula sproof))))
(use-with sproof)
;; Proof finished.
(save "ProdPermSound")

(pp (rename-variables (nf (proof-to-formula sproof))))

;; all p,m,l(
;;  l<m -> 
;;  (ExLTMR (cterm (n) p l*n=Prod m p))
;;  ((Rec nat=>nat=>nat)m([n]0)([n,p0,n0][if (n0<n) (p0 n0*p n) (Prod n p)])l))

(define proof (theorem-name-to-proof "UnionNpsUnifClosed"))
(animate "ProdPerm")
(define sproof (proof-to-soundness-proof proof))
;; (cdp sproof);ok

(pp (rename-variables (nf (proof-to-formula sproof))))

;; all p,m(
;;  all l(l<m -> 1<=p l) -> 
;;  (ExLTMR (cterm (n) 
;;            all x(
;;             all l,n0(l<m -> x=p l*n0 -> F) -> 
;;             all n0,l,n1(l<m -> x+n*n0=p l*n1 -> F))))
;;  (Prod m p))

;; UnionNpsUnifClosedSound
(set-goal(rename-variables (nf (proof-to-formula sproof))))
(use-with sproof)
;; Proof finished.
(save "UnionNpsUnifClosedSound")

(define proof (theorem-name-to-proof "mPrimesDontSuffice"))
(animate "UnionNpsUnifClosed")
(define sproof (proof-to-soundness-proof proof))
;; (cdp sproof) ;ok
(define nsproof (np sproof))
(proof-to-expr-with-formulas nsproof)

;; ElimMR: all m,p,n^(
;;  (ExLTMR (cterm (n0) 
;;            all x(
;;             all l,n1(l<m -> x=p l*n1 -> F) -> 
;;             all n1,l,n2(l<m -> x+n0*n1=p l*n2 -> F))))
;;  n^ -> 
;;  all n0(
;;   all x(
;;    all l,n1(l<m -> x=p l*n1 -> F) -> all n1,l,n2(l<m -> x+n0*n1=p l*n2 -> F)) --> 
;;   (ExLTMR (cterm (x) all l,n1(l<m -> x=p l*n1 -> F)))(Succ n0)) -> 
;;  (ExLTMR (cterm (x) all l,n0(l<m -> x=p l*n0 -> F)))(Succ n^))
;; UnionNpsUnifClosedSound: all p,m(
;;  all l(l<m -> 1<=p l) -> 
;;  (ExLTMR (cterm (n) 
;;            all x(
;;             all l,n0(l<m -> x=p l*n0 -> F) -> 
;;             all n0,l,n1(l<m -> x+n*n0=p l*n1 -> F))))
;;  (Prod m p))
;; NatLtToLe: all n,m(n<m -> n<=m)
;; Intro: all m,p,n(
;;  all l,n0(l<m -> n=p l*n0 -> F) --> 
;;  (ExLTMR (cterm (n0) all l,n1(l<m -> n0=p l*n1 -> F)))n)
;; PrimeProdNotOne: all x,n(1<x -> 1=x*n -> F)
;; u: all l(l<m -> 1<p l)
;; u0: l<m
;; u1: l4470<m

;; (lambda (p)
;;   (lambda (m)
;;     (lambda (u)
;;       (((((ElimMR m) p) ((Prod m) p))
;;          (((UnionNpsUnifClosedSound p) m)
;;            (lambda (l)
;;              (lambda (u0) (((NatLtToLe 1) (p l)) ((u l) u0))))))
;;         (lambda (n4465)
;;           (lambda (u0)
;;             ((((Intro m) p) (+ n4465 1))
;;               (((u0 1)
;;                  (lambda (l4470)
;;                    (lambda (n1)
;;                      (lambda (u1)
;;                        (((PrimeProdNotOne (p l4470)) n1)
;;                          ((u l4470) u1))))))
;;                 1))))))))







