;; $Id: higman01.scm 2581 2012-12-27 02:01:15Z miyamoto $
;; An inductive proof Higman's Lemma for a 0/1 alphabet
;; see Coquand/Fridlender 1994
;; We prove that every infinite sequence in a 0/1 alphabet has a good
;; initial segment


;; 1. Definitions
;; ==============

;; (load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(exload "bar/bar.scm")
(set! COMMENT-FLAG #t)
(add-global-assumption
 "OnlyTwoLetters" "all a,b,c((a=b -> F) -> (c=a -> F) -> c=b)")

;; R a vs ws means vs= v1 ... vn, ws = a::v1 ... a::vn

(add-ids
 (list (list "R" (make-arity nat seq seq)))
 '("allnc a R a(Nil list nat)(Nil list nat)" "InitR") 
 '("allnc vs,ws,w,a(R a vs ws -> R a(vs++(w:))(ws++((a::w):)))" "GenR"))

;; TT a ws zs holds iff zs = z_1 ... z_n is of length n>0, all z_p are
;; of the form z_p = a_p::u_p, and ws = z_1 ... z_m u_{l_1} ...u_{l_k}
;; where m = l_1 < l_2 < ... < l_k is the set of indices p<=n such that
;; a_p=a.

(add-ids
 (list (list "TT" (make-arity nat seq seq)))
 '("allnc ws,zs,w,a,b((a=b -> F) -> R b ws zs ->
                      TT a(zs++w:)(zs++(a::w):))" "InitTT")
 '("allnc ws,zs,w,a(TT a ws zs -> TT a(ws++w:)(zs++(a::w):))" "GenTTEq")
 '("allnc ws,zs,w,a,b((a=b -> F) -> TT a ws zs -> TT a ws(zs++(b::w):))"
   "GenTTNeq"))

(display-idpc "Emb" "L" "Good" "R" "TT")

(add-global-assumption
 "Lemma2nc" "allnc ws,zs,a(R a ws zs -> Good ws -> Good zs)")
(add-global-assumption
 "Lemma3nc" "allnc ws,zs,a(TT a ws zs -> Good ws -> Good zs)")
(add-global-assumption
 "Lemma4nc" "allnc ws,zs,a((ws=(Nil list nat) -> F) -> 
                           R a ws zs -> TT a ws zs)")

;; 2. Interactive proofs
;; =====================

;; Prop1 has been proven in bar.scm

;; Prop2

(set-goal "allnc xs(Bar xs ->
           allnc ys(Bar ys -> 
           all zs,a,b((a=b -> F) -> TT a xs zs  -> TT b ys zs -> Bar zs)))")
(assume "xs1" "Bxs1")
(elim "Bxs1")

;; 1. Good xs 
(assume "xs" "Good xs" "ys" "Bar ys" "zs" "a" "b" "a=b -> F" 
        "TT a xs zs" "TT b ys zs")
(use "Leaf")
(use-with "Lemma3nc" (pt "xs") (pt "zs") (pt "a") "TT a xs zs" "Good xs")

;; 2. all w Bar(xs::w)
(assume "xs" "all w Bar(xs++w:)" "IH1" "ys1" "Bys1")
(elim "Bys1")

;; 2.1
(assume "ys" "Good ys" "zs" "a" "b" "a=b -> F" "TT a xs zs" "TT b ws zs")
(use "Leaf")
(use-with "Lemma3nc" (pt "ys") (pt "zs") (pt "b") "TT b ws zs" "Good ys")

;; 2.2
(assume "ys" "all w Bar(ys++w:)" "IH2" "zs" "a" "b"
	"a=b -> F" "TT a xs zs" "TT b ws zs")
(use "Branch")

;; structural induction on w 
(ind) 

;; 2.2.1
(use "Prop1")

;; 2.2.2
(assume "c" "z" "Bar(zs++z:)")

(cases (pt "c=a"))

(assume "c=a")
(simp "c=a")

(use "IH1" (pt "z") (pt "ys") (pt "a") (pt"b"))
;; Bar ys
(use "Branch")

(use "all w Bar(ys++w:)")
;; a=b -> F
(use "a=b -> F")

;; TT a(xs++z:)(zs++(a::):)
(use "GenTTEq")
(use "TT a xs zs")

;; TT b ys(zs++(a::z):)
(use "GenTTNeq")
(assume "b=a")
(use "a=b -> F")
(simp "b=a")
(use "Truth")
(use "TT b ws zs")

;; false
(assume "c=a -> F")
(cut (pf "c=b"))
(assume "c=b")

(use-with "IH2" (pt "z") (pt "zs++(c::z):") (pt "a") (pt "c") "?" "?" "?")
(assume "a=c")
(use "c=a -> F")
(simp "a=c")
(use "Truth")

(simp "c=b")
(use "GenTTNeq")
(use "a=b -> F")
(use "TT a xs zs")

;; TT c(ys++z:)(zs++(c::z):) from
(simp "c=b")
(use "GenTTEq")
(use "TT b ws zs")
(use "OnlyTwoLetters" (pt "a"))
(use "a=b -> F")
(use "c=a -> F")
;; Proof finished.
(save  "Prop2")

;; The extracted program from Prop2

(add-var-name "gc" (py "list nat=>list(list nat)=>algBar"))
(add-var-name "gd" (py "list nat=>algBar=>list(list nat)=>nat=>nat=>algBar"))
(add-var-name "ge" (py "list nat=>list(list nat)=>nat=>nat=>algBar"))

(define eterm (proof-to-extracted-term (theorem-name-to-proof "Prop2")))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [algBar]
;;  (Rec algBar=>algBar=>list list nat=>nat=>nat=>algBar)algBar
;;  ([algBar0,ws,a,a0]CLeaf)
;;  ([ga,gd,algBar0]
;;    (Rec algBar=>list list nat=>nat=>nat=>algBar)algBar0([ws,a,a0]CLeaf)
;;    ([ga0,ge,ws,a,a0]
;;      CBranch
;;      ([w]
;;        [if w
;;          cPropOne
;;          ([a1,w0]
;;           [if (a1=a)
;;             (gd w0(CBranch ga0)(ws++(a::w0):)a a0)
;;             (ge w0(ws++(a1::w0):)a a1)])])))

;; Prop3

(set-goal
 "all a 
 allnc xs(Bar xs -> (xs=(Nil list nat) -> F) -> all zs(R a xs zs -> Bar zs))")
(assume "a" "xs1" "Bxs1")
(elim "Bxs1")

;; all ws(good ws -> formula[a,ws])

(assume "xs" "Good xs" "xs ne Nil" "zs" "R a xs zs")
(use "Leaf")
(use-with "Lemma2nc" (pt "xs") (pt "zs") (pt "a") "R a xs zs" "Good xs")

;; step
(assume "xs"  "all w Bar xs++w:" "IH"  "xs ne Nil" "zs" "R a xs zs")
(use "Branch")
(ind)
(use "Prop1")
(assume "c" "z" "Bar zs++z:")
(cases (pt "c=a"))
(assume "c=a")
(use-with "IH" (pt "z") "?" (pt "zs++(c::z):") "?")
;; xs++z: =(Nil list nat) -> F
(assume "xs++z: =(Nil list nat)")
(assert (pf "Lh(xs++z:)=0"))
 (simp "xs++z: =(Nil list nat)")
 (use "Truth")
(assume "Absurd")
(use "Absurd")

;; R a(xs++z:)(zs++(c::z):)
(simp "c=a")
(use "GenR")
(use "R a xs zs")

;; (c=a -> F) -> Bar(zs++(c::z):)
(assume "c=a -> F")
(cut (pf "a=c -> F"))
(assume "a=c -> F")
(use-with "Prop2"  (pt "xs") "?" 
                   (pt "zs++z:") "Bar zs++z:" 
                   (pt "zs++(c::z):")(pt "a") (pt "c") "?" "?" "?")

;; Bar xs
(use "Branch")
(use "all w Bar xs++w:")

;; a=c -> F 
(use "a=c -> F")

;; TT a xs(zs++(c::z):)
(use "GenTTNeq")
(use "a=c -> F")

;; TT a xs zs
(use "Lemma4nc" )
(use "xs ne Nil")
(use "R a xs zs")

;; TT c(zs++z:)(zs++(c::z):)
(use "InitTT" (pt "xs") (pt "a"))
(use "c=a -> F")
(use "R a xs zs")

;; a=c -> F
(assume "a=c")
(use "c=a -> F")
(simp "a=c")
(use "Truth")
;; Proof finished.
(save "Prop3")

;; The extracted program from Prop3

(define eterm (proof-to-extracted-term (theorem-name-to-proof "Prop3")))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [a,algBar]
;;  (Rec algBar=>list list nat=>algBar)algBar([ws]CLeaf)
;;  ([ga,gc,ws]
;;    CBranch
;;    ([w]
;;      (Rec list nat=>algBar)w cPropOne
;;      ([a0,w0,algBar0]
;;        [if (a0=a)
;;          (gc w0(ws++(a0::w0):))
;;          (cPropTwo(CBranch ga)algBar0(ws++(a0::w0):)a a0)])))

;; The proof of the Theorem

(set-goal "Bar(Nil list nat)")
(use "Branch")

(ind)
;1.
(use "Prop1")
;2.
(assume "a" "w" "Bar((Nil list nat)++w:)")
(use-with "Prop3" (pt "a") (pt "w:") "Bar((Nil list nat)++w:)" "?"
	  (pt "(a::w):") "?")
(ng #t)
(assume "Absurd")
(use "Absurd")

;; R a(w:)((a::w):)
(use-with "GenR" (pt "(Nil list nat)") (pt "(Nil list nat)")
	  (pt "w") (pt "a") "?")
(use "InitR")
;; Proof finished.
(save "Thm")

(define eterm (proof-to-extracted-term (theorem-name-to-proof "Thm")))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

(pp (nt (proof-to-extracted-term (theorem-name-to-proof "Thm"))))

;; CBranch
;; ([w]
;;   (Rec list nat=>algBar)w cPropOne
;;   ([a,w0,algBar]cPropThree a algBar(a::w0):))

(set-goal "all f ex m Good(f fbar m)")
(assume "f")
(use-with "BarThm" (pt "(Nil list nat)") "Thm" (pt "f") (pt "0") "?")
;; (f fbar 0)=(Nil list nat)
(ng #t)
(use "Truth")
;; Proof finished.
(save "HigmanThm")

(define eterm (proof-to-extracted-term (theorem-name-to-proof "HigmanThm")))
(pp eterm)
;; [f]cBarThm cThm f 0


(animate "BarThm")
(animate "Thm")
(animate "Prop1")
(animate "Prop2")
(animate "Prop3")

(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [f]
;;  (Rec algBar=>(nat=>list nat)=>nat=>nat)
;;  ((Rec list nat=>algBar)(f 0)(CBranch([w]CLeaf))
;;   ([a,w,algBar]
;;     (Rec algBar=>list list nat=>algBar)algBar([ws]CLeaf)
;;     ([ga,gc,ws]
;;       CBranch
;;       ([w0]
;;         (Rec list nat=>algBar)w0(CBranch([w1]CLeaf))
;;         ([a0,w1,algBar0]
;;           [if (a0=a)
;;             (gc w1(ws++(a0::w1):))
;;             ((Rec algBar=>list list nat=>nat=>nat=>algBar)algBar0
;;             ([ws0,a1,a2]CLeaf)
;;             ([ga0,ge,ws0,a1,a2]
;;               CBranch
;;               ([w2]
;;                 [if w2
;;                   (CBranch([w3]CLeaf))
;;                   ([a3,w3]
;;                    [if (a3=a1)
;;                      ((Rec algBar=>algBar=>list list nat=>nat=>nat=>algBar)
;;                      (ga w3)
;;                      ([algBar1,ws1,a4,a5]CLeaf)
;;                      ([ga1,gd,algBar1]
;;                        (Rec algBar=>list list nat=>nat=>nat=>algBar)algBar1
;;                        ([ws1,a4,a5]CLeaf)
;;                        ([ga2,ge0,ws1,a4,a5]
;;                          CBranch
;;                          ([w4]
;;                            [if w4
;;                              (CBranch([w5]CLeaf))
;;                              ([a6,w5]
;;                               [if (a6=a4)
;;                                 (gd w5(CBranch ga2)(ws1++(a4::w5):)a4 a5)
;;                                 (ge0 w5(ws1++(a6::w5):)a4 a6)])])))
;;                      (CBranch ga0)
;;                      (ws0++(a1::w3):)
;;                      a1 
;;                      a2)
;;                      (ge w3(ws0++(a3::w3):)a1 a3)])]))
;;             (ws++(a0::w1):)
;;             a 
;;             a0)])))
;;     (a::w):))
;;  ([f0,a]a)
;;  ([ga,gb,f0,a]gb(f0 a)f0(Succ a))
;;  f 
;;  1

;; 3. Test of the extracted term
;; =============================

(define (run-higman infinite-sequence)
  (pp (nt (mk-term-in-app-form neterm infinite-sequence))))

;; a. [0 0], [1 1 0], [0 1 0 1], [0], ...
(add-program-constant "Seq" (mk-arrow (py "nat") (py "(list nat)")))
(add-rewrite-rule (pt "Seq 0") (pt "0::0:"))
(add-rewrite-rule (pt "Seq 1") (pt "1::1::0:"))
(add-rewrite-rule (pt "Seq 2") (pt "0::1::0::1:"))
(add-rewrite-rule (pt "Seq(n+3)") (pt "0:"))
(run-higman (pt "Seq"))

;; ==> 3
;; i.e., the subsequence of consisting of the first three words is good.

;; b. [0 0], [1], [0 1], [], [], ...

(add-program-constant "Interesting" (mk-arrow (py "nat") (py "(list nat)")))
(add-rewrite-rule (pt "Interesting 0") (pt "0::0:"))
(add-rewrite-rule (pt "Interesting 1") (pt "1:"))
(add-rewrite-rule (pt "Interesting 2") (pt "0::1:"))
(add-rewrite-rule (pt "Interesting 3") (pt "(Nil nat)"))
(add-rewrite-rule (pt "Interesting(n+4)") (pt "(Nil nat)"))
(run-higman (pt "Interesting"))

;; ==> 5  
;; This is an example in which not the shortest good initial segment is found.
