;; 2014-10-11.  ratsds.scm

;; (load "~/git/minlog/init.scm") ;correct path to minlog if necessary.

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(libload "numbers.scm")
(libload "simpreal.scm")
(libload "real.scm")
(set! COMMENT-FLAG #t)

(add-rewrite-rule "a-b+b" "a")
(add-rewrite-rule "a+2*b" "a+b+b")

;; NegOrPos
(set-goal "all a(a<=0 ori 0<=a)")
(cases)
(cases)
(assume "p0" "p1")
(intro 1)
(use "Truth")
(assume "p0")
(intro 0)
(use "Truth")
(assume "p0" "p1")
(intro 0)
(use "Truth")
;; Proof finished.
(save "NegOrPos")

;; SplitAtRational
(set-goal "all a,b(a<=b ori b<=a)")
(assume "a" "b")
(assert "a-b<=0 ori 0<=a-b")
 (use "NegOrPos")
(assume "NegOrPos inst")
(elim "NegOrPos inst")
(drop "NegOrPos inst")
(assume "Hneg")
(intro 0)
(assert "(a-b)+b<=0+b")
 (use "RatLeMonPlus")
 (use "Hneg")
 (use "Truth")
(assume "H0")
(use "H0")
(assume "Hpos")
(intro 1)
(assert "0+b<=(a-b)+b")
 (use "RatLeMonPlus")
 (use "Hpos")
 (use "Truth")
(assume "H0")
(use "H0")
;; Proof finished.
(save "SplitAtRational")

(add-alg "intv" '("CInt" "intv") '("CIntN" "intv=>intv")
         '("CIntZ" "intv=>intv") '("CIntP" "intv=>intv"))

(add-ids (list (list "Q" (make-arity (py "rat")) "algQ"))
	 '("all a(IntN 1<=a andi a<=1 -> Q a)" "GenQ"))

(add-ids (list (list "I" (make-arity (py "rat")) "intv"))
	 '("I(0#1)" "InitI")
	 '("allnc a^(I a^ -> I((a^ -1)/2))" "GenIP")
	 '("allnc a^(I a^ -> I(a^ /2))" "GenIZ")
	 '("allnc a^(I a^ -> I((a^ +1)/2))" "GenIP"))

(add-co "I")
(pp (rename-variables (aconst-to-formula
		       (theorem-name-to-aconst "CoIClause"))))

;; allnc a^(
;;  CoI a^ -> 
;;  a^ eqd 0 orr 
;;  exr a^0(CoI a^0 andl a^ eqd(a^0-1)/2) ord 
;;  exr a^0(CoI a^0 andl a^ eqd a^0/2) ord 
;;  exr a^0(CoI a^0 andl a^ eqd(a^0+1)/2))

;; "LemmaA"
(set-goal "allnc a^(Q a^ -> CoI a^)")
(assume "a^0")
(coind)
;; ?_3:allnc a^(
;;      Q a^ -> 
;;      a^ eqd 0 orr 
;;      exr a^0((CoI a^0 ord Q a^0) andl a^ eqd(a^0-1)/2) ord 
;;      exr a^0((CoI a^0 ord Q a^0) andl a^ eqd a^0/2) ord 
;;      exr a^0((CoI a^0 ord Q a^0) andl a^ eqd(a^0+1)/2))

;; (cdp) ;ok

(assume "a^")
(elim)
(assume "a" "a in [-1,1]")
(elim "a in [-1,1]")
(drop "a in [-1,1]")
(assume "IntN 1<=a" "a<=1")
(assert "a<=(IntN 1#3) ori (IntN 1#3)<=a")
 (use "SplitAtRational")
(assume "a<=(IntN 1#3) oru (IntN 1#3)<=a")
(elim "a<=(IntN 1#3) oru (IntN 1#3)<=a")
(drop "a<=(IntN 1#3) oru (IntN 1#3)<=a")
(assume "a<=(IntN 1#3)")

;; Case "a<=(IntN 1#3)"
(intro 1)
(intro 0)
(intro 0 (pt "2*a+1"))
(split)

(intro 1)
(intro 0)
(intro 0)
(ord-field-simp-bwd)
(use-with "RatLeMonPlus"
	  (pt "1#1") (pt "1#1") (pt "IntN 1#1") (pt "a")
	  "Truth" "IntN 1<=a")
(ord-field-simp-bwd)
(use "RatLeTrans" (pt "IntN 1#3"))
(use "a<=(IntN 1#3)")
(use "Truth")
(ord-field-simp-bwd)
(drop "a<=(IntN 1#3) oru (IntN 1#3)<=a")
(assume "(IntN 1#3)<=a")

;; Case "(IntN 1#3)<=a"
(assert "a<=(1#3) ori (1#3)<=a")
 (use "SplitAtRational")
(assume "a<=(1#3) oru (1#3)<=a")
(elim "a<=(1#3) oru (1#3)<=a")
(drop "a<=(1#3) oru (1#3)<=a")
(assume "a<=(1#3)")

;; Subcase "a<=(1#3)"
(intro 1)
(intro 1)
(intro 0)
(intro 0 (pt "a+a"))
(split)
(intro 1)
(intro 0)
(intro 0)
(assert "(IntN 1#3)+(IntN 1#3)<=a+a")
 (use-with "RatLeMonPlus"
	   (pt "(IntN 1#3)") (pt "a") (pt "(IntN 1#3)") (pt "a")
	   "(IntN 1#3)<=a" "(IntN 1#3)<=a")
(assume "(IntN 1#3)+(IntN 1#3)<=a+a")
(ord-field-simp-bwd)
(assert "1+(IntN 2#3)<=1+a+a")
 (use-with "RatLeMonPlus"
	   (pt "1#1") (pt "1#1") (pt "(IntN 2#3)") (pt "a+a")
	   "Truth" "(IntN 1#3)+(IntN 1#3)<=a+a")
(assume "1+(IntN 2#3)<=1+a+a")
(use "RatLeTrans" (pt "1+(IntN 2#3)"))
(use "Truth")
(use "1+(IntN 2#3)<=1+a+a")
(use "RatLeTrans" (pt "(1#3)+(1#3)"))
(use "RatLeMonPlus")
(use "a<=(1#3)")
(use "a<=(1#3)")
(use "Truth")
(ord-field-simp-bwd)
(drop "a<=(1#3) oru (1#3)<=a")
(assume "(1#3)<=a")

;; Subcase "(1#3)<=a"
(intro 1)
(intro 1)
(intro 1)
(intro 0 (pt "2*a-1"))
(split)
(intro 1)
(intro 0)
(intro 0)
(ord-field-simp-bwd)
(use "RatLeTrans" (pt "(1#3)"))
(use "Truth")
(use "(1#3)<=a")
(ord-field-simp-bwd)
(use "a<=1")
(ord-field-simp-bwd)
;; Proof finished.
(save "LemmaA")

(define eterm (proof-to-extracted-term (theorem-name-to-proof "LemmaA")))
;; (pp eterm)
(animate "SplitAtRational")
(animate "NegOrPos")

(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [algQ]
;;  (CoRec algQ=>intv)algQ
;;  ([algQ0]
;;    [if algQ0
;;      ([a]
;;       [if (a-(IntN 1#3))
;;         ([k,p]
;;          [if k
;;            ([p0]
;;             [if (a-(1#3))
;;               ([k0,p1]
;;                [if k0
;;                  ([p2]
;;                   Inr((InR ((intv ysum algQ)ysum intv ysum algQ)
;; 			   (intv ysum algQ))
;;                       ((InR (intv ysum algQ) (intv ysum algQ))
;;                        ((InR algQ intv)(CGenQ(2*a-1))))))
;;                  (Inr((InR ((intv ysum algQ)ysum intv ysum algQ)
;; 			   (intv ysum algQ))
;;                      ((InL (intv ysum algQ) (intv ysum algQ))
;;                       ((InR algQ intv)(CGenQ(a+a))))))
;;                  ([p2]
;;                   Inr((InR ((intv ysum algQ)ysum intv ysum algQ)
;; 			   (intv ysum algQ))
;;                       ((InL (intv ysum algQ) (intv ysum algQ))
;;                        ((InR algQ intv)(CGenQ(a+a))))))])])
;;            (Inr((InL (intv ysum algQ) ((intv ysum algQ)ysum intv ysum algQ))
;;                ((InR algQ intv)(CGenQ(2*a+1)))))
;;            ([p0]
;;             Inr((InL (intv ysum algQ) ((intv ysum algQ)ysum intv ysum algQ))
;;                 ((InR algQ intv)(CGenQ(2*a+1)))))])])])

(define bcorecterm (undelay-delayed-corec neterm 1))
;; (pp (rename-variables bcorecterm))

(pp (nt (undelay-delayed-corec
         (make-term-in-app-form neterm (pt "CGenQ 0")) 5)))

;; CIntZ
;; (CIntZ
;;  (CIntZ
;;   (CIntZ
;;    (CIntZ
;;     ((CoRec algQ=>intv)(CGenQ 0) ...)))))

(pp (nt (undelay-delayed-corec
	 (make-term-in-app-form neterm (pt "CGenQ 1")) 5)))
;; CIntP CIntP CIntP ...

(pp (nt (undelay-delayed-corec
	 (make-term-in-app-form neterm (pt "CGenQ IntN 1")) 5)))
;; CIntN CIntN CIntN ...

(pp (nt (undelay-delayed-corec
	 (make-term-in-app-form neterm (pt "CGenQ(1#2)")) 5)))
;; CIntP CIntZ CIntZ CIntZ ...

(pp (nt (undelay-delayed-corec
	 (make-term-in-app-form neterm (pt "CGenQ(IntN 1#2)")) 5)))
;; CIntN CIntZ CIntZ CIntZ ...

;; approximated pi.
(pp (nt (undelay-delayed-corec
	 (make-term-in-app-form neterm (pt "CGenQ((22#7)/4)")) 10)))

;; CIntP
;; (CIntP
;;  (CIntZ
;;   (CIntZ
;;    (CIntP
;;     (CIntZ
;;      (CIntZ
;;       (CIntP
;;        (CIntZ
;;         (CIntZ
;;          ((CoRec algQ=>intv)(CGenQ(4#7)) ...))))))))))
