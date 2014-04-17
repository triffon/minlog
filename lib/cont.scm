;; $Id: cont.scm 2649 2013-09-16 07:39:44Z schwicht $

;; (load "~/git/minlog/init.scm")

;; (set! COMMENT-FLAG #f)
;; (libload "nat.scm")
;; (libload "numbers.scm")
;; (libload "simpreal.scm")
;; (exload "analysis/real.scm")
;; (set! COMMENT-FLAG #t)

(if (not (member "lib/real.scm" LOADED-FILES))
    (myerror "First load lib/real.scm"))

(display "loading cont.scm ...") (newline)

;; Continuous functions
;; ====================

;; 2004-01-24
;; Algebraic structures (`hierarchy') versus concrete algebras.

;; To develop general group theory, take a type variable alpha (the
;; type of the group elements) and a predicate variable G of arity
;; alpha (the property to be an element of the group).  Take a binary
;; predicate variable == and formulate as its properties that it is an
;; equivalence relation on G.  Take a binary function variable o
;; (composition), a unary function variable inv (inverse) and a
;; variable e (unit), and formulate as their properties that G is
;; closed under them, compatibility with ==, and finally the ordinary
;; group axioms.  For equality reasoning we cannot use computation or
;; rewrite rules (there are no program constants), but must use simp
;; instead.  To apply general results for a concrete group, use proof
;; substitution.

;; For a concrete algebra (`record') the underlying data type is a
;; free algebra with one non-iterable constructor.  The destructors
;; are program constants and come with the obvious computation rules.
;; They should have informative names (`fields').  In a second step
;; the actual elements of the concrete algebra are singled out by
;; means of a (formally) inductively defined predicate, which in fact
;; is explicitly defined by the required properties of the field
;; components.

;; Example: continuous functions.

(add-alg
 "cont"
 (list "ContConstr" "rat=>rat=>(rat=>nat=>rat)=>(int=>nat)=>(int=>int)=>cont"))
(add-totality "cont")

(add-var-name "h" (py "rat=>nat=>rat"))
(add-var-name "al" (py "int=>nat"))
(add-var-name "om" (py "int=>int"))

(add-program-constant "ContDoml" (py "cont=>rat") t-deg-zero)
(add-postfix-display-string "ContDoml" "doml")

 
(add-computation-rules
 "(ContConstr a0 b0 h al om)doml" "a0")

(add-var-name "f" (make-alg "cont"))

;; ContDomlTotal
(set-goal (rename-variables (term-to-totality-formula (pt "ContDoml"))))
(assume "f^" "Tf")
(elim "Tf")
(assume "a^" "Ta" "b^" "Tb" "h^" "Th" "M^" "TM" "om^" "Tom")
(ng #t)
(use "Ta")
;; Proof finished.
(save "ContDomlTotal")

(add-program-constant "ContDomr" (py "cont=>rat") t-deg-zero)
(add-postfix-display-string "ContDomr" "domr")
 
(add-computation-rules
 "(ContConstr a0 b0 h al om)domr" "b0")

;; ContDomrTotal
(set-goal (rename-variables (term-to-totality-formula (pt "ContDomr"))))
(assume "f^" "Tf")
(elim "Tf")
(assume "a^" "Ta" "b^" "Tb" "h^" "Th" "M^" "TM" "om^" "Tom")
(ng #t)
(use "Tb")
;; Proof finished.
(save "ContDomrTotal")

(add-program-constant
 "ContApprox" (py "cont=>rat=>nat=>rat") t-deg-zero 'const 1)
(add-postfix-display-string "ContApprox" "approx")

(add-computation-rules
 "(ContConstr a0 b0 h al om)approx" "h")

;; ContApproxTotal
(set-goal (rename-variables (term-to-totality-formula (pt "ContApprox"))))
(assume "f^" "Tf")
(elim "Tf")
(assume "a^" "Ta" "b^" "Tb" "h^" "Th" "M^" "TM" "om^" "Tom")
(ng #t)
(use "Th")
;; Proof finished.
(save "ContApproxTotal")

(add-program-constant "ContuMod" (py "cont=>int=>nat") t-deg-zero 'const 1)
(add-postfix-display-string "ContuMod" "uMod")

(add-computation-rules
 "(ContConstr a0 b0 h al om)uMod" "al")

;; ContuModTotal
(set-goal (rename-variables (term-to-totality-formula (pt "ContuMod"))))
(assume "f^" "Tf")
(elim "Tf")
(assume "a^" "Ta" "b^" "Tb" "h^" "Th" "M^" "TM" "om^" "Tom")
(ng #t)
(use "TM")
;; Proof finished.
(save "ContuModTotal")

(add-program-constant "ContuModCont" (py "cont=>int=>int") t-deg-zero 'const 1)
(add-postfix-display-string "ContuModCont" "uModCont")

(add-computation-rules
 "(ContConstr a0 b0 h al om)uModCont" "om")

;; ContuModContTotal
(set-goal (rename-variables (term-to-totality-formula (pt "ContuModCont"))))
(assume "f^" "Tf")
(elim "Tf")
(assume "a^" "Ta" "b^" "Tb" "h^" "Th" "M^" "TM" "om^" "Tom")
(ng #t)
(use "Tom")
;; Proof finished.
(save "ContuModContTotal")

;; Now the (formally inductive) definition of Cont

(add-ids
 (list (list "Cont" (make-arity (make-alg "cont"))))
 '("allnc a0,b0,h,al,om(
     all a(a0<=a -> a<=b0 -> Cauchy(h a)al) --> 
     all a,b,k,n(a0<=a -> a<=b0 -> a0<=b -> b<=b0 ->
                  al k<=n -> 
                  abs(a-b)<=1/2**(om k) ->
                  abs(h a n-h b n)<=1/2**k) -->
     all k,l(k<=l -> al k<=al l) -->
     all k,l(k<=l -> om k<=om l) -->
     Cont(ContConstr a0 b0 h al om))" "ContIntro"))

; Example of a continuous function: a^2-2 on [1,2]

(pp (nt (pt "(ContConstr 1 2([a,n]a*a-2)([k]Zero)([k]k+3))approx (14#10) 1")))

(pp
 (nt
  (simp-term
   (nt (pt "(ContConstr 1 2([a,n]a*a-2)([k]Zero)([k]k+3))approx (14#10) 1")))))

;; Now the properties of Cont.

;; ContElim1
(set-goal
 "all f(Cont f ->
        all a(f doml<=a -> a<=f domr -> Cauchy(f approx a)(f uMod)))")
(ind)
(assume "a0" "b0" "h" "al" "om")
(elim)
(search)
;; Proof finished.
(save "ContElim1")

;; ContElim2
(set-goal "all f(
 Cont f -> 
 all a,b,k,n(
  f doml<=a -> 
  a<=f domr -> 
  f doml<=b -> 
  b<=f domr -> 
  f uMod k<=n -> 
  abs(a-b)<=1/2**f uModCont k -> abs(f approx a n-f approx b n)<=1/2**k))")
(ind)
(assume "a0" "b0" "h" "al" "om")
(elim)
(search)
;; Proof finished.
(save "ContElim2")

;; ContElim3
(set-goal "all f(Cont f -> all k,l(k<=l -> f uMod k<=f uMod l))")
(ind)
(assume "a0" "b0" "h" "al" "om")
(elim)
(search)
;; Proof finished.
(save "ContElim3")

;; ContElim4
(set-goal "all f(Cont f -> all k,l(k<=l -> f uModCont k<=f uModCont l))")
(ind)
(assume "a0" "b0" "h" "al" "om")
(elim)
(search)
;; Proof finished.
(save "ContElim4")

;; All this could be done automatically by evaluating

;; (add-record
;;  "Cont" "f"
;;  (list "doml" "rat")
;;  (list "domr" "rat")
;;  (list "approx" "rat=>nat=>rat")
;;  (list "uMod" "pos=>pos")
;;  (list "uModCont" "pos=>pos")
;;  "all a(f doml<=a -> a<=f domr -> Cauchy(f approx a)(f uMod))"
;;  "all a,b,k,n(f doml<=a -> a<=f domr -> f doml<=b -> b<=f domr ->
;;               f uMod k<=n -> 
;;               abs(a-b)<=(1#2**(f uModCont k)) ->
;;               abs(f approx a n-f approx b n)<=1/2**k))"
;;  "all m,n(m<=n -> f uMod m<=f uMod n)"
;;  "all m,n(m<=n -> f uModCont m<=f uModCont n)")

;; However, for the time being it is done by hand.

;; Recall the intermediate value theorem, now written as follows:

;; (pf "all f,M(Cont f -> f app f doml<=0 -> 0<=f app f domr ->
;;      all x,y,k(RealLt x y k -> RealLt(f app x)(f app y)(M k)) -> 
;;      ex z(Real z & f app z===0))")

;; We aim at an application notation: (f x) instead of (f app x), so

;; For an application notation (f x) we must from (x seq) and (x mod)
;; produce the real whose Cauchy sequence is [n]f approx(x seq n)n and
;; whose modulus is \max(\alpha_f(k+2), \alpha(\omega_f(k+1)-1)) or
;; formally [k]f uMod(IntS(IntS k))max x mod(IntPred(f uModCont(IntS k)))

;; (pp (pt "[n]f approx(x seq n)n"))
;; (pp (pt "[k]f uMod(k+2)max x mod(f uModCont(k+1)-1)"))

;; 2013-05-08.  add-application used (instead of add-new-application)

(add-program-constant "AppContOne" (py "cont=>rea=>rea") t-deg-zero)

;; (add-computation-rule
;;  "AppContOne(ContConstr a0 b0 h al om)(RealConstr as M)"
;;  "RealConstr([n]h(as n)n)([k](al(k+2))max(M(om(k+1)-1)))")

;; (set-goal (rename-variables (term-to-totality-formula (pt "AppContOne"))))
;; (assume "f^" "Tf")
;; (elim "Tf")
;; (assume "a^" "Ta" "b^" "Tb" "h^" "Th" "al^" "Tal" "om^" "Tom" "x^" "Tx")
;; (elim "Tx")
;; (assume "as^" "Tas" "M^" "TM")
;; (ng #t)
;; (use "TotalReaRealConstr")
;; (ng #t)
;; (assume "n^" "Tn")
;; (use "Th")
;; (use "Tas")
;; (use "Tn")
;; (use "Tn")
;; (assume "k^" "Tk")
;; (ng #t)
;; (use "NatMaxTotal")
;; (use "Tal")
;; (use "IntSTotal")
;; (use "IntSTotal")
;; (use "Tk")
;; (use "TM")
;; (use "IntMinusTotal")
;; (use "Tom")
;; (use "IntSTotal")
;; (use "Tk")
;; (use "TotalIntIntPos")
;; (use "TotalPosOne")
;; ;; Proof finished.
;; (save "AppContOneTotal")

(add-computation-rule
 "AppContOne f x"
 "RealConstr([n]f approx(x seq n)n)
            ([k]f uMod(IntS(IntS k))max x mod(IntPred(f uModCont(IntS k))))")

(set-goal (rename-variables (term-to-totality-formula (pt "AppContOne"))))
(assume "f^" "Tf")
(elim "Tf")
(assume "a^" "Ta" "b^" "Tb" "h^" "Th" "al^" "Tal" "om^" "Tom" "x^" "Tx")
(elim "Tx")
(assume "as^" "Tas" "M^" "TM")
(ng #t)
(use "TotalReaRealConstr")
(ng #t)
(assume "n^" "Tn")
(use "Th")
(use "Tas")
(use "Tn")
(use "Tn")
(assume "k^" "Tk")
(ng #t)
(use "NatMaxTotal")
(use "Tal")
(use "IntSTotal")
(use "IntSTotal")
(use "Tk")
(use "TM")
(use "IntPredTotal")
(use "Tom")
(use "IntSTotal")
(use "Tk")
;; Proof finished.
(save "AppContOneTotal")

(add-application (pt "AppContOne"))

;; ;; AppContRealConstr
;; (set-goal "all f,as,M f(RealConstr as M) eqd
;;   RealConstr([n]f approx(as n)n)([k]f uMod(k+2)max M(f uModCont(k+1)-1))")
;; (ind)
;; (ng #t)
;; (strip)
;; (use "InitEqD")
;; ;; Proof finished.
;; (save "AppContRealConstr")

;; (define (make-term-in-cont-app-form f x)
;;   (let ((n (type-to-new-var (py "nat")))
;; 	(k (type-to-new-var (py "int"))))
;;     (mk-term-in-app-form
;;      (make-term-in-const-form (constr-name-to-constr "RealConstr"))
;;      (make-term-in-abst-form
;;       n (mk-term-in-app-form
;; 	 (make-term-in-const-form (pconst-name-to-pconst "ContApprox"))
;; 	 f (mk-term-in-app-form
;; 	    (make-term-in-const-form (pconst-name-to-pconst "RealSeq"))
;; 	    x (make-term-in-var-form n))
;; 	 (make-term-in-var-form n)))
;;      (make-term-in-abst-form
;;       k (mk-term-in-app-form
;; 	 (make-term-in-const-form
;; 	  (pconst-name-to-pconst "NatMax"))
;; 	 (mk-term-in-app-form
;; 	  (make-term-in-const-form (pconst-name-to-pconst "ContuMod"))
;; 	  f (make-term-in-app-form
;; 	     (make-term-in-const-form (pconst-name-to-pconst "IntS"))
;; 	     (make-term-in-app-form
;; 	      (make-term-in-const-form (pconst-name-to-pconst "IntS"))
;; 	      (make-term-in-var-form k))))
;; 	 (mk-term-in-app-form
;; 	  (make-term-in-const-form (pconst-name-to-pconst "RealMod"))
;; 	  x (mk-term-in-app-form
;; 	     (make-term-in-const-form (pconst-name-to-pconst "IntPred"))
;; 	     (mk-term-in-app-form
;; 	      (make-term-in-const-form (pconst-name-to-pconst "ContuModCont"))
;; 	      f (make-term-in-app-form
;; 		 (make-term-in-const-form (pconst-name-to-pconst "IntS"))
;; 		 (make-term-in-var-form k))))))))))

;; (pp (nt (make-term-in-cont-app-form (pt "f") (pt "x"))))

;; (add-new-application
;;  (lambda (type) (equal? type (make-alg "cont")))
;;  make-term-in-cont-app-form)

;; A term is in cont-app-form if it is in application form with
;; operator RealConstr, with seq field of the form [n]f approx(x seq
;; n)n.  It should then be displayed as f x, where f and x can be read
;; off.

;; (define (term-in-cont-app-form? term)
;;   (and
;;    (term-in-app-form? term)
;;    (let ((op (term-in-app-form-to-final-op term))
;; 	 (args (term-in-app-form-to-args term)))
;;      (and
;;       (term-in-const-form? op)
;;       (string=? "RealConstr" (const-to-name (term-in-const-form-to-const op)))
;;       (= 2 (length args))
;;       (equal? (py "int=>nat") (term-to-type (cadr args)))
;;       (term-in-abst-form? (car args))
;;       (let* ((var (term-in-abst-form-to-var (car args)))
;; 	     (kernel (term-in-abst-form-to-kernel (car args)))
;; 	     (op1 (term-in-app-form-to-final-op kernel))
;; 	     (args1 (term-in-app-form-to-args kernel)))
;; 	(and
;; 	 (term-in-const-form? op1)
;; 	 (string=? "ContApprox"
;; 		   (const-to-name (term-in-const-form-to-const op1)))
;; 	 (= 3 (length args1))
;; 	 (let ((arg1 (car args1)) ;this is f
;; 	       (arg2 (cadr args1)) ;this is x seq n
;; 	       (arg3 (caddr args1))) ;this is n
;; 	   (and
;; 	    (term-in-var-form? arg3)
;; 	    (equal? var (term-in-var-form-to-var arg3))
;; 	    (let ((op2 (term-in-app-form-to-final-op arg2))
;; 		  (args2 (term-in-app-form-to-args arg2)))
;; 	      (and
;; 	       (term-in-const-form? op2)
;; 	       (string=? "RealSeq"
;; 			 (const-to-name (term-in-const-form-to-const op2)))
;; 	       (= 2 (length args2))
;; 	       (let ((arg21 (car args2)) ;this is x
;; 		     (arg22 (cadr args2))) ;this is n
;; 		 (and
;; 		  (term-in-var-form? arg22)
;; 		  (equal? var (term-in-var-form-to-var arg22))))))))))))))

;; (term-in-cont-app-form? (make-term-in-cont-app-form (pt "f") (pt "x")))

;; (define (term-in-cont-app-form-to-op term)
;;   (let* ((args (term-in-app-form-to-args term))
;; 	 (kernel (term-in-abst-form-to-kernel (car args)))
;; 	 (args1 (term-in-app-form-to-args kernel)))
;;     (car args1)))

;; (define (term-in-cont-app-form-to-arg term)
;;   (let* ((args (term-in-app-form-to-args term))
;; 	 (kernel (term-in-abst-form-to-kernel (car args)))
;; 	 (args1 (term-in-app-form-to-args kernel))
;; 	 (arg2 (cadr args1)) ;this is x seq n
;; 	 (args2 (term-in-app-form-to-args arg2)))
;;     (car args2)))

;; ;; (term-in-cont-app-form-to-op (make-term-in-cont-app-form (pt "f") (pt "x")))
;; ;; (term-in-cont-app-form-to-arg (make-term-in-cont-app-form (pt "f") (pt "x")))

;; (add-display
;;  (py "rea")
;;  (lambda (x)
;;    (if (term-in-cont-app-form? x)
;;        (list 'appterm ""
;; 	     (term-to-token-tree
;; 	      (term-in-cont-app-form-to-op x))
;; 	     (term-to-token-tree
;; 	      (term-to-original (term-in-cont-app-form-to-arg x))))
;;        #f)))

;; (pp (pt "f x"))
;; (pp (pt "(f x)mod"))
;; (pp (nt (pt "(f x)seq")))
;; (pp (nt (pt "(f x)mod")))

(add-global-assumption
 "ContReal"
 "all f,x(Cont f -> Real x -> f doml<<=x -> x<<=f domr -> Real(f x))")

(add-global-assumption
 "ContRealRat"
 "all f,c(Cont f -> f doml<<=c -> c<<=f domr -> Real(f c))")

;; Approximate splitting principle.

;; We will make use of some lemmata, that can be proved easily:

;; (add-global-assumption
;;  "RealLeCrit"
;;  "all x,y,n0(Real x -> Real y -> all n(n0<=n -> x seq n<=y seq n) -> x<<=y)")

;; For the proof we can use

(add-global-assumption
 "RealLeChar1"
 "all x,y(Real x -> Real y ->
          all k ex n0 all n(n0<=n -> 1/2**k<=y seq n-x seq n) ->
          x<<=y)")

;; (add-global-assumption
;;  "CauchyEstPlus"
;;  "all as,M(Cauchy as M ->
;;            all k,n,m(M k<=n -> M k<=m ->
;;                      as n<=as m+1/2**k))")

;; (add-global-assumption
;;  "CauchyEstMinus"
;;  "all as,M(Cauchy as M ->
;;            all k,n,m(M k<=n -> M k<=m ->
;;                      as n-1/2**k<=as m))")

;; (add-global-assumption
;;  "RatMinusLe2"
;;  "all a1,a2,b1,b2(a1<=a2 -> b2<=b1 -> a1-b1<=a2-b2)")

;; (add-global-assumption
;;  "RatLeLin"
;;  "all a,b((a<=b -> Pvar) -> (b<=a -> Pvar) -> Pvar)")

;; (add-var-name "L" (py "int=>nat"))

;; 2013-09-15.  ApproxSplit and its corollaries, together with the
;; used global assumptions, moved from here to real.scm.  However, here
;; we (still) use a formulation of ApproxSplit without disjunction.

;; ApproxSplitBoole
(set-goal "all x1,x2,x3,k(Real x1 -> Real x2 -> Real x3 ->
                    RealLt x1 x2 k -> ex boole(
                    (boole -> x3<<=x2) & ((boole -> F) -> x1<<=x3)))")
(assume "x1" "x2" "x3" "k" "Rx1" "Rx2" "Rx3" "x1<x2")
(assert "x3<<=x2 oru x1<<=x3")
 (use "ApproxSplit" (pt "k"))
 (use "Rx1")
 (use "Rx2")
 (use "Rx3")
 (use "x1<x2")
(assume "Disj")
(elim "Disj")
(drop "Disj")
(assume "x3<=x2")
(ex-intro (pt "True"))
(split)
(assume "Useless")
(use "x3<=x2")
(assume "Absurd")
(use "Efq")
(use "Absurd")
(use "Truth")
;; 11
(assume "x1<=x3")
(ex-intro (pt "False"))
(split)
(assume "Absurd")
(use "Efq")
(use "Absurd")
(assume "Useless")
(use "x1<=x3")
;; Proof finished.
(save "ApproxSplitBoole")

;; Intermediate value theorem, with 1/2^l a lower bound on the slope:

;; We first prove an auxiliary lemma IVTAux, for the construction step.

;; First we define a (formally inductive) correctness predicate:

(add-ids
 (list (list "Corr" (make-arity (py "cont") (py "rat") (py "rat") (py "int"))))
 '("allnc f,c,d,k(
     f doml<=c --> d<=f domr --> 1/2**k<=d-c -->
     f c<<=0 --> 0<<=f d -->
     Corr f c d k)" "CorrIntro"))

;; Now the properties of Corr.

(set-goal "all f,c,d,k(Corr f c d k -> f doml<=c)")
(assume "f" "c" "d" "k")
(elim)
(search)
(save "CorrElim1")

(set-goal "all f,c,d,k(Corr f c d k -> d<=f domr)")
(assume "f" "c" "d" "k")
(elim)
(search)
(save "CorrElim2")

(set-goal "all f,c,d,k(Corr f c d k -> 1/2**k<=d-c)")
(assume "f" "c" "d" "k")
(elim)
(search)
(save "CorrElim3")

(set-goal "all f,c,d,k(Corr f c d k -> f c<<=0)")
(assume "f" "c" "d" "k")
(elim)
(search)
(save "CorrElim4")

(set-goal "all f,c,d,k(Corr f c d k -> 0<<=f d)")
(assume "f" "c" "d" "k")
(elim)
(search)
(save "CorrElim5")

;; To unclutter the proof of IVTAux, we first prove two easy lemmata
;; concerning correctness.  First IVTAux1:

;; IVTAux1
(set-goal "all f,c,d,k(Cont f -> Corr f c d k -> 0<<=f((1#3)*c+(2#3)*d) ->
                       Corr f c((1#3)*c+(2#3)*d)(IntS k))")
(assume "f" "c" "d" "k" "Cont f" "Corr f c d k" "0<<=f d1")
(cut "f doml<=c")
(assume "a<=c")
(cut "d<=f domr")
(assume "d<=b")
(cut "1/2**k<=d-c")
(assume "c<_k d")
(cut "f c<<=0")
(assume "f c<<=0")
(cut "0<<=f d")
(assume "0<<=f d")

;; Corr f c((1#3)*c+(2#3)*d)(IntS k)
(use "CorrIntro")
(auto)

;; (1#3)*c+(2#3)*d<=f domr
(use "RatLeTrans" (pt "d"))

;; (1#3)*c+(2#3)*d<=d
(ord-field-simp-bwd)

;; c<=d
(use "RatLeAux1")
(use "RatLeTrans" (pt "1/2**k"))
(ord-field-simp-bwd)
(auto)

;; (1/2**(IntS k))<=(1#3)*c+(2#3)*d-c 
(add-global-assumption "RatLeTimes" "all a,b,c(0<=a -> b<=c -> a*b<=a*c)")
(add-global-assumption
 "RatLeTimes2" "all a,b,c,d(0<=a -> a<=b -> 0<=c -> c<=d -> a*c<=b*d)")
(use "RatEqvLe" (pt "(1/2)*(1/2**k)"))

(add-global-assumption
 "ExpTwoSuc" "all k(1/2**IntS k==1/2*(1/2**k))")
(use "ExpTwoSuc")

;; (1/2)*(1/2**k)<=(1#3)*c+(2#3)*d-c
(use "RatLeEq" (pt "(2#3)*(d-c)"))
(use "RatLeTimes2")
(use "Truth")
(use "Truth")
(ord-field-simp-bwd)
(auto)

;; (2#3)*(d-c)==(1#3)*c+(2#3)*d-c
(ord-field-simp-bwd)

;; f c<<=0
(use-with "CorrElim4" (pt "f") (pt "c") (pt "d") (pt "k") "Corr f c d k")
(auto)

;; 0<<=f d
(use-with "CorrElim5" (pt "f") (pt "c") (pt "d") (pt "k") "Corr f c d k")

;; f c<<=0
(use-with "CorrElim4" (pt "f") (pt "c") (pt "d") (pt "k") "Corr f c d k")

(use-with "CorrElim3" (pt "f") (pt "c") (pt "d") (pt "k") "Corr f c d k")
(use-with "CorrElim2" (pt "f") (pt "c") (pt "d") (pt "k") "Corr f c d k")
(use-with "CorrElim1" (pt "f") (pt "c") (pt "d") (pt "k") "Corr f c d k")
;; Proof finished.
(save "IVTAux1")

;; IVTAux2
(set-goal "all f,c,d,k(Cont f -> Corr f c d k -> f((2#3)*c+(1#3)*d)<<=0 ->
                       Corr f((2#3)*c+(1#3)*d)d(IntS k))")
(assume "f" "c" "d" "k" "Cont f" "Corr f c d k" "f c1<<=0")
(cut "f doml<=c")
(assume "a<=c")
(cut "d<=f domr")
(assume "d<=b")
(cut "(1/2**k)<=d-c")
(assume "c<_k d")
(cut "f c<<=0")
(assume "f c<<=0")
(cut "0<<=f d")
(assume "0<<=f d")

;; Corr f((2#3)*c+(1#3)*d)d(IntS k)
(use "CorrIntro")

;; f doml<=(2#3)*c+(1#3)*d
(use "RatLeTrans" (pt "c"))
(auto)

;; c<=(2#3)*c+(1#3)*d
(ord-field-simp-bwd)

;; c<=d
(use "RatLeAux1")
(use "RatLeTrans" (pt "1/2**k"))
(ord-field-simp-bwd)
(auto)

;; 1/2**(IntS k)<=d-((2#3)*c+(1#3)*d)
(use "RatEqvLe" (pt "(1/2)*(1/2**k)"))
(use "ExpTwoSuc")

;; (1/2)*(1/2**k)<=d-((2#3)*c+(1#3)*d)
(use "RatLeEq" (pt "(2#3)*(d-c)"))
(use "RatLeTimes2")
(auto)
(ord-field-simp-bwd)
(auto)

;; (2#3)*(d-c)==d-((2#3)*c+(1#3)*d)
(ord-field-simp-bwd)
(auto)

;; 0<<=f d
(use-with "CorrElim5" (pt "f") (pt "c") (pt "d") (pt "k") "Corr f c d k")

;; f c<<=0
(use-with "CorrElim4" (pt "f") (pt "c") (pt "d") (pt "k") "Corr f c d k")

(use-with "CorrElim3" (pt "f") (pt "c") (pt "d") (pt "k") "Corr f c d k")
(use-with "CorrElim2" (pt "f") (pt "c") (pt "d") (pt "k") "Corr f c d k")
(use-with "CorrElim1" (pt "f") (pt "c") (pt "d") (pt "k") "Corr f c d k")
;; Proof finished.
(save "IVTAux2")

;; Now we prove IVTAux

(add-var-name "cd" (make-star (py "rat") (py "rat")))

;; IVTAux
(set-goal "all f,l(
 Cont f -> 
 f f doml<<=0 -> 
 0<<=f f domr -> 
 all c,d,k(f doml<=c -> d<=f domr -> 1/2**k<=d-c -> RealLt(f c)(f d)(k+l)) -> 
 all k,cd(
  Corr f(left cd)(right cd)k -> 
  ex cd1(
   Corr f(left cd1)(right cd1)(IntS k) & 
   (left cd<=left cd1 & right cd1<=right cd & 
    right cd1-left cd1=(2#3)*(right cd-left cd)))))")
(assume "f" "l" "Cont f" "f a<<=0" "0<<=f b" "HypSlope" "k")
(assume "cd" "Corr f c d k")
(cut "f doml<=left cd")
(assume "a<=c")
(cut "right cd<=f domr")
(assume "d<=b")
(cut "left cd<=right cd")
(assume "c<=d")

(cut "ex cd0(left cd0=(2#3)*left cd+(1#3)*right cd &
             right cd0=(1#3)*left cd+(2#3)*right cd)")
(use "Id")
(assume "ExHyp")
(by-assume "ExHyp" "cd0" "cd0-Def")
(inst-with-to "cd0-Def" 'left "c0-Def")
(inst-with-to "cd0-Def" 'right "d0-Def")
(drop "cd0-Def")

(cut "ex boole((boole -> 0<<=f(right cd0)) &
               ((boole -> F) -> f(left cd0)<<=0))")
(assume "ExBooleHyp")
(by-assume "ExBooleHyp" "boole" "ExKernel")
(cases (pt "boole"))

;; Case 1
(assume "Left")
(cut "0<<=f(right cd0)")
(assume "0<<=f d0")
(ex-intro (pt "left cd@right cd0"))
(split)
(ng #t)

;; Corr f(left cd)(right cd0)(IntS k)
(simp "d0-Def")
(use "IVTAux1")
(auto)
(cut "0<<=RealConstr(f approx right cd0)([k1]f uMod(IntS(IntS k1)))")
(simp "d0-Def")

(ng #t)
(auto)

(split)
(use "Truth")
(split)

;; right(left cd@right cd0)<=right cd
(ng #t)
(simp "d0-Def")
(ord-field-simp-bwd)
(use "c<=d")

;; right(left cd@right cd0)-left(left cd@right cd0)=(2#3)*(right cd-left cd)
(ng #t)
(simp "d0-Def")
(ord-field-simp-bwd)
(search)

;; Case 2
(assume "Right")
(cut "f(left cd0)<<=0")
(assume "f c0<<=0")
(ex-intro (pt "left cd0@right cd"))
(split)
(ng #t)

;; Corr f(left cd0)(right cd)(IntS k)
(simp "c0-Def")
(use "IVTAux2")
(auto)
(cut "RealConstr(f approx left cd0)([k1]f uMod(IntS(IntS k1)))<<=0")
(simp "c0-Def")
(ng #t)
(auto)

(split)

;; left cd<=left(left cd0@right cd)
(ng #t)
(simp "c0-Def")
(ord-field-simp-bwd)
(auto)

(split)
(use "Truth")

;; right(left cd0@right cd)-left(left cd0@right cd)=(2#3)*(right cd-left cd)
(ng #t)
(simp "c0-Def")
(ord-field-simp-bwd)
(auto)

;; ex boole((boole -> 0<<=f(right cd0)) & ((boole -> F) -> f(left cd0)<<=0))
(cut "f doml<=left cd0")
(assume "a<=c0")
(cut "left cd0<=f domr")
(assume "c0<=b")
(cut "f doml<=right cd0")
(assume "a<=d0")
(cut "right cd0<=f domr")
(assume "d0<=b")

(use "ApproxSplitBoole" (pt "k+2+l"))

;; Real(f(left cd0))
(add-global-assumption
 "ContValsReal"
 "all f,x(Cont f -> Real x -> f doml<<=x -> x<<=f domr -> Real(f x))")
(add-global-assumption
 "ContRatValsReal"
 "all f,c(Cont f -> f doml<=c -> c<=f domr -> Real(f c))")
(use "ContRatValsReal")
(auto)

;; Real(f(right cd0))
(use "ContRatValsReal")
(auto)

;; Real(0)
(add-global-assumption "RatReal" "all a Real a")
(use "RatReal")

;; RealLt(f(left cd0))(f(right cd0))(k+2+l)
(use "HypSlope")
(auto)

;; (1/2**(k+2))<=right cd0-(left cd0)
(use "RatLeTrans" (pt "(right cd-left cd)*(1/2**2)"))

;; (1/2**(k+2))<=(right cd-left cd)*(1/2**2)
(add-global-assumption
 "IvtAuxAux2"
 "all k,a((1/2**k)<=a -> (1/2**(k+2))<=a*(1/2**2))")
(use "IvtAuxAux2")
(use "CorrElim3" (pt "f"))
(use "Corr f c d k")

;; (right cd-left cd)*(1/2**2)<=right cd0-left cd0
(simp "c0-Def")
(simp "d0-Def")
(ord-field-simp-bwd)
(ng #t)
(ord-field-simp-bwd)
(auto)

;; Now we need to prove the 4 estimates cut in earlier.

;; right cd0<=f domr
(use "RatLeTrans" (pt "right cd"))

;; right cd0<=right cd
(simp "d0-Def")
(ord-field-simp-bwd)
(auto)

;; f doml<=right cd0
(simp "d0-Def")
(use "RatLeTrans" (pt "left cd"))
(auto)

;; left cd<=(1#3)*left cd+(2#3)*right cd
(ord-field-simp-bwd)
(use "c<=d")

;; left cd0<=f domr
(use "RatLeTrans" (pt "right cd"))

;; left cd0<=right cd
(simp "c0-Def")
(ord-field-simp-bwd)
(auto)

;; f doml<=left cd0
(use "RatLeTrans" (pt "left cd"))
(auto)

;; left cd<=left cd0
(simp "c0-Def")
(ord-field-simp-bwd)
(use "c<=d")

;; ex cd0(left cd0=(2#3)*left cd+(1#3)*right cd &
;;        right cd0=(1#3)*left cd+(2#3)*right cd)
(ex-intro (pt "((2#3)*left cd+(1#3)*right cd)@((1#3)*left cd+(2#3)*right cd)"))
(prop)

;; left cd<=right cd
(use "RatLeAux1")
(use "RatLeTrans" (pt "1/2**k"))
(ord-field-simp-bwd)
(auto)
(use-with
 "CorrElim3" (pt "f") (pt "left cd") (pt "right cd") (pt "k") "Corr f c d k")

;; right cd<=f domr
(use-with
 "CorrElim2" (pt "f") (pt "left cd") (pt "right cd") (pt "k") "Corr f c d k")

;; f doml<=left cd
(use-with
 "CorrElim1" (pt "f") (pt "left cd") (pt "right cd") (pt "k") "Corr f c d k")
;; Proof finished.
(save "IVTAux")

(define IVTAux-eterm
  (proof-to-extracted-term (theorem-name-to-proof "IVTAux")))
(define IVTAux-neterm (rename-variables (nt IVTAux-eterm)))

(pp IVTAux-neterm)

;; [f,k,k0,cd]
;;  [let cd0
;;    ((2#3)*left cd+(1#3)*right cd@(1#3)*left cd+(2#3)*right cd)
;;    [if (cApproxSplitBoole
;;         (RealConstr(f approx left cd0)([k1]f uMod(IntS(IntS k1))))
;;         (RealConstr(f approx right cd0)([k1]f uMod(IntS(IntS k1))))
;;         0
;;         (IntS(IntS(k0+k))))
;;     (left cd@right cd0)
;;     (left cd0@right cd)]]

(pp (term-to-type IVTAux-neterm))
;; cont=>int=>int=>rat@@rat=>rat@@rat

;; We now want prove the existence of the sequence of cds.

;; It seems most direct to make use of the (valid) axiom of dependent choice:

(add-var-name "xx" "yy" (py "alpha"))
(add-var-name "xxs" (py "nat=>alpha"))
(add-pvar-name "RR" (make-arity (py "nat") (py "alpha")))
(add-pvar-name "SS" (make-arity (py "nat") (py "alpha") (py "alpha")))

;; For the moment we add DC as a global assumption, animated by the
;; appropriate recursion operator.  Later, it should be added as an
;; axiom.  For simplicity we choose a formulation of DC using a
;; predicate variable without computational content.

(add-global-assumption
 "DC"
 "all xx0(
 RR^ Zero xx0 -> 
 all n,xx(RR^ n xx -> ex yy(RR^(Succ n)yy & SS^ n xx yy)) -> 
 ex xxs(
  xxs Zero eqd xx0 & all n RR^ n(xxs n) & all n SS^ n(xxs n)(xxs(Succ n))))"
 3)

(define et-type (formula-to-et-type
		 (aconst-to-uninst-formula
		  (global-assumption-name-to-aconst "DC"))))

(pp et-type)
;; alpha=>(nat=>alpha=>alpha)=>nat=>alpha

(add-var-name "init" (py "alpha"))
(add-var-name "step" (py "nat=>alpha=>alpha"))

(add-computation-rules
 "(cDC alpha) init step Zero" "init"
 "(cDC alpha) init step(Succ n)" "step(Succ n)((cDC alpha) init step n)")

(display-pconst "cDC")

(add-var-name "cds" (py "nat=>rat@@rat"))

;; IVTcds
(set-goal "all f,l,k0(
 Cont f -> 
 f f doml<<=0 -> 
 0<<=f f domr -> 
 1/2**k0<=f domr-f doml -> 
 all c,d,k(f doml<=c -> d<=f domr -> 1/2**k<=d-c -> RealLt(f c)(f d)(k+l)) -> 
 ex cds(
  cds Zero eqd(f doml@f domr) & 
  all n Corr f(left(cds n))(right(cds n))(k0+n) & 
  all n(
   left(cds n)<=left(cds(Succ n)) & right(cds(Succ n))<=right(cds n) & 
   right(cds(Succ n))-left(cds(Succ n))=(2#3)*(right(cds n)-left(cds n)))))")
(assume "f" "l" "k0" "Cont f" "f a<<=0" "0<<=f b" "a <_k0 b" "HypSlope")

;;   f  l  k0  Cont f:Cont f
;;   f a<<=0:f f doml<<=0
;;   0<<=f b:0<<=f f domr
;;   a <_k0 b:1/2**k0<=f domr-f doml
;;   HypSlope:all c,d,k(f doml<=c -> d<=f domr -> 1/2**k<=d-c -> RealLt(f c)(f d)(k+l))
;; -----------------------------------------------------------------------------
;; ?_2:ex cds(
;;      cds Zero eqd(f doml@f domr) & 
;;      all n Corr f(left(cds n))(right(cds n))(k0+n) & 
;;      all n(
;;       left(cds n)<=left(cds(Succ n)) & 
;;       right(cds(Succ n))<=right(cds n) & 
;;       right(cds(Succ n))-left(cds(Succ n))=(2#3)*(right(cds n)-left(cds n))))

(cut "ex cds(
 cds Zero eqd(f doml@f domr) & 
 all n Corr f(left(cds n))(right(cds n))(k0+n) & 
 all n(
  left(cds n)<=left(cds(Succ n)) & right(cds(Succ n))<=right(cds n) & 
  right(cds(Succ n))-left(cds(Succ n))=(2#3)*(right(cds n)-left(cds n))))")
(assume "DCInst")
(by-assume "DCInst" "cds" "H")
(ex-intro (pt "cds"))
(search)

;; Now we prove the cut formula by instantiating DC
(use-with
 "DC"
 (py "rat@@rat")
 (make-cterm (pv "n") (pv "cd") (pf "Corr f(left cd)(right cd)(k0+n)"))
 (make-cterm (pv "n") (pv "cd") (pv "cd1")
	     (pf "left cd<=left cd1 & right cd1<=right cd &
                  right cd1-left cd1=(2#3)*(right cd-left cd)"))
 (pt "f doml@f domr") "?" "?")

;; Corr f(left(f doml@f domr))(right(f doml@f domr))(k0+Zero)
(use "CorrIntro")
(auto)

;; Now the step hypothesis, to be proved by means of IVTAux
(assume "n" "cd" "Corr-Hyp")

;;   f  l  k0  Cont f:Cont f
;;   f a<<=0:f f doml<<=0
;;   0<<=f b:0<<=f f domr
;;   a <_k0 b:1/2**k0<=f domr-f doml
;;   HypSlope:all c,d,k(f doml<=c -> d<=f domr -> 1/2**k<=d-c ->
;;                      RealLt(f c)(f d)(k+l))
;;   n  cd  Corr-Hyp:Corr f(left cd)(right cd)(k0+n)
;; -----------------------------------------------------------------------------
;; ?_17:ex cd0(
;;       Corr f(left cd0)(right cd0)(k0+Succ n) & 
;;       left cd<=left cd0 & 
;;       right cd0<=right cd & right cd0-left cd0=(2#3)*(right cd-left cd))

(use "IVTAux" (pt "l"))
(auto)
;; Proof finished.
(save "IVTcds")

(define IVTcds-eterm
  (proof-to-extracted-term (theorem-name-to-proof "IVTcds")))
(define IVTcds-neterm (rename-variables (nt IVTcds-eterm)))

(pp IVTcds-neterm)
;; [f,k,k0](cDC rat@@rat)(f doml@f domr)([n]cIVTAux f k(k0+n))

;; We now prove that [k]left(cds n+k) increases.

;; IVTLeftIncr
(set-goal "all f,l,k0(
 Cont f -> 
 f f doml<<=0 -> 
 0<<=f f domr -> 
 1/2**k0<=f domr-f doml -> 
 all c,d,k(f doml<=c -> d<=f domr -> 1/2**k<=d-c -> RealLt(f c)(f d)(k+l)) -> 
 all cds(
  cds Zero eqd(f doml@f domr) & 
  all n Corr f(left(cds n))(right(cds n))(k0+n) & 
  all n(
   left(cds n)<=left(cds(Succ n)) & right(cds(Succ n))<=right(cds n) & 
   right(cds(Succ n))-left(cds(Succ n))=(2#3)*(right(cds n)-left(cds n))) -> 
  all n,m left(cds n)<=left(cds(n+m))))")
(assume "f" "l" "k0" "Cont f" "f a<<=0" "0<<=f b" "a <_k0 b" "HypSlope"
	"cds" "Hcds" "n")
(ind)
(use "Truth")
(assume "m" "IH")
(use "RatLeTrans" (pt "left(cds(n+m))"))
(use "IH")
(use "Hcds")
;; Proof finished.
(save "IVTLeftIncr")

;; The corresponding proof of d(n+k)<=dn:

;; IVTRightDecr
(set-goal "all cds(
 all n right(cds(Succ n))<=right(cds n) -> 
 all n,m right(cds(n+m))<=right(cds n))")
(assume "cds" "Step" "n")
(ind)
(use "Truth")
(assume "m" "IH")
(use "RatLeTrans" (pt "right(cds(n+m))"))
(auto)
;; Proof finished.
(save "IVTRightDecr")

;; Now what we wanted to do:

;; IVTDiff
(set-goal "all f,cds(
 cds Zero eqd(f doml@f domr) -> 
 all n right(cds(Succ n))-left(cds(Succ n))=
       (2#3)*(right(cds n)-left(cds n)) -> 
 all n right(cds n)-left(cds n)=(2#3)**n*(f domr-f doml))")
(assume "f" "cds" "EqZero" "Step")
(ind)
  (simp "EqZero")
  (use "Truth")
(assume "n" "IH")
(simp "Step")
(simp "IH")
(ng #t)
(ord-field-simp-bwd)
;; Proof finished.
(save "IVTDiff")

;; Proof that (left(cds n)) is a Cauchy sequence with modulus 2*(n+k0)

;; We will need a general criterion for Cauchyness, in order to avoid
;; doing a symmetric argument twice, in a concrete case.  To be called
;; CauchyCrit.

(add-global-assumption "RatAbsSym" "all a,b(abs(a-b)==abs(b-a))")
(add-global-assumption "RatAbsNNeg" "all a(0<=a -> abs a==a)")
(add-global-assumption "RatAbsNPos" "all a,b(a<=b -> abs(a-b)==b-a)")

;; CauchyCrit
(set-goal "all as,M(all k,n,m(M k<=n -> n<=m -> abs(as n-as m)<=1/2**k) ->
                    Cauchy as M)")
(assume "as" "M" "Hyp")
(use "CauchyIntro")

;; all k,n,m(M k<=n -> M k<=m -> abs(as n-as m)<=1/2**k)
(assume "k" "n" "m" "M k<=n" "M k<=m")
(use "NatLeLin" (pt "n") (pt "m"))

;; n<=m -> abs(as n-as m)<=1/2**k
(assume "n<=m")
(auto)

;; m<=n -> abs(as n-as m)<=1/2**k
(assume "m<=n")
(use "RatEqvLe" (pt "abs(as m-as n)"))

;; abs(as n-as m)==abs(as m-as n)
(use "RatAbsSym")
(auto)
;; Proof finished.
(save "CauchyCrit")

;; For the Cauchy modulus we need

(add-program-constant "IntToNat" (py "int=>nat") t-deg-zero)

(add-computation-rules
 "IntToNat IntZero" "Zero"
 "IntToNat IntP pos" "PosToNat pos"
 "IntToNat IntN pos" "Zero")

(set-goal (rename-variables (term-to-totality-formula (pt "IntToNat"))))
(assume "k^" "Tk")
(elim "Tk") ;3-5
(assume "p^" "Tp")
(ng #t)
(elim "Tp")
(ng #t)
(use "TotalNatSucc")
(use "TotalNatZero")
(assume "q^" "Tq" "IHq")
(ng #t)
(use "NatDoubleTotal")
(use "IHq")
(assume "q^" "Tq" "IHq")
(ng #t)
(use "TotalNatSucc")
(use "NatDoubleTotal")
(use "IHq")
;; 4
(ng #t)
(use "TotalNatZero")
;; 5
(assume "p^" "Tp")
(ng #t)
(use "TotalNatZero")
;; Proof finished.
(save "IntToNatTotal")

(add-global-assumption
 "IntToNatMon"
 "all int1,int2(int1<=int2 -> IntToNat int1<=IntToNat int2)")

;; IVTRealLeft
(set-goal 
 "all a,b,k1(
 b-a<=2**k1 -> 
 all cds(
  all n,m(n<=m -> left(cds n)<=left(cds m)) -> 
  all n,m(n<=m -> right(cds m)<=right(cds n)) -> 
  all n left(cds n)<=right(cds n) -> 
  all n right(cds n)-left(cds n)=(2#3)**n*(b-a) -> 
  Real(RealConstr([n]left(cds n))([k]IntToNat(2*(k+k1))))))")
(assume "a" "b" "k1" "IntBound" "cds" "cIncr" "dDecr" "cs<=ds" "cdDiff")
(use "RealIntro")

;; Cauchyness
(use "CauchyCrit")
(ng #t)

;; all k,n,m(
;;   abs(2*(k+k1))<=n -> n<=m -> abs(left(cds n)-left(cds m))<=1/2**k)
(assume "k" "n" "m" "Mk<=n" "n<=m")

;; abs(left(cds n)-left(cds m))<=1/2**k
(use "RatEqvLe" (pt "left(cds m)-left(cds n)"))

;; abs(left(cds n)-left(cds m))==left(cds m)-left(cds n)
(use "RatAbsNPos")
(auto)

;; left(cds m)-left(cds n)<=1/2**k
(use "RatLeTrans" (pt "right(cds m)-left(cds n)"))

;; left(cds m)-left(cds n)<=right(cds m)-left(cds n)
(use "RatMinusLe2")
(auto)

;; right(cds m)-left(cds n)<=1/2**k
(use "RatLeTrans" (pt "right(cds n)-left(cds n)"))

;; right(cds m)-left(cds n)<=right(cds n)-left(cds n)
(use "RatMinusLe2")
(auto)

;; right(cds n)-left(cds n)<=1/2**k
(inst-with-to "cdDiff" (pt "n") "cdDiffn")
(add-global-assumption
 "IVTRealAux1"
 "all a,b,c,d,n,k,k1(b-a<=2**k1 -> IntToNat(2*(k+k1))<=n -> 
                         d-c=(2#3)**n*(b-a) ->
                         d-c<=1/2**k)")
;; Proof: d-c =  (2#3)**n*(b-a)
;;            <= (2#3)**n*2**k1
;;            <= (2#3)**(2*(k+k1))*2**k1
;;            <= (2**3)**k* (2**3)*k1 / (3**2)**k* (3**2)*k1 *(1/2**k)
;;            =  exp(1/2)k
(use "IVTRealAux1" (pt "a") (pt "b") (pt "n") (pt "k1"))
(auto)

;; Mon((RealConstr([n]left(cds n))([k]IntToNat(2*(k+k1))))mod)
(ng #t)

;; Mon([k2]IntToNat(2*(k2+k1)))
(use "MonIntro")
(ng #t)
(assume "k" "l" "k<=l")
(use "IntToNatMon")
(ord-field-simp-bwd)
(use "k<=l")
;; Proof finished.
(save "IVTRealLeft")

;; The final goal, split into parts:

;; IVTFinalRealLeft
(set-goal 
 "all f,l,k0,k1(
 Cont f -> 
 f f doml<<=0 -> 
 0<<=f f domr -> 
 1/2**k0<=f domr-f doml -> 
 f domr-f doml<=2**k1 -> 
 all c,d,k(f doml<=c -> d<=f domr -> 1/2**k<=d-c -> RealLt(f c)(f d)(k+l)) -> 
 all cds(
  cds Zero eqd(f doml@f domr) -> 
  all n Corr f(left(cds n))(right(cds n))(k0+n) -> 
  all n left(cds n)<=left(cds(Succ n)) -> 
  all n right(cds(Succ n))<=right(cds n) -> 
  all n 
   right(cds(Succ n))-left(cds(Succ n))=(2#3)*(right(cds n)-left(cds n)) -> 
  Real(RealConstr([n]left(cds n))([k]IntToNat(2*(k+k1))))))")
(assume "f" "l" "k0" "k1" "Cont f" "f a<<=0" "0<<=f b"
	"a <_k0 b" "b-a<=2**k1" "HypSlope" 
        "cds" "cdsProp1" "cdsProp2" "cdsProp3" "cdsProp4" "cdsProp5")
(use "IVTRealLeft" (pt "f doml") (pt "f domr"))
(use "b-a<=2**k1")

;; ?_4: all n,m(n<=m -> left(cds n)<=left(cds m))
(add-global-assumption
 "IVTFinalAux1"
 "all cs(all n cs n<=cs(Succ n) -> all n,m(n<=m -> cs n<=cs m))")
(assume "n" "m" "n<=m")
(use-with "IVTFinalAux1" (pt "[n]left(cds n)") "?" (pt "n") (pt "m") "n<=m")
(ng #t)
(use "cdsProp3")

;; ?_5: all n,m(n<=m -> right(cds m)<=right(cds n))
(add-global-assumption
 "IVTFinalAux2"
 "all ds(all n ds(Succ n)<=ds n -> all n,m(n<=m -> ds m<=ds n))")
(assume "n" "m" "n<=m")
(use-with "IVTFinalAux2" (pt "[n]right(cds n)") "?" (pt "n") (pt "m") "n<=m")
(ng #t)
(use "cdsProp4")

;; ?_6: all n left(cds n)<=right(cds n)
(add-global-assumption
 "IVTFinalAux3"
 "all f,c,d,k(Corr f c d k -> c<=d)")
(assume "n")
(cut "Corr f(left(cds n))(right(cds n))(k0+n)")
(assume "CorrHyp")
(use-with "IVTFinalAux3" (pt "f") (pt "(left(cds n))") (pt "right(cds n)")
	  (pt "k0+n") "CorrHyp")
(use "cdsProp2")

;; ?_7: all n (2#3)*(right(cds n)-left(cds n))=(2#3)**n*(f domr-f doml)
;; Here we need IVTDiff (pp "IVTDiff")
(use "IVTDiff")
(use "cdsProp1")
(use "cdsProp5")
;; Proof finished.
(save "IVTFinalRealLeft")

;; IVTRealAppLeft
(set-goal 
 "all f,l,k0,k1(
 Cont f -> 
 f f doml<<=0 -> 
 0<<=f f domr -> 
 1/2**k0<=f domr-f doml -> 
 f domr-f doml<=2**k1 -> 
 all c,d,k(f doml<=c -> d<=f domr -> 1/2**k<=d-c -> RealLt(f c)(f d)(k+l)) -> 
 all cds(
  cds Zero eqd(f doml@f domr) -> 
  all n Corr f(left(cds n))(right(cds n))(k0+n) -> 
  all n left(cds n)<=left(cds(Succ n)) -> 
  all n right(cds(Succ n))<=right(cds n) -> 
  all n 
   right(cds(Succ n))-left(cds(Succ n))=(2#3)*(right(cds n)-left(cds n)) -> 
  Real(f(RealConstr([n]left(cds n))([k]IntToNat(2*(k+k1)))))))")
(assume "f" "l" "k0" "k1" "Cont f" "f a<<=0" "0<<=f b"
	"a <_k0 b" "b-a<=2**k1" "HypSlope" 
        "cds" "cdsProp1" "cdsProp2" "cdsProp3" "cdsProp4" "cdsProp5")
(add-global-assumption
 "ContAppReal"
 "all f,x(Cont f -> Real x -> 
          all n f doml<=x seq n -> all n x seq n<=f domr -> Real(f x))")
(use "ContAppReal")
(auto)
(use  "IVTFinalRealLeft" (pt "f") (pt "l") (pt "k0"))
(auto)

;; ?_5: all n f doml<=(RealConstr([n]left(cds n))([k]2*(k+k1+1)))seq n
(assume "n")
(use "CorrElim1" (pt "right(cds n)") (pt "k0+n"))
(ng #t)
(auto)

;; ?_6: all n (RealConstr([n]left(cds n))([k]2*(k+k1+1)))seq n<=f domr
(assume "n")
(ng #t)
(use "RatLeTrans" (pt "right(cds n)"))
;; (pp "IVTFinalAux3")
(use "IVTFinalAux3" (pt "f") (pt "k0+n"))
(auto)
(use "CorrElim2" (pt "left(cds n)") (pt "k0+n"))
(auto)
;; Proof finished.
(save "IVTRealAppLeft")

;; Similary for right:

;; IVTRealRight
(set-goal 
 "all a,b,k1(
 b-a<=2**k1 -> 
 all cds(
  all n,m(n<=m -> left(cds n)<=left(cds m)) -> 
  all n,m(n<=m -> right(cds m)<=right(cds n)) -> 
  all n left(cds n)<=right(cds n) -> 
  all n right(cds n)-left(cds n)=(2#3)**n*(b-a) -> 
  Real(RealConstr([n]right(cds n))([k]IntToNat(2*(k+k1))))))")
(assume "a" "b" "k1" "IntBound" "cds" "cIncr" "dDecr" "cs<=ds" "cdDiff")
(use "RealIntro")

;; Cauchyness
(use "CauchyCrit")
(ng #t)

;; all k,n,m(
;;       IntToNat(2*(k+k1))<=n -> 
;;       n<=m -> abs(right(cds n)-right(cds m))<=1/2**k)
(assume "k" "n" "m" "Mk<=n" "n<=m")

;; abs(right(cds n)-right(cds m))<=1/2**k
(use "RatEqvLe" (pt "right(cds n)-right(cds m)"))

;; abs(right(cds n)-right(cds m))==right(cds n)-right(cds m)
(add-global-assumption
 "RatAbsPos"
 "all a,b(a<=b -> abs(b-a)==b-a)")
(use "RatAbsPos")
(auto)

;; right(cds n)-right(cds m)<=1/2**k
(use "RatLeTrans" (pt "right(cds n)-left(cds m)"))

;; right(cds n)-right(cds m)<=right(cds n)-left(cds m)
(use "RatMinusLe2")
(auto)

;; right(cds n)-left(cds m)<=1/2**k
(use "RatLeTrans" (pt "right(cds n)-left(cds n)"))

;; right(cds n)-left(cds m)<=right(cds n)-left(cds n)
(use "RatMinusLe2")
(auto)

;; right(cds n)-left(cds n)<=1/2**k
(inst-with-to "cdDiff" (pt "n") "cdDiffn")
(use "IVTRealAux1" (pt "a") (pt "b") (pt "n") (pt "k1"))
(auto)

;; Mon((RealConstr([n]left(cds n))([k]IntToNat(2*(k+k1))))mod)
(ng #t)

;; Mon([k2]IntToNat(2*(k2+k1)))
(use "MonIntro")
(ng #t)
(assume "k" "l" "k<=l")
(use "IntToNatMon")
(ord-field-simp-bwd)
(use "k<=l")
;; Proof finished.
(save "IVTRealRight")

;; IVTFinalRealRight
(set-goal 
 "all f,l,k0,k1(
 Cont f -> 
 f f doml<<=0 -> 
 0<<=f f domr -> 
 1/2**k0<=f domr-f doml -> 
 f domr-f doml<=2**k1 -> 
 all c,d,k(f doml<=c -> d<=f domr -> 1/2**k<=d-c -> RealLt(f c)(f d)(k+l)) -> 
 all cds(
  cds Zero eqd(f doml@f domr) -> 
  all n Corr f(left(cds n))(right(cds n))(k0+n) -> 
  all n left(cds n)<=left(cds(Succ n)) -> 
  all n right(cds(Succ n))<=right(cds n) -> 
  all n 
   right(cds(Succ n))-left(cds(Succ n))=(2#3)*(right(cds n)-left(cds n)) -> 
  Real(RealConstr([n]right(cds n))([k]IntToNat(2*(k+k1))))))")
(assume "f" "l" "k0" "k1" "Cont f" "f a<<=0" "0<<=f b"
	"a <_k0 b" "b-a<=2**k1" "HypSlope" 
        "cds" "cdsProp1" "cdsProp2" "cdsProp3" "cdsProp4" "cdsProp5")
(use "IVTRealRight" (pt "f doml") (pt "f domr"))
(use "b-a<=2**k1")

;; all n,m(n<=m -> left(cds n)<=left(cds m))
(assume "n" "m" "n<=m")
(use-with "IVTFinalAux1" (pt "[n]left(cds n)") "?" (pt "n") (pt "m") "n<=m")
(ng #t)
(use "cdsProp3")

;; all n,m(n<=m -> right(cds m)<=right(cds n))
(assume "n" "m" "n<=m")
(use-with "IVTFinalAux2" (pt "[n]right(cds n)") "?" (pt "n") (pt "m") "n<=m")
(ng #t)
(use "cdsProp4")

;; all n left(cds n)<=right(cds n)
(assume "n")
(cut "Corr f(left(cds n))(right(cds n))(k0+n)")
(assume "CorrHyp")
(use-with "IVTFinalAux3" (pt "f") (pt "(left(cds n))") (pt "right(cds n)")
	  (pt "k0+n") "CorrHyp")
(use "cdsProp2")

;; all n right(cds n)-left(cds n)=(2#3)**n*(f domr-f doml)
(use "IVTDiff")
(use "cdsProp1")
(use "cdsProp5")
;; Proof finished.
(save "IVTFinalRealRight")

;; IVTRealAppRight
(set-goal 
 "all f,l,k0,k1(
 Cont f -> 
 f f doml<<=0 -> 
 0<<=f f domr -> 
 1/2**k0<=f domr-f doml -> 
 f domr-f doml<=2**k1 -> 
 all c,d,k(f doml<=c -> d<=f domr -> 1/2**k<=d-c -> RealLt(f c)(f d)(k+l)) -> 
 all cds(
  cds Zero eqd(f doml@f domr) -> 
  all n Corr f(left(cds n))(right(cds n))(k0+n) -> 
  all n left(cds n)<=left(cds(Succ n)) -> 
  all n right(cds(Succ n))<=right(cds n) -> 
  all n 
   right(cds(Succ n))-left(cds(Succ n))=(2#3)*(right(cds n)-left(cds n)) -> 
  Real(f(RealConstr([n]right(cds n))([k]IntToNat(2*(k+k1)))))))")
(assume "f" "l" "k0" "k1" "Cont f" "f a<<=0" "0<<=f b"
	"a <_k0 b" "b-a<=2**k1" "HypSlope" 
        "cds" "cdsProp1" "cdsProp2" "cdsProp3" "cdsProp4" "cdsProp5")
(use "ContAppReal")
(auto)
(use  "IVTFinalRealRight" (pt "f") (pt "l") (pt "k0"))
(auto)

;; all n f doml<=(RealConstr([n]right(cds n))([k]IntToNat(2*(k+k1))))seq n
(assume "n")
(ng #t)
(use "RatLeTrans" (pt "left(cds n)"))
(use "CorrElim1" (pt "right(cds n)") (pt "k0+n"))
(auto)
;; (pp "IVTFinalAux3")
(use "IVTFinalAux3" (pt "f") (pt "k0+n"))
(auto)

;; all n (RealConstr([n]right(cds n))([k]IntToNat(2*(k+k1))))seq n<=f domr
(assume "n")
(ng #t)
(use "CorrElim2" (pt "left(cds n)") (pt "k0+n"))
(auto)
;; Proof finished.
(save "IVTRealAppRight")

;; IVTFinal
(set-goal 
 "all f,l,k0,k1(
 Cont f -> 
 f f doml<<=0 -> 
 0<<=f f domr -> 
 1/2**k0<=f domr-f doml -> 
 f domr-f doml<=2**k1 -> 
 all c,d,k(f doml<=c -> d<=f domr -> 1/2**k<=d-c -> RealLt(f c)(f d)(k+l)) -> 
 ex x(Real x & f x===0))")
(assume "f" "l" "k0" "k1" "Cont f" "f a<<=0" "0<<=f b"
	"a <_k0 b" "b-a<=2**k1" "HypSlope")
(cut "ex cds(
 cds Zero eqd(f doml@f domr) & 
 all n Corr f(left(cds n))(right(cds n))(k0+n) & 
 all n(
  left(cds n)<=left(cds(Succ n)) & right(cds(Succ n))<=right(cds n) & 
  right(cds(Succ n))-left(cds(Succ n))=(2#3)*(right(cds n)-left(cds n))))")
(assume "Excds")
(by-assume "Excds" "cds" "cdsProp")
(ex-intro (pt "RealConstr([n]left(cds n))([k]IntToNat(2*(k+k1)))"))
(split)
(use  "IVTFinalRealLeft" (pt "f") (pt "l") (pt "k0"))
(auto)

;; f(RealConstr([n]left(cds n))([k]IntToNat(2*(k+k1))))===0
(add-global-assumption
 "RealLeAntiSym"
 "all x,y(Real x -> Real y -> x<<=y -> y<<=x -> x===y)")
(use "RealLeAntiSym")

;; Real(f(RealConstr([n]left(cds n))([k]IntToNat(2*(k+k1)))))
(use "IVTRealAppLeft" (pt "l") (pt "k0"))
(auto)

;; Real 0
(use "RealRat")
;; (add-global-assumption "RealZero" "Real(0)")
;; (use "RealZero")

;; (RealConstr([n]left(cds n))([k]IntToNat(2*(k+k1))))<<=0
(add-global-assumption
 "LeContAppZero"
 "all f,x(Cont f -> Real x -> all n f(x seq n)<<=0 -> f x<<=0)")
(use "LeContAppZero")
(use "Cont f")
(use  "IVTFinalRealLeft" (pt "f") (pt "l") (pt "k0"))
(auto)

;; all n f((RealConstr([n]left(cds n))([k]IntToNat(2*(k+k1))))seq n)<<=0
(assume "n")
(use "CorrElim4" (pt "right(cds n)") (pt "k0+n"))
(auto)

;; 0<<=f(RealConstr([n]left(cds n))([k]IntToNat(2*(k+k1))))
(add-global-assumption
 "RealLeZeroCompat"
 "all x,y(Real x -> Real y -> x===y -> 0<<=y -> 0<<=x)")
(use "RealLeZeroCompat"
     (pt "f(RealConstr([n]right(cds n))([k]IntToNat(2*(k+k1))))"))

;; Real(f(RealConstr([n]left(cds n))([k]IntToNat(2*(k+k1)))))
(use "IVTRealAppLeft" (pt "l") (pt "k0"))
(auto)

;; Real(f(RealConstr([n]right(cds n))([k]IntToNat(2*(k+k1)))))
(use "IVTRealAppRight" (pt "l") (pt "k0"))
(auto)

;; f(RealConstr([n]left(cds n))([k]IntToNat(2*(k+k1))))===
;; f(RealConstr([n]right(cds n))([k]IntToNat(2*(k+k1))))
(add-global-assumption
 "ContAppCompat"
 "all f,x,y(Cont f -> Real x -> Real y -> x===y -> f x===f y)")
(use "ContAppCompat")
(auto)
(use "IVTRealLeft" (pt "f doml") (pt "f domr"))
(auto)

;; all n,m(n<=m -> left(cds n)<=left(cds m))
(assume "n" "m" "n<=m")
(use-with "IVTFinalAux1" (pt "[n]left(cds n)") "?" (pt "n") (pt "m") "n<=m")
(ng #t)
(auto)

;; all n,m(n<=m -> right(cds m)<=right(cds n))
(assume "n" "m" "n<=m")
(use-with "IVTFinalAux2" (pt "[n]right(cds n)") "?" (pt "n") (pt "m") "n<=m")
(ng #t)
(auto)

;; all n left(cds n)<=right(cds n)
(assume "n")
(cut "Corr f(left(cds n))(right(cds n))(k0+n)")
(assume "CorrHyp")
(use-with "IVTFinalAux3" (pt "f") (pt "(left(cds n))") (pt "right(cds n)")
	  (pt "k0+n") "CorrHyp")
(auto)

;; all n right(cds n)-left(cds n)=(2#3)**n*(f domr-f doml)
;; Here we need IVTDiff (pp "IVTDiff")
(use "IVTDiff")
(auto)

;; Real(RealConstr([n]right(cds n))([k]IntToNat(2*(k+k1))))
(use "IVTRealRight" (pt "f doml") (pt "f domr"))
(auto)

;; all n,m(n<=m -> left(cds n)<=left(cds m))
(assume "n" "m" "n<=m")
(use-with "IVTFinalAux1" (pt "[n]left(cds n)") "?" (pt "n") (pt "m") "n<=m")
(ng #t)
(auto)

;; all n,m(n<=m -> right(cds m)<=right(cds n))
(assume "n" "m" "n<=m")
(use-with "IVTFinalAux2" (pt "[n]right(cds n)") "?" (pt "n") (pt "m") "n<=m")
(ng #t)
(auto)

;; all n left(cds n)<=right(cds n)
(assume "n")
(cut "Corr f(left(cds n))(right(cds n))(k0+n)")
(assume "CorrHyp")
(use-with "IVTFinalAux3" (pt "f") (pt "(left(cds n))") (pt "right(cds n)")
	  (pt "k0+n") "CorrHyp")
(auto)

;; all n right(cds n)-left(cds n)=(2#3)**n*(f domr-f doml)
;; Here we need IVTDiff (pp "IVTDiff")
(use "IVTDiff")
(auto)

;; RealConstr([n]left(cds n))([k]IntToNat(2*(k+k1)))===
;; RealConstr([n]right(cds n))([k]IntToNat(2*(k+k1)))
(use "RealEqChar2")

;; Cauchy([n]left(cds n))([k]IntToNat(2*(k+k1)))
(cut "Real(RealConstr([n]left(cds n))([k]IntToNat(2*(k+k1))))")
(use "RealElimVariant1")
(use "IVTRealLeft" (pt "f doml") (pt "f domr"))
(auto)

;; all n,m(n<=m -> left(cds n)<=left(cds m))
(assume "n" "m" "n<=m")
(use-with "IVTFinalAux1" (pt "[n]left(cds n)") "?" (pt "n") (pt "m") "n<=m")
(ng #t)
(auto)

;; all n,m(n<=m -> right(cds m)<=right(cds n))
(assume "n" "m" "n<=m")
(use-with "IVTFinalAux2" (pt "[n]right(cds n)") "?" (pt "n") (pt "m") "n<=m")
(ng #t)
(auto)

;; all n left(cds n)<=right(cds n)
(assume "n")
(cut "Corr f(left(cds n))(right(cds n))(k0+n)")
(assume "CorrHyp")
(use-with "IVTFinalAux3" (pt "f") (pt "(left(cds n))") (pt "right(cds n)")
	  (pt "k0+n") "CorrHyp")
(auto)

;; all n right(cds n)-left(cds n)=(2#3)**n*(f domr-f doml)
;; Here we need IVTDiff (pp "IVTDiff")
(use "IVTDiff")
(auto)

;; Cauchy([n]right(cds n))([k]IntToNat(2*(k+k1)))
(cut "Real(RealConstr([n]right(cds n))([k]IntToNat(2*(k+k1))))")
(use "RealElimVariant1")
(use "IVTRealRight" (pt "f doml") (pt "f domr"))
(auto)

;; all n,m(n<=m -> left(cds n)<=left(cds m))
(assume "n" "m" "n<=m")
(use-with "IVTFinalAux1" (pt "[n]left(cds n)") "?" (pt "n") (pt "m") "n<=m")
(ng #t)
(auto)

;; all n,m(n<=m -> right(cds m)<=right(cds n))
(assume "n" "m" "n<=m")
(use-with "IVTFinalAux2" (pt "[n]right(cds n)") "?" (pt "n") (pt "m") "n<=m")
(ng #t)
(auto)

;; all n left(cds n)<=right(cds n)
(assume "n")
(cut "Corr f(left(cds n))(right(cds n))(k0+n)")
(assume "CorrHyp")
(use-with "IVTFinalAux3" (pt "f") (pt "(left(cds n))") (pt "right(cds n)")
	  (pt "k0+n") "CorrHyp")
(auto)

;; all n right(cds n)-left(cds n)=(2#3)**n*(f domr-f doml)
;; Here we need IVTDiff (pp "IVTDiff")
(use "IVTDiff")
(auto)

;; all k ex n0 all n(n0<=n -> abs(([n]left(cds n))n-([n]right(cds n))n)<=1/2**k)
(assume "k")
(ng #t)

;; ex n0 all n(n0<=n -> abs(left(cds n)-right(cds n))<=1/2**k)
(add-global-assumption
 "IVTFinalAux4"
 "all f,cds(
      (all n right(cds n)-left(cds n)=(2#3)**n*(f domr-f doml)) ->
      all k ex n0 all n(n0<=n -> abs(left(cds n)-right(cds n))<=1/2**k))")
;; needs an additional assumption left(cds n)<=right(cds n) to be correct
(use "IVTFinalAux4" (pt "f"))
(use "IVTDiff")
(auto)

;; 0<<=f(RealConstr([n]right(cds n))([k]IntToNat(2*(k+k1))))
(add-global-assumption
 "LeZeroContApp"
 "all f,y(Cont f -> Real y -> all n 0<<=f(y seq n) -> 0<<=f y)")
(use "LeZeroContApp")
(use "Cont f")
(use  "IVTFinalRealRight" (pt "f") (pt "l") (pt "k0"))
(auto)

;; all n 0<<=f((RealConstr([n]right(cds n))([k]IntToNat(2*(k+k1))))seq n)
(assume "n")
(pp "CorrElim5")
(use "CorrElim5" (pt "left(cds n)") (pt "k0+n"))
(auto)
(use "IVTcds" (pt "l"))
(auto)
;; Proof finished.
(save "IVTFinal")

(define IVTFinal-eterm
  (proof-to-extracted-term (theorem-name-to-proof "IVTFinal")))
(define IVTFinal-neterm (rename-variables (nt IVTFinal-eterm)))
(pp IVTFinal-neterm)

;; [f,k,k0,k1]RealConstr([n]left(cIVTcds f k k0 n))([k2]IntToNat(2*(k2+k1)))

;; For to extract an approximation of sqrt 2 we prove IVTApprox
;; This needs RealApprox (in real.scm)

;; IVTApprox
(set-goal 
 "all f,l,k0,k1(
 Cont f -> 
 f f doml<<=0 -> 
 0<<=f f domr -> 
 1/2**k0<=f domr-f doml -> 
 f domr-f doml<=2**k1 -> 
 all c,d,k(f doml<=c -> d<=f domr -> 1/2**k<=d-c -> RealLt(f c)(f d)(k+l)) -> 
 exr x(Real x & f x===0 & all k ex c abs(c-x)<<=1/2**k))")
(assume "f" "l" "k0" "k1" "Cont f" "f a<<=0" "0<<=f b"
	"a <_k0 b" "b-a<=2**k1" "HypSlope")
(cut "ex x(Real x & f x===0)")
(assume "ExHyp")
(by-assume "ExHyp" "x" "xProp")

;; exr x(Real x & f x===0 & all k ex c abs(c-x)<<=1/2**k)
(intro 0 (pt "x"))
(split)
(use "xProp")

(split)
(use "xProp")

;; all k ex c abs(c-x)<<=1/2**k
(assume "k")
(use "RealApprox")

(use "xProp")

;; ex x(Real x & f x===0)
(use "IVTFinal" (pt "l") (pt "k0") (pt "k1"))
(auto)
;; Proof finished.
(save "IVTApprox")

(define IVTApprox-eterm
  (proof-to-extracted-term (theorem-name-to-proof "IVTApprox")))
(define IVTApprox-neterm (rename-variables (nt IVTApprox-eterm)))
(pp IVTApprox-neterm)

;; [f,k,k0,k1]cRealApprox(cIVTFinal f k k0 k1)

;; We now prove that every continuous monotone function with a lower
;; bound on its slope has a continuous inverse.

(add-var-name "g" (make-alg "cont"))
(add-var-name "u" (make-alg "rat"))

(add-program-constant "Shift" (py "cont=>rat=>cont") 1)

(add-computation-rule
 "Shift f u"
 "ContConstr f doml f domr([a,n]f approx a n-u)f uMod f uModCont")

(add-global-assumption
 "ShiftProp"
 "all f,u,c(Cont f -> f doml<=c -> c<=f domr -> Shift f u c===f c-u)")

(add-global-assumption
 "ShiftPropRev"
 "all f,u,c(Cont f -> f doml<=c -> c<=f domr -> f c-u===Shift f u c)")

(add-global-assumption
 "ContShift" "all f,u(Cont f -> Cont(Shift f u))")

;; We will apply AC to "all u ex x(Real x & Shift f u x===0)".  The left
;; component of x is a Cauchy sequence, and the whole function is the
;; approximation part of the continuous function to be constructed.

;; (add-global-assumption
;;  "AC" (pf "all alpha1^ ex alpha2^ (Pvar alpha1 alpha2)alpha1^alpha2^ ->
;;             ex alpha1=>alpha2^ all alpha1^ 
;;              (Pvar alpha1 alpha2)alpha1^(alpha1=>alpha2^alpha1^)"))

(add-global-assumption ;to be used instead of "IVTFinalAux4"
 "InvAux1"
 "all a,b,k1,k,n(b-a<=2**k1 -> 2*(k1+k)<=n -> (2#3)**n*(b-a)<=1/2**k)")

(add-global-assumption "RealLeRefl" "all x(Real x -> x<<=x)")

;; Inv
(set-goal
 "all f,l,k0,k1,a1,b1(
 Cont f -> 
 f f doml<<=a1 -> 
 b1<<=f f domr -> 
 a1<b1 -> 
 1/2**k0<=f domr-f doml -> 
 f domr-f doml<=2**k1 -> 
 all c,d,k(f doml<=c -> d<=f domr -> 1/2**k<=d-c -> RealLt(f c)(f d)(k+l)) -> 
 ex g(
  Cont g & a1==g doml & b1==g domr & all y(a1<<=y -> y<<=b1 -> f(g y)===y) & 
  all x(f doml<<=x -> x<<=f domr -> g(f x)===x)))")
(assume "f" "l" "k0" "k1" "a1" "b1" "Cont f" "f a<=a1" "b1<=f b" "a1<b1"
	"a <_k0 b" "b-a<=2**k1" "HypSlope")
(assert
 "all u(a1<=u -> u<=b1 -> 
      ex cds(cds Zero eqd((Shift f u)doml@(Shift f u)domr) &
            all n Corr(Shift f u)(left(cds n))(right(cds n))(k0+n) &
            all n(left(cds n)<=left(cds(Succ n)) & 
                  right(cds(Succ n))<=right(cds n) &
                  right(cds(Succ n))-left(cds(Succ n))=
                  (2#3)*(right(cds n)-left(cds n)))))")
 (assume "u" "a1<=u" "u<=b1")
 (use "IVTcds" (pt "l") (pt "k0+1") (pt "k1"))
 (use "ContShift")
 (use "Cont f")

;; Shift f u(Shift f u)doml<<=0 from
 (add-global-assumption
  "InvAux2"
  "all f,u(Cont f -> Shift f u(f doml)===(f doml-u))")
 (simp (pf "(Shift f u)doml=f doml"))
 (add-global-assumption
  "RealEqLe"
  "all x1,x2,x3(x1===x2 -> x2<<=x3 -> x1<<=x3)")
 (use "RealEqLe" (pt "f f doml-u"))
 (use "ShiftProp")
 (auto)

;; f doml<=f domr ;should be part of the definition of Cont
 (add-global-assumption
  "ContDom" "all f(Cont f -> f doml<=f domr)")
 (use "ContDom")
 (use "Cont f")

;; f f doml-u<<=0
 (ord-field-simp-bwd)
 (add-global-assumption
  "RealLeTrans"
  "all x1,x2,x3(
       Real x1 -> Real x2 -> Real x3 -> x1<<=x2 -> x2<<=x3 -> x1<<=x3)")
 (use "RealLeTrans" (pt "RealConstr([n]a1)([k]Zero)"))
 (add-global-assumption
  "ContAppRat"
  "all f,c(Cont f -> f doml<=c -> c<=f domr -> Real(f c))")
 (use "ContAppRat")
 (auto)
 (use "ContDom")
 (auto)
;;  (add-global-assumption "RealRat" "all a Real a")
 (use "RealRat")
 (use "RealRat")

;; f f doml<<=a1 (with f a<=a1:f f doml<<=a1 in context)
 (use "f a<=a1")
 (auto)

;; a1<<=u
 (add-global-assumption "RatRealLe" "all a,b(a<=b -> a<<=b)")
 (use "RatRealLe")
 (auto)

;; 0<<=Shift f u(Shift f u)domr
 (simp (pf "(Shift f u)domr=f domr"))
 (add-global-assumption
  "RealLeEq"
  "all x,x2,x3(x<<=x2 -> x2===x3 -> x<<=x3)")
 (use "RealLeEq" (pt "f f domr-u"))
 (ord-field-simp-bwd)
 (use "RealLeTrans" (pt "RealConstr([n]b1)([k]Zero)"))
 (use "RealRat")
 (use "RealRat")
 (use "ContAppRat")
 (auto)

;; f doml<=f domr
 (use "ContDom")
 (auto)
 (use "RatRealLe")
 (auto)

;; f f domr-u===Shift f u f domr 
 (use "ShiftPropRev")
 (auto)

;; ?_47: f doml<=f domr
 (use "ContDom")
 (auto)

;; ?_10: all c,d,k(
;;        (Shift f u)doml<=c -> 
;;        d<=(Shift f u)domr -> 
;;        1/2**k<=d-c -> RealLt(Shift f u c)(Shift f u d)(k+l))
(assume "c" "d" "k" "a<=c" "d<=b" "(1/2**k)<=d-c")
(add-global-assumption
 "InvAux3"
 "all f,u,c,d,k(Cont f -> RealLt(f c)(f d)k -> 
                    RealLt(Shift f u c)(Shift f u d)k)")
(use "InvAux3")
(auto)

;; all u(
;;       a1<=u -> 
;;       u<=b1 -> 
;;       ex cds(
;;        cds Zero eqd((Shift f u)doml@(Shift f u)domr) & 
;;        all n Corr(Shift f u)(left(cds n))(right(cds n))(k0+n) & 
;;        all n(
;;         left(cds n)<=left(cds(Succ n)) & right(cds(Succ n))<=right(cds n) & 
;;         right(cds(Succ n))-left(cds(Succ n))=
;;         (2#3)*(right(cds n)-left(cds n))))) -> 
;;      ex g(
;;       Cont g & a1==g doml & b1==g domr & 
;;       all y(a1<<=y -> y<<=b1 -> f(g y)===y) & 
;;       all x(f doml<<=x -> x<<=f domr -> g(f x)===x))
(assume "IVTcdsHyp")
(add-var-name "pcds" (py "rat=>nat=>rat@@rat")) ;parametized cds
(assert
 "all u ex cds(
    a1<=u -> 
    u<=b1 ->        
     cds Zero eqd((Shift f u)doml@(Shift f u)domr) & 
     all n Corr(Shift f u)(left(cds n))(right(cds n))(k0+n) & 
     all n(
      left(cds n)<=left(cds(Succ n)) & right(cds(Succ n))<=right(cds n) & 
      right(cds(Succ n))-left(cds(Succ n))=(2#3)*(right(cds n)-left(cds n))))")
 (assume "u")
;; Here we could use cases on a1<=u etc, if we want to avoid IP.
;; However, this would bring the case distinctions in the extracted
;; term.  On the other hand, IP is completely harmless for decidable
;; premises.

;; (add-global-assumption
;;  "IP" (pf "(Pvar -> ex alpha^ (Pvar alpha)alpha^) -> 
;;            ex alpha^(Pvar -> (Pvar alpha)alpha^)"))
;; Problem with alpha^ for cds.  Hence: alpha

(add-global-assumption
 "IP" "(Pvar^ -> ex alpha (Pvar alpha)^alpha) -> 
            ex alpha(Pvar^ -> (Pvar alpha)^alpha)")

(use-with
 "IP" (py "nat=>rat@@rat")
 (make-cterm (pf "a1<=u"))
 (make-cterm (pv "cds")
	     (pf "u<=b1 -> 
     cds Zero eqd((Shift f u)doml@(Shift f u)domr) & 
     all n Corr(Shift f u)(left(cds n))(right(cds n))(k0+n) & 
     all n(
      left(cds n)<=left(cds(Succ n)) & right(cds(Succ n))<=right(cds n) & 
      right(cds(Succ n))-left(cds(Succ n))=(2#3)*(right(cds n)-left(cds n)))"))
 "?")
(assume "a1<=u")
(use-with
 "IP" (py "nat=>rat@@rat")
 (make-cterm (pf "u<=b1"))
 (make-cterm (pv "cds")
	     (pf "
     cds Zero eqd((Shift f u)doml@(Shift f u)domr) & 
     all n Corr(Shift f u)(left(cds n))(right(cds n))(k0+n) & 
     all n(
      left(cds n)<=left(cds(Succ n)) & right(cds(Succ n))<=right(cds n) & 
      right(cds(Succ n))-left(cds(Succ n))=(2#3)*(right(cds n)-left(cds n)))"))
 "?")
(assume "u<=b1")
(use "IVTcdsHyp")
(use "a1<=u")
(use "u<=b1")

(drop "IVTcdsHyp")
(assume "IVTcdsHAC")
(assert
 "ex pcds
      all u(
  a1<=u -> 
  u<=b1 -> 
   pcds u Zero eqd((Shift f u)doml@(Shift f u)domr) & 
   all n Corr(Shift f u)(left(pcds u n))(right(pcds u n))(k0+n) & 
   all n(
    left(pcds u n)<=left(pcds u(Succ n)) & 
    right(pcds u(Succ n))<=right(pcds u n) & 
    right(pcds u(Succ n))-left(pcds u(Succ n))=
    (2#3)*(right(pcds u n)-left(pcds u n))))")
(add-global-assumption
 "AC"
 "all alpha1 ex alpha2 (Pvar alpha1 alpha2)^alpha1 alpha2 -> 
      ex alpha1=>alpha2 
      all alpha1 (Pvar alpha1 alpha2)^alpha1(alpha1=>alpha2 alpha1)")
(use-with
 "AC"
 (py "rat") (py "nat=>rat@@rat")
 (make-cterm
  (pv "u") (pv "cds")
  (pf "a1<=u -> 
               u<=b1 -> 
               cds Zero eqd((Shift f u)doml@(Shift f u)domr) & 
               all n Corr(Shift f u)(left(cds n))(right(cds n))(k0+n) & 
               all n(
                left(cds n)<=left(cds(Succ n)) & 
                right(cds(Succ n))<=right(cds n) & 
                right(cds(Succ n))-left(cds(Succ n))=
                (2#3)*(right(cds n)-left(cds n)))"))
 "?")
(use "IVTcdsHAC")

(drop "IVTcdsHAC")
(assume "Expcds")
(by-assume "Expcds" "pcds" "Hpcds")
(ex-intro
 (pt "ContConstr a1 b1 ([u,n]left(pcds u n))
                       ([k]IntToNat(2*(f uModCont(k+l+2))+k1+k1))([k]k+l+2)"))
;; (ex-intro (pt "ContConstr a1 b1 ([u,n]left(pcds u n))
;;                           ([k]2*(k1+f uModCont(k+l+2)))([k]k+l+2)"))

;; Now we must verify that the construction of g indeed gives a
;; continuos function, following the informal proof.  However, all this
;; will not affect the extracted term.  So for the moment we use (admit)

(split)
(admit)
(split)
(admit)
(split)
(admit)
(split)
(admit)
(admit)
;; Proof finished.
(save "Inv")

(pp (rename-variables
     (nt (proof-to-extracted-term (theorem-name-to-proof "Inv")))))

;; [f,k,k0,k1,a,a0]
;;  ContConstr a a0
;;  ([a1,n]
;;    left((cAC rat nat=>rat@@rat)
;;         ([a2]
;;           (cIP nat=>rat@@rat)
;;           ((cIP nat=>rat@@rat)
;;            (cIVTcds
;;             (ContConstr f doml f domr([a3,n0]f approx a3 n0-a2)f uMod 
;;              f uModCont)
;;             k 
;;             k0)))
;;         a1 
;;         n))
;;  ([k2]IntToNat(2*f uModCont(IntS(IntS(k2+k)))+k1+k1))
;;  ([k2]IntS(IntS(k2+k)))

;; For to use "Inv" for numerical computations we prove InvApprox.
;; This needs RealApprox (in real.scm)

;; InvApprox
(set-goal 
 "all f,l,k0,k1,a1,b1(
 Cont f -> 
 f f doml<<=a1 -> 
 b1<<=f f domr -> 
 a1<b1 -> 
 1/2**k0<=f domr-f doml -> 
 f domr-f doml<=2**k1 -> 
 all c,d,k(f doml<=c -> d<=f domr -> 1/2**k<=d-c -> RealLt(f c)(f d)(k+l)) -> 
 exr g(
  Cont g & a1==g doml & b1==g domr & all y(a1<<=y -> y<<=b1 -> f(g y)===y) & 
  all x(f doml<<=x -> x<<=f domr -> g(f x)===x) & 
  all u(a1<=u -> u<=b1 -> all k ex c abs(c-g u)<<=1/2**k)))")
(assume "f" "l" "k0" "k1" "a1" "b1" "Cont f" "f a<=a1" "b1<=f b" "a1<b1"
	"a <_k0 b" "b-a<=2**k1" "HypSlope")
(cut "ex g(Cont g & a1==g doml & b1==g domr &
             all y(a1<<=y -> y<<=b1 -> f(g y)===y) &
             all x(f doml<<=x -> x<<=f domr -> g(f x)===x))")
(assume "ExHyp")
(by-assume "ExHyp" "g" "gProp")

;; exr g ...
(intro 0 (pt "g"))
(split)
(use "gProp")
(split)
(use "gProp")
(split)
(use "gProp")
(split)
(use "gProp")
(split)
(use "gProp")

;; all u(a1<=u -> u<=b1 -> all k ex c abs(c-g u)<<=1/2**k)
(assume "u" "a1<=u" "u<=b1" "k")
(use "RealApprox")

;; Real(g u)
(use "ContReal")
(use "gProp")
(use "RealRat")
(use "RatRealLe")
(use "RatEqvLe" (pt "a1"))
(add-global-assumption "RatEqvSym" "all a,b(a==b -> b==a)")
(use "RatEqvSym")
(use "gProp")
(use "a1<=u")
(use "RatRealLe")
(use "RatLeEq" (pt "b1"))
(use "u<=b1")
(use "gProp")

;; ex g(
;;       Cont g & a1==g doml & b1==g domr & 
;;       all y.a1<<=y -> y<<=b1 -> f(g y)===y & 
;;       all x.f doml<<=x -> x<<=f domr -> g(f x)===x)
(use "Inv"  (pt "l") (pt "k0") (pt "k1"))
(auto)
;; Proof finished.
(save "InvApprox")

(define InvApprox-eterm
  (proof-to-extracted-term (theorem-name-to-proof "InvApprox")))
(define InvApprox-neterm (rename-variables (nt InvApprox-eterm)))
(pp InvApprox-neterm)

;; [f,k,k0,k1,a,a0,a1]
;;  cRealApprox
;;  (RealConstr((cInv f k k0 k1 a a0)approx a1)
;;   ([k2](cInv f k k0 k1 a a0)uMod(IntS(IntS k2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Brainstorming: necessary and useful properties of Real, Cont, Corr,
;; Cauchy, Mon, RealNNeg, RealPos, RealLt, RealLe <<=

;; RealPlus
(set-goal "all x,y(Real x -> Real y -> Real(x+y))")

;; 2004-06-05

(add-var-name "xs" (py "nat=>rea"))

(add-ids (list (list "RealCauchy"
		     (make-arity (py "nat=>rea") (py "int=>nat"))))
	 '("allnc xs,M(all n Real(xs n) -->
                       all k,n,m(M k<=n -> M k<=m ->
                                 abs(xs n-xs m)<<=1/2**k) -->
                       RealCauchy xs M)" "RealCauchyIntro"))

;; RealCauchyElim1
(set-goal "all xs,M(RealCauchy xs M -> all n Real(xs n))")
(assume "xs" "M")
(elim)
(search)
;; Proof finished.
(save "RealCauchyElim1")

;; RealCauchyElim2
(set-goal "all xs,M(RealCauchy xs M -> 
               all k,n,m(M k<=n ->  M k<=m ->
                       abs(xs n-xs m)<<=1/2**k))")
(assume "xs" "M")
(elim)
(search)
;; Proof finished.
(save "RealCauchyElim2")

(add-ids
 (list (list "RealConv"
	     (make-arity (py "nat=>rea") (py "rea") (py "int=>nat"))))
 '("allnc xs,x,M(all n Real(xs n) --> Real x --> 
                 all k,n(M k<=n -> abs(xs n-x)<<=1/2**k) -->
                 RealConv xs x M)" "RealConvIntro"))

;; RealConvElim1
(set-goal "all xs,x,M(RealConv xs x M -> all n Real(xs n))")
(assume "xs" "x" "M")
(elim)
(search)
;; Proof finished.
(save "RealConvElim1")

;; RealConvElim2
(set-goal "all xs,x,M(RealConv xs x M -> Real x)")
(assume "xs" "x" "M")
(elim)
(search)
;; Proof finished.
(save "RealConvElim2")

;; RealConvElim3
(set-goal "all xs,x,M(RealConv xs x M ->
                 all k,n(M k<=n -> abs(xs n-x)<<=1/2**k))")
(assume "xs" "x" "M")
(elim)
(search)
;; Proof finished.
(save "RealConvElim3")

;; RealLeChar1
(set-goal "all as,M,bs,N(Cauchy as M -> Cauchy bs N ->
                    RealConstr as M<<=RealConstr bs N ->
                    all k ex n0 all n(n0<=n -> as n<=bs n+1/2**k))") 

;; RealLeChar2
(set-goal "all as,M,bs,N(Cauchy as M -> Cauchy bs N ->
                    (all k ex n0 all n(n0<=n -> as n<=bs n+1/2**k)) ->
                    RealConstr as M<<=RealConstr bs N)") 

;; RatCauchyConvMod
(set-goal "all as,M,k,n(Cauchy as M -> M k<=n ->
                   abs(as n-RealConstr as M)<<=1/2**k)")

;; RealComplete
(set-goal "all xs,M(RealCauchy xs M -> 
               RealConv xs(RealConstr([n](xs n)seq((xs n)mod n))
                                     ([k]IntToNat(M(k+1)max(k+2))))
                        ([k]IntToNat(M(k+2)max(k+3))))")

;; RealCauchyConvMod
(set-goal "all xs,M,k,n(RealCauchy xs M -> M k<=n ->
                   abs(xs n-RealConstr
                            ([n](xs n)seq((xs n)mod n))
                            ([k]IntToNat(M(k+1)max(k+2))))<<=1/2**k)")

;; ContLim
(set-goal "all f,xs,M,y(Cont f -> RealCauchy xs M ->
       all p ex n0 all n(n0<=n -> 
       abs(f(xs n)-f(RealConstr([n](xs n)seq((xs n)mod n))
                               ([k]IntToNat(M(k+1)max(k+2)))))<<=(1/2**p)))")

;; RealNNegLim
(set-goal "all xs,M(RealCauchy xs M -> all n 0<<=(xs n) ->
               0<<=(RealConstr ([n](xs n)seq((xs n)mod n))
                              ([k]IntToNat(M(k+1)max(k+2)))))")

