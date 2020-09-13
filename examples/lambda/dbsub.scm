;; 2014-10-07.  dbsub.scm.  Substitution for de Bruijn indices, with
;; substitutions in the style of Hancock/Joachimski, following the
;; general treatment in Joachimski's thesis (Section 2.4 and B.1.3,
;; p.183) (LMU, 2001), as in minlog/examples/tait/sn.scm.  We prove
;; associativity of composition, and the substitution lemma.

;; We also define beta conversion, one-step beta reduction and beta
;; reduction, and state the Church-Rosser theorem and its type.  The
;; proof is left for further work.

;; (load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(libload "list.scm")
(set! COMMENT-FLAG #t)

(add-var-name "k" (py "nat"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Algebras
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(add-algs "dB"
	  '("Var" "nat=>dB")
	  '("App" "dB=>dB=>dB")
	  '("Abs" "dB=>dB"))
(add-totality "dB")

;; DBTotalVar
(set-goal "all dB TotalDB dB")
(use "AllTotalIntro")
(assume "dB^" "TdB")
(use "TdB")
;; Proof finished
(save "DBTotalVar")

;; DBEqToEqD
(set-goal "all dB1,dB2(dB1=dB2 -> dB1 eqd dB2)")
(ind)
;; Case Var
(assume "n")
(cases)
(assume "m")
(ng)
(assume "n=m")
(simp "n=m")
(use "InitEqD")
(assume "dB1" "dB2")
(ng)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "dB")
(ng)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
;; Case App
(assume "dB1" "IHdB1" "dB2" "IHdB2")
(cases)
(assume "n")
(ng)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "dB3" "dB4")
(ng)
(assume "Conj")
(simp "IHdB1" (pt "dB3"))
(simp "IHdB2" (pt "dB4"))
(use "InitEqD")
(use "Conj")
(use "Conj")
(assume "dB")
(ng)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
;; Case Abs
(assume "dB" "IHdB")
(cases)
(assume "n")
(ng)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "dB1" "dB2")
(ng)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "dB1")
(ng)
(assume "dB=dB1")
(simp "IHdB" (pt "dB1"))
(use "InitEqD")
(use "dB=dB1")
;; Proof finished.
(save "DBEqToEqD")

(add-var-name "r" "s" "t" (py "dB"))
(add-var-name "rs" (py "list dB"))

; Application for terms is via the constant App

(add-new-application 
 (lambda (type) (equal? type (py "dB")))
 (lambda (term1 term2) (mk-term-in-app-form (pt "App") term1 term2)))

(add-new-application-syntax
 ;; predicate
 (lambda (term)
   (and (term-in-app-form? term)
	(let ((op (term-in-app-form-to-op term)))
	  (term-in-app-form? op)
	  (term=? (pt "App") (term-in-app-form-to-op op)))))
 ;; to arg
 (lambda (term)
   (term-in-app-form-to-arg term))
 ;; to op
 (lambda (term)
   (term-in-app-form-to-arg
    (term-in-app-form-to-op term))))

(add-algs "sub" '("Up" "nat=>sub") '("Dot" "dB=>sub=>sub"))
(add-totality "sub")

;; SubTotalVar
(set-goal "all sub TotalSub sub")
(use "AllTotalIntro")
(assume "sub^" "Tsub")
(use "Tsub")
;; Proof finished
(save "SubTotalVar")

;; SubEqToEqD
(set-goal "all sub1,sub2(sub1=sub2 -> sub1 eqd sub2)")
(ind)
;; Case Up
(assume "n")
(cases)
(assume "m")
(ng)
(assume "n=m")
(simp "n=m")
(use "InitEqD")
(assume "dB" "sub")
(ng)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
;; Case Dot
(assume "dB" "sub" "IHsub")
(cases)
(assume "n")
(ng)
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "dB1" "sub1")
(ng)
(assume "Conj")
(simp "IHsub" (pt "sub1"))
(assert "dB=dB1")
 (use "Conj")
(assume "dB=dB1")
(simp "dB=dB1")
(use "InitEqD")
(use "Conj")
;; Proof finished.
(save "SubEqToEqD")

(add-var-name "theta" (py "sub"))

(add-alg "pos" '("One" "pos") '("SZero" "pos=>pos") '("SOne" "pos=>pos"))
(add-totality "pos")

;; PosTotalVar
(set-goal "all pos TotalPos pos")
(ind)
(use "TotalPosOne")
(assume "pos" "Tpos")
(use "TotalPosSZero")
(use "Tpos")
(assume "pos" "Tpos")
(use "TotalPosSOne")
(use "Tpos")
;; Proof finished.
(save "PosTotalVar")

;; PosEqToEqD
(set-goal "all pos1,pos2(pos1=pos2 -> pos1 eqd pos2)")
(ind)
;; 2-4
(cases)
;; 5-7
(assume "Useless")
(use "InitEqD")
;; 6
(assume "pos1" "1=SZero p1")
(use "EfEqD")
(use "1=SZero p1")
;; 7
(assume "pos1" "1=SOne p1")
(use "EfEqD")
(use "1=SOne p1")
;; 3
(assume "pos1" "IH1")
(cases)
;; 14-16
(assume "SZero p1=1")
(use "EfEqD")
(use "SZero p1=1")
;; 15
(assume "pos2" "SZero p1=SZero p2")
(assert "pos1 eqd pos2")
 (use "IH1")
 (use "SZero p1=SZero p2")
(assume "pos1 eqd pos2")
(elim "pos1 eqd pos2")
(assume "pos^1")
(use "InitEqD")
;; 16
(assume "pos2" "SZero p1=SOne p2")
(use "EfEqD")
(use "SZero p1=SOne p2")
;; 4
(assume "pos1" "IH1")
(cases)
;; 29-31
(assume "SOne p1=1")
(use "EfEqD")
(use "SOne p1=1")
;; 30
(assume "pos2" "SOne p1=SZero p2")
(use "EfEqD")
(use "SOne p1=SZero p2")
;; 31
(assume "pos2" "SOne p1=SOne p2")
(assert "pos1 eqd pos2")
 (use "IH1")
 (use "SOne p1=SOne p2")
(assume "pos1 eqd pos2")
(elim "pos1 eqd pos2")
(assume "pos^1")
(use "InitEqD")
;; Proof finished.
(save "PosEqToEqD")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Definitions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(add-program-constant "Lift" (py "dB=>nat=>nat=>dB"))
(add-computation-rules
 "Lift(Var n)l k" "[if (n<l) (Var n) (Var(n+k))]"
 "Lift(r s)l k"   "Lift r l k(Lift s l k)"
 "Lift(Abs r)l k" "Abs(Lift r(l+1)k)")

;; LiftTotal
(set-totality-goal "Lift")
(use "AllTotalElim")
(ind)
(assume "n")
(use "AllTotalElim")
(assume "l")
(use "AllTotalElim")
(assume "k")
;; TotalDB(Lift(Var n)l k)
(ng)
(use "BooleIfTotal")
(use "BooleTotalVar")
(use "DBTotalVar")
(use "DBTotalVar")
;; Case App
(assume "r" "IHr" "s" "IHs")
(use "AllTotalElim")
(assume "l")
(use "AllTotalElim")
(assume "k")
;; TotalDB(Lift(r s)l k)
(ng)
(use "TotalDBApp")
(use "IHr")
(use "NatTotalVar")
(use "NatTotalVar")
(use "IHs")
(use "NatTotalVar")
(use "NatTotalVar")
;; Case Abs
(assume "r" "IHr")
(use "AllTotalElim")
(assume "l")
(use "AllTotalElim")
(assume "k")
;; TotalDB(Lift(Abs r)l k)
(ng)
(use "TotalDBAbs")
(use "IHr")
(use "NatTotalVar")
(use "NatTotalVar")
;; Proof finished.
(save-totality)

;; Substitution in the style of Hancock/Joachimski.  A substitution
;; theta consists of a list rs (of length n) of terms to be
;; substituted for the first n variables followed by an index k by
;; which the rest of the variables is to be lifted.

;; We also need a lifting for substitutions.

(add-program-constant "Sublift" (py "sub=>nat=>sub"))
(add-computation-rules
 "Sublift(Up m)n" "Up(m+n)"
 "Sublift(Dot r theta)n" "Dot(Lift r 0 n)(Sublift theta n)")

;; SubliftTotal
(set-totality-goal "Sublift")
(use "AllTotalElim")
(ind)
;; Case Up
(assume "m")
(use "AllTotalElim")
(assume "n")
;; TotalSub(Sublift(Up m)n)
(ng)
(use "SubTotalVar")
;; Case Dot
(assume "r" "theta" "IHtheta")
(use "AllTotalElim")
(assume "n")
;; TotalSub(Sublift(Dot r theta)n)
(ng)
(use "TotalSubDot")
(use "DBTotalVar")
(use "IHtheta")
(use "NatTotalVar")
;; Proof finished.
(save-totality)

;; Sub r theta substitutes theta in the term r

(add-program-constant "Sub" (py "dB=>sub=>dB"))
(add-computation-rules
 "Sub(Var n)(Up m)" "Var(n+m)"
 "Sub(Var 0)(Dot r theta)" "r"
 "Sub(Var(Succ n))(Dot r theta)" "Sub(Var n)theta"
 "Sub(r s)theta" "Sub r theta(Sub s theta)"
 "Sub(Abs r)theta" "(Abs(Sub r(Dot(Var 0)(Sublift theta 1))))")

;; SubTotal
(set-totality-goal "Sub")
(use "AllTotalElim")
(ind)
;; Case Var
(ind)
(use "AllTotalElim")
(cases)
(assume "m")
;; TotalDB(Sub(Var 0)(Up m))
(ng)
(use "DBTotalVar")
(assume "r" "theta")
;; TotalDB(Sub(Var 0)(Dot r theta))
(ng)
(use "DBTotalVar")
(assume "n" "IHn")
(use "AllTotalElim")
(cases)
(assume "m")
;; TotalDB(Sub(Var(Succ n))(Up m))
(ng)
(use "DBTotalVar")
(assume "r" "theta")
;; TotalDB(Sub(Var(Succ n))(Dot r theta))
(ng)
(use "IHn")
(use "SubTotalVar")
;; Case App
(assume "r" "IHr" "s" "IHs")
(use "AllTotalElim")
(assume "theta")
;; TotalDB(Sub(r s)theta)
(ng)
(use "TotalDBApp")
(use "IHr")
(use "SubTotalVar")
(use "IHs")
(use "SubTotalVar")
;; Case Abs
(assume "r" "IHr")
(use "AllTotalElim")
(assume "theta")
(ng)
(use "TotalDBAbs")
(use "IHr")
(use "SubTotalVar")
;; Proof finished.
(save-totality)

;; Spare appends 0 1 ... (m-1) to a substitution.

(add-program-constant "Spare" (py "nat=>sub=>sub"))
(add-computation-rules
 "Spare 0 theta" "theta"
 "Spare(Succ m)theta" "Spare m(Dot(Var m)theta)")

;; SpareTotal
(set-totality-goal "Spare")
(use "AllTotalElim")
(ind)
(use "AllTotalElim")
(assume "theta")
(use "SubTotalVar")
;; Step
(assume "n" "IH")
(use "AllTotalElim")
(assume "theta")
(ng)
(use "IH")
(use "SubTotalVar")
;; Proof finished.
(save-totality)

;; Composition on substitutions, written infix

(add-program-constant "Subcompose" (py "sub=>sub=>sub"))
(add-infix-display-string "Subcompose" "circ" 'mul-op)
(add-computation-rules
 "Up 0 circ theta" "theta"
 "Up(Succ n) circ Dot r theta" "Up n circ theta"
 "Up(Succ n)circ Up m" "Up(Succ n+m)"
 "Dot r theta circ theta1" "Dot(Sub r theta1)(theta circ theta1)")

;; SubcomposeTotal
(set-totality-goal "Subcompose")
(use "AllTotalElim")
(ind)
(ind)
(use "AllTotalElim")
(assume "theta")
(use "SubTotalVar")
(assume "n" "IHn")
(use "AllTotalElim")
(cases)
(assume "m")
(ng)
(use "SubTotalVar")
(assume "r" "theta")
(ng)
(use "IHn")
(use "SubTotalVar")
;; Step of main induction
(assume "r" "theta" "IHtheta")
(use "AllTotalElim")
(assume "theta1")
(ng)
(use "TotalSubDot")
(use "DBTotalVar")
(use "IHtheta")
(use "SubTotalVar")
;; Proof finished.
(save-totality)

(add-program-constant "Pushlist" (py "list dB=>sub=>sub"))
(add-computation-rules
 "Pushlist(Nil dB)theta" "theta"
 "Pushlist(r::rs)theta" "Dot r(Pushlist rs theta)")

;; PushlistTotal
(set-totality-goal "Pushlist")
(use "AllTotalElim")
(ind)
(use "AllTotalElim")
(assume "theta")
(ng)
(use "SubTotalVar")
;; Step
(assume "r" "rs" "IH")
(use "AllTotalElim")
(assume "theta")
(ng)
(use "TotalSubDot")
(use "DBTotalVar")
(use "IH")
(use "SubTotalVar")
;; Proof finished.
(save-totality)

(add-program-constant "Liftlist" (py "list dB=>nat=>nat=>list dB"))
(add-computation-rules
 "Liftlist(Nil dB)m n" "(Nil dB)"
 "Liftlist(r::rs)m n" "(Lift r m n)::(Liftlist rs m n)")

;; LiftlistTotal
(set-totality-goal "Liftlist")
(use "AllTotalElim")
(ind)
(use "AllTotalElim")
(assume "n")
(use "AllTotalElim")
(assume "m")
(ng)
(use "ListTotalVar")
;; Step
(assume "r" "rs" "IH")
(use "AllTotalElim")
(assume "m")
(use "AllTotalElim")
(assume "n")
(ng)
(use "TotalListCons")
(use "DBTotalVar")
(use "IH")
(use "NatTotalVar")
(use "NatTotalVar")
;; Proof finished.
(save-totality)

;; Beta conversion
(add-program-constant "Beta" (py "dB=>dB=>dB"))
(add-computation-rules
 "Beta(Var n)s" "Var n s"
 "Beta(r1 r2)s" "r1 r2 s"
 "Beta(Abs r)s" "Sub r(Dot s(Up 0))")

;; BetaTotal
(set-totality-goal "Beta")
(use "AllTotalElim")
(cases)
;; Case Var
(assume "n")
(use "AllTotalElim")
(assume "s")
;; TotalDB(Beta(Var n)s)
(ng)
(use "DBTotalVar")
;; Case App
(assume "r1" "r2")
(use "AllTotalElim")
(assume "s")
;; TotalDB(Beta(r1 r2)s)
(ng)
(use "DBTotalVar")
;; Case Abs
(assume "r")
(use "AllTotalElim")
(assume "s")
;; TotalDB(Beta(Abs r)s)
(ng)
(use "DBTotalVar")
;; Proof finished.
(save-totality)

;; Parallel reduction (Tait and Martin-Loef) converts all beta redexes
;; in parallel, working from the inside to the outside.  It does not
;; convert newly created redexes.  (In APAL 1998: Red reduces the rank
;; by one).

(add-program-constant "Red" (py "dB=>dB"))
(add-computation-rules
 "Red(Var n)" "Var n"
 "Red(Var n s)" "Var n(Red s)"
 "Red(r1 r2 s)" "Beta(Red(r1 r2))(Red s)"
 "Red(Abs r s)" "Beta(Abs(Red r))(Red s)"
 "Red(Abs r)" "Abs(Red r)")

;; RedTotal
(set-totality-goal "Red")
(use "AllTotalElim")
(ind)
;; Case Var
(assume "n")
;; TotalDB(Red(Var n))
(ng)
(use "DBTotalVar")
;; Case App
(cases)
(assume "n" "IHn" "s" "IHs")
;; TotalDB(Red(Var n s))
(ng)
(use "TotalDBApp")
(use "DBTotalVar")
(use "IHs")
(assume "r1" "r2" "IH" "s" "IHs")
;; TotalDB(Red(r1 r2 s))
(ng)
(use "BetaTotal")
(use "IH")
(use "IHs")
(assume "r" "IH" "s" "IHs")
;; TotalDB(Red(Abs r s))
(simp "Red3CompRule")
(use "BetaTotal")
(use "IH")
(use "IHs")
;; Case Abs
(assume "r" "IH")
;; TotalDB(Red(Abs r))
(ng)
(use "TotalDBAbs")
(use "IH")
;; Proof finished.
(save-totality)

;; Example: SKK reduces in 2 steps to identity.

(pp (pt "Abs(Abs(Var 1))")) ;K
(pp (pt "Abs(Abs(Abs(Var 2(Var 0)(Var 1(Var 0)))))")) ;S

(pp (nt (pt "Red(Red((Abs(Abs(Abs(Var 2(Var 0)(Var 1(Var 0))))))
                     (Abs(Abs(Var 1)))
                     (Abs(Abs(Var 1)))))")))
;; Abs(Var 0)

;; To state the Church-Rosser theorem we need one the step beta
;; reduction relation which reduces exactly one redex.

(add-ids (list (list "OneBeta" (make-arity (py "dB") (py "dB")) "pos"))
	 '("allnc r,s OneBeta(Abs r s)(Beta(Abs r)s)" "InitOneBeta")
	 '("allnc r,s,t(OneBeta r s -> OneBeta(r t)(s t))" "GenOneBetaLeft")
	 '("allnc r,s,t(OneBeta r s -> OneBeta(t r)(t s))" "GenOneBetaRight"))

;; Beta reduction is the reflexive transitive closure of OneBeta.

(add-var-name "x" "y" "z" (py "alpha"))
(add-pvar-name "R" (make-arity (py "alpha") (py "alpha")))
(add-ids (list (list "RTrCl" (make-arity (py "alpha") (py "alpha")) "list"))
	 '("allnc x^ RTrCl x^ x^" "InitRTrCl")
	 '("allnc x^,y^,z^(R x^ y^ -> RTrCl y^ z^ -> RTrCl x^ z^)" "GenRTrCl"))
(remove-var-name "x" "y" "z")
(remove-pvar-name "R")

;; Beta reduction r ->_beta s is written as
(pp (pf "(RTrCl (cterm (r^,s^) OneBeta r^ s^))r s"))

;; The type of r ->_beta s is (list pos), since pos is the type of OneBeta
(pp (formula-to-et-type (pf "(RTrCl (cterm (r^,s^) OneBeta r^ s^))r s")))

;; We now can state

;; ChurchRosser
(set-goal "all r,s1,s2(
(RTrCl (cterm (r^,s^) OneBeta r^ s^))r s1 ->
(RTrCl (cterm (r^,s^) OneBeta r^ s^))r s2 ->
ex t(
(RTrCl (cterm (r^,s^) OneBeta r^ s^))s1 t &
(RTrCl (cterm (r^,s^) OneBeta r^ s^))s2 t))")

;; Its type is dB=>dB=>dB=>list pos=>list pos=>dB@@list pos@@list pos

;; However, a formal proof still needs to be done.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Theorems
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; DBEqTrans
(set-goal "all r1,r2,r3(r1=r2 -> r2=r3 -> r1=r3)")
(assume "r1" "r2" "r3" "r1=r2")
(simp "r1=r2")
(assume "r2=r3")
(use "r2=r3")
;; Proof finished.
(save "DBEqTrans")

;; "DBCompatApp
(set-goal "all r1,r2,s1,s2(r1=r2 -> s1=s2 -> r1 s1 = r2 s2)")
(assume "r1" "r2" "s1" "s2" "r1=r2" "s1=s2")
(use "DBEqTrans" (pt "r1 s2"))
(use "s1=s2")
(use "r1=r2")
;; Proof finished.
(save "DBCompatApp")

;; Lift0RewRule
(set-goal "all r,k Lift r k 0=r")
(ind)
(assume "n" "k")
(ng)
(use "Truth")
;; Case App
(assume "r" "IHr" "s" "IHs" "k")
(ng)
(simp "IHr")
(simp "IHs")
(use "Truth")
;; Case Abs
(assume "r" "IHr" "k")
(ng)
(use "IHr")
;; Proof finished.
(add-rewrite-rule "Lift r k 0" "r")
;; (pp "Lift0RewRule")

;; Lift1RewRule
(set-goal "all r,l,k,k1 Lift(Lift r l k)l k1=Lift r l(k+k1)")
(ind)
(assume "n" "l" "k" "k1")
(cases (pt "n<l"))
(assume "n<l")
(ng)
(simp "n<l")
(ng)
(simp "n<l")
(use "Truth")
(assume "n<l -> F")
(ng)
(simp "n<l -> F")
(ng)
(assert "n+k<l -> F")
 (assume "n+k<l")
 (use "n<l -> F")
 (use "NatLeLtTrans" (pt "n+k"))
 (use "Truth")
 (use "n+k<l")
(assume "n+k<l -> F")
(simp "n+k<l -> F")
(use "Truth")
;; Case App
(assume "r" "IHr" "s" "IHs" "l" "k" "k1")
(ng)
(simp "IHr")
(simp "IHs")
(use "Truth")
;; Case Abs
(assume "r" "IHr" "l" "k" "k1")
(ng)
(use "IHr")
;; Proof finished.
(add-rewrite-rule "Lift(Lift r l k)l k1" "Lift r l(k+k1)")
;; (pp "Lift1RewRule")

;; Lift2RewRule
(set-goal "all r,l,k,k1 Lift(Lift r l k)(k+l)k1=Lift r l(k+k1)")
(ind)
;; Case Var
(ng)
(assume "n" "l" "k" "k1")
(cases (pt "n<l"))
(assume "n<l")
(ng)
(assert "n<k+l")
 (use "NatLtLeTrans" (pt "l"))
 (use "n<l")
 (use "Truth")
(assume "n<k+l")
(simp "n<k+l")
(use "Truth")
(assume "n<l -> F")
(ng)
(assert "n+k<k+l -> F")
 (assert "k+l=l+k")
  (use "NatPlusComm")
 (assume "k+l=l+k")
 (simp "k+l=l+k")
 (assume "n+k<l+k")
 (use "n<l -> F")
 (assert "n+k--k<l+k--k")
  (use "NatLtMonMinusLeft")
  (use "n+k<l+k")
  (use "Truth")
 (assume "n+k--k<l+k--k")
 (use "n+k--k<l+k--k")
(assume "n+k<k+l -> F")
(simp "n+k<k+l -> F")
(use "Truth")
;; Case App
(assume "r" "IHr" "s" "IHs" "l" "k" "k1")
(ng)
(simp "IHr")
(simp "IHs")
(use "Truth")
;; Case Abs
(assume "r" "IHr" "l" "k" "k1")
(ng)
;; (use "IHr") ;`unusable formula' ??  Reason: (-> ref.tex)
;; There are situations when use is not applicable but use-with is.
;; Consider the goal P(Succ(k+l)) in a context H: all l P(k+l).  Then
;; (use "H") cannot find the substitution l -> Succ l, but clearly
;; (use-with (pt "Succ l")) works.
(use-with "IHr" (pt "Succ l") (pt "k") (pt "k1"))
;; Proof finished.
(add-rewrite-rule "Lift(Lift r l k)(k+l)k1" "Lift r l(k+k1)")
;; (pp "Lift2RewRule")

;; Sublift0RewRule
(set-goal "all theta Sublift theta 0=theta")
(ind)
(assume "k")
(use "Truth")
(assume "r" "theta" "IHtheta")
(ng)
(use "IHtheta")
;; Proof finished.
(add-rewrite-rule "Sublift theta 0" "theta")
;; (pp "Sublift0RewRule")

;; SubliftTwice
(set-goal "all theta,n,m.Sublift(Sublift theta n)m=Sublift theta(n+m)")
(ind)
(assume "k" "n" "m")
(ng)
(use "Truth")
(assume "r" "theta" "IHtheta" "n" "m")
(ng)
(use "IHtheta")
;; Proof finished.
(save "SubliftTwice")

;; SubVarSpare
(set-goal "all m,k,theta Sub(Var(k+m))(Spare m theta)=Sub(Var k)theta")
(ind)
(assume "k" "theta")
(use "Truth")
(assume "m" "IHm" "k" "theta")
(ng)
(cut (pf "Succ(k+m)=Succ k+m"))
(assume "H1")
(simp "H1")
(use-with "IHm" (pt "Succ k") (pt "Dot(Var m)theta"))
(use "Truth")
;; Proof finished.
(save "SubVarSpare")

;; SubVarSpareLt
(set-goal "all m,k,theta(k<m -> Sub(Var k)(Spare m theta)=Var k)")
(ind)
(assume "k" "theta" "Absurd")
(use "EfAtom")
(use "Absurd")
(assume "m" "IHm" "k" "theta" "k<m+1")
(use "NatLtSuccCases" (pt "k") (pt "m"))
(use "k<m+1")
(ng)
(use "IHm")
(assume "k=m")
(simp "k=m")
(ng)
(use-with "SubVarSpare" (pt "m") (pt "0") (pt "Dot(Var m)theta"))
;; Proof finished.
(save "SubVarSpareLt")

;; DotVarSubliftSpare
(set-goal "all m,theta Dot(Var 0)(Sublift(Spare m theta)1)=
                       Spare(Succ m)(Sublift theta 1)")
(ind)
(assume "theta")
(use "Truth")
(assume "m" "IHm" "theta")
(ng)
(use-with "IHm" (pt "Dot(Var m)theta"))
;; Proof finished.
(save "DotVarSubliftSpare")

;; Joachimski's (2)
;; LiftEq
(set-goal "all r,n,m Lift r m n=Sub r(Spare m(Up(m+n)))")
(ind)
;; Case Var
(assume "k" "n" "m")
(ng)
(cases (pt "k<m"))
(assume "k<m")
(ng)
(inst-with-to "SubVarSpareLt" (pt "m") (pt "k") (pt "Up(m+n)") "k<m" "H1")
(simp "H1")
(use "Truth")
(assume "k<m -> F")
(ng)
(assert "k--m+m=k")
 (use "NatMinusPlusEq")
 (use "NatNotLtToLe")
 (use "k<m -> F")
(assume "k--m+m=k")
(assert "Var k=Var(k--m+m)")
 (simp "k--m+m=k")
 (use "Truth")
(assume "Var k=Var(k--m+m)")
(simp "Var k=Var(k--m+m)")
(simp "SubVarSpare")
(ng #t)
(simp "k--m+m=k")
(use "Truth")
;; App
(assume "r" "IHr" "s" "IHs" "n" "m")
(ng)
(inst-with-to "IHr" (pt "n") (pt "m") "IHrEq")
(simp "IHrEq")
(inst-with-to "IHs" (pt "n") (pt "m") "IHsEq")
(simp "IHsEq")
(use "Truth")
;; Abs
(assume "r" "IHr" "n" "m")
(ng)
(simp "DotVarSubliftSpare")
(simp "IHr")
(use "Truth")
;; Proof finished.
(save "LiftEq")

;; Subcompose0RewRule
(set-goal "all m,n Up m circ Up n=Up(m+n)")
(ind)
(assume "n")
(use "Truth")
(assume "m" "IHm" "n")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "Up m circ Up n" "Up(m+n)")
;; (pp "Subcompose0RewRule")

;; Joachimski's (3)
;; Subcompose1RewRule
(set-goal "all n,theta theta circ Up n=Sublift theta n")
(assume "n")
(ind)
(assume "m")
(ng)
(use "Truth")
(assume "r" "theta" "IHtheta")
(ng)
(simp "IHtheta")
(simp "LiftEq")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "theta circ Up n" "Sublift theta n")
;; (pp "Subcompose1RewRule")

;; Joachimski's (4)
;; LiftSubSpare
(set-goal "all r,m,theta,n
  Lift(Sub r(Spare m theta))m n=Sub r(Spare m(Sublift theta n))")

;; Counterexample:
;; r=Var 1, m=1, theta=Up 0, n=2
;; (pp (nt (pt "Lift(Sub(Var 1)(Spare 1(Up 0)))1 2"))) ;=> Var 0
;; (pp (nt (pt "Sub(Var 1)(Spare 1(Sublift(Up 0)2))"))) ;=> Var 2

;; Correction (4').  First an auxiliary proposition.

;; LiftSubSpareAux1
(set-goal "all theta,l,m,n Lift(Sub(Var l)(Sublift theta m))m n=
                           Sub(Var l)(Sublift theta(m+n))")
(ind)
(assume "k" "l" "m" "n")
(ng)
(assert "l+k+m<m -> F")
 (assume "l+k+m<m")
 (assert "m<m")
  (use "NatLeLtTrans" (pt "l+k+m"))
   (ng #t)
   (use "Truth")
   (use "l+k+m<m")
 (assume "m<m")
 (use "m<m")
(assume "l+k+m<m -> F")
(simp "l+k+m<m -> F")
(use "Truth")
;; Case App
(assume "s" "theta" "IHtheta")
(ind)
(assume "m" "n")
(ng)
(use-with "Lift2RewRule" (pt "s") (pt "0") (pt "m") (pt "n"))
(assume "l" "IHl" "m" "n")
(ng)
(use "IHtheta")
;; Proof finished.
(save "LiftSubSpareAux")

;; Now the corrected (4')
;; LiftSubSpare
(set-goal "all r,m,theta,n
  Lift(Sub r(Spare m(Sublift theta m)))m n=
  Sub r(Spare m(Sublift theta(m+n)))")
(ind)
;; Case Var
(assume "k" "m" "theta" "n")
(cases (pt "k<m"))
(assume "k<m")
(simp "SubVarSpareLt")
(simp "SubVarSpareLt")
(ng)
(simp "k<m")
(use "Truth")
(use "k<m")
(use "k<m")
(assume "k<m -> F")
(assert "k=(k--m)+m")
 (simp "NatMinusPlusEq")
 (use "Truth")
 (use "NatNotLtToLe")
 (use "k<m -> F")
(assume "k=(k--m)+m")
(simp "k=(k--m)+m")
(simp "SubVarSpare")
(simp "SubVarSpare")
(use "LiftSubSpareAux")
;; Case App
(assume "r" "IHr" "s" "IHs" "m" "theta" "n")
(ng)
(simp "IHr")
(simp "IHs")
(use "Truth")
;; Case Abs
(assume "r" "IHr" "m" "theta" "n")
(ng)
(simp "DotVarSubliftSpare")
(simp "SubliftTwice")
(simp (pf "m+1=Succ m"))
(simp "IHr")
(simp "DotVarSubliftSpare")
(simp "SubliftTwice")
(simp (pf "Succ m+n=m+n+1"))
(use "Truth")
(use "Truth")
(use "Truth")
;; Proof finished.
(save "LiftSubSpare")

;; Joachimski's (5)
;; CircSublift
(set-goal "all theta,theta1,n
  theta circ Sublift theta1 n=Sublift (theta circ theta1) n")
(ind)
(ind)
(assume "theta1" "n")
(use "Truth")
(assume "k" "IHk")
(cases)
(assume "l" "n")
(ng)
(use "Truth")
(assume "r" "theta1" "n")
(ng)
(use "IHk")
;; Case Dot
(assume "r" "theta" "IHtheta" "theta1" "n")
(ng)
(simp "IHtheta")
(ng)
(simp-with "<-" "LiftSubSpare" (pt "r") (pt "0") (pt "theta1") (pt "n"))
(use "Truth-Axiom")
;; Proof finished.
(save "CircSublift")

;; Sub0RewRule
(set-goal "all k,theta,rs
  Sub(Var(k+Lh rs))(Pushlist rs theta)=Sub(Var k)theta")
(assume "k" "theta")
(ind)
(use "Truth")
(assume "r" "rs" "IHrs")
(ng)
(use "IHrs")
;; Proof finished.
(add-rewrite-rule "Sub(Var(k+Lh rs))(Pushlist rs theta)" "Sub(Var k)theta")
;; (pp "Sub0RewRule")

;; Sublift1RewRule
(set-goal "all theta,n,rs
 Sublift(Pushlist rs theta)n=Pushlist(Liftlist rs 0 n)(Sublift theta n)")
(assume "theta" "n")
(ind)
(use "Truth")
(assume "r" "rs" "IHrs")
(ng)
(use "IHrs")
;; Proof finished.
(add-rewrite-rule "Sublift(Pushlist rs theta)n"
		  "Pushlist(Liftlist rs 0 n)(Sublift theta n)")
;; (pp "Sublift1RewRule")

;; LhLiftlist
(set-goal "all m,n,rs Lh rs=Lh(Liftlist rs m n)")
(assume "m" "n")
(ind)
(use "Truth")
(assume "r" "rs" "IHrs")
(ng)
(use "IHrs")
;; Proof finished.
(save "LhLiftlist")

;; Joachimski's (6)
;; SubLiftSpare
(set-goal "all r,m,rs,theta
  Sub(Lift r m Lh rs)(Spare m(Pushlist rs theta))=Sub r(Spare m theta)")
(ind)
;; Case Var
(assume "k" "m" "rs" "theta")
(cases (pt "k<m"))
(assume "k<m")
(ng)
(simp "k<m")
(ng)
(simp "SubVarSpareLt")
(simp "SubVarSpareLt")
(use "Truth")
(use "k<m")
(use "k<m")
(assume "k<m -> F")
(ng)
(simp "k<m -> F")
(ng)
(cut "k+Lh rs=k--m+Lh rs+m")
(assume "H3")
(simp "H3")
(cut "Sub(Var(k--m+Lh rs+m))(Spare m(Pushlist rs theta))=
      Sub(Var(k--m+Lh rs))(Pushlist rs theta)")
(assume "H4")
(ng)
(simp "H4")
(ng)
(cut "Var k=Var(k--m+m)")
(assume "H5")
(simp "H5")
(cut "Sub(Var(k--m+m))(Spare m theta)=Sub(Var(k--m))theta")
(assume "H6")
(simp "H6")
(use "Truth")
(use "SubVarSpare")
(assert "k--m+m=k")
 (simp "NatMinusPlusEq")
 (use "Truth")
 (use "NatNotLtToLe")
 (use "k<m -> F")
(assume "k--m+m=k")
(simp "k--m+m=k")
(use "Truth")
(use "SubVarSpare")
(assert "k--m+m=k")
 (simp "NatMinusPlusEq")
 (use "Truth")
 (use "NatNotLtToLe")
 (use "k<m -> F")
(assume "k--m+m=k")
(assert "k+Lh rs=k--m+m+Lh rs")
 (simp "k--m+m=k")
 (use "Truth")
(assume "k+Lh rs=k--m+m+Lh rs")
(simp "k+Lh rs=k--m+m+Lh rs")
(simp "<-" "NatPlus2RewRule")
(assert "m+Lh rs=Lh rs+m")
 (use "NatPlusComm")
(assume "m+Lh rs=Lh rs+m")
(simp "m+Lh rs=Lh rs+m")
(use "Truth")
;; App
(assume "r" "IHr" "s" "IHs" "m" "rs" "theta")
(ng)
(simp "IHr")
(simp "IHs")
(use "Truth")
;; Abs
(assume "r" "IHr" "m" "rs" "theta")
(ng)
(cut "(Dot(Var 0)(Sublift(Spare m(Pushlist rs theta))1))=
      Spare(Succ m)(Sublift(Pushlist rs theta)1)")
(assume "H8")
(simp "H8")
(cut "(Dot(Var 0)(Sublift(Spare m theta)1))=
      Spare(Succ m)(Sublift theta 1)")
(assume "H9")
(simp "H9")
(cut "Sublift(Pushlist rs theta)1=
      Pushlist(Liftlist rs 0 1)(Sublift theta 1)")
(assume "H10")
(simp "H10")
(cut "Lh rs=Lh(Liftlist rs 0 1)")
(assume "H11")
(simp "H11")
(use "IHr")
(use "LhLiftlist")
(use "Sublift0RewRule" (pt "theta"))
(use "DotVarSubliftSpare")
(use "DotVarSubliftSpare")
;; Proof finished.
(save "SubLiftSpare")

;; SubliftCircAux
(set-goal "all m,theta,rs Up(m+Lh rs)circ Pushlist rs theta=Up m circ theta")
(assume "m" "theta")
(ind)
(ng)
(use "Truth")
(assume "r" "rs" "IHr")
(ng)
(use "IHr")
;; Proof finished.
(save "SubliftCircAux")

;; Joachimski's (6')
;; "SubliftCirc
(set-goal "all theta,theta1,rs
  Sublift theta Lh rs circ Pushlist rs theta1=theta circ theta1")
(ind)
(assume "m" "theta1" "rs")
(ng)
(use "SubliftCircAux")
(assume "r" "theta" "IHtheta" "theta1" "rs")
(ng)
(cut "(Sub(Lift r 0 Lh rs)(Pushlist rs theta1))=Sub r theta1")
(assume "H1")
(simp "H1")
(cut "Sublift theta Lh rs circ Pushlist rs theta1=theta circ theta1")
(assume "H2")
(simp "H2")
(use "Truth")
(use "IHtheta")
(use-with "SubLiftSpare" (pt "r") (pt "0") (pt "rs") (pt "theta1"))
;; Proof finished.
(save "SubliftCirc")

;; SubVarUp
(set-goal "all theta,n,m Sub(Var(n+m))theta=Sub(Var n)(Up m circ theta)")
(ind)
(assume "k" "n" "m")
(ng)
(use "Truth")
(assume "r" "theta" "IHtheta" "n")
(cases)
(ng)
(use "Truth")
(assume "m")
(use "IHtheta")
;; Proof finished.
(save "SubVarUp")

;; Joachimski's (7)
;; SubSub
(set-goal "all r,theta,theta1 Sub(Sub r theta)theta1=Sub r(theta circ theta1)")
(ind)
(ind)
(ind)
(assume "m" "theta1")
(ng)
(use-with "SubVarUp" (pt "theta1") (pt "0") (pt "m"))
(assume "r" "theta" "IHtheta" "theta1")
(ng)
(use "Truth")
(assume "n" "IHn")
(ind)
(assume "k" "theta1")
(ng)
(use-with "SubVarUp" (pt "theta1") (pt "Succ n") (pt "k"))
(assume "r" "theta" "IHtheta")
(ng)
(use "IHn")
;; Case App
(assume "r" "IHr" "s" "IHs" "theta" "theta1")
(ng)
(simp "IHr")
(simp "IHs")
(use "Truth")
;; Case Abs
(assume "r" "IHr" "theta" "theta1")
(ng)
(cut "Sub(Sub r(Dot(Var 0)(Sublift theta 1)))(Dot(Var 0)(Sublift theta1 1))
    =Sub r((Dot(Var 0)(Sublift theta 1))circ(Dot(Var 0)(Sublift theta1 1)))")
(assume "H1")
(simp "H1")
(cut "Dot(Var 0)(Sublift theta 1)circ Dot(Var 0)(Sublift theta1 1)=
      Dot(Var 0)(Sublift(theta circ theta1)1)")
(assume "H2")
(simp "H2")
(use "Truth")
(ng)
(cut "Sublift theta 1 circ Dot(Var 0)(Sublift theta1 1)=
      theta circ(Sublift theta1 1)")
(assume "H3")
(simp "H3")
(use "CircSublift")
(use-with "SubliftCirc" (pt "theta") (pt "Sublift theta1 1")
	  (pt "(Var 0)::(Nil dB)"))
(use "IHr")
;; Proof finished.
(save "SubSub")

;; Joachimski's (7')
;; CircAssoc
(set-goal "all theta,theta1,theta2
  theta circ(theta1 circ theta2)=(theta circ theta1)circ theta2")
(ind)
(ind)
(ng)
(assume "theta1" "theta2")
(use "Truth")
(assume "k" "IHk")
(ind)
(ind)
(assume "theta2")
(ng)
(use "Truth")
(assume "n" "IHn")
(ind)
(ng)
(assume "l")
(use "Truth")
(assume "r" "theta2")
(assume "IHtheta2")
(ng)
(cut "Up(Succ k)circ(Up n circ theta2)=Up(Succ(k+n))circ theta2")
(assume "H1")
(simp "H1")
(use "Truth")
(use "IHn")
(assume "r" "theta1" "IHtheta1")
(ng)
(assume "theta2")
(use "IHk")
(assume "r" "theta" "IHtheta")
(assume "theta1" "theta2")
(ng)
(cut "theta circ(theta1 circ theta2)=theta circ theta1 circ theta2")
(assume "H2")
(simp "H2")
(cut "Sub r(theta1 circ theta2)=Sub(Sub r theta1)theta2")
(assume "H3")
(simp "H3")
(use "Truth")
(cut"Sub(Sub r theta1)theta2=Sub r(theta1 circ theta2)")
(assume "H4")
(simp "H4")
(use "Truth")
(use "SubSub")
(use "IHtheta")
;; Proof finished.
(save "CircAssoc")  

;; Joachimski's (8)
;; SubVarCirc
(set-goal "all n,theta Sub(Var n)theta=Sub(Var 0)(Up n circ theta)")
(ind)
(assume "theta")
(use "Truth-Axiom")
(assume "n" "IHn")
(cases)
(assume "m")
(use "Truth")
(assume "r" "theta")
(ng)
(use "IHn")
;; Proof finished.
(save "SubVarCirc")

;; SubLemma
(set-goal "all r,s,theta
 Sub(Sub r(Dot s(Up 0)))theta=Sub r(Dot(Sub s theta)theta)")
(assume "r" "s" "theta")
(simp "SubSub")
(ng)
(use "Truth")
;; Proof finished.
