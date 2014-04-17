;; (load "~/git/minlog/init.scm")

;; Contents
;; 1. A Cauchy real to an SDS. (PropA)
;; 2. An SDS to a Cauchy real. (PropB)
;; 3. Experiments.

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(libload "numbers.scm")
(libload "simpreal.scm")
(libload "real.scm")
(set! COMMENT-FLAG #t)

;; 1. A Cauchy real to an SDS
;; ==========================

(add-tvar-name "r") ;type of real numbers
(remove-var-name "x")
(add-var-name "x" (py "r"))

(add-alg "sd" '("Lft" "sd") '("Mid" "sd") '("Rht" "sd"))
(add-totality "sd")

(add-program-constant "SDToInt" (py "sd=>int"))
(add-computation-rules
 "SDToInt Lft" "IntN 1"
 "SDToInt Mid" "0"
 "SDToInt Rht" "1")

(set-goal (term-to-totality-formula (pt "SDToInt")))
(assume "sd^" "Td")
(elim "Td")
(ng #t)
(use "TotalIntIntNeg")
(use "TotalPosOne")
(ng #t)
(use "TotalIntIntZero")
(ng #t)
(use "TotalIntIntPos")
(use "TotalPosOne")
;; Proof finished.
(save "SDToIntTotal")

(add-algs "iv" '("II" "iv") '("C" "sd=>iv=>iv"))

(add-program-constant "Elem" (py "r=>rat=>nat=>boole"))
(add-program-constant "Z" (py "r")) ;zero
(add-program-constant "Av" (py "r=>sd=>r")) ;average
(add-program-constant "Va" (py "r=>sd=>r")) ;inverse of average

(add-ids (list (list "I" (make-arity (py "r")) "iv"))
	 '("I(Z r)" "InitI")
	 '("allnc x^ all sd(I x^ -> I((Av r)x^ sd))" "GenI"))

(add-co "I")
(pp (rename-variables (aconst-to-formula
		       (theorem-name-to-aconst "CoIClause"))))

;; Standard Split
(set-goal "all a(a<(IntN 1#4) orr (IntN 1#4)<=a & a<(1#4) oru (1#4)<=a)")
(cases)
(cases)
(assume "p" "q")
(ng #t)
(intro 1)
(cases (pt "SZero(SZero p)<q"))
(assume "4p<q")
(intro 0)
(split)
(use "Truth")
(use "Truth")
(assume "4p<q -> F")
(intro 1)
(use "PosNotLtToLe")
(use "4p<q -> F")
;; 4
(assume "p")
(ng #t)
(intro 1)
(intro 0)
(split)
(use "Truth")
(use "Truth")
;; 5
(assume "p" "q")
(ng #t)
(cases (pt "SZero(SZero p)<=q"))
(assume "4p<=q")
(intro 1)
(intro 0)
(split)
(use "Truth")
(use "Truth")
(assume "4p<=q -> F")
(intro 0)
(use "PosNotLeToLt")
(use "4p<=q -> F")
;; Proof finished.
(save "StandardSplit")

;; Axioms for PropA
(add-global-assumption
 "AxRealLeft"
 "all x^,a(a<(IntN 1#4) -> (Elem r)x^ a(PosToNat 2) ->
           (Elem r)x^(IntN 1#2)(PosToNat 1))")

(add-global-assumption
 "AxRealMiddle"
 "all x^,a((IntN 1#4)<=a -> a<(1#4) -> (Elem r)x^ a(PosToNat 2) ->
           (Elem r)x^(0#2)(PosToNat 1))")

(add-global-assumption
 "AxRealRight"
 "all x^,a((1#4)<=a -> (Elem r)x^ a(PosToNat 2) ->
           (Elem r)x^(1#2)(PosToNat 1))")

(add-global-assumption
 "AxAvVaIdent"
 "all x^,sd((Elem r)x^(SDToInt sd#2)(PosToNat 1) ->
             x^ eqd(Av r)((Va r)x^ sd)sd)")

(add-global-assumption
 "AxVaIntro"
 "all x^,sd,a,n((Elem r)x^(SDToInt sd#2)(PosToNat 1) ->
   (Elem r)x^ a(Succ n) -> (Elem r)((Va r)x^ sd)(2*a-SDToInt sd)n)")

;; Axioms for PropB
(add-global-assumption
 "AxRealBound"
 "allnc x^((Elem r)x^ (0#1) Zero)")

(add-global-assumption
 "AxRealZero"
 "all n (Elem r)(Z r)(0#1)n")

(add-global-assumption
 "AxAvIntro"
 "all x^,a,sd,n((Elem r)x^ a n ->
            (Elem r)((Av r)x^ sd)((a+SDToInt sd)/2)(Succ n))")

;; Split Property Lemma for Abstract Reals
;; SplitProp
(set-goal "allnc x^(all n exi a((Elem r)x^ a n) ->
                    exi sd (Elem r)x^(SDToInt sd#2)1)")
(assume "x^" "Q x")
(inst-with-to "Q x" (pt "Succ(Succ Zero)") "HQ2")
(by-assume "HQ2" "a" "Elem x a 2")

;; (assert "exl a (Elem r)x^ a(Succ(Succ Zero))")
;;  (use "HQ2")
;; (use "Id")
;; (elim)
;; (assume "a")
;; (assume "Elem x1 a 2")

(inst-with-to "StandardSplit" (pt "a") "SSa")
(elim "SSa")
;; a Left
(assume "a Left")
(intro 0 (pt "Lft"))
(use "AxRealLeft" (pt "a"))
(use "a Left")
(use "Elem x a 2")
(assume "SSa Mid Right")
(elim "SSa Mid Right")
;; a Middle
(assume "a Middle")
(intro 0 (pt "Mid"))
(use "AxRealMiddle" (pt "a"))
(use "a Middle")
(use "a Middle")
(use "Elem x a 2")
;; a Right
(assume "a Right")
(intro 0 (pt "Rht"))
(use "AxRealRight" (pt "a"))
(use "a Right")
(use "Elem x a 2")
;; Proof finished.
(save "SplitProp")

;; "PropA"
(set-goal "allnc x^(all n exi a((Elem r)x^ a n) -> CoI x^)")
(assume "x^" "Q x")
(coind "Q x")
;; ?_3:allnc x^(
;;      all n exl a (Elem r)x^ a n -> 
;;      x^ eqd(Z r) orr 
;;      exr x^0 
;;       ex sd(
;;        (CoI x^0 ord all n exl a (Elem r)x^0 a n) andl x^ eqd(Av r)x^0 sd))
(assume "x^1" "Q x1")
(intro 1)
(inst-with-to "SplitProp" (pt "x^1") "Q x1" "SP")
;; (by-assume "SP" "sd" "HElem")
(assert "exl sd (Elem r)x^1(SDToInt sd#2)(PosToNat 1)")
 (use "SP")
(use "Id")
(assume "ExHyp")
(by-assume "ExHyp" "sd" "HElem")
;; (elim "ExHyp")
;; (assume "sd" "HElem")
(intro 0 (pt "(Va r)x^1 sd"))
(ex-intro (pt "sd"))
(split)
;; CoI
(intro 1)
(assume "n")
(inst-with-to "Q x1" (pt "Succ n") "Hex")
(elim "Hex")
(assume "a" "HElem2")
(intro 0 (pt "2*a-(SDToInt sd)"))
(use "AxVaIntro")
(use "HElem")
(use "HElem2")
;; x^1 eqd ...
(use "AxAvVaIdent")
(use "HElem")
;; Proof finished.
(save "PropA")

;; 2. An SDS to a Cauchy real
;; ==========================

;; PropB
(set-goal "allnc x^(CoI x^ -> all n exi a((Elem r)x^ a n))")
(assume "x^" "CoI x" "n")
(cut "all n allnc x^(CoI x^ -> exl a (Elem r)x^ a n)")
 (assume "Hyp")
 (use "Hyp")
 (use "CoI x")
(ind)
;; n=0
(assume "x^0" "CoI x0")
(intro 0 (pt "0#1"))
(use "AxRealBound")
;; n -> n+1
(assume "m" "IH" "x^1" "CoI x1")
(inst-with-to "CoIClause" (pt "x^1") "CoI x1" "Cases x1")
(elim "Cases x1")
;; base case
(assume "x1 eqd Z")
(intro 0 (pt "0#1"))
(simp "x1 eqd Z")
(use "AxRealZero")
;; step case
(assume "Hex")
(by-assume "Hex" "x^2" "Hex sd")
(by-assume "Hex sd" "sd" "Hand")
(inst-with-to "Hand" 'left "CoI x2")
(inst-with-to "Hand" 'right "Eq")
(inst-with-to "IH" (pt "x^2") "CoI x2" "Hex a")
(by-assume "Hex a" "a" "HElem x1")
(intro 0 (pt "(a+SDToInt sd)/2"))
(simp "Eq")
(use "AxAvIntro")
(use "HElem x1")
;; Proof finished.
(save "PropB")

;; 3. Experiments
;; ==============

;; 3.1. Cauchy Sequence -> SDS
;; ===========================
(define eterm-a
  (proof-to-extracted-term (theorem-name-to-proof "PropA")))
(define neterm-a (nt eterm-a))

(animate "SplitProp")
(animate "StandardSplit")

;; extracting a program from PropA
;; (pp (rename-variables (nt neterm-a)))
(ppc (rename-variables (nt neterm-a)))
;; [as]
;;  (CoRec (nat=>rat)=>iv)as
;;  ([as0]
;;    Inr[let sd
;;         [case (as0(Succ(Succ Zero)))
;;          (k#p -> 
;;          [case k
;;            (p0 -> [case (SZero(SZero p0)<p) (True -> Mid) (False -> Rht)])
;;            (0 -> Mid)
;;            (IntN p0 -> 
;;            [case (SZero(SZero p0)<=p) (True -> Mid) (False -> Lft)])])]
;;         (sd@(InR nat=>rat iv)([n]2*as0(Succ n)-SDToInt sd))])

(animate "Id")

;; 0 in real with 5 times of unfolding
(define res0
  (nt (undelay-delayed-corec
       (make-term-in-app-form neterm-a (pt "[n]0#1")) 5)))
;; profile
;;     9 collections
;;     266 ms elapsed cpu time, including 3 ms collecting
;;     266 ms elapsed real time, including 1 ms collecting
;;     36120856 bytes allocated, including 37888976 bytes reclaimed

(pp res0)
;; C Mid(C Mid(C Mid(C Mid(C Mid( ...

;; 1 in real
(pp (nt (undelay-delayed-corec
	 (make-term-in-app-form neterm-a (pt "[n]1")) 5)))
;; C Rht(C Rht(C Rht(C Rht(C Rht(...

;; -1 in real
(pp (nt (undelay-delayed-corec
	 (make-term-in-app-form neterm-a (pt "[n]IntN 1")) 5)))
;; C Lft(C Lft(C Lft(C Lft(C Lft(...

;; 1/2 in real
(pp (nt (undelay-delayed-corec
	 (make-term-in-app-form neterm-a (pt "[n]1#2")) 5)))
;; C Rht(C Mid(C Mid(C Mid(C Mid(...

;; -1/2 in real
(pp (nt (undelay-delayed-corec
	 (make-term-in-app-form neterm-a (pt "[n]IntN 1#2")) 5)))
;; C Lft(C Mid(C Mid(C Mid(C Mid(...

;; approximated pi.
(define
  piterm5
  (nt (undelay-delayed-corec
       (make-term-in-app-form neterm-a (pt "[n]((22#7)/4)")) 5)))
;; profile:
;;     13 collections
;;     148 ms elapsed cpu time, including 36 ms collecting
;;     152 ms elapsed real time, including 31 ms collecting
;;     13949584 bytes allocated, including 13942248 bytes reclaimed

(pp piterm5)
;; C Rht(C Rht(C Mid(C Rht(C Lft(...

;; a rational number to the square root of it
(add-program-constant "sqrt" (py "rat=>nat=>rat"))
(add-program-constant "sqrtaux" (py "rat=>nat=>rat"))
(add-computation-rules
 "sqrtaux a Zero" "Succ Zero"
 "sqrtaux a(Succ n)" "((sqrtaux a n) + (a / (sqrtaux a n)))/2")
(add-computation-rule "sqrt a n" "sqrtaux a(Succ n)")

;; the square root of 1/2
'(
(pp (nt (undelay-delayed-corec
	 (make-term-in-app-form neterm-a (pt "sqrt (1#2)"))
	 5)))
)
;; profile:
;;     34865 collections
;;     211809 ms elapsed cpu time, including 20024 ms collecting
;;     212155 ms elapsed real time, including 20097 ms collecting
;;     37162113608 bytes allocated, including 37162579368 bytes reclaimed
;
;; C Rht
;; (C Rht
;;  (C Mid
;;   (C Lft
;;    (C Rht
;;     ((CoRec (nat=>rat)=>iv) ...

;; the square root of 1/3
'(
(pp (nt (undelay-delayed-corec
	 (make-term-in-app-form neterm-a (pt "sqrt (1#3)"))
	 5)))
)
;; profile
;;     34861 collections
;;     212246 ms elapsed cpu time, including 20266 ms collecting
;;     212589 ms elapsed real time, including 20237 ms collecting
;;     37159145600 bytes allocated, including 37158545928 bytes reclaimed
;; C Rht
;; (C Mid
;;  (C Rht
;;   (C Lft
;;    (C Mid
;;     ((CoRec (nat=>rat)=>iv) ...

;; 3.2. SDS -> Cauchy Sequence
;; ===========================
;; extracting a program from PropB
(define eterm-b (proof-to-extracted-term (theorem-name-to-proof "PropB")))
(define neterm-b (rename-variables (nt eterm-b)))
(ppc neterm-b)
'(
[iv,n]
 (Rec nat=>iv=>rat)n([iv0]0)
 ([n0,(iv=>rat)_0,iv1]
   [case (Des iv1)
     ((DummyL sd@@iv) -> 0)
     (Inr(sd@@iv)_2 -> ((iv=>rat)_0 right(sd@@iv)_2+SDToInt left(sd@@iv)_2)/2)])
 iv
)

(pp (nt (mk-term-in-app-form neterm-b
			     (pt "C Mid(C Mid(C Mid(C Mid(C Mid II))))")
			     (pt "PosToNat 5"))))
;; 0

(pp (nt (mk-term-in-app-form neterm-b
			     (pt "C Lft(C Lft(C Mid(C Mid(C Mid II))))")
			     (pt "PosToNat 5"))))
;; IntN 3#4

(pp (nt (mk-term-in-app-form neterm-b
			     (pt "C Mid(C Rht(C Rht(C Rht(C Rht II))))")
			     (pt "PosToNat 5"))))
;; 15#32

(pp (nt (mk-term-in-app-form neterm-b
			     (pt "C Lft(C Lft(C Lft(C Lft(C Lft II))))")
			     (pt "PosToNat 5"))))
;; IntN 31#32

(pp (nt (mk-term-in-app-form neterm-b
			     (pt "C Rht(C Mid(C Lft(C Lft(C Lft II))))")
			     (pt "PosToNat 5"))))
;; 9#32

(pp (nt (mk-term-in-app-form neterm-b
			     (pt "C Rht(C Rht(C Mid(C Lft II)))")
			     (pt "PosToNat 4"))))
;; 11#16

(pp (nt
     (mk-term-in-app-form
      neterm-b
      (pt "C Rht(C Rht(C Mid(C Lft(C Rht II))))")
      (pt "PosToNat 5"))))
;; 23#32
;; (* (/ 23. 32) 2)= 1.4375

(abs (- (sqrt (/ 1 2)) (/ 23. 32)))
;; 0.011643218813452427
;; the numerical error is smaller than 1/2^5 = 0.03125

;; 3.3. Haskell translation
;; ========================
'(
(terms-to-haskell-program "cauchysds.hs"
			  (list (list neterm-a "cauchysds")
 				(list neterm-b "sdscauchy")
				(list (pt "sqrt") "rattosqrt")))
)
;; This is the file cauchysds.hs:

;; module Main where

;; import Data.Ratio

;; ----- Algebras ------------------

;; type Nat = Integer

;; data Iv = II  | C Sd Iv
;;   deriving (Show, Read, Eq, Ord)

;; type Pos = Integer

;; data Sd = Lft  | Mid  | Rht 
;;   deriving (Show, Read, Eq, Ord)

;; ----- Recursion operators -------

;; ivCoRec :: (alpha1518 -> ((alpha1518 -> (Maybe (Sd, (Either Iv alpha1518)))) -> Iv))
;; ivCoRec e f = (case (f e) of
;;  { Nothing -> II ;
;;  Just g0 -> (C (fst g0) (case (snd g0) of
;;  { Left w1 -> w1 ;
;;  Right e2 -> (ivCoRec e2 f) })) })

;; natRec :: Nat -> a -> (Nat -> a -> a) -> a
;; natRec 0 g h = g
;; natRec n g h | n > 0 = h (n - 1) (natRec (n - 1) g h)

;; ivDestr :: (Iv -> (Maybe (Sd, Iv)))
;; ivDestr II = Nothing
;; ivDestr (C e w) = (Just (e, w))

;; ----- Program constants ---------

;; sDToInt :: (Sd -> Integer)
;; sDToInt Lft = -1
;; sDToInt Mid = 0
;; sDToInt Rht = 1

;; cSplitProp :: ((Nat -> Rational) -> Sd)
;; cSplitProp = (\ as0 -> (if ((numerator (as0 2)) > 0) then ((\ p3 -> (if (((p3 * 2) * 2) < (denominator (as0 2))) then Mid else Rht)) (numerator (as0 2))) else if ((numerator (as0 2)) == 0) then (Mid) else (((\ p3 -> (if (((p3 * 2) * 2) <= (denominator (as0 2))) then Mid else Lft)) (-(numerator (as0 2)))))))

;; natToInt :: (Nat -> Integer)
;; natToInt 0 = 0
;; natToInt nat | nat > 0 = ((natToInt (nat - 1)) + 1)

;; sqrtaux :: (Rational -> (Nat -> Rational))
;; sqrtaux a 0 = ((natToInt 1) % 1)
;; sqrtaux a n | n > 0 = (((sqrtaux a (n - 1)) + (a / (sqrtaux a (n - 1)))) / (2))

;; sqrt :: (Rational -> (Nat -> Rational))
;; sqrt a n = (sqrtaux a (n + 1))

;; ---------------------------------

;; cauchysds :: ((Nat -> Rational) -> Iv)
;; cauchysds = (\ as0 -> (ivCoRec as0 (\ as1 -> (Just (let sd2 = (cSplitProp as1) in (sd2, (Right (\ n3 -> (((2) * (as1 (n3 + 1))) - ((sDToInt sd2) % 1))))))))))

;; sdscauchy :: (Iv -> (Nat -> Rational))
;; sdscauchy = (\ iv -> (\ n -> (natRec n (\ iv0 -> (0)) (\ n0 -> (\ o -> (\ iv1 -> (case (ivDestr iv1) of
;;  { Nothing -> (0) ;
;;  Just h0 -> (((o (snd h0)) + ((sDToInt (fst h0)) % 1)) / (2)) })))) iv)))

;; rattosqrt :: (Rational -> (Nat -> Rational))
;; rattosqrt = Main.sqrt

;; ---------------------------------

;; main :: IO ()
;; main = putStrLn ""

;; To run cauchysds.hs type in terminal

;; $ ghc cauchysds.hs 
;; $ ghci cauchysds.hs

;; The square root of 1/2

;; Prelude Main> cauchysds(rattosqrt (1/2))

;; The result is (after interrupting by Ctrl-c twice)

;; C Rht (C Rht (C Mid (C Lft (C Rht (C Lft (C Rht (C Lft (C Mid (C Mid

;; Again we can input this term as an argument to neterm-b
(pp
 (nt
  (mk-term-in-app-form
   neterm-b
   (pt
    "C Rht(C Rht(C Mid(C Lft(C Rht(C Lft(C Rht(C Lft(C Mid(C Mid II)))))))))")
   (pt "PosToNat 10"))))

;; 181#256
;; (* (/ 181. 256) 2)= 1.4140625

(abs (- (sqrt (/ 1 2)) (/ 181. 256)))
;; 7.553118654757274e-5
;; the numerical error is smaller than 1/2^10 = 9.765625e-4

;; The square root of 1/3

;; Prelude Main> cauchysds(rattosqrt (1/3))

;; The result is (after interrupting by Ctrl-c twice)

;; C Rht (C Mid (C Rht (C Lft (C Mid (C Rht (C Mid (C Mid (C Mid (C Lft 

;; Again we can input this term as an argument to neterm-b
(pp
 (nt
  (mk-term-in-app-form
   neterm-b
   (pt
    "C Rht(C Mid(C Rht(C Lft(C Mid(C Rht(C Mid(C Mid(C Mid(C Lft II)))))))))")
   (pt "PosToNat 10"))))

;; 591#1024
;; (* (/ 591. 1024) 2)= 1.154296875

(abs (- (sqrt (/ 1 3)) (/ 591. 1024)))
;; 2.0183168962573106e-4
;; the numerical error is smaller than 1/2^10 = 9.765625e-4

;; We also have

;; Prelude Main> sdscauchy (cauchysds (rattosqrt (1/2))) 10
;; 181 % 256
;; Prelude Main> sdscauchy (cauchysds (rattosqrt (1/3))) 10
;; 591 % 1024
