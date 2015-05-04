;; 2015-04-25.  gray.scm

(load "~/git/minlog/init.scm")

;; To provide interesting streams of signed digits we also provide
;; concrete reals.  They will not be used in the conversion of signed
;; digit streams to Gray code and back.

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(libload "numbers.scm")
(libload "simpreal.scm")
(libload "real.scm")
(set! COMMENT-FLAG #t)

(remove-var-name "i" "j") ;will be used as variable names for sdtwo.
(remove-var-name "d") ;will be used as variable name for sd
(remove-var-name "a" "b") ;will be used as variable names for psd
(remove-var-name "c") ;will be used as variable name for four
(remove-var-name "x" "y" "z") ;will be used for the type variable r
(remove-var-name "p") ;will be used as variable name for ag
(remove-var-name "q") ;will be used as variable name for ah
(remove-var-name "L") ;will be used as a constructor for lr
(remove-token "L")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Signed digits 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Here we follow lib/numbers.scm for parsing and display, with
;; overloading and coercion.

;; We introduce the algebras sd (signed digits -1,0,1 written Lft,
;; Mid, Rht), psd (proper signed digits -1,1 written PLft, PRht) and
;; sdtwo (-2,-1,0,1,2 written LL, LT, MT, MR, RR).  We add their
;; totality predicates and variable names (d,e for sd, b for psd and
;; i,j for sdtwo).  For each algebra we prove its TotalVar property
;; (for instance SdTotalVar: all d TotalSd d), and that its decidable
;; equality = implies Leibniz equality eqd.

(add-alg "sd" '("Lft" "sd") '("Rht" "sd") '("Mid" "sd"))
(add-totality "sd")
(add-var-name "d" "e" (py "sd"))

;; SdTotalVar
(set-goal "all d TotalSd d")
(use "AllTotalIntro")
(assume "d^" "Td")
(use "Td")
;; Proof finished
(save "SdTotalVar")

;; SdEqToEqD
(set-goal "all d1,d2(d1=d2 -> d1 eqd d2)")
(cases)
(cases)
(assume "Useless")
(use "InitEqD")
(assume "Absurd")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "Absurd")
(assume "Absurd")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "Absurd")
(cases)
(assume "Absurd")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "Absurd")
(assume "Useless")
(use "InitEqD")
(assume "Absurd")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "Absurd")
(cases)
(assume "Absurd")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "Absurd")
(assume "Absurd")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "Absurd")
(assume "Useless")
(use "InitEqD")
;; Proof finished.
(save "SdEqToEqD")

(add-alg "psd" '("PLft" "psd") '("PRht" "psd"))
(add-totality "psd")
(add-var-name "a" "b" (py "psd"))

;; PsdTotalVar
(set-goal "all a TotalPsd a")
(use "AllTotalIntro")
(assume "a^" "Ta")
(use "Ta")
;; Proof finished.
(save "PsdTotalVar")

;; PsdEqToEqD
(set-goal "all a1,a2(a1=a2 -> a1 eqd a2)")
(cases)
(cases)
(assume "Useless")
(use "InitEqD")
(assume "Absurd")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "Absurd")
(cases)
(assume "Absurd")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "Absurd")
(assume "Useless")
(use "InitEqD")
;; Proof finished.
(save "PsdEqToEqD")

(add-alg "sdtwo"
	 '("LL" "sdtwo")
	 '("LT" "sdtwo")
	 '("MT" "sdtwo")
	 '("RT" "sdtwo")
	 '("RR" "sdtwo"))
(add-totality "sdtwo")
(add-var-name "i" "j" (py "sdtwo"))

;; SdtwoTotalVar
(set-goal "all i TotalSdtwo i")
(use "AllTotalIntro")
(assume "i^" "Ti")
(use "Ti")
;; Proof finished
(save "SdtwoTotalVar")

;; SdtwoEqToEqD
(set-goal "all i1,i2(i1=i2 -> i1 eqd i2)")
(cases)
(cases)
(assume "Useless")
(use "InitEqD")
(assume "Absurd")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "Absurd")
(assume "Absurd")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "Absurd")
(assume "Absurd")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "Absurd")
(assume "Absurd")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "Absurd")
(cases)
(assume "Absurd")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "Absurd")
(assume "Useless")
(use "InitEqD")
(assume "Absurd")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "Absurd")
(assume "Absurd")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "Absurd")
(assume "Absurd")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "Absurd")
(cases)
(assume "Absurd")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "Absurd")
(assume "Absurd")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "Absurd")
(assume "Useless")
(use "InitEqD")
(assume "Absurd")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "Absurd")
(assume "Absurd")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "Absurd")
(cases)
(assume "Absurd")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "Absurd")
(assume "Absurd")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "Absurd")
(assume "Absurd")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "Absurd")
(assume "Useless")
(use "InitEqD")
(assume "Absurd")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "Absurd")
(cases)
(assume "Absurd")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "Absurd")
(assume "Absurd")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "Absurd")
(assume "Absurd")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "Absurd")
(assume "Absurd")
(use "EFEqD")
(use "AtomToEqDTrue")
(use "Absurd")
(assume "Useless")
(use "InitEqD")
;; Proof finished.
(save "SdtwoEqToEqD")

;; Want coercions psd sub sd sub sdtwo, hence provide embeddings.

(add-program-constant "PsdToSd" (py "psd=>sd"))
(add-computation-rules
 "PsdToSd PLft" "Lft"
 "PsdToSd PRht" "Rht")

(set-totality-goal "PsdToSd")
(use "AllTotalElim")
(cases)
(use "SdTotalVar")
(use "SdTotalVar")
;; Proof finished.
(save-totality)

(add-program-constant "SdToSdtwo" (py "sd=>sdtwo"))
(add-computation-rules
 "SdToSdtwo Lft" "LT"
 "SdToSdtwo Rht" "RT"
 "SdToSdtwo Mid" "MT")

(set-totality-goal "SdToSdtwo")
(use "AllTotalElim")
(cases)
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
;; Proof finished.
(save-totality)

;; ALGEBRA-EDGE-TO-EMBED-TERM-ALIST associates to two-element lists
;; (type1 type2) a coercion function.  This is looked up if the type
;; of the arguments do not fit (i.e., are too small).  We can extend
;; this alist via add-item-to-algebra-edge-to-embed-term-alist .

(add-item-to-algebra-edge-to-embed-term-alist
 "psd" "sd"
 (let ((var (make-var (make-alg "psd") -1 t-deg-one "")))
   (make-term-in-abst-form
    var (make-term-in-app-form
         (make-term-in-const-form
          (pconst-name-to-pconst "PsdToSd"))
         (make-term-in-var-form var)))))

(add-item-to-algebra-edge-to-embed-term-alist
 "sd" "sdtwo"
 (let ((var (make-var (make-alg "psd") -1 t-deg-one "")))
   (make-term-in-abst-form
    var (make-term-in-app-form
         (make-term-in-const-form
          (pconst-name-to-pconst "SdToSdtwo"))
         (make-term-in-var-form var)))))

;; (alg-le? (make-alg "psd") (make-alg "sd"))
;; (alg-le? (make-alg "sd") (make-alg "sdtwo"))
;; (alg-le? (make-alg "psd") (make-alg "sdtwo"))

;; We add the (additive) inverse of psd, sd and sdtwo.

(add-program-constant "PsdInv" (py "psd=>psd") t-deg-zero)
(add-program-constant "SdInv" (py "sd=>sd") t-deg-zero)
(add-program-constant "SdtwoInv" (py "sdtwo=>sdtwo") t-deg-zero)

;; We add an overloaded multiplication.

(add-program-constant "PsdTimes" (py "psd=>psd=>psd") t-deg-zero)
(add-program-constant "SdTimes" (py "sd=>sd=>sd") t-deg-zero)

;; We add an overloaded addition.

(add-program-constant "PsdPlus" (py "psd=>psd=>sdtwo") t-deg-zero)
(add-program-constant "SdPlus" (py "sd=>sd=>sdtwo") t-deg-zero)

;; We define the tokens that are used by the parser

(add-token "inv" 'prefix-op (make-term-creator1 "inv" "psd"))
(add-token-and-type-to-name "inv" (py "psd") "PsdInv")
(add-token-and-type-to-name "inv" (py "sd") "SdInv")
(add-token-and-type-to-name "inv" (py "sdtwo") "SdtwoInv")

(add-token "times" 'mul-op (make-term-creator "times" "psd"))
(add-token-and-type-to-name "times" (py "psd") "PsdTimes")
(add-token-and-type-to-name "times" (py "sd") "SdTimes")

(add-token "plus" 'mul-op (make-term-creator "plus" "psd"))
(add-token-and-type-to-name "plus" (py "psd") "PsdPlus")
(add-token-and-type-to-name "plus" (py "sd") "SdPlus")

;; (pp (pt "inv a"))
;; PsdInv a
;; (pp (pt "inv d"))
;; SdInv d
;; (pp (pt "inv i"))
;; SdtwoInv i
;; (pp (pt "a1 times a2"))
;; PsdTimes a1 a2
;; (pp (pt "a times d"))
;; SdTimes(PsdToSd a)d
;; (pp (pt "d1 times d2"))
;; SdTimes d1 d2
;; (pp (pt "a1 plus a2"))
;; PsdPlus a1 a2
;; (pp (pt "a plus d"))
;; SdPlus(PsdToSd a)d
;; (pp (pt "d1 plus d2"))
;; SdPlus d1 d2

;; We add display creators

(add-display (py "psd") (make-display-creator1 "PsdInv" "inv" 'prefix-op))
(add-display (py "sd") (make-display-creator1 "SdInv" "inv" 'prefix-op))
(add-display (py "sdtwo") (make-display-creator1 "SdtwoInv" "inv" 'prefix-op))

(add-display (py "psd") (make-display-creator "PsdTimes" "times" 'mul-op))
(add-display (py "sd") (make-display-creator "SdTimes" "times" 'mul-op))

(add-display (py "sdtwo") (make-display-creator "PsdPlus" "plus" 'add-op))
(add-display (py "sdtwo") (make-display-creator "SdPlus" "plus" 'add-op))

;; (pp (pt "inv a"))
;; inv a
;; (pp (pt "inv d"))
;; inv d
;; (pp (pt "inv i"))
;; inv i
;; (pp (pt "a1 times a2"))
;; a1 times a2
;; (pp (pt "a times d"))
;; a times d
;; (pp (pt "d1 times d2"))
;; d1 times d2
;; (pp (pt "a1 plus a2"))
;; a1 plus a2
;; (pp (pt "a plus d"))
;; a plus d
;; (pp (pt "d1 plus d2"))
;; d1 plus d2

;; We define the program constants by their computation rules and
;; prove their totality.  We also prove and add useful rewrite rules.

(add-computation-rules
 "inv PLft" "PRht"
 "inv PRht" "PLft")

(set-totality-goal "PsdInv")
(use "AllTotalElim")
(cases)
(use "PsdTotalVar")
(use "PsdTotalVar")
;; Proof finished.
(save-totality)

(add-computation-rules
 "inv Lft" "Rht"
 "inv Rht" "Lft"
 "inv Mid" "Mid")

(set-totality-goal "SdInv")
(use "AllTotalElim")
(cases)
(use "SdTotalVar")
(use "SdTotalVar")
(use "SdTotalVar")
;; Proof finished.
(save-totality)

(add-computation-rules
 "inv LL" "RR"
 "inv LT" "RT"
 "inv MT" "MT"
 "inv RT" "LT"
 "inv RR" "LL")

(set-totality-goal "SdtwoInv")
(use "AllTotalElim")
(cases)
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
;; Proof finished.
(save-totality)

(add-computation-rules
 "PLft times PLft" "PRht"
 "PRht times a" "a"
 "a times PRht" "a")

(set-totality-goal "PsdTimes")
(use "AllTotalElim")
(cases)
(use "AllTotalElim")
(cases)
(use "PsdTotalVar")
(use "PsdTotalVar")
(use "AllTotalElim")
(assume "a")
(ng)
(use "PsdTotalVar")
;; Proof finished.
(save-totality)

(add-computation-rules
 "Lft times Lft" "Rht"
 "Rht times d" "d"
 "d times Rht" "d"
 "Mid times d" "Mid"
 "d times Mid" "Mid")

(set-totality-goal "SdTimes")
(use "AllTotalElim")
(cases)
(use "AllTotalElim")
(cases)
(use "SdTotalVar")
(use "SdTotalVar")
(use "SdTotalVar")
(use "AllTotalElim")
(assume "d")
(ng)
(use "SdTotalVar")
(use "AllTotalElim")
(assume "d")
(ng)
(use "SdTotalVar")
;; Proof finished.
(save-totality)

(add-computation-rules
 "PLft plus PLft" "LL"
 "PLft plus PRht" "MT"
 "PRht plus PLft" "MT"
 "PRht plus PRht" "RR")

(set-totality-goal "PsdPlus")
(use "AllTotalElim")
(cases)
(use "AllTotalElim")
(cases)
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "AllTotalElim")
(cases)
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
;; Proof finished.
(save-totality)

(add-computation-rules
 "Lft plus Lft" "LL"
 "Lft plus Mid" "LT"
 "Lft plus Rht" "MT"
 "Mid plus Lft" "LT"
 "Mid plus Mid" "MT"
 "Mid plus Rht" "RT"
 "Rht plus Lft" "MT"
 "Rht plus Mid" "RT"
 "Rht plus Rht" "RR")

(set-totality-goal "SdPlus")
(use "AllTotalElim")
(cases)
(use "AllTotalElim")
(cases)
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "AllTotalElim")
(cases)
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "AllTotalElim")
(cases)
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
;; Proof finished.
(save-totality)

;; We prove properties of these functions and take some of them as
;; rewrite rules.

(set-goal "all a inv inv a=a")
(cases)
(use "Truth")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "inv inv a" "a")

;; (pp "PsdInv0RewRule")
;; all a inv inv a=a

(set-goal "all d inv inv d=d")
(cases)
(use "Truth")
(use "Truth")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "inv inv d" "d")

(set-goal "all a PsdToSd(PsdInv a)=SdInv a")
(cases)
(use "Truth")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "PsdToSd(PsdInv a)" "SdInv a")

;; Notice that (PsdToSd a)plus(PsdToSd b)= PsdPlus a b is displayed as
;; a plus b=a plus b, although these are different terms (i.e., they
;; have no common reduct).  But we can prove their equality and then
;; add this as a rewrite rule.

(set-goal "all a,b (PsdToSd a)plus(PsdToSd b)= PsdPlus a b")
(cases)
(cases)
(use "Truth")
(use "Truth")
(cases)
(use "Truth")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "(PsdToSd a)plus(PsdToSd b)" "PsdPlus a b")

(set-goal "all i inv inv i=i")
(cases)
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "inv inv i" "i")

(set-goal "all d d times Lft=inv d")
(cases)
(use "Truth")
(use "Truth")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "d times Lft" "inv d")

(set-goal "all d Lft times d=inv d")
(cases)
(use "Truth")
(use "Truth")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "Lft times d" "inv d")

(set-goal "all a a times a=PRht")
(cases)
(use "Truth")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "a times a" "PRht")

(set-goal "all a,b inv a times b=inv(a times b)")
(cases)
(cases)
(use "Truth")
(use "Truth")
(cases)
(use "Truth")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "inv a times b" "inv(a times b)")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Abstract real numbers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(add-tvar-name "r") ;type of real numbers
(add-var-name "x" "y" "z" (py "r"))

(add-program-constant "Z" (py "r")) ;zero

(add-program-constant "UnaryMinusScheme" (py "r=>r"))
(add-prefix-display-string "UnaryMinusScheme" "~")

(add-program-constant "AverageRealSd" (py "r=>sd=>r"))
(add-infix-display-string "AverageRealSd" "av" 'add-op)

;; We add axioms, as rewrite rules.

(add-rewrite-rule "~ ~x^" "x^")
(add-rewrite-rule "~(Z r)" "(Z r)")

;; (add-global-assumption "MinusMinus" "all x^ ~ ~x^ eqd x^")
;; (add-global-assumption "MinusZ" "~(Z r)eqd(Z r)")

(add-program-constant "PsdTimesReal" (py "psd=>r=>r"))
(add-infix-display-string "PsdTimesReal" "***" 'mul-op)

;; We have axioms (also used as rewrite rules), and some helpful
;; rewrite rules, proved from the axioms.  The principles are (i)
;; associate products to the left, (ii) move products with average
;; inside (i.e., distribute), and (iii) move minus in products
;; outside.

;; Axioms:
;; PRhtTimes: PRht***x eqd x
;; PLftTimes: PLft***x eqd ~x
;; PsdTimesAv: a***(x av d) eqd a***x av a times d

;; Further rewrite rules proved from the axioms:
;; PsdTimesAssoc: a***(b***x) eqd (a times b)***x
;; MinusMinus: ~ ~x eqd x
;; MinusAv: ~(x av d) eqd ~x av inv d
;; MinusAvInv: ~(x av inv d)eqd~x av d
;; TimesRealInv: inv a***x eqd ~(a***x)
;; TimesRealMinus: a*** ~x eqd ~(a***x)

(add-rewrite-rule "PRht***x^" "x^")
(add-rewrite-rule "PLft***x^" "~x^")

(add-rewrite-rule "a***(x^ av PsdToSd b)" "a***x^ av PsdToSd(a times b)")
(add-rewrite-rule "a***(x^ av d)" "a***x^ av a times d")

;; We need two rewrite rules in this order.  If we only have the second
;; one, then (pp (nt (pt "a***(x^2 av PsdToSd b)"))) returns the term
;; a***x^2 av a times q, which cannot be parsed: the parser does not
;; lift the second argument of av.

;; PRhtTimes
(set-goal "all x^ PRht***x^ eqd x^")
(use "RewriteGA81")
;; Proof finished.
(save "PRhtTimes")

;; PLftTimes
(set-goal "all x^ PLft***x^ eqd~x^")
(use "RewriteGA82")
;; Proof finished.
(save "PLftTimes")

;; PsdTimesAv
(set-goal "all a,x^,d a***(x^ av d)eqd a***x^ av a times d")
(use "RewriteGA84")
;; Proof finished.
(save "PsdTimesAv")

;; PsdTimesAssoc
(set-goal "all x^,a,b a***(b***x^)eqd a times b***x^")
(assume "x^")
(cases)
(cases)
(use "InitEqD")
(use "InitEqD")
(cases)
(use "InitEqD")
(use "InitEqD")
;; Proof finished.
(save "PsdTimesAssoc")
(add-rewrite-rule "a***(b***x^)" "a times b***x^")

;; MinusMinus
(set-goal "allnc x^ ~ ~x^ eqd x^")
(assume "x^")
(simp "<-" "PLftTimes")
(simp "<-" "PLftTimes")
(ng)
(use "InitEqD")
;; Proof finished.
(save "MinusMinus")
(add-rewrite-rule "~ ~x^" "x^")

;; MinusAv
(set-goal "all x^,d ~(x^ av d) eqd~x^ av inv d")
(assume "x^" "d")
(inst-with-to "PsdTimesAv" (pt "PLft") (pt "x^") (pt "d") "PsdTimesAvInst")
(use "PsdTimesAvInst")
;; Proof finished.
(save "MinusAv")
(add-rewrite-rule "~(x^ av d)" "~x^ av inv d")

;; MinusAvInv
(set-goal "all x^,d ~(x^ av inv d)eqd~x^ av d")
(assume "x^" "d")
(inst-with-to "PsdTimesAv" (pt "PLft") (pt "x^") (pt "inv d") "PsdTimesAvInst")
(use "PsdTimesAvInst")
;; Proof finished.
(save "MinusAvInv")
(add-rewrite-rule "~(x^ av inv d)" "~x^ av d")

;; TimesRealInv
(set-goal "all x^,a inv a***x^ eqd ~(a***x^)")
(assume "x^")
(cases)
(ng)
(use "InitEqD")
(ng)
(use "InitEqD")
;; Proof finished.
(save "TimesRealInv")
(add-rewrite-rule "inv a***x^" "~(a***x^)")

;; TimesRealMinus:
(set-goal "all x^,a a*** ~x^ eqd ~(a***x^)")
(assume "x^")
(cases)
(ng)
(use "InitEqD")
(ng)
(use "InitEqD")
;; Proof finished.
(save "TimesRealMinus")
(add-rewrite-rule "a*** ~x^" "~(a***x^)")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Inductive predicate I
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(add-algs "iv" '("C" "sd=>iv=>iv"))
(add-var-name "v" (py "iv"))
(add-totality "iv")

;; We inductively define a set I of reals, by the single clause
;; GenI: I x -> I(x+d)/2 (d a signed digit).

(add-ids
 (list (list "I" (make-arity (py "r")) "iv"))
 '("allnc x^ all d(I x^ -> I(x^ av d))" "GenI"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; General properties of I
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; By the least-fixed-point (or elimination) axiom I is a fixed point.
;; Hence the inverse implication holds as well.

;; IClauseInv
(set-goal "allnc x^(I x^ -> exr x^0 ex d(I x^0 andl x^ eqd x^0 av d))")
(assume "x^" "Ix")
(elim "Ix")
(assume "x^1" "d" "Ix1" "Useless")
(intro 0 (pt "x^1"))
(ex-intro "d")
(split)
(use "Ix1")
(use "InitEqD")
;; Proof finished.
(save "IClauseInv")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [v][if v ([d,v0]d@v0)]

;; We now add the companion predicate CoI for I, meant to be the
;; greatest-fixed-point of the I clauses.

(add-co "I")
(pp "CoIClause")
;; allnc x^(CoI x^ -> exr x^0 ex d(CoI x^0 andl x^ eqd x^0 av d))

;; By the greatest-fixed-point (or coinduction) axiom CoI is a fixed
;; point.  Hence the inverse implication holds as well.

;; CoIClauseInv
(set-goal "allnc x^(exr x^0 ex d(CoI x^0 andl x^ eqd x^0 av d) -> CoI x^)")
(assume "x^" "ExHyp")
(coind "ExHyp")
(assume "x^1" "x1Prop")
(by-assume "x1Prop" "x^2" "x2Prop")
(by-assume "x2Prop" "d" "x2dProp")
(intro 0 (pt "x^2"))
(ex-intro "d")
(split)
(intro 0)
(use "x2dProp")
(use "x2dProp")
;; Proof finished.
(save "CoIClauseInv")

(define eterm (proof-to-extracted-term))
(add-var-name "dv" (py "sd@@iv"))
(define neterm (rename-variables (nt eterm)))
(define nneterm (rename-variables (nt (undelay-delayed-corec neterm 1))))
(pp nneterm)
;; [dv]C left dv right dv

;; We show that CoI satisfies the clause of I

;; GenCoI
(set-goal "allnc x^ all d(CoI x^ -> CoI(x^ av d))")
(assume "x^" "d" "CoIx")
(use "CoIClauseInv")
(intro 0 (pt "x^"))
(ex-intro "d")
(split)
(use "CoIx")
(use "InitEqD")
;; Proof finished.
(save "GenCoI")

(define eterm (proof-to-extracted-term))
(animate "CoIClauseInv")
(define neterm (rename-variables (nt eterm)))
(define nneterm (nt (undelay-delayed-corec neterm 1)))
(pp nneterm)
;; C

;; An immediate consequence is that the least-fixed-point is contained
;; in the greatest-fixed-point.

;; IToCoI
(set-goal "allnc x^(I x^ -> CoI x^)")
(assume "x^" "Ix")
(elim "Ix")
(assume "x^1" "d" "Useless" "CoIx1")
(use "GenCoI")
(use "CoIx1")
;; Proof finished.
(save "IToCoI")

(define eterm (proof-to-extracted-term))
(animate "GenCoI")
(define neterm (rename-variables (nt eterm)))
(define nneterm (rename-variables (nt (undelay-delayed-corec neterm 1))))
(pp nneterm)
;; [v](Rec iv=>iv)v([d,v0]C d)
;; This is extensionally equal to the identity on iv.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Inductive predicates G and H
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(add-algs (list "ag" "ah")
	  '("psd=>ag=>ag" "LR") ;for left/right (was GLR)
	  '("ah=>ag" "U") ;for undefined (was GM)
	  '("psd=>ag=>ah" "Fin") ;for finally (was HLR)
	  '("ah=>ah" "D")) ;for delay (was HM)

(display-alg "ag" "ah")
;; ag
;; 	LR:	psd=>ag=>ag
;; 	U:	ah=>ag
;; ah
;; 	Fin:	psd=>ag=>ah
;; 	D:	ah=>ah

(add-ids (list (list "G" (make-arity (py "r")) "ag")
	       (list "H" (make-arity (py "r")) "ah"))
	 '("allnc x^ all a(G x^ -> G(inv a***(x^ av Lft)))" "GenLR")
	 '("allnc x^(H x^ -> G(x^ av Mid))" "GenU")
	 '("allnc x^ all a(G x^ -> H(a***(x^ av Rht)))" "GenFin")
	 '("allnc x^(H x^ -> H(x^ av Mid))" "GenD"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; General properties of G
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; We add the companion predicate CoG for G, meant to be the
;; greatest-fixed-point of the G clauses.

(add-co "G")
(pp "CoGClause")
;; allnc x^(
;;  CoG x^ -> 
;;  exr x^0 ex a(CoG x^0 andl x^ eqd inv a***(x^0 av Lft)) ord 
;;  exr x^0(CoH x^0 andl x^ eqd x^0 av Mid))

;; By the greatest-fixed-point (or coinduction) axiom CoG is a fixed
;; point.  Hence the inverse implication holds as well.

;; CoGClauseInv
(set-goal "allnc x^(
 exr x^0 ex a(CoG x^0 andl x^ eqd inv a***(x^0 av Lft)) ord 
 exr x^0(CoH x^0 andl x^ eqd x^0 av Mid) -> CoG x^)")
(assume "x^" "Disj")
(coind "Disj"
       (pf "exr x^0 ex a(CoG x^0 andl x^ eqd a***(x^0 av Rht)) ord 
            exr x^0(CoH x^0 andl x^ eqd x^0 av Mid) -> CoH x^"))
(drop "Disj")
(assume "x^1" "x1Prop")
(elim "x1Prop")
(drop "x1Prop")
;; LR initial case
(assume "ExHypLR")
(by-assume "ExHypLR" "x^2" "x2Prop")
(by-assume "x2Prop" "a" "x2aProp")
(intro 0)
(intro 0 (pt "x^2"))
(ex-intro "a")
(split)
(intro 0)
(use "x2aProp")
(use "x2aProp")
(drop "x1Prop")
;; generating case
(assume "ExHypU")
(by-assume "ExHypU" "x^2" "x2Prop")
(intro 1)
(intro 0 (pt "x^2"))
(split)
(inst-with-to "x2Prop" 'left "CoHx2")
(drop "x2Prop")
(intro 0)
(use "CoHx2")
(use "x2Prop")
(drop "Disj")
;;
(assume "x^1" "x1Prop")
(elim "x1Prop")
(drop "x1Prop")
;; LR
(assume "ExHypLR")
(by-assume "ExHypLR" "x^2" "x2Prop")
(by-assume "x2Prop" "a" "x2aProp")
(intro 0)
(intro 0 (pt "x^2"))
(ex-intro (pt "a"))
(split)
(intro 0)
(use "x2aProp")
(use "x2aProp")
(drop "x1Prop")
;; Mid
(assume "ExHypD")
(by-assume "ExHypD" "x^2" "x2Prop")
(intro 1)
(intro 0 (pt "x^2"))
(split)
(intro 0)
(use "x2Prop")
(use "x2Prop")
;; Proof finished.
(save "CoGClauseInv")

(define eterm (proof-to-extracted-term))
(add-var-name "atpq" (py "psd@@ag ysum ah")) ;t for times
(define neterm (rename-variables (nt eterm)))
(ppc neterm)
;; [atpq]
;;  (CoRec psd@@ag ysum ah=>ag psd@@ag ysum ah=>ah)atpq
;;  ([atpq0]
;;    [case atpq0 (InL ap -> InL(left ap@InL right ap)) (InR q -> InR(InL q))])
;;  ([atpq0]
;;    [case atpq0 (InL ap -> InL(left ap@InL right ap)) (InR q -> InR(InL q))])

(define nneterm (rename-variables (nt (undelay-delayed-corec neterm 1))))
(pp nneterm)
;; [atpq][if atpq ([ap]LR left ap right ap) U]

;; GenCoGLR
(set-goal "allnc x^ all a(CoG x^ -> CoG(inv a***(x^ av Lft)))")
(assume "x^" "a" "CoGx")
(use "CoGClauseInv")
(intro 0)
(intro 0 (pt "x^"))
(ex-intro "a")
(split)
(use "CoGx")
(use "InitEqD")
;; Proof finished.
(save "GenCoGLR")

(define eterm (proof-to-extracted-term))
(animate "CoGClauseInv")
(define neterm (rename-variables (nt eterm)))
(define nneterm (nt (undelay-delayed-corec neterm 1)))
(pp nneterm)
;; LR

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Specific properties of CoG
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; CoGToCoIGen
(set-goal "allnc x^(ex a(CoG(a***x^) ord CoH(a***x^)) -> CoI x^)")
(assume "x^" "ExHyp")
(coind "ExHyp")
(assume "x^1" "x1Prop")
(by-assume "x1Prop" "a" "x1aProp")
(elim "x1aProp")
(drop "x1aProp")
;; Case CoG
(assume "CoGax1")
(inst-with-to "CoGClause" (pt "a***x^1") "CoGax1" "CoGClauseInst")
(elim "CoGClauseInst")
(drop "CoGClauseInst")
;; Case GLR
(assume "ExHypGLR")
(by-assume "ExHypGLR" "x^2" "x2Prop")
(by-assume "x2Prop" "b" "x2bProp")
(intro 0 (pt "inv a***(b***x^2)"))
(ex-intro "PsdToSd(a times b)")
(split)
(intro 1)
(ex-intro "inv a times b")
(intro 0)
(ng #t)
(use "x2bProp")
(assert "x^1 eqd a***(a*** x^1)")
 (use "InitEqD")
(assume "x1=aax1")
(simp "x1=aax1")
(simp "x2bProp")
(ng #t)
(use "InitEqD")
(drop "CoGClauseInst")
;; Case GM
(assume "ExHypGM")
(by-assume "ExHypGM" "x^2" "x2Prop")
(intro 0 (pt "a***x^2"))
(ex-intro "Mid")
(split)
(intro 1)
(ex-intro "a")
(intro 1)
(use "x2Prop")
(assert "x^1 eqd a***(a*** x^1)")
 (use "InitEqD")
(assume "x1=aax1")
(simp "x1=aax1")
(simp "x2Prop")
(ng #t)
(use "InitEqD")
;; Goal 9
(assume "CoHax1")
(inst-with-to "CoHClause" (pt "a***x^1") "CoHax1" "CoHClauseInst")
(elim "CoHClauseInst")
(drop "CoHClauseInst")
;; Case GLR
(assume "ExHypGLR")
(by-assume "ExHypGLR" "x^2" "x2Prop")
(by-assume "x2Prop" "b" "x2bProp")
(intro 0 (pt "a***(b***x^2)"))
(ex-intro "PsdToSd(a times b)")
(split)
(intro 1)
(ex-intro "a times b")
(intro 0)
(ng #t)
(use "x2bProp")
(assert "x^1 eqd a***(a*** x^1)")
 (use "InitEqD")
(assume "x1=aax1")
(simp "x1=aax1")
(simp "x2bProp")
(ng #t)
(use "InitEqD")
;; Case HM
(assume "ExHypHM")
(by-assume "ExHypHM" "x^2" "x2Prop")
(intro 0 (pt "a***x^2"))
(ex-intro "Mid")
(split)
(intro 1)
(ex-intro "a")
(intro 1)
(use "x2Prop")
(assert "x^1 eqd a***(a*** x^1)")
 (use "InitEqD")
(assume "x1=aax1")
(simp "x1=aax1")
(simp "x2Prop")
(ng #t)
(use "InitEqD")
;; Proof finished.
(save "CoGToCoIGen")

(define eterm (proof-to-extracted-term))
(add-var-name "p" (py "ag"))
(add-var-name "q" (py "ah"))
(add-var-name "apq" (py "psd@@(ag ysum ah)"))
(add-var-name "ap" (py "psd@@ag"))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)
;; [apq]
;;  (CoRec psd@@(ag ysum ah)=>iv)apq
;;  ([apq0]
;;    [case (right apq0)
;;      (InL p -> 
;;      [case (Des p)
;;        (InL ap -> 
;;        PsdToSd(left apq0 times left ap)@
;;        InR(inv(left apq0 times left ap)@InL right ap))
;;        (InR q -> Mid@InR(left apq0@InR q))])
;;      (InR q -> 
;;      [case (Des q)
;;        (InL ap -> 
;;        PsdToSd(left apq0 times left ap)@
;;        InR(left apq0 times left ap@InL right ap))
;;        (InR q0 -> Mid@InR(left apq0@InR q0))])])

(pp (term-to-type (pt "(CoRec psd@@(ag ysum ah)=>iv)")))
;; psd@@(ag ysum ah)=>(psd@@(ag ysum ah)=>sd@@(iv ysum psd@@(ag ysum ah)))=>iv

;; CoGToCoI
(set-goal "allnc x^ all a(CoG(a***x^) -> CoI x^)")
(assume "x^" "a" "CoGax")
(use "CoGToCoIGen")
(ex-intro "a")
(intro 0)
(use "CoGax")
;; Proof finished.
(save "CoGToCoI")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [a,p]cCoGToCoIGen(a@InL p)
(animate "CoGToCoIGen")
(define neterm-gtos (rename-variables (nt eterm)))
(ppc neterm-gtos)
;; [a,p]
;;  (CoRec psd@@(ag ysum ah)=>iv)(a@InL p)
;;  ([apq]
;;    [case (right apq)
;;      (InL p0 -> 
;;      [case (Des p0)
;;        (InL ap -> 
;;        PsdToSd(left apq times left ap)@
;;        InR(inv(left apq times left ap)@InL right ap))
;;        (InR q -> Mid@InR(left apq@InR q))])
;;      (InR q -> 
;;      [case (Des q)
;;        (InL ap -> 
;;        PsdToSd(left apq times left ap)@
;;        InR(left apq times left ap@InL right ap))
;;        (InR q0 -> Mid@InR(left apq@InR q0))])])

;; CoIToCoG
(set-goal "allnc x^ (ex a CoI(a***x^) -> CoG x^)")
(assume "x^" "ExHyp")
(coind "ExHyp" (pf "ex a CoI(a***x^) -> CoH x^"))
;; 
(assume "x^1" "x1Prop")
(by-assume "x1Prop" "a1" "x1a1Prop")
(inst-with-to "CoIClause" (pt "a1***x^1") "x1a1Prop" "CoIClauseInst")
(elim "CoIClauseInst")
(drop "CoIClauseInst")
;;
(assume "x^2" "x2Prop")
(by-assume "x2Prop" "d" "x2dProp")
(cases (pt "d"))
;; Case d=Lft
(assume "d=Lft")
(intro 0)
(intro 0 (pt "x^2"))
(ex-intro "inv a_1")
(split)
(intro 1)
(ex-intro "PRht")
(use "x2dProp")
(simp "<-" "d=Lft")
(simp "<-" "x2dProp")
(ng #t)
(use "InitEqD")
;; Case d=Rht
(assume "d=Rht")
(intro 0)
(intro 0 (pt "~x^2"))
(ex-intro "a_1")
(split)
(intro 1)
(ex-intro "PLft")
(ng #t)
(use "x2dProp")
(assert "x^1 eqd a1***(a1*** x^1)")
 (use "InitEqD")
(assume "x1=a1a1x1")
(simp "x1=a1a1x1")
(simp "x2dProp")
(simp "d=Rht")
(ng #t)
(use "InitEqD")
;; Case d=Mid
(assume "d=Mid")
(intro 1)
(intro 0 (pt "a1***x^2"))
(split)
(intro 1)
(ex-intro "a_1")
(use "x2dProp")
(assert "x^1 eqd a1***(a1*** x^1)")
 (use "InitEqD")
(assume "x1=a1a1x1")
(simp "x1=a1a1x1")
(simp "x2dProp")
(simp "d=Mid")
(ng #t)
(use "InitEqD")
;; Goal 4
(assume "x^1" "x1Prop")
(by-assume "x1Prop" "a" "x1aProp")
(inst-with-to "CoIClause" (pt "a***x^1") "x1aProp" "CoIClauseInst")
(elim "CoIClauseInst")
(drop "CoIClauseInst")
(assume "x^2" "x2Prop")
(by-assume "x2Prop" "d" "x2dProp")
(cases (pt "d"))
;; Case d=Lft
(assume "d=Lft")
(intro 0)
(intro 0 (pt "~x^2"))
(ex-intro "inv a")
(split)
(intro 1)
(ex-intro "PLft")
(ng #t)
(use "x2dProp")
(assert "x^1 eqd a***(a*** x^1)")
 (use "InitEqD")
(assume "x1=aax1")
(simp "x1=aax1")
(simp "x2dProp")
(simp "d=Lft")
(ng #t)
(use "InitEqD")
(drop "CoIClauseInst")
;; Case d=Rht
(assume "d=Rht")
(intro 0)
(intro 0 (pt "x^2"))
(ex-intro "a")
(split)
(intro 1)
(ex-intro "PRht")
(use "x2dProp")
(assert "x^1 eqd a***(a*** x^1)")
 (use "InitEqD")
(assume "x1=aax1")
(simp "x1=aax1")
(simp "x2dProp")
(simp "d=Rht")
(use "InitEqD")
;; Case d=Mid
(assume "d=Mid")
(intro 1)
(intro 0 (pt "a***x^2"))
(split)
(intro 1)
(ex-intro "a")
(use "x2dProp")
(assert "x^1 eqd a***(a*** x^1)")
 (use "InitEqD")
(assume "x1=aax1")
(simp "x1=aax1")
(simp "x2dProp")
(simp "d=Mid")
(use "InitEqD")
;; Proof finished.
(save "CoIToCoG")

(define eterm (proof-to-extracted-term))
(add-var-name "bv" (py "psd@@iv")) ;av is used for average
(define neterm-stog (rename-variables (nt eterm)))
(ppc neterm-stog)
;; [bv]
;;  (CoRec psd@@iv=>ag psd@@iv=>ah)bv
;;  ([bv0]
;;    [case (left Des right bv0)
;;      (Lft -> InL(inv left bv0@InR(PRht@right Des right bv0)))
;;      (Rht -> InL(left bv0@InR(PLft@right Des right bv0)))
;;      (Mid -> InR(InR(left bv0@right Des right bv0)))])
;;  ([bv0]
;;    [case (left Des right bv0)
;;      (Lft -> InL(inv left bv0@InR(PLft@right Des right bv0)))
;;      (Rht -> InL(left bv0@InR(PRht@right Des right bv0)))
;;      (Mid -> InR(InR(left bv0@right Des right bv0)))])

(pp (term-to-type (pt "(CoRec psd@@iv=>ag psd@@iv=>ah)")))
;; psd@@iv=>
;; (psd@@iv=>psd@@(ag ysum psd@@iv)ysum ah ysum psd@@iv)=>
;; (psd@@iv=>psd@@(ag ysum psd@@iv)ysum ah ysum psd@@iv)=>ag

;; We add another example, which uses the fact that our coinductive
;; definitions are in strengthened form.

;; CoGMinus
(set-goal "allnc x^(CoG(~x^) -> CoG x^)")
(assume "x^" "CoG-x")
(coind "CoG-x" (pf "CoH(~x^) -> CoH x^"))
(assume "x^1" "CoG-x1")
(inst-with-to "CoGClause" (pt "~x^1") "CoG-x1" "Disj")
(elim "Disj")
(drop "Disj")
;; LR generating case
(assume "ExHyp")
(by-assume "ExHyp" "x^2" "x2Prop")
(by-assume "x2Prop" "a" "x2aProp")
(intro 0)
(intro 0 (pt "x^2"))
(ex-intro "inv a")
(split)
(intro 0)
(use "x2aProp")
(assert "x^1 eqd ~ ~x^1")
 (ng #t)
 (use "InitEqD")
(assume "Assertion")
(simp "Assertion")
(drop "Assertion")
(simp "x2aProp")
(ng #t)
(use "InitEqD")
(drop "Disj")
;; middle generating case
(assume "ExHyp")
(by-assume "ExHyp" "x^2" "x2Prop")
(intro 1)
(intro 0 (pt "~x^2"))
(split)
(intro 1)
(ng #t)
(use "x2Prop")
(assert "x^1 eqd ~ ~x^1")
 (ng #t)
 (use "InitEqD")
(assume "Assertion")
(simp "Assertion")
(drop "Assertion")
(simp "x2Prop")
(ng #t)
(use "InitEqD")
;; Goal 4
(assume "x^1" "CoH-x1")
(inst-with-to "CoHClause" (pt "~x^1") "CoH-x1" "Disj")
(elim "Disj")
(drop "Disj")
;; LR generating case
(assume "ExHyp")
(by-assume "ExHyp" "x^2" "x2Prop")
(by-assume "x2Prop" "a" "x2aProp")
(intro 0)
(intro 0 (pt "x^2"))
(ex-intro "inv a")
(split)
(intro 0)
(use "x2aProp")
(assert "x^1 eqd ~ ~x^1")
 (ng #t)
 (use "InitEqD")
(assume "Assertion")
(simp "Assertion")
(drop "Assertion")
(simp "x2aProp")
(ng #t)
(use "InitEqD")
(drop "Disj")
;; middle generating case
(assume "ExHyp")
(by-assume "ExHyp" "x^2" "x2Prop")
(intro 1)
(intro 0 (pt "~x^2"))
(split)
(intro 1)
(ng #t)
(use "x2Prop")
(assert "x^1 eqd ~ ~x^1")
 (ng #t)
 (use "InitEqD")
(assume "Assertion")
(simp "Assertion")
(drop "Assertion")
(simp "x2Prop")
(ng #t)
(use "InitEqD")
;; Proof finished.
(save "CoGMinus")

(define eterm (proof-to-extracted-term))
(animate "CoGClause")
(animate "CoHClause")
(define neterm-gminus (rename-variables (nt eterm)))
(ppc neterm-gminus)
;; [p]
;;  (CoRec ag=>ag ah=>ah)p
;;  ([p0]
;;    [case (Des p0)
;;      (InL ap -> InL(inv left ap@InL right ap))
;;      (InR q -> InR(InR q))])
;;  ([q]
;;    [case (Des q)
;;      (InL ap -> InL(inv left ap@InL right ap))
;;      (InR q0 -> InR(InR q0))])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Average for signed digits
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; We adapt average.scm to the present setting.

(add-program-constant "AverageReal" (py "r=>r=>r"))
(add-infix-display-string "AverageReal" "avr" 'add-op)

(add-program-constant "Av" (py "r=>r=>sdtwo=>r"))

(add-global-assumption
 "AverageRealAverage"
 "all x^,y^,d,e x^ av d avr(y^ av e)eqd(Av r)x^ y^(d plus e)")

;; (add-global-assumption "AverageZero" "(Z r)av Mid eqd(Z r)")
;; (add-global-assumption "AvZero" "(Av r)(Z r)(Z r)MT eqd(Z r)")

;; XSubY
(set-goal "allnc x^,y^(
      CoI x^ -> 
      CoI y^ -> 
      exr x^1,y^1 ex i(CoI x^1 & CoI y^1 & x^ avr y^ eqd(Av r)x^1 y^1 i))")
(assume "x^" "y^" "CoIx" "CoIy")
(inst-with-to "CoIClause" (pt "x^") "CoIx" "CoIClauseInstx")
(by-assume "CoIClauseInstx" "x^1" "x1Prop")
(by-assume "x1Prop" "d" "x1dProp")
(inst-with-to "CoIClause" (pt "y^") "CoIy" "CoIClauseInsty")
(by-assume "CoIClauseInsty" "y^1" "y1Prop")
(by-assume "y1Prop" "e" "y1eProp")
(intro 0 (pt "x^1"))
(intro 0 (pt "y^1"))
(ex-intro "d plus e")
(msplit)
(simp "x1dProp")
(simp "y1eProp")
(use "AverageRealAverage")
(use "y1eProp")
(use "x1dProp")
;; Proof finished.
(save "XSubY")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [v,v0]left Des v plus left Des v0@right Des v@right Des v0

;; This term can be read as follows.  Given v, v0, destruct both.
;; Both are composed, i.e., of the form dv1 and dv2.  Take their
;; components d1,v1 and d2,v2.  Then the result is d1 plus d2 pair v1
;; pair v2.

;; We define J: sd=>sd=>sdtwo=>sdtwo and K: sd=>sd=>sdtwo=>sd such that
;; d+e+2*i=J d e i+4*(K d e i).  For J'(d+e+2*i) := J d e i and
;; K'(d+e+2*i) := K d e i we want

;; J' k = [if (rem k 4=3) 1 (sg k)*(rem k 4)]
;; K' k = [if (abs k<=2) 0 (sg k)]

;; Hence J' should map
;; -6 -> -2
;; -5 -> -1
;; -4 -> 0
;; -3 -> 1
;; -2 -> -2
;; -1 -> -1
;; 0 -> 0
;; 1 -> 1
;; 2 -> 2
;; 3 -> -1
;; 4 -> 0
;; 5 -> 1
;; 6 -> 2

;; Similarly K' should map
;; -6 -> -1
;; -5 -> -1
;; -4 -> -1
;; -3 -> -1
;; -2 -> 0
;; -1 -> 0
;; 0 -> 0
;; 1 -> 0
;; 2 -> 0
;; 3 -> 1
;; 4 -> 1
;; 5 -> 1
;; 6 -> 1

;; k    J'k  K'k  J'k+4*K'k
;; -6   -2   -1   -6
;; -5   -1   -1   -5
;; -4   0    -1   -4
;; -3   1    -1   -3
;; -2   -2   0    -2
;; -1   -1   0    -1
;; 0    0    0    0
;; 1    1    0    1
;; 2    2    0    2
;; 3    -1   1    3
;; 4    0    1    4
;; 5    1    1    5
;; 6    2    1    6

;; Then for abs k<=6 we have k=J' k+K' k:
;; -6=-2+4*(-1)
;; -5=-1+4*(-1)
;; -4=0+4*(-1)
;; -3=1+4*(-1)
;; -2=-2
;; -1=-1
;; 0=0
;; 1=1
;; 2=2
;; 3=-1+4
;; 4=0+4
;; 5=1+4
;; 6=2+4

(add-program-constant "J" (py "sd=>sd=>sdtwo=>sdtwo"))

(add-computation-rules
 "J Lft Lft LL" "LL"
 "J Lft Lft LT" "MT"
 "J Lft Lft MT" "LL"
 "J Lft Lft RT" "MT"
 "J Lft Lft RR" "RR"

 "J Lft Mid LL" "LT"
 "J Lft Mid LT" "RT"
 "J Lft Mid MT" "LT"
 "J Lft Mid RT" "RT"
 "J Lft Mid RR" "LT"

 "J Lft Rht LL" "MT"
 "J Lft Rht LT" "LL"
 "J Lft Rht MT" "MT"
 "J Lft Rht RT" "RR"
 "J Lft Rht RR" "MT"

 "J Mid Lft LL" "LT"
 "J Mid Lft LT" "RT"
 "J Mid Lft MT" "LT"
 "J Mid Lft RT" "RT"
 "J Mid Lft RR" "LT"

 "J Mid Mid LL" "MT"
 "J Mid Mid LT" "LL"
 "J Mid Mid MT" "MT"
 "J Mid Mid RT" "RR"
 "J Mid Mid RR" "MT"

 "J Mid Rht LL" "RT"
 "J Mid Rht LT" "LT"
 "J Mid Rht MT" "RT"
 "J Mid Rht RT" "LT"
 "J Mid Rht RR" "RT"

 "J Rht Lft LL" "MT"
 "J Rht Lft LT" "LL"
 "J Rht Lft MT" "MT"
 "J Rht Lft RT" "RR"
 "J Rht Lft RR" "MT"

 "J Rht Mid LL" "RT"
 "J Rht Mid LT" "LT"
 "J Rht Mid MT" "RT"
 "J Rht Mid RT" "LT"
 "J Rht Mid RR" "RT"

 "J Rht Rht LL" "LL"
 "J Rht Rht LT" "MT"
 "J Rht Rht MT" "RR"
 "J Rht Rht RT" "MT"
 "J Rht Rht RR" "RR")

;; JTotal
(set-totality-goal "J")
(use "AllTotalElim")
(cases)
(use "AllTotalElim")
(cases)
(use "AllTotalElim")
(cases)
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "AllTotalElim")
(cases)
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "AllTotalElim")
(cases)
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "AllTotalElim")
(cases)
(use "AllTotalElim")
(cases)
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "AllTotalElim")
(cases)
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "AllTotalElim")
(cases)
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "AllTotalElim")
(cases)
(use "AllTotalElim")
(cases)
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "AllTotalElim")
(cases)
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "AllTotalElim")
(cases)
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
(use "SdtwoTotalVar")
;; Proof finished.
(save-totality)

(add-program-constant "K" (py "sd=>sd=>sdtwo=>sd"))
(add-computation-rules
 "K Lft Lft LL" "Lft"
 "K Lft Lft LT" "Lft"
 "K Lft Lft MT" "Mid"
 "K Lft Lft RT" "Mid"
 "K Lft Lft RR" "Mid"

 "K Lft Mid LL" "Lft"
 "K Lft Mid LT" "Lft"
 "K Lft Mid MT" "Mid"
 "K Lft Mid RT" "Mid"
 "K Lft Mid RR" "Rht"

 "K Lft Rht LL" "Lft"
 "K Lft Rht LT" "Mid"
 "K Lft Rht MT" "Mid"
 "K Lft Rht RT" "Mid"
 "K Lft Rht RR" "Rht"

 "K Mid Lft LL" "Lft"
 "K Mid Lft LT" "Lft"
 "K Mid Lft MT" "Mid"
 "K Mid Lft RT" "Mid"
 "K Mid Lft RR" "Rht"

 "K Mid Mid LL" "Lft"
 "K Mid Mid LT" "Mid"
 "K Mid Mid MT" "Mid"
 "K Mid Mid RT" "Mid"
 "K Mid Mid RR" "Rht"

 "K Mid Rht LL" "Lft"
 "K Mid Rht LT" "Mid"
 "K Mid Rht MT" "Mid"
 "K Mid Rht RT" "Rht"
 "K Mid Rht RR" "Rht"

 "K Rht Lft LL" "Lft"
 "K Rht Lft LT" "Mid"
 "K Rht Lft MT" "Mid"
 "K Rht Lft RT" "Mid"
 "K Rht Lft RR" "Rht"

 "K Rht Mid LL" "Lft"
 "K Rht Mid LT" "Mid"
 "K Rht Mid MT" "Mid"
 "K Rht Mid RT" "Rht"
 "K Rht Mid RR" "Rht"

 "K Rht Rht LL" "Mid"
 "K Rht Rht LT" "Mid"
 "K Rht Rht MT" "Mid"
 "K Rht Rht RT" "Rht"
 "K Rht Rht RR" "Rht")

(set-totality-goal "K")
(use "AllTotalElim")
(cases)
(use "AllTotalElim")
(cases)
(use "AllTotalElim")
(cases)
(use "SdTotalVar")
(use "SdTotalVar")
(use "SdTotalVar")
(use "SdTotalVar")
(use "SdTotalVar")
(use "AllTotalElim")
(cases)
(use "SdTotalVar")
(use "SdTotalVar")
(use "SdTotalVar")
(use "SdTotalVar")
(use "SdTotalVar")
(use "AllTotalElim")
(cases)
(use "SdTotalVar")
(use "SdTotalVar")
(use "SdTotalVar")
(use "SdTotalVar")
(use "SdTotalVar")
(use "AllTotalElim")
(cases)
(use "AllTotalElim")
(cases)
(use "SdTotalVar")
(use "SdTotalVar")
(use "SdTotalVar")
(use "SdTotalVar")
(use "SdTotalVar")
(use "AllTotalElim")
(cases)
(use "SdTotalVar")
(use "SdTotalVar")
(use "SdTotalVar")
(use "SdTotalVar")
(use "SdTotalVar")
(use "AllTotalElim")
(cases)
(use "SdTotalVar")
(use "SdTotalVar")
(use "SdTotalVar")
(use "SdTotalVar")
(use "SdTotalVar")
(use "AllTotalElim")
(cases)
(use "AllTotalElim")
(cases)
(use "SdTotalVar")
(use "SdTotalVar")
(use "SdTotalVar")
(use "SdTotalVar")
(use "SdTotalVar")
(use "AllTotalElim")
(cases)
(use "SdTotalVar")
(use "SdTotalVar")
(use "SdTotalVar")
(use "SdTotalVar")
(use "SdTotalVar")
(use "AllTotalElim")
(cases)
(use "SdTotalVar")
(use "SdTotalVar")
(use "SdTotalVar")
(use "SdTotalVar")
(use "SdTotalVar")
;; Proof finished.
(save-totality)

(add-global-assumption
 "JKAxiom"
 "all x^,y^,d,e,i
  (Av r)(x^ av d)(y^ av e)i eqd((Av r)x^ y^(J d e i)av K d e i)")

;; YSatCoIClause
(set-goal "all i 
     allnc x^,y^(
      CoI x^ -> 
      CoI y^ -> 
      exr x^0,y^0 
       ex j,d(CoI x^0 & CoI y^0 & (Av r)x^ y^ i eqd(Av r)x^0 y^0 j av d))")
(assume "i" "x^" "y^" "CoIx" "CoIy")
(inst-with-to "CoIClause" (pt "x^") "CoIx" "CoIClauseInstx")
(by-assume "CoIClauseInstx" "x^1" "x1Prop")
(by-assume "x1Prop" "d" "x1dProp")
(inst-with-to "CoIClause" (pt "y^") "CoIy" "CoIClauseInsty")
(by-assume "CoIClauseInsty" "y^1" "y1Prop")
(by-assume "y1Prop" "e" "y1eProp")
(intro 0 (pt "x^1"))
(intro 0 (pt "y^1"))
(ex-intro "J d e i")
(ex-intro "K d e i")
(msplit)
(simp "x1dProp")
(simp "y1eProp")
(use "JKAxiom")
(use "y1eProp")
(use "x1dProp")
;; Proof finished.
(save "YSatCoIClause")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [i,v,v0]
;;  J left Des v left Des v0 i@
;;  K left Des v left Des v0 i@right Des v@right Des v0

;; This term can be read as follows.  Given i, v, v0, destruct the
;; latter two.  Both are composed, i.e., of the form dv1 and dv2.
;; Take their components d1,v1 and d2,v2.  Then we obtain J d1 d2 i
;; pair K d1 d2 i pair v1 pair v2.

;; Putting things together

;; YSubCoI
(set-goal "allnc z^(exr x^,y^ ex i(CoI x^ & CoI y^ andl
 z^ eqd(Av r) x^ y^ i) -> CoI z^)")
(assume "z^" "Yz")
(coind "Yz")
(assume "x^" "Yx")
(by-assume "Yx" "x^1" "x1Prop")
(by-assume "x1Prop" "y^1" "x1y1Prop")
(by-assume "x1y1Prop" "i" "x1y1iProp")
(inst-with-to "x1y1iProp" 'left "CoIx1")
(inst-with-to "x1y1iProp" 'right "y1iProp")
(drop "x1y1iProp")
(elim "y1iProp")
(assume "CoIy1" "x=(x1+y1+i)/4")
(drop "y1iProp")
(cut "exr x^0,y^0 
   ex j,d(CoI x^0 & CoI y^0 & (Av r)x^1 y^1 i eqd(Av r)x^0 y^0 j av d)")
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "YSatCoIClauseInst")
(by-assume "YSatCoIClauseInst" "x^2" "x2Prop")
(by-assume "x2Prop" "y^2" "x2y2Prop")
(by-assume "x2y2Prop" "j" "x2y2jProp")
(by-assume "x2y2jProp" "d" "x2y2jdProp")
(intro 0 (pt "(Av r)x^2 y^2 j"))
(ex-intro "d")
(split)
(intro 1)
(intro 0 (pt "x^2"))
(intro 0 (pt "y^2"))
(ex-intro "j")
(msplit)
(use "InitEqD")
(use "x2y2jdProp")
(use "x2y2jdProp")
(simp "x=(x1+y1+i)/4")
(use "x2y2jdProp")
;; Now we prove the formula cut in above
(use-with "YSatCoIClause" (pt "i") (pt "x^1") (pt "y^1") "CoIx1" "CoIy1")
;; Proof finished.
(save "YSubCoI")

(define eterm (proof-to-extracted-term))
(add-var-name "ivw" (py "sdtwo@@iv@@iv"))
(add-var-name "jdvw" (py "sdtwo@@sd@@iv@@iv"))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)
;; [ivw]
;;  (CoRec sdtwo@@iv@@iv=>iv)ivw
;;  ([ivw0]
;;    [let jdvw
;;      (cYSatCoIClause left ivw0 left right ivw0 right right ivw0)
;;      (left right jdvw@InR(left jdvw@right right jdvw))])

;; CoIAverage
(set-goal "allnc x^,y^(CoI x^ -> CoI y^ -> CoI(x^ avr y^))")
(assume "x^" "y^" "CoIx" "CoIy")
(inst-with-to "XSubY" (pt "x^") (pt "y^") "CoIx" "CoIy" "XSubYInst")
(by-assume "XSubYInst" "x^1" "x1Prop")
(by-assume "x1Prop" "y^1" "x1y1Prop")
(by-assume "x1y1Prop" "i" "x1y1iProp")
(simp "x1y1iProp")
(use "YSubCoI")
(intro 0 (pt "x^1"))
(intro 0 (pt "y^1"))
(ex-intro "i")
(msplit)
(use "InitEqD")
(use "x1y1iProp")
(use "x1y1iProp")
;; Proof finished.
(save "CoIAverage")

(define eterm (proof-to-extracted-term))
(animate "YSubCoI")
(define neterm (rename-variables (nt eterm)))
(ppc neterm)
;; [v,v0]
;;  (CoRec sdtwo@@iv@@iv=>iv)(cXSubY v v0)
;;  ([ivw]
;;    [let jdvw
;;      (cYSatCoIClause left ivw left right ivw right right ivw)
;;      (left right jdvw@InR(left jdvw@right right jdvw))])

(animate "XSubY")
(animate "YSatCoIClause")
(define neterm-av (rename-variables (nt eterm)))
(pp neterm-av)
;; [v,v0]
;;  (CoRec sdtwo@@iv@@iv=>iv)
;;  (left Des v plus left Des v0@right Des v@right Des v0)
;;  ([ivw]
;;    [let jdvw
;;      (J left Des left right ivw left Des right right ivw left ivw@
;;      K left Des left right ivw left Des right right ivw left ivw@
;;      right Des left right ivw@right Des right right ivw)
;;      (left right jdvw@(InR sdtwo@@iv@@iv iv)
;; 	 (left jdvw@right right jdvw))])

;; Experiments

;; To obtain interesting signed digit streams we use material from
;; cauchysds.scm.

(add-program-constant "SDToInt" (py "sd=>int"))
(add-computation-rules
 "SDToInt Lft" "IntN 1"
 "SDToInt Mid" "0"
 "SDToInt Rht" "1")

(set-totality-goal "SDToInt")
(use "AllTotalElim")
(cases)
(use "IntTotalVar")
(use "IntTotalVar")
(use "IntTotalVar")
;; Proof finished.
(save-totality)

(add-program-constant "Elem" (py "r=>rat=>nat=>boole"))
(add-program-constant "AverageRealInvSD" (py "r=>sd=>r"))
(add-infix-display-string "AverageRealInvSD" "va" 'add-op)

;; Standard Split
(set-goal
 "all rat(rat<(IntN 1#4) orr (IntN 1#4)<=rat & rat<(1#4) oru (1#4)<=rat)")
(cases)
(cases)
(assume "pos1" "pos2")
(ng #t)
(intro 1)
(cases (pt "SZero(SZero pos1)<pos2"))
(assume "4pos1<pos2")
(intro 0)
(split)
(use "Truth")
(use "Truth")
(assume "4pos1<pos2 -> F")
(intro 1)
(use "PosNotLtToLe")
(use "4pos1<pos2 -> F")
;; 4
(assume "pos1")
(ng #t)
(intro 1)
(intro 0)
(split)
(use "Truth")
(use "Truth")
;; 5
(assume "pos1" "pos2")
(ng #t)
(cases (pt "SZero(SZero pos1)<=pos2"))
(assume "4pos1<=pos2")
(intro 1)
(intro 0)
(split)
(use "Truth")
(use "Truth")
(assume "4pos1<=pos2 -> F")
(intro 0)
(use "PosNotLeToLt")
(use "4pos1<=pos2 -> F")
;; Proof finished.
(save "StandardSplit")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)
;; [rat]
;;  [case rat
;;    (k#pos -> 
;;    [case k
;;      (pos0 -> Inr(SZero(SZero pos0)<pos))
;;      (0 -> Inr True)
;;      (IntN pos0 -> 
;;      [case (SZero(SZero pos0)<=pos)
;;        (True -> Inr True)
;;        (False -> DummyL)])])]

(add-global-assumption
 "AxRealLeft"
 "all x^,rat(rat<(IntN 1#4) -> (Elem r)x^ rat(PosToNat 2) ->
           (Elem r)x^(IntN 1#2)(PosToNat 1))")

(add-global-assumption
 "AxRealMiddle"
 "all x^,rat((IntN 1#4)<=rat -> rat<(1#4) -> (Elem r)x^ rat(PosToNat 2) ->
           (Elem r)x^(0#2)(PosToNat 1))")

(add-global-assumption
 "AxRealRight"
 "all x^,rat((1#4)<=rat -> (Elem r)x^ rat(PosToNat 2) ->
           (Elem r)x^(1#2)(PosToNat 1))")

;; SplitProp
(set-goal "allnc x^(all n exi rat((Elem r)x^ rat n) ->
                    exi sd (Elem r)x^(SDToInt sd#2)1)")
(assume "x^" "Q x")
(inst-with-to "Q x" (pt "Succ(Succ Zero)") "HQ2")
(by-assume "HQ2" "rat" "Elem x rat 2")
(inst-with-to "StandardSplit" (pt "rat") "SSrat")
(elim "SSrat")
(drop "SSrat")
;; rat Left
(assume "rat Left")
(intro 0 (pt "Lft"))
(use "AxRealLeft" (pt "rat"))
(use "rat Left")
(use "Elem x rat 2")
(assume "SSrat Mid Right")
(elim "SSrat Mid Right")
(drop "SSrat" "SSrat Mid Right")
;; rat Middle
(assume "rat Middle")
(intro 0 (pt "Mid"))
(use "AxRealMiddle" (pt "rat"))
(use "rat Middle")
(use "rat Middle")
(use "Elem x rat 2")
(drop "SSrat" "SSrat Mid Right")
;; rat Right
(assume "rat Right")
(intro 0 (pt "Rht"))
(use "AxRealRight" (pt "rat"))
(use "rat Right")
(use "Elem x rat 2")
;; Proof finished.
(save "SplitProp")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [as][if (cStandardSplit(as(Succ(Succ Zero))))
;; 	Lft
;; 	([boole][if boole Mid Rht])]

(add-global-assumption
 "AxVaIntro"
 "all x^,sd,rat,n((Elem r)x^(SDToInt sd#2)(PosToNat 1) ->
   (Elem r)x^ rat(Succ n) -> (Elem r)(x^ va sd)(2*rat-SDToInt sd)n)")

(add-global-assumption
 "AxAvVaIdent"
 "all x^,sd((Elem r)x^(SDToInt sd#2)(PosToNat 1) ->
             x^ eqd x^ va sd av sd)")

;; CauchyToSds
(set-goal "allnc x^(all n exi rat((Elem r)x^ rat n) -> CoI x^)")
(assume "x^" "Q x")
(coind "Q x")
(assume "x^1" "Q x1")
(inst-with-to "SplitProp" (pt "x^1") "Q x1" "SP")
;; (by-assume "SP" "sd" "HElem")
(assert "exl sd (Elem r)x^1(SDToInt sd#2)(PosToNat 1)")
 (use "SP")
(use "Id")
(assume "ExHyp")
(by-assume "ExHyp" "sd" "HElem")
(intro 0 (pt "x^1 va sd"))
(ex-intro "sd")
(split)
;; CoI
(intro 1)
(assume "n")
(inst-with-to "Q x1" (pt "Succ n") "Hex")
(elim "Hex")
(assume "rat" "HElem2")
(intro 0 (pt "2*rat-SDToInt sd"))
(use "AxVaIntro")
(use "HElem")
(use "HElem2")
;; x^1 eqd ...
(use "AxAvVaIdent")
(use "HElem")
;; Proof finished.
(save "CauchyToSds")

(define eterm (proof-to-extracted-term))
(animate "SplitProp")
(animate "StandardSplit")
(define neterm-ctos (rename-variables (nt eterm)))
(pp neterm-ctos)
;; [as]
;;  (CoRec (nat=>rat)=>iv)as
;;  ([as0]
;;    [let d
;;      [if (as0(Succ(Succ Zero)))
;;       ([k,p]
;;        [if k
;;          ([p0][if (SZero(SZero p0)<p) Mid Rht])
;;          Mid
;;          ([p0][if (SZero(SZero p0)<=p) Mid Lft])])]
;;      (d@(InR nat=>rat iv)([n]2*as0(Succ n)-SDToInt d))])

;; Now for the converse.

(add-global-assumption
 "AxRealBound"
 "allnc x^((Elem r)x^ (0#1) Zero)")

(add-global-assumption
 "AxRealZero"
 "all n (Elem r)(Z r)(0#1)n")

(add-global-assumption
 "AxAvIntro"
 "all x^,rat,d,n((Elem r)x^ rat n ->
               (Elem r)(x^ av d)((rat+SDToInt d)/2)(Succ n))")

;; SdsToCauchy
(set-goal "allnc x^(CoI x^ -> all n exi rat((Elem r)x^ rat n))")
(assume "x^" "CoI x" "n")
(cut "all n allnc x^(CoI x^ -> exl rat (Elem r)x^ rat n)")
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
(by-assume "Cases x1" "x^2" "x2Prop")
(by-assume "x2Prop" "d" "x2dProp")
(inst-with-to "x2dProp" 'left "CoI x2")
(inst-with-to "x2dProp" 'right "Eq")
(inst-with-to "IH" (pt "x^2") "CoI x2" "Hex a")
(by-assume "Hex a" "rat" "HElem x1")
(intro 0 (pt "(rat+SDToInt d)/2"))
(simp "Eq")
(use "AxAvIntro")
(use "HElem x1")
;; Proof finished.
(save "SdsToCauchy")

(define eterm (proof-to-extracted-term))
(define neterm-stoc (rename-variables (nt eterm)))
(ppc neterm-stoc)
;; [v,n]
;;  (Rec nat=>iv=>rat)n([v0]0)
;;  ([n0,(iv=>rat),v0]((iv=>rat)right Des v0+SDToInt left Des v0)/2)
;;  v

;; For experiments we define approximations to the square root of a rational.
(add-program-constant "sqrt" (py "rat=>nat=>rat"))
(add-program-constant "sqrtaux" (py "rat=>nat=>rat"))
(add-computation-rules
 "sqrtaux rat Zero" "Succ Zero"
 "sqrtaux rat(Succ n)" "((sqrtaux rat n) + (rat / (sqrtaux rat n)))/2")
(add-computation-rule "sqrt rat n" "sqrtaux rat(Succ n)")

(define threebyfour (pt "[n](3#4)"))

;; Postprocessing following gray-tsuikiSection8

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Inductive predicate BH
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (add-algs "bh" '("bh" "BHN") '("bh=>bh" "BHD"))

(add-ids
 (list (list "BH" (make-arity (py "r") (py "nat")) "nat"))
 '("allnc x^(BH x^ Zero)" "InitBH")
 '("allnc x^, n^(BH x^ n^ -> BH(x^ av Mid)(Succ n^))" "GenBH"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Inductive predicate BG
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(add-algs "bg" '("bg" "Nz") '("psd=>bg=>bg" "LRz") '("nat=>bg" "Uz"))

(add-ids
 (list (list "BG" (make-arity (py "r") (py "nat")) "bg"))
 '("allnc x^(BG x^ Zero)" "InitBG")
 '("allnc x^,n^ all a(BG x^ n^ -> BG(inv a***(x^ av Lft))(Succ n^))" "GenLRz")
 '("allnc x^,n^(BH x^ n^ -> BG(x^ av Mid)(Succ n^))" "GenUz"))

(add-global-assumption "AvSdMid" "all x^,d x^ av d av Mid eqd x^ av inv d av d")

;; CoGToBGGen
(set-goal "all n(allnc x^(CoG x^ -> BG x^ n) &
 allnc x^(CoH x^ ->
  BH x^ n ord exr y^ ex a(CoG y^ & BG y^(Pred n) & x^ eqd a***(y^ av Rht))))")
(ind)
;; Base
(split)
(assume "x^" "CoGx")
(use "InitBG")
(assume "x^" "CoHx")
(intro 0)
(use "InitBH")
;; Step
(assume "n" "IndHyp")
(inst-with-to "IndHyp" 'left "IHBG")
(inst-with-to "IndHyp" 'right "IHBH")
(drop "IndHyp")
(split)
;; Case CoGx
(assume "x^" "CoGx")
;; Goal 17: BG x^(Succ n)
(inst-with-to "CoGClause" (pt "x^") "CoGx" "CoGClauseInst")
(elim "CoGClauseInst")
(drop "CoGClauseInst")
;; 
(assume "ExHypLR")
(by-assume "ExHypLR" "x^1" "x1Prop")
(by-assume "x1Prop" "a" "x1aProp")
(simp "x1aProp")
(use "GenLRz")
(use "IHBG")
(use "x1aProp")
(drop "CoGClauseInst")
;; 
(assume "ExHypU")
(by-assume "ExHypU" "x^1" "x1Prop")
(inst-with-to "x1Prop" 'left "CoHx1")
(inst-with-to "IHBH" (pt "x^1") "CoHx1" "IHBHInst")
(elim "IHBHInst")
(drop "IHBHInst")
;; Case B1
(assume "BHx1n")
(simp "x1Prop")
(use "GenUz")
(use "BHx1n")
(drop "IHBHInst")
;; Case B2
(assume "ExHypLR")
(by-assume "ExHypLR" "x^2" "x2Prop")
(by-assume "x2Prop" "a" "x2aProp")
(assert "exr x^3 x^3 eqd inv PRht***(x^2 av Lft)")
 (intro 0 (pt "inv PRht***(x^2 av Lft)"))
 (use "InitEqD")
(assume "exr x^3 x^3 eqd inv PRht***(x^2 av Lft)")
(by-assume "exr x^3 x^3 eqd inv PRht***(x^2 av Lft)" "x^3" "x3Def")
(assert "x^ eqd inv a***(x^3 av Lft)")
 (simp "x3Def")
 (simp "x1Prop")
 (simp "x2aProp")
 (assert "Mid=a times Mid")
  (use "Truth")
 (assume "Mid=a times Mid")
 (simp "Mid=a times Mid")
 (drop "Mid=a times Mid")
 (simp "<-" "PsdTimesAv")
 (simp "AvSdMid")
 (ng #t)
 (use "InitEqD")
(assume "xProp")
(simp "xProp")
(use "GenLRz")
(simp "x3Def")
(cases (pt "n"))
(assume "Useless")
(use "InitBG")
(assume "m" "n=m+1")
(use "GenLRz")
(simphyp-with-to "x2aProp" "n=m+1" "x2aPropSimp")
(use "x2aPropSimp")
;; Case CoHx
(assume "x^" "CoHx")
(inst-with-to "CoHClause" (pt "x^") "CoHx" "CoHClauseInst")
(elim "CoHClauseInst")
(drop "CoHClauseInst")
;; 
(assume "ExHypLR")
(by-assume "ExHypLR" "x^1" "x1Prop")
(by-assume "x1Prop" "a" "x1aProp")
(simp "x1aProp")
(intro 1)
(intro 0 (pt "x^1"))
(ex-intro "a")
(msplit)
(use "InitEqD")
(use "IHBG")
(use "x1aProp")
(use "x1aProp")
(drop "CoHClauseInst")
;; 
(assume "ExHypD")
(by-assume "ExHypD" "x^1" "x1Prop")
(inst-with-to "x1Prop" 'left "CoHx1")
(inst-with-to "IHBH" (pt "x^1") "CoHx1" "IHBHInst")
(elim "IHBHInst")
(drop "IHBHInst")
;; Case B1
(assume "BHx1n")
(simp "x1Prop")
(intro 0)
(use "GenBH")
(use "BHx1n")
(drop "IHBHInst")
;; Case B2
(assume "ExHypLR")
(by-assume "ExHypLR" "x^2" "x2Prop")
(by-assume "x2Prop" "a" "x2aProp")
(assert "exr x^3 x^3 eqd x^2 av Lft")
 (intro 0 (pt "x^2 av Lft"))
 (use "InitEqD")
(assume "exr x^3 x^3 eqd x^2 av Lft")
(by-assume "exr x^3 x^3 eqd x^2 av Lft" "x^3" "x3Def")
(assert "x^ eqd a***(x^3 av Rht)")
 (simp "x3Def")
 (simp "x1Prop")
 (simp "x2aProp")
 (assert "Mid=a times Mid")
  (use "Truth")
 (assume "Mid=a times Mid")
 (simp "Mid=a times Mid")
 (drop "Mid=a times Mid")
 (simp "<-" "PsdTimesAv")
 (simp "AvSdMid")
 (ng #t)
 (use "InitEqD")
(assume "xProp")
(simp "xProp")
(intro 1)
(intro 0 (pt "x^3"))
(ex-intro "a")
(msplit)
(use "InitEqD")
(simp "x3Def")
(use "IHBG")
(inst-with-to "x2aProp" 'left "CoGx2")
(use-with "GenCoGLR" (pt "x^2") (pt "PLft") "CoGx2")
(simp "x3Def")
(inst-with-to "x2aProp" 'left "CoGx2")
(use-with "GenCoGLR" (pt "x^2") (pt "PLft") "CoGx2")

(ng #t)
(cases (pt "n"))
;; Case n=0
(assume "n=0")
(use "InitBG")
;; Case n=n1+1
(assume "n1" "n=n1+1")
(simp "x3Def")
(use-with "GenLRz" (pt "x^2") (pt "n1") (pt "PLft") "?")
(assert "n1=Pred n")
 (simp "n=n1+1")
 (use "Truth")
(assume "n1=Pred n")
(simp "n1=Pred n")
(use "x2aProp")
;; CoG x^3
(simp "x3Def")
(inst-with-to "x2aProp" 'left "CoGx2")
(use-with "GenCoGLR" (pt "x^2") (pt "PLft") "CoGx2")
;; Proof finished.
(save "CoGToBGGen")

(define eterm (proof-to-extracted-term))
(animate "GenCoGLR")
;; (display-default-varnames)
(add-var-name
 "psf" ;for pair of step functions
 (py "(ag=>bg)@@(ah=>nat ysum psd@@ag@@bg)"))
(add-var-name "apbg" (py "psd@@ag@@bg"))
(define neterm (rename-variables (nt eterm)))
(define nneterm (rename-variables (nt (undelay-delayed-corec neterm 1))))
(ppc nneterm)
;; [n](Rec nat=>(ag=>bg)@@(ah=>nat ysum psd@@ag@@bg))n
;;  (([p]Nz)@([q]InL Zero))
;;  ([n0,psf]
;;    ([p][case (Des p)
;;        (InL ap -> LRz left ap(left psf right ap))
;;        (InR q -> 
;;        [case (right psf q)
;;          (InL n -> Uz n)
;;          (InR apbg -> 
;;          LRz left apbg
;;          [case n0
;;            (Zero -> Nz)
;;            (Succ n1 -> LRz PRht right right apbg)])])])@
;;    ([q][case (Des q)
;;        (InL ap -> InR(left ap@right ap@left psf right ap))
;;        (InR q0 -> 
;;        [case (right psf q0)
;;          (InL n1 -> InL(Succ n1))
;;          (InR apbg -> 
;;          InR
;;          (left apbg@
;;           LR PLft left right apbg@
;;           [case n0
;;             (Zero -> Nz)
;;             (Succ n1 -> LRz PLft right right apbg)]))])]))

;; CoGToBG
(set-goal "all n allnc x^(CoG x^ -> BG x^ n)")
(assume "n" "x^" "CoGx")
(use "CoGToBGGen")
(use "CoGx")
;; Proof finished.
(save "CoGToBG")

(define eterm (proof-to-extracted-term))
(animate "CoGToBGGen")
(define neterm (rename-variables (nt eterm)))
(define nneterm (rename-variables (nt (undelay-delayed-corec neterm 1))))
(ppc nneterm)

;; [n]left((Rec nat=>(ag=>bg)@@(ah=>nat ysum psd@@ag@@bg))n
;;       (([p]Nz)@([q]InL Zero))
;;       ([n0,psf]
;;         ([p][case (Des p)
;;             (InL ap -> LRz left ap(left psf right ap))
;;             (InR q -> 
;;             [case (right psf q)
;;               (InL n -> Uz n)
;;               (InR apbg -> 
;;               LRz left apbg
;;               [case n0
;;                 (Zero -> Nz)
;;                 (Succ n1 -> LRz PRht right right apbg)])])])@
;;         ([q][case (Des q)
;;             (InL ap -> InR(left ap@right ap@left psf right ap))
;;             (InR q0 -> 
;;             [case (right psf q0)
;;               (InL n1 -> InL(Succ n1))
;;               (InR apbg -> 
;;               InR
;;               (left apbg@
;;                LR PLft left right apbg@
;;                [case n0
;;                  (Zero -> Nz)
;;                  (Succ n1 -> LRz PLft right right apbg)]))])])))

(define neterm-gtobg nneterm)

;; (set! COMMENT-FLAG #t)

;; Haskell translation

(terms-to-haskell-program
 "gray.hs"
 (list (list neterm-stog "stog")
       (list neterm-gtos "gtos")
       (list neterm-gminus "gminus")
       (list neterm-av "av")
       (list neterm-ctos "ctos")
       (list neterm-stoc "stoc")
       (list (pt "sqrt") "rattosqrt")
       (list neterm-gtobg "gtobg")))

;; This is the file gray.hs

;; module Main where

;; import Data.Ratio

;; ----- Algebras ------------------

;; data Psd = PLft  | PRht 
;;   deriving (Show, Read, Eq, Ord)

;; data Iv = C Sd Iv
;;   deriving (Show, Read, Eq, Ord)

;; data Ag = LR Psd Ag | U Ah
;;   deriving (Show, Read, Eq, Ord)

;; data Ah = Fin Psd Ag | D Ah
;;   deriving (Show, Read, Eq, Ord)

;; data Sd = Lft  | Rht  | Mid 
;;   deriving (Show, Read, Eq, Ord)

;; data Sdtwo = LL  | LT  | MT  | RT  | RR 
;;   deriving (Show, Read, Eq, Ord)

;; type Nat = Integer

;; type Pos = Integer

;; data Bg = Nz  | LRz Psd Bg | Uz Nat
;;   deriving (Show, Read, Eq, Ord)

;; ----- Recursion operators -------

;; agCoRec :: (alpha2476 -> ((alpha2476 -> (Either (Psd, (Either Ag alpha2476)) (Either Ah alpha2477))) -> ((alpha2477 -> (Either (Psd, (Either Ag alpha2476)) (Either Ah alpha2477))) -> Ag)))
;; agCoRec c g f = (case (g c) of
;;  { Left o0 -> (LR (fst o0) (case (snd o0) of
;;  { Left p18898 -> p18898 ;
;;  Right c2 -> (agCoRec c2 g f) })) ;
;;  Right w0 -> (U (case w0 of
;;  { Left q18895 -> q18895 ;
;;  Right h1 -> (ahCoRec h1 g f) })) })

;; ahCoRec :: (alpha2457 -> ((alpha2458 -> (Either (Psd, (Either Ag alpha2458)) (Either Ah alpha2457))) -> ((alpha2457 -> (Either (Psd, (Either Ag alpha2458)) (Either Ah alpha2457))) -> Ah)))
;; ahCoRec c g f = (case (f c) of
;;  { Left h0 -> (Fin (fst h0) (case (snd h0) of
;;  { Left p18865 -> p18865 ;
;;  Right o1 -> (agCoRec o1 g f) })) ;
;;  Right w0 -> (D (case w0 of
;;  { Left q18862 -> q18862 ;
;;  Right c2 -> (ahCoRec c2 g f) })) })

;; ivDestr :: (Iv -> (Sd, Iv))
;; ivDestr (C d18832 v18831) = (d18832, v18831)

;; ivCoRec :: (alpha2451 -> ((alpha2451 -> (Sd, (Either Iv alpha2451))) -> Iv))
;; ivCoRec c f = (C (fst (f c)) (case (snd (f c)) of
;;  { Left v18830 -> v18830 ;
;;  Right c1 -> (ivCoRec c1 f) }))

;; agDestr :: (Ag -> (Either (Psd, Ag) Ah))
;; agDestr (LR a18818 p18817) = (Left (a18818, p18817))
;; agDestr (U q18816) = (Right q18816)

;; ahDestr :: (Ah -> (Either (Psd, Ag) Ah))
;; ahDestr (Fin a18815 p18814) = (Left (a18815, p18814))
;; ahDestr (D q18813) = (Right q18813)

;; natRec :: Nat -> a -> (Nat -> a -> a) -> a
;; natRec 0 g h = g
;; natRec n g h | n > 0 = h (n - 1) (natRec (n - 1) g h)

;; ----- Program constants ---------

;; psdInv :: (Psd -> Psd)
;; psdInv PLft = PRht
;; psdInv PRht = PLft

;; psdToSd :: (Psd -> Sd)
;; psdToSd PLft = Lft
;; psdToSd PRht = Rht

;; psdTimes :: (Psd -> (Psd -> Psd))
;; psdTimes PLft PLft = PRht
;; psdTimes PRht a = a
;; psdTimes a PRht = a

;; sdPlus :: (Sd -> (Sd -> Sdtwo))
;; sdPlus Lft Lft = LL
;; sdPlus Lft Mid = Main.LT
;; sdPlus Lft Rht = MT
;; sdPlus Mid Lft = Main.LT
;; sdPlus Mid Mid = MT
;; sdPlus Mid Rht = RT
;; sdPlus Rht Lft = MT
;; sdPlus Rht Mid = RT
;; sdPlus Rht Rht = RR

;; j :: (Sd -> (Sd -> (Sdtwo -> Sdtwo)))
;; j Lft Lft LL = LL
;; j Lft Lft Main.LT = MT
;; j Lft Lft MT = LL
;; j Lft Lft RT = MT
;; j Lft Lft RR = RR
;; j Lft Mid LL = Main.LT
;; j Lft Mid Main.LT = RT
;; j Lft Mid MT = Main.LT
;; j Lft Mid RT = RT
;; j Lft Mid RR = Main.LT
;; j Lft Rht LL = MT
;; j Lft Rht Main.LT = LL
;; j Lft Rht MT = MT
;; j Lft Rht RT = RR
;; j Lft Rht RR = MT
;; j Mid Lft LL = Main.LT
;; j Mid Lft Main.LT = RT
;; j Mid Lft MT = Main.LT
;; j Mid Lft RT = RT
;; j Mid Lft RR = Main.LT
;; j Mid Mid LL = MT
;; j Mid Mid Main.LT = LL
;; j Mid Mid MT = MT
;; j Mid Mid RT = RR
;; j Mid Mid RR = MT
;; j Mid Rht LL = RT
;; j Mid Rht Main.LT = Main.LT
;; j Mid Rht MT = RT
;; j Mid Rht RT = Main.LT
;; j Mid Rht RR = RT
;; j Rht Lft LL = MT
;; j Rht Lft Main.LT = LL
;; j Rht Lft MT = MT
;; j Rht Lft RT = RR
;; j Rht Lft RR = MT
;; j Rht Mid LL = RT
;; j Rht Mid Main.LT = Main.LT
;; j Rht Mid MT = RT
;; j Rht Mid RT = Main.LT
;; j Rht Mid RR = RT
;; j Rht Rht LL = LL
;; j Rht Rht Main.LT = MT
;; j Rht Rht MT = RR
;; j Rht Rht RT = MT
;; j Rht Rht RR = RR

;; k :: (Sd -> (Sd -> (Sdtwo -> Sd)))
;; k Lft Lft LL = Lft
;; k Lft Lft Main.LT = Lft
;; k Lft Lft MT = Mid
;; k Lft Lft RT = Mid
;; k Lft Lft RR = Mid
;; k Lft Mid LL = Lft
;; k Lft Mid Main.LT = Lft
;; k Lft Mid MT = Mid
;; k Lft Mid RT = Mid
;; k Lft Mid RR = Rht
;; k Lft Rht LL = Lft
;; k Lft Rht Main.LT = Mid
;; k Lft Rht MT = Mid
;; k Lft Rht RT = Mid
;; k Lft Rht RR = Rht
;; k Mid Lft LL = Lft
;; k Mid Lft Main.LT = Lft
;; k Mid Lft MT = Mid
;; k Mid Lft RT = Mid
;; k Mid Lft RR = Rht
;; k Mid Mid LL = Lft
;; k Mid Mid Main.LT = Mid
;; k Mid Mid MT = Mid
;; k Mid Mid RT = Mid
;; k Mid Mid RR = Rht
;; k Mid Rht LL = Lft
;; k Mid Rht Main.LT = Mid
;; k Mid Rht MT = Mid
;; k Mid Rht RT = Rht
;; k Mid Rht RR = Rht
;; k Rht Lft LL = Lft
;; k Rht Lft Main.LT = Mid
;; k Rht Lft MT = Mid
;; k Rht Lft RT = Mid
;; k Rht Lft RR = Rht
;; k Rht Mid LL = Lft
;; k Rht Mid Main.LT = Mid
;; k Rht Mid MT = Mid
;; k Rht Mid RT = Rht
;; k Rht Mid RR = Rht
;; k Rht Rht LL = Mid
;; k Rht Rht Main.LT = Mid
;; k Rht Rht MT = Mid
;; k Rht Rht RT = Rht
;; k Rht Rht RR = Rht

;; sDToInt :: (Sd -> Integer)
;; sDToInt Lft = -1
;; sDToInt Mid = 0
;; sDToInt Rht = 1

;; natToInt :: (Nat -> Integer)
;; natToInt 0 = 0
;; natToInt nat | nat > 0 = ((natToInt (nat - 1)) + 1)

;; sqrtaux :: (Rational -> (Nat -> Rational))
;; sqrtaux rat 0 = ((natToInt 1) % 1)
;; sqrtaux rat n | n > 0 = (((sqrtaux rat (n - 1)) + (rat / (sqrtaux rat (n - 1)))) / (2))

;; sqrt :: (Rational -> (Nat -> Rational))
;; sqrt rat n = (sqrtaux rat (n + 1))

;; ---------------------------------

;; stog :: ((Psd, Iv) -> Ag)
;; stog = (\ bv -> (agCoRec bv (\ bv0 -> (case (fst (ivDestr (snd bv0))) of
;;  { Lft -> (Left ((psdInv (fst bv0)), (Right (PRht, (snd (ivDestr (snd bv0))))))) ;
;;  Rht -> (Left ((fst bv0), (Right (PLft, (snd (ivDestr (snd bv0))))))) ;
;;  Mid -> (Right (Right ((fst bv0), (snd (ivDestr (snd bv0)))))) })) (\ bv0 -> (case (fst (ivDestr (snd bv0))) of
;;  { Lft -> (Left ((psdInv (fst bv0)), (Right (PLft, (snd (ivDestr (snd bv0))))))) ;
;;  Rht -> (Left ((fst bv0), (Right (PRht, (snd (ivDestr (snd bv0))))))) ;
;;  Mid -> (Right (Right ((fst bv0), (snd (ivDestr (snd bv0)))))) }))))

;; gtos :: (Psd -> (Ag -> Iv))
;; gtos = (\ a -> (\ p -> (ivCoRec (a, (Left p)) (\ apq -> (case (snd apq) of
;;  { Left p18922 -> (case (agDestr p18922) of
;;  { Left ap18924 -> ((psdToSd (psdTimes (fst apq) (fst ap18924))), (Right ((psdInv (psdTimes (fst apq) (fst ap18924))), (Left (snd ap18924))))) ;
;;  Right q18923 -> (Mid, (Right ((fst apq), (Right q18923)))) }) ;
;;  Right q18919 -> (case (ahDestr q18919) of
;;  { Left ap18921 -> ((psdToSd (psdTimes (fst apq) (fst ap18921))), (Right ((psdTimes (fst apq) (fst ap18921)), (Left (snd ap18921))))) ;
;;  Right q18920 -> (Mid, (Right ((fst apq), (Right q18920)))) }) })))))

;; gminus :: (Ag -> Ag)
;; gminus = (\ p -> (agCoRec p (\ p0 -> (case (agDestr p0) of
;;  { Left ap18914 -> (Left ((psdInv (fst ap18914)), (Left (snd ap18914)))) ;
;;  Right q18913 -> (Right (Right q18913)) })) (\ q -> (case (ahDestr q) of
;;  { Left ap18912 -> (Left ((psdInv (fst ap18912)), (Left (snd ap18912)))) ;
;;  Right q18911 -> (Right (Right q18911)) }))))

;; av :: (Iv -> (Iv -> Iv))
;; av = (\ v -> (\ v0 -> (ivCoRec ((sdPlus (fst (ivDestr v)) (fst (ivDestr v0))), ((snd (ivDestr v)), (snd (ivDestr v0)))) (\ ivw -> (let jdvw = ((j (fst (ivDestr (fst (snd ivw)))) (fst (ivDestr (snd (snd ivw)))) (fst ivw)), ((k (fst (ivDestr (fst (snd ivw)))) (fst (ivDestr (snd (snd ivw)))) (fst ivw)), ((snd (ivDestr (fst (snd ivw)))), (snd (ivDestr (snd (snd ivw))))))) in ((fst (snd jdvw)), (Right ((fst jdvw), (snd (snd jdvw))))))))))

;; ctos :: ((Nat -> Rational) -> Iv)
;; ctos = (\ as -> (ivCoRec as (\ as0 -> (let d = (if ((numerator (as0 2)) > 0) then ((\ pos0 -> (if (((pos0 * 2) * 2) < (denominator (as0 2))) then Mid else Rht)) (numerator (as0 2))) else if ((numerator (as0 2)) == 0) then (Mid) else (((\ pos0 -> (if (((pos0 * 2) * 2) <= (denominator (as0 2))) then Mid else Lft)) (-(numerator (as0 2)))))) in (d, (Right (\ n -> (((2) * (as0 (n + 1))) - ((sDToInt d) % 1)))))))))

;; stoc :: (Iv -> (Nat -> Rational))
;; stoc = (\ v -> (\ n -> (natRec n (\ v0 -> (0)) (\ n0 -> (\ s -> (\ v0 -> (((s (snd (ivDestr v0))) + ((sDToInt (fst (ivDestr v0))) % 1)) / (2))))) v)))

;; rattosqrt :: (Rational -> (Nat -> Rational))
;; rattosqrt = Main.sqrt

;; gtobg :: (Nat -> (Ag -> Bg))
;; gtobg = (\ n -> (fst (natRec n ((\ p -> Nz), (\ q -> (Left 0))) (\ n0 -> (\ psf -> ((\ p -> (case (agDestr p) of
;;  { Left ap18904 -> (LRz (fst ap18904) ((fst psf) (snd ap18904))) ;
;;  Right q18901 -> (case ((snd psf) q18901) of
;;  { Left n18903 -> (Uz n18903) ;
;;  Right apbg18902 -> (LRz (fst apbg18902) (if (n0 == 0) then Nz else ((LRz PRht (snd (snd apbg18902)))))) }) })), (\ q -> (case (ahDestr q) of
;;  { Left ap18910 -> (Right ((fst ap18910), ((snd ap18910), ((fst psf) (snd ap18910))))) ;
;;  Right q18907 -> (case ((snd psf) q18907) of
;;  { Left n18909 -> (Left (n18909 + 1)) ;
;;  Right apbg18908 -> (Right ((fst apbg18908), ((LR PLft (fst (snd apbg18908))), (if (n0 == 0) then Nz else ((LRz PLft (snd (snd apbg18908)))))))) }) }))))))))

;; ---------------------------------

;; main :: IO ()
;; main = putStrLn ""

;; How to run the Haskell program.
;; In a terminal type ghci gray.hs.  The result is

;; GHCi, version 7.0.4: http://www.haskell.org/ghc/  :? for help
;; Loading package ghc-prim ... linking ... done.
;; Loading package integer-gmp ... linking ... done.
;; Loading package base ... linking ... done.
;; Loading package ffi-1.0 ... linking ... done.
;; [1 of 1] Compiling Main             ( gray.hs, interpreted )
;; Ok, modules loaded: Main.
;; *Main> 

;; Experiments.  1.  Flip mode.  Note that stog and gtos need as
;; argument a pair with PRht as its left hand side.  This is because
;; CoGToCoI and CoIToCoG allow for a sign of the argument.

;; *Main> stog (PRht, (C Rht (C Lft (C Rht (C Lft (ctos (\ n -> 0)))))))
;; LR PRht (LR PRht (LR PRht (LR PRht (U (D (D (D ...

;; *Main> stog (PRht, (C Rht (C Rht (C Lft (C Rht (C Lft (ctos (\ n -> 0))))))))
;; LR PRht (LR PLft (LR PRht (LR PRht (LR PRht (U (D (D (D ...

;; gtos works as a converse

;; *Main> gtos PRht (stog (PRht, (C Rht (C Lft (C Rht (C Lft (ctos (\ n -> 0))))))))
;; C Rht (C Lft (C Rht (C Lft (C Mid (C Mid (C Mid ...

;; *Main> gtos PRht (stog (PRht, (C Rht (C Rht (C Lft (C Rht (C Lft (ctos (\ n -> 0)))))))))
;; C Rht (C Rht (C Lft (C Rht (C Lft (C Mid (C Mid (C Mid ...

;; 2.  Block.

;; *Main> stog (PRht, (C Mid (C Mid (C Rht (C Lft (ctos (\ n -> 0)))))))
;; U (D (Fin PRht (LR PLft (U (D (D (D ...

;; *Main> gtos PRht (stog (PRht, (C Mid (C Mid (C Rht (C Lft (ctos (\ n -> 0))))))))
;; C Mid (C Mid (C Rht (C Lft (C Mid (C Mid (C Mid ....

;; 3.  Flip mode in a block.

;; *Main> stog (PRht, (C Mid (C Lft (C Rht (C Rht (ctos (\ n -> 0)))))))
;; U (Fin PLft (LR PLft (LR PLft (U (D (D (D ...

;; *Main> stog (PRht, (C Mid (C Rht (C Rht (C Rht (ctos (\ n -> 0)))))))
;; U (Fin PRht (LR PRht (LR PLft (U (D (D (D ...

;; *Main> stog (PRht, (C Rht (C Mid (C Mid (C Lft (C Lft (C Lft (ctos (\ n -> 0)))))))))
;; LR PRht (U (D (Fin PRht (LR PRht (LR PLft (U (D (D (D ...

;; 4.  Average.

;; *Main> stog (PRht, (av (gtos PRht (LR PRht (U (Fin PLft (stog (PRht, (ctos (\ n -> 0)))))))) (gtos PRht (LR PRht (LR PLft (stog (PRht, (ctos (\ n -> 0)))))))))
;; LR PRht (LR PLft (U (Fin PRht (U (D (D ...

;; 5.  Gray code.

;; *Main> gtobg 5 (U (D (Fin PLft (U (Fin PRht (stog (PLft, (ctos (\ n -> 0)))))))))
;; LRz PLft (LRz PRht (LRz PLft (LRz PRht (LRz PRht Nz))))

;; *Main> gtobg 5 (stog (PRht, (ctos (\ n -> 0))))
;; Uz 4

;; *Main> gtobg 5 (U (Fin PLft (stog (PRht, (ctos (\ n -> 0))))))
;; LRz PLft (LRz PRht (Uz 2))

