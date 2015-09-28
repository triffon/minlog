;; 2015-09-28.  gray.scm.  Type of reals still a tvar.

;; (load "~/git/minlog/init.scm")

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
(remove-var-name "M") ;will be used as modified G
(remove-token "M")
(remove-var-name "N") ;will be used as modified H
(remove-token "N")

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
(add-program-constant "SdSdtwoTimes" (py "sd=>sdtwo=>sdtwo") t-deg-zero)

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
;; 2015-08-03.  Added
(add-token-and-type-to-name "times" (py "sdtwo") "SdSdtwoTimes")
;; (add-token-and-type-to-name "times" (py "sdtwo") "PsdSdtwoTimes")

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
;; (pp (pt "a times i"))
;; SdSdtwoTimes a i
;; (pp (pt "d times i"))
;; SdSdtwoTimes d i
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
(add-display (py "sdtwo") (make-display-creator "SdSdtwoTimes" "times" 'mul-op))

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
;; (pp (pt "a times i"))
;; a times i
;; (pp (pt "d times i"))
;; d times i
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
 "Lft times i" "inv i"
 "Rht times i" "i"
 "Mid times i" "MT")

(set-totality-goal "SdSdtwoTimes")
(use "AllTotalElim")
(cases)
(use "AllTotalElim")
(assume "i")
(ng #t)
(use "SdtwoTotalVar")
(use "AllTotalElim")
(assume "i")
(ng #t)
(use "SdtwoTotalVar")
(use "AllTotalElim")
(assume "i")
(ng #t)
(use "SdtwoTotalVar")
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

;; Added 2015-08-19

(set-goal "all a a times PLft=inv a")
(cases)
(use "Truth")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "a times PLft" "inv a")

(set-goal "all a PLft times a=inv a")
(cases)
(use "Truth")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "PLft times a" "inv a")

;; End of additions

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

(set-goal "all i,a a times(a times i)=i")
(assume "i")
(cases)
(use "Truth")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "a times(a times i)" "i")

(set-goal "all i,d inv d times i=inv(d times i)")
(assume "i")
(cases)
(use "Truth")
(use "Truth")
(use "Truth")
;; Proof finished.
(add-rewrite-rule "inv d times i" "inv(d times i)")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Abstract real numbers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(add-tvar-name "r") ;type of real numbers
(add-var-name "x" "y" "z" (py "r"))

(add-program-constant "Z" (py "r")) ;zero

(add-program-constant "UnaryMinusScheme" (py "r=>r"))
(add-prefix-display-string "UnaryMinusScheme" "~")

(add-program-constant "AverageRealSd" (py "r=>sd=>r"))

;; 2015-08-19.  Added better display for av.  Corrects failure of the
;; parser for (x av a): it cannot lift the type psd of a to sd.

;; Instead of (add-infix-display-string "AverageRealSd" "av" 'add-op)
;; we now use make-term-creator-av (as in lib/numbers.scm)

(add-program-constant "AverageRealPsd" (py "r=>psd=>r"))

(define (make-term-creator-av token min-type-string)
  (lambda (x y)
    (let* ((type1 (term-to-type x)) ;the type variable r for abstract reals
	   (type2 (term-to-type y)) ;psd or sd
	   (min-type (py min-type-string))
	   (type (types-lub type2 min-type))
	   (internal-name (token-and-type-to-name token type)))
      (mk-term-in-app-form
       (make-term-in-const-form (pconst-name-to-pconst internal-name))
       x y))))

(add-token "av" 'add-op (make-term-creator-av "av" "psd"))
(add-token-and-type-to-name "av" (py "psd") "AverageRealPsd")
(add-token-and-type-to-name "av" (py "sd") "AverageRealSd")

(add-display
 (py "r")
 (lambda (x)
   (if (term-in-app-form? x)
       (let ((op (term-in-app-form-to-final-op x))
	     (args (term-in-app-form-to-args x)))
	 (if (and (term-in-const-form? op)
		  (member (const-to-name (term-in-const-form-to-const op))
			  (list "AverageRealPsd" "AverageRealSd"))
		  (= 2 (length args)))
	     (list 'add-op "av"
		   (term-to-token-tree (car args))
		   (term-to-token-tree (cadr args)))
	     #f))
       #f)))

;; (pp (pt "x av d"))
;; x av d
;; (pp (pt "x av a"))
;; x av a

(add-rewrite-rule "x^ av PsdToSd a" "x^ av a")
(add-rewrite-rule "x^ av Lft" "x^ av PLft")
(add-rewrite-rule "x^ av Rht" "x^ av PRht")

;; 2015-08-19.  End of addition for better display of av.

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

(add-rewrite-rule "a***(x^ av b)" "a***x^ av a times b")
;; (add-rewrite-rule "a***(x^ av PsdToSd b)" "a***x^ av PsdToSd(a times b)")
(add-rewrite-rule "a***(x^ av d)" "a***x^ av a times d")

;; PRhtTimes
(set-goal "all x^ PRht***x^ eqd x^")
(use "RewriteGA82")
;; Proof finished.
(save "PRhtTimes")

;; PLftTimes
(set-goal "all x^ PLft***x^ eqd~x^")
(use "RewriteGA85")
;; Proof finished.
(save "PLftTimes")

;; PsdTimesAvPsd
(set-goal "all a,x^,b a***(x^ av b)eqd a***x^ av a times b")
(use "RewriteGA86")
;; Proof finished.
(save "PsdTimesAvPsd")

;; PsdTimesAvSd
(set-goal "all a,x^,d a***(x^ av d)eqd a***x^ av a times d")
(use "RewriteGA87")
;; Proof finished.
(save "PsdTimesAvSd")

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

;; MinusAvPsd
(set-goal "all x^,a ~(x^ av a) eqd~x^ av inv a")
(assume "x^" "a")
(inst-with-to "PsdTimesAvPsd"
	      (pt "PLft") (pt "x^") (pt "a") "PsdTimesAvPsdInst")
(use "PsdTimesAvPsdInst")
;; Proof finished.
(save "MinusAvPsd")
(add-rewrite-rule "~(x^ av a)" "~x^ av inv a")

;; MinusAvSd
(set-goal "all x^,d ~(x^ av d) eqd~x^ av inv d")
(assume "x^" "d")
(inst-with-to "PsdTimesAvSd" (pt "PLft") (pt "x^") (pt "d") "PsdTimesAvSdInst")
(use "PsdTimesAvSdInst")
;; Proof finished.
(save "MinusAvSd")
(add-rewrite-rule "~(x^ av d)" "~x^ av inv d")

;; MinusAvPsdInv
(set-goal "all x^,a ~(x^ av inv a)eqd~x^ av a")
(assume "x^" "a")
(inst-with-to "PsdTimesAvPsd"
	      (pt "PLft") (pt "x^") (pt "inv a") "PsdTimesAvPsdInst")
(use "PsdTimesAvPsdInst")
;; Proof finished.
(save "MinusAvPsdInv")
(add-rewrite-rule "~(x^ av inv a)" "~x^ av a")

;; MinusAvSdInv
(set-goal "all x^,d ~(x^ av inv d)eqd~x^ av d")
(assume "x^" "d")
(inst-with-to "PsdTimesAvSd"
	      (pt "PLft") (pt "x^") (pt "inv d") "PsdTimesAvSdInst")
(use "PsdTimesAvSdInst")
;; Proof finished.
(save "MinusAvSdInv")
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
;; Specific properties of I
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; CoIMinus
(set-goal "allnc x^(CoI(~x^) -> CoI x^)")
(assume "x^" "CoI-x")
(coind "CoI-x")
(assume "x^1" "CoI-x1")
(inst-with-to "CoIClause" (pt "~x^1") "CoI-x1" "CoIClauseInst")
(by-assume "CoIClauseInst" "x^2" "x2Prop")
(by-assume "x2Prop" "d" "x2dProp")
(intro 0 (pt "~x^2"))
(ex-intro "SdInv d")
(split)
(intro 1)
(simp "MinusMinus")
(use "x2dProp")
(simp "<-" "MinusAvSd")
(simp "<-" "x2dProp")
(simp "MinusMinus")
(use "InitEqD")
;; Proof finished.
(save "CoIMinus")

(define eterm (proof-to-extracted-term))
(animate "CoIClause")
(define neterm (rename-variables (nt eterm)))
(ppc neterm)
;; [v](CoRec iv=>iv)v([v0]inv left Des v0@InR right Des v0)

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
	 '("allnc x^ all a(G x^ -> G(inv a***(x^ av PLft)))" "GenLR")
	 '("allnc x^(H x^ -> G(x^ av Mid))" "GenU")
	 '("allnc x^ all a(G x^ -> H(a***(x^ av PRht)))" "GenFin")
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
;;  exr x^0 ex a(CoG x^0 andl x^ eqd inv a***(x^0 av PLft)) ord 
;;  exr x^0(CoH x^0 andl x^ eqd x^0 av Mid))

;; By the greatest-fixed-point (or coinduction) axiom CoG is a fixed
;; point.  Hence the inverse implication holds as well.

;; CoGClauseInv
(set-goal "allnc x^(
 exr x^0 ex a(CoG x^0 andl x^ eqd inv a***(x^0 av PLft)) ord 
 exr x^0(CoH x^0 andl x^ eqd x^0 av Mid) -> CoG x^)")
(assume "x^" "Disj")
(coind "Disj"
       (pf "exr x^0 ex a(CoG x^0 andl x^ eqd a***(x^0 av PRht)) ord 
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
(set-goal "allnc x^ all a(CoG x^ -> CoG(inv a***(x^ av PLft)))")
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
;; Average for signed digits
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; We adapt examples/analysis/average.scm to the present setting.

(add-program-constant "AverageReal" (py "r=>r=>r"))
(add-infix-display-string "AverageReal" "avr" 'add-op)

(add-program-constant "Av" (py "r=>r=>sdtwo=>r"))
;; (Av r)x y i = (x+y+i)/4

;; ((x+d)/2 + (y+e)/2)/2 = (x+y+d+e)/4

(add-global-assumption
 "AverageRealAverage"
 "all x^,y^,d,e x^ av d avr(y^ av e)eqd(Av r)x^ y^(d plus e)")

(add-global-assumption
 "AverageRealAveragePsd"
 "all x^,y^,a,b x^ av a avr(y^ av b)eqd(Av r)x^ y^(a plus b)")

;; (remove-global-assumption "AverageRealAveragePsdMid")
(add-global-assumption
 "AverageRealAveragePsdMid"
 "all x^,y^,a x^ av a avr(y^ av Mid)eqd(Av r)x^ y^(a plus Mid)")

(add-global-assumption
 "AverageRealAverageMidPsd"
 "all x^,y^,b x^ av Mid avr(y^ av b)eqd(Av r)x^ y^(Mid plus b)")

;; ~ distributes over (Av r)

(add-rewrite-rule "~((Av r)x^ y^ i)" "(Av r)~x^ ~y^ inv i")
;; Added 2015-08-05
(add-rewrite-rule "a***((Av r)x^ y^ i)" "(Av r)(a***x^)(a***y^)(a times i)")

;; CoIAvToAvc
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
(save "CoIAvToAvc")

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

;; CoIAvcSatCoICl
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
(save "CoIAvcSatCoICl")

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

;; CoIAvcToCoI
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
(assume "CoIAvcSatCoIClInst")
(by-assume "CoIAvcSatCoIClInst" "x^2" "x2Prop")
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
(use-with "CoIAvcSatCoICl" (pt "i") (pt "x^1") (pt "y^1") "CoIx1" "CoIy1")
;; Proof finished.
(save "CoIAvcToCoI")

(define eterm (proof-to-extracted-term))
(add-var-name "ivw" (py "sdtwo@@iv@@iv"))
(add-var-name "jdvw" (py "sdtwo@@sd@@iv@@iv"))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)
;; [ivw]
;;  (CoRec sdtwo@@iv@@iv=>iv)ivw
;;  ([ivw0]
;;    [let jdvw
;;      (cCoIAvcSatCoICl left ivw0 left right ivw0 right right ivw0)
;;      (left right jdvw@InR(left jdvw@right right jdvw))])

;; CoIAverage
(set-goal "allnc x^,y^(CoI x^ -> CoI y^ -> CoI(x^ avr y^))")
(assume "x^" "y^" "CoIx" "CoIy")
(inst-with-to "CoIAvToAvc" (pt "x^") (pt "y^") "CoIx" "CoIy" "CoIAvToAvcInst")
(by-assume "CoIAvToAvcInst" "x^1" "x1Prop")
(by-assume "x1Prop" "y^1" "x1y1Prop")
(by-assume "x1y1Prop" "i" "x1y1iProp")
(simp "x1y1iProp")
(use "CoIAvcToCoI")
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
(animate "CoIAvcToCoI")
(define neterm (rename-variables (nt eterm)))
(ppc neterm)
;; [v,v0]
;;  (CoRec sdtwo@@iv@@iv=>iv)(cCoIAvToAvc v v0)
;;  ([ivw]
;;    [let jdvw
;;      (cCoIAvcSatCoICl left ivw left right ivw right right ivw)
;;      (left right jdvw@InR(left jdvw@right right jdvw))])

(animate "CoIAvToAvc")
(animate "CoIAvcSatCoICl")
(define neterm-CoIAverage (rename-variables (nt eterm)))
(pp neterm-CoIAverage)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; CoGToCoI
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; CoGToCoIAux
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
(save "CoGToCoIAux")

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
(set-goal "allnc x^(CoG(x^) -> CoI x^)")
(assume "x^" "CoGx")
(use "CoGToCoIAux")
(ex-intro "PRht")
(intro 0)
(use "CoGx")
;; Proof finished.
(save "CoGToCoI")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [p]cCoGToCoIAux(PRht@(InL ag ah)p)
(animate "CoGToCoIAux")
(define neterm-CoGToCoI (rename-variables (nt eterm)))
(ppc neterm-CoGToCoI)

;; [p]
;;  (CoRec psd@@(ag ysum ah)=>iv)(PRht@InL p)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; CoIToCoG
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; CoIToCoGAux
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
(simphyp-with-to "x2dProp" "d=Lft" "x2dPropSimp")
(ng "x2dPropSimp")
(simp "<-" "x2dPropSimp")
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
(save "CoIToCoGAux")

(define eterm (proof-to-extracted-term))
(add-var-name "bv" (py "psd@@iv")) ;av is used for average
(define neterm-CoIToCoGAux (rename-variables (nt eterm)))
(ppc neterm-CoIToCoGAux)
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

;; CoIToCoG
(set-goal "allnc x^(CoI(x^) -> CoG x^)")
(assume "x^" "CoGx")
(use "CoIToCoGAux")
(ex-intro "PRht")
(use "CoGx")
;; Proof finished.
(save "CoIToCoG")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(pp neterm)
;; [v]cCoIToCoGAux(PRht@v)
(animate "CoIToCoGAux")
(define neterm-CoIToCoG (rename-variables (nt eterm)))
(ppc neterm-CoIToCoG)
;; [v]
;;  (CoRec psd@@iv=>ag psd@@iv=>ah)(PRht@v)
;;  ([bv]
;;    [case (left Des right bv)
;;      (Lft -> InL(inv left bv@InR(PRht@right Des right bv)))
;;      (Rht -> InL(left bv@InR(PLft@right Des right bv)))
;;      (Mid -> InR(InR(left bv@right Des right bv)))])
;;  ([bv]
;;    [case (left Des right bv)
;;      (Lft -> InL(inv left bv@InR(PLft@right Des right bv)))
;;      (Rht -> InL(left bv@InR(PRht@right Des right bv)))
;;      (Mid -> InR(InR(left bv@right Des right bv)))])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Average for Gray code
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; We consider the problem to compute the average of two real numbers
;; given in pre-Gray code directly, without going via signed digit
;; code.

;; For CoGMinus we use the fact that our coinductive definitions are
;; in strengthened form.

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
(define neterm-CoGMinus (rename-variables (nt eterm)))
(pp neterm-CoGMinus)
;; [p](CoRec ag=>ag ah=>ah)p
;;  ([p0][if (Des p0)
;;      ([ap](InL (psd@@(ag ysum ag)) (ah ysum ah))
;;            (inv left ap@(InL ag ag)right ap))
;;      ([q](InR (ah ysum ah) (psd@@(ag ysum ag)))((InR ah ah)q))])
;;  ([q][if (Des q)
;;      ([ap](InL (psd@@(ag ysum ag)) (ah ysum ah))
;;            (inv left ap@(InL ag ag)right ap))
;;      ([q0](InR (ah ysum ah) (psd@@(ag ysum ag)))((InR ah ah)q0))])

(ppc neterm-CoGMinus)
;; [p](CoRec ag=>ag ah=>ah)p
;;  ([p0][case (Des p0)
;;      (InL ap -> InL(inv left ap@InL right ap))
;;      (inr q -> InR(InR q))])
;;  ([q][case (Des q)
;;      (InL ap -> InL(inv left ap@InL right ap))
;;      (InR q0 -> InR(InR q0))])

;; CoGPsdTimes
(set-goal "allnc x^ all a(CoG x^ -> CoG(a***x^))")
(assume "x^")
(cases)
;; Case PLft
(assume "CoGx")
(simp "PLftTimes")
(use "CoGMinus")
(simp "MinusMinus")
(use "CoGx")
;; Case PRht
(assume "CoGx")
(simp "PRhtTimes")
(use "CoGx")
;; Proof finished.
(save "CoGPsdTimes")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)
;; [a,p][case a (PLft -> cCoGMinus p) (PRht -> p)]

(animate "CoGMinus")
(define neterm-CoGPsdTimes (rename-variables (nt eterm)))
(ppc neterm-CoGPsdTimes)

;; [a,p][case a
;;    (PLft -> (CoRec ag=>ag ah=>ah)p
;;             ([p0][case (Des p0)
;;               (InL ap -> InL(inv left ap@InL right ap))
;;               (InR q -> InR(InR q))])
;;             ([q][case (Des q)
;;               (InL ap -> InL(inv left ap@InL right ap))
;;               (InR q0 -> InR(InR q0))]))
;;    (PRht -> p)]

;; CoHToCoG
(set-goal "allnc x^(CoH x^ -> CoG x^)")
(assume "x^" "CoHx")
(coind "CoHx" (pf "CoG x^ -> CoH x^"))
;; 3,4
(assume "x^1" "CoHx1")
(inst-with-to "CoHClause" (pt "x^1") "CoHx1" "CoHClauseInst")
(elim "CoHClauseInst")
;; 7,8
(drop "CoHClauseInst")
;; left case
(assume "ExHyp")
(by-assume "ExHyp" "x^2" "x2Prop")
(by-assume "x2Prop" "a" "x2aProp")
(intro 0)
(intro 0 (pt "~x^2"))
(ex-intro "a")
(split)
(intro 0)
(use "CoGMinus")
(ng #t)
(use "x2aProp")
(simp "x2aProp")
(ng #t)
(use "InitEqD")
;; middle case
(assume "ExHyp")
(by-assume "ExHyp" "x^2" "x2Prop")
(intro 1)
(intro 0 (pt "x^2"))
(split)
(intro 0)
(use "x2Prop")
(use "x2Prop")
;; 4
(assume "x^1" "CoGx1")
(inst-with-to "CoGClause" (pt "x^1") "CoGx1" "CoGClauseInst")
(elim "CoGClauseInst")
;; 40,41
(drop "CoGClauseInst")
;; left case
(assume "ExHyp")
(by-assume "ExHyp" "x^2" "x2Prop")
(by-assume "x2Prop" "a" "x2aProp")
(intro 0)
(intro 0 (pt "~x^2"))
(ex-intro "a")
(split)
(intro 0)
(use "CoGMinus")
(ng #t)
(use "x2aProp")
(simp "x2aProp")
(ng #t)
(use "InitEqD")
;; 41 middle case
(assume "ExHyp")
(by-assume "ExHyp" "x^2" "x2Prop")
(intro 1)
(intro 0 (pt "x^2"))
(split)
(intro 0)
(use "x2Prop")
(use "x2Prop")
;; Proof finished.
(save "CoHToCoG")

(define eterm (proof-to-extracted-term))
(deanimate "CoGMinus")
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [q](CoRec ah=>ag ag=>ah)q
;;  ([q0][if (Des q0)
;;      ([ap](InL (psd@@(ag ysum ah)) (ah ysum ag))
;;            (left ap@(InL ag ah)(cCoGMinus right ap)))
;;      ([q1](InR (ah ysum ag) (psd@@(ag ysum ah)))((InL ah ag)q1))])
;;  ([p][if (Des p)
;;      ([ap](InL (psd@@(ag ysum ah)) (ah ysum ag))
;;            (left ap@(InL ag ah)(cCoGMinus right ap)))
;;      ([q0](InR (ah ysum ag) (psd@@(ag ysum ah)))((InL ah ag)q0))])

(ppc neterm)

;; [q](CoRec ah=>ag ag=>ah)q
;;  ([q0][case (Des q0)
;;      (InL ap -> InL(left ap@InL(cCoGMinus right ap)))
;;      (InR q1 -> InR(InL q1))])
;;  ([p][case (Des p)
;;      (InL ap -> InL(left ap@InL(cCoGMinus right ap)))
;;      (InR q0 -> InR(InL q0))])

(animate "CoGMinus")
(define neterm-CoHToCoG (rename-variables (nt eterm)))
(ppc neterm-CoHToCoG)

;; [q](CoRec ah=>ag ag=>ah)q
;;  ([q0][case (Des q0)
;;      (InL ap -> InL(left ap@InL
;;       ((CoRec ag=>ag ah=>ah)right ap
;;        ([p][case (Des p)
;;            (InL ap0 -> InL(inv left ap0@InL right ap0))
;;            (InR q1 -> InR(InR q1))])
;;        ([q1][case (Des q1)
;;            (InL ap0 -> InL(inv left ap0@InL right ap0))
;;            (InR q2 -> InR(InR q2))]))))
;;      (InR q1 -> InR(InL q1))])
;;  ([p][case (Des p)
;;      (InL ap -> InL(left ap@InL
;;       ((CoRec ag=>ag ah=>ah)right ap
;;        ([p0][case (Des p0)
;;            (InL ap0 -> InL(inv left ap0@InL right ap0))
;;            (InR q0 -> InR(InR q0))])
;;        ([q0][case (Des q0)
;;            (InL ap0 -> InL(inv left ap0@InL right ap0))
;;            (InR q1 -> InR(InR q1))]))))
;;      (InR q0 -> InR(InL q0))])

;; P := {(x+y)/2 | x,y in CoG}  (was: X)
;; Q := {(x+y+i)/4 | x,y in CoG cup CoH} (was: Y)

;; CoGAvToAvc
(set-goal "allnc x^,y^(
      CoG x^ -> 
      CoG y^ -> 
      exr x^1,y^1 ex i(CoG x^1 & CoG y^1 andl x^ avr y^ eqd(Av r)x^1 y^1 i))")
(assume "x^" "y^" "CoGx" "CoGy")
;; We first distinguish cases on CoG x
(inst-with-to "CoGClause" (pt "x^") "CoGx" "xCases")
(elim "xCases")
(drop "xCases")

;; Case LRx
(assume "ExHypx")
(by-assume "ExHypx" "x^1" "x1Prop")
(by-assume "x1Prop" "a" "x1aProp")

;; We distinguish cases on CoG y
(inst-with-to "CoGClause" (pt "y^") "CoGy" "yCases")
(elim "yCases")
(drop "yCases")

;; Subcase LRx, LRy
(assume "ExHypy")
(by-assume "ExHypy" "y^1" "y1Prop")
(by-assume "y1Prop" "b" "y1bProp")
(intro 0 (pt "inv a***x^1"))
(intro 0 (pt "inv b***y^1"))
(ex-intro "a plus b")
(msplit)
(simp "x1aProp")
(simp "y1bProp")
(ng #t)
;; Need AverageRealAveragePsd here
(simp "AverageRealAveragePsd")
(ng #t)
(use "InitEqD")
(use "CoGPsdTimes")
(use "y1bProp")
(use "CoGPsdTimes")
(use "x1aProp")
(drop "yCases")

;; Case LRx,Midy
(assume "ExHypy")
(by-assume "ExHypy" "y^1" "y1Prop")
(intro 0 (pt "inv a***x^1"))
(intro 0 (pt "y^1"))
(ex-intro "a plus Mid")
(msplit)
(simp "x1aProp")
(ng #t)
(simp "y1Prop")
(simp "AverageRealAveragePsdMid")
(ng #t)
(use "InitEqD")
(use "CoHToCoG")
(use "y1Prop")
(use "CoGPsdTimes")
(use "x1aProp")

;; 6 Case Midx
(assume "ExHypx")
(by-assume "ExHypx" "x^1" "x1Prop")

;; We distinguish cases on CoG y
(inst-with-to "CoGClause" (pt "y^") "CoGy" "yCases")
(elim "yCases")
(drop "yCases")

;; Subcase Midx, LRy
(assume "ExHypy")
(by-assume "ExHypy" "y^1" "y1Prop")
(by-assume "y1Prop" "b" "y1bProp")
(intro 0 (pt "x^1"))
(intro 0 (pt "inv b***y^1"))
(ex-intro "Mid plus b")
(msplit)
(simp "y1bProp")
(ng #t)
(simp "x1Prop")
(simp "AverageRealAverageMidPsd")
(ng #t)
(use "InitEqD")
(use "CoGPsdTimes")
(use "y1bProp")
(use "CoHToCoG")
(use "x1Prop")

;; Subcase Midx, Midy
(assume "ExHypy")
(by-assume "ExHypy" "y^1" "y1Prop")
(intro 0 (pt "x^1"))
(intro 0 (pt "y^1"))
(ex-intro "Mid plus Mid")
(msplit)
(simp "x1Prop")
(simp "y1Prop")
(simp "AverageRealAverage")
(ng #t)
(use "InitEqD")
(use "CoHToCoG")
(use "y1Prop")
(use "CoHToCoG")
(use "x1Prop")
;; Proof finished.
(save "CoGAvToAvc")

(define eterm (proof-to-extracted-term))
(define neterm-CoGAvToAvc (rename-variables (nt eterm)))
(ppc neterm-CoGAvToAvc)

;; [p,p0]
;;  [case (Des p)
;;    (InL ap -> 
;;    [case (Des p0)
;;      (InL ap0 -> 
;;      left ap plus left ap0@
;;      cCoGPsdTimes inv left ap right ap@cCoGPsdTimes inv left ap0 right ap0)
;;      (InR q -> left ap plus Mid@cCoGPsdTimes inv left ap right ap@
;;                cCoHToCoG q)])
;;    (InR q -> 
;;    [case (Des p0)
;;      (InL ap -> 
;;      Mid plus left ap@cCoHToCoG q@cCoGPsdTimes inv left ap right ap)
;;      (InR q0 -> MT@cCoHToCoG q@cCoHToCoG q0)])]

;; SdDisj
(set-goal "all d(d=Mid orr ex a d=PsdToSd a)")
(cases)
(intro 1)
(ex-intro "PLft")
(use "Truth")
(intro 1)
(ex-intro "PRht")
(use "Truth")
(intro 0)
(use "Truth")
;; Proof finsihed.
(save "SdDisj")

(define eterm (proof-to-extracted-term))
(define neterm-SdDisj (rename-variables (nt eterm)))
(ppc neterm-SdDisj)
;; [d][case d (Lft -> Inr PLft) (Rht -> Inr PRht) (Mid -> DummyL)]

;; CoGAvcSatCoICl
(set-goal "all i 
     allnc x^,y^(
      CoG x^ -> 
      CoG y^ -> 
      exr x^0,y^0 
       ex j,d(CoG x^0 & CoG y^0 andl (Av r)x^ y^ i eqd(Av r)x^0 y^0 j av d))")
(assume "i" "x^" "y^" "CoGx" "CoGy")
(inst-with-to "CoGClause" (pt "x^") "CoGx" "CoGClauseInstx")
(elim "CoGClauseInstx")
;; 5,6
(drop "CoGClauseInstx")
(assume "CoGClauseInstxLeft")
(by-assume "CoGClauseInstxLeft" "x^1" "x1Prop")
(by-assume "x1Prop" "a" "x1aProp")
(inst-with-to "CoGClause" (pt "y^") "CoGy" "CoGClauseInsty")
(elim "CoGClauseInsty")
;; 17,18
(drop "CoGClauseInsty")
(assume "CoGClauseInstyLeft")
(by-assume "CoGClauseInstyLeft" "y^1" "y1Prop")
(by-assume "y1Prop" "b" "y1bProp")
(intro 0 (pt "inv a***x^1"))
(intro 0 (pt "inv b***y^1"))
(ex-intro "J a b i")
(ex-intro "K a b i")
(msplit)
(simp "<-" "JKAxiom")
(simp "x1aProp")
(simp "y1bProp")
;; (simp "PsdTimesAv")
;; (simp "PsdTimesAv")
(ng #t)
(use "InitEqD")
(use "CoGPsdTimes")
(use "y1bProp")
(use "CoGPsdTimes")
(use "x1aProp")
;; 18
(drop "CoGClauseInsty")
(assume "CoGClauseInstyRight")
(by-assume "CoGClauseInstyRight" "y^1" "y1Prop")
(intro 0 (pt "inv a***x^1"))
(intro 0 (pt "y^1"))
(ex-intro "J a Mid i")
(ex-intro "K a Mid i")
(msplit)
(simp "<-" "JKAxiom")
(simp "x1aProp")
(simp "y1Prop")
;; (simp "PsdTimesAv")
(ng #t)
(use "InitEqD")
(use "CoHToCoG")
(use "y1Prop")
(use "CoGPsdTimes")
(use "x1aProp")
;; 6
(drop "CoGClauseInstx")
(assume "CoGClauseInstxRight")
(by-assume "CoGClauseInstxRight" "x^1" "x1Prop")
(inst-with-to "CoGClause" (pt "y^") "CoGy" "CoGClauseInsty")
(elim "CoGClauseInsty")
;; 70.71
(drop "CoGClauseInsty")
(assume "CoGClauseInstyLeft")
(by-assume "CoGClauseInstyLeft" "y^1" "y1Prop")
(by-assume "y1Prop" "b" "y1bProp")
(intro 0 (pt "x^1"))
(intro 0 (pt "inv b***y^1"))
(ex-intro "J Mid b i")
(ex-intro "K Mid b i")
(msplit)
(simp "<-" "JKAxiom")
(simp "x1Prop")
(simp "y1bProp")
;; (simp "PsdTimesAv")
(ng #t)
(use "InitEqD")
(use "CoGPsdTimes")
(use "y1bProp")
(use "CoHToCoG")
(use "x1Prop")
;; 71
(drop "CoGClauseInsty")
(assume "CoGClauseInstyRight")
(by-assume "CoGClauseInstyRight" "y^1" "y1Prop")
(intro 0 (pt "x^1"))
(intro 0 (pt "y^1"))
(ex-intro "J Mid Mid i")
(ex-intro "K Mid Mid i")
(msplit)
(simp "<-" "JKAxiom")
(simp "x1Prop")
(simp "y1Prop")
(use "InitEqD")
(use "CoHToCoG")
(use "y1Prop")
(use "CoHToCoG")
(use "x1Prop")
;; Proof finished.
(save "CoGAvcSatCoICl")

(define eterm (proof-to-extracted-term))
(define neterm-CoGAvcSatCoICl (rename-variables (nt eterm)))
(ppc neterm-CoGAvcSatCoICl)

;; [i,p,p0]
;;  [case (Des p)
;;    (InL ap -> 
;;    [case (Des p0)
;;      (InL ap0 -> 
;;      J(PsdToSd left ap)(PsdToSd left ap0)i@
;;      K(PsdToSd left ap)(PsdToSd left ap0)i@
;;      cCoGPsdTimes inv left ap right ap@cCoGPsdTimes inv left ap0 right ap0)
;;      (InR q -> 
;;      J(PsdToSd left ap)Mid i@
;;      K(PsdToSd left ap)Mid i@cCoGPsdTimes inv left ap right ap@cCoHToCoG q)])
;;    (InR q -> 
;;    [case (Des p0)
;;      (InL ap -> 
;;      J Mid(PsdToSd left ap)i@
;;      K Mid(PsdToSd left ap)i@cCoHToCoG q@cCoGPsdTimes inv left ap right ap)
;;      (InR q0 -> J Mid Mid i@K Mid Mid i@cCoHToCoG q@cCoHToCoG q0)])]

;; CoGAvcToCoG
(set-goal "allnc z^(
 exr x^,y^ ex i(CoG x^ & CoG y^ andl z^ eqd(Av r)x^ y^ i) -> CoG z^)")
(assume "z^" "Qz")
(coind "Qz" (pf "exr x^,y^ 
  ex i(CoG x^ & CoG y^ andl z^ eqd(Av r)x^ y^ i) -> CoH z^"))
;; 3,4
(assume "z^1" "Qz1")
(by-assume "Qz1" "x^" "xProp")
(by-assume "xProp" "y^" "xyProp")
(by-assume "xyProp" "i" "xyiProp")
(inst-with-to "xyiProp" 'left "CoGx")
(inst-with-to "xyiProp" 'right "xyiPropRight")
(drop "xyiProp")
(inst-with-to "xyiPropRight" 'left "CoGy")
(inst-with-to "xyiPropRight" 'right "z1Def")
(drop "xyiPropRight")
;; let introduction
(cut "exr x^0,y^0 
   ex j,d(CoG x^0 & CoG y^0 andl (Av r)x^ y^ i eqd(Av r)x^0 y^0 j av d)")
;; 25,26
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "ExCoGAvcSatCoICl")
(by-assume "ExCoGAvcSatCoICl" "x^1" "x1Prop")
(by-assume "x1Prop" "y^1" "x1y1Prop")
(by-assume "x1y1Prop" "i1" "x1y1i1Prop")
(by-assume "x1y1i1Prop" "d1" "x1y1i1d1Prop")
(inst-with-to "SdDisj" (pt "d1") "Disj")
(elim "Disj")
;; 43,44
(drop "Disj")
(assume "d1=Mid") ;case small
(intro 1)
(intro 0 (pt "(Av r)x^1 y^1 i1"))
(split)
(intro 1)
(intro 0 (pt "x^1"))
(intro 0 (pt "y^1"))
(ex-intro "i1")
(split)
(use "x1y1i1d1Prop")
(split)
(use "x1y1i1d1Prop")
(use "InitEqD")
(simp "z1Def")
(simp "<-" "d1=Mid")
(use "x1y1i1d1Prop")
;; 44
(drop "Disj")
(assume "ExHyp")
(by-assume "ExHyp" "a" "aDef")
(intro 0)
(intro 0 (pt "(Av r)(inv a***x^1)(inv a***y^1)(a times inv i1)"))
(ex-intro "a")
(split)
;; 69,70
(intro 1)
(intro 0 (pt "(inv a***x^1)"))
(intro 0 (pt "(inv a***y^1)"))
(ex-intro "a times inv i1")
(split)
(use "CoGPsdTimes")
(use "x1y1i1d1Prop")
(split)
(use "CoGPsdTimes")
(use "x1y1i1d1Prop")
(use "InitEqD")
;; 70
(simp "z1Def")
(ng #t)
(simp "x1y1i1d1Prop")
(simp "aDef")
(use "InitEqD")
;; 26
;; Now use CoGAvcSatCoICl
(use "CoGAvcSatCoICl")
(use "CoGx")
(use "CoGy")
;; 4
(assume "z^1" "Qz1")
(by-assume "Qz1" "x^" "xProp")
(by-assume "xProp" "y^" "xyProp")
(by-assume "xyProp" "i" "xyiProp")
(inst-with-to "xyiProp" 'left "CoGx")
(inst-with-to "xyiProp" 'right "xyiPropRight")
(drop "xyiProp")
(inst-with-to "xyiPropRight" 'left "CoGy")
(inst-with-to "xyiPropRight" 'right "z1Def")
(drop "xyiPropRight")
;; let introduction
(cut "exr x^0,y^0 
   ex j,d(CoG x^0 & CoG y^0 andl (Av r)x^ y^ i eqd(Av r)x^0 y^0 j av d)")
;; 107,108
(use-with "Id" (make-cterm (goal-to-formula (current-goal))) "?")
(assume "ExCoGAvcSatCoICl")
(by-assume "ExCoGAvcSatCoICl" "x^1" "x1Prop")
(by-assume "x1Prop" "y^1" "x1y1Prop")
(by-assume "x1y1Prop" "i1" "x1y1i1Prop")
(by-assume "x1y1i1Prop" "d1" "x1y1i1d1Prop")
(inst-with-to "SdDisj" (pt "d1") "Disj")
(elim "Disj")
;; 125,126
(drop "Disj")
(assume "d1=Mid") ;case small
(intro 1)
(intro 0 (pt "(Av r)x^1 y^1 i1"))
(split)
(intro 1)
(intro 0 (pt "x^1"))
(intro 0 (pt "y^1"))
(ex-intro "i1")
(split)
(use "x1y1i1d1Prop")
(split)
(use "x1y1i1d1Prop")
(use "InitEqD")
(simp "z1Def")
(simp "<-" "d1=Mid")
(use "x1y1i1d1Prop")
;; 126
(drop "Disj")
(assume "ExHyp")
(by-assume "ExHyp" "a" "aDef")
(intro 0)
(intro 0 (pt "(Av r)(a***x^1)(a***y^1)(a times i1)"))
(ex-intro "a")
(split)
;; 151,152
(intro 1)
(intro 0 (pt "(a***x^1)"))
(intro 0 (pt "(a***y^1)"))
(ex-intro "a times i1")
(split)
(use "CoGPsdTimes")
(use "x1y1i1d1Prop")
(split)
(use "CoGPsdTimes")
(use "x1y1i1d1Prop")
(use "InitEqD")
;; 152
(simp "z1Def")
(ng #t)
(simp "x1y1i1d1Prop")
(simp "aDef")
(use "InitEqD")
;; 26
;; Now use CoGAvcSatCoICl
(use "CoGAvcSatCoICl")
(use "CoGx")
(use "CoGy")
;; Proof finished.
(save "CoGAvcToCoG")

(define eterm (proof-to-extracted-term))
(add-var-name "ipp" (py "sdtwo@@ag@@ag"))
(add-var-name "idpp" (py "sdtwo@@sd@@ag@@ag"))
(define neterm-CoGAvcToCoG (rename-variables (nt eterm)))
(ppc neterm-CoGAvcToCoG)

;; [ipp]
;;  (CoRec sdtwo@@ag@@ag=>ag sdtwo@@ag@@ag=>ah)ipp
;;  ([ipp0]
;;    [let idpp
;;      (cCoGAvcSatCoICl left ipp0 left right ipp0 right right ipp0)
;;      [case (cSdDisj left right idpp)
;;       (DummyL -> InR(InR(left idpp@right right idpp)))
;;       (Inr a -> 
;;       InL
;;       (a@
;;        InR
;;        (a times inv left idpp@
;;         cCoGPsdTimes inv a left right right idpp@
;;         cCoGPsdTimes inv a right right right idpp)))]])
;;  ([ipp0]
;;    [let idpp
;;      (cCoGAvcSatCoICl left ipp0 left right ipp0 right right ipp0)
;;      [case (cSdDisj left right idpp)
;;       (DummyL -> InR(InR(left idpp@right right idpp)))
;;       (Inr a -> 
;;       InL
;;       (a@
;;        InR
;;        (a times left idpp@
;;         cCoGPsdTimes a left right right idpp@
;;         cCoGPsdTimes a right right right idpp)))]])

;; CoGAverage
(set-goal "allnc x^,y^(CoG x^ -> CoG y^ -> CoG(x^ avr y^))")
(assume "x^" "y^" "CoGx" "CoGy")
(use "CoGAvcToCoG")
(use "CoGAvToAvc")
(use "CoGx")
(use "CoGy")
;; Proof finished.
(save "CoGAverage")

(define eterm (proof-to-extracted-term))
(define neterm-CoGAverage (rename-variables (nt eterm)))
(ppc neterm-CoGAverage)

;; [p,p0]cCoGAvcToCoG(cCoGAvToAvc p p0)

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

;; CoGToBGAux
(set-goal "all n(allnc x^(CoG x^ -> BG x^ n & BG x^(Succ n)) &
 allnc x^(CoH x^ ->
  (BH x^ n ord exr y^ ex a(CoG y^ & BG y^(Pred n) & x^ eqd a***(y^ av Rht))) &
  (BH x^(Succ n) ord exr y^ ex a(CoG y^ & BG y^ n & x^ eqd a***(y^ av Rht)))))")
(ind)
;; Base
(split)
(assume "x^" "CoGx")
(split)
(use "InitBG")
(inst-with-to "CoGClause" (pt "x^") "CoGx" "CoGClauseInst")
(elim "CoGClauseInst")
(drop "CoGClauseInst")
;;
(assume "ExHypLR")
(by-assume "ExHypLR" "x^1" "x1Prop")
(by-assume "x1Prop" "a" "x1aProp")
(simp "x1aProp")
(use "GenLRz")
(use "InitBG")
(drop "CoGClauseInst")
;;
(assume "ExHypU")
(by-assume "ExHypU" "x^1" "x1Prop")
(simp "x1Prop")
(use "GenUz")
(use "InitBH")
;;
(assume "x^" "CoHx")
(split)
(intro 0)
(use "InitBH")
(inst-with-to "CoHClause" (pt "x^") "CoHx" "CoHClauseInst")
(elim "CoHClauseInst")
(drop "CoHClauseInst")
;;
(assume "ExHypFin")
(by-assume "ExHypFin" "x^1" "x1Prop")
(by-assume "x1Prop" "a" "x1aProp")
(simp "x1aProp")
(intro 1)
(intro 0 (pt "x^1"))
(ex-intro "a")
(msplit)
(use "InitEqD")
(use "InitBG")
(use "x1aProp")
(drop "CoHClauseInst")
;;
(assume "ExHypD")
(by-assume "ExHypD" "x^1" "x1Prop")
(intro 0)
(simp "x1Prop")
(use "GenBH")
(use "InitBH")
;; Step
(assume "n" "IndHyp")
(inst-with-to "IndHyp" 'left "IHBG")
(inst-with-to "IndHyp" 'right "IHBH")
(drop "IndHyp")
(split)
;; Case CoGx
(assume "x^" "CoGx")
(split)
(use-with "IHBG" (pt "x^") "CoGx" 'right)
;; Goal 72: BG x^(Succ(Succ n))
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
;; (simp "x1Prop")
;; (use "GenUz")
(inst-with-to "x1Prop" 'left "CoHx1")
(inst-with-to "IHBH" (pt "x^1") "CoHx1" 'right "IHBHInst")
(elim "IHBHInst")
(drop "IHBHInst")
;;
(assume "BHx1Sn")
(simp "x1Prop")
(use "GenUz")
(use "BHx1Sn")
(drop "IHBHInst")
;; 
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
 (simp "<-" "PsdTimesAvSd")
 (simp "AvSdMid")
 (ng #t)
 (use "InitEqD")
(assume "xProp")
(simp "xProp")
(use "GenLRz")
(simp "x3Def")
(use "GenLRz")
(use "x2aProp")
;; Case CoHx
(assume "x^" "CoHx")
(split)
(use-with "IHBH" (pt "x^") "CoHx" 'right)
;; Goal 138:BH x^(Succ(Succ n)) ord 
;;       exr y^ ex a(CoG y^ & BG y^(Succ n) & x^ eqd a***(y^ av Rht))
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
(inst-with-to "IHBH" (pt "x^1") "CoHx1" 'right "IHBHInst")
(elim "IHBHInst")
(drop "IHBHInst")
;;
(assume "BHx1Sn")
(simp "x1Prop")
(intro 0)
(use "GenBH")
(use "BHx1Sn")
(drop "IHBHInst")
;; 
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
 (simp "<-" "PsdTimesAvSd")
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
;; Proof finished.
(save "CoGToBGAux")

(define eterm (proof-to-extracted-term))
(animate "GenCoGLR")
;; (display-default-varnames)
(add-var-name
 "psf" ;for pair of step functions
 (py "(ag=>bg@@bg)@@(ah=>(nat ysum psd@@ag@@bg)@@(nat ysum psd@@ag@@bg))"))
(add-var-name "apbg" (py "psd@@ag@@bg"))
(define neterm (rename-variables (nt eterm)))
(define nneterm (rename-variables (nt (undelay-delayed-corec neterm 1))))
(ppc nneterm)
;; [n0]
;; (Rec nat=>(ag=>bg@@bg)@@(ah=>(nat ysum psd@@ag@@bg)@@(nat ysum psd@@ag@@bg)))
;;  n0
;;  (([p2]Nz@[case (Des p2) (InL ap3 -> LRz left ap3 Nz) (InR q3 -> Uz Zero)])@
;;   ([q2]
;;     InL Zero@
;;     [case (Des q2)
;;       (InL ap3 -> InR(left ap3@right ap3@Nz))
;;       (InR q3 -> InL(Succ Zero))]))
;;  ([n2,psf3]
;;    ([p4]
;;      right(left psf3 p4)@
;;      [case (Des p4)
;;        (InL ap5 -> LRz left ap5 right(left psf3 right ap5))
;;        (InR q5 -> 
;;        [case (right(right psf3 q5))
;;          (InL n -> Uz n)
;;          (InR apbg6 -> LRz left apbg6(LRz PRht right right apbg6))])])@
;;    ([q4]
;;      right(right psf3 q4)@
;;      [case (Des q4)
;;        (InL ap5 -> InR(left ap5@right ap5@right(left psf3 right ap5)))
;;        (InR q5 -> 
;;        [case (right(right psf3 q5))
;;          (InL n6 -> InL(Succ n6))
;;          (InR apbg6 -> 
;;          InR
;;          (left apbg6@
;;           LR PLft left right apbg6@
;;           right(left psf3(LR PLft left right apbg6))))])]))

;; CoGToBG
(set-goal "all n allnc x^(CoG x^ -> BG x^ n)")
(assume "n" "x^" "CoGx")
(use "CoGToBGAux")
(use "CoGx")
;; Proof finished.
(save "CoGToBG")

(define eterm (proof-to-extracted-term))
(animate "CoGToBGAux")
(define neterm-CoGToBG (rename-variables (nt eterm)))
(define nneterm (nt (undelay-delayed-corec neterm-CoGToBG 1)))
(ppc nneterm)
;; [n0,p1]
;;  left(left((Rec nat=>(ag=>bg@@bg)@@(ah=>(nat ysum psd@@ag@@bg)@@
;;                                         (nat ysum psd@@ag@@bg)))
;;            n0
;;            (([p2]Nz@[case (Des p2)
;;                       (InL ap3 -> LRz left ap3 Nz)
;;                       (InR q3 -> Uz Zero)])@
;;             ([q2]
;;               InL Zero@
;;               [case (Des q2)
;;                 (InL ap3 -> InR(left ap3@right ap3@Nz))
;;                 (InR q3 -> InL(Succ Zero))]))
;;            ([n2,psf3]
;;              ([p4]right(left psf3 p4)@
;;                [case (Des p4)
;;                  (InL ap5 -> LRz left ap5 right(left psf3 right ap5))
;;                  (InR q5 -> 
;;                  [case (right(right psf3 q5))
;;                    (InL n -> Uz n)
;;                    (InR apbg6 ->
;;                      LRz left apbg6(LRz PRht right right apbg6))])])@
;;              ([q4]right(right psf3 q4)@
;;                [case (Des q4)
;;                  (InL ap5 -> 
;;                  InR(left ap5@right ap5@right(left psf3 right ap5)))
;;                  (InR q5 -> 
;;                  [case (right(right psf3 q5))
;;                    (InL n6 -> InL(Succ n6))
;;                    (InR apbg6 -> 
;;                    InR
;;                    (left apbg6@
;;                     LR PLft left right apbg6@
;;                     right(left psf3(LR PLft left right apbg6))))])])))
;;       p1)

;; For CoGToModCoG we will need

;; CoHClauseInv
(set-goal "allnc x^(
 exr x^0 ex a(CoG x^0 andl x^ eqd a***(x^0 av PRht)) ord 
 exr x^0(CoH x^0 andl x^ eqd x^0 av Mid) -> CoH x^)")
(assume "x^" "Disj")
(coind "Disj"
       (pf "exr x^0 ex a(CoG x^0 andl x^ eqd inv a***(x^0 av PLft)) ord 
            exr x^0(CoH x^0 andl x^ eqd x^0 av Mid) -> CoG x^"))
;; 3,4
(drop "Disj")
(assume "x^1" "x1Prop")
(elim "x1Prop")
;; 7,8
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
;; 36
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
(save "CoHClauseInv")

(define eterm (proof-to-extracted-term))
(define neterm-CoHClauseInv (rename-variables (nt eterm)))
(ppc neterm-CoHClauseInv)
;; [atpq]
;;  (CoRec psd@@ag ysum ah=>ah psd@@ag ysum ah=>ag)atpq
;;  ([atpq0]
;;    [case atpq0 (InL ap -> InL(left ap@InL right ap)) (InR q -> InR(InL q))])
;;  ([atpq0]
;;    [case atpq0 (InL ap -> InL(left ap@InL right ap)) (InR q -> InR(InL q))])

;; Same as for CoGClauseInv

;; Problem:
(pp (nt (pt "a***(x^ av Lft)"))) ;"a***x^ av inv a"
(pp (pt "a***x^ av inv a")) ;error.  Should have PsdToSd(inv a)
;; This is cured in the present approach with AverageRealSd as well as
;; AverageRealPsd

;; Added 2015-08-18.  Axiom as rewrite rule
(add-rewrite-rule "x^ av inv a av a" "x^ av a av Mid")
(add-rewrite-rule "x^ av a av inv a" "x^ av inv a av Mid")

(add-rewrite-rule "x^ av PLft av PRht" "x^ av PRht av Mid")
(add-rewrite-rule "x^ av PRht av PLft" "x^ av PLft av Mid")

;; (add-rewrite-rule "a***x^ av Mid" "a***(x^ av Mid)")

(add-global-assumption
 "AAMidEqInvAMidA"
 "all x^,a x^ av a av a av Mid eqd x^ av inv a av Mid av a")

(add-global-assumption
 "PsdTimesNotZero"
 "all x^,a((x^ eqd(Z r) -> F) -> a***x^ eqd(Z r) -> F)")

(add-global-assumption
 "AANotZero"
 "all x^,a(x^ av a av a eqd(Z r) -> F)")

(add-global-assumption
 "RMidLNotZero"
 "all x^(x^ av PRht av Mid av PLft eqd(Z r) -> F)")

(add-global-assumption
 "LMidRNotZero"
 "all x^(x^ av PLft av Mid av PRht eqd(Z r) -> F)")

(add-global-assumption
 "MidNotZero"
 "all x^((x^ eqd(Z r) -> F) -> x^ av Mid eqd(Z r) -> F)")

(add-global-assumption
 "MidANotZero"
 "all x^,a(x^ av Mid av a eqd(Z r) -> F)")

(add-program-constant "PMH" (py "r=>boole")) ;plus minus one half

(add-global-assumption
 "PsdTimesNotPMH"
 "all x^,a(((PMH r)x^ -> F) -> (PMH r)(a***x^) -> F)")

(add-global-assumption
 "MidMidNotPMH"
 "all x^((PMH r)(x^ av Mid av Mid) -> F)")

(add-global-assumption
 "MidAMidNotPMH"
 "all x^,a((PMH r)(x^ av Mid av a av Mid) -> F)")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Inductive predicates M and N
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(add-ids (list (list "M" (make-arity (py "r")) "ag")
	       (list "N" (make-arity (py "r")) "ah"))
      	 '("allnc x^,y^ all a(M x^ -> y^ eqd inv a***(x^ av PLft) ->
                              (y^ eqd(Z r) -> F) -> M y^)" "GenMLR")
	 '("allnc x^,y^(N x^ -> y^ eqd x^ av Mid ->
                        ((PMH r)y^ -> F) -> M y^)" "GenMU")
	 '("allnc x^,y^ all a(M x^ -> y^ eqd a***(x^ av PRht) ->
                              (y^ eqd(Z r) -> F) -> N y^)" "GenNFin")
	 '("allnc x^,y^(N x^ -> y^ eqd x^ av Mid ->
                        ((PMH r)y^ -> F) -> N y^)" "GenND"))

;; We add the companion predicate CoM for M, meant to be the
;; greatest-fixed-point of the M clauses.

(add-co "M")
;; (pp "CoMClause")

;; CoGToCoM
(set-goal "allnc x^(CoG x^ -> CoM x^)")
(assume "x^" "CoGx")
(coind "CoGx" (pf "CoH x^ -> CoN x^"))
;; 3,4
;; Case g
(assume "x^0" "CoGx0")
(inst-with-to "CoGClause" (pt "x^0") "CoGx0" "CoGClauseInst")
(elim "CoGClauseInst")
;; 8,9
(drop "CoGClauseInst")
;; Case ga
(assume "ExHyp1")
(by-assume "ExHyp1" "x^1" "x1Prop")
(by-assume "x1Prop" "a1" "x1a1Prop")
(inst-with-to "x1a1Prop" 'left "CoGx1")
(inst-with-to "CoGClause" (pt "x^1") "CoGx1" "CoGClauseInst1")
(elim "CoGClauseInst1")
;; 22,23
(drop "CoGClauseInst1")
;; Case gaa
(assume "ExHyp2")
(by-assume "ExHyp2" "x^2" "x2Prop")
(by-assume "x2Prop" "a2" "x2a2Prop")
(cases (pt "a2"))
;; 32,33
(assume "a2=PLft")
;; Case gaL
(intro 0) ;go for lhs of goal
(intro 0 (pt "x^1")) ;with x1
(intro 0 (pt "inv a1***(x^1 av PLft)"))
(ex-intro "a1") ;and a1
(split)
(intro 1) ;recursive call
(use "x1a1Prop")
(split)
(use "InitEqD")
(split)
(simp "x2a2Prop")
(simp "a2=PLft")
(use "PsdTimesNotZero")
(ng #t)
(use "AANotZero")
(use "x1a1Prop")
;; 33
(assume "a2=PRht")
;; Case gaR
(inst-with-to "x2a2Prop" 'left "CoGx2")
(inst-with-to "CoGClause" (pt "x^2") "CoGx2" "CoGClauseInst2")
(elim "CoGClauseInst2")
;; 55,56
(drop "CoGClauseInst2")
;; Case gaRa
(assume "ExHyp3")
(by-assume "ExHyp3" "x^3" "x3Prop")
(by-assume "x3Prop" "a3" "x3a3Prop")
(cases (pt "a3"))
;; 65,66
(assume "a3=PLft")
;; Case gaRL
(intro 1) ;go for rhs of goal
(intro 0 (pt "a1***(x^2 av PRht)")) ;with delta(a1)(x_2)
(intro 0 (pt "a1***(x^2 av PRht)av Mid"))
(split)
(intro 1) ;recursive call
(use "CoHClauseInv")
(intro 0)
(intro 0 (pt "x^2"))
(ex-intro "a1")
(split)
(use "x2a2Prop")
(use "InitEqD")
(split)
(use "InitEqD")
(split)
(simp "x3a3Prop")
(simp "a3=PLft")
(ng #t)
(use "MidMidNotPMH")
(simp "x1a1Prop")
(simp "x2a2Prop")
(simp "a2=PRht")
(ng #t)
(use "InitEqD")
;; 66
(assume "a3=PRht")
;; Case gaRR
(intro 0) ;go for lhs of goal
(intro 0 (pt "x^1")) ;with x1
(intro 0 (pt "inv a1***(x^1 av PLft)"))
(ex-intro "a1") ;and a1
(split)
(intro 1) ;recursive call
(use "x1a1Prop")
(split)
(use "InitEqD")
(split)
(use "PsdTimesNotZero")
(simp "x2a2Prop")
(simp "a2=PRht")
(simp "x3a3Prop")
(simp "a3=PRht")
(ng #t)
(use "RMidLNotZero")
(use "x1a1Prop")
;; 56
(drop "CoGClauseInst2")
;; Case gaRU
(assume "ExHyp3")
(by-assume "ExHyp3" "x^3" "x3Prop")
(intro 0) ;go for lhs of goal
(intro 0 (pt "x^1")) ;with x1
(intro 0 (pt "inv a1***(x^1 av PLft)"))
(ex-intro "a1")
(split)
(intro 1) ;recursive call
(use "x1a1Prop")
(split)
(use "InitEqD")
(split)
(use "PsdTimesNotZero")
(simp "x2a2Prop")
(simp "a2=PRht")
(simp "x3Prop")
(ng #t)
(use "MidNotZero")
(use "MidANotZero")
(use "x1a1Prop")
;; 23
(drop "CoGClauseInst1")
;; Case gaU
(assume "ExHyp2")
(by-assume "ExHyp2" "x^2" "x2Prop")
(intro 0) ;go for lhs of goal
(intro 0 (pt "x^1")) ;with x1
(intro 0 (pt "inv a1***(x^1 av PLft)"))
(ex-intro "a1") ;and a1
(split)
(intro 1) ;recursive call
(use "x1a1Prop")
(split)
(use "InitEqD")
(split)
(use "PsdTimesNotZero")
(simp "x2Prop")
(use "MidANotZero")
(use "x1a1Prop")
;; 9
(drop "CoGClauseInst")
;; Case gU
(assume "ExHyp1")
(by-assume "ExHyp1" "x^1" "x1Prop")
(inst-with-to "x1Prop" 'left "CoHx1")
(inst-with-to "CoHClause" (pt "x^1") "CoHx1" "CoHClauseInst1")
(elim "CoHClauseInst1")
;; 158,159
(drop "CoHClauseInst1")
;; Case gUa
(assume "ExHyp2")
(by-assume "ExHyp2" "x^2" "x2Prop")
(by-assume "x2Prop" "a2" "x2a2Prop")
(inst-with-to "x2a2Prop" 'left "CoGx2")
(inst-with-to "CoGClause" (pt "x^2") "CoGx2" "CoGClauseInst2")
(elim "CoGClauseInst2")
;; 172,173
(drop "CoGClauseInst2")
;; Case gUaa
(assume "ExHyp3")
(by-assume "ExHyp3" "x^3" "x3Prop")
(by-assume "x3Prop" "a3" "x3a3Prop")
(cases (pt "a3"))
;; 182,183
(assume "a3=PLft")
;; Case gUaL
(intro 1) ;go for rhs of goal
(intro 0 (pt "a2***(x^2 av PRht)")) ;with delta(a2)(x_2)
(intro 0 (pt "a2***(x^2 av PRht)av Mid"))
(split)
(intro 1) ;recursive call
(use "CoHClauseInv")
(intro 0)
(intro 0 (pt "x^2"))
(ex-intro "a2")
(split)
(use "x2a2Prop")
(use "InitEqD")
(split)
(use "InitEqD")
(split)
(simp "x3a3Prop")
(simp "a3=PLft")
(ng #t)
(use "MidMidNotPMH")
(simp "x1Prop")
(simp "x2a2Prop")
(use "InitEqD")
;; 183
(assume "a3=PRht")
;; Case gUaR
(intro 0) ;go for lhs of goal
(intro 0 (pt "x^3 av PRht av Mid"))
(intro 0 (pt "inv a2***(x^3 av PRht av Mid av PLft)"))
(ex-intro "a2") ;and a2
(split)
(intro 1) ;recursive call
(use "CoGClauseInv")
(intro 1)
(intro 0 (pt "x^3 av PRht"))
(split)
(use "CoHClauseInv")
(intro 0)
(intro 0 (pt "x^3"))
(ex-intro "PRht")
(split)
(use "x3a3Prop")
(use "InitEqD")
(use "InitEqD")
(split)
(use "InitEqD")
(split)
(use "PsdTimesNotZero")
(use "RMidLNotZero")
(simp "x1Prop")
(simp "x2a2Prop")
(simp "x3a3Prop")
(simp "a3=PRht")
(ng #t)
(use "AAMidEqInvAMidA")
;; 173
(drop "CoGClauseInst2")
;; Case gUaU
(assume "ExHyp3")
(by-assume "ExHyp3" "x^3" "x3Prop")
(intro 1) ;go for rhs of goal
(intro 0 (pt "a2***(x^2 av PRht)")) ;with delta(a2)(x_2)
(intro 0 (pt "a2***(x^2 av PRht)av Mid"))
(split)
(intro 1) ;recursive call
(use "CoHClauseInv")
(intro 0)
(intro 0 (pt "x^2"))
(ex-intro "a2")
(split)
(use "x2a2Prop")
(use "InitEqD")
(split)
(use "InitEqD")
(split)
(simp "x3Prop")
(ng #t)
(use "MidAMidNotPMH")
(simp "x1Prop")
(simp "x2a2Prop")
(use "InitEqD")
;; 159
(drop "CoHClauseInst1")
;; Case gUD
(assume "ExHyp2")
(by-assume "ExHyp2" "x^2" "x2Prop")
(intro 1) ;go to rhs of goal
(intro 0 (pt "x^1"))
(intro 0 (pt "x^1 av Mid"))
(split)
(intro 1) ;recursive call
(use "x1Prop")
(split)
(use "InitEqD")
(split)
(simp "x2Prop")
(use "MidMidNotPMH")
(use "x1Prop")
;; 4
;; Case h
(assume "x^0" "CoHx0")
(inst-with-to "CoHClause" (pt "x^0") "CoHx0" "CoHClauseInst")
(elim "CoHClauseInst")
;; 283,284
(drop "CoHClauseInst")
;; Case ha
(assume "ExHyp1")
(by-assume "ExHyp1" "x^1" "x1Prop")
(by-assume "x1Prop" "a1" "x1a1Prop")
(inst-with-to "x1a1Prop" 'left "CoGx1")
(inst-with-to "CoGClause" (pt "x^1") "CoGx1" "CoGClauseInst1")
(elim "CoGClauseInst1")
;; 297,298
(drop "CoGClauseInst1")
;; Case haa
(assume "ExHyp2")
(by-assume "ExHyp2" "x^2" "x2Prop")
(by-assume "x2Prop" "a2" "x2a2Prop")
(cases (pt "a2"))
(assume "a2=PLft")
;; Case haL
(inst-with-to "x2a2Prop" 'left "CoGx2")
(inst-with-to "CoGClause" (pt "x^2") "CoGx2" "CoGClauseInst2")
(elim "CoGClauseInst2")
;; 314,315
(drop "CoGClauseInst2")
;; Case haLa
(assume "ExHyp3")
(by-assume "ExHyp3" "x^3" "x3Prop")
(by-assume "x3Prop" "a3" "x3a3Prop")
(cases (pt "a3"))
;; 324,325
(assume "a3=PLft")
;; Case haLL
(intro 1) ;go for rhs of goal
(intro 0 (pt "a1***(x^2 av PRht)"))
(intro 0 (pt "a1***(x^2 av PRht) av Mid"))
(split)
(intro 1) ;recursive call
(use "CoHClauseInv")
(intro 0)
(intro 0 (pt "x^2"))
(ex-intro "a1")
(split)
(use "x2a2Prop")
(use "InitEqD")
(split)
(use "InitEqD")
(split)
(simp "x3a3Prop")
(simp "a3=PLft")
(ng #t)
(use "MidMidNotPMH")
(simp "x1a1Prop")
(simp "x2a2Prop")
(simp "a2=PLft")
(ng #t)
(use "InitEqD")
;; 325
(assume "a3=PRht")
;; Case haLR
(intro 0) ;go for lhs of goal
(intro 0 (pt "x^1")) ;with x1
(intro 0 (pt "a1***(x^1 av PRht)"))
(ex-intro "a1") ;and a1
(split)
(intro 1) ;recursive call
(use "x1a1Prop")
(split)
(use "InitEqD")
(split)
(use "PsdTimesNotZero")
(simp "x2a2Prop")
(simp "x3a3Prop")
(simp "a2=PLft")
(simp "a3=PRht")
(ng #t)
(use "LMidRNotZero")
(use "x1a1Prop")
;; 315
(drop "CoGClauseInst2")
;; Case haLU
(assume "ExHyp3")
(by-assume "ExHyp3" "x^3" "x3Prop")
(intro 0) ;go for lhs of goal
(intro 0 (pt "x^1")) ;with x1
(intro 0 (pt "a1***(x^1 av PRht)"))
(ex-intro "a1")
(split)
(intro 1) ;recursive call
(use "x1a1Prop")
(split)
(use "InitEqD")
(split)
(use "PsdTimesNotZero")
(simp "x2a2Prop")
(simp "x3Prop")
(simp "a2=PLft")
(ng #t)
(use "MidNotZero")
(use "MidANotZero")
(use "x1a1Prop")
;; 308
(assume "a2=PRht")
;; Case haR
(intro 0) ;go for lhs of goal
(intro 0 (pt "x^1")) ;with x1
(intro 0 (pt "a1***(x^1 av PRht)"))
(ex-intro "a1") ;and a1
(split)
(intro 1) ;recursive call
(use "x1a1Prop")
(split)
(use "InitEqD")
(split)
(simp "x2a2Prop")
(simp "a2=PRht")
(use "AANotZero")
(use "x1a1Prop")
;; 294
(drop "CoGClauseInst1")
;; Case haU
(assume "ExHyp2")
(by-assume "ExHyp2" "x^2" "x2Prop")
(intro 0) ;go for lhs of goal
(intro 0 (pt "x^1")) ;with x1
(intro 0 (pt "a1***(x^1 av PRht)"))
(ex-intro "a1") ;and a1
(split)
(intro 1) ;recursive call
(use "x1a1Prop")
(split)
(use "InitEqD")
(split)
(use "PsdTimesNotZero")
(simp "x2Prop")
(use "MidANotZero")
(use "x1a1Prop")
;; 280
(drop "CoHClauseInst")
;; Case hD
(assume "ExHyp1")
(by-assume "ExHyp1" "x^1" "x1Prop")
(inst-with-to "x1Prop" 'left "CoHx1")
(inst-with-to "CoHClause" (pt "x^1") "CoHx1" "CoHClauseInst1")
(elim "CoHClauseInst1")
;; 427,428
(drop "CoHClauseInst1")
;; Case hDa
(assume "ExHyp2")
(by-assume "ExHyp2" "x^2" "x2Prop")
(by-assume "x2Prop" "a2" "x2a2Prop")
(inst-with-to "x2a2Prop" 'left "CoGx2")
(inst-with-to "CoGClause" (pt "x^2") "CoGx2" "CoGClauseInst2")
(elim "CoGClauseInst2")
;; 441,442
(drop "CoGClauseInst2")
;; Case hDaa
(assume "ExHyp3")
(by-assume "ExHyp3" "x^3" "x3Prop")
(by-assume "x3Prop" "a3" "x3a3Prop")
(cases (pt "a3"))
;; 451,452
(assume "a3=PLft")
;; Case hDaL
(intro 1) ;go for rhs of goal
(intro 0 (pt "a2***(x^2 av PRht)")) ;with delta(a2)(x_2)
(intro 0 (pt "a2***(x^2 av PRht)av Mid"))
(split)
(intro 1) ;recursive call
(use "CoHClauseInv")
(intro 0)
(intro 0 (pt "x^2"))
(ex-intro "a2")
(split)
(use "x2a2Prop")
(use "InitEqD")
(split)
(use "InitEqD")
(split)
(simp "x3a3Prop")
(simp "a3=PLft")
(ng #t)
(use "MidMidNotPMH")
(simp "x1Prop")
(simp "x2a2Prop")
(use "InitEqD")
;; 452
(assume "a3=PRht")
;; Case hDaR
(intro 0) ;go for lhs of goal
(intro 0 (pt "~x^3 av PLft av Mid"))
(intro 0 (pt "a2***(~x^3 av PLft av Mid av PRht)"))
(ex-intro "a2") ;and a2
(split)
(intro 1) ;recursive call
(use "CoGClauseInv")
(intro 1)
(intro 0 (pt "~x^3 av PLft"))
(split)
(use "CoHClauseInv")
(intro 0)
(intro 0 (pt "x^3"))
(ex-intro "PLft")
(split)
(use "x3a3Prop")
(use "InitEqD")
(use "InitEqD")
(split)
(use "InitEqD")
(split)
(use "PsdTimesNotZero")
(use "LMidRNotZero")
(simp "x1Prop")
(simp "x2a2Prop")
(simp "x3a3Prop")
(simp "a3=PRht")
(ng #t)
(use "AAMidEqInvAMidA")
;; 442
(drop "CoGClauseInst2")
;; Case hDaU
(assume "ExHyp3")
(by-assume "ExHyp3" "x^3" "x3Prop")
(intro 1) ;go for rhs of goal
(intro 0 (pt "a2***(x^2 av PRht)")) ;with delta(a2)(x_2)
(intro 0 (pt "a2***(x^2 av PRht)av Mid"))
(split)
(intro 1) ;recursive call
(use "CoHClauseInv")
(intro 0)
(intro 0 (pt "x^2"))
(ex-intro "a2")
(split)
(use "x2a2Prop")
(use "InitEqD")
(split)
(use "InitEqD")
(split)
(simp "x3Prop")
(ng #t)
(use "MidAMidNotPMH")
(simp "x1Prop")
(simp "x2a2Prop")
(use "InitEqD")
;; 428
(drop "CoHClauseInst1")
;; Case hDD
(assume "ExHyp2")
(by-assume "ExHyp2" "x^2" "x2Prop")
(intro 1) ;go to rhs of goal
(intro 0 (pt "x^1"))
(intro 0 (pt "x^1 av Mid"))
(split)
(intro 1) ;recursive call
(use "x1Prop")
(split)
(use "InitEqD")
(split)
(simp "x2Prop")
(use "MidMidNotPMH")
(use "x1Prop")
;; Proof finished.
(save "CoGToCoM")

(define eterm (proof-to-extracted-term))
(deanimate "CoGClauseInv")
(define neterm-CoGToCoM (rename-variables (nt eterm)))
(ppc neterm-CoGToCoM)

;; [p](CoRec ag=>ag ah=>ah)p
;;  ([p0][case (Des p0)
;;      (InL ap -> [case (Des right ap)
;;        (InL ap0 -> [case (left ap0)
;;          (PLft -> InL(left ap@InR right ap))
;;          (PRht -> [case (Des right ap0)
;;            (InL ap1 -> [case (left ap1)
;;              (PLft -> InR(InR(cCoHClauseInv
;;                                (InL(left ap@right ap0)))))
;;              (PRht -> InL(left ap@InR right ap))])
;;            (InR q -> InL(left ap@InR right ap))])])
;;        (InR q -> InL(left ap@InR right ap))])
;;      (InR q -> [case (Des q)
;;        (InL ap -> [case (Des right ap)
;;          (InL ap0 -> [case (left ap0)
;;            (PLft -> InR(InR(cCoHClauseInv(InL ap))))
;;            (PRht -> InL(left ap@InR(cCoGClauseInv
;;                     (InR(cCoHClauseInv(InL(PRht@right ap0)))))))])
;;          (InR q0 -> InR(InR(cCoHClauseInv(InL ap))))])
;;        (InR q0 -> InR(InR q))])])
;;  ([q][case (Des q)
;;      (InL ap -> [case (Des right ap)
;;        (InL ap0 -> [case (left ap0)
;;          (PLft -> [case (Des right ap0)
;;            (InL ap1 -> [case (left ap1)
;;              (PLft -> InR(InR(cCoHClauseInv
;;                                (InL(left ap@right ap0)))))
;;              (PRht -> InL(left ap@InR right ap))])
;;            (InR q0 -> InL(left ap@InR right ap))])
;;          (PRht -> InL(left ap@InR right ap))])
;;        (InR q0 -> InL(left ap@InR right ap))])
;;      (InR q0 -> [case (Des q0)
;;        (InL ap -> [case (Des right ap)
;;          (InL ap0 -> [case (left ap0)
;;            (PLft -> InR(InR(cCoHClauseInv(InL ap))))
;;            (PRht -> InL(left ap@InR(cCoGClauseInv
;;                     (InR(cCoHClauseInv(InL(PLft@right ap0)))))))])
;;          (InR q1 -> InR(InR(cCoHClauseInv(InL ap))))])
;;        (InR q1 -> InR(InR q0))])])

;; We now aim for experiments.  To obtain interesting signed digit
;; streams we use material from cauchysds.scm.

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
(define neterm-CauchyToSds (rename-variables (nt eterm)))
(pp neterm-CauchyToSds)

;; [as]
;;  (CoRec (nat=>rat)=>iv)as
;;  ([as0]
;;    [let d (cSplitProp as0)
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
(define neterm-SdsToCauchy (rename-variables (nt eterm)))
(ppc neterm-SdsToCauchy)

;; [v,n]
;;  (Rec nat=>iv=>rat)n([v0]0)
;;  ([n0,(iv=>rat),v0]
;;    ((iv=>rat)right(cCoIClause v0)+SDToInt left(cCoIClause v0))/2)
;;  v

;; For experiments we define approximations to the square root of a rational.
(add-program-constant "sqrt" (py "rat=>nat=>rat"))
(add-program-constant "sqrtaux" (py "rat=>nat=>rat"))
(add-computation-rules
 "sqrtaux rat Zero" "Succ Zero"
 "sqrtaux rat(Succ n)" "((sqrtaux rat n) + (rat / (sqrtaux rat n)))/2")
(add-computation-rule "sqrt rat n" "sqrtaux rat(Succ n)")

(define threebyfour (pt "[n](3#4)"))

;; We had the following animate / deanimate usages.  They should all
;; have heen deanimated after usage.

;; (animate "CoIClauseInv")
;; (animate "GenCoI")
;; (animate "CoIClause")
;; (animate "CoGClauseInv")
;; (animate "CoIAvcToCoI")
;; (animate "CoIAvToAvc")
;; (animate "CoIAvcSatCoICl")
;; (animate "CoGToCoIAux")
;; (animate "CoIToCoGAux")
;; (animate "CoGClause")
;; (animate "CoHClause")
;; (animate "CoGMinus")
;; (animate "GenCoGLR")
;; (animate "CoGToBGAux")

;; We deanimate them all now.

(deanimate "CoIClauseInv")
(deanimate "GenCoI")
(deanimate "CoIClause")
(deanimate "CoGClauseInv")
(deanimate "CoIAvcToCoI")
(deanimate "CoIAvToAvc")
(deanimate "CoIAvcSatCoICl")
(deanimate "CoGToCoIAux")
(deanimate "CoIToCoGAux")
(deanimate "CoGClause")
(deanimate "CoHClause")
(deanimate "CoGMinus")
(deanimate "GenCoGLR")
(deanimate "CoGToBGAux")

(set! COMMENT-FLAG #t)

;; We use Christian Ittner's terms-to-haskell-program-with-lemmas to
;; animate in the right order, for proper subfunctions in the Haskell
;; export.

'(
(terms-to-haskell-program-with-lemmas
 "~/temp/gray.hs"
 (list (list neterm-CoIAverage "cCoIAverage")
       (list neterm-CoIToCoG "cCoIToCoG")
       (list neterm-CoGToCoI "cCoGToCoI")
       (list neterm-CoGAverage "cCoGAverage")
       (list neterm-CauchyToSds "cCauchyToSds")
       (list neterm-SdsToCauchy "cSdsToCauchy")
       (list neterm-CoGToBG "cCoGToBG")
       (list neterm-CoGToCoM "cCoGToCoM")))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; How to run the Haskell program.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; In a terminal type ghci examplesanalysisgraytvar.hs.  The result is

;; GHCi, version 7.0.4: http://www.haskell.org/ghc/  :? for help
;; Loading package ghc-prim ... linking ... done.
;; Loading package integer-gmp ... linking ... done.
;; Loading package base ... linking ... done.
;; Loading package ffi-1.0 ... linking ... done.
;; [1 of 1] Compiling Main             ( gray.hs, interpreted )
;; Ok, modules loaded: Main.
;; *Main> 

;; Experiments.  1.  Flip mode.

;; *Main> cCoIToCoG (C Rht (C Lft (C Rht (C Lft (cCauchyToSds (\ n -> 0))))))
;; LR PRht (LR PRht (LR PRht (LR PRht (U (D (D (D ...

;; *Main> cCoIToCoG (C Rht (C Rht (C Lft (C Rht (C Lft (cCauchyToSds (\ n -> 0)))))))
;; LR PRht (LR PLft (LR PRht (LR PRht (LR PRht (U (D (D (D ...

;; cCoGToCoI works as a converse

;; *Main> cCoGToCoI (cCoIToCoG (C Rht (C Lft (C Rht (C Lft (cCauchyToSds (\ n -> 0)))))))
;; C Rht (C Lft (C Rht (C Lft (C Mid (C Mid (C Mid ...

;; *Main> cCoGToCoI (cCoIToCoG (C Rht (C Rht (C Lft (C Rht (C Lft (cCauchyToSds (\ n -> 0))))))))
;; C Rht (C Rht (C Lft (C Rht (C Lft (C Mid (C Mid (C Mid ...

;; 2.  Block.

;; *Main> cCoIToCoG (C Mid (C Mid (C Rht (C Lft (cCauchyToSds (\ n -> 0))))))
;; U (D (Fin PRht (LR PLft (U (D (D (D ...

;; *Main> cCoGToCoI (cCoIToCoG (C Mid (C Mid (C Rht (C Lft (cCauchyToSds (\ n -> 0)))))))
;; C Mid (C Mid (C Rht (C Lft (C Mid (C Mid (C Mid ....

;; 3.  Flip mode in a block.

;; *Main> cCoIToCoG (C Mid (C Lft (C Rht (C Rht (cCauchyToSds (\ n -> 0))))))
;; U (Fin PLft (LR PLft (LR PLft (U (D (D (D ...

;; *Main> cCoIToCoG (C Mid (C Rht (C Rht (C Rht (cCauchyToSds (\ n -> 0))))))
;; U (Fin PRht (LR PRht (LR PLft (U (D (D (D ...

;; *Main> cCoIToCoG (C Rht (C Mid (C Mid (C Lft (C Lft (C Lft (cCauchyToSds (\ n -> 0))))))))
;; LR PRht (U (D (Fin PRht (LR PRht (LR PLft (U (D (D (D ...

;; 4.  Average.

;; *Main> cCoIAverage (cCauchyToSds (\ n -> (5 % 8))) (cCauchyToSds (\ n -> (3 % 4)))
;; C Rht (C Rht (C Mid (C Lft (C Mid (C Mid (C Mid ...

;; *Main> cCoIToCoG (cCauchyToSds (\ n -> (5 % 8)))
;; LR PRht (LR PLft (LR PRht (U (D (D ...

;; *Main> cCoIToCoG (cCauchyToSds (\ n -> (3 % 4)))
;; LR PRht (LR PLft (U (D (D ...

;; *Main> cCoGAverage (cCoIToCoG (cCauchyToSds (\ n -> (5 % 8)))) (cCoIToCoG (cCauchyToSds (\ n -> (3 % 4))))
;; LR PRht (LR PLft (U (Fin PRht (U (D (D ...

;; 5.  Gray code.

;; *Main> cCoGToBG 5 (U (D (Fin PLft (U (Fin PRht (cCoIToCoG (cCauchyToSds (\ n -> 0))))))))
;; LRz PLft (LRz PRht (LRz PLft (LRz PRht (LRz PRht Nz))))

;; *Main> cCoGToBG 5 (cCoIToCoG (cCauchyToSds (\ n -> 0)))
;; Uz 4

;; *Main> cCoGToBG 5 (U (Fin PLft (cCoIToCoG (cCauchyToSds (\ n -> 0)))))
;; LRz PLft (LRz PRht (Uz 2))

;; 6.  CoGToCoM

;; *Main> cCoGToCoM (LR PLft (LR PRht (LR PLft (cCoIToCoG (cCauchyToSds (\ n -> 0))))))
;; U (Fin PLft (LR PLft (U (D (D ...

;; *Main> cCoGToCoM (LR PRht (LR PRht (LR PLft (cCoIToCoG (cCauchyToSds (\ n -> 0))))))
;; U (Fin PRht (LR PLft (U (D (D ...

;; *Main> cCoGToCoM (U (Fin PLft (LR PRht (cCoIToCoG (cCauchyToSds (\ n -> 0))))))
;; LR PLft (LR PRht (LR PRht (U (D (D ...

;; *Main> cCoGToCoM (U (Fin PRht (LR PRht (cCoIToCoG (cCauchyToSds (\ n -> 0))))))
;; LR PRht (LR PRht (LR PRht (U (D (D ...

;; *Main> cCoGToCoM (U (Fin PLft (LR PLft (LR PLft (cCoIToCoG (cCauchyToSds (\ n -> 0)))))))
;; U (D (Fin PLft (LR PLft (U (D (D ...

;; *Main> cCoGToCoM (U (Fin PRht (LR PLft (LR PLft (cCoIToCoG (cCauchyToSds (\ n -> 0)))))))
;; U (D (Fin PRht (LR PLft (U (D (D ...

;; *Main> cCoGToCoM (U (D (Fin PLft (LR PRht (cCoIToCoG (cCauchyToSds (\ n -> 0)))))))
;; U (Fin PLft (LR PLft (LR PRht (U (D (D ...

;; *Main> cCoGToCoM (U (D (Fin PRht (LR PRht (cCoIToCoG (cCauchyToSds (\ n -> 0)))))))
;; U (Fin PRht (LR PLft (LR PRht (U (D (D ...

