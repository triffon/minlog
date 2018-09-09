;; 2018-09-08.  str.scm

;; (load "~/git/minlog/init.scm")
;; (set! COMMENT-FLAG #f)
;; (libload "nat.scm")
;; (libload "list.scm")
;; (set! COMMENT-FLAG #t)

(if (not (assoc "nat" ALGEBRAS))
    (myerror "First execute (libload \"nat.scm\")"))

(if (not (assoc "list" ALGEBRAS))
    (myerror "First execute (libload \"list.scm\")"))

(display "loading str.scm ...") (newline)

(add-algs "str" 'prefix-typeop
	  '("alpha=>str=>str" "SCons"))

;; Infix notation allowed (and type parameters omitted) for binary
;; constructors, as follows.  This would also work for prefix notation.
;; Example: :~: for SCons.  x^1:~:x^2:~:x^3:~:xstr^

(add-infix-display-string "SCons" ":~:" 'pair-op) ;right associative

(add-var-name "x" (py "alpha"))
(add-var-name "xs" (py "list alpha"))
(add-var-name "xstr" (py "str alpha"))
(add-var-name "xxstr" (py "alpha yprod str alpha"))

(add-totality "str")
(add-rtotality "str")
(add-totalnc "str")
(add-rtotalnc "str")
(add-co "TotalStr")
(add-co "TotalStrNc")

(add-eqp "str")
(add-eqpnc "str")
(add-co "EqPStr")
;; (pp "CoEqPStrClause")
(add-co "EqPStrNc")

;; An inverse to CoTotalStrClause
;; CoTotalStrSCons
(set-goal "allnc x^(Total x^ ->
 allnc xstr^(CoTotalStr xstr^ -> CoTotalStr(x^ :~:xstr^)))")
(assume "x^" "Tx")
;; We prove an auxiliary proposition, by coinduction.
(assert "allnc xstr^(
 exr xstr^1(CoTotalStr xstr^1 andi
            xstr^ eqd(x^ :~:xstr^1)) -> CoTotalStr xstr^)")
(assume "xstr^0" "ExHyp0")
(coind "ExHyp0")
(drop "ExHyp0")
(assume "xstr^" "ExHyp")
(by-assume "ExHyp" "xstr^1" "Conj")
(intro 0 (pt "x^"))
(split)
(use "Tx")
(intro 0 (pt "xstr^1"))
(split)
(intro 0)
(use "Conj")
(use "Conj")
;; Assertion proved
(assume "Assertion" "xstr^" "CoTxstr")
(use "Assertion")
(intro 0 (pt "xstr^"))
(split)
(use "CoTxstr")
(use "InitEqD")
;; Proof finished.
(save "CoTotalStrSCons")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [x,xstr](CoRec str alpha=>str alpha)xstr
;;  ([xstr0]x pair(InL (str alpha) (str alpha))xstr0)

(add-algs "inf" '("Gen" "inf=>inf"))

(add-ids (list (list "STotalStr" (make-arity (py "str alpha")) "inf"))
	 '("allnc x^,xstr^(
             STotalStr xstr^ -> STotalStr(x^ :~:xstr^))" "STotalStrSCons"))
(add-co "STotalStr")
;; (pp "CoSTotalStrClause")

;; allnc xstr^(CoSTotalStr xstr^ -> 
;;  exr x^,xstr^0(CoSTotalStr xstr^0 andl xstr^ eqd(x^ :~:xstr^0)))

;; An inverse to CoSTotalStrClause
;; CoSTotalStrSCons
(set-goal "allnc x^,xstr^(CoSTotalStr xstr^ -> CoSTotalStr(x^ :~:xstr^))")
(assume "x^")
;; We prove an auxiliary proposition, by coinduction.
(assert "allnc xstr^(
 exr xstr^1(CoSTotalStr xstr^1 andi
            xstr^ eqd(x^ :~:xstr^1)) -> CoSTotalStr xstr^)")
(assume "xstr^0" "ExHyp0")
(coind "ExHyp0")
(drop "ExHyp0")
(assume "xstr^" "ExHyp")
(by-assume "ExHyp" "xstr^1" "Conj")
(intro 0 (pt "x^"))
(intro 0 (pt "xstr^1"))
(split)
(intro 0)
(use "Conj")
(use "Conj")
;; Assertion proved
(assume "Assertion" "xstr^" "CoSTxstr")
(use "Assertion")
(intro 0 (pt "xstr^"))
(split)
(use "CoSTxstr")
(use "InitEqD")
;; Proof finished.
(save "CoSTotalStrSCons")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [inf](CoRec inf=>inf)inf(InL inf inf)

(add-program-constant "StrToList" (py "str alpha=>list alpha"))
(add-computation-rules
 "(StrToList alpha)((SCons alpha)x^ xstr^)" "x^ ::(StrToList alpha)xstr^")

(add-item-to-algebra-edge-to-embed-term-alist
 "str" "list"
 (let* ((type (apply make-alg "str" (alg-name-to-tvars "str")))
	(var (make-var type -1 t-deg-one (default-var-name type))))
   (make-term-in-abst-form
    var (make-term-in-app-form
         (make-term-in-const-form
          (pconst-name-to-pconst "StrToList"))
         (make-term-in-var-form var)))))

;; (map car ALGEBRA-EDGE-TO-EMBED-TERM-ALIST)

;; (type-le? (apply make-alg "str" (list (py "int")))
;; 	  (apply make-alg "list" (list (py "rat"))))
;; #t

;; StrCoTotalToCoSTotal
(set-goal "allnc xstr^(CoTotalStr xstr^ -> CoSTotalStr xstr^)")
(assume "xstr^" "CoTxstr")
(coind "CoTxstr")
(assume "xstr^1" "CoTxstr1")
(inst-with-to "CoTotalStrClause"
	      (pt "xstr^1") "CoTxstr1" "CoTotalStrClauseInst")
(by-assume "CoTotalStrClauseInst" "x^1" "x1Prop")
(elim "x1Prop")
(drop "x1Prop")
(assume "Tx1" "ExHyp")
(by-assume "ExHyp" "xstr^2" "Conj")
(intro 0 (pt "x^1"))
(intro 0 (pt "xstr^2"))
(split)
(intro 1)
(use "Conj")
(use "Conj")
;; Proof finished.
(save "StrCoTotalToCoSTotal")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [xstr](CoRec str alpha=>inf)xstr
;;  ([xstr0][case (DesYprod xstr0) (x pair xstr -> InR xstr)])

;; Now for StrAppd

(add-program-constant "StrAppd" (py "list alpha=>str alpha=>str alpha"))

(remove-token "++")
(add-token "++" 'mul-op (make-param-term-creator2 "++"))
(add-token-and-types-to-name "++" (list (py "list alpha") (py "list alpha"))
			     "ListAppd")
(add-token-and-types-to-name "++" (list (py "list alpha") (py "str alpha"))
			     "StrAppd")
(add-display (py "str alpha")
             (make-display-creator "StrAppd" "++" 'mul-op))

;; (pp (pt "xs^1++xs^2"))
;; xs^1++xs^2
;; (pp (pt "xs^1++xstr^2"))
;; xs^1++xstr^2
;; (pp (pt "(list pos)^ ++(str pos)^"))
;; ;; (list pos)^ ++(str pos)^
;; (pp (pt "(1::2::3:)++(4::5:)"))
;; ;; (1::2::3:)++(4::5:)
;; (pp (pt "(1::2::3:)++(str pos)^"))
;; ;; (1::2::3:)++(str pos)^
;; (pp (rename-variables (pt "(list pos)^ ++(str int)^")))

;; ;; (Rec list pos=>list int)(list pos)^(Nil int)([p,(list pos)](Cons int)p)++
;; ;; (str int)^

(add-computation-rules
 "(Nil alpha)++xstr" "xstr"
 "(x::xs)++xstr" "x:~:xs++xstr")

;; (pp (nt (pt "(1::2::3:)++(str pos)^")))
;; 1:~:2:~:3:~:(str pos)^

;; CoTotalStrAppd
(set-goal "allnc xs^(TotalList xs^ ->
 allnc xstr^(CoTotalStr xstr^ -> CoTotalStr(xs^ ++xstr^)))")
(assume "xs^" "Txs")
(elim "Txs")
(ng)
(auto)
(assume "x^" "Tx" "xs^1" "Txs1" "IH" "xstr^" "CoTxstr")
(ng #t)
(use "CoTotalStrSCons")
(use "Tx")
(use "IH")
(use "CoTxstr")
;; Proof finished.
(save "CoTotalStrAppd")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [xs](Rec list alpha=>str alpha=>str alpha)xs([xstr]xstr)
;;  ([x,xs0,(str alpha=>str alpha),xstr]
;;    (cCoTotalStrSCons alpha)x((str alpha=>str alpha)xstr))

;; CoSTotalStrAppd
(set-goal "allnc xs^(STotalList xs^ ->
 allnc xstr^(CoSTotalStr xstr^ -> CoSTotalStr(xs^ ++xstr^)))")
(assume "xs^" "STxs")
(elim "STxs")
(ng)
(auto)
(assume "x^" "xs^1" "STxs1" "IH" "xstr^" "CoSTxstr")
(ng #t)
(use "CoSTotalStrSCons")
(use "IH")
(use "CoSTxstr")
;; Proof finished.
(save "CoSTotalStrAppd")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [n](Rec nat=>inf=>inf)n([inf]inf)
;;  ([n0,(inf=>inf),inf]cCoSTotalStrSCons((inf=>inf)inf))

;; Now for projection StrProj.

(add-program-constant "StrProj" (py "nat=>str alpha=>alpha"))

(remove-token "thof")
(add-token "thof" 'pair-op (make-param-term-creator2 "thof"))
(add-token-and-types-to-name "thof" (list (py "nat") (py "list alpha"))
			     "ListProj")
(add-token-and-types-to-name "thof" (list (py "nat") (py "str alpha"))
			     "StrProj")
(add-display (py "alpha")
             (make-display-creator "StrProj" "thof" 'pair-op))

;; (pp (pt "n^ thof xs^"))
;; n^ thof xs^
;; (pp (pt "n^ thof xstr^"))
;; n^ thof xstr^
;; (pp (pt "n^ thof(str pos)^"))
;; ;; n^ thof(str pos)^
;; (pp (pt "Succ Zero thof (1::2::3::4:)"))
;; ;; Succ Zero thof 1::2::3::4:
;; (pp (pt "Succ Zero thof (1:~:2:~:3:~:(str pos)^)"))
;; ;; Succ Zero thof 1:~:2:~:3:~:(str pos)^

(add-computation-rules
 "Zero thof x:~:xstr" "x"
 "Succ nat thof x:~:xstr" "nat thof xstr")


;; (pp (nt (pt "Zero thof 3:~:2:~:1:~:(str pos)")))
;; 3
;; (pp (nt (pt "Succ Zero thof 3:~:2:~:1:~:(str pos)")))
;; 2
;; (pp (nt (pt "Succ(Succ Zero) thof 3:~:2:~:1:~:(str pos)")))
;; 1
;; (pp (nt (pt "Succ(Succ(Succ Zero)) thof 3:~:2:~:1:~:(str pos)")))
;; Zero thof(str pos)

;; Now for StrBar

(add-program-constant "StrBar" (py "str alpha=>nat=>list alpha"))

(remove-token "bar")
(add-token "bar" 'add-op (make-param-term-creator2 "bar"))
(add-token-and-types-to-name "bar" (list (py "list alpha") (py "nat"))
			     "ListBar")
(add-token-and-types-to-name "bar" (list (py "str alpha") (py "nat"))
			     "StrBar")
(add-display (py "list alpha")
             (make-display-creator "StrBar" "bar" 'add-op))

;; (pp (pt "xs^ bar n^"))
;; xs^ bar n^
;; (pp (pt "xstr^ bar n^"))
;; xstr^ bar n^
;; (pp (pt "(str pos)^ bar n^"))
;; ;; (str pos)^ bar n^
;; (pp (pt "(1::2::3::4:)bar Succ(Succ(Succ Zero))"))
;; ;; (1::2::3::4:)bar Succ(Succ(Succ Zero))
;; (pp (pt "(1:~:2:~:3:~:(str pos)^)bar Succ(Succ(Succ Zero))"))
;; ;; (1:~:2:~:3:~:(str pos)^)bar Succ(Succ(Succ Zero))

(add-computation-rules
 "xstr bar Zero" "(Nil alpha)"
 "(x:~:xstr)bar Succ n" "x::xstr bar n")

;; (pp (nt (pt "(1:~:2:~:3:~:(str pos)^)bar Succ(Succ Zero)")))
;; 1::2:

;; Now for StrMap

(add-program-constant "StrMap" (py "(alpha1=>alpha2)=>str alpha1=>str alpha2"))

(add-infix-display-string "StrMap" "smap" 'pair-op) ;right associative

(add-var-name "phi" (py "alpha1=>alpha2"))
(add-var-name "y" (py "alpha1"))
(add-var-name "ystr" (py "str alpha1"))

(add-computation-rules
 "phi smap y:~:ystr" "phi y:~:phi smap ystr")

;; (pp (pt "Succ smap Zero:~:Succ Zero:~:(str nat)^"))
;; Succ smap Zero:~:Succ Zero:~:(str nat)^

(add-var-name "z" (py "alpha2"))
(add-var-name "zstr" (py "str alpha2"))

;; StrMapCoTotal
(set-goal
 "all phi allnc ystr^(CoTotalStr ystr^ -> CoTotalStr(phi smap ystr^))")
(use "AllTotalIntro")
(assume "phi^" "Tphi")
;; We prove an auxiliary proposition, by coinduction.
(assert "allnc zstr^(
 exr ystr^1(CoTotalStr ystr^1 andi zstr^ eqd(phi^ smap ystr^1)) ->
 CoTotalStr zstr^)")
(assume "zstr^0" "ExHyp0")
(coind "ExHyp0")
(drop "ExHyp0")
(assume "zstr^" "ExHyp")
(by-assume "ExHyp" "ystr^" "Conj")
(assert "exr y^(Total y^ andi
 exr ystr^1(CoTotalStr ystr^1 andl ystr^ eqd(y^ :~: ystr^1)))")
(use "CoTotalStrClause")
(use "Conj")
(assume "yExHyp")
(by-assume "yExHyp" "y^" "yProp")
(elim "yProp")
(drop "yProp")
(assume "Ty" "ystrExHyp")
(by-assume "ystrExHyp" "ystr^1" "Conj1")
(simp "Conj")
(simp "Conj1")
(ng #t)
(intro 0 (pt "phi^ y^"))
(split)
(use "Tphi")
(use "Ty")
(intro 0 (pt "phi^ smap ystr^1"))
(split)
(intro 1)
(intro 0 (pt "ystr^1"))
(split)
(use "Conj1")
(use "InitEqD")
(use "InitEqD")
;; Assertion proved.
(assume "Assertion" "ystr^" "ystrCoT")
(use "Assertion")
(intro 0 (pt "ystr^"))
(split)
(use "ystrCoT")
(use "InitEqD")
;; Proof finished.
(save "StrMapCoTotal")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [phi,ystr](CoRec str alpha1=>str alpha2)ystr
;;  ([ystr0][case (DesYprod ystr0) (y pair ystr1 -> phi y pair InR ystr1)])

;; StrProjMap
(set-goal "all phi,n,ystr^(CoSTotalStr ystr^ ->
 n thof (phi smap ystr^)eqd phi(n thof ystr^))")
(assume "phi")
(ind)
;; 3,4
(assume "ystr^" "CoSTystr")
(inst-with-to "CoSTotalStrClause" (py "alpha1") (pt "ystr^") "CoSTystr" "Inst")
(by-assume "Inst" "y^" "yProp")
(by-assume "yProp" "ystr^1" "Conj")
(simp "Conj")
(ng)
(use "InitEqD")
;; 4
(assume "n" "IH" "ystr^" "CoSTystr")
(inst-with-to "CoSTotalStrClause" (py "alpha1") (pt "ystr^") "CoSTystr" "Inst")
(by-assume "Inst" "y^" "yProp")
(by-assume "yProp" "ystr^1" "Conj")
(simp "Conj")
(ng)
(use "IH")
(use "Conj")
;; Proof finished.
(save "StrProjMap")

;; Now for StrHead

(add-program-constant "StrHead" (py "str alpha=>alpha"))

(remove-token "Head")
(add-token "Head" 'prefix-op (make-param-term-creator1 "Head"))
(add-token-and-type-to-name "Head" (py "list alpha") "ListHead")
(add-token-and-type-to-name "Head" (py "str alpha") "StrHead")
(add-display (py "alpha") (make-display-creator1 "StrHead" "Head" 'prefix-op))

;; (pp (pt "Head xs^"))
;; Head xs^
;; (pp (pt "Head xstr^"))
;; Head xstr^

(add-computation-rules
 "Head(x:~:xstr)" "x")

;; (pp (nt (pt "Head(x^ ::xs^)")))
;; x^
;; (pp (nt (pt "Head(x^ :~:xstr^)")))
;; x^

;; CoTotalStrToTotalHead
(set-goal "allnc xstr^(CoTotalStr xstr^ -> Total(Head xstr^))")
(assume "xstr^" "CoTxstr")
(inst-with-to "CoTotalStrClause"
	      (pt "xstr^") "CoTxstr" "CoTotalStrClauseInst" )
(by-assume "CoTotalStrClauseInst" "x^1" "x1Prop")
(elim "x1Prop")
(drop "x1Prop")
(assume "Tx1" "ExHyp")
(by-assume "ExHyp" "xstr^1" "Conj")
(simp "Conj")
(ng)
(use "Tx1")
;; Proof finished.
(save "CoTotalStrToTotalHead")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [xstr][case (DesYprod xstr) (x pair xstr0 -> x)]

;; Now for StrTail

(add-program-constant "StrTail" (py "str alpha=>str alpha"))

(remove-token "Tail")
(add-token "Tail" 'prefix-op (make-param-term-creator1 "Tail"))
(add-token-and-type-to-name "Tail" (py "list alpha") "ListTail")
(add-token-and-type-to-name "Tail" (py "str alpha") "StrTail")
(add-display (py "str alpha")
	     (make-display-creator1 "StrTail" "Tail" 'prefix-op))

;; (pp (pt "Tail xs^"))
;; Tail xs^
;; (pp (pt "Tail xstr^"))
;; Tail xstr^

(add-computation-rules
 "Tail(x:~:xstr)" "xstr")

;; (pp (nt (pt "Tail(x^ ::xs^)")))
;; xs^
;; (pp (nt (pt "Tail(x^ :~:xstr^)")))
;; xstr^

;; CoTotalStrTail
(set-goal "allnc xstr^(CoTotalStr xstr^ -> CoTotalStr(Tail xstr^))")
(assume "xstr^" "CoTxstr")
(inst-with-to "CoTotalStrClause"
	      (pt "xstr^") "CoTxstr" "CoTotalStrClauseInst" )
(by-assume "CoTotalStrClauseInst" "x^1" "x1Prop")
(elim "x1Prop")
(drop "x1Prop")
(assume "Tx1" "ExHyp")
(by-assume "ExHyp" "xstr^1" "Conj")
(simp "Conj")
(ng)
(use "Conj")
;; Proof finished.
(save "CoTotalStrTail")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
(ppc neterm)

;; [xstr][case (DesYprod xstr) (x pair xstr0 -> xstr0)]

;; CoSTotalStrTail
(set-goal "allnc xstr^(CoSTotalStr xstr^ -> CoSTotalStr(Tail xstr^))")
(assume "xstr^" "CoSTxstr")
(inst-with-to "CoSTotalStrClause"
	      (pt "xstr^") "CoSTxstr" "CoSTotalStrClauseInst" )
(by-assume "CoSTotalStrClauseInst" "x^1" "x1Prop")
(by-assume "x1Prop" "xstr^1" "Conj")
(simp "Conj")
(ng)
(use "Conj")
;; Proof finished.
(save "CoSTotalStrTail")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; (Destr inf)

;; Now for StrInit

(add-program-constant "StrInit" (py "nat=>str alpha=>list alpha"))

(remove-token "init")
(add-token "init" 'mul-op (make-param-term-creator2 "init"))
(add-token-and-types-to-name "init" (list (py "nat") (py "list alpha"))
			     "ListInit")
(add-token-and-types-to-name "init" (list (py "nat") (py "str alpha"))
			     "StrInit")
(add-display (py "list alpha")
             (make-display-creator "StrInit" "init" 'mul-op))

;; (pp (pt "n^ init xs^"))
;; n^ init xs^
;; (pp (pt "n^ init xstr^"))
;; n^ init xstr^
;; (pp (pt "n^ init(str pos)^"))
;; ;; n^ init(str pos)^
;; (pp (pt "Succ(Succ(Succ Zero))init(1::2::3::4:)"))
;; ;; Succ(Succ(Succ Zero))init(1::2::3::4:)
;; (pp (pt "Succ(Succ(Succ Zero))init(1:~:2:~:3:~:(str pos)^)"))
;; ;; Succ(Succ(Succ Zero))init(1:~:2:~:3:~:(str pos)^)

(add-computation-rules
 "Zero init xstr" "(Nil alpha)"
 "Succ n init(x:~:xstr)" "x::n init xstr")

;; (pp (nt (pt "Succ(Succ Zero)init(1:~:2:~:3:~:(str pos)^)")))
;; 1::2:

;; n^ init xstr^ is exactly the same as xstr^ bar n^.  Hoewever, they
;; differ for lists: in case the number n is larger than the length,
;; ListInit returns the original list whereas ListBar appends Inhab's.

;; CoTotalStrToTotalInit
(set-goal "all n allnc xstr^(CoTotalStr xstr^ -> Total(n init xstr^))")
(ind)
(strip)
(use "TotalListNil")
(assume "n" "IH" "xstr^" "CoTxstr")
(inst-with-to "CoTotalStrClause"
	      (pt "xstr^") "CoTxstr" "CoTotalStrClauseInst" )
(by-assume "CoTotalStrClauseInst" "x^1" "x1Prop")
(elim "x1Prop")
(drop "x1Prop")
(assume "Tx1" "ExHyp")
(by-assume "ExHyp" "xstr^1" "Conj")
(simp "Conj")
(ng)
(use "TotalListCons")
(use "Tx1")
(use "IH")
(use "Conj")
;; Proof finished.
(save "CoTotalStrToTotalInit")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [n](Rec nat=>str alpha=>list alpha)n([xstr]Nil)
;;  ([n0,(str alpha=>list alpha),xstr]
;;    [case (DesYprod xstr)
;;     (x pair xstr0 -> x::(str alpha=>list alpha)xstr0)])

;; CoSTotalStrToSTotalInit
(set-goal "all n allnc xstr^(CoSTotalStr xstr^ -> STotalList(n init xstr^))")
(ind)
(strip)
(use "STotalListNil")
(assume "n" "IH" "xstr^" "CoSTxstr")
(inst-with-to "CoSTotalStrClause"
	      (pt "xstr^") "CoSTxstr" "CoSTotalStrClauseInst")
(by-assume "CoSTotalStrClauseInst" "x^1" "x1Prop")
(by-assume "x1Prop" "xstr^1" "Conj")
(simp "Conj")
(ng)
(use "STotalListCons")
(use "IH")
(use "Conj")
;; Proof finished.
(save "CoSTotalStrToSTotalInit")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [n](Rec nat=>inf=>nat)n([inf]0)([n0,(inf=>nat),inf]Succ((inf=>nat)Des inf))

;; StrLengthInit
(set-goal "all n,xstr^(CoSTotalStr xstr^ ->  Lh(n init xstr^)eqd n)")
(ind)
(assume "xstr^" "Useless")
(use "InitEqD")
(assume "n" "IH" "xstr^" "CoSTxstr")
(inst-with-to "CoSTotalStrClause"
	      (pt "xstr^") "CoSTxstr" "CoSTotalStrClauseInst")
(by-assume "CoSTotalStrClauseInst" "x^1" "x1Prop")
(by-assume "x1Prop" "xstr^1" "Conj")
(simp "Conj")
(ng)
(simp "IH")
(use "InitEqD")
(use "Conj")
;; Proof finished.
(save "StrLengthInit")

;; StrInitAppd
(set-goal
 "all xs^,xstr^(STotalList xs^ -> Lh xs^ init(xs^ ++xstr^)eqd xs^)")
(assume "xs^" "xstr^" "STxs")
(elim "STxs")
(ng)
(use "InitEqD")
(assume "x^" "xs^1" "STxs1")
(ng)
(assume "EqHyp")
(simp "EqHyp")
(use "InitEqD")
;; Proof finished.
(save "StrInitAppd")

;; StrInitPlusAppdPartial
(set-goal "all n,xs^(STotalList xs^ ->
 all xstr^ (n+Lh xs^)init(xs^ ++xstr^)eqd xs^ ++(n init xstr^))")
(assume "n" "xs^" "STxs")
(elim "STxs")
(ng)
(strip)
(use "InitEqD")
;; 3
(assume "x^" "xs^1" "STxs1" "IH" "xstr^")
(ng)
(simp "IH")
(use "InitEqD")
;; Proof finished.
(save "StrInitPlusAppdPartial")

;; StrInitPlusAppd
(set-goal "all n,xs,xstr^ (n+Lh xs)init(xs++xstr^)eqd xs++(n init xstr^)")
(assume "n" "xs" "xstr^")
(use "StrInitPlusAppdPartial")
(use "ListSTotalVar")
;; Proof finished.
(save "StrInitPlusAppd")

;; Now for StrRest

;; n srest xstr returns the rest of xstr after removing its initial
;; segment of length n

(add-program-constant "StrRest" (py "nat=>str alpha=>str alpha"))

(remove-token "rest")
(add-token "rest" 'mul-op (make-param-term-creator2 "rest"))
(add-token-and-types-to-name "rest" (list (py "nat") (py "list alpha"))
			     "ListRest")
(add-token-and-types-to-name "rest" (list (py "nat") (py "str alpha"))
			     "StrRest")
(add-display (py "str alpha")
             (make-display-creator "StrRest" "rest" 'mul-op))

;; (pp (pt "n^ rest xs^"))
;; n^ rest xs^
;; (pp (pt "n^ rest xstr^"))
;; n^ rest xstr^
;; (pp (pt "n^ rest(str pos)^"))
;; ;; n^ rest(str pos)^
;; (pp (pt "Succ Zero rest(4::5:)"))
;; ;; Succ Zero rest(4::5:)
;; (pp (pt "Succ Zero rest(str pos)^"))
;; ;; Succ Zero rest(str pos)^
;; (pp (pt "Succ Zero rest(4:~:5:~:(str pos)^)"))
;; ;; Succ Zero rest(4:~:5:~:(str pos)^)

(add-computation-rules
 "Zero rest xstr" "xstr"
 "Succ n rest(x:~: xstr)" "n rest xstr")

;; ;; (pp (nt (pt "Succ Zero rest(4:~:5:~:(str pos)^)")))
;; 5:~:(str pos)^
;; (pp (nt (pt "(0:~:1:~:2:~:(str nat)^)node 2")))
;; 1::0:
;; (pp (nt (pt "2 rest(0:~:1:~:2:~:(str nat)^)")))
;; 2:~:(str nat)^

;; CoTotalStrRest
(set-goal "all n allnc xstr^(CoTotalStr xstr^ -> CoTotalStr(n rest xstr^))")
(ind)
(assume "xstr^" "CoTxstr")
(use "CoTxstr")
(assume "n" "IH" "xstr^" "CoTxstr")
(inst-with-to "CoTotalStrClause"
	      (pt "xstr^") "CoTxstr" "CoTotalStrClauseInst" )
(by-assume "CoTotalStrClauseInst" "x^1" "x1Prop")
(elim "x1Prop")
(drop "x1Prop")
(assume "Tx1" "ExHyp")
(by-assume "ExHyp" "xstr^1" "Conj")
(simp "Conj")
(ng)
(use "IH")
(use "Conj")
;; Proof finished.
(save "CoTotalStrRest")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [n](Rec nat=>str alpha=>str alpha)n([xstr]xstr)
;;  ([n0,(str alpha=>str alpha),xstr]
;;    [case (DesYprod xstr) (x pair xstr -> (str alpha=>str alpha)xstr)])

;; StrTailRestComposed
(set-goal "all n,x^,xstr^(CoTotalStr xstr^ ->
 (Tail(n rest(x^ :~:xstr^))eqd n rest xstr^))")
(ind)
;; 2,3
(ng)
(strip)
(use "InitEqD")
;; 3
(assume "n" "IH" "x^" "xstr^" "CoTxstr")
(ng)
(inst-with-to "CoTotalStrClause" (pt "xstr^") "CoTxstr" "CoTotalStrClauseInst")
(by-assume "CoTotalStrClauseInst" "x^1" "x1Prop")
(elim "x1Prop")
(drop "x1Prop")
(assume "Tx1" "ExHyp")
(by-assume "ExHyp" "xstr^1" "Conj")
(simp "Conj")
(ng)
(use "IH")
(use "Conj")
;; Proof finished.
(save "StrTailRestComposed")

;; StrTailRest
(set-goal "all xstr^,n(CoTotalStr xstr^ ->
 (Tail(n rest xstr^))eqd(Succ n rest xstr^))")
(assume "xstr^" "n" "CoTxstr")
(inst-with-to "CoTotalStrClause" (pt "xstr^") "CoTxstr" "CoTotalStrClauseInst")
(by-assume "CoTotalStrClauseInst" "x^1" "x1Prop")
(elim "x1Prop")
(drop "x1Prop")
(assume "Tx1" "ExHyp")
(by-assume "ExHyp" "xstr^1" "Conj")
(simp "Conj")
(ng)
(use "StrTailRestComposed")
(use "Conj")
;; Proof finished.
(save "StrTailRest")

;; StrAppdInitRest
(set-goal "all n,xstr^(CoSTotalStr xstr^ ->
 n init xstr^ ++(n rest xstr^)eqd xstr^)")
(ind)
(ng)
(strip)
(use "InitEqD")
(assume "n" "IH" "xstr^" "CoSTxstr")
(inst-with-to
 "CoSTotalStrClause" (pt "xstr^") "CoSTxstr" "CoSTotalStrClauseInst")
(by-assume "CoSTotalStrClauseInst" "x^" "xProp")
(by-assume "xProp" "xstr^1" "Conj")
(simp "Conj")
(ng)
(simp "IH")
(use "InitEqD")
(use "Conj")
;; Proof finished.
(save "StrAppdInitRest")

;; StrAppdInitRestGen
(set-goal "all xs,n,xstr^((Lh xs+n)init(xs++xstr^)eqd xs ++(n init xstr^))")
(ind)
(ng)
(strip)
(use "InitEqD")
;; 3
(assume "x" "xs" "IH" "n" "xstr^")
(ng)
(simp "IH")
(use "InitEqD")
;; Proof finished.
(save "StrAppdInitRestGen")

;; Now for StrNode, which returns the reverse of StrInit.  We give a
;; direct definition by structural computation rules.  Later we will
;; show that the result can be obtained more efficiently with
;; StrNodeRest.

(add-program-constant "StrNode" (py "nat=>str alpha=>list alpha"))
(add-infix-display-string "StrNode" "node" 'mul-op)

(add-computation-rules
 "Zero node xstr" "(Nil alpha)"
 "Succ n node(x:~:xstr)" "n node xstr++x:")

;; CoTotalStrToTotalNode
(set-goal "all n allnc xstr^(CoTotalStr xstr^ -> Total(n node xstr^))")
(ind)
(strip)
(use "TotalListNil")
(assume "n" "IH" "xstr^" "CoTxstr")
(inst-with-to "CoTotalStrClause"
	      (pt "xstr^") "CoTxstr" "CoTotalStrClauseInst" )
(by-assume "CoTotalStrClauseInst" "x^1" "x1Prop")
(elim "x1Prop")
(drop "x1Prop")
(assume "Tx1" "ExHyp")
(by-assume "ExHyp" "xstr^1" "Conj")
(simp "Conj")
(ng)
(use "ListAppdTotal")
(use "IH")
(use "Conj")
(use "TotalListCons")
(use "Tx1")
(use "TotalListNil")
;; Proof finished.
(save "CoTotalStrToTotalNode")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [n](Rec nat=>str alpha=>list alpha)n([xstr]Nil)
;;  ([n0,(str alpha=>list alpha),xstr]
;;    [case (DesYprod xstr)
;;      (x pair xstr0 -> (str alpha=>list alpha)xstr0++x:)])

;; CoSTotalStrToSTotalNode
(set-goal "all n allnc xstr^(CoSTotalStr xstr^ -> STotalList(n node xstr^))")
(ind)
(strip)
(use "STotalListNil")
(assume "n" "IH" "xstr^" "CoSTxstr")
(inst-with-to "CoSTotalStrClause"
	      (pt "xstr^") "CoSTxstr" "CoSTotalStrClauseInst")
(by-assume "CoSTotalStrClauseInst" "x^1" "x1Prop")
(by-assume "x1Prop" "xstr^1" "Conj")
(simp "Conj")
(ng)
(use "ListAppdSTotal")
(use "IH")
(use "Conj")
(use "STotalListCons")
(use "STotalListNil")
;; Proof finished.
(save "CoSTotalStrToSTotalNode")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (pp neterm)

;; [n](Rec nat=>inf=>nat)n([inf]0)
;;  ([n0,(inf=>nat),inf](Rec nat=>nat)((inf=>nat)Des inf)1([n1]Succ))

;; StrRevInitEqNodePartial
(set-goal
 "all n^(TotalNat n^ -> all xstr^(CoSTotalStr xstr^ ->
  Rev(n^ init xstr^)eqd n^ node xstr^))")
(assume "n^" "Tn")
(elim "Tn")
(ng)
(strip)
(use "InitEqD")
(assume "n^1" "Tn1" "IH" "xstr^" "CoSTxstr")
(inst-with-to "CoSTotalStrClause"
	      (pt "xstr^") "CoSTxstr" "CoSTotalStrClauseInst")
(by-assume "CoSTotalStrClauseInst" "x^1" "x1Prop")
(by-assume "x1Prop" "xstr^1" "Conj")
(simp "Conj")
(ng)
(simp "IH")
(use "InitEqD")
(use "Conj")
;; Proof finished.
(save "StrRevInitEqNodePartial")

;; StrRevInitEqNode
(set-goal
 "all n,xstr^(CoSTotalStr xstr^ ->  Rev(n init xstr^)eqd n node xstr^)")
(use "AllTotalIntro")
(assume "n^")
(use "StrRevInitEqNodePartial")
;; Proof finished.
(save "StrRevInitEqNode")

;; StrLengthNode
(set-goal "all n,xstr^(CoSTotalStr xstr^ ->  Lh(n node xstr^)eqd n)")
(assume "n" "xstr^" "CoSTxstr")
(simp "<-" "StrRevInitEqNode")
(simp "ListLhRevPartial")
(use "StrLengthInit")
(use "CoSTxstr")
(use "CoSTotalStrToSTotalInit")
(use "CoSTxstr")
(use "CoSTxstr")
;; Proof finished.
(save "StrLengthNode")

;; StrNodeMap
(set-goal "all phi,n,ystr^(CoSTotalStr ystr^ ->
 (n node(phi smap ystr^))eqd(phi map(n node ystr^)))")
(assume "phi")
(ind)
(assume "ystr^" "CoSTystr")
(ng)
(use "InitEqD")
(assume "n" "IH" "ystr^" "CoSTystr")
(inst-with-to "CoSTotalStrClause" (py "alpha1") (pt "ystr^") "CoSTystr" "Inst")
(by-assume "Inst" "y^" "yProp")
(by-assume "yProp" "ystr^1" "Conj")
(simp "Conj")
(ng)
(simp "ListMapAppdPartial")
(ng)
(simp "IH")
(use "InitEqD")
(use "Conj")
(use "CoSTotalStrToSTotalNode")
(use "Conj")
;; Proof finished.
(save "StrNodeMap")

;; StrNodeAppd
(set-goal
 "all xs^,xstr^(STotalList xs^ -> Lh xs^ node(xs^ ++xstr^)eqd Rev xs^)")
(assume "xs^" "xstr^" "STxs")
(elim "STxs")
(ng)
(use "InitEqD")
(assume "x^" "xs^1" "STxs1")
(ng)
(assume "EqHyp")
(simp "EqHyp")
(use "InitEqD")
;; Proof finished.
(save "StrNodeAppd")

;; StrNodePlusAppdPartial
(set-goal "all n,xs^(STotalList xs^ -> all xstr^(CoSTotalStr xstr^ -> 
 (n+Lh xs^)node(Rev xs^ ++xstr^)eqd n node xstr^ ++xs^))")
(assume "n" "xs^" "STxs" "xstr^" "CoSTxstr")
;; Revert both sides of StrInitPlusAppdPartial at Rev xs
(assert
 "Rev((n+Lh Rev xs^)init(Rev xs^ ++xstr^))eqd Rev(Rev xs^ ++(n init xstr^))")
 (simp "StrInitPlusAppdPartial")
 (use "InitEqD")
 (use "ListRevSTotal")
 (use "STxs")
;; Assertion proved.  We simplify the implication
(simp "StrRevInitEqNodePartial")
(simp "ListLhRevPartial")
(simp "ListRevAppdPartial")
(simp "StrRevInitEqNodePartial")
(simp "ListRevInvolPartial")
;; Done: now the hypothesis equals the conclusion
(assume "Hyp")
(use "Hyp")
;; We now need to prove all assumptions on (structural) totality
(use "STxs")
(use "CoSTxstr")
(use "NatTotalVar")
(use "CoSTotalStrToSTotalInit")
(use "CoSTxstr")
(use "ListRevSTotal")
(use "STxs")
(use "STxs")
(use "CoSTotalStrAppd")
(use "ListRevSTotal")
(use "STxs")
(use "CoSTxstr")
(use "NatPlusTotal")
(use "NatTotalVar")
(use "ListLengthSTotal")
(use "ListRevSTotal")
(use "STxs")
;; Proof finished.
(save "StrNodePlusAppdPartial")

;; StrNodePlusAppd
(set-goal "all n,xs,xstr^(CoSTotalStr xstr^ -> 
 (n+Lh xs)node(Rev xs ++xstr^)eqd n node xstr^ ++xs)")
(assume "n" "xs" "xstr^")
(use "StrNodePlusAppdPartial")
(use "ListSTotalVar")
;; Proof finished.
(save "StrNodePlusAppd")

;; StrRestAppd
(set-goal
 "all xs^,xstr^(STotalList xs^ -> Lh xs^ rest(xs^ ++xstr^)eqd xstr^)")
(assume "xs^" "xstr^" "STxs")
(elim "STxs")
(ng)
(use "InitEqD")
(assume "x^" "xs^1" "STxs1")
(ng)
(assume "EqHyp")
(simp "EqHyp")
(use "InitEqD")
;; Proof finished.
(save "StrRestAppd")

;; StrAppdAssoc
(set-goal "all xs^1,xs^2,xstr^(STotalList xs^1 ->
 xs^1++(xs^2++xstr^)eqd xs^1++xs^2++xstr^)")
(assume "xs^1" "xs^2" "xstr^" "STxs1")
(elim "STxs1")
(ng)
(use "InitEqD")
(assume "x^" "xs^" "STxs" "EqHyp")
(ng)
(simp "EqHyp")
(use "InitEqD")
;; Proof finished.
(save "StrAppdAssoc")

;; StrNodeSum
(set-goal "all xs^1,xs^2,xstr^(
     STotalList xs^1 -> 
     STotalList xs^2 -> 
     Lh(xs^1++xs^2)node(xs^1++xs^2++xstr^)eqd 
     Lh xs^2 node(Lh xs^1 rest(xs^1++xs^2++xstr^))++
     (Lh xs^1 node(xs^1++xs^2++xstr^)))")
(assume "xs^1" "xs^2" "xstr^" "STxs1" "STxs2")
(simp "StrNodeAppd")
(simp "<-" "StrAppdAssoc")
(simp "StrNodeAppd")
(simp "StrRestAppd")
(simp "StrNodeAppd")
(use "ListRevAppdPartial")
(use "STxs1")
(use "STxs2")
(use "STxs2")
(use "STxs1")
(use "STxs1")
(use "STxs1")
(use "ListAppdSTotal")
(use "STxs1")
(use "STxs2")
;; Proof finished.
(save "StrNodeSum")

;; For efficiency reasons we also define StrNodeRest.

(add-program-constant
 "StrNodeRest" (py "nat=>str alpha=>list alpha yprod str alpha"))
(add-infix-display-string "StrNodeRest" "snr" 'mul-op)

(add-computation-rules
 "Zero snr xstr" "(Nil alpha)pair xstr"
 "Succ n snr xstr"
 "[if (n snr xstr) ([xs,xstr1](Head xstr1::xs)pair Tail xstr1)]")

;; StrRestSucc
(set-goal
 "all n,xstr^(CoSTotalStr xstr^ -> Succ n rest xstr^ eqd Tail(n rest xstr^))")
(ind)
(assume "xstr^" "CoSTxstr")
(inst-with-to "CoSTotalStrClause" (pt "xstr^") "CoSTxstr"
	      "CoSTotalStrClauseInst")
(by-assume "CoSTotalStrClauseInst" "x^" "xProp")
(by-assume "xProp" "xstr^1" "xxstr1Prop")
(simp "xxstr1Prop")
(ng)
(use "InitEqD")
;; 3
(assume "n" "IH" "xstr^" "CoSTxstr")
(inst-with-to "CoSTotalStrClause" (pt "xstr^") "CoSTxstr"
	      "CoSTotalStrClauseInst")
(by-assume "CoSTotalStrClauseInst" "x^" "xProp")
(by-assume "xProp" "xstr^1" "xxstr1Prop")
(simp "xxstr1Prop")
(ng)
(use "IH")
(use "xxstr1Prop")
;; Proof finished.
(save "StrRestSucc")

(pp "StrNodeSum")
;; We will also need an instance of StrNodeSum for the second list of
;; length one and CoSTotalStr xstr^

;; StrNodeSucc
(set-goal "all n,xstr^(CoSTotalStr xstr^ -> 
     Succ n node xstr^ eqd(Head(n rest xstr^)::n node xstr^))")
(ind)
(assume "xstr^" "CoSTxstr")
(inst-with-to "CoSTotalStrClause" (pt "xstr^") "CoSTxstr"
	      "CoSTotalStrClauseInst")
(by-assume "CoSTotalStrClauseInst" "x^" "xProp")
(by-assume "xProp" "xstr^1" "xxstr1Prop")
(simp "xxstr1Prop")
(ng)
(use "InitEqD")
(assume "n" "IH" "xstr^" "CoSTxstr")
(inst-with-to "CoSTotalStrClause" (pt "xstr^") "CoSTxstr"
	      "CoSTotalStrClauseInst")
(by-assume "CoSTotalStrClauseInst" "x^" "xProp")
(by-assume "xProp" "xstr^1" "xxstr1Prop")
(simp "xxstr1Prop")
(ng)
(simp "IH")
(ng)
(use "InitEqD")
(use "xxstr1Prop")
;; Proof finished.
(save "StrNodeSucc")

;; StrNodeRestEq
(set-goal "all n,xstr^(CoSTotalStr xstr^ ->
 n snr xstr^ eqd(n node xstr^ pair n rest xstr^))")
(ind)
(assume "xstr^" "CoSTxstr")
(ng)
(use "InitEqD")
(assume "n" "IH" "xstr^" "CoSTxstr")
(ng)
(simp "IH")
(ng)
(simp "StrNodeSucc")
(simp "StrRestSucc")
(use "InitEqD")
(use "CoSTxstr")
(use "CoSTxstr")
(use "CoSTxstr")
;; Proof finished.
(save "StrNodeRestEq")

;; StrHeadRest
(set-goal
 "all n,xstr^(CoSTotalStr xstr^ -> Head(n rest xstr^)eqd(n thof xstr^))")
(ind)
(assume "xstr^" "CoSTxstr")
(inst-with-to "CoSTotalStrClause" (pt "xstr^") "CoSTxstr"
	      "CoSTotalStrClauseInst")
(by-assume "CoSTotalStrClauseInst" "x^" "xProp")
(by-assume "xProp" "xstr^1" "Conj")
(simp "Conj")
(ng)
(use "InitEqD")
(assume "n" "IH" "xstr^" "CoSTxstr")
(inst-with-to "CoSTotalStrClause" (pt "xstr^") "CoSTxstr"
	      "CoSTotalStrClauseInst")
(by-assume "CoSTotalStrClauseInst" "x^" "xProp")
(by-assume "xProp" "xstr^1" "Conj")
(simp "Conj")
(ng)
(use "IH")
(use  "Conj")
;; Proof finished.
(save "StrHeadRest")

;; StrHeadNodeSucc
(set-goal
 "all n,xstr^(CoSTotalStr xstr^ -> Head(Succ n node xstr^)eqd(n thof xstr^))")
(assume "n" "xstr^" "CoSTxstr")
(simp "StrNodeSucc")
(ng)
(use "StrHeadRest")
(use "CoSTxstr")
(use "CoSTxstr")
;; Proof finished.
(save "StrHeadNodeSucc")

;; We now address the question how to generate streams.  Before
;; dealing with the general corecursion operator we introduce
;; iteration paths.

(add-var-name "f" (py "alpha=>alpha"))

;; (remove-program-constant "Iterate")
;; (remove-token "***")
(add-program-constant "Iterate" (py "(alpha=>alpha)=>nat=>alpha=>alpha"))
(add-infix-display-string "Iterate" "***" 'pair-op)

(add-computation-rules
 "(f***0)x" "x"
 "(f***(Succ n))x" "(f***n)(f x)")

(set-totality-goal "Iterate")
(assert "allnc n^,n^0(
     EqPNat n^ n^0 -> 
     allnc f^,f^0(
      allnc x^,x^0(EqP x^ x^0 -> EqP(f^ x^)(f^0 x^0)) -> 
      allnc x^,x^0(EqP x^ x^0 -> EqP((f^ ***n^)x^)((f^0***n^0)x^0))))")
(assume "n^1" "n^2" "EqPn1n2")
(elim "EqPn1n2")
;; 5,6
(assume "f^1" "f^2" "EqPf1f2" "x^1" "x^2" "EqPx1x2")
(ng #t)
(use "EqPx1x2")
;; 6
(assume "n^3" "n^4" "EqPn3n4" "IH" "f^1" "f^2" "EqPf1f2" "x^1" "x^2" "EqPx1x2")
(ng #t)
(use "IH")
(use "EqPf1f2")
(use "EqPf1f2")
(use "EqPx1x2")
;; 2
(assume "Assertion"
	"f^1" "f^2" "EqPf1f2" "n^1" "n^2" "EqPn1n2" "x^1" "x^2" "EqPx1x2")
(use "Assertion")
(use "EqPn1n2")
(use "EqPf1f2")
(use "EqPx1x2")
;; Proof finished.
(save-totality)

;; IterateExt
(set-totality-goal "Iterate")
(assert "allnc n^,n^0(
     EqPNat n^ n^0 -> 
     allnc f^,f^0(
      allnc x^,x^0(EqP x^ x^0 -> EqP(f^ x^)(f^0 x^0)) -> 
      allnc x^,x^0(EqP x^ x^0 -> EqP((f^ ***n^)x^)((f^0***n^0)x^0))))")
(assume "n^1" "n^2" "EqPn1n2")
(elim "EqPn1n2")
;; 5,6
(assume "f^1" "f^2" "EqPf1f2" "x^1" "x^2" "EqPx1x2")
(ng #t)
(use "EqPx1x2")
;; 6
(assume "n^3" "n^4" "EqPn3n4" "IH" "f^1" "f^2" "EqPf1f2" "x^1" "x^2" "EqPx1x2")
(ng #t)
(use "IH")
(use "EqPf1f2")
(use "EqPf1f2")
(use "EqPx1x2")
;; 2
(assume "Assertion"
	"f^1" "f^2" "EqPf1f2" "n^1" "n^2" "EqPn1n2" "x^1" "x^2" "EqPx1x2")
(use "Assertion")
(use "EqPn1n2")
(use "EqPf1f2")
(use "EqPx1x2")
;; Proof finished.
(save "IterateExt")

;; IterateInOut
(set-goal "all f^,n,x^ (f^ ***n)(f^ x^)eqd f^((f^ ***n)x^)")
(assume "f^")
(ind)
(assume "x^")
(use "InitEqD")
(assume "n" "IH" "x^")
(ng)
(use "IH")
;; Proof finished.
(save "IterateInOut")

;; (remove-program-constant "StrPath")
;; (remove-token "path")
(add-program-constant "StrPath" (py "(alpha=>alpha)=>alpha=>str alpha"))
(add-infix-display-string "StrPath" "path" 'pair-op)

;; As for corecursion we do not add (f path x) -> (x:~:f path f x) as
;; a computation rule since it does not terminate.  However, we take
;; this equation as an axiom (temporarily as a global assumption).

(add-global-assumption
 "StrPathAxiom"
 (pf "all f^,x^ (f^ path x^) eqd (x^ :~:f^ path f^ x^)"))

;; Assume that f is sufficiently defined on P.  Then -- again on P --
;; f^ path x^ is structurally total.

;; CoSTotalStrPath
(set-goal "allnc f^(allnc x^((Pvar alpha)x^ -> (Pvar alpha)(f^ x^)) -> 
                    allnc x^((Pvar alpha)x^ -> CoSTotalStr(f^ path x^)))")
(assume "f^" "fHyp")
;; We prove an auxiliary proposition, by coinduction.
(assert "allnc xstr^(exr x^((Pvar alpha)x^ andl xstr^ eqd f^ path x^) ->
 CoSTotalStr xstr^)")
(assume "xstr^" "ExHyp0")
(coind "ExHyp0")
(drop "ExHyp0")
(assume "xstr^1" "ExHyp")
(by-assume "ExHyp" "x^1" "x1Prop")
(intro 0 (pt "x^1"))
(intro 0 (pt "f^ path f^ x^1"))
(split)
(intro 1)
(intro 0 (pt "f^ x^1"))
(split)
(use "fHyp")
(use "x1Prop")
(use "InitEqD")
(simp "x1Prop")
(use "StrPathAxiom")
;; Assertion proved.
(assume "Assertion" "x^" "Px")
(use "Assertion")
(intro 0 (pt "x^"))
(split)
(use "Px")
(use "InitEqD")
;; Proof finished.
(save "CoSTotalStrPath")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [(gamma=>gamma),gamma]
;;  (CoRec gamma=>inf)gamma([gamma_0]InR((gamma=>gamma)gamma_0))

;; CoTotalStrPath
(set-goal "all f,x CoTotalStr(f path x)")
(assume "f")
;; We prove an auxiliary proposition, by coinduction.
(assert "allnc xstr^(exl x xstr^ eqd f path x -> CoTotalStr xstr^)")
(assume "xstr^" "ExHyp0")
(coind "ExHyp0")
(drop "ExHyp0")
(assume "xstr^1" "ExHyp")
(by-assume "ExHyp" "x1" "x1Prop")
(intro 0 (pt "x1"))
(split)
(use "TotalVar")
(intro 0 (pt "f path f x1"))
(split)
(intro 1)
(intro 0 (pt "f x1"))
(use "InitEqD")
(simp "x1Prop")
(use "StrPathAxiom")
;; Assertion proved.
(assume "Assertion" "x")
(use "Assertion")
(intro 0 (pt "x"))
(use "InitEqD")
;; Proof finished.
(save "CoTotalStrPath")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [f,x](CoRec alpha=>str alpha)x([x0]x0 pair InR(f x0))

;; CoSTConstFalse
(set-goal "CoSTotalStr(([boole]False)path False)")
(use "StrCoTotalToCoSTotal")
(use "CoTotalStrPath")
;; Proof finished.
(save "CoSTConstFalse")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)
;; cStrCoTotalToCoSTotal(cCoTotalStrPath([p]False)False)

;; CoSTConstTrue
(set-goal "CoSTotalStr(([boole]True)path True)")
(use "StrCoTotalToCoSTotal")
(use "CoTotalStrPath")
;; Proof finished.
(save "CoSTConstTrue")

;; StrProjPath
(set-goal "all f^,n,x^(n thof(f^ path x^)eqd(f^ ***n)x^)")
(assume "f^")
(ind)
(assume "x^")
(simp "StrPathAxiom")
(ng)
(use "InitEqD")
(assume "n" "IH" "x^")
(simp "StrPathAxiom")
(ng)
(use "IH")
;; Proof finished.
(save "StrProjPath")

;; StrHeadRestPath
(set-goal "all f^,x^,n(
 CoTotalStr(f^ path x^) -> Head(n rest(f^ path x^))eqd(f^ ***n)x^)")
(assume "f^" "x^" "n" "CoTHyp")
(simp "StrHeadRest")
(use "StrProjPath")
(use "StrCoTotalToCoSTotal")
(use "CoTHyp")
;; Proof finished.
(save "StrHeadRestPath")

;; StrMapPath
;; Postponed.

;; StrHeadPath
(set-goal "all f^,x^ Head(f^ path x^)eqd x^")
(assume "f^" "x^")
(simp "StrPathAxiom")
(use "InitEqD")
;; Proof finished.
(save "StrHeadPath")

;; StrTailPath
(set-goal "all f^,x^ Tail(f^ path x^)eqd(f^ path f^ x^)")
(assume "f^" "x^")
(simp (pf "(f^ path x^)eqd(x^ :~:f^ path f^ x^)"))
(use "InitEqD")
(use "StrPathAxiom")
;; Proof finished.
(save "StrTailPath")

;; StrLhNode
(set-goal "all n,xstr^(CoSTotalStr xstr^ -> Lh(n node xstr^)=n)")
(ind)
(strip)
(use "Truth")
(assume "n" "IH" "xstr^" "CoSTxstr")
(inst-with-to "CoSTotalStrClause" (pt "xstr^") "CoSTxstr"
	      "CoSTotalStrClauseInst")
(by-assume "CoSTotalStrClauseInst" "x^1" "x1Prop")
(by-assume "x1Prop" "xstr^1" "Conj")
(simp "Conj")
(ng)
(simp "ListLhAppdPartial")
(simp "IH")
(use "Truth")
(use "Conj")
(use "STotalListCons")
(use "STotalListNil")
(use "CoSTotalStrToSTotalNode")
(use "Conj")
;; Proof finished.
(save "StrLhNode")

;; ListHeadNodeSuccPath
(set-goal "all f,n,x Head(Succ n node(f path x))eqd(f ***n)x")
(assume "f")
(ind)
(assume "x")
(simp "StrPathAxiom")
(ng)
(use "InitEqD")
;; 4
(assume "n" "IH" "x")
(simp "StrPathAxiom")
(ng)
(assert "all xs^1,xs^2(
     STotalList xs^1 -> Lh xs^1=Succ n -> Head(xs^1++xs^2)eqd Head xs^1)")
(assume "xs^1" "xs^2" "STxs1")
(elim "STxs1")
(assume "Absurd")
(use "EfEqD")
(use "Absurd")
(assume "x^" "xs^" "STxs" "Useless1" "Useless2")
(ng)
(use "InitEqD")
;; Assertione proved
(assume "ListHeadAppd")
(simp "ListHeadAppd")
(drop "ListHeadAppd")
(use "IH")
(use "StrLhNode")
;; ?_25:CoSTotalStr(f path f x)
(use "StrCoTotalToCoSTotal")
(use "CoTotalStrPath")
(use "CoSTotalStrToSTotalNode")
(use "StrCoTotalToCoSTotal")
(use "CoTotalStrPath")
;; Proof finished.
(save "ListHeadNodeSuccPath")

;; SeqPath (prefix display SPath) converts a sequence xseq :
;; nat=>alpha into a path.  To this end we use NumSeqPath (prefix
;; display NSPath) converting xseq into a numerated path.  NumSeqPath
;; uses the step function SeqStep

(add-var-name "xseq" (py "nat=>alpha"))
(add-var-name "nx" (py "nat yprod alpha"))

;; SeqStep is the step function needed to iteratively build NumSPath
(add-program-constant
 "SeqStep" (py "(nat=>alpha)=>nat yprod alpha=>nat yprod alpha"))

(add-computation-rules
 "(SeqStep alpha)xseq nx" "Succ lft nx pair xseq(Succ lft nx)")

(set-totality-goal "SeqStep")
(assume "xseq^1" "xseq^2" "EqPxseq1xseq2" "nx^1" "nx^2" "EqPnx1nx2")
(ng #t)
(use "EqPYprodPairConstr")
(use "EqPNatSucc")
(use "EqPYprodPairOne")
(use "EqPnx1nx2")
;; 5
(use "EqPxseq1xseq2")
(use "EqPNatSucc")
(use "EqPYprodPairOne")
(use "EqPnx1nx2")
;; Proof finished.
(save-totality)

;; SeqStepExt
(set-totality-goal "SeqStep")
(assume "xseq^1" "xseq^2" "EqPxseq1xseq2" "nx^1" "nx^2" "EqPnx1nx2")
(ng #t)
(use "EqPYprodPairConstr")
(use "EqPNatSucc")
(use "EqPYprodPairOne")
(use "EqPnx1nx2")
;; 5
(use "EqPxseq1xseq2")
(use "EqPNatSucc")
(use "EqPYprodPairOne")
(use "EqPnx1nx2")
;; Proof finished.
(save "SeqStepExt")

;; IterateSeqStep
(set-goal "all xseq^,m^,n
 ((SeqStep alpha)xseq^ ***n)(m^ pair xseq^ m^)eqd(m^ +n pair xseq^(m^ +n))")
(assume "xseq^" "m^")
(ind)
;; 3,4
(ng)
(use "InitEqD")
;; 4
(assume "n" "IH")
(simp "Iterate1CompRule")
(simp "IterateInOut")
(simp "IH")
(simp "SeqStep0CompRule")
(ng)
(use "InitEqD")
;; Proof finished.
(save "IterateSeqStep")

;; StrProjPathSeqStep
(set-goal "all xseq^,m^,n 
     (n thof(SeqStep alpha)xseq^ path m^ pair xseq^ m^)eqd
     (m^ +n pair xseq^(m^ +n))")
(assume "xseq^" "m^" "n")
(simp "StrProjPath")
(use "IterateSeqStep")
;; Proof finished.
(save "StrProjPathSeqStep")

;; (pp (term-to-type (pt "(SeqStep alpha)xseq path n pair x")))
;; str(nat yprod alpha)

(add-program-constant "NumSeqPath" (py "(nat=>alpha)=>str(nat yprod alpha)"))
(add-prefix-display-string "NumSeqPath" "NSPath")

(add-computation-rules
 "NSPath xseq" "(SeqStep alpha)xseq path 0 pair xseq 0")

; CoTotalNumSeqPath
(set-goal "all xseq CoTotalStr(NSPath xseq)")
(assume "xseq")
(ng)
(use "CoTotalStrPath")
;; Proof finished.
(save "CoTotalNumSeqPath")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [xseq]cCoTotalStrPath([nx]Succ lft nx pair xseq(Succ lft nx))(0 pair xseq 0)

(animate "CoTotalStrPath")
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [xseq](CoRec nat yprod alpha=>str(nat yprod alpha))(0 pair xseq 0)
;;  ([nx]nx pair InR(Succ lft nx pair xseq(Succ lft nx)))

(deanimate "CoTotalStrPath")

(add-program-constant "SeqPath" (py "(nat=>alpha)=>str alpha"))
(add-prefix-display-string "SeqPath" "SPath")

(add-computation-rules
 "SPath xseq" "(PairTwo nat alpha)smap NSPath xseq")

;; CoTotalSeqPath
(set-goal "all xseq CoTotalStr(SPath xseq)")
(assume "xseq")
(simp "SeqPath0CompRule")
(use "StrMapCoTotal")
(use "CoTotalNumSeqPath")
;; Proof finished.
(save "CoTotalSeqPath")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [xseq]cStrMapCoTotal PairTwo(cCoTotalNumSeqPath xseq)

;; We show that StrProj inverts SeqPath

;; StrProjSeqPath
(set-goal "all xseq,n (n thof SPath xseq)eqd xseq n")
(assume "xseq" "n")
(simp "SeqPath0CompRule")
(simp "StrProjMap")
(simp "NumSeqPath0CompRule")
;; ?_6:rht(n thof(SeqStep alpha)xseq path 0 pair xseq 0)eqd xseq n
(simp "StrProjPathSeqStep")
(ng)
(use "InitEqD")
(use "StrCoTotalToCoSTotal")
(use "CoTotalNumSeqPath")
;; Proof finished.
(save "StrProjSeqPath")

(remove-var-name "f")

(remove-var-name "y")
(remove-var-name "ystr")
(add-var-name "y" (py "beta"))
(add-var-name "ystr" (py "str beta"))
(add-var-name "s" (py "str beta ysum alpha"))
(add-var-name "f" (py "alpha=>beta yprod(str beta ysum alpha)"))

(pp (aconst-to-formula
     (alg-or-arrow-types-to-corec-aconst (py "alpha=>str beta"))))

;; (CoRec alpha=>str beta)eqd
;; ([x,f]
;;   lft(f x):~:[if (rht(f x)) ([ystr]ystr) ([x0](CoRec alpha=>str beta)x0 f)])

;; StrCoRecInR
(set-goal
 "allnc f^,x^,y^,s^,x^1(
   f^ x^ eqd y^ pair s^ andi s^ eqd(InR alpha (str beta))x^1 -> 
   (CoRec alpha=>str beta)x^ f^ eqd(y^ :~:(CoRec alpha=>str beta)x^1 f^))")
(assume "f^" "x^" "y^" "s^" "x^1" "Conj")
(elim "Conj")
(drop "Conj")
(assume "fEq" "sEq")
(assert "all ystr^((y^ :~:(CoRec alpha=>str beta)x^1 f^)eqd ystr^ ->
 (CoRec alpha=>str beta)x^ f^ eqd ystr^)")
 (assume "ystr^" "EqHyp")
 (simp (make-proof-in-aconst-form
        (alg-or-arrow-types-to-corec-aconst (py "alpha=>str beta"))))
 (ng #t)
 (simp "fEq")
 (simp "sEq")
 (ng #t)
 (use "EqHyp")
(assume "Assertion")
(use "Assertion")
(use "InitEqD")
;; Proof finished.
(save "StrCoRecInR")

;; StrCoRecInL
(set-goal
 "allnc f^,x^,y^,s^,ystr^(
 f^ x^ eqd y^ pair s^ andnc s^ eqd(InL (str beta) alpha)ystr^ -> 
 (CoRec alpha=>str beta)x^ f^ eqd(y^ :~:ystr^))")
(assume "f^" "x^" "y^" "s^" "ystr^" "Conj")
(elim "Conj")
(drop "Conj")
(assume "fEq" "sEq")
(simp (make-proof-in-aconst-form
       (alg-or-arrow-types-to-corec-aconst (py "alpha=>str beta"))))
(ng #t)
(simp "fEq")
(simp "sEq")
(ng #t)
(use "InitEqD")
;; Proof finished.
(save "StrCoRecInL")

;; Assume that f is sufficiently defined on P.  Then -- again on P --
;; (CoRec alpha=>list beta)x^ f^ is structurally total.

;; CoSTotalStrCoRec
(set-goal "allnc f^(
 allnc x^(
  (Pvar alpha)x^ -> 
  exr y^,s^(
   f^ x^ eqd(y^ pair s^) andr 
   (exr ystr^(CoSTotalStr ystr^ andl s^ eqd(InL (str beta) alpha)ystr^) ord 
    exr x^1((Pvar alpha)x^1 andl s^ eqd(InR alpha (str beta))x^1)))) -> 
  allnc x^((Pvar alpha)x^ -> CoSTotalStr((CoRec alpha=>str beta)x^ f^)))")
(assume "f^" "fHyp")
;; We prove an auxiliary proposition, by coinduction.
(assert "allnc ystr^(
  exr x^((Pvar alpha)x^ andl ystr^ eqd(CoRec alpha=>str beta)x^ f^) -> 
  CoSTotalStr ystr^)")
(assume "ystr^0" "ExHyp0")
(coind "ExHyp0")
(drop "ExHyp0")
(assume "ystr^" "ExHyp")
(by-assume "ExHyp" "x^" "xConj")
(elim "xConj")
(drop "xConj")
(assume "Px" "ystrDef")
(inst-with-to "fHyp" (pt "x^") "Px" "fHypInst")
(drop "fHyp")
(elim "fHypInst")
;; 18
(drop "fHypInst")
(assume "y^" "ExHypInL")
(by-assume "ExHypInL" "s^" "sConj")
(elim "sConj")
(drop "sConj")
(assume "fxEq" "Disj")
(elim "Disj")
;; 27,28
(drop "Disj")
(assume "ExHypL")
(by-assume "ExHypL" "ystr^1" "ystr1Conj")
(elim "ystr1Conj")
(drop "ystr1Conj")
(assume "CoSTystr1" "sEq")
(simp "ystrDef")
(intro 0 (pt "y^"))
(intro 0 (pt "ystr^1"))
(split)
(intro 0)
(use "CoSTystr1")
(use "StrCoRecInL" (pt "s^"))
(simp "fxEq")
(simp "sEq")
(split)
(use "InitEqD")
(use "InitEqD")
;; 28
(drop "Disj")
(assume "ExHypR")
(by-assume "ExHypR" "x^1" "x1Conj")
(elim "x1Conj")
(drop "x1Conj")
(assume "Px1" "sEq")
(simp "ystrDef")
(intro 0 (pt "y^"))
(intro 0 (pt "(CoRec alpha=>str beta)x^1 f^"))
(split)
(intro 1)
(intro 0 (pt "x^1"))
(split)
(use "Px1")
(use "InitEqD")
(use "StrCoRecInR" (pt "s^"))
(simp "fxEq")
(simp "sEq")
(split)
(use "InitEqD")
(use "InitEqD")
;; Auxiliary proposition proved.
(assume "Aux" "x^" "Px")
(use "Aux")
(intro 0 (pt "x^"))
(split)
(use "Px")
(use "InitEqD")
;; Proof finished.
(save "CoSTotalStrCoRec")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [(gamma=>inf ysum gamma),gamma]
;;  (CoRec gamma=>inf)gamma(gamma=>inf ysum gamma)

;; CoTotalStrCoRec
(set-goal "allnc f^(
 allnc x^(
  (Pvar alpha)x^ -> 
  exr y^,s^(
   f^ x^ eqd(y^ pair s^) andi Total y^ andi
   (exr ystr^(CoTotalStr ystr^ andl s^ eqd(InL (str beta) alpha)ystr^) ord 
    exr x^1((Pvar alpha)x^1 andl s^ eqd(InR alpha (str beta))x^1)))) -> 
  allnc x^((Pvar alpha)x^ -> CoTotalStr((CoRec alpha=>str beta)x^ f^)))")
(assume "f^" "fHyp")
;; We prove an auxiliary proposition, by coinduction.
(assert "allnc ystr^(
  exr x^((Pvar alpha)x^ andl ystr^ eqd(CoRec alpha=>str beta)x^ f^) -> 
  CoTotalStr ystr^)")
(assume "ystr^0" "ExHyp0")
(coind "ExHyp0")
(drop "ExHyp0")
(assume "ystr^" "ExHyp")
(by-assume "ExHyp" "x^" "xConj")
(elim "xConj")
(drop "xConj")
(assume "Px" "ystrDef")
(inst-with-to "fHyp" (pt "x^") "Px" "fHypInst")
(drop "fHyp")
(elim "fHypInst")
;; 18
(drop "fHypInst")
(assume "y^" "ExHypInL")
(by-assume "ExHypInL" "s^" "sConj")
(elim "sConj")
(drop "sConj")
(assume "fxEq" "sConj2")
(elim "sConj2")
(drop "sConj2")
(assume "Ty" "Disj")
(elim "Disj")
;; 30,31
(drop "Disj")
(assume "ExHypL")
(by-assume "ExHypL" "ystr^1" "ystr1Conj")
(elim "ystr1Conj")
(drop "ystr1Conj")
(assume "CoTystr1" "sEq")
(simp "ystrDef")
(intro 0 (pt "y^"))
(split)
(use "Ty")
(intro 0 (pt "ystr^1"))
(split)
(intro 0)
(use "CoTystr1")
(use "StrCoRecInL" (pt "s^"))
(simp "fxEq")
(simp "sEq")
(split)
(use "InitEqD")
(use "InitEqD")
;; 31
(drop "Disj")
(assume "ExHypR")
(by-assume "ExHypR" "x^1" "x1Conj")
(elim "x1Conj")
(drop "x1Conj")
(assume "Px1" "sEq")
(simp "ystrDef")
(intro 0 (pt "y^"))
(split)
(use "Ty")
(intro 0 (pt "(CoRec alpha=>str beta)x^1 f^"))
(split)
(intro 1)
(intro 0 (pt "x^1"))
(split)
(use "Px1")
(use "InitEqD")
(use "StrCoRecInR" (pt "s^"))
(simp "fxEq")
(simp "sEq")
(split)
(use "InitEqD")
(use "InitEqD")
;; Auxiliary proposition proved.
(assume "Aux" "x^" "Px")
(use "Aux")
(intro 0 (pt "x^"))
(split)
(use "Px")
(use "InitEqD")
;; Proof finished.
(save "CoTotalStrCoRec")

(define eterm (proof-to-extracted-term))
(define neterm (rename-variables (nt eterm)))
;; (ppc neterm)

;; [(gamma=>beta yprod(str beta ysum gamma)),gamma]
;;  (CoRec gamma=>str beta)gamma
;;  ([gamma_0]
;;    [case ((gamma=>beta yprod(str beta ysum gamma))gamma_0)
;;      (y pair(str beta ysum gamma) -> 
;;      [case (str beta ysum gamma)
;;        (InL ystr -> y pair InL ystr)
;;        (InR gamma_1 -> y pair InR gamma_1)])])

(remove-var-name
 "f" "s" "ystr" "y" "nx" "xseq" "zstr" "z" "phi" "xxstr" "xstr" "xs" "x")
