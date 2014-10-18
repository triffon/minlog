;; 2014-10-13.  warshall.scm

;; (load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(libload "list.scm")
(set! COMMENT-FLAG #t)

(add-var-name "a" "b" "c" "d" "e" "i" "j" "k" (py "nat"))
(add-var-name "x" "y" "z" (py "list nat"))
(add-var-name "r" (py "nat=>nat=>boole"))

(add-program-constant
 "Path" (py "(nat=>nat=>boole)=>nat=>(list nat)=>nat=>nat=>boole"))
(add-computation-rules
 "Path r i(Nil nat)b c" "False"
 "Path r i(a:)b c" "[if (a=b) (b=c) False]"
 "Path r i(a::d:)b c" "[if (a=b) [if (d=c) (r a d) False] False]"
 "Path r i(a::d::e::x)b c" "[if (a=b) 
                                [if (r a d) 
                                    [if (d<i)
                                        (Path r i(d::e::x)d c)
                                        False]
                                    False]
                                False]")

;; PathTotal
(set-goal (rename-variables (term-to-totality-formula (pt "Path"))))
(assume "r^" "Tr")
(use "AllTotalElim")
(assume "i")
(use "AllTotalElim")
(ind)
(strip)
(ng)
(use "TotalBooleFalse")
(assume "a")
(cases)
(assume "Useless")
(use "AllTotalElim")
(assume "b")
(use "AllTotalElim")
(assume "c")
(ng #t)
(use "BooleIfTotal")
(use "BooleTotalVar")
(use "BooleTotalVar")
(use "TotalBooleFalse")
(assume "d")
(cases)
(assume "Useless")
(use "AllTotalElim")
(assume "b")
(use "AllTotalElim")
(assume "c")
(ng #t)
(use "BooleIfTotal")
(use "BooleTotalVar")
(use "BooleIfTotal")
(use "BooleTotalVar")
(use "Tr")
(use "NatTotalVar")
(use "NatTotalVar")
(use "TotalBooleFalse")
(use "TotalBooleFalse")
(assume "e" "x" "IH")
(use "AllTotalElim")
(assume "b")
(use "AllTotalElim")
(assume "c")
(ng #t)
(use "BooleIfTotal")
(use "BooleTotalVar")
(use "BooleIfTotal")
(use "Tr")
(use "NatTotalVar")
(use "NatTotalVar")
(use "BooleIfTotal")
(use "BooleTotalVar")
(use "IH")
(use "NatTotalVar")
(use "NatTotalVar")
(use "TotalBooleFalse")
(use "TotalBooleFalse")
(use "TotalBooleFalse")
;; Proof finished.
(save "PathTotal")

(add-program-constant "Rf" (py "(list nat)=>boole"))
(add-computation-rules
 "Rf(Nil nat)" "True"
 "Rf(a::x)" "[if (a in x) False (Rf x)]")

;; RfTotal
(set-goal (rename-variables (term-to-totality-formula (pt "Rf"))))
(use "AllTotalElim")
(ind)
(ng)
(use "TotalBooleTrue")
(assume "a" "x" "IH")
(ng)
(use "BooleIfTotal")
(use "BooleTotalVar")
(use "TotalBooleFalse")
(use "IH")
;; Proof finished.
(save "RfTotal")

(add-program-constant "Dot" (py "(list nat)=>(list nat)=>(list nat)"))
(add-infix-display-string "Dot" "|" 'add-op)

;; (add-token
;;  "|"
;;  'add-op
;;  (lambda (x y)
;;    (mk-term-in-app-form
;;     (make-term-in-const-form (pconst-name-to-pconst "Dot")) x y)))

;; (add-display
;;  (py "list nat")
;;  (lambda (x)
;;    (let* ((op (term-in-app-form-to-final-op x))
;; 	  (args (term-in-app-form-to-args x)))
;;      (if (and (term-in-const-form? op)
;; 	      (string=? "Dot"
;; 			(const-to-name (term-in-const-form-to-const op)))
;; 	      (= 2 (length args)))
;; 	 (list 'pair-op "|"
;; 	       (term-to-token-tree (car args))
;; 	       (term-to-token-tree (cadr args)))
;; 	 #f))))

(add-computation-rules
 "(Nil nat)|y" "y"
 "a: |(Nil nat)" "a:"
 "a: |(b::y)" "[if (a=b) (b::y) (Nil nat)]"
 "(a::d::x)|y" "a::d::x|y")

;; DotTotal
(set-goal (rename-variables (term-to-totality-formula (pt "Dot"))))
(assert "all n,x(Lh x<n -> all y TotalList(x|y))")
 (ind)
 (assume "x")
 (ng)
 (use "Efq")
 (assume "n" "IHn")
 (cases)
 (assume "Useless" "y")
 (ng)
 (use "ListTotalVar")
 (assume "a")
 (cases)
 (assume "Useless")
 (cases)
 (ng)
 (use "ListTotalVar")
 (assume "b" "y")
 (ng)
 (use "BooleIfTotal")
 (use "BooleTotalVar")
 (use "ListTotalVar")
 (use "TotalListNil")
 (assume "d" "x")
 (ng)
 (assume "LhBd" "y")
 (use "TotalListCons")
 (use "NatTotalVar")
 (use "TotalListCons")
 (use "NatTotalVar")
 (use "IHn")
 (use "NatLtTrans" (pt "Succ Lh x"))
 (use "Truth")
 (use "LhBd")
(assume "DotTotalAux")
(use "AllTotalElim")
(assume "x")
(use "AllTotalElim")
(assume "y")
(use "DotTotalAux" (pt "Succ Lh x"))
(use "Truth")
;; Proof finished.
(save "DotTotal")

;; Warshall
(set-goal "all r,i,j,k ex x(
                (x=(Nil nat) -> all y(Path r i y j k -> F)) &
                ((x=(Nil nat) -> F) -> Path r i x j k & Rf x))")

(assume "r")
(ind)

;; Base
(assume "j" "k")

(cases (pt "j=k"))

;; Case j=k
(assume "j=k")
(ex-intro (pt "j:"))
(split)
(assume 2 "y")
(prop)
(prop)

;; Case j\ne k
(cases (pt "r j k"))

;; Case r j k
(assume "rjk" "jnek")
(ex-intro (pt "j::k:"))
(split)
(search)

(ng)
(simp "jnek")
(ng)
(prop)

;; Case r j k -> F            
(assume "negrjk" "jnek")
(ex-intro (pt "(Nil nat)"))
(split)
(ng)

(add-global-assumption
 "Rf0path" "all r,x,j,k(Path r 0 x j k -> (j=k -> F) -> r j k)")

(assume 3 "y" 4)
(use "negrjk")
(use-with "Rf0path" (pt "r") (pt "y") (pt "j") (pt "k") 4 2)

(ng)
(prop)

;; Step
(assume "i" 1 "j" "k")
;; We want to use the induction hypothesis for j,k

(ex-elim (pf "ex x(
 (x=(Nil nat) -> all y(Path r i y j k -> F)) & 
 ((x=(Nil nat) -> F) -> Path r i x j k & Rf x))"))
;; use the IH
(use 1)

(assume "x1" 2)
(cases (pt "x1=(Nil nat)"))

;; Case x1=(Nil nat)
(assume 3)
;; We want to use the induction hypothesis for j,i
(ex-elim (pf "ex x.(x=(Nil nat) -> all y.Path r i y j i -> F) & ((x=(Nil nat) -> F) -> Path r i x j i & Rf x)"))
;; use the IH
(use 1)

(assume "x2" 4)
;; We also want to use the induction hypothesis for i,k
(ex-elim (pf "ex x(
 (x=(Nil nat) -> all y(Path r i y i k -> F)) & 
 ((x=(Nil nat) -> F) -> Path r i x i k & Rf x))"))
;; use the IH
(use 1)

(assume "x3" 5)

(cases (pt "x2=(Nil nat)"))
;; Subcase x2=(Nil nat)
(assume 6)
(ex-intro (pt "(Nil nat)"))
(split)
(assume 7 "y" 8)

(add-global-assumption "PathSplit1" (pf "all r,i1,x,i,j,k(
 Path r(i1+1)x j k -> 
 (Path r i1 x j k -> F) -> all y(Path r i1 y j i -> F) -> F)"))
(use-with "PathSplit1"  (pt "r") (pt "i") (pt "y") (pt "i") (pt "j") (pt "k")
	  8 DEFAULT-GOAL-NAME DEFAULT-GOAL-NAME)
(use-with 2 'left 3 (pt "y"))
(use-with 4 'left 6)

(prop)

;; Subcase x2 \ne (Nil nat)
(assume 6)
(cases (pt "x3=(Nil nat)"))

;; UUFall x3=(Nil nat)
(assume 7)
(ex-intro (pt "(Nil nat)"))
(split)
(assume 8)
(assume "y" 9)
(add-global-assumption "PathSplit2" (pf "all r,i1,x,i,j,k(
 Path r(i1+1)x j k -> 
 (Path r i1 x j k -> F) -> all z(Path r i1 z i k -> F) -> F)"))
(use-with "PathSplit2" (pt "r") (pt "i") (pt "y") (pt "i") (pt "j") (pt "k")
	  9 DEFAULT-GOAL-NAME DEFAULT-GOAL-NAME)
(use-with 2 'left 3 (pt "y"))
(use-with 5 'left 7)
(prop)

;; UUFall x3\ne (Nil nat)
(assume 7)
(ex-intro (pt "x2 | x3"))
(split)
(assume 8)

(add-global-assumption "Dotdef" "all r,i,j,k,x2,x3((x2=(Nil nat) -> F) ->
  (x3=(Nil nat) -> F) -> Path r i x2 j i -> Path r i x3 i k
  -> (x2 | x3)=(Nil nat) -> F)")
(assume "y" 9)
(use-with "Dotdef" (pt "r") (pt "i") (pt "j") (pt "k") (pt "x2") (pt "x3")
	  6 7 DEFAULT-GOAL-NAME DEFAULT-GOAL-NAME 8)
(prop)
(prop)

;; Case x2 | x3 \ne (Nil nat), i.e. defined
(assume 8)
(split)
(add-global-assumption "PathDot" "all r,i,j,k,x2,x3(Path r i x2 j i ->
  Path r i x3 i k -> Path r(i+1)(x2 | x3)j k)")
(use-with "PathDot" (pt "r") (pt "i") (pt "j") (pt "k") (pt "x2") (pt "x3")
	  DEFAULT-GOAL-NAME DEFAULT-GOAL-NAME)
(prop)
(prop)
(add-global-assumption "Rfdot" (pf "all r,i,j,k,x2,x3(Path r i x2 j i ->
  Rf x2 -> Path r i x3 i k -> Rf x3 -> 
  all z(Path r i z j k -> F) -> Rf(x2 | x3))"))
(use-with "Rfdot" (pt "r") (pt "i") (pt "j") (pt "k") (pt "x2") (pt "x3")
	  DEFAULT-GOAL-NAME DEFAULT-GOAL-NAME DEFAULT-GOAL-NAME
	  DEFAULT-GOAL-NAME DEFAULT-GOAL-NAME)
(prop)
(prop)
(prop)
(prop)
(use-with 2 'left 3)

;; Case x1 defined.
(assume 3)
(ex-intro (pt "x1"))
(split)
(search)
(assume 4)
(split)

(add-global-assumption
 "pathlift" "all r,i,j,k,x1(Path r i x1 j k -> Path r(i+1)x1 j k)")
(use-with "pathlift" (pt "r") (pt "i") (pt "j") (pt "k") (pt "x1")
	  DEFAULT-GOAL-NAME)
(use-with 2 'right 3 'left)
(use-with 2 'right 3 'right)
;; Proof finished.
(save "Warshall")

(add-var-name "f" (py "nat=>nat=>list nat"))

(define eterm (proof-to-extracted-term (theorem-name-to-proof "Warshall")))
(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [r,n]
;;  (Rec nat=>nat=>nat=>list nat)n
;;  ([n0,n1][if (n0=n1) n0: [if (r n0 n1) (n0::n1:) (Nil nat)]])
;;  ([n0,f,n1,n2]
;;    [if (f n1 n2=(Nil nat))
;;      [if (f n1 n0=(Nil nat))
;;       (Nil nat)
;;       [if (f n0 n2=(Nil nat)) (Nil nat) (f n1 n0|f n0 n2)]]
;;      (f n1 n2)])
