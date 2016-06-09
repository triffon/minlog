;; 2016-04-12.  posgcd.scm.

;; (load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(libload "list.scm")
(libload "pos.scm")
(set! COMMENT-FLAG #t)

;; Definitions and totality proofs for quotient and gcd in pos.

;; We define an overloaded quotient and greatest commom divisor.

(add-program-constant "PosQuot" (py "pos=>pos=>pos"))
(add-program-constant "PosGcd" (py "pos=>pos=>pos"))

(add-token "quot" 'mul-op (make-term-creator "quot" "pos"))
(add-token-and-type-to-name "quot" (py "pos") "PosQuot")

(add-token "gcd" 'mul-op (make-term-creator "gcd" "pos"))
(add-token-and-type-to-name "gcd" (py "pos") "PosGcd")

(add-display (py "pos") (make-display-creator "PosQuot" "quot" 'mul-op))
(add-display (py "pos") (make-display-creator "PosGcd" "gcd" 'mul-op))

;; Rules for PosQuot

(add-program-constant "PosQuotAux" (py "nat=>pos=>pos=>list boole"))
(add-computation-rules
 "PosQuotAux Zero pos pos1" "(Nil boole)"
 "PosQuotAux(Succ nat)pos pos1"
 "[if (pos1<2**nat*pos)
   (False::PosQuotAux nat pos pos1)
   [if (pos1=2**nat*pos)
    (True::([nat]False)fbar nat)
    (True::PosQuotAux nat pos(pos1--2**nat*pos))]]")

(set-totality-goal "PosQuotAux")
(assert "allnc p^(TotalPos p^ -> allnc n^(TotalNat n^ -> 
      allnc p^0(TotalPos p^0 ->
       TotalList(PosQuotAux n^ p^ p^0))))")
(use "AllTotalElim")
(assume "p")
(use "AllTotalElim")
(ind)
(strip)
(use "ListTotalVar")
(assume "n" "IH")
(assume "p^1" "Tp1")
(ng)
(use "BooleIfTotal")
(use "PosLtTotal")
(use "Tp1")
(use "PosTotalVar")
(use "TotalListCons")
(use "BooleTotalVar")
(use "IH")
(use "Tp1")
(use "BooleIfTotal")
(use "PosEqTotal")
(use "Tp1")
(use "PosTotalVar")
(use "ListTotalVar")
(use "TotalListCons")
(use "BooleTotalVar")
(use "IH")
(use "PosMinusTotal")
(use "Tp1")
(use "PosTotalVar")
;; Assertion proved.
(assume "Assertion" "n^" "Tn" "p^" "Tp")
(use "Assertion")
(use "Tp")
(use "Tn")
;; Proof finished.
(save-totality)

(add-program-constant "ListBooleToPosAux" (py "list boole=>pos"))
(add-computation-rules
 "ListBooleToPosAux(Nil boole)" "1"

 "ListBooleToPosAux(True::(list boole))"
 "SOne(ListBooleToPosAux(list boole))"

 "ListBooleToPosAux(False::(list boole))"
 "SZero(ListBooleToPosAux(list boole))")

(set-totality-goal "ListBooleToPosAux")
(use "AllTotalElim")
(ind)
(use "PosTotalVar")
(cases)
(assume "(list boole)" "IH")
(ng)
(use "TotalPosSOne")
(use "IH")
(assume "(list boole)" "IH")
(ng)
(use "TotalPosSZero")
(use "IH")
;; Proof finished.
(save-totality)

(add-program-constant "ListBooleToPos" (py "list boole=>pos"))
(add-computation-rules
 "ListBooleToPos(Nil boole)" "1" ;arbitrary

 "ListBooleToPos(False::(list boole))"
 "ListBooleToPos(list boole)"

 "ListBooleToPos(True::(list boole))"
 "ListBooleToPosAux Rev(list boole)")

(set-totality-goal "ListBooleToPos")
(use "AllTotalElim")
(ind)
(use "PosTotalVar")
(cases)
(assume "(list boole)" "IH")
(ng)
(use "PosTotalVar")
(assume "(list boole)" "IH")
(ng)
(use "IH")
;; Proof finished.
(save-totality)

(add-computation-rules
 "pos1 quot pos" "ListBooleToPos(PosQuotAux(PosLog pos1)pos pos1)")

(set-totality-goal "PosQuot")
(use "AllTotalElim")
(assume "p")
(use "AllTotalElim")
(assume "q")
(ng)
(use "PosTotalVar")
;; Proof finished.

;; (pp (nt (pt "3 quot 3")))
;; 1
;; (pp (nt (pt "5 quot 3")))
;; 1
;; (pp (nt (pt "6 quot 3")))
;; 2
;; (pp (nt (pt "8 quot 3")))
;; 2
;; (pp (nt (pt "9 quot 3")))
;; 3
;; (pp (nt (pt "1057 quot 33")))
;; 32
;; (pp (nt (pt "123456 quot 123")))
;; 1003

(add-computation-rules
 "1 gcd pos" "1"
 "SZero pos gcd 1" "1"
 "SZero pos1 gcd SZero pos2" "SZero(pos1 gcd pos2)"
 "SZero pos1 gcd SOne pos2" "pos1 gcd SOne pos2"
 "SOne pos gcd 1" "1"
 "SOne pos1 gcd SZero pos2" "SOne pos1 gcd pos2"
 "SOne pos1 gcd SOne pos2"
 "[if (pos1=pos2) (SOne pos1)
      [if (pos1<pos2) (SOne pos1 gcd(pos2--pos1))
                      ((pos1--pos2)gcd SOne pos2)]]")

(set-totality-goal "PosGcd")
(assert "all n,pos1,pos2(pos1+pos2<n -> TotalPos(pos1 gcd pos2))")
(ind)
;; 4-5
(assume "pos1" "pos2")
(ng)
(use "Efq")
;; 5
(assume "n" "IH")
(cases)
;; 9-11
(strip)
(ng)
(use "PosTotalVar")
;; 10
(assume "pos1")
(cases)
;; 15-17
(strip)
(ng)
(use "PosTotalVar")
;; 16
(assume "pos2" "LtHyp")
(ng #t)
(use "TotalPosSZero")
(use "IH")
(use "NatLtTrans" (pt "PosToNat(SZero pos1+pos2)"))
(simp "PosToNatPlus")
(simp "PosToNatPlus")
(ng #t)
(use "NatLtMonPlus1")
(use "NatLtDouble")
(use "NatLt0PosToNat")
(use "Truth")
(use "NatLtLeTrans" (pt "PosToNat(SZero pos1+SZero pos2)"))
(simp "PosToNatPlus")
(simp "PosToNatPlus")
(ng #t)
(use "NatLtMonPlus2")
(use "Truth")
(use "NatLtDouble")
(use "NatLt0PosToNat")
(use "NatLtSuccToLe")
(use "LtHyp")
;; 17
(assume "pos2" "LtHyp")
(ng #t)
(use "IH")
(use "NatLtLeTrans" (pt "PosToNat(SZero pos1+SOne pos2)"))
(simp "PosToNatPlus")
(simp "PosToNatPlus")
(ng #t)
(use "NatLtMonPlus1")
(use "NatLtDouble")
(use "NatLt0PosToNat")
(use "Truth")
(use "NatLtSuccToLe")
(use "LtHyp")
;; 11
(assume "pos1")
(cases)
;; 54-56
(strip)
(ng)
(use "PosTotalVar")
;; 55
(assume "pos2" "LtHyp")
(ng #t)
(use "IH")
(use "NatLtLeTrans" (pt "PosToNat(SOne pos1+SZero pos2)"))
(simp "PosToNatPlus")
(simp "PosToNatPlus")
(ng #t)
(use "NatLtMonPlus2")
(use "Truth")
(use "NatLtDouble")
(use "NatLt0PosToNat")
(use "NatLtSuccToLe")
(use "LtHyp")
;; 56
(assume "pos2" "LtHyp")
(ng #t) ;BooleIfTotal does not suffice.  Need PosToNatMinus and hence cases
(cases (pt "pos1=pos2"))
;; Case p1=p2
(assume "p1=p2")
(ng #t)
(use "PosTotalVar")
;; Case p1=p2 -> F
(assume "p1=p2 -> F")
(ng #t)
(cases (pt "pos1<pos2"))
;; Case p1<p2
(assume "p1<p2")
(ng #t)
(use "IH")
(use "NatLeLtTrans" (pt "PosToNat(SOne pos1+pos2)"))
(simp "PosToNatPlus")
(simp "PosToNatPlus")
(ng #t)
(use "NatLeMonPlus")
(use "Truth")
(simp "PosToNatMinus")
(use "Truth")
(use "p1<p2")
(use "NatLtLeTrans" (pt "PosToNat(SOne pos1+SOne pos2)"))
(simp "PosToNatPlus")
(simp "PosToNatPlus")
(use "NatLtMonPlus2")
(use "Truth")
(ng #t)
(use "NatLtTrans" (pt "NatDouble(PosToNat pos2)"))
(use "NatLtDouble")
(use "NatLt0PosToNat")
(use "Truth")
(use "NatLtSuccToLe")
(use "LtHyp")
;; Case p1<p2 -> F
(assume "p1<p2 -> F")
(ng #t)
(assert "pos2<pos1")
 (use "PosNotLeToLt")
 (assume "p1<=p2")
 (use "PosLeCases" (pt "pos1") (pt "pos2"))
 (use "p1<=p2")
 (use "p1<p2 -> F")
 (use "p1=p2 -> F")
(assume "p2<p1")
(use "IH")
(use "NatLeLtTrans" (pt "PosToNat(pos1+SOne pos2)"))
(simp "PosToNatPlus")
(simp "PosToNatPlus")
(use "NatLeMonPlus")
(simp "PosToNatMinus")
(use "Truth")
(use "p2<p1")
(use "Truth")
(use "NatLtLeTrans" (pt "PosToNat(SOne pos1+SOne pos2)"))
(simp "PosToNatPlus")
(simp "PosToNatPlus")
(use "NatLtMonPlus1")
(ng #t)
(use "NatLtTrans" (pt "NatDouble(PosToNat pos1)"))
(use "NatLtDouble")
(use "NatLt0PosToNat")
(use "Truth")
(use "Truth")
(use "NatLtSuccToLe")
(use "LtHyp")
;; Assertion proved
(assume "Assertion")
(use "AllTotalElim")
(assume "pos1")
(use "AllTotalElim")
(assume "pos2")
(use "Assertion" (pt "Succ(PosToNat(pos1+pos2))"))
(use "Truth")
;; Proof finished.
(save-totality)

;; (pp (nt (pt "PosGcd 66 27")))
;; 3
;; (pp (nt (pt "PosGcd 974636 754")))
;; 26

