;;;; "logical.scm", bit access and operations for integers for Scheme
;;; Copyright (C) 1991, 1993, 2001, 2003 Aubrey Jaffer
;
;Permission to copy this software, to modify it, to redistribute it,
;to distribute modified versions, and to use it for any purpose is
;granted, subject to the following restrictions and understandings.
;
;1.  Any copy made of this software must include this copyright notice
;in full.
;
;2.  I have made no warranty or representation that the operation of
;this software will be error-free, and I am under no obligation to
;provide any services, by way of maintenance, update, or otherwise.
;
;3.  In conjunction with products arising from the use of this
;material, there shall be no use of my name in any advertising,
;promotional, or sales literature without prior written consent in
;each case.

;@
(define integer-expt expt)
;   (if (provided? 'inexact)
;       expt
;       (lambda (n k)
; 	(do ((x n (* x x))
; 	     (j k (quotient j 2))
; 	     (acc 1 (if (even? j) acc (* x acc))))
; 	    ((<= j 1)
; 	     (case j
; 	       ((0) acc)
; 	       ((1) (* x acc))
; 	       (else (slib:error 'integer-expt n k))))))))

(define logical:boole-xor
 '#(#(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15)
    #(1 0 3 2 5 4 7 6 9 8 11 10 13 12 15 14)
    #(2 3 0 1 6 7 4 5 10 11 8 9 14 15 12 13)
    #(3 2 1 0 7 6 5 4 11 10 9 8 15 14 13 12)
    #(4 5 6 7 0 1 2 3 12 13 14 15 8 9 10 11)
    #(5 4 7 6 1 0 3 2 13 12 15 14 9 8 11 10)
    #(6 7 4 5 2 3 0 1 14 15 12 13 10 11 8 9)
    #(7 6 5 4 3 2 1 0 15 14 13 12 11 10 9 8)
    #(8 9 10 11 12 13 14 15 0 1 2 3 4 5 6 7)
    #(9 8 11 10 13 12 15 14 1 0 3 2 5 4 7 6)
    #(10 11 8 9 14 15 12 13 2 3 0 1 6 7 4 5)
    #(11 10 9 8 15 14 13 12 3 2 1 0 7 6 5 4)
    #(12 13 14 15 8 9 10 11 4 5 6 7 0 1 2 3)
    #(13 12 15 14 9 8 11 10 5 4 7 6 1 0 3 2)
    #(14 15 12 13 10 11 8 9 6 7 4 5 2 3 0 1)
    #(15 14 13 12 11 10 9 8 7 6 5 4 3 2 1 0)))

(define logical:boole-and
 '#(#(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
    #(0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1)
    #(0 0 2 2 0 0 2 2 0 0 2 2 0 0 2 2)
    #(0 1 2 3 0 1 2 3 0 1 2 3 0 1 2 3)
    #(0 0 0 0 4 4 4 4 0 0 0 0 4 4 4 4)
    #(0 1 0 1 4 5 4 5 0 1 0 1 4 5 4 5)
    #(0 0 2 2 4 4 6 6 0 0 2 2 4 4 6 6)
    #(0 1 2 3 4 5 6 7 0 1 2 3 4 5 6 7)
    #(0 0 0 0 0 0 0 0 8 8 8 8 8 8 8 8)
    #(0 1 0 1 0 1 0 1 8 9 8 9 8 9 8 9)
    #(0 0 2 2 0 0 2 2 8 8 10 10 8 8 10 10)
    #(0 1 2 3 0 1 2 3 8 9 10 11 8 9 10 11)
    #(0 0 0 0 4 4 4 4 8 8 8 8 12 12 12 12)
    #(0 1 0 1 4 5 4 5 8 9 8 9 12 13 12 13)
    #(0 0 2 2 4 4 6 6 8 8 10 10 12 12 14 14)
    #(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15)))

(define (logical:ash-4 x)
  (if (negative? x)
      (+ -1 (quotient (+ 1 x) 16))
      (quotient x 16)))
;@
(define logand
  (letrec
      ((lgand
	(lambda (n2 n1 scl acc)
	  (cond ((= n1 n2) (+ acc (* scl n1)))
		((zero? n2) acc)
		((zero? n1) acc)
		(else (lgand (logical:ash-4 n2)
			     (logical:ash-4 n1)
			     (* 16 scl)
			     (+ (* (vector-ref (vector-ref logical:boole-and
							   (modulo n1 16))
					       (modulo n2 16))
				   scl)
				acc)))))))
    (lambda (n1 n2) (lgand n2 n1 1 0))))
;@
(define logior
  (letrec
      ((lgior
	(lambda (n2 n1 scl acc)
	  (cond ((= n1 n2) (+ acc (* scl n1)))
		((zero? n2) (+ acc (* scl n1)))
		((zero? n1) (+ acc (* scl n2)))
		(else (lgior (logical:ash-4 n2)
			     (logical:ash-4 n1)
			     (* 16 scl)
			     (+ (* (- 15 (vector-ref
					  (vector-ref logical:boole-and
						      (- 15 (modulo n1 16)))
					  (- 15 (modulo n2 16))))
				   scl)
				acc)))))))
    (lambda (n1 n2) (lgior n2 n1 1 0))))
;@
(define logxor
  (letrec
      ((lgxor
	(lambda (n2 n1 scl acc)
	  (cond ((= n1 n2) acc)
		((zero? n2) (+ acc (* scl n1)))
		((zero? n1) (+ acc (* scl n2)))
		(else (lgxor (logical:ash-4 n2)
			     (logical:ash-4 n1)
			     (* 16 scl)
			     (+ (* (vector-ref (vector-ref logical:boole-xor
							   (modulo n1 16))
					       (modulo n2 16))
				   scl)
				acc)))))))
    (lambda (n1 n2) (lgxor n2 n1 1 0))))
;@
(define (lognot n) (- -1 n))
;@
(define (logtest n1 n2)
  (not (zero? (logical:logand n1 n2))))
;@
(define (logbit? index n)
  (logical:logtest (logical:integer-expt 2 index) n))
;@
(define (copy-bit index to bool)
  (if bool
      (logical:logior to (logical:ash 1 index))
      (logical:logand to (logical:lognot (logical:ash 1 index)))))

;;@ This procedure is careful not to use more than DEG bits in
;; computing (- (expt 2 DEG) 1)
(define (logical:ones deg)
  (if (zero? deg) 0 (+ (* 2 (+ -1 (logical:integer-expt 2 (- deg 1)))) 1)))
;@
(define (bit-field n start end)
  (logical:logand (logical:ones (- end start))
		  (logical:ash n (- start))))
;@
(define (bitwise-if mask n0 n1)
  (logical:logior (logical:logand mask n0)
		  (logical:logand (logical:lognot mask) n1)))
;@
(define (copy-bit-field to start end from)
  (logical:bitwise-if (logical:ash (logical:ones (- end start)) start)
		      (logical:ash from start)
		      to))
;@
(define (ash n count)
  (if (negative? count)
      (let ((k (logical:integer-expt 2 (- count))))
	(if (negative? n)
	    (+ -1 (quotient (+ 1 n) k))
	    (quotient n k)))
      (* (logical:integer-expt 2 count) n)))
;@
(define integer-length
  (letrec ((intlen (lambda (n tot)
		     (case n
		       ((0 -1) (+ 0 tot))
		       ((1 -2) (+ 1 tot))
		       ((2 3 -3 -4) (+ 2 tot))
		       ((4 5 6 7 -5 -6 -7 -8) (+ 3 tot))
		       (else (intlen (logical:ash-4 n) (+ 4 tot)))))))
    (lambda (n) (intlen n 0))))
;@
(define logcount
  (letrec ((logcnt (lambda (n tot)
		     (if (zero? n)
			 tot
			 (logcnt (quotient n 16)
				 (+ (vector-ref
				     '#(0 1 1 2 1 2 2 3 1 2 2 3 2 3 3 4)
				     (modulo n 16))
				    tot))))))
    (lambda (n)
      (cond ((negative? n) (logcnt (logical:lognot n) 0))
	    ((positive? n) (logcnt n 0))
	    (else 0)))))

;;;; Bit order and lamination
;@
(define (logical:rotate k count len)
  (set! count (modulo count len))
  (logical:logior (logical:logand (ash k count) (logical:ones len))
		  (logical:ash k (- count len))))
;@
(define (bit-reverse k n)
  (do ((m (if (negative? n) (lognot n) n) (ash m -1))
       (k (+ -1 k) (+ -1 k))
       (rvs 0 (logior (ash rvs 1) (logand 1 m))))
      ((negative? k) (if (negative? n) (lognot rvs) rvs))))
;@
(define (integer->list k . len)
  (if (null? len)
      (do ((k k (ash k -1))
	   (lst '() (cons (odd? k) lst)))
	  ((<= k 0) lst))
      (do ((idx (+ -1 (car len)) (+ -1 idx))
	   (k k (ash k -1))
	   (lst '() (cons (odd? k) lst)))
	  ((negative? idx) lst))))
;@
(define (list->integer bools)
  (do ((bs bools (cdr bs))
       (acc 0 (+ acc acc (if (car bs) 1 0))))
      ((null? bs) acc)))
(define (booleans->integer . bools)
  (list->integer bools))
;@
(define (bitwise:laminate . ks)
  (define nks (length ks))
  (define nbs (apply max (map integer-length ks)))
  (do ((kdx (+ -1 nbs) (+ -1 kdx))
       (ibs 0 (+ (list->integer (map (lambda (k) (logbit? kdx k)) ks))
		 (ash ibs nks))))
      ((negative? kdx) ibs)))
;@
(define (bitwise:delaminate count k)
  (define nbs (* count (+ 1 (quotient (integer-length k) count))))
  (do ((kdx (- nbs count) (- kdx count))
       (lst (vector->list (make-vector count 0))
	    (map (lambda (k bool) (+ (if bool 1 0) (ash k 1)))
		 lst
		 (integer->list (ash k (- kdx)) count))))
      ((negative? kdx) lst)))

;;;; Gray-code
;@
(define (integer->gray-code k)
  (logxor k (ash k -1)))
;@
(define (gray-code->integer k)
  (if (negative? k)
      (slib:error 'gray-code->integer 'negative? k)
      (let ((kln (integer-length k)))
	(do ((d 1 (* d 2))
	     (ans (logxor k (ash k -1))	; == (integer->gray-code k)
		  (logxor ans (ash ans (* d -2)))))
	    ((>= (* 2 d) kln) ans)))))

(define (grayter k1 k2)
  (define kl1 (integer-length k1))
  (define kl2 (integer-length k2))
  (if (eqv? kl1 kl2)
      (> (gray-code->integer k1) (gray-code->integer k2))
      (> kl1 kl2)))
;@
(define (gray-code<? k1 k2)
  (not (or (eqv? k1 k2) (grayter k1 k2))))
(define (gray-code<=? k1 k2)
  (or (eqv? k1 k2) (not (grayter k1 k2))))
(define (gray-code>? k1 k2)
  (and (not (eqv? k1 k2)) (grayter k1 k2)))
(define (gray-code>=? k1 k2)
  (or (eqv? k1 k2) (grayter k1 k2)))

(define logical:logand logand)
(define logical:logior logior)
;;(define logical:logxor logxor)
(define logical:lognot lognot)
(define logical:logtest logtest)
;;(define logical:logbit? logbit?)
;;(define logical:copy-bit copy-bit)
(define logical:ash ash)
;;(define logical:logcount logcount)
;;(define logical:integer-length integer-length)
;;(define logical:bit-field bit-field)
;;(define bit-extract bit-field)
(define logical:bitwise-if bitwise-if)
;;(define logical:copy-bit-field copy-bit-field)
(define logical:integer-expt integer-expt)
