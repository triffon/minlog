;; (load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(libload "numbers.scm")
(libload "simpreal.scm")
(libload "real.scm")
(libload "cont.scm")
(set! COMMENT-FLAG #t)

;; 2014-04-16.  This was minlog/examples/analysis/extraction.scm

(if (not (member "lib/cont.scm" LOADED-FILES))
    (myerror "First load lib/cont.scm"))

;; (time (pp (nt (pt "(IntN 2#9)+(2*((IntP 7#9)-(IntN 2#9)))/4"))))
;; 5#18 ;7ms
;; (time (pp (nt (pt "(IntN 2#9)+((IntP 7#9)-(IntN 2#9))/2")))) ;5#18 ;6ms
;; (time (pp (nt (pt "((IntN 2#9)+(7#9))/2")))) ;5#18 ;4ms
;; (time (pp (nt (pt "((IntN 2#9)+(7#9))")))) ;5#9 ;3ms

;; For further speed-up we provide an external version of +

;; We now want to view RatPlus as a program constant with external
;; code, using add-external-code.  The external code - after evaluation
;; and application to tsubst and the arguments - should give either the
;; final value (e.g., the numeral for the sum) or else #f, in which
;; case the rules are tried next on the arguments.

(define ratplus-code
  '(lambda (tsubst objs)
     (let ((val1 (nbe-object-to-value (car objs)))
	   (val2 (nbe-object-to-value (cadr objs))))
       (and (nbe-constr-value? val1) (nbe-constr-value? val2)
	    (let* ((args1 (nbe-constr-value-to-args val1))
		   (args2 (nbe-constr-value-to-args val2))
		   (vals1 (map nbe-object-to-value args1))
		   (vals2 (map nbe-object-to-value args2)))
	      (and (int-numeral-value? (car vals1))
		   (pos-numeral-value? (cadr vals1))
		   (int-numeral-value? (car vals2))
		   (pos-numeral-value? (cadr vals2))
		   (let* ((numer1 (int-numeral-value-to-number (car vals1)))
			  (denom1 (pos-numeral-value-to-number (cadr vals1)))
			  (numer2 (int-numeral-value-to-number (car vals2)))
			  (denom2 (pos-numeral-value-to-number (cadr vals2)))
			  (sum (+ (/ numer1 denom1) (/ numer2 denom2)))
			  (numer (numerator sum))
			  (denom (denominator sum))
			  (numer-term (int-to-int-term numer))
			  (denom-term (make-numeric-term denom))
			  (constr (constr-name-to-constr "RatConstr"))
			  (term (mk-term-in-app-form
				 (make-term-in-const-form constr)
				 numer-term denom-term)))
		     (nbe-term-to-object
		      term (nbe-make-bindings '() '())))))))))

(define ratminus-code
  '(lambda (tsubst objs)
     (let ((val1 (nbe-object-to-value (car objs)))
	   (val2 (nbe-object-to-value (cadr objs))))
       (and (nbe-constr-value? val1) (nbe-constr-value? val2)
	    (let* ((args1 (nbe-constr-value-to-args val1))
		   (args2 (nbe-constr-value-to-args val2))
		   (vals1 (map nbe-object-to-value args1))
		   (vals2 (map nbe-object-to-value args2)))
	      (and (int-numeral-value? (car vals1))
		   (pos-numeral-value? (cadr vals1))
		   (int-numeral-value? (car vals2))
		   (pos-numeral-value? (cadr vals2))
		   (let* ((numer1 (int-numeral-value-to-number (car vals1)))
			  (denom1 (pos-numeral-value-to-number (cadr vals1)))
			  (numer2 (int-numeral-value-to-number (car vals2)))
			  (denom2 (pos-numeral-value-to-number (cadr vals2)))
			  (diff (- (/ numer1 denom1) (/ numer2 denom2)))
			  (numer (numerator diff))
			  (denom (denominator diff))
			  (numer-term (int-to-int-term numer))
			  (denom-term (make-numeric-term denom))
			  (constr (constr-name-to-constr "RatConstr"))
			  (term (mk-term-in-app-form
				 (make-term-in-const-form constr)
				 numer-term denom-term)))
		     (nbe-term-to-object
		      term (nbe-make-bindings '() '())))))))))

(define rattimes-code
  '(lambda (tsubst objs)
     (let ((val1 (nbe-object-to-value (car objs)))
	   (val2 (nbe-object-to-value (cadr objs))))
       (and (nbe-constr-value? val1) (nbe-constr-value? val2)
	    (let* ((args1 (nbe-constr-value-to-args val1))
		   (args2 (nbe-constr-value-to-args val2))
		   (vals1 (map nbe-object-to-value args1))
		   (vals2 (map nbe-object-to-value args2)))
	      (and (int-numeral-value? (car vals1))
		   (pos-numeral-value? (cadr vals1))
		   (int-numeral-value? (car vals2))
		   (pos-numeral-value? (cadr vals2))
		   (let* ((numer1 (int-numeral-value-to-number (car vals1)))
			  (denom1 (pos-numeral-value-to-number (cadr vals1)))
			  (numer2 (int-numeral-value-to-number (car vals2)))
			  (denom2 (pos-numeral-value-to-number (cadr vals2)))
			  (prod (* (/ numer1 denom1) (/ numer2 denom2)))
			  (numer (numerator prod))
			  (denom (denominator prod))
			  (numer-term (int-to-int-term numer))
			  (denom-term (make-numeric-term denom))
			  (constr (constr-name-to-constr "RatConstr"))
			  (term (mk-term-in-app-form
				 (make-term-in-const-form constr)
				 numer-term denom-term)))
		     (nbe-term-to-object
		      term (nbe-make-bindings '() '())))))))))

(define ratdiv-code
  '(lambda (tsubst objs)
     (let ((val1 (nbe-object-to-value (car objs)))
	   (val2 (nbe-object-to-value (cadr objs))))
       (and (nbe-constr-value? val1) (nbe-constr-value? val2)
	    (let* ((args1 (nbe-constr-value-to-args val1))
		   (args2 (nbe-constr-value-to-args val2))
		   (vals1 (map nbe-object-to-value args1))
		   (vals2 (map nbe-object-to-value args2)))
	      (and (int-numeral-value? (car vals1))
		   (pos-numeral-value? (cadr vals1))
		   (int-numeral-value? (car vals2))
		   (pos-numeral-value? (cadr vals2))
		   (let* ((numer1 (int-numeral-value-to-number (car vals1)))
			  (denom1 (pos-numeral-value-to-number (cadr vals1)))
			  (numer2 (int-numeral-value-to-number (car vals2)))
			  (denom2 (pos-numeral-value-to-number (cadr vals2)))
			  (quot (/ (/ numer1 denom1) (/ numer2 denom2)))
			  (numer (numerator quot))
			  (denom (denominator quot))
			  (numer-term (int-to-int-term numer))
			  (denom-term (make-numeric-term denom))
			  (constr (constr-name-to-constr "RatConstr"))
			  (term (mk-term-in-app-form
				 (make-term-in-const-form constr)
				 numer-term denom-term)))
		     (nbe-term-to-object
		      term (nbe-make-bindings '() '())))))))))

(define ratlt-code
  '(lambda (tsubst objs)
     (let ((val1 (nbe-object-to-value (car objs)))
	   (val2 (nbe-object-to-value (cadr objs))))
       (and (nbe-constr-value? val1) (nbe-constr-value? val2)
	    (let* ((args1 (nbe-constr-value-to-args val1))
		   (args2 (nbe-constr-value-to-args val2))
		   (vals1 (map nbe-object-to-value args1))
		   (vals2 (map nbe-object-to-value args2)))
	      (and (int-numeral-value? (car vals1))
		   (pos-numeral-value? (cadr vals1))
		   (int-numeral-value? (car vals2))
		   (pos-numeral-value? (cadr vals2))
		   (let* ((numer1 (int-numeral-value-to-number (car vals1)))
			  (denom1 (pos-numeral-value-to-number (cadr vals1)))
			  (numer2 (int-numeral-value-to-number (car vals2)))
			  (denom2 (pos-numeral-value-to-number (cadr vals2)))
			  (res (< (/ numer1 denom1) (/ numer2 denom2)))
			  (const (if res true-const false-const))
			  (term (make-term-in-const-form const)))
		     (nbe-term-to-object
		      term (nbe-make-bindings '() '())))))))))

(define ratle-code
  '(lambda (tsubst objs)
     (let ((val1 (nbe-object-to-value (car objs)))
	   (val2 (nbe-object-to-value (cadr objs))))
       (and (nbe-constr-value? val1) (nbe-constr-value? val2)
	    (let* ((args1 (nbe-constr-value-to-args val1))
		   (args2 (nbe-constr-value-to-args val2))
		   (vals1 (map nbe-object-to-value args1))
		   (vals2 (map nbe-object-to-value args2)))
	      (and (int-numeral-value? (car vals1))
		   (pos-numeral-value? (cadr vals1))
		   (int-numeral-value? (car vals2))
		   (pos-numeral-value? (cadr vals2))
		   (let* ((numer1 (int-numeral-value-to-number (car vals1)))
			  (denom1 (pos-numeral-value-to-number (cadr vals1)))
			  (numer2 (int-numeral-value-to-number (car vals2)))
			  (denom2 (pos-numeral-value-to-number (cadr vals2)))
			  (res (<= (/ numer1 denom1) (/ numer2 denom2)))
			  (const (if res true-const false-const))
			  (term (make-term-in-const-form const)))
		     (nbe-term-to-object
		      term (nbe-make-bindings '() '())))))))))

(add-external-code "RatPlus" ratplus-code)
(add-external-code "RatMinus" ratminus-code)
(add-external-code "RatTimes" rattimes-code)
(add-external-code "RatDiv" ratdiv-code)
(add-external-code "RatLt" ratlt-code)
(add-external-code "RatLe" ratle-code)

;; We animate all theorems, working from root to leaves

(animate "IVTApprox")
(animate "RealApprox")
(animate "IVTFinal")
(animate "IVTcds")
(animate "IVTAux")
(animate "ApproxSplit")
(animate "ApproxSplitBoole")

;; Finally we animate Id, to enable numeric calculations

(animate "Id")

;; Test

(define a-sq-minus-two
  (pt "ContConstr 1 2([a0,n1]a0*a0-2)([k]Zero)([k]k+3)"))

;; (time (pp (nt
;;    (apply mk-term-in-app-form
;; 	  (list (proof-to-extracted-term (theorem-name-to-proof "IVTApprox"))
;; 		a-sq-minus-two
;; 		(pt "IntN One") ;-1 is the modulus of increase
;; 		(pt "IntZero")  ;1 <= b-a
;; 		(pt "IntZero")  ;b-a <= 1
;; 		(pt "20"))))))
;; 17193534846817967675#12157665459056928801
;; 460 ms

(exact->inexact (/ 17193534846817967675 12157665459056928801))
;; 1.4142135186002784
(sqrt 2)
;; 1.4142135623730951

;; Check accuracy
;; (define diff (- 1.4142135186002784 1.4142135623730951))
;; diff
;; -4.3772816704645834e-8
;; (exact->inexact (expt 2 -20))
;; 9.5367431640625e-7

(deanimate "Id")

(pp (rename-variables
     (nt (proof-to-extracted-term (theorem-name-to-proof "IVTApprox")))))

;; [f,k,k0,k1,k2]
;;  left((cDC rat@@rat)(f doml@f domr)
;;       ([n,cd]
;;         [let cd0
;;           ((2#3)*left cd+(1#3)*right cd@(1#3)*left cd+(2#3)*right cd)
;;           [if (0<=
;;                (f approx left cd0
;;                 (f uMod(IntS(IntS(IntS(IntS(IntS(IntS(k0+n+k))))))))+
;;                 f approx right cd0
;;                 (f uMod(IntS(IntS(IntS(IntS(IntS(IntS(k0+n+k)))))))))/
;;                2)
;;            (left cd@right cd0)
;;            (left cd0@right cd)]])
;;       (IntToNat(2*(k2+k1))))

(define sqrt-two-approx
  (rename-variables
   (nt (apply mk-term-in-app-form
	      (list (proof-to-extracted-term
		     (theorem-name-to-proof "IVTApprox"))
		    a-sq-minus-two
		    (pt "IntN One") ;-1 is the modulus of increase
		    (pt "IntZero")  ;1 <= b-a
		    (pt "IntZero")  ;b-a <= 1
		    )))))

(pp sqrt-two-approx)

;; [k]
;;  left((cDC rat@@rat)(1@2)
;;       ([n,cd]
;;         [let cd0
;;           ((2#3)*left cd+(1#3)*right cd@(1#3)*left cd+(2#3)*right cd)
;;           [if (0<=(left cd0*left cd0-2+(right cd0*right cd0-2))/2)
;;            (left cd@right cd0)
;;            (left cd0@right cd)]])
;;       (IntToNat(2*k)))

(animate "Id")
(pp (nt (make-term-in-app-form sqrt-two-approx (pt "2"))))
;; 107#81
(pp (nt (make-term-in-app-form sqrt-two-approx (pt "20"))))
;; 17193534846817967675#12157665459056928801
;; (time (tag (nbe-normalize-term-without-eta
;; 	    (make-term-in-app-form sqrt-two-approx (pt "20")))))
;; 300 ms
(deanimate "Id")

;; We now translate terms into scheme expressions, for faster
;; evaluation (no conversions between internal and external numbers)

(term-to-expr sqrt-two-approx)

;; (lambda (k)
;;   (car (((cDC (cons 1 2))
;;           (lambda (n)
;;             (lambda (cd)
;;               (let ([cd0 (cons
;;                            (+ (* 2/3 (car cd)) (* 1/3 (cdr cd)))
;;                            (+ (* 1/3 (car cd)) (* 2/3 (cdr cd))))])
;;                 (if (<= 0
;;                         (/ (+ (- (* (car cd0) (car cd0)) 2)
;;                               (- (* (cdr cd0) (cdr cd0)) 2))
;;                            2))
;;                     (cons (car cd) (cdr cd0))
;;                     (cons (car cd0) (cdr cd)))))))
;;          (IntToNat (* 2 k)))))

;; (time ((ev (term-to-expr sqrt-two-approx)) 20))
;; 3 ms
;; 1910392699673572643/1350851717672992089

;; (time ((ev (term-to-expr sqrt-two-approx)) 100))
;; 35 ms
41737211713808721950509113461986613702889339109196103625535604673708288858253142530485267574435/29512665430652752148753480226197736314359272517043832886063884637676943433478020332709411004889

;; (time ((ev (term-to-expr sqrt-two-approx)) 300))
;; 500 ms
2944593304156165436102846247558257490730845085059145775348712785737552429558941055472664500523847993653960875075500489392461830532348741253430285578096821615417701491158209086792184369992128090401780684332213746112424235660933353732326055138766537198666286440104173743582833475176351331/2082141893205326654083779991150902602700941003443642395329656664801323440350862630969568906052114539645303398663539990042118787521457672342793285135263403898153882623763114393917433013110956461871522162788143751759237923280744039682511207437298831530097535001606799426410247097767236889

;; Same for "Inv"

(deanimate "IVTApprox")
(deanimate "RealApprox")
(deanimate "IVTFinal")
(deanimate "IVTcds")
(deanimate "IVTAux")
(deanimate "ApproxSplit")
(deanimate "ApproxSplitBoole")

;; We now animate all theorems, working from root to leaves

(animate "InvApprox")
(animate "RealApprox")
(animate "Inv")
(animate "IVTcds")
(animate "IVTAux")
(animate "ApproxSplit")
(animate "ApproxSplitBoole")

;; We also need to animate "AC" "IP" with identities:

(animate "AC" (pt "[alpha1=>alpha2]alpha1=>alpha2"))
(animate "IP" (pt "[alpha]alpha"))

(define inv-approx-eterm
  (rename-variables
   (nt (proof-to-extracted-term (theorem-name-to-proof "InvApprox")))))
(pp inv-approx-eterm)

;; [f,k,k0,k1,a,a0,a1,k2]
;;  left((cDC rat@@rat)(f doml@f domr)
;;       ([n,cd]
;;         [let cd0
;;           ((2#3)*left cd+(1#3)*right cd@(1#3)*left cd+(2#3)*right cd)
;;           [if (0<=
;;                (f approx left cd0
;;                 (f uMod(IntS(IntS(IntS(IntS(IntS(IntS(k0+n+k))))))))-
;;                 a1+
;;                 (f approx right cd0
;;                  (f uMod(IntS(IntS(IntS(IntS(IntS(IntS(k0+n+k))))))))-
;;                  a1))/
;;                2)
;;            (left cd@right cd0)
;;            (left cd0@right cd)]])
;;       (IntToNat(2*f uModCont(IntS(IntS(IntS(IntS(k2+k)))))+k1+k1)))

(define sq (pt "ContConstr 1 2([a0,n1]a0*a0)([k]Zero)([k]k+3)"))

(define inv-sq-approx
  (rename-variables
   (nt (apply mk-term-in-app-form
	      (list (proof-to-extracted-term
		     (theorem-name-to-proof "InvApprox"))
		    sq ;continuous function to be inverted
		    (pt "IntN One") ;uniform lower bound on the slope
		    (pt "IntZero") (pt "IntZero") ;bounds for b-a
		    (pt "1") (pt "4") ;interval in range
		    )))))

(pp inv-sq-approx)

;; [a,k]
;;  left((cDC rat@@rat)(1@2)
;;       ([n,cd]
;;         [let cd0
;;           ((2#3)*left cd+(1#3)*right cd@(1#3)*left cd+(2#3)*right cd)
;;           [if (0<=(left cd0*left cd0-a+(right cd0*right cd0-a))/2)
;;            (left cd@right cd0)
;;            (left cd0@right cd)]])
;;       (IntToNat(2*IntS(IntS(IntS(IntS(IntS(IntS(IntS(k+IntN 1))))))))))

;; Finally we animate Id, to enable numeric calculations

(animate "Id")

;; (time
(pp (nbe-normalize-term-without-eta
      (mk-term-in-app-form
       inv-sq-approx
       (pt "3") ;argument of inverted function
       (pt "20") ;error bound (number of binary digits)
       )))
;; )

;; 3730307366945298869534434#2153693963075557766310747 in 470 ms

;; (exact->inexact (/ 3730307366945298869534434 2153693963075557766310747))
;; 1.7320508070785863
;; (sqrt 3)
;; 1.7320508075688772
;; Difference at the 10th decimal digit

;; We now translate terms into scheme expressions, for faster
;; evaluation (no conversions between internal and external numbers)

(term-to-expr inv-sq-approx)

;; (lambda (a)
;;   (lambda (k)
;;     (car (((cDC (cons 1 2))
;;             (lambda (n)
;;               (lambda (cd)
;;                 (let ([cd0 (cons
;;                              (+ (* 2/3 (car cd)) (* 1/3 (cdr cd)))
;;                              (+ (* 1/3 (car cd)) (* 2/3 (cdr cd))))])
;;                   (if (<= 0
;;                           (/ (+ (- (* (car cd0) (car cd0)) a)
;;                                 (- (* (cdr cd0) (cdr cd0)) a))
;;                              2))
;;                       (cons (car cd) (cdr cd0))
;;                       (cons (car cd0) (cdr cd)))))))
;;            (IntToNat
;;              (* 2
;;                 (+ (+ (+ (+ (+ (+ (+ (+ k -1) 1) 1) 1) 1) 1) 1) 1)))))))

;; (time (((ev (term-to-expr inv-sq-approx)) 3) 20))
;; 5 ms

;; (time (((ev (term-to-expr inv-sq-approx)) 3) 100))
;; 40 ms

;; (time (((ev (term-to-expr inv-sq-approx)) 3) 200))
;; 200 ms

