;; 2014-10-14.  normtest.scm (originally written by U.Berger, 14.9.93)

;; Efficiency of normalization
;; ===========================

;; We compare three algorithms for normalization of simply typed
;; lambda terms w.r.t. their efficiency:

;; 1.  Normalization by evaluation (as used in Minlog)

;; 2.  Normalization by a usual recursive algorithm

;; 3.  A variant of 2 corresponding to a call-by-name strategy.

;; As test examples we use iterators applied to other iterators, which
;; have exponentially growing reduction lengths.  It turns out that
;; nbe is the most efficient one.

;; Contents

;; 1.  Normalization by evaluation
;; 1.1.  Long normal form
;; 1.2.  Short (eta) normal form
;; 2.  Recursive normalization
;; 2.1.  Call-by-value
;; 2.2.  call-by-name
;; 3.  Auxiliary functions
;; 4.  Examples
;; 5.  Run times

;; (load "~/git/minlog/init.scm")

;; (define (ev x)
;;   (eval x (the-environment)))

;; 1. Normalization by evaluation
;; ==============================

;; This algorithm can be extracted from the Tait/Troelstra proof of
;; strong normalization.  The following verions work for closed terms
;; only.

;; 1.1.  Long normal form

(define (norm r rho)
  (((phi rho) (ev r)) 0))

(define (phi type)
  (if (ground-type? type)
      (lambda (u) u)
           (let ((psi-rho (psi (arg-type type)))
                 (phi-sigma (phi (val-type type))))
             (lambda (u)
               (lambda (k)
                 (let ((xk (mvar k)))
                   (nabst xk ((phi-sigma (u (psi-rho (lambda (l) xk)))) 
                             (+ k 1)))))))))

(define (psi type)
  (if (ground-type? type)
      (lambda (g) g)
      (let ((phi-rho (phi (arg-type type)))
            (psi-sigma (psi (val-type type))))
          (lambda (g)
             (lambda (v)
                (psi-sigma
                 (lambda (k)
                   (app (g k) ((phi-rho v) k)))))))))


;; 1.2.  Short (eta) normal form

;; Do (set! nabst cabst) .  Then (norm r) computes the eta normal form
;; of r.  Back with (set! nabst abst)

(define (cabst x r)
  (if (application? r)
      (let ((s (operator r))
            (y (argument r)))
        (if (and (equal? x y) (not (free? x s)))
            s
            (list 'lambda (list x) r)))
      (list 'lambda (list x) r)))

;; 2.  Recursive normalization
;; ===========================

;; 2.1.  Call-by-value

(define (recnorm r)
  (cond ((variable? r) r)
	((application? r)
	 (let ((op (recnorm (operator r)))
	       (arg (recnorm (argument r))))
	   (if (abstraction? op)
	       (let ((x (abstvar op))
		     (s (kernel op)))
		 (recnorm (substitute s x arg)))
	       (app op arg))))
	((abstraction? r) (abst (abstvar r) (recnorm (kernel r))))))

;; 2.2.  call-by-name

;; Head normal form, i.e. call-by-name.  Only closed terms of ground
;; type are normalized completely.

(define (hnorm r)
  (cond ((variable? r) r)
	((application? r)
	 (let ((op (hnorm (operator r)))
	       (arg (argument r)))
	   (if (abstraction? op)
	       (let ((x (abstvar op))
		     (s (kernel op)))
		 (hnorm (substitute s x arg)))
	       (app op (hnorm arg)))))
	((abstraction? r) r)))

;; 3.  Auxiliary functions
;; =======================

(define (make-var x k)
  (string->symbol (string-append (symbol->string x) (number->string k))))
(define (mvar k)
  (string->symbol (string-append "X" (number->string k))))
(define (abst x r)
  (list 'lambda (list x) r))
(define app list)

(define nabst abst)

(define ground-type? symbol?)
(define arg-type car)
(define val-type cadr)
(define arrow list)

(define operator car)
(define argument cadr)

(define abstvar caadr)
(define kernel caddr)

(define variable? symbol?)
(define (application? r) (and (list? r) (equal? (length r) 2)))
(define (abstraction? r)
  (and (list? r) (equal? (length r) 3) (equal? (car r) 'lambda)))

(define (fvar r)
  (cond ((variable? r) (list r))
        ((application? r) (append (fvar (operator r))
                                  (fvar (argument r))))
        ((abstraction? r) (erase (abstvar r) (fvar (kernel r))))))

(define (bvar r)
  (cond ((variable? r) '())
        ((application? r) (append (bvar (operator r))
                                  (bvar (argument r))))
        ((abstraction? r) (cons (abstvar r) (bvar (kernel r))))))

(define (free? x r) (memq x (fvar r)))

(define (erase x l)
  (if (null? l)
      '()
      (if (equal? x (car l))
          (erase x (cdr l))
          (cons (car l) (erase x (cdr l))))))

(define (replace s x r)
  (cond ((variable? s) (if (equal? s x)
			   r
			   s))
	((application? s) (app (replace (operator s) x r)
			       (replace (argument s) x r)))
	((abstraction? s)
         (let ((y (abstvar s))
	       (t (kernel s)))
	   (if (equal? x y)
	       s
	       (abst y (replace t x r)))))))
	   
(define (substitute s x r)
  (cond ((variable? s) (if (equal? s x)
			   r
			   s))
	((application? s) (app (substitute (operator s) x r)
			       (substitute (argument s) x r)))
	((abstraction? s)
         (let ((y (abstvar s))
	       (t (kernel s)))
	   (if (equal? x y)
	       s
	       (if (not (member y (fvar r)))
	           (abst y (substitute t x r))
	           (let* ((new-y (fresh y (append (bvar t) (fvar r))))
		          (new-t (replace t y new-y)))
		     (abst new-y (substitute new-t x r)))))))))	    
					   
(define (fresh y l)  ;computes some yk not in the list l
  (do ((k 0 (+ k 1)) ;with minimal k
       (yk (make-var y 0) (make-var y k)))
      ((not (member yk l)) yk)))
      
;; 4.  Examples
;; ============

(define (int-type n)
  (if (zero? n)
      'nat
      (let ((rho (int-type (- n 1))))
        (list rho rho))))

(define (it n)
  (letrec ((iterator-kernel (lambda (n)
                               (if (zero? n)
                                   'x
                                   (app 'f (iterator-kernel (- n 1)))))))
     (abst 'f (abst 'x (iterator-kernel n)))))

(define (rnm n m)
  (app (app (it n) (it m)) (abst 'x 'x)))

(define (rnmx n m) (app (rnm n m) 'x))

;; 5.  Run times
;; =============

(time (norm (rnm 4 4) 'x)) ;0ms
(time (norm (rnm 5 5) 'x)) ;1ms
(time (norm (rnm 5 6) 'x)) ;0 ms
(time (norm (rnm 6 6) 'x)) ;2 ms
(time (norm (rnm 7 6) 'x)) ;11 ms
(time (norm (rnm 7 7) 'x)) ;20 ms
(time (norm (rnm 8 6) 'x)) ;37 ms
(time (norm (rnm 8 7) 'x)) ;104 ms
(time (norm (rnm 8 8) 'x)) ;249 ms

(time (recnorm (rnm 4 4))) ;2 ms
(time (recnorm (rnm 5 5))) ;14 ms
(time (recnorm (rnm 5 6))) ;26 ms
(time (recnorm (rnm 6 6))) ;132 ms
(time (recnorm (rnm 7 6))) ;994 ms
(time (recnorm (rnm 7 7))) ;3 s
(time (recnorm (rnm 8 6))) ;8 s
(time (recnorm (rnm 8 7))) ;40 s

(time (hnorm (rnmx 4 4))) ;6 ms
(time (hnorm (rnmx 5 5))) ;65 ms
(time (hnorm (rnmx 5 6))) ;156 ms
(time (hnorm (rnmx 6 6))) ;1 s
(time (hnorm (rnmx 7 6))) ;11 s
(time (hnorm (rnmx 7 7))) ;36 s
(time (hnorm (rnmx 8 6))) ;91 s

