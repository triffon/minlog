;; $Id: gen-app.scm 2673 2014-01-08 10:00:19Z schwicht $

;; Generic applications: The user hook to define new syntax, written as
;; application.

;; The global look-up table for all kinds of applications:

(define GENERIC-APPLICATION-TABLE '())

;; The interface to the parser:

(define (make-gen-application x y)
  (define (make-gen-app-aux l type x y)
    (cond
     ((null? l)
      (myerror "make-gen-application: unknown form of application"
	       (type-to-string type)))
     (((caar l) type) ((cdar l) x y))
     (else (make-gen-app-aux (cdr l) type x y))))
  (make-gen-app-aux GENERIC-APPLICATION-TABLE (term-to-type x) x y))

;; The interface for the user:

(define (add-new-application pred fun)
  (set! GENERIC-APPLICATION-TABLE
	(cons (cons pred fun)
	      GENERIC-APPLICATION-TABLE)))

;; The inverse: User can specify terms to be recognized as generic
;; applications

(define GENERIC-APPLICATION-SYNTAX-TABLE '())

(define (add-new-application-syntax pred toarg toop)
  (set! GENERIC-APPLICATION-SYNTAX-TABLE
	(cons (list pred toarg toop)
	      GENERIC-APPLICATION-SYNTAX-TABLE)))

(define (term-in-symbolic-app-form? term)
  (term-in-symbolic-app-form-aux GENERIC-APPLICATION-SYNTAX-TABLE term))

(define (term-in-symbolic-app-form-aux l term)
  (cond ((null? l) #f)
	(((caar l) term) #t)
	(else (term-in-symbolic-app-form-aux (cdr l) term))))

(define (term-in-symbolic-app-form-to-arg term)
  (term-in-symbolic-app-form-to-arg-aux GENERIC-APPLICATION-SYNTAX-TABLE term))

(define (term-in-symbolic-app-form-to-arg-aux l term)
  (cond ((null? l)
	 (myerror "term-in-symbolic-app-form-to-arg: not a symbolic app!"
		  (term-to-string term)))
	(((caar l) term)
	 ((cadar l) term))
	(else (term-in-symbolic-app-form-to-arg-aux (cdr l) term))))

(define (term-in-symbolic-app-form-to-op term)
  (term-in-symbolic-app-form-to-op-aux GENERIC-APPLICATION-SYNTAX-TABLE term))

(define (term-in-symbolic-app-form-to-op-aux l term)
  (cond ((null? l)
	 (myerror "term-in-symbolic-app-form-to-op: not a symbolic app!"
		  (term-to-string term)))
	(((caar l) term)
	 ((caddar l) term))
	(else (term-in-symbolic-app-form-to-op-aux (cdr l) term))))

;; Introduction of application notation simplified:
;; add-application takes an application operator as argument.

(define (add-application appop)
  (let* ((optype (term-to-type appop))
	 (type (if (arrow-form? optype)
		   (arrow-form-to-arg-type optype)
		   (myerror "add-application"
			    "application operator of arrow type expected"
			    appop))))
    (if (arrow-form? type)
	(myerror "add-application" "unexpected arrow form" type))
    (add-new-application
     (lambda (x) (equal? x type))
     (lambda (term1 term2) (mk-term-in-app-form appop term1 term2)))
    (add-new-application-syntax
     ;; predicate
     (lambda (term)
       (and (term-in-app-form? term)
	    (let ((op (term-in-app-form-to-op term)))
	      (and (term-in-app-form? op)
		   (term=? appop (term-in-app-form-to-op op))))))
     ;; to arg
     term-in-app-form-to-arg
     ;; to op
     (lambda (term) (term-in-app-form-to-arg (term-in-app-form-to-op term))))))
