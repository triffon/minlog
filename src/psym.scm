;; $Id: psym.scm 2661 2014-01-08 09:51:52Z schwicht $
;; 5. Predicates
;; =============

;; To be renamed into pred.scm

;; A predicate is
;; - a predicate variable
;; - a predicate constant
;; - an inductively defined predicate constant
;; Generalities for all kinds of predicates:

(define (predicate-to-arity predicate)
  (cond ((pvar-form? predicate) (pvar-to-arity predicate))
	((predconst-form? predicate) (predconst-to-arity predicate))
	((idpredconst-form? predicate) (idpredconst-to-arity predicate))
	(else (myerror "predicate-to-arity"  "predicate expected" predicate))))

;; Totality matters for the abstracted variables of a cterm, because of
;; the inductively defined existential quantifier.  The default is the
;; use of partial variables.

(define (predicate-to-cterm predicate)
  (let* ((arity (predicate-to-arity predicate))
	 (types (arity-to-types arity))
	 (vars (map type-to-new-partial-var types))
	 (varterms (map make-term-in-var-form vars))
	 (formula (apply make-predicate-formula predicate varterms)))
    (apply make-cterm (append vars (list formula)))))

(define (predicate-to-cterm-with-total-vars predicate)
  (let* ((arity (predicate-to-arity predicate))
	 (types (arity-to-types arity))
	 (vars (map type-to-new-var types))
	 (varterms (map make-term-in-var-form vars))
	 (formula (apply make-predicate-formula predicate varterms)))
    (apply make-cterm (append vars (list formula)))))

(define (predicate-to-cterm-with-partial-total-vars predicate)
  (let* ((arity (predicate-to-arity predicate))
	 (types (arity-to-types arity))
	 (vars (if (pair? types)
		   (cons (type-to-new-partial-var (car types))
			 (map type-to-new-var (cdr types)))
		   '()))
	 (varterms (map make-term-in-var-form vars))
	 (formula (apply make-predicate-formula predicate varterms)))
    (apply make-cterm (append vars (list formula)))))

(define (predicate-to-tvars pred)
  (cond ((pvar-form? pred)
	 (let* ((arity (pvar-to-arity pred))
		(types (arity-to-types arity)))
	   (apply union (map type-to-tvars types))))
	((predconst-form? pred)
	 (let* ((arity (predconst-to-arity pred))
		(types (arity-to-types arity)))
	   (apply union (map type-to-tvars types))))
	((idpredconst-form? pred)
	 (let* ((types (idpredconst-to-types pred))
		(cterms (idpredconst-to-cterms pred))
		(formulas (map cterm-to-formula cterms)))
	   (apply union (append (map type-to-tvars types)
				(map formula-to-tvars formulas)))))
	(else (myerror "predicate-to-tvars" "predicate expected" pred))))

(define (predicate-equal? pred1 pred2)
  (cond
   ((pvar-form? pred1)
    (and (pvar-form? pred2) (equal? pred1 pred2)))
   ((predconst-form? pred1)
    (and (predconst-form? pred2)
	 (let ((name1 (predconst-to-name pred1))
	       (arity1 (predconst-to-arity pred1))
	       (index1 (predconst-to-index pred1))
	       (name2 (predconst-to-name pred2))
	       (arity2 (predconst-to-arity pred2))
	       (index2 (predconst-to-index pred2)))
	   (and (string=? name1 name2)
		(equal? arity1 arity2)
		(= index1 index2)))))
   ((idpredconst-form? pred1)
    (and (idpredconst-form? pred2)
	 (let ((name1 (idpredconst-to-name pred1))
	       (types1 (idpredconst-to-types pred1))
	       (cterms1 (idpredconst-to-cterms pred1))
	       (name2 (idpredconst-to-name pred2))
	       (types2 (idpredconst-to-types pred2))
	       (cterms2 (idpredconst-to-cterms pred2)))
	   (and (string=? name1 name2)
		(equal? types1 types2)
		(= (length cterms1) (length cterms2))
		(apply and-op (map (lambda (x y) (cterm=? x y))
				   cterms1 cterms2))))))
   (else (myerror "predicate-equal?" "predicate expected" pred1))))

;; 5-1. Predicate variables
;; ========================

;; A predicate variable of arity rho_1,..., rho_n is viewed as a
;; placeholder for a formula with distinguished (different) variables
;; x_1,..., x_n of types rho_1,..., rho_n (a so called comprehension
;; term).

(define (make-arity . x) (cons 'arity x))

(define (arity-to-types arity) (cdr arity))

(define (arity-to-string arity)
  (if (and (list? arity)
           (< 0 (length arity))
           (eq? 'arity (car arity)))
      (let* ((types (arity-to-types arity))
             (strings (map type-to-string types))
             (strings-with-leading-spaces
              (map (lambda (s) (string-append " " s)) strings)))
        (apply string-append
	       "(arity"
               (append strings-with-leading-spaces
		       (list ")"))))
      (myerror "arity-to-string" "arity expected" arity)))

(define (d-arity arity)
  (if COMMENT-FLAG (display (arity-to-string arity))))

;; Complete test

(define (arity? x)
  (and (list? x)
       (< 0 (length x))
       (eq? 'arity (car x))
       (apply and-op (map type? (arity-to-types x)))))

(define (arity-to-alg-names arity)
  (apply union (map type-to-alg-names (arity-to-types arity))))

;; Predicate variable names are provided in the form of an association
;; list, which assigns to the names their arities.  By default we have
;; the predicate variable bot of arity (arity), called (logical) falsity.

;; For the convenient display of predicate variables, we may provide
;; default variable names for certain arities.

(define DEFAULT-PVAR-NAMES '())

(define (default-pvar-name arity)
  (let ((info (assoc arity DEFAULT-PVAR-NAMES)))
    (if info (cadr info) "")))

(define (set-default-pvar-name arity string)
  (set! DEFAULT-PVAR-NAMES (cons (list arity string) DEFAULT-PVAR-NAMES)))

(define PREDICATE-VARIABLES (list (list "bot" (make-arity))))

(define (add-pvar-name . x)
  (if (null? x)
      (myerror "add-pvar-name" "arguments expected")
      (let* ((rev (reverse x))
	     (arity (car rev))
	     (strings (reverse (cdr rev))))
	(if (not (arity? arity))
	    (myerror "add-pvar-name" "arity expected" arity))
	(for-each
	 (lambda (string)
	   (if (and (string? string) (not (string=? string "")))
	       (if (is-used? string arity 'pvar)
		   *the-non-printing-object*
		   (begin
		     (set! PREDICATE-VARIABLES
			   (append PREDICATE-VARIABLES
				   (list (list string arity))))
		     (add-token string 'pvar-name (cons arity string))
		     (if (string=? "" (default-pvar-name arity))
			 (set-default-pvar-name arity string))
		     (comment
		      "ok, predicate variable " string ": "
		      (arity-to-string arity) " added")))
	       (myerror "add-pvar-name" "string expected" string)))
	 strings))))

(define apv add-pvar-name)

(define (remove-pvar-name . strings)
  (define (rpv1 string)
    (let ((info (assoc string PREDICATE-VARIABLES)))
      (if info
	  (let* ((arity (cadr info))
		 (info1 (assoc arity DEFAULT-PVAR-NAMES)))
	    (do ((l PREDICATE-VARIABLES (cdr l))
		 (res '() (if (string=? (caar l) string)
			      res
			      (cons (car l) res))))
		((null? l) (set! PREDICATE-VARIABLES (reverse res))))
	    (do ((l DEFAULT-PVAR-NAMES (cdr l)) ;added 2001-05-24
		 (res '() (if (string=? (cadar l) string)
			      res
			      (cons (car l) res))))
		((null? l) (set! DEFAULT-PVAR-NAMES (reverse res))))
	    (remove-token string)
	    (comment "ok, predicate variable " string " is removed")
	    (if (and info1 (string=? (cadr info1) string))
		(comment
		 "warning: " string " was default pvariable of arity "
		 (arity-to-string arity))))
	  (multiline-comment
	   "remove-pvar-name" "predicate variable name expected" string))))
  (for-each rpv1 strings))

(define rpv remove-pvar-name)

;; Predicate variables are implemented as lists ('pvar arity index
;; h-deg n-deg name).  If a predicate variable carries no index, we let
;; the index be -1.  name is a string (the name of the predicate
;; variable), to be used for output.

;; To make sure that predicate variables generated by the system are
;; different from all user introduced predicate variables, we maintain a
;; global counter MAXPVARINDEX.  Whenever the user introduces a
;; predicate variable, e.g. p^27, then MAXPVARINDEX is incremented to
;; at least 27.

(define MAXPVARINDEX -1)

;; Degrees of positivity (Harrop-degree) and negativity.

;; Every predicate variable carries a pair h-deg, n-deg.  This
;; restricts the admitted comprehension term {x|A} as follows.
;; h-deg  n-deg   tau^+(A)    tau^-(A)
;;   0      0     arbitrary   arbitrary
;;   1      0     nulltype    arbitrary
;;   0      1     arbitrary   nulltype
;;   1      1     nulltype    nulltype

(define h-deg-zero 0)
(define h-deg-one 1)

(define (h-deg-zero? h-deg)
  (and (integer? h-deg) (zero? h-deg)))

(define (h-deg-one? h-deg)
  (and (integer? h-deg) (positive? h-deg)))

(define (h-deg? x)
  (and (integer? x) (not (negative? x))))

(define n-deg-zero 0)
(define n-deg-one 1)

(define (n-deg-zero? n-deg)
  (and (integer? n-deg) (zero? n-deg)))

(define (n-deg-one? n-deg)
  (and (integer? n-deg) (positive? n-deg)))

(define (n-deg? x)
  (and (integer? x) (not (negative? x))))

;; Constructor, accessors and tests for predicate variables:

(define (make-pvar arity index h-deg n-deg name)
  (set! MAXPVARINDEX (max index MAXPVARINDEX))
  (list 'pvar arity index h-deg n-deg name))

(define (pvar-form? x) (and (pair? x) (eq? 'pvar (car x))))

(define pvar-to-arity cadr)
(define pvar-to-index caddr)
(define pvar-to-h-deg cadddr)
(define (pvar-to-n-deg pvar) (car (cddddr pvar)))
(define (pvar-to-name pvar) (cadr (cddddr pvar)))

;; Complete test:

(define (pvar? x)
  (and (list? x)
       (= 6 (length x))
       (let ((tag (car x))
	     (arity (cadr x))
	     (index (caddr x))
	     (h-deg (cadddr x))
	     (n-deg (car (cddddr x)))
	     (name (cadr (cddddr x))))
	 (and (eq? 'pvar tag)
	      (arity? arity)
	      (integer? index) (<= -1 index)
	      (h-deg? h-deg)
	      (n-deg? n-deg)
	      (or (string=? "" name)
		  (assoc name PREDICATE-VARIABLES))))))

;; For convenience we add mk-pvar with options.  Options are index
;; (default -1), h-deg (default h-deg-zero), n-deg (default
;; n-deg-zero), and name (default given by (default-pvar-name arity)).

(define (mk-pvar arity . options)
  (let ((index -1)
	(h-deg h-deg-zero)
	(n-deg n-deg-zero)
	(name (default-pvar-name arity)))
    (if (pair? options)
	(begin (set! index (car options))
	       (set! options (cdr options))))
    (if (pair? options)
	(begin (set! h-deg (car options))
	       (set! options (cdr options))))
    (if (pair? options)
	(begin (set! n-deg (car options))
	       (set! options (cdr options))))
    (if (pair? options)
	(begin (set! name (car options))
	       (set! options (cdr options))))
    (if (pair? options)
	 (myerror "make-pvar" "unexpected argument" options))
  (cond ((not (and (integer? index) (<= -1 index)))
	 (myerror "make-pvar" "index >= -1 expected" index))
	((not (h-deg? h-deg))
	 (myerror "make-pvar" "h-deg expected" h-deg))
	((not (n-deg? n-deg))
	 (myerror "make-pvar" "n-deg expected" n-deg))
	((not (string? name))
	 (myerror "make-pvar" "string expected" name))
	(else (make-pvar arity index h-deg n-deg name)))))

(define (pvar-with-positive-content? pvar)
  (h-deg-zero? (pvar-to-h-deg pvar)))

(define (pvar-with-negative-content? pvar)
  (n-deg-zero? (pvar-to-n-deg pvar)))

;; For display purposes we use

(define (pvar-to-string pvar)
  (let* ((arity (pvar-to-arity pvar))
	 (index (pvar-to-index pvar))
	 (h-deg (pvar-to-h-deg pvar))
	 (n-deg (pvar-to-n-deg pvar))
	 (name (pvar-to-name pvar))
	 (name1
	  (if (not (string=? "" name))
	      name
	      (let ((info (assoc name DEFAULT-PVAR-NAMES)))
		(if info
		    (cadr info)
		    (let* ((strings (map type-to-string (arity-to-types arity)))
			   (strings-with-leading-spaces
			    (map (lambda (x) (string-append " " x)) strings)))
		      (if (null? (arity-to-types arity))
			  "Pvar"
			  (apply string-append
				 "(Pvar" (append strings-with-leading-spaces
						 (list ")")))))))))
	 (modifier
	  (if (h-deg-zero? h-deg)
	      (if (n-deg-zero? n-deg)
		  (if (and (not (= index -1))
			   (initial-substring? "(Pvar" name1))
		      "_"
		      "")
		  "'")
	      (if (n-deg-zero? n-deg) "^" "^'")))
	 (index-string (if (= index -1) "" (number-to-string index))))
    (string-append name1 modifier index-string)))

(define (pvar-name? string) (assoc string PREDICATE-VARIABLES))

(define (pvar-name-to-arity string)
  (let ((info (assoc string PREDICATE-VARIABLES)))
    (if info
	(cadr info)
	(myerror "pvar-name-to-arity" "pvar-name expected"
		 string))))

;; For automatic generation of predicate variables we need

(define (numerated-pvar? pvar)
  (and (string=? "" (pvar-to-name pvar))
       (<= 0 (pvar-to-index pvar))))

(define (numerated-pvar-to-index x) (pvar-to-index x))

(define (arity-to-new-pvar arity . rest)
  (if (null? rest)
      (make-pvar arity (+ 1 MAXPVARINDEX) h-deg-one n-deg-one
		 (default-pvar-name arity))
      (make-pvar arity (+ 1 MAXPVARINDEX)
		 (pvar-to-h-deg (car rest)) (pvar-to-n-deg (car rest))
		 (default-pvar-name arity))))

(define (arity-to-new-non-harrop-pvar arity)
  (make-pvar arity (+ 1 MAXPVARINDEX) h-deg-zero n-deg-one
	     (default-pvar-name arity)))

(define (arity-to-new-harrop-pvar arity)
  (make-pvar arity (+ 1 MAXPVARINDEX) h-deg-one n-deg-zero
	     (default-pvar-name arity)))

(define (arity-to-new-general-pvar arity)
  (make-pvar arity (+ 1 MAXPVARINDEX) h-deg-zero n-deg-zero
	     (default-pvar-name arity)))

;; Occasionally we may want to create a new pvariable with the same name
;; (and degree of totality) as a given one.  This is useful e.g. for
;; bound renaming.  Therefore we supply

(define (pvar-to-new-pvar pvar)
  (make-pvar
   (pvar-to-arity pvar)
   (+ 1 MAXPVARINDEX)
   (pvar-to-h-deg pvar)
   (pvar-to-n-deg pvar)
   (pvar-to-name pvar)))

;; 5-2. Predicate constants
;; ========================

;; General reasons for having predicate constants:
;; - We need Total and TotalMR, which are *not*
;;   placeholders for formulas.
;; - We need predicates to be axiomatized

;; General properties of predconsts:
;; - Only Total has computational content.
;; - They do not change their name when a tsubst is employed.  Hence from
;;   a name one can only read off the uninstantiated type.
;; - Their meaning can be fixed by axioms (e.g. for E and also for
;;   Bar(.,.) of arity ('arity tree seq))

;; Predicate constant names are provided in the form of an association
;; list, which assigns to the names their arities.  By default we have
;; the predicate constant Total of arity (arity alpha).

(define PREDCONST-NAMES
  (list
   (list "Total" (make-arity (make-tvar -1 DEFAULT-TVAR-NAME)))
   (list "TotalMR" (make-arity (make-tvar -1 DEFAULT-TVAR-NAME)
			       (make-tvar -1 DEFAULT-TVAR-NAME)))))

(define (add-predconst-name . x)
  (if (null? x)
      (myerror "add-predconst-name" "arguments expected")
      (let* ((rev (reverse x))
	     (arity (car rev))
	     (strings (reverse (cdr rev))))
	(if (not (arity? arity))
	    (myerror "add-predconst-name" "arity expected" arity))
	(for-each
	 (lambda (string)
	   (if (and (string? string) (not (string=? string "")))
	       (if (is-used? string arity 'predconst)
		   *the-non-printing-object*
		   (begin
		     (set! PREDCONST-NAMES
			   (append PREDCONST-NAMES (list (list string arity))))
		     (add-token
		      string
		      'predconst-name
		      (string-and-arity-to-predconst-parse-function
		       string arity))
		     (comment
		      "ok, predicate constant " string ": "
		      (arity-to-string arity) " added")))
	       (myerror "add-predconst-name" "string expected" string)))
	 strings))))

(define (string-and-arity-and-cterms-to-idpc-parse-function name arity cterms)
  (lambda args
    (let* ((uninst-types (arity-to-types arity))
	   (arg-types
	    (if (= (length uninst-types) (length args))
		(map term-to-type args)
		(apply
		 myerror
		 "string-and-arity-and-cterms-to-idpc-parse-function"
		 "arguments and arity of different lengths"
		 name arity
		 args)))
	   (uninst-type (apply mk-arrow (append uninst-types
						(list (make-alg "boole")))))
	   (type (apply mk-arrow (append arg-types
					 (list (make-alg "boole")))))
	   (tsubst (type-match-modulo-coercion uninst-type type))
	   (tvars (idpredconst-name-to-tvars name)))
      (if tsubst
	  (let ((subst-types
		 (map (lambda (tvar) (let ((info (assoc tvar tsubst)))
				       (if info (cadr info) tvar)))
		      tvars)))
	    (apply make-predicate-formula
		   (make-idpredconst name subst-types cterms) args))
	  (apply
	   myerror
	   "string-and-arity-and-cterms-to-idpc-parse-function"
	   "types do not fit for inductively defined predicate constant"
	   name
	   uninst-types arg-types)))))

(define (string-and-arity-to-predconst-parse-function string arity)
  (lambda (index . args)
    (let* ((uninst-types (arity-to-types arity))
	   (types (map term-to-type args))
	   (uninst-type
	    (apply mk-arrow (append uninst-types (list (make-alg "boole")))))
	   (type (apply mk-arrow (append types (list (make-alg "boole")))))
	   (tsubst (if (= (length uninst-types) (length types))
		       (type-match uninst-type type)
		       #f)))
      (if tsubst
	  (apply make-predicate-formula
		 (make-predconst arity tsubst index string)
		 args)
	  (apply myerror "types do not fit" string
		 (append uninst-types types))))))

(define apredc add-predconst-name)

(define (remove-predconst-name . strings)
  (define (rpredc1 string)
    (if (assoc string PREDCONST-NAMES)
	(begin
	  (do ((l PREDCONST-NAMES (cdr l))
	       (res '() (if (string=? (caar l) string)
			    res
			    (cons (car l) res))))
	      ((null? l) (set! PREDCONST-NAMES (reverse res))))
	  (remove-token string)
	  (comment "ok, predicate constant " string " is removed"))
	(multiline-comment
	 "remove-predconst-name" "predicate constant name expected" string)))
  (for-each rpredc1 strings))

(define rpredc remove-predconst-name)

;; Predicate constants are implemented as lists
;; ('predconst uninst-arity tsubst index name).

;; Constructor, accessors and tests for predicate constants:

(define (make-predconst uninst-arity tsubst index name)
  (list 'predconst uninst-arity tsubst index name))

(define (predconst-form? x) (and (pair? x) (eq? 'predconst (car x))))

(define predconst-to-uninst-arity cadr)
(define predconst-to-tsubst caddr)
(define predconst-to-index cadddr)
(define (predconst-to-name predconst) (car (cddddr predconst)))

(define (predconst-to-arity predconst)
  (let* ((uninst-arity (predconst-to-uninst-arity predconst))
	 (tsubst (predconst-to-tsubst predconst))
	 (uninst-types (arity-to-types uninst-arity))
	 (types (map (lambda (x) (type-substitute x tsubst)) uninst-types)))
    (apply make-arity types)))

;; (Almost) complete test:

(define (predconst? x)
  (and (list? x)
       (= 5 (length x))
       (let ((tagsymbol (car x))
	     (uninst-arity (cadr x))
	     (tsubst (caddr x))
	     (index (cadddr x))
	     (name (car (cddddr x))))
	 (and (eq? 'predconst tagsymbol)
	      (arity? uninst-arity)
	      (integer? index) (<= -1 index)
	      (tsubst? tsubst)
	      (or (string=? "" name)
		  (assoc name PREDCONST-NAMES))))))

(define (predconst-name? string) (assoc string PREDCONST-NAMES))

(define (predconst-name-to-arity predconst-name)
  (let ((info (assoc string PREDCONST-NAMES)))
    (if info
	(cadr info)
	(myerror "predconst-name-to-arity" "predconst-name expected"
		 predconst-name))))

;; To allow for a convenient display, we maintain a global variable
;; PREDCONST-DISPLAY consisting of entries (name token-type display-string)

(define PREDCONST-DISPLAY '())

(define (add-predconst-display name token-type display-string)
  (set! PREDCONST-DISPLAY
	(cons (list name token-type display-string) PREDCONST-DISPLAY)))

;; For instance, adding for a predconst Less the token type predconst-infix
;; and the display string << requires

;; (add-token
;;  "<<"
;;  'predconst-infix
;;  (string-and-arity-to-predconst-parse-function
;;   "Less" (make-arity (py DEFAULT-TVAR-NAME) (py DEFAULT-TVAR-NAME))))

;; (add-predconst-display "Less" 'predconst-infix "<<")

(define (predconst-to-string predconst)
  (let* ((name (predconst-to-name predconst))
	 (index (predconst-to-index predconst))
	 (index-string (if (= index -1) "" (number-to-string index)))
	 (info (assoc name PREDCONST-DISPLAY)))
    (if info
	(string-append (caddr info) index-string)
	(string-append name index-string))))

;; 5-3. Inductively defined predicate constants
;; ============================================

;; Inductively defined predicate constants (idpredconsts) are implemented
;; as lists

;; ('idpredconst name types cterms).

;; Constructor, accessors and tests for inductively defined predicate
;; constants:

(define (make-idpredconst name types cterms)
  (if
   (and (member name '("ExDT" "ExLT" "ExRT" "ExUT"))
	(not (t-deg-one? (var-to-t-deg (car (cterm-to-vars (car cterms)))))))
   (myerror "make-idpredconst"
	    "comprehension term with total variable expected"
	    (car (cterm-to-vars (car cterms)))))
  (list 'idpredconst name types cterms))

;; The following is used in grammar.scm, and involves some tests

(define (idpredconst-name-and-types-and-cterms-to-idpredconst name types
							      cterms)
  (let* ((tvars (idpredconst-name-to-tvars name))
	 (tsubst
	  (if (= (length tvars) (length types))
	      (make-substitution tvars types)
	      (myerror "idpredconst-name-and-types-and-cterms-to-idpredconst"
		       "equal lengths expected of tvars" tvars
		       "and types" types)))
	 (param-pvars (idpredconst-name-to-param-pvars name))
	 (subst-param-pvar-arities
	  (map (lambda (arity)
		 (apply make-arity (map (lambda (type)
					  (type-substitute type tsubst))
					(arity-to-types arity))))
	       (map pvar-to-arity param-pvars)))
	 (cterm-arities
	  (map (lambda (cterm) (apply make-arity
				      (map var-to-type (cterm-to-vars cterm))))
	       cterms)))
    (if (not (equal? subst-param-pvar-arities cterm-arities))
	(myerror "idpredconst-name-and-types-and-cterms-to-idpredconst"
		 "equal arities expected of subst-param-pvar-arities"
		 subst-param-pvar-arities "and cterm-arities"
		 cterm-arities))
    (make-idpredconst name types cterms)))

(define (idpredconst-form? x) (and (pair? x) (eq? 'idpredconst (car x))))

(define idpredconst-to-name cadr)
(define idpredconst-to-types caddr)
(define idpredconst-to-cterms cadddr)

(define (idpredconst-to-arity idpc)
  (let* ((name (idpredconst-to-name idpc))
	 (types (idpredconst-to-types idpc))
	 (tsubst (idpredconst-name-and-types-to-tsubst name types))
	 (pvar (idpredconst-name-to-pvar name))
	 (uninst-arity (pvar-to-arity pvar))
	 (uninst-types (arity-to-types uninst-arity))
	 (inst-types
	  (map (lambda (x) (type-substitute x tsubst)) uninst-types)))
    (apply make-arity inst-types)))

;; (Almost) complete test:

(define (idpredconst? x)
  (and (list? x)
       (= 4 (length x))
       (let ((tag (car x))
	     (name (cadr x))
	     (types (caddr x))
	     (cterms (cadddr x)))
	 (and (eq? 'idpredconst tag)
	      (assoc name IDS)))))

(define (idpredconst-to-tpsubst idpc)
  (let* ((name (idpredconst-to-name idpc))
	 (types (idpredconst-to-types idpc))
	 (param-cterms (idpredconst-to-cterms idpc))
	 (tsubst (idpredconst-name-and-types-to-tsubst name types))
	 (param-pvars (idpredconst-name-to-param-pvars name))
	 (psubst
	  (make-substitution-wrt pvar-cterm-equal? param-pvars param-cterms)))
    (append tsubst psubst)))

(define (check-idpredconst x)
  (if (not (idpredconst-form? x))
      (myerror "check-idpredconst" "idpredconst form expected" x))
  (if (not (and (list? x) (= 4 (length x))))
      (myerror "check-idpredconst" "list of length 4 expected" x))
  (let ((name (cadr x))
	(types (caddr x))
	(cterms (cadddr x)))
    (if (not (assoc name IDS))
	(myerror "check-idpredconst" "idpredconst name expected" name))
    (if (not (list? types))
	(myerror "check-idpredconst" "list of types expected" types))
    (if (not (list? cterms))
	(myerror "check-idpredconst" "list of cterms expected" cterms))
    (let ((tvars (idpredconst-name-to-tvars name))
	  (param-pvars (idpredconst-name-to-param-pvars name)))
      (if (not (= (length tvars) (length types)))
	  (myerror "check-idpredconst" "lists of the same lengths expected"
		   tvars types))
      (if (not (= (length param-pvars) (length cterms)))
	  (myerror "check-idpredconst" "lists of the same lengths expected"
		   param-pvars cterms))
      (let ((tpsubst (append (map (lambda (tvar type) (list tvar type))
				  tvars types)
			     (map (lambda (pvar cterm) (list pvar cterm))
				  param-pvars cterms))))
	(check-admissible-tpsubst tpsubst))
					;tvar(param-pvar) in mr-et-tvars
					;implies cterm c.r.
      (let* ((names (idpredconst-name-to-simidpc-names name))
	     (clauses-with-names
	      (apply append
		     (map idpredconst-name-to-clauses-with-names names)))
	     (clauses (map car clauses-with-names))
	     (et-types (map formula-to-et-type clauses))
	     (et-tvars (apply union (map type-to-tvars et-types)))
	     (et-tvars-of-param-pvars (map PVAR-TO-TVAR param-pvars))
	     (mr-et-tvars (list-transform-positive et-tvars
			    (lambda (tvar)
			      (member tvar et-tvars-of-param-pvars)))))
	(for-each
	 (lambda (pvar cterm)
	   (if (and (member (PVAR-TO-TVAR pvar) mr-et-tvars)
		    (formula-of-nulltype? (cterm-to-formula cterm)))
	       (myerror "check-idpredconst" "c.r. formula expected"
			(cterm-to-formula cterm)
			"for param-pvar" pvar)))
	 param-pvars cterms)))))

;; To allow for a convenient display, we maintain a global variable
;; IDPREDCONST-DISPLAY consisting of entries (name token-type display-string)

(define IDPREDCONST-DISPLAY '())

(define (add-idpredconst-display name token-type display-string)
  (set! IDPREDCONST-DISPLAY
	(cons (list name token-type display-string) IDPREDCONST-DISPLAY)))

;; For instance, adding for a idpredconst RatEq the token type
;; pred-infix and the display string === requires

;; (add-token
;;  "==="
;;  'pred-infix
;;  (lambda (x y)
;;    (make-predicate-formula (make-idpredconst "RatEq" '() '()) x y)))

;; (add-idpredconst-display "RatEq" 'pred-infix "===")

(define (idpredconst-to-string idpc)
  (let* ((name (idpredconst-to-name idpc))
	 (types (idpredconst-to-types idpc))
	 (param-cterms (idpredconst-to-cterms idpc))
	 (type-strings (map type-to-string types))
	 (cterm-strings (map cterm-to-string param-cterms))
	 (strings (append type-strings cterm-strings))
	 (type-strings-with-leading-spaces
	  (map (lambda (x) (string-append " " x)) type-strings))
	 (cterm-strings-with-leading-spaces
	  (map (lambda (x) (string-append " " x)) cterm-strings)))
    (cond
     ((member name '("ExD" "ExDT"))
      (let* ((cterm (car param-cterms))
	     (var (car (cterm-to-vars cterm)))
	     (kernel (cterm-to-formula cterm))
	     (varstring (var-to-string var))
	     (kernelstring (formula-to-string kernel)))
	(string-append "exd" (separator-string "exd" varstring)
		       varstring (separator-string varstring kernelstring)
		       kernelstring)))
     ((member name '("ExL" "ExLT"))
      (let* ((cterm (car param-cterms))
	     (var (car (cterm-to-vars cterm)))
	     (kernel (cterm-to-formula cterm))
	     (varstring (var-to-string var))
	     (kernelstring (formula-to-string kernel)))
	(string-append "exl" (separator-string "exl" varstring)
		       varstring (separator-string varstring kernelstring)
		       kernelstring)))
     ((member name '("ExR" "ExRT"))
      (let* ((cterm (car param-cterms))
	     (var (car (cterm-to-vars cterm)))
	     (kernel (cterm-to-formula cterm))
	     (varstring (var-to-string var))
	     (kernelstring (formula-to-string kernel)))
	(string-append "exr" (separator-string "exr" varstring)
		       varstring (separator-string varstring kernelstring)
		       kernelstring)))
     ((member name '("ExU" "ExUT"))
      (let* ((cterm (car param-cterms))
	     (var (car (cterm-to-vars cterm)))
	     (kernel (cterm-to-formula cterm))
	     (varstring (var-to-string var))
	     (kernelstring (formula-to-string kernel)))
	(string-append "exu" (separator-string "exu" varstring)
		       varstring (separator-string varstring kernelstring)
		       kernelstring)))
     ((string=? "AndD" name)
      (let* ((cterm1 (car param-cterms))
	     (cterm2 (cadr param-cterms))
	     (kernel1 (cterm-to-formula cterm1))
	     (kernel2 (cterm-to-formula cterm2)))
	(string-append (formula-to-string kernel1)
		       " andd "
		       (formula-to-string kernel2))))
     ((string=? "AndL" name)
      (let* ((cterm1 (car param-cterms))
	     (cterm2 (cadr param-cterms))
	     (kernel1 (cterm-to-formula cterm1))
	     (kernel2 (cterm-to-formula cterm2)))
	(string-append (formula-to-string kernel1)
		       " andl "
		       (formula-to-string kernel2))))
     ((string=? "AndR" name)
      (let* ((cterm1 (car param-cterms))
	     (cterm2 (cadr param-cterms))
	     (kernel1 (cterm-to-formula cterm1))
	     (kernel2 (cterm-to-formula cterm2)))
	(string-append (formula-to-string kernel1)
		       " andr "
		       (formula-to-string kernel2))))
     ((string=? "AndU" name)
      (let* ((cterm1 (car param-cterms))
	     (cterm2 (cadr param-cterms))
	     (kernel1 (cterm-to-formula cterm1))
	     (kernel2 (cterm-to-formula cterm2)))
	(string-append (formula-to-string kernel1)
		       " andu "
		       (formula-to-string kernel2))))
     ((string=? "OrD" name)
      (let* ((cterm1 (car param-cterms))
	     (cterm2 (cadr param-cterms))
	     (kernel1 (cterm-to-formula cterm1))
	     (kernel2 (cterm-to-formula cterm2)))
	(string-append (formula-to-string kernel1)
		       " ord "
		       (formula-to-string kernel2))))
     ((string=? "OrL" name)
      (let* ((cterm1 (car param-cterms))
	     (cterm2 (cadr param-cterms))
	     (kernel1 (cterm-to-formula cterm1))
	     (kernel2 (cterm-to-formula cterm2)))
	(string-append (formula-to-string kernel1)
		       " orl "
		       (formula-to-string kernel2))))
     ((string=? "OrR" name)
      (let* ((cterm1 (car param-cterms))
	     (cterm2 (cadr param-cterms))
	     (kernel1 (cterm-to-formula cterm1))
	     (kernel2 (cterm-to-formula cterm2)))
	(string-append (formula-to-string kernel1)
		       " orr "
		       (formula-to-string kernel2))))
     ((string=? "OrU" name)
      (let* ((cterm1 (car param-cterms))
	     (cterm2 (cadr param-cterms))
	     (kernel1 (cterm-to-formula cterm1))
	     (kernel2 (cterm-to-formula cterm2)))
	(string-append (formula-to-string kernel1)
		       " oru "
		       (formula-to-string kernel2))))
     ((string=? "OrNc" name)
      (let* ((cterm1 (car param-cterms))
	     (cterm2 (cadr param-cterms))
	     (kernel1 (cterm-to-formula cterm1))
	     (kernel2 (cterm-to-formula cterm2)))
	(string-append (formula-to-string kernel1)
		       " ornc "
		       (formula-to-string kernel2))))
     ((string=? "EqD" name) "eqd")
     (else
      (let* ((info (assoc name IDPREDCONST-DISPLAY))
	     (new-name (if info (caddr info) name))
	     (tvars-inferable-from-arity?
	      (null? (set-minus
		      (idpredconst-name-to-tvars name)
		      (apply union (map type-to-tvars
					(arity-to-types
					 (pvar-to-arity
					  (idpredconst-name-to-pvar
					   name)))))))))
	(if tvars-inferable-from-arity?
	    (if (null? param-cterms)
		new-name
		(apply string-append
		       "(" new-name
		       (append cterm-strings-with-leading-spaces
			       (list ")"))))
	    (apply string-append
		   "(" new-name
		   (append type-strings-with-leading-spaces
			   cterm-strings-with-leading-spaces
			   (list ")")))))))))

(define (idpredconst-to-free idpc)
  (let* ((types (idpredconst-to-types idpc))
	 (cterms (idpredconst-to-cterms idpc)))
    (apply union (map cterm-to-free cterms))))

;; Inductively defined predicate constant names are provided in the form
;; of an association list IDS, which assigns all relevant information to
;; the name.

;; Format of IDS:

;; ((idpredconst-name idpredconst-names-with-pvars-and-opt-alg-names
;; 	             (clause1 name1) (clause2 name2)...)
;;  ...)

;; Here the assigned pvars serve for ease of substitutions when forming
;; e.g. an elimination axiom.  The presence of an alg-name indicates
;; that this idpredconst is computationally relevant, i.e., has
;; computational content.

;; Example:
;; (add-ids
;;  (list (list "TrCl" (make-arity (py "alpha") (py "alpha")) "algTrCl"))
;;  '("allnc x^,y^(R x^ y^ -> TrCl x^ y^)" "InitTrCl")
;;  '("allnc x^,y^,z^(R x^ y^ -> TrCl y^ z^ -> TrCl x^ z^)" "GenTrCl"))

;; How it works: add TrCl temporarily as a predicate variable.  Then
;; parse the clauses.  Create new pvar X.  Substitute TrCl by X.
;; Remove pvar TrCl.  Create idpredconst TrCl.  Form clauses by
;; substituting TrCl for X.

(define IDS '())

(define (idpredconst-name? string) (assoc string IDS))

(define (idpredconst-name-to-pvar name)
  (let* ((info1 (assoc name IDS))
	 (idpredconst-names-with-pvars-and-opt-alg-names
	  (if
	   info1 (cadr info1)
	   (myerror
	    "idpredconst-name-to-pvar-name" "idpredconst name expected" name)))
	 (info2 (assoc name idpredconst-names-with-pvars-and-opt-alg-names)))
    (cadr info2)))

(define (idpredconst-name-to-opt-alg-name name)
  (let* ((info1 (assoc name IDS))
	 (idpredconst-names-with-pvars-and-opt-alg-names
	  (if
	   info1 (cadr info1)
	   (myerror
	    "idpredconst-name-to-opt-alg-name" "idpredconst name expected"
	    name)))
	 (info2 (assoc name idpredconst-names-with-pvars-and-opt-alg-names)))
    (cddr info2)))

(define (idpredconst-name-to-alg-name name)
  (let ((opt-alg-name (idpredconst-name-to-opt-alg-name name)))
    (if (pair? opt-alg-name) (car opt-alg-name)
	(myerror "idpredconst-name-to-alg-name"
		 "alg name expected for" name))))

(define (idpredconst-name-to-nbe-alg-name name)
  (string-append "nbe" name))

(define (idpredconst-name-to-idpc-names-with-pvars-and-opt-alg-names name)
  (let* ((info (assoc name IDS)))
    (if info (cadr info)
	(myerror "idpredconst-name-to-idpc-names-with-pvars-and-opt-alg-names"
		 "idpredconst name expected" name))))

(define (idpredconst-name-to-simidpc-names name)
  (map car (idpredconst-name-to-idpc-names-with-pvars-and-opt-alg-names name)))

(define (idpredconst-name-to-pvars name)
  (map cadr
       (idpredconst-name-to-idpc-names-with-pvars-and-opt-alg-names name)))

(define (idpredconst-name-to-param-pvars name)
  (let* ((idpc-names-with-pvars-and-opt-alg-names
	  (idpredconst-name-to-idpc-names-with-pvars-and-opt-alg-names name))
	 (names (map car idpc-names-with-pvars-and-opt-alg-names))
	 (pvars (map cadr idpc-names-with-pvars-and-opt-alg-names))
	 (clauses-with-names
	  (apply append (map idpredconst-name-to-clauses-with-names names)))
	 (clauses (map car clauses-with-names))
	 (clause-pvars-list (map formula-to-pvars clauses))
	 (clause-pvars (apply union clause-pvars-list)))
    (set-minus clause-pvars pvars)))

(define (idpredconst-name-to-spos-param-pvars name)
  (let* ((idpc-names-with-pvars-and-opt-alg-names
	  (idpredconst-name-to-idpc-names-with-pvars-and-opt-alg-names name))
	 (names (map car idpc-names-with-pvars-and-opt-alg-names))
	 (pvars (map cadr idpc-names-with-pvars-and-opt-alg-names))
	 (clauses-with-names
	  (apply append (map idpredconst-name-to-clauses-with-names names)))
	 (clauses (map car clauses-with-names))
	 (prems
	  (apply append (map imp-impnc-all-allnc-form-to-premises clauses)))
	 (spos-pvars (apply union (map formula-to-spos-pvars prems))))
    (set-minus spos-pvars pvars)))

(define (idpredconst-name-to-relevant-param-pvars name)
  (let* ((idpc-names-with-pvars-and-opt-alg-names
	  (idpredconst-name-to-idpc-names-with-pvars-and-opt-alg-names name))
	 (names (map car idpc-names-with-pvars-and-opt-alg-names))
	 (pvars (map cadr idpc-names-with-pvars-and-opt-alg-names))
	 (clauses-with-names
	  (apply append (map idpredconst-name-to-clauses-with-names names)))
	 (clauses (map car clauses-with-names))
	 (prems
	  (apply append (map imp-impnc-all-allnc-form-to-premises clauses)))
	 (spos-pvars (apply union (map formula-to-spos-pvars prems)))
	 (spos-param-pvars (set-minus spos-pvars pvars))
	 (cr-pvars (list-transform-positive spos-param-pvars
		     (lambda (pvar) (h-deg-zero? (pvar-to-h-deg pvar)))))
	 (et-types (map formula-to-et-type clauses))
	 (et-tvars (apply union (map type-to-tvars et-types))))
    (list-transform-positive cr-pvars
      (lambda (pvar) (member (PVAR-TO-TVAR pvar) et-tvars)))))

(define (idpredconst-to-spos-pvars idpc)
  (let* ((idpc-name (idpredconst-to-name idpc))
	 (cterms (idpredconst-to-cterms idpc))
	 (spos-cterms
	  (list-head cterms (length (idpredconst-name-to-spos-param-pvars
				     idpc-name)))))
    (apply union (map formula-to-spos-pvars
		      (map cterm-to-formula spos-cterms)))))

(define (idpredconst-name-to-clauses-with-names name)
  (let* ((info (assoc name IDS)))
    (if info (cddr info)
	(myerror "idpredconst-name-to-clauses-with-names"
		 "idpredconst name expected" name))))

(define (idpredconst-name-to-clauses name)
  (map car (idpredconst-name-to-clauses-with-names name)))

(define (mr-idpredconst-name? x)
  (and (string? x) (final-substring? "MR" x) (not (string=? "MR" x))))

(define (nc-idpredconst-name? name)
  (let ((info (assoc name IDS)))
    (and (pair? info)
	 (null? (cddr (assoc name (cadr info)))))))

(define (mr-idpredconst-name-to-orig-idpredconst-name mr-idpc-name)
  (if (mr-idpredconst-name? mr-idpc-name)
      (substring mr-idpc-name 0 (- (string-length mr-idpc-name)
				   (string-length "MR")))
      (myerror "mr-idpredconst-name-to-orig-idpredconst-name"
	       "name of an mr-idpredconst expected"
	       mr-idpc-name)))

(define (idpredconst-name-to-tvars name)
  (if (mr-idpredconst-name? name)
      (mr-idpredconst-name-to-tvars name)
      (orig-idpredconst-name-to-tvars name)))

(define (orig-idpredconst-name-to-tvars name)
  (let* ((idpredconst-names-with-pvars-and-opt-alg-names
	  (idpredconst-name-to-idpc-names-with-pvars-and-opt-alg-names name))
	 (names (map car idpredconst-names-with-pvars-and-opt-alg-names))
	 (clauses-with-names
	  (apply append (map idpredconst-name-to-clauses-with-names names)))
	 (clauses (map car clauses-with-names))
	 (clause-tvars-list (map formula-to-tvars clauses)))
    (apply union clause-tvars-list)))

(define (mr-idpredconst-name-to-tvars mr-idpc-name)
  (let* ((name (if (mr-idpredconst-name? mr-idpc-name)
		   (mr-idpredconst-name-to-orig-idpredconst-name mr-idpc-name)
		   (myerror "mr-idpredconst-name-to-tvars"
			    "name of an mr-idpredconst expected"
			    mr-idpc-name)))
	 (names (idpredconst-name-to-simidpc-names name))
	 (clauses-with-names
	  (apply append (map idpredconst-name-to-clauses-with-names names)))
	 (clauses (map car clauses-with-names))
	 (clause-tvars-list (map formula-to-tvars clauses))
	 (tvars (apply union clause-tvars-list))
	 (et-types (map formula-to-et-type clauses))
	 (et-tvars (apply union (map type-to-tvars et-types)))
	 (param-pvars (idpredconst-name-to-param-pvars name))
	 (et-tvars-of-param-pvars (map PVAR-TO-TVAR param-pvars))
	 (mr-et-tvars (list-transform-positive et-tvars
			(lambda (tvar)
			  (member tvar et-tvars-of-param-pvars)))))
    (append mr-et-tvars tvars)))

(define (idpredconst-name-and-types-to-tsubst name types)
  (let ((tvars (idpredconst-name-to-tvars name)))
    (if (= (length tvars) (length types))
	(make-substitution tvars types)
	(myerror "idpredconst-name-and-types-to-tsubst"
		 "equal lengths expected: tvars" tvars
		 "should have the same length as types" types))))

(define (idpredconst-name-to-params name)
  (apply union (map formula-to-free (idpredconst-name-to-clauses name))))

;; add-ids means add inductively defined predicates.  How it works: We
;; are given idpc-names-with-arities-and-opt-alg-names.  For simplicity
;; assume that there is only one idpc-name.  We are also given its
;; clauses as clause-strings-with-opt-names.  For parsing the
;; clause-strings, a new predicate variable idpc-pvar is created and
;; (using it) clauses-with-idpc-pvars-and-names are built.  The names
;; of the clauses are either given or else created, in the form
;; EvenZero, EvenOne etc.  The presence of an alg-name (e.g., algEven)
;; in idpc-names-with-arities-and-opt-alg-names indicates that the idpc
;; is computationally relevant (c.r.), that is requires witnesses, for
;; extraction.  If an alg-name is present, the clauses generate
;; constructors;; default-name CEvenZero, CEvenOne.  We use nbeEven as
;; alg-name for nbe.

;; We may also have the string identity in the field where an
;; opt-alg-name is expected.  This is allowed iff there is exactly one
;; clause with et-type of the form et-tvar=>idpc-pvar-tvar.  Then no
;; new algebra is created.  Later [x]x will be taken as realizer for
;; the (single) clause, and [x,f]f x as realizer for the elim axiom.

;; Structure of add-ids.  First some tests are done, and some global
;; data are computed.  Then an algebra et-alg for the extracted terms
;; is created (if it was not provided) and ALGEBRAS updated.  Finally
;; add-ids-aux is called for the added idpcs.  add-ids-aux updates
;; ALGEBRAS with nbe-alg, adds tokens for the idpc-names and adds the
;; clauses as theorems.

;; We also allow non-computational (n.c.) inductively defined predicates.
;; Then idpc-names-with-arities-and-opt-alg-names has no alg-name.  The
;; elimination scheme for such inductive predicates must be restricted to
;; n.c. formulas.  However, there is an important exception: in the
;; special case of a one-clause-nc definition (i.e., with only one clause
;; involving tonc, allnc only) there are no restrictions on the
;; elimination scheme.  This is the case for Leibniz equality EqD, and
;; n.c. variants ExU and AndU of the existential quantifier and of
;; conjunction.

(define (add-ids idpc-names-with-arities-and-opt-alg-names .
		 clause-strings-with-opt-names)
  (if (not (list? idpc-names-with-arities-and-opt-alg-names))
      (myerror
       "add-ids" "list idpc-names-with-arities-and-opt-alg-names expected"
       idpc-names-with-arities-and-opt-alg-names))
  (for-each
   (lambda (x)
     (if
      (not (and (<= 2 (length x))
		(string? (car x))
		(arity? (cadr x))
		(or (= 2 (length x))
		    (and (= 3 (length x)) (string? (caddr x))))))
      (myerror "add-ids" "idpc-name with arity and opt alg-name expected" x)))
   idpc-names-with-arities-and-opt-alg-names)
  (set! OLD-COMMENT-FLAG COMMENT-FLAG)
  (set! COMMENT-FLAG #f)
  (let*
      ((idpc-names (map car idpc-names-with-arities-and-opt-alg-names))
       (new-idpc-names-test
	(if (not (apply and-op (map (lambda (s)
				      (and (string? s)
					   (not (is-used?
						 s '() 'idpredconst))))
				    idpc-names)))
	    (begin (set! COMMENT-FLAG OLD-COMMENT-FLAG)
		   (myerror "add-ids" "list of new strings expected"
			    idpc-names))))
       (clause-strings-with-opt-names-test
	(for-each
	 (lambda (x)
	   (if (or (not (list? x))
		   (< 2 (length x))
		   (not (string? (car x)))
		   (and (pair? (cdr x)) (not (string? (cadr x)))))
	       (begin
		 (set! COMMENT-FLAG OLD-COMMENT-FLAG)
		 (myerror "add-ids"
			  "list of clause-string and optional name expected"
			  x))))
	 clause-strings-with-opt-names))
       (all-with-content?
	(apply and-op (map (lambda (x) (< 2 (length x)))
			   idpc-names-with-arities-and-opt-alg-names)))
       (all-without-content?
	(apply and-op (map (lambda (x) (= 2 (length x)))
			   idpc-names-with-arities-and-opt-alg-names)))
       (all-with-or-all-without-content-test
	(if
	 (not (or all-with-content? all-without-content?))
	 (begin
	   (set! COMMENT-FLAG OLD-COMMENT-FLAG)
	   (myerror "add-ids" "inductively defined predicate constants"
		    idpc-names
		    "should be either all with or all without content"))))
       (arities (map cadr idpc-names-with-arities-and-opt-alg-names))
       (clause-strings (map car clause-strings-with-opt-names))
       (opt-names (map cdr clause-strings-with-opt-names))
       (temporal-pvar-names (do ((l1 idpc-names (cdr l1))
				 (l2 arities (cdr l2)))
				((null? l1))
			      (add-pvar-name (car l1) (car l2))))
       (clauses (map pf clause-strings))
       (special-nc-idpc?
	(and (= 1 (length clauses))
	     (impnc-allnc-pvar-formula? (car clauses))))
       (remove-temporal-pvar-names (apply remove-pvar-name idpc-names))
       (idpc-pvars
	(map (if (or all-with-content? special-nc-idpc?)
		 arity-to-new-general-pvar
		 arity-to-new-harrop-pvar) arities))
       (var-lists
	(map (lambda (arity)
	       (map type-to-new-partial-var (arity-to-types arity)))
	     arities))
       (atoms (map (lambda (x y)
		     (apply make-predicate-formula
			    (cons x (map make-term-in-var-form y))))
		   idpc-pvars var-lists))
       (cterms (map (lambda (x y) (apply make-cterm (append x (list y))))
		    var-lists atoms))
					;temporarily add idpc-names as
					;pvars to parse clause-strings
       (clauses-with-idpc-pvars
	(let* ((pvars
		(map (lambda (x y)
		       (make-pvar x -1 h-deg-zero n-deg-zero y))
		     arities idpc-names))
	       (psubst (map list pvars cterms)))
	  (map (lambda (x) (formula-substitute x psubst)) clauses)))
       (param-pvars (set-minus (apply union (map formula-to-pvars
						 clauses-with-idpc-pvars))
			       idpc-pvars))
					;test: idpc-pvars occur only strictly
					;positive in premises of clauses
       (test-for-strict-positivity-of-idpc-pvars-in-prems
	(let* ((prems (apply append (map imp-impnc-all-allnc-form-to-premises
					 clauses-with-idpc-pvars)))
	       (spos-pvars (apply union (map formula-to-spos-pvars prems)))
	       (pvars (apply union (map formula-to-pvars prems))))
					;idpc-pvars subseteq spos-pvars
	  (if (pair? (intersection (set-minus pvars spos-pvars) idpc-pvars))
	      (begin
		(set! COMMENT-FLAG OLD-COMMENT-FLAG)
		(apply myerror "add-ids"
		       "strict positivity of idpc pvars in premises expected"
		       clauses-with-idpc-pvars)))))
       (clauses-with-idpc-pvars-and-opt-names
	(map cons
	     clauses-with-idpc-pvars
	     opt-names))
					;create names EvenZero etc if
					;none are given
       (clauses-with-idpc-pvars-and-names
	(do ((l clauses-with-idpc-pvars-and-opt-names (cdr l))
	     (pvar-counter-alist-and-res
	      (list (map (lambda (pvar) (list pvar 0)) idpc-pvars) '())
	      (let* ((pvar-counter-alist (car pvar-counter-alist-and-res))
		     (res (cadr pvar-counter-alist-and-res))
		     (clause-with-idpc-pvar-and-opt-name (car l))
		     (clause (car clause-with-idpc-pvar-and-opt-name))
		     (opt-name (cdr clause-with-idpc-pvar-and-opt-name))
		     (pvar (predicate-form-to-predicate
			    (imp-impnc-all-allnc-form-to-final-conclusion
			     clause)))
		     (idpc-name
		      (cadr (assoc pvar (map list idpc-pvars idpc-names))))
		     (i (cadr (assoc pvar pvar-counter-alist)))
		     (name (if (null? opt-name)
			       (string-append
				idpc-name
				(number-to-alphabetic-string i))
			       (car opt-name))))
		(list (cons (list pvar (+ 1 i))
			    (remove (list pvar i) pvar-counter-alist))
		      (cons (list clause name) res)))))
	    ((null? l) (reverse (cadr pvar-counter-alist-and-res)))))
       (clause-names (map cadr clauses-with-idpc-pvars-and-names))
       (idpc-tvars (map PVAR-TO-TVAR idpc-pvars))
       (idpc-tvars-cr (if all-with-content?
			  (map PVAR-TO-TVAR idpc-pvars)
			  '()))
       (alg-names (if all-with-content?
		      (map caddr idpc-names-with-arities-and-opt-alg-names)
		      '()))
       (param-pvar-tvars (map PVAR-TO-TVAR param-pvars))
       (known-alg-names?
	(and all-with-content?
	     (assoc (car alg-names) ALGEBRAS)
	     (equal? alg-names (alg-name-to-simalg-names (car alg-names)))))
       (identity? ;single clause with alg-name identity and et-type of
					;the form et-tvar=>idpc-pvar-tvar
	(and
	 all-with-content?
	 (= 1 (length alg-names))
	 (string=? "identity" (car alg-names))
	 (= 1 (length clauses-with-idpc-pvars))
	 (let ((et-type (formula-to-et-type (car clauses-with-idpc-pvars))))
	   (and (arrow-form? et-type)
		(tvar-form? (arrow-form-to-arg-type et-type))
		(tvar-form? (arrow-form-to-val-type et-type))))))
       (et-types (if (not all-with-content?) '()
		     (map formula-to-et-type clauses-with-idpc-pvars)))
       (et-constr-names
	(if (and (pair? alg-names) (not known-alg-names?) (not identity?))
	    (map (lambda (name) (string-append "C" name)) clause-names)))
       (et-tvars
	(if (pair? alg-names)
	    (set-minus (apply union (map (lambda (x)
					   (type-to-tvars
					    (formula-to-et-type x)))
					 clauses-with-idpc-pvars))
		       idpc-tvars)))
       (et-standard-tvars
	(if (pair? alg-names)
	    (do ((i 1 (+ 1 i))
		 (res '() (cons (make-tvar i DEFAULT-TVAR-NAME) res)))
		((> i (length et-tvars)) (reverse res)))))
       (et-standard-tsubst
	(if (pair? alg-names)
	    (make-substitution et-tvars et-standard-tvars)))
       (tsubst2 ;temporarily add alg-names with token type alg to ALGEBRAS
	(if (and (pair? alg-names) (not known-alg-names?) (not identity?))
	    (begin
	      (set! OLD-ALGEBRAS ALGEBRAS)
	      (for-each (lambda (x)
			  (set! ALGEBRAS
				(cons (list x alg-names 'alg) ALGEBRAS)))
			alg-names)
	      (map (lambda (x y) (list x (make-alg y)))
		   idpc-tvars-cr alg-names))))
       (et-constr-types
	(if (and (pair? alg-names) (not known-alg-names?) (not identity?))
	    (map (lambda (x)
		   (type-substitute x (append tsubst2 et-standard-tsubst)))
		 et-types)))
       (et-constr-type-strings-with-names
	(if (and (pair? alg-names) (not known-alg-names?) (not identity?))
	    (let ((constr-type-strings (map type-to-string et-constr-types)))
	      (set! ALGEBRAS OLD-ALGEBRAS)
	      (map list constr-type-strings et-constr-names))))
       (test ;check whether known alg-names fit with et-types
	(and
	 known-alg-names?
	 (let* ((final-val-types
		 (map (lambda (alg-name)
			(arrow-form-to-final-val-type
			 (typed-constr-name-to-type
			  (car (alg-name-to-typed-constr-names alg-name)))))
		      alg-names))
		(alg-tvars (alg-name-to-tvars (car alg-names)))
		(alg-standard-tvars
		 (do ((i 1 (+ 1 i))
		      (res '() (cons (make-tvar i DEFAULT-TVAR-NAME) res)))
		     ((> i (length alg-tvars)) (reverse res))))
		(alg-standard-tsubst
		 (make-substitution alg-tvars alg-standard-tvars))
		(standard-final-val-types
		 (map (lambda (type) (type-substitute type alg-standard-tsubst))
		      final-val-types))
		(tsubst-for-idpc-tvars-cr
		 (make-substitution idpc-tvars-cr standard-final-val-types))
		(subst-et-types
		 (map (lambda (x)
			(type-substitute x (append tsubst-for-idpc-tvars-cr
						   et-standard-tsubst)))
		      et-types))
		(typed-constr-names
		 (apply append
			(map alg-name-to-typed-constr-names alg-names)))
		(constr-types
		 (map typed-constr-name-to-type typed-constr-names))
		(standard-constr-types
		 (map (lambda (type) (type-substitute type alg-standard-tsubst))
		      constr-types))
		(equality-test (equal? subst-et-types standard-constr-types)))
	   (if
	    (not equality-test)
	    (begin
	      (set! COMMENT-FLAG OLD-COMMENT-FLAG)
	      (apply myerror
		     "add-ids" "standard constructor types"
		     (append standard-constr-types
			     (list "are different from substituted et-types")
			     subst-et-types)))))))
       (idpc-pvars-with-clauses ;((idpc-pvar1 clause1 clause2 ...) ...)
	(map (lambda (idpc-pvar)
	       (do ((l clauses-with-idpc-pvars (cdr l))
		    (res '()
			 (if (equal?
			      idpc-pvar
			      (predicate-form-to-predicate
			       (imp-impnc-all-allnc-form-to-final-conclusion
				(car l))))
			     (cons (car l) res)
			     res)))
		   ((null? l) (cons idpc-pvar (reverse res)))))
	     idpc-pvars))
       (clauses-list (map cdr idpc-pvars-with-clauses))
       (init-clauses (map car clauses-list))
       ;; (test-for-inhabitedness
       ;; 	 (for-each
       ;; 	  (lambda (init-clause)
       ;; 	   (if (pair? (intersection ;pvars in prems of present init-clause
       ;; 		       (apply union (map formula-to-pvars
       ;; 					 (imp-impnc-all-allnc-form-to-premises
       ;; 					  init-clause)))
       ;; 					;present and later idpc-pvars
       ;; 		       (member (predicate-form-to-predicate
       ;; 				(imp-impnc-all-allnc-form-to-final-conclusion
       ;; 				 init-clause))
       ;; 			       idpc-pvars)))
       ;; 	       (begin
       ;; 		 (set! COMMENT-FLAG OLD-COMMENT-FLAG)
       ;; 		 (myerror "add-ids" "nullary initial clause expected"
       ;; 			  init-clause))))
       ;; 	  init-clauses))
       )
					;remove pvars that were temporarily
					;added to parse the clause-strings
    (apply remove-pvar-name idpc-names)
    (set! OLD-ALGEBRAS ALGEBRAS)
					;remove algebras temporarily
					;added to create et-constr-type-strings
    (if (and (pair? alg-names) (not known-alg-names?) (not identity?))
	(set! ALGEBRAS OLD-ALGEBRAS))
					;add et algebras
    (if (and (pair? alg-names) (not known-alg-names?) (not identity?))
	(apply add-algs alg-names et-constr-type-strings-with-names))
    (add-ids-aux idpc-names-with-arities-and-opt-alg-names
		 clauses-with-idpc-pvars
		 idpc-pvars
		 idpc-tvars
		 opt-names)))

(define (add-ids-aux idpc-names-with-arities-and-opt-alg-names
		     clauses-with-idpc-pvars
		     idpc-pvars
		     idpc-tvars
		     opt-names)
  (let* ((idpc-names (map car idpc-names-with-arities-and-opt-alg-names))
	 (clauses-with-idpc-pvars-and-opt-names
	  (map cons clauses-with-idpc-pvars opt-names))
	 (clauses-with-idpc-pvars-and-names
	  (do ((l clauses-with-idpc-pvars-and-opt-names (cdr l))
	       (pvar-counter-alist-and-res
		(list (map (lambda (pvar)
			     (list pvar 0)) idpc-pvars) '())
		(let* ((pvar-counter-alist
			(car pvar-counter-alist-and-res))
		       (res (cadr pvar-counter-alist-and-res))
		       (clause-with-idpc-pvar-and-opt-name (car l))
		       (clause (car clause-with-idpc-pvar-and-opt-name))
		       (opt-name (cdr clause-with-idpc-pvar-and-opt-name))
		       (pvar (predicate-form-to-predicate
			      (imp-impnc-all-allnc-form-to-final-conclusion
			       clause)))
		       (idpc-name
			(cadr (assoc pvar (map list idpc-pvars idpc-names))))
		       (i (cadr (assoc pvar pvar-counter-alist)))
		       (name (if (null? opt-name)
				 (string-append
				  idpc-name (number-to-alphabetic-string i))
				 (car opt-name))))
		  (list (cons (list pvar (+ 1 i))
			      (remove (list pvar i) pvar-counter-alist))
			(cons (list clause name) res)))))
	      ((null? l) (reverse (cadr pvar-counter-alist-and-res)))))
	 (idpc-names-and-clauses-with-idpc-pvars-and-names
	  (map (lambda (idpc-name)
		 (do ((l clauses-with-idpc-pvars-and-names (cdr l))
		      (res
		       '()
		       (if
			(let* ((pvar (cadr (assoc idpc-name
						  (map list
						       idpc-names
						       idpc-pvars))))
			       (concl
				(imp-impnc-all-allnc-form-to-final-conclusion
				 (caar l))))
			  (and (predicate-form? concl)
			       (equal? pvar (predicate-form-to-predicate
					     concl))))
			(cons (car l) res)
			res)))
		     ((null? l) (cons idpc-name (reverse res)))))
	       idpc-names))
	 (nbe-types (map nbe-formula-to-type clauses-with-idpc-pvars))
	 (nbe-alg-names (map idpredconst-name-to-nbe-alg-name idpc-names))
	 (nbe-alg-names-and-number-of-clauses
	  (map (lambda (x y) (list x (length (cdr y))))
	       nbe-alg-names idpc-names-and-clauses-with-idpc-pvars-and-names))
	 (nbe-constr-names
	  (apply
	   append
	   (map (lambda (nbe-alg-name idpredconst-name)
		  (let ((number-of-clauses
			 (cadr (assoc
				nbe-alg-name
				nbe-alg-names-and-number-of-clauses))))
		    (do ((n 0 (+ 1 n))
			 (res '()
			      (cons (string-append
				     (number-to-alphabetic-string n)
				     idpredconst-name)
				    res)))
			((= n number-of-clauses) (reverse res)))))
		nbe-alg-names idpc-names)))
	 (nbe-tvars (set-minus (apply union (map (lambda (x)
						   (type-to-tvars
						    (nbe-formula-to-type x)))
						 clauses-with-idpc-pvars))
			       idpc-tvars))
	 (nbe-standard-tvars
	  (do ((i 1 (+ 1 i))
	       (res '() (cons (make-tvar i DEFAULT-TVAR-NAME) res)))
	      ((> i (length nbe-tvars)) (reverse res))))
	 (nbe-tsubst (make-substitution nbe-tvars nbe-standard-tvars))
	 (nbe-alg-names (map idpredconst-name-to-nbe-alg-name idpc-names))
					;temporarily add nbe-alg-names
					;with token type alg for
					;nbe-constr-type-strings-with-names
	 (nbe-tsubst-for-idpc-tvars ;overrides nbe-tsubst for idpc-tvars
	  (begin (set! OLD-ALGEBRAS ALGEBRAS)
		 (for-each
		  (lambda (x)
		    (set! ALGEBRAS
			  (cons (list x nbe-alg-names 'alg) ALGEBRAS)))
		  nbe-alg-names)
		 (map (lambda (x y) (list x (make-alg y)))
		      idpc-tvars nbe-alg-names)))
	 (nbe-constr-types
	  (map (lambda (x) (type-substitute
			    x (append nbe-tsubst-for-idpc-tvars nbe-tsubst)))
	       nbe-types))
	 (nbe-constr-type-strings-with-names
	  (let ((constr-type-strings (map type-to-string nbe-constr-types)))
	    (set! ALGEBRAS OLD-ALGEBRAS)
	    (map list constr-type-strings nbe-constr-names))))
					;add nbe algebras
    (apply add-algs nbe-alg-names nbe-constr-type-strings-with-names)
					;add idpcs
    (set! COMMENT-FLAG OLD-COMMENT-FLAG)
    (for-each ;of idpc-names-and-clauses-with-idpc-pvars-and-names
					;and arities
     (lambda (x arity)
       (let ((idpc-name (car x))
	     (clauses-with-idpc-pvars-and-names (cdr x))
	     (idpc-names-with-pvars-and-opt-alg-names
	      (map (lambda (x y) (cons (car x) (cons y (cddr x))))
		   idpc-names-with-arities-and-opt-alg-names
		   idpc-pvars)))
	 (comment "ok, inductively defined predicate constant "
		  idpc-name " added")
	 (set! IDS (cons (append
			  (list idpc-name
				idpc-names-with-pvars-and-opt-alg-names)
			  clauses-with-idpc-pvars-and-names)
			 IDS))))
     idpc-names-and-clauses-with-idpc-pvars-and-names
     (map cadr idpc-names-with-arities-and-opt-alg-names))
    (let ((param-tvars
	   (apply union (map idpredconst-name-to-tvars idpc-names)))
	  (param-pvars
	   (set-minus (apply union (map formula-to-pvars
					clauses-with-idpc-pvars))
		      idpc-pvars)))
      (for-each ;of idpc-names-and-clauses-with-idpc-pvars-and-names
					;and arities
       (lambda (x arity)
	 (let ((idpc-name (car x))
	       (clauses-with-idpc-pvars-and-names (cdr x))
	       (idpc-names-with-pvars-and-opt-alg-names
		(map (lambda (x y) (cons (car x) (cons y (cddr x))))
		     idpc-names-with-arities-and-opt-alg-names
		     idpc-pvars))
	       (non-inferable-param-tvars
		(set-minus
		 param-tvars
		 (apply union
			(map type-to-tvars (arity-to-types arity))))))
					;add tokens for idpc-names
	   (cond
	    ((and (null? param-pvars)
		  (null? non-inferable-param-tvars))
	     (add-token
	      idpc-name
	      'idpredconst-name
	      (string-and-arity-and-cterms-to-idpc-parse-function
	       idpc-name arity '())))
	    ((and (pair? param-pvars)
		  (pair? non-inferable-param-tvars))
	     (add-token
	      idpc-name
	      'idpredconstscheme-name
	      idpc-name))
	    ((and (pair? param-pvars)
		  (null? non-inferable-param-tvars))
	     (add-token
	      idpc-name
	      'idpredconstscheme-name-wit ;wit=with-inferable-types
	      (lambda (cterms)
		(string-and-arity-and-cterms-to-idpc-parse-function
		 idpc-name arity cterms))))
	    (else
	     (myerror
	      "add-ids-aux"
	      "unexpected idpredconst without cterms whose param-tvars"
	      "cannot be inferred from the arguments" idpc-name)))))
       idpc-names-and-clauses-with-idpc-pvars-and-names
       (map cadr idpc-names-with-arities-and-opt-alg-names))
					;add clauses as theorems
      (for-each ;of idpc-names-and-clauses-with-idpc-pvars-and-names
       (lambda (x)
	 (let ((idpc-name (car x))
	       (clauses-with-idpc-pvars-and-names (cdr x)))
	   (do ((i 0 (+ 1 i))
		(names (map cadr clauses-with-idpc-pvars-and-names)
		       (cdr names)))
	       ((= i (length clauses-with-idpc-pvars-and-names)))
	     (let* ((cterms
		     (if (member idpc-name '("ExDT" "ExLT" "ExRT" "ExUT"))
			 (map predicate-to-cterm-with-total-vars param-pvars)
			 (map predicate-to-cterm param-pvars)))
		    (aconst
		     (number-and-idpredconst-to-intro-aconst
		      i (make-idpredconst idpc-name param-tvars cterms)))
		    (proof (make-proof-in-aconst-form aconst))
		    (string (car names))
		    (formula (proof-to-formula proof)))
	       (set! THEOREMS (cons (list string aconst proof) THEOREMS))
	       (if (not (formula-of-nulltype? formula))
		   (let* ((pconst-name
			   (theorem-or-global-assumption-name-to-pconst-name
			    string))
			  (type (formula-to-et-type formula)))
		     (set! OLD-COMMENT-FLAG COMMENT-FLAG)
		     (set! COMMENT-FLAG #f)
		     (add-program-constant pconst-name type t-deg-one 'const 0)
		     (set! COMMENT-FLAG OLD-COMMENT-FLAG)))))))
       idpc-names-and-clauses-with-idpc-pvars-and-names))))

(define (clauses-with-idpc-pvars-to-nullary-clauses clauses-with-idpc-pvars)
  (let ((clauses-to-clauses-wo-rec-calls-for-concl-pvars
	 (lambda (clauses)
	   (let ((concl-pvars
		  (map (lambda (x)
			 (predicate-form-to-predicate
			  (imp-impnc-all-allnc-form-to-final-conclusion x)))
		       clauses)))
	     (list-transform-positive clauses
	       (lambda (clause)
		 (null?
		  (list-transform-positive
		      (imp-impnc-form-to-premises
		       (all-allnc-form-to-final-kernel clause))
		    (lambda (prem)
		      (let ((concl (imp-impnc-all-allnc-form-to-final-conclusion
				    prem)))
			(and (predicate-form? concl)
			     (member (predicate-form-to-predicate concl)
				     concl-pvars))))))))))))
    (do ((nullary-clauses-and-rest-clauses
	  (list '() clauses-with-idpc-pvars)
	  (let* ((nullary-clauses (car nullary-clauses-and-rest-clauses))
		 (rest-clauses (cadr nullary-clauses-and-rest-clauses))
		 (clauses-wo-rec-calls-for-concl-pvars
		  (clauses-to-clauses-wo-rec-calls-for-concl-pvars
		   rest-clauses))
		 (safe-pvars
		  (map (lambda (x)
			 (predicate-form-to-predicate
			  (imp-impnc-all-allnc-form-to-final-conclusion x)))
		       clauses-wo-rec-calls-for-concl-pvars))
		 (safe-clauses
		  (list-transform-positive rest-clauses
		    (lambda (x)
		      (member
		       (predicate-form-to-predicate
			(imp-impnc-all-allnc-form-to-final-conclusion x))
		       safe-pvars)))))
	    (if (null? safe-clauses)
		(begin
		  (set! COMMENT-FLAG OLD-COMMENT-FLAG)
		  (apply
		   myerror
		   "clauses-with-idpc-pvars-to-nullary-clauses"
		   "nullary clause missing in clauses"
		   rest-clauses)))
	    (list (append nullary-clauses clauses-wo-rec-calls-for-concl-pvars)
		  (set-minus rest-clauses safe-clauses)))))
	((null? (cadr nullary-clauses-and-rest-clauses))
	 (car nullary-clauses-and-rest-clauses)))))

;; IMR is created by calling add-mr-ids for a known idpc-name I.
;; add-mr-ids needs real-and-formula-to-mr-formula-for-mr-clauses as
;; auxiliary function.

(define (add-mr-ids idpc-name)
  (set! OLD-COMMENT-FLAG COMMENT-FLAG)
  (set! COMMENT-FLAG #f)
  (let* ((idpc-pvars (idpredconst-name-to-pvars idpc-name))
	 (idpc-tvars (map PVAR-TO-TVAR idpc-pvars))
	 (idpc-names (idpredconst-name-to-simidpc-names idpc-name))
	 (clauses-with-idpc-pvars
	  (apply append (map idpredconst-name-to-clauses idpc-names)))
	 (et-tvars (set-minus (apply union (map (lambda (x)
						  (type-to-tvars
						   (formula-to-et-type x)))
						clauses-with-idpc-pvars))
			      idpc-tvars))
	 (alg-names (map idpredconst-name-to-alg-name idpc-names))
	 (identity? (and (= 1 (length alg-names))
			 (string? (car alg-names))
			 (string=? "identity" (car alg-names))))
	 (typed-constr-names
	  (if (not identity?)
	      (apply append (map alg-name-to-typed-constr-names alg-names))))
	 (constr-names
	  (if (not identity?)
	      (map typed-constr-name-to-name typed-constr-names)))
	 (alg-tvars
	  (if (not identity?) (alg-name-to-tvars (car alg-names))))
	 (tsubst (if (not identity?) (map list alg-tvars et-tvars)))
	 (constrs
	  (if (not identity?)
	      (map (lambda (name)
		     (let ((constr (constr-name-to-constr name '())))
		       (const-substitute constr tsubst #f)))
		   constr-names)))
	 (constr-terms
	  (if (not identity?) (map make-term-in-const-form constrs)))
	 (algs
	  (if (not identity?)
	      (map (lambda (alg-name) (apply make-alg alg-name et-tvars))
		   alg-names)))
	 (idpc-pvar-to-mr-idpc-arity-alist
	  (if (not identity?)
	      (map (lambda (idpc-pvar alg)
		     (list idpc-pvar
			   (apply make-arity
				  alg (arity-to-types
				       (predicate-to-arity idpc-pvar)))))
		   idpc-pvars algs)
	      (list (list (car idpc-pvars)
			  (apply make-arity
				 (arrow-form-to-arg-type
				  (formula-to-et-type
				   (car clauses-with-idpc-pvars)))
				 (arity-to-types
				  (predicate-to-arity (car idpc-pvars))))))))
	 (pvar-to-mr-pvar ;local pvar-to-mr-pvar, special for idpc-pvars
	  (let ((assoc-list '()))
	    (lambda (pvar)
	      (let ((info (assoc pvar assoc-list)))
		(if
		 info
		 (cadr info)
		 (let* ((mr-idpc-arity
			 (if (member pvar idpc-pvars)
			     (cadr (assoc pvar
					  idpc-pvar-to-mr-idpc-arity-alist))
			     (apply make-arity
				    (PVAR-TO-TVAR pvar)
				    (arity-to-types
				     (predicate-to-arity pvar)))))
			(mr-idpc-pvar
			 (if (member pvar idpc-pvars)
			     (arity-to-new-harrop-pvar mr-idpc-arity)
			     (PVAR-TO-MR-PVAR pvar))))
		   (set! assoc-list
			 (cons (list pvar mr-idpc-pvar) assoc-list))
		   mr-idpc-pvar))))))
	 (param-pvars (idpredconst-name-to-param-pvars idpc-name))
	 (et-tvars-of-param-pvars (map PVAR-TO-TVAR param-pvars))
	 (mr-et-tvars (list-transform-positive et-tvars
			(lambda (tvar)
			  (member tvar et-tvars-of-param-pvars))))
	 (mr-clauses-with-mr-idpc-pvars
	  (if (not identity?)
	      (map (lambda (constr-term clause-with-idpc-pvars)
		     (real-and-formula-to-mr-formula-for-mr-clauses
		      constr-term clause-with-idpc-pvars
		      mr-et-tvars idpc-pvars pvar-to-mr-pvar))
		   constr-terms clauses-with-idpc-pvars)
	      (let* ((et-tvar (car et-tvars))
		     (var (type-to-new-partial-var et-tvar))
		     (real (make-term-in-abst-form
			    var (make-term-in-var-form var))))
		(list (nf (real-and-formula-to-mr-formula-for-mr-clauses
			   real (car clauses-with-idpc-pvars)
			   mr-et-tvars idpc-pvars pvar-to-mr-pvar))))))
	 (mr-idpc-names (map (lambda (name) (string-append name "MR"))
			     idpc-names))
	 (arities (map cadr idpc-pvar-to-mr-idpc-arity-alist))
	 (mr-idpc-names-with-arities (map list mr-idpc-names arities))
	 (mr-idpc-pvars (map pvar-to-mr-pvar idpc-pvars))
	 (mr-idpc-tvars (map PVAR-TO-TVAR mr-idpc-pvars))
	 (clauses-with-names
	  (apply union
		 (map idpredconst-name-to-clauses-with-names idpc-names)))
	 (opt-names (map cdr clauses-with-names))
	 (opt-mr-clause-names
	  (map (lambda (x) (if (and (pair? x) (string? (car x)))
			       (list (string-append (car x) "MR"))
			       '()))
	       opt-names)))
    (add-ids-aux mr-idpc-names-with-arities
		 mr-clauses-with-mr-idpc-pvars
		 mr-idpc-pvars
		 mr-idpc-tvars
		 opt-mr-clause-names)))

(define (formula-to-et-type-for-mr-clauses
	 formula mr-et-tvars idpc-pvars pvar-to-mr-pvar)
  (case (tag formula)
    ((atom) (make-tconst "nulltype"))
    ((predicate)
     (let ((pred (predicate-form-to-predicate formula)))
       (cond ((pvar-form? pred)
	      (if (or (member (PVAR-TO-TVAR pred) mr-et-tvars)
		      (member pred idpc-pvars))
		  (car (arity-to-types (predicate-to-arity
					(pvar-to-mr-pvar pred))))
		  (make-tconst "nulltype")))
	     ((predconst-form? pred)
	      (if (string=? "Total" (predconst-to-name pred))
		  (car (arity-to-types (predconst-to-arity pred)))
		  (make-tconst "nulltype")))
	     ((idpredconst-form? pred)
	      (idpredconst-to-et-type-for-mr-clauses
	       pred mr-et-tvars idpc-pvars pvar-to-mr-pvar))
	     (else (myerror "formula-to-et-type-for-mr-clauses"
			    "predicate expected" pred)))))
    ((imp) (make-arrow-et
	    (formula-to-et-type-for-mr-clauses
	     (imp-form-to-premise formula)
	     mr-et-tvars idpc-pvars pvar-to-mr-pvar)
	    (formula-to-et-type-for-mr-clauses
	     (imp-form-to-conclusion formula)
	     mr-et-tvars idpc-pvars pvar-to-mr-pvar)))
    ((impnc) (formula-to-et-type-for-mr-clauses
	      (impnc-form-to-conclusion formula)
	      mr-et-tvars idpc-pvars pvar-to-mr-pvar))
    ((and) (make-star-et
	    (formula-to-et-type-for-mr-clauses
	     (and-form-to-left formula)
	     mr-et-tvars idpc-pvars pvar-to-mr-pvar)
	    (formula-to-et-type-for-mr-clauses
	     (and-form-to-right formula)
	     mr-et-tvars idpc-pvars pvar-to-mr-pvar)))
    ((all) (make-arrow-et
	    (var-to-type (all-form-to-var formula))
	    (formula-to-et-type-for-mr-clauses
	     (all-form-to-kernel formula)
	     mr-et-tvars idpc-pvars pvar-to-mr-pvar)))
    ((ex) (make-star-et
	   (var-to-type (ex-form-to-var formula))
	   (formula-to-et-type-for-mr-clauses
	    (ex-form-to-kernel formula)
	    mr-et-tvars idpc-pvars pvar-to-mr-pvar)))
    ((allnc) (formula-to-et-type-for-mr-clauses
	      (allnc-form-to-kernel formula)
	      mr-et-tvars idpc-pvars pvar-to-mr-pvar))
    ((exca excl excu) (formula-to-et-type-for-mr-clauses
		       (unfold-formula formula)
		       mr-et-tvars idpc-pvars pvar-to-mr-pvar))
    (else (myerror "formula-to-et-type-for-mr-clauses" "formula expected"
		   formula))))

(define (idpredconst-to-et-type-for-mr-clauses
	 idpc mr-et-tvars idpc-pvars pvar-to-mr-pvar)
  (let* ((name (idpredconst-to-name idpc))
	 (opt-alg-name (idpredconst-name-to-opt-alg-name name)))
    (if
     (null? opt-alg-name)
     (make-tconst "nulltype")
     (let* ((string (car opt-alg-name))
	    (types (idpredconst-to-types idpc))
	    (cterms (idpredconst-to-cterms idpc))
	    (tvars (idpredconst-name-to-tvars name))
	    (local-idpc-pvars (idpredconst-name-to-pvars name))
	    (param-pvars (idpredconst-name-to-param-pvars name))
	    (names (idpredconst-name-to-simidpc-names name))
	    (clauses-with-names
	     (apply append (map idpredconst-name-to-clauses-with-names names)))
	    (clauses (map car clauses-with-names))
	    (et-types (map formula-to-et-type clauses))
	    (local-idpc-tvars (map PVAR-TO-TVAR local-idpc-pvars))
	    (et-tvars (set-minus (apply union (map type-to-tvars et-types))
				 local-idpc-tvars))
	    (relevant-types (do ((l1 tvars (cdr l1))
				 (l2 types (cdr l2))
				 (res '() (let ((tvar (car l1))
						(type (car l2)))
					    (if (member tvar et-tvars)
						(cons type res)
						res))))
				((null? l2) (reverse res))))
	    (relevant-cterm-types
	     (do ((l1 param-pvars (cdr l1))
		  (l2 cterms (cdr l2))
		  (res '() (let* ((pvar (car l1))
				  (cterm (car l2))
				  (formula (cterm-to-formula cterm))
				  (cterm-et-type
				   (formula-to-et-type-for-mr-clauses
				    formula
				    mr-et-tvars idpc-pvars pvar-to-mr-pvar)))
			     (if (and (pvar-with-positive-content? pvar)
				      (member (PVAR-TO-TVAR pvar) et-tvars))
				 (cons cterm-et-type res)
				 res))))
		 ((null? l1) (reverse res)))))
       (if ;string is an alg-name
	(not (string=? "identity" string))
					;replace nulltype by unit in
					;relevant-cterm-types
	(apply make-alg
	       string
	       (append relevant-types
		       (map (lambda (x)
			      (if (equal? x (make-tconst "nulltype"))
				  (make-alg "unit")
				  x))
			    relevant-cterm-types)))
	(if (member (make-tconst "nulltype") relevant-cterm-types)
	    (make-tconst "nulltype")
	    (let ((relevant-types-and-cterm-types
		   (append relevant-types relevant-cterm-types)))
	      (if (null? relevant-types-and-cterm-types)
		  (myerror "idpredconst-to-et-type"
			   "empty relevant-types-and-cterm-types"
			   idpc)
		  (car relevant-types-and-cterm-types)))))))))

;; real-and-formula-to-mr-formula-for-mr-clauses is similar to
;; real-and-formula-to-mr-formula-aux .  The difference is in the
;; usage of the local pvar-to-mr-pvar (with special results for
;; idpc-pvars) and formula-to-et-type-for-mr-clauses .  Moved here
;; since they will be needed in axiom.scm

(define (real-and-formula-to-mr-formula real formula)
  (cond
   ((eq? 'eps real)
    (if
     (not (formula-of-nulltype? formula))
     (myerror "real-and-formula-to-mr-formula"
	      "n.c. formula expected" formula)
     (begin
       (comment
	"warning: real-and-formula-to-mr-formula superfluous for n.c. formula "
	(formula-to-string formula))
       formula)))
   ((and (term-form? real)
	 (equal? (term-to-type real) (formula-to-et-type formula)))
    (real-and-formula-to-mr-formula-aux real formula))
   (else (myerror "real-and-formula-to-mr-formula" "equal types expected"
		  (if (term-form? real)
		      (type-to-string (term-to-type real))
		      real)
		  (formula-to-et-type formula)))))

;; Test
;; (real-and-formula-to-mr-formula 'eps (pf "Pvar^"))
;; (real-and-formula-to-mr-formula 'eps (pf "Pvar"))

(define (real-and-formula-to-mr-formula-aux real formula)
  (case (tag formula)
    ((atom) formula) ;should be obsolete once all calls with 'eps are removed
    ((predicate)
     (let ((pred (predicate-form-to-predicate formula))
	   (args (predicate-form-to-args formula)))
       (cond
	((pvar-form? pred)
	 (if (pvar-with-positive-content? pred)
	     (apply make-predicate-formula (PVAR-TO-MR-PVAR pred) real args)
	     formula))
	((predconst-form? pred)
	 (if (string=? "Total" (predconst-to-name pred))
	     (let* ((arg (car args))
		    (type (term-to-type arg)))
	       (cond ((tvar-form? type) (make-totalmr real arg))
		     ((or (alg-form? type)
			  (arrow-form? type)
			  (star-form? type))
		      (real-and-formula-to-mr-formula-aux
		       real (unfold-formula formula)))
		     (else (myerror
			    "real-and-formula-to-mr-formula-aux"
			    "type of tvar-, alg-, arrow- or star-form expected"
			    type))))
	     formula))
	((idpredconst-form? pred)
	 (let* ((idpc-name (idpredconst-to-name pred))
		(clauses (idpredconst-name-to-clauses idpc-name))
		(opt-alg-name (idpredconst-name-to-opt-alg-name idpc-name))
		(alg-name (if (pair? opt-alg-name) ;c.r.idpc
			      (car opt-alg-name)
			      (myerror "real-and-formula-to-mr-formula-aux"
				       "alg name expected for idpredconst"
				       formula))))
	   (apply make-predicate-formula
		  (idpredconst-to-mr-idpredconst pred) real args)))
	(else ;witnessing idpc like "EvenMR"
	 formula))))
    ((imp)
     (let* ((prem (imp-form-to-premise formula))
	    (type1 (formula-to-et-type prem))
	    (concl (imp-form-to-conclusion formula)))
       (if (nulltype? type1)
	   (make-imp prem (real-and-formula-to-mr-formula-aux real concl))
	   (let* ((var (type-to-new-partial-var type1))
		  (varterm (make-term-in-var-form var))
		  (appterm (make-term-in-app-form real varterm)))
	     (make-all var (make-imp (real-and-formula-to-mr-formula-aux
				      varterm prem)
				     (real-and-formula-to-mr-formula-aux
				      appterm concl)))))))
    ((impnc)
     (let ((prem (imp-form-to-premise formula))
	   (concl (imp-form-to-conclusion formula)))
       (make-imp prem (real-and-formula-to-mr-formula-aux real concl))))
    
    ((and)
     (let ((left (and-form-to-left formula))
	   (right (and-form-to-right formula)))
       (cond
	((formula-of-nulltype? left)
	 (make-and left (real-and-formula-to-mr-formula-aux real right)))
	((formula-of-nulltype? right)
	 (make-and (real-and-formula-to-mr-formula-aux real left) right))
	(else ;neither type1 nor type2 equals nulltype
	 (let ((term1 (make-term-in-lcomp-form real))
	       (term2 (make-term-in-rcomp-form real)))
	   (make-and (real-and-formula-to-mr-formula-aux term1 left)
		     (real-and-formula-to-mr-formula-aux term2 right)))))))
    ((all)
     (let* ((var (all-form-to-var formula))
	    (kernel (all-form-to-kernel formula))
	    (varterm (make-term-in-var-form var))
	    (appterm (make-term-in-app-form real varterm)))
       (make-all var (real-and-formula-to-mr-formula-aux appterm kernel))))
    ((allnc)
     (let ((var (allnc-form-to-var formula))
	   (kernel (allnc-form-to-kernel formula)))
       (make-all var (real-and-formula-to-mr-formula-aux real kernel))))
    ((ex)
     (let ((var (ex-form-to-var formula))
	   (kernel (ex-form-to-kernel formula)))
       (if (formula-of-nulltype? kernel)
	   (formula-subst kernel var real)
	   (let ((term1 (make-term-in-lcomp-form real))
		 (term2 (make-term-in-rcomp-form real)))
	     (real-and-formula-to-mr-formula-aux
	      term2 (formula-subst kernel var term1))))))
    ((exca excl excu)
     (real-and-formula-to-mr-formula-aux real (unfold-formula formula)))
    (else (myerror "real-and-formula-to-mr-formula-aux" "formula expected"
		   formula))))

(define (real-and-formula-to-mr-formula-for-mr-clauses
	 real formula mr-et-tvars idpc-pvars pvar-to-mr-pvar)
  (case (tag formula)
    ((atom)
     (myerror "real-and-formula-to-mr-formula-for-mr-clauses"
	      "c.r. formula expected"
	      formula))
    ((predicate)
     (let ((pred (predicate-form-to-predicate formula))
	   (args (predicate-form-to-args formula)))
       (cond
	((pvar-form? pred)
	 (if ;idpc-pvar or cr-param-pvar
	  (or (member pred idpc-pvars)
	      (member (PVAR-TO-TVAR pred) mr-et-tvars))
	  (apply make-predicate-formula (pvar-to-mr-pvar pred) real args)
	  (myerror "real-and-formula-to-mr-formula-for-mr-clauses"
		   "c.r. pvar expected"
		   formula)))
	((predconst-form? pred)
	 (if (string=? "Total" (predconst-to-name pred))
	     (make-totalmr real (car args))
	     (myerror "real-and-formula-to-mr-formula-for-mr-clauses"
		      "c.r. predicate constant with mr version expected"
		      formula)))
	((idpredconst-form? pred)
	 (let* ((idpc-name (idpredconst-to-name pred))
		(clauses (idpredconst-name-to-clauses idpc-name)))
	   (if (pair? (idpredconst-name-to-opt-alg-name idpc-name)) ;c.r.idpc
	       (apply make-predicate-formula
		      (idpredconst-to-mr-idpredconst-for-mr-clauses
		       pred mr-et-tvars idpc-pvars pvar-to-mr-pvar)
		      real args)
	       (myerror "real-and-formula-to-mr-formula-for-mr-clauses"
			"c.r. idpredconst expected" formula))))
	(else (myerror "real-and-formula-to-mr-formula-for-mr-clauses"
		       "c.r. predicate expected" formula)))))
    ((imp)
     (let* ((prem (imp-form-to-premise formula))
	    (concl (imp-form-to-conclusion formula)))
       (if (formula-of-nulltype? prem)
	   (make-imp prem
		     (real-and-formula-to-mr-formula-for-mr-clauses
		      real concl mr-et-tvars idpc-pvars pvar-to-mr-pvar))
	   (let* ((type1 (formula-to-et-type-for-mr-clauses
			  prem mr-et-tvars idpc-pvars pvar-to-mr-pvar))
		  (var (type-to-new-partial-var type1))
		  (varterm (make-term-in-var-form var))
		  (appterm (make-term-in-app-form real varterm)))
	     (make-all
	      var (make-imp
		   (real-and-formula-to-mr-formula-for-mr-clauses
		    varterm prem mr-et-tvars idpc-pvars pvar-to-mr-pvar)
		   (real-and-formula-to-mr-formula-for-mr-clauses
		    appterm concl mr-et-tvars idpc-pvars pvar-to-mr-pvar)))))))
    ((impnc)
     (let* ((prem (impnc-form-to-premise formula))
	    (concl (impnc-form-to-conclusion formula)))
       (if (formula-of-nulltype? prem)
	   (make-imp prem
		     (real-and-formula-to-mr-formula-for-mr-clauses
		      real concl mr-et-tvars idpc-pvars pvar-to-mr-pvar))
	   (make-impnc prem
		       (real-and-formula-to-mr-formula-for-mr-clauses
			real concl mr-et-tvars idpc-pvars pvar-to-mr-pvar)))))
    ((and)
     (let* ((left (and-form-to-left formula))
	    (type1 (formula-to-et-type-for-mr-clauses
		    left mr-et-tvars idpc-pvars pvar-to-mr-pvar))
	    (right (and-form-to-right formula))
	    (type2 (formula-to-et-type-for-mr-clauses
		    right mr-et-tvars idpc-pvars pvar-to-mr-pvar)))
       (cond
	((and (not (nulltype? type1)) (nulltype? type2))
	 (make-and (real-and-formula-to-mr-formula-for-mr-clauses
		    real left mr-et-tvars idpc-pvars pvar-to-mr-pvar)
		   right))
	((and (nulltype? type1) (not (nulltype? type2)))
	 (make-and left
		   (real-and-formula-to-mr-formula-for-mr-clauses
		    real right mr-et-tvars idpc-pvars pvar-to-mr-pvar)))
	((and (not (nulltype? type1)) (not (nulltype? type2)))
	 (let*  ((term1 (make-term-in-lcomp-form real))
		 (term2 (make-term-in-rcomp-form real)))
	   (make-and (real-and-formula-to-mr-formula-for-mr-clauses
		      term1 left mr-et-tvars idpc-pvars pvar-to-mr-pvar)
		     (real-and-formula-to-mr-formula-for-mr-clauses
		      term2 right mr-et-tvars idpc-pvars pvar-to-mr-pvar))))
	(else (myerror "real-and-formula-to-mr-formula-for-mr-clauses"
		       "c.r. conjunction expected" formula)))))
    ((all)
     (let* ((var (all-form-to-var formula))
	    (kernel (all-form-to-kernel formula))
	    (type (formula-to-et-type-for-mr-clauses
		   kernel mr-et-tvars idpc-pvars pvar-to-mr-pvar)))
       (if (nulltype? type)
	   (myerror "real-and-formula-to-mr-formula-for-mr-clauses"
		    "c.r. all formula expected" formula)
	   (let* ((varterm (make-term-in-var-form var))
		  (appterm (make-term-in-app-form real varterm)))
	     (make-all var (real-and-formula-to-mr-formula-for-mr-clauses
			    appterm kernel
			    mr-et-tvars idpc-pvars pvar-to-mr-pvar))))))
    ((allnc)
     (let* ((var (allnc-form-to-var formula))
	    (kernel (allnc-form-to-kernel formula))
	    (type (formula-to-et-type-for-mr-clauses
		   kernel mr-et-tvars idpc-pvars pvar-to-mr-pvar)))
       (if (nulltype? type)
	   (myerror "real-and-formula-to-mr-formula-for-mr-clauses"
		    "c.r. allnc formula expected" formula)
	   (make-all var (real-and-formula-to-mr-formula-for-mr-clauses
			  real kernel
			  mr-et-tvars idpc-pvars pvar-to-mr-pvar)))))
    ((ex)
     (let* ((var (ex-form-to-var formula))
	    (kernel (ex-form-to-kernel formula))
	    (type (formula-to-et-type-for-mr-clauses
		   kernel mr-et-tvars idpc-pvars pvar-to-mr-pvar)))
       (if (nulltype? type)
	   (formula-subst kernel var real)
	   (let ((term1 (make-term-in-lcomp-form real))
		 (term2 (make-term-in-rcomp-form real)))
	     (real-and-formula-to-mr-formula-for-mr-clauses
	      term2 (formula-subst kernel var term1)
	      mr-et-tvars idpc-pvars pvar-to-mr-pvar)))))
    ((exca excl excu)
     (real-and-formula-to-mr-formula-for-mr-clauses
      real (unfold-formula formula) mr-et-tvars idpc-pvars pvar-to-mr-pvar))
    (else (myerror "real-and-formula-to-mr-formula-for-mr-clauses"
		   "c.r. formula expected" formula))))

;; We must require a sharp substitution for c.r. param pvars Y in a c.r.
;; idpc I if tau(Y) is free in tau of any of the clauses.  Reason: Y^r
;; in I^r needs a cterm of arity (tau(A), rhos) if Y |-> {xs|A} in I.
;; Similarly: a param-pvar Y in a relevant occurrence of an aconst
;; with tau(Y) in the type of its uninst formula must be sharply
;; substituted as well, to avoid nullterm in eterms.

(define (idpredconst-to-mr-idpredconst-for-mr-clauses
	 idpc mr-et-tvars idpc-pvars pvar-to-mr-pvar)
  (let* ((idpc-name (idpredconst-to-name idpc))
	 (types (idpredconst-to-types idpc))
	 (cterms (idpredconst-to-cterms idpc))
	 (mr-idpc-name (string-append idpc-name "MR"))
	 (tsubst (idpredconst-name-and-types-to-tsubst idpc-name types))
	 (idpc-names (idpredconst-name-to-simidpc-names idpc-name))
	 (clauses (apply append (map idpredconst-name-to-clauses idpc-names)))
	 (clause-et-types (map formula-to-et-type clauses))
	 (clause-et-tvars (apply union (map type-to-tvars clause-et-types)))
	 (param-pvars (idpredconst-name-to-param-pvars idpc-name))
	 (et-tvars-of-param-pvars (map PVAR-TO-TVAR param-pvars))
	 (local-mr-et-tvars
	  (list-transform-positive clause-et-tvars
	    (lambda (tvar) (member tvar et-tvars-of-param-pvars))))
	 (pvar-et-type-alist
	  (map (lambda (pvar cterm)
		 (list pvar (formula-to-et-type-for-mr-clauses
			     (cterm-to-formula cterm)
			     mr-et-tvars idpc-pvars pvar-to-mr-pvar)))
	       param-pvars cterms))
	 (relevant-pvar-et-type-alist
	  (list-transform-positive pvar-et-type-alist
	    (lambda (x) (member (PVAR-TO-TVAR (car x)) local-mr-et-tvars))))
	 (et-tsubst (map (lambda (x)
			   (let ((pvar (car x))
				 (et-type (cadr x)))
			     (list (PVAR-TO-TVAR pvar) et-type)))
			 relevant-pvar-et-type-alist))
	 (orig-and-mr-tvars (idpredconst-name-to-tvars mr-idpc-name))
	 (orig-and-mr-types (map (lambda (tvar)
				   (let ((info1 (assoc tvar tsubst))
					 (info2 (assoc tvar et-tsubst)))
				     (cond (info1 (cadr info1))
					   (info2 (cadr info2))
					   (else tvar))))
				 orig-and-mr-tvars))
	 (orig-and-mr-pvars (idpredconst-name-to-param-pvars mr-idpc-name))
	 (pvar-cterm-alist (map list param-pvars cterms)) ;not a psubst
	 (mr-pvar-cterm-alist
	  (map
	   (lambda (pvar cterm)
	     (let ((vars (cterm-to-vars cterm))
		   (formula (cterm-to-formula cterm)))
	       (if ;relevant param-pvar
		(member (PVAR-TO-TVAR pvar) local-mr-et-tvars)
		(if ;n.c. cterm
		 (formula-of-nulltype? formula)
		 (myerror
		  "idpredconst-to-mr-idpredconst" "c.r. formula expected"
		  formula "for relevant param-pvar" pvar)
					;else c.r. cterm
		 (let* ((et-type
			 (formula-to-et-type-for-mr-clauses
			  formula mr-et-tvars idpc-pvars pvar-to-mr-pvar))
			(mr-var (type-to-new-partial-var et-type))
			(mr-vars (cons mr-var vars))
			(mr-formula
			 (idpredconst-to-mr-idpredconst-for-mr-clauses
			  (make-term-in-var-form mr-var) formula
			  mr-et-tvars idpc-pvars pvar-to-mr-pvar)))
		   (list
		    (PVAR-TO-MR-PVAR pvar)
		    (apply make-cterm (append mr-vars (list mr-formula))))))
					;else irrelevant param-pvar.  Not used
		(list pvar cterm))))
	   param-pvars cterms))
	 (orig-and-mr-cterms
	  (map (lambda (pvar)
		 (let ((info1 (assoc pvar pvar-cterm-alist))
		       (info2 (assoc pvar mr-pvar-cterm-alist)))
		   (cond (info1 (cadr info1))
			 (info2 (cadr info2))
			 (else (myerror
				"idpredconst-to-mr-idpredconst-for-mr-clauses"
				"unexpected orig-and-mr-pvars"
				orig-and-mr-pvars)))))
	       orig-and-mr-pvars)))
    (make-idpredconst mr-idpc-name orig-and-mr-types orig-and-mr-cterms)))

(define (alg-and-cterms-to-rtotality-idpredconst alg cterms)
  (let* ((alg-name (alg-form-to-name alg))
	 (types (alg-form-to-types alg))
	 (idpredconst-name (alg-name-to-rtotality-idpredconst-name alg-name))
	 (param-pvars (idpredconst-name-to-param-pvars idpredconst-name)))
    (if (not (= (length param-pvars) (length cterms)))
	(apply myerror "alg-and-cterms-to-rtotality-idpredconst"
	       "param-pvars and cterms differ in length" cterms))
    (idpredconst-name-and-types-and-cterms-to-idpredconst ;involves some tests
     idpredconst-name types cterms)))

(define (alg-name-to-totality-clauses-and-pvars alg-name)
  (let* ((alg-names (alg-name-to-simalg-names alg-name))
	 (tvars (alg-name-to-tvars alg-name))
	 (algs (map (lambda (name) (apply make-alg name tvars))
		    alg-names))
	 (typed-constr-names
	  (apply append (map alg-name-to-typed-constr-names alg-names)))
	 (constr-names (map car typed-constr-names))
	 (constr-types (map typed-constr-name-to-type typed-constr-names))
	 (totality-idpc-names
	  (map alg-name-to-totality-idpredconst-name alg-names))
	 (param-arg-types-list
	  (map constr-type-to-constr-param-types constr-types))
	 (rec-arg-types-list
	  (map (lambda (x y)
		 (list-tail (arrow-form-to-arg-types x) (length y)))
	       constr-types param-arg-types-list))
	 (param-vars-list (map (lambda (l) (map type-to-new-partial-var l))
			       param-arg-types-list))
	 (rec-vars-list (map (lambda (l) (map type-to-new-partial-var l))
			     rec-arg-types-list))
	 (param-varterms-list (map (lambda (l) (map make-term-in-var-form l))
				   param-vars-list))
	 (rec-varterms-list (map (lambda (l) (map make-term-in-var-form l))
				 rec-vars-list))
	 (param-totality-prems-list
	  (map (lambda (param-varterms)
		 (map term-to-totality-formula param-varterms))
	       param-varterms-list))
	 (alg-to-pvar-alist
	  (do ((l algs (cdr l))
	       (res '() (let* ((alg (car l))
			       (alg-name (alg-form-to-name alg))
			       (totality-idpc-name
				(alg-name-to-totality-idpredconst-name
				 alg-name))
			       (pvar (make-pvar (make-arity alg)
						(+ 1 MAXPVARINDEX)
						h-deg-zero n-deg-zero
						"")))
			  (cons (list alg pvar) res))))
	      ((null? l) (reverse res))))
	 (rec-totality-prems-list
	  (map (lambda (rec-arg-types rec-varterms)
		 (map (lambda (rec-arg-type rec-varterm)
			(let* ((arg-types
				(arrow-form-to-arg-types rec-arg-type))
			       (val-type
				(arrow-form-to-final-val-type rec-arg-type))
			       (vars (map type-to-new-partial-var arg-types))
			       (varterms (map make-term-in-var-form vars))
			       (totality-prems
				(map term-to-totality-formula varterms))
			       (appterm (apply mk-term-in-app-form
					       rec-varterm varterms))
			       (alg (arrow-form-to-final-val-type
				     rec-arg-type))
			       (concl (make-predicate-formula
				       (cadr (assoc alg alg-to-pvar-alist))
				       appterm)))
			  (apply
			   mk-allnc
			   (append vars
				   (list (apply mk-imp
						(append totality-prems
							(list concl))))))))
		      rec-arg-types rec-varterms))
	       rec-arg-types-list rec-varterms-list))
	 (constr-list (map constr-name-to-constr constr-names))
	 (constr-appterm-list
	  (map (lambda (constr param-varterms rec-varterms)
		 (apply mk-term-in-app-form
			(append (list (make-term-in-const-form constr))
				param-varterms rec-varterms)))
	       constr-list param-varterms-list rec-varterms-list))
	 (concl-list (map (lambda (constr-appterm)
			    (make-predicate-formula
			     (cadr (assoc (term-to-type constr-appterm)
					  alg-to-pvar-alist))
			     constr-appterm))
			  constr-appterm-list)))
					;return totality clauses and pvars
    (list
     (map (lambda (param-vars
		   rec-vars
		   param-totality-prems
		   rec-totality-prems
		   concl)
	    (apply mk-allnc
		   (append param-vars rec-vars
			   (list (apply mk-imp (append param-totality-prems
						       rec-totality-prems
						       (list concl)))))))
	  param-vars-list
	  rec-vars-list
	  param-totality-prems-list
	  rec-totality-prems-list
	  concl-list)
     (map cadr alg-to-pvar-alist))))

(define (add-totality alg-name)
  (if (not (assoc alg-name ALGEBRAS))
      (myerror "add-totality" "alg-name expected" alg-name))
  (set! OLD-COMMENT-FLAG COMMENT-FLAG)
  (set! COMMENT-FLAG #f)
  (let* ((alg-names (alg-name-to-simalg-names alg-name))
	 (tvars (alg-name-to-tvars alg-name))
	 (algs (map (lambda (name) (apply make-alg name tvars)) alg-names))
	 (idpc-arities (map make-arity algs))
	 (idpc-pvars (map arity-to-new-general-pvar idpc-arities))
	 (alg-to-idpc-pvar-alist (map list algs idpc-pvars))
	 (typed-constr-names
	  (apply append (map alg-name-to-typed-constr-names alg-names)))
	 (constr-names (map car typed-constr-names))
	 (constrs (map constr-name-to-constr constr-names))
	 (clauses-with-idpc-pvars
	  (map (lambda (constr) (term-and-alist-to-totality-formula
				 (make-term-in-const-form constr)
				 alg-to-idpc-pvar-alist))
	       constrs))
	 (totality-idpc-names
	  (map alg-name-to-totality-idpredconst-name alg-names))
	 (idpc-names-with-arities-and-opt-alg-names
	  (map list totality-idpc-names idpc-arities alg-names))
	 (idpc-tvars (map PVAR-TO-TVAR idpc-pvars))
	 (typed-constr-names-list
	  (map alg-name-to-typed-constr-names alg-names))
	 (constr-names-list (map (lambda (typed-constr-names)
	 			   (map car typed-constr-names))
	 			 typed-constr-names-list))
	 (clause-names-list
	  (map (lambda (totality-idpc-name constr-names)
		 (map (lambda (constr-name)
			(string-append totality-idpc-name constr-name))
		      constr-names))
	       totality-idpc-names constr-names-list))
	 (opt-names (map list (apply append clause-names-list))))
    (add-ids-aux idpc-names-with-arities-and-opt-alg-names
		 clauses-with-idpc-pvars
		 idpc-pvars
		 idpc-tvars
		 opt-names)))

;; For add-totality we need the following auxiliary functions

(define (alg-name-to-totality-idpredconst-name alg-name)
  (let* ((char-list (string->list alg-name))
	 (capitalized-alg-name
	  (list->string (cons (char-upcase (car char-list)) (cdr char-list)))))
    (string-append "Total" capitalized-alg-name)))

(define (alg-to-totality-idpredconst alg)
  (let* ((alg-name (alg-form-to-name alg))
	 (types (alg-form-to-types alg))
	 (idpredconst-name (alg-name-to-totality-idpredconst-name alg-name)))
    (idpredconst-name-and-types-and-cterms-to-idpredconst
     idpredconst-name types '())))

(define (term-and-alist-to-totality-formula term type-to-pred-alist)
  (let ((type (term-to-type term)))
    (cond
     ((tvar-form? type)
      (let ((info (assoc type type-to-pred-alist)))
	(if info
	    (make-predicate-formula (cadr info) term)
	    (make-total term))))
     ((alg-form? type)
      (let ((info (assoc type type-to-pred-alist)))
	(if
	 info ;idpc-pvar, needed in add-totality for add-ids-aux
	 (make-predicate-formula (cadr info) term)
	 (let* ((types (alg-form-to-types type))
		(alg-to-pvar-alist (list-transform-positive type-to-pred-alist
				     (lambda (item) (alg-form? (car item)))))
		(alist-alg-names (map alg-form-to-name
				      (map car alg-to-pvar-alist)))
		(alg-names-list (map type-to-alg-names types))
		(intersections
		 (map (lambda (alg-names)
			(intersection alist-alg-names alg-names))
		      alg-names-list)))
	   (cond
	    ((apply and-op (map null? intersections))
	     (make-predicate-formula (alg-to-totality-idpredconst type) term))
	    ((apply and-op (map pair? intersections))
	     (let* ((vars (map type-to-new-partial-var types))
		    (varterms (map make-term-in-var-form vars))
		    (prevs (map (lambda (varterm)
				  (term-and-alist-to-totality-formula
				   varterm type-to-pred-alist))
				varterms))
		    (cterms (map make-cterm vars prevs)))
	       (make-predicate-formula
		(alg-and-cterms-to-rtotality-idpredconst type cterms) term)))
	    (else (apply myerror "term-and-alist-to-totality-formula"
			 "not implemented for term" term
			 "and type-to-pred-alist" type-to-pred-alist)))))))
     ((arrow-form? type)
      (let* ((arg-type (arrow-form-to-arg-type type))
	     (var (type-to-new-partial-var arg-type))
	     (varterm (make-term-in-var-form var))
	     (appterm (make-term-in-app-form term varterm))
	     (arg-formula
	      (term-and-alist-to-totality-formula varterm type-to-pred-alist))
	     (val-formula
	      (term-and-alist-to-totality-formula appterm type-to-pred-alist)))
	(make-allnc var (make-imp arg-formula val-formula))))
     ((star-form? type)
      (let ((left (if (term-in-pair-form? term)
		      (term-in-pair-form-to-left term)
		      (make-term-in-lcomp-form term)))
	    (right (if (term-in-pair-form? term)
		       (term-in-pair-form-to-right term)
		       (make-term-in-rcomp-form term))))
	(make-and
	 (term-and-alist-to-totality-formula left type-to-pred-alist)
	 (term-and-alist-to-totality-formula right type-to-pred-alist))))
     (else (myerror "term-and-alist-to-totality-formula" "type expected" type
		    "of term" term)))))

(define (term-to-totality-formula term)
  (term-and-alist-to-totality-formula term '()))

(define (add-rtotality alg-name)
  (if (not (assoc alg-name ALGEBRAS))
      (myerror "add-rtotality" "alg-name expected" alg-name))
  (set! OLD-COMMENT-FLAG COMMENT-FLAG)
  (set! COMMENT-FLAG #f)
  (let* ((alg-names (alg-name-to-simalg-names alg-name))
	 (tvars (alg-name-to-tvars alg-name))
	 (algs (map (lambda (name) (apply make-alg name tvars)) alg-names))
	 (idpc-arities (map make-arity algs))
	 (idpc-pvars (map arity-to-new-general-pvar idpc-arities))
	 (alg-to-idpc-pvar-alist (map list algs idpc-pvars))
	 (arities (map make-arity tvars))
	 (pvars (map arity-to-new-general-pvar arities))
	 (tvar-to-pvar-alist (map list tvars pvars))
	 (typed-constr-names
	  (apply append (map alg-name-to-typed-constr-names alg-names)))
	 (constr-names (map car typed-constr-names))
	 (constrs (map constr-name-to-constr constr-names))
	 (clauses-with-idpc-pvars
	  (map (lambda (constr)
		 (term-and-alist-to-totality-formula
		  (make-term-in-const-form constr)
		  (append alg-to-idpc-pvar-alist tvar-to-pvar-alist)))
	       constrs))
	 (rtotality-idpc-names
	  (map alg-name-to-rtotality-idpredconst-name alg-names))
	 (idpc-names-with-arities-and-opt-alg-names
	  (map list rtotality-idpc-names idpc-arities alg-names))
	 (idpc-tvars (map PVAR-TO-TVAR idpc-pvars))
	 (typed-constr-names-list
	  (map alg-name-to-typed-constr-names alg-names))
	 (constr-names-list (map (lambda (typed-constr-names)
	 			   (map car typed-constr-names))
	 			 typed-constr-names-list))
	 (clause-names-list
	  (map (lambda (rtotality-idpc-name constr-names)
		 (map (lambda (constr-name)
			(string-append rtotality-idpc-name constr-name))
		      constr-names))
	       rtotality-idpc-names constr-names-list))
	 (opt-names (map list (apply append clause-names-list))))
    (add-ids-aux idpc-names-with-arities-and-opt-alg-names
		 clauses-with-idpc-pvars
		 idpc-pvars
		 idpc-tvars
		 opt-names)))

;; add-rtotality should be used for algebras with parameters.  Other
;; totality notions can then be defined via appropriate comprehension
;; terms.  For instance, STotalList was defined in lib/list.scm:

;; (add-ids (list (list "STotalList" (make-arity (py "list alpha")) "nat"))
;; 	 '("STotalList(Nil alpha)" "STotalListNil")
;; 	 '("allnc x^,xs^(
;;              STotalList xs^ -> STotalList(x^ ::xs^))" "STotalListCons"))

;; We could use (RTotalList (cterm (x^) T))xs^ for STotalList xs^.
;; However, STotalList is just convenient.

;; For add-rtotality we need the following auxiliary function

(define (alg-name-to-rtotality-idpredconst-name alg-name)
  (let* ((char-list (string->list alg-name))
	 (capitalized-alg-name
	  (list->string (cons (char-upcase (car char-list)) (cdr char-list)))))
    (string-append "RTotal" capitalized-alg-name)))

;; term-to-unfolded-totality-formula uses
;; alg-name-to-rtotality-idpredconst-name in case alg has parameters.
;; This is needed when normalizing proofs with elim for totality.

(define (term-to-unfolded-totality-formula term)
  (let ((type (term-to-type term)))
    (cond
     ((tvar-form? type) (make-total term))
     ((alg-form? type)
      (let* ((alg-name (alg-form-to-name type))
	     (types (alg-form-to-types type))
	     (idpredconst-name
	      (if (zero? (alg-name-to-arity alg-name))
		  (alg-name-to-totality-idpredconst-name alg-name)
		  (alg-name-to-rtotality-idpredconst-name alg-name)))
	     (cterms (map (lambda (type)
			    (let* ((var (type-to-new-partial-var type))
				   (idpredconst-formula
				    (term-to-unfolded-totality-formula
				     (make-term-in-var-form var))))
			      (make-cterm var idpredconst-formula)))
			  types)))
	(make-predicate-formula
	 (idpredconst-name-and-types-and-cterms-to-idpredconst
	  idpredconst-name types cterms)
	 term)))
     ((arrow-form? type)
      (let* ((arg-type (arrow-form-to-arg-type type))
	     (var (type-to-new-partial-var arg-type))
	     (varterm (make-term-in-var-form var))
	     (appterm (make-term-in-app-form term varterm))
	     (arg-formula (term-to-unfolded-totality-formula varterm))
	     (val-formula (term-to-unfolded-totality-formula appterm)))
	(make-allnc var (make-imp arg-formula val-formula))))
     ((star-form? type)
      (let ((left (if (term-in-pair-form? term)
		      (term-in-pair-form-to-left term)
		      (make-term-in-lcomp-form term)))
	    (right (if (term-in-pair-form? term)
		       (term-in-pair-form-to-right term)
		       (make-term-in-rcomp-form term))))
	(make-and (term-to-unfolded-totality-formula left)
		  (term-to-unfolded-totality-formula right))))
     (else (myerror "term-to-unfolded-totality-formula" "unexpected type" type
		    "of term" term)))))

;; There is no add-stotality for structural totality.  Instead one
;; should use add-ids with the proper clauses for e.g. STotalList.
;; Then one can provide a known alg name (nat in this case).
;; STotalList was defined in lib/list.scm:

;; (add-ids (list (list "STotalList" (make-arity (py "list alpha")) "nat"))
;; 	 '("STotalList(Nil alpha)" "STotalListNil")
;; 	 '("allnc x^,xs^(
;;              STotalList xs^ -> STotalList(x^ ::xs^))" "STotalListCons"))

;; We could use (RTotalList (cterm (x^) T))xs^ for STotalList xs^.
;; However, STotalList is just convenient.

(define (term-to-stotality-formula term)
  (let ((type (term-to-type term)))
    (cond
     ((tvar-form? type) (make-total term))
     ((alg-form? type)
      (if (and (sfinalg? type) (not (finalg? type)))
	  (make-predicate-formula (alg-to-stotality-idpredconst type) term)
	  (make-predicate-formula (alg-to-totality-idpredconst type) term)))
     ((arrow-form? type)
      (let* ((arg-type (arrow-form-to-arg-type type))
	     (var (type-to-new-partial-var arg-type))
	     (varterm (make-term-in-var-form var))
	     (appterm (make-term-in-app-form term varterm))
	     (arg-formula (term-to-stotality-formula varterm))
	     (val-formula (term-to-stotality-formula appterm)))
	(make-allnc var (make-imp arg-formula val-formula))))
     ((star-form? type) ;obsolete.  Use yprod
      (let ((left (if (term-in-pair-form? term)
		      (term-in-pair-form-to-left term)
		      (make-term-in-lcomp-form term)))
	    (right (if (term-in-pair-form? term)
		       (term-in-pair-form-to-right term)
		       (make-term-in-rcomp-form term))))
	(make-and (term-to-stotality-formula left)
		  (term-to-stotality-formula right))))
     (else (myerror "term-to-stotality-formula" "type expected" type)))))

(define (alg-to-stotality-idpredconst alg)
  (let* ((alg-name (alg-form-to-name alg))
	 (types (alg-form-to-types alg))
	 (idpredconst-name (alg-name-to-stotality-idpredconst-name alg-name)))
    (idpredconst-name-and-types-and-cterms-to-idpredconst
     idpredconst-name types '())))

(define (alg-name-to-stotality-idpredconst-name alg-name)
  (let* ((char-list (string->list alg-name))
	 (capitalized-alg-name
	  (list->string (cons (char-upcase (car char-list)) (cdr char-list)))))
    (string-append "STotal" capitalized-alg-name)))

(define (terms-to-mr-totality-formula term1 term2)
  (let ((type (term-to-type term1)))
    (if (not (equal? type (term-to-type term2)))
	(myerror "terms-to-mr-totality-formula"
		 "terms of equal type expected"
		 term1 term2
		 "which have types"
		 type (term-to-type term2)))
    (cond
     ((tvar-form? type) (make-totalmr term1 term2))
     ((alg-form? type)
      (make-predicate-formula
       (alg-to-mr-totality-idpredconst type) term1 term2))
     ((arrow-form? type)
      (let* ((arg-type (arrow-form-to-arg-type type))
	     (var (type-to-new-partial-var arg-type))
	     (varterm (make-term-in-var-form var))
	     (appterm1 (make-term-in-app-form term1 varterm))
	     (appterm2 (make-term-in-app-form term2 varterm))
	     (arg-formula (term-to-totality-formula varterm))
	     (val-formula (terms-to-mr-totality-formula appterm1 appterm2)))
	(make-allnc var (make-imp arg-formula val-formula))))
     ((star-form? type)
      (make-and
       (terms-to-mr-totality-formula (make-term-in-lcomp-form term1)
				     (make-term-in-lcomp-form term2))
       (terms-to-mr-totality-formula (make-term-in-rcomp-form term1)
				     (make-term-in-rcomp-form term2))))
     (else (myerror "terms-to-mr-totality-formula" "type expected" type)))))

(define (alg-to-mr-totality-idpredconst alg)
  (let* ((alg-name (alg-form-to-name alg))
	 (types (alg-form-to-types alg))
	 (idpredconst-name
	  (alg-name-to-mr-totality-idpredconst-name alg-name)))
    (idpredconst-name-and-types-and-cterms-to-idpredconst
     idpredconst-name types '())))

(define (alg-name-to-mr-totality-idpredconst-name alg-name)
  (string-append (alg-name-to-totality-idpredconst-name alg-name) "MR"))

;; (add-var-name "ns" (py "list nat"))
;; (pp (rename-variables (term-to-unfolded-totality-formula (pt "ns^"))))
;; (RTotalList (cterm (n^) TotalNat n^))ns^

;; To do: term-to-unfolded-mr-totality-formula

(define (display-idpc . x)
  (if
   COMMENT-FLAG
   (let ((reduced-ids (if (null? x)
			  IDS
			  (do ((l IDS (cdr l))
			       (res '() (if (member (caar l) x)
					    (cons (car l) res)
					    res)))
			      ((null? l) res)))))
     (for-each
      (lambda (id)
	(let* ((idpc-name (car id))
	       (clauses-with-names
		(idpredconst-name-to-clauses-with-names idpc-name))
	       (clause-names (map cadr clauses-with-names)))
	  (display idpc-name) (newline)
	  (for-each (lambda (cn)
		      (display tab)
		      (display cn) (display ":")
		      (display tab)
		      (pp cn))
		    clause-names)))
      reduced-ids))))

;; In remove-idpc-name we assume that a user provided new alg-name for
;; witnesses for an idpredconst I is algI.

(define (remove-idpc-name . strings)
  (define (rin1 idpc-name)
    (if
     (assoc idpc-name IDS)
     (let* ((simidpc-names (idpredconst-name-to-simidpc-names idpc-name))
	    (opt-alg-names
	     (map idpredconst-name-to-opt-alg-name simidpc-names))
	    (alg-names (apply append opt-alg-names))
	    (user-provided-new-alg-names ;for instance "algEv" "algOd"
	     (list-transform-positive alg-names
	       (lambda (alg-name)
		 (and (initial-substring? "alg" alg-name)
		      (member (substring alg-name
					 (string-length "alg")
					 (string-length alg-name))
			      simidpc-names)))))
	    (affected-alg-names ;"algEv" "algOd" "nbeEv" "nbeOd"
	     (append user-provided-new-alg-names
		     (map idpredconst-name-to-nbe-alg-name simidpc-names)))
	    (affected-constr-names
	     (list-transform-positive (map car CONSTRUCTORS)
	       (lambda (x)
		 (pair? (intersection affected-alg-names
				      (type-to-alg-names
				       (const-to-type
					(constr-name-to-constr x))))))))
	    (affected-theorem-names
	     (list-transform-positive (map car THEOREMS)
	       (lambda (x)
		 (pair? (intersection
			 simidpc-names
			 (map
			  (lambda (idpc-formula)
			    (idpredconst-to-name
			     (predicate-form-to-predicate
			      idpc-formula)))
			 (list-transform-positive
			     (formula-to-prime-subformulas
			      (aconst-to-uninst-formula
			       (theorem-name-to-aconst x)))
			   (lambda (prime-formula)
			     (and (prime-predicate-form? prime-formula)
				  (idpredconst-form?
				   (predicate-form-to-predicate
				    prime-formula)))))))))))
	    (affected-global-assumption-names
	     (list-transform-positive (map car GLOBAL-ASSUMPTIONS)
	       (lambda (x)
		 (pair? (intersection
			 simidpc-names
			 (map
			  (lambda (idpc-formula)
			    (idpredconst-to-name
			     (predicate-form-to-predicate
			      idpc-formula)))
			 (list-transform-positive
			     (formula-to-prime-subformulas
			      (aconst-to-uninst-formula
			       (global-assumption-name-to-aconst x)))
			   (lambda (prime-formula)
			     (and (prime-predicate-form? prime-formula)
				  (idpredconst-form?
				   (predicate-form-to-predicate
				    prime-formula))))))))))))

       (set! OLD-COMMENT-FLAG COMMENT-FLAG)
       (set! COMMENT-FLAG #f)
       (set! ALGEBRAS
	     (list-transform-positive ALGEBRAS
	       (lambda (x) (not (member (car x) affected-alg-names)))))
       (for-each (lambda (x)
		   (remove-token x)
		   (comment "ok, algebra " x " removed"))
		 affected-alg-names)
       (set! CONSTRUCTORS
	     (list-transform-positive CONSTRUCTORS
	       (lambda (x) (not (member (car x) affected-constr-names)))))
       (for-each (lambda (x)
		   (remove-token x)
		   (comment "ok, constructor " x " removed"))
		 affected-constr-names)
       (apply remove-theorem affected-theorem-names)
       (apply remove-global-assumption affected-global-assumption-names)
       (apply remove-program-constant
	      (list-transform-positive (map car PROGRAM-CONSTANTS)
		(lambda (x)
		  (pair? (intersection affected-alg-names
				       (type-to-alg-names
					(const-to-type
					 (pconst-name-to-pconst x))))))))
       (set! IDS (list-transform-positive IDS
		   (lambda (x) (not (member (car x) simidpc-names)))))
       (set! COMMENT-FLAG OLD-COMMENT-FLAG)
       (for-each
	(lambda (x)
	  (remove-token x)
	  (comment
	   "ok, inductively defined predicate constant " x " removed"))
	simidpc-names))
     (multiline-comment "remove-idpc-name" "idpc name expected" idpc-name)))
  (let* ((list-of-simidpc-names
	  (map idpredconst-name-to-simidpc-names strings))
	 (reduced-list-of-simidpc-names
	  (remove-duplicates list-of-simidpc-names))
	 (reduced-strings (map car reduced-list-of-simidpc-names)))
    (for-each rin1 reduced-strings)))

;; append-hat appends ^ to every occurrence of name in string, where
;; the following character is neither ^ nor alphabetic and the
;; preceding character is not alphabetic.

(define (number-to-alphabetic-string i)
  (do ((charlist (reverse (string->list (number-to-string i))) (cdr charlist))
       (res '() (append (let ((char (car charlist)))
			  (cond ((char=? char #\0) (list #\Z #\e #\r #\o))
				((char=? char #\1) (list #\O #\n #\e))
				((char=? char #\2) (list #\T #\w #\o))
				((char=? char #\3) (list #\T #\h #\r #\e #\e))
				((char=? char #\4) (list #\F #\o #\u #\r))
				((char=? char #\5) (list #\F #\i #\v #\e))
				((char=? char #\6) (list #\S #\i #\x))
				((char=? char #\7) (list #\S #\e #\v #\e #\n))
				((char=? char #\8) (list #\E #\i #\g #\h #\t))
				((char=? char #\9) (list #\N #\i #\n #\e))
				(else (myerror "numeric char expected" char))))
			res)))
      ((null? charlist) (list->string res))))

(define (alphabetic-string-to-number string)
  (let ((l (string-length string)))
    (cond
     ((and (<= 4 l) (string=? "Zero" (substring string 0 4))) 0)
     ((and (<= 3 l) (string=? "One" (substring string 0 3))) 1)
     ((and (<= 3 l) (string=? "Two" (substring string 0 3))) 2)
     ((and (<= 5 l) (string=? "Three" (substring string 0 5))) 3)
     ((and (<= 4 l) (string=? "Four" (substring string 0 4))) 4)
     ((and (<= 4 l) (string=? "Five" (substring string 0 4))) 5)
     ((and (<= 3 l) (string=? "Six" (substring string 0 3))) 6)
     ((and (<= 5 l) (string=? "Seven" (substring string 0 5))) 7)
     ((and (<= 5 l) (string=? "Eight" (substring string 0 5))) 8)
     ((and (<= 4 l) (string=? "Nine" (substring string 0 4))) 9)
     (else
      (myerror "alphabetic-string-to-number" "unexpected string" string)))))

(define (strings-and-rest-to-numbers-and-rest string)
  (let ((l (string-length string)))
    (cond
     ((and (<= 4 l) (string=? "Zero" (substring string 0 4)))
      (cons 0 (strings-and-rest-to-numbers-and-rest (substring string 4 l))))
     ((and (<= 3 l) (string=? "One" (substring string 0 3)))
      (cons 1 (strings-and-rest-to-numbers-and-rest (substring string 3 l))))
     ((and (<= 3 l) (string=? "Two" (substring string 0 3)))
      (cons 2 (strings-and-rest-to-numbers-and-rest (substring string 3 l))))
     ((and (<= 5 l) (string=? "Three" (substring string 0 5)))
      (cons 3 (strings-and-rest-to-numbers-and-rest (substring string 5 l))))
     ((and (<= 4 l) (string=? "Four" (substring string 0 4)))
      (cons 4 (strings-and-rest-to-numbers-and-rest (substring string 4 l))))
     ((and (<= 4 l) (string=? "Five" (substring string 0 4)))
      (cons 5 (strings-and-rest-to-numbers-and-rest (substring string 4 l))))
     ((and (<= 3 l) (string=? "Six" (substring string 0 3)))
      (cons 6 (strings-and-rest-to-numbers-and-rest (substring string 3 l))))
     ((and (<= 5 l) (string=? "Seven" (substring string 0 5)))
      (cons 7 (strings-and-rest-to-numbers-and-rest (substring string 5 l))))
     ((and (<= 5 l) (string=? "Eight" (substring string 0 5)))
      (cons 8 (strings-and-rest-to-numbers-and-rest (substring string 5 l))))
     ((and (<= 4 l) (string=? "Nine" (substring string 0 4)))
      (cons 9 (strings-and-rest-to-numbers-and-rest (substring string 4 l))))
     (else (list string)))))

(define (constructor-name-to-i-and-idpredconst-name string)
  (let* ((numbers-and-rest (strings-and-rest-to-numbers-and-rest string))
	 (i (do ((l numbers-and-rest (cdr l))
		 (res 0 (if (integer? (car l))
			    (+ (* 10 res) (car l))
			    (myerror "integer expected" (car l)))))
		((or (string? (car l)) (null? l)) res)))
	 (name (car (last-pair numbers-and-rest))))
    (list i name)))

(define COIDS '())

;; Format of COIDS (similar to the format of IDS, to make utility
;; functions usable for both):

;; ((coidpredconst-name coidpredconst-names-with-pvars-and-opt-alg-names
;;   	               (clause name))
;;  ...)

;; Here the assigned pvars serve for ease of substitutions when forming
;; a greatest fixed point axiom.

;; add-co adds companions for inductively defined predicate
;; constants to COIDS, for instance CoEv, CoOd for Ev, Od.  The
;; optional algebra names and pvars are the same as for the
;; corresponding idpcs.

;; add-co takes an optional argument opt-prim-prod-eq-info where
;; ()              means ('prim EqD)
;; ('prim)         means ('prim EqD)
;; ('idpc)         means ('idpc EqD)
;; ('prim RealEq)  means ('prim RealEq)
;; ('idpc RealEq)  means ('idpc RealEq)
;; In case prim the clauses are formed with mk-ex, mk-and
;; (generating extracted terms with the primitive product make-star).  In
;; case idpc the clauses are formed with the inductively defined
;; existential quantifiers and conjunctions (generating extracted terms
;; with the defined product yprod).  In case Eqd equations are formed
;; with Leibniz equality, otherwise with the equality given by RealEq.

(define (make-realeq arg1 arg2)
  (make-predicate-formula
   (idpredconst-name-and-types-and-cterms-to-idpredconst "RealEq" '() '())
   arg1 arg2))

(define (add-co idpc-name . opt-prim-prod-eq-info)
  (let*
      ((info (assoc idpc-name IDS))
       (idpredconst-names-with-pvars-and-opt-alg-names
	(if info (cadr info)
	    (myerror "add-co" "idpredconst name expected" idpc-name)))
       (coidpc-names-with-pvars-and-opt-alg-names
	(map (lambda (x)
	       (cons (string-append "Co" (car x)) (cdr x)))
	     idpredconst-names-with-pvars-and-opt-alg-names))
       (coidpc-names (map car coidpc-names-with-pvars-and-opt-alg-names))
       (clause-names (map (lambda (coidpc-name)
			    (string-append coidpc-name "Clause"))
			  coidpc-names))
       (idpc-names (map car idpredconst-names-with-pvars-and-opt-alg-names))
       (pvars (map cadr idpredconst-names-with-pvars-and-opt-alg-names))
       (opt-alg-names
	(map cddr idpredconst-names-with-pvars-and-opt-alg-names))
       (arities (map pvar-to-arity pvars))
       (idpc-clauses-with-names-list
	(map (lambda (name)
	       (cddr (assoc name IDS)))
	     idpc-names))
       (idpc-clauses-list (map (lambda (idpc-clauses-with-names)
				 (map car idpc-clauses-with-names))
			       idpc-clauses-with-names-list))
       (prim-prod-flag-and-eq-name
	(cond ((null? opt-prim-prod-eq-info)
	       (list #t "EqD"))
	      ((= 1 (length opt-prim-prod-eq-info))
	       (list (eq? 'prim (car opt-prim-prod-eq-info)) "EqD"))
	      (else
	       (list (eq? 'prim (car opt-prim-prod-eq-info))
		     (cadr opt-prim-prod-eq-info)))))
       (prim-prod? (car prim-prod-flag-and-eq-name))
       (eq-name (cadr prim-prod-flag-and-eq-name))
       (var-lists (map (lambda (arity)
			 (map (if (string=? eq-name "RealEq")
				  type-to-new-var
				  type-to-new-partial-var)
			      (arity-to-types arity)))
		       arities))
       (mr-idpc? (mr-idpredconst-name? idpc-name))
       (nc-idpc? (nc-idpredconst-name? idpc-name))
       (clauses-with-fvars ;one for each of idpc-names
	(map
	 (lambda (vars pvar idpc-clauses)
	   (letrec
	       ((make-cr-or-nc-andl (if mr-idpc? make-andu make-andl))
		(make-cr-or-nc-andr (if mr-idpc? make-andu make-andr))
		(make-cr-or-nc-andd
		 (if prim-prod? make-and (if mr-idpc? make-andu make-andd)))
		(m-eq (lambda (x y)
			(if (string=? eq-name "EqD")
			    (make-eqd x y)
			    (make-realeq x y))))
		(m-andu (if prim-prod? mk-and mk-andu))
		(make-cr-or-nc-exl (if mr-idpc? make-exu make-exl))
		(make-cr-or-nc-exr (if mr-idpc? make-exu make-exr))
		(make-cr-or-nc-exd
		 (if prim-prod? make-ex (if mr-idpc? make-exu make-exd)))
		(clause-to-exand-fla-and-c-flag
		 (lambda (fla)
		   (cond
		    ((and (predicate-form? fla)
			  (equal? pvar (predicate-form-to-predicate fla)))
		     (let ((eq-list (map m-eq
					 (map make-term-in-var-form vars)
					 (predicate-form-to-args fla))))
		       (list
			(apply
			 m-andu
			 (if mr-idpc? ; change the order of eqd formulas
			     (append (cdr eq-list) (list (car eq-list)))
			     eq-list))
			#f)))
		    ((imp-impnc-form? fla)
		     (let* ((prem (imp-impnc-form-to-premise fla))
			    (concl (imp-impnc-form-to-conclusion fla))
			    (prev (clause-to-exand-fla-and-c-flag concl)))
		       (if
			(and (predicate-form? concl)
			     (equal? pvar (predicate-form-to-predicate concl)))
			(if (or (not (formula-of-nulltype? prem))
				(intersection (formula-to-pvars prem) pvars))
			    (list (make-cr-or-nc-andl prem (car prev)) #t)
			    (list (m-andu prem (car prev)) #f))
			(if (and (imp-form? fla)
				 (or (not (formula-of-nulltype? prem))
				     (intersection
				      (formula-to-pvars prem) pvars)))
			    (if (cadr prev)
				(list (make-cr-or-nc-andd prem (car prev)) #t)
				(list (make-cr-or-nc-andl prem (car prev)) #t))
			    (if (cadr prev)
				(list (make-cr-or-nc-andr prem (car prev)) #t)
				(list (m-andu prem (car prev)) #f))))))
		    ((all-allnc-form? fla)
		     (let* ((var (all-allnc-form-to-var fla))
			    (kernel (all-allnc-form-to-kernel fla))
			    (prev (clause-to-exand-fla-and-c-flag kernel)))
		       (if
			(and (predicate-form? kernel)
			     (equal? pvar (predicate-form-to-predicate kernel)))
			(if (all-form? fla)
			    (list (make-cr-or-nc-exl var (car prev)) #t)
			    (list (make-exu var (car prev)) #f))
			(if (all-form? fla)
			    (if (cadr prev)
				(list (make-cr-or-nc-exd var (car prev)) #t)
				(list (make-cr-or-nc-exl var (car prev)) #t))
			    (if (cadr prev)
				(list (make-cr-or-nc-exr var (car prev)) #t)
				(list (make-exu var (car prev)) #f))))))
		    (else (myerror "clause-to-exand-fla-and-c-flag"
				   "unexpected formula" fla))))))
	     (let* ((exand-fla-and-c-flag-list
		     (map clause-to-exand-fla-and-c-flag idpc-clauses))
		    (exand-fla-list (map car exand-fla-and-c-flag-list)))
	       (make-imp
		(apply make-predicate-formula
		       pvar (map make-term-in-var-form vars))
		(apply (if nc-idpc? mk-ornc mk-ori)
		       exand-fla-list)))))
	 var-lists pvars idpc-clauses-list))
       (param-tvars (apply union (map formula-to-tvars clauses-with-fvars)))
       (clauses
	(map (lambda (vars clause-with-fvars)
	       (apply
		mk-allnc
		(append
		 (if mr-idpc?
		     (append (cdr vars) (list (car vars)))
		     vars)
		 (list clause-with-fvars))))
	     var-lists clauses-with-fvars))
       (param-pvars
	(set-minus
	 (apply union (map formula-to-pvars clauses))
	 pvars)))
    (for-each
     (lambda (coidpc-name clause-name clause arity)
       (let ((non-inferable-param-tvars
	      (set-minus
	       param-tvars
	       (apply union (map type-to-tvars (arity-to-types arity))))))
	 (comment "ok, coinductively defined predicate constant "
		  coidpc-name " added")
	 (set! COIDS (cons (list coidpc-name
				 coidpc-names-with-pvars-and-opt-alg-names
				 (list clause clause-name))
			   COIDS))
	 (set! IDS (cons (list coidpc-name
			       coidpc-names-with-pvars-and-opt-alg-names
			       (list clause clause-name))
			 IDS))
					;add tokens for idpc-names
	 (cond
	  ((and (null? param-pvars)
		(null? non-inferable-param-tvars))
	   (add-token
	    coidpc-name
	    'idpredconst-name
	    (string-and-arity-and-cterms-to-idpc-parse-function
	     coidpc-name arity '())))
	  ((and (pair? param-pvars)
		(pair? non-inferable-param-tvars))
	   (add-token
	    coidpc-name
	    'idpredconstscheme-name
	    coidpc-name))
	  ((and (pair? param-pvars)
		(null? non-inferable-param-tvars))
	   (add-token
	    coidpc-name
	    'idpredconstscheme-name-wit ;wit=with-inferable-types
	    (lambda (cterms)
	      (string-and-arity-and-cterms-to-idpc-parse-function
	       coidpc-name arity cterms))))
	  (else
	   (myerror
	    "add-co"
	    "unexpected coidpredconst without cterms whose param-tvars"
	    "cannot be inferred from the arguments" coidpc-name)))))
     coidpc-names clause-names clauses arities)
					;add clauses as theorems
    (for-each
     (lambda (coidpc-name clause-name)
       (let* ((cterms (map predicate-to-cterm param-pvars))
	      (aconst (coidpredconst-to-closure-aconst
		       (make-idpredconst coidpc-name param-tvars cterms)))
	      (proof (make-proof-in-aconst-form aconst)))
	 (add-theorem clause-name proof)))
     coidpc-names clause-names)
					;and animate the c.r. ones
    (for-each animate (list-transform-positive
			  clause-names
			(lambda (clause-name)
			  (not (formula-of-nulltype?
				(proof-to-formula
				 (theorem-name-to-proof clause-name)))))))))

;; Code discarded 2016-07-28
;; ;; add-co takes an optional argument opt-prim-prod-flag.  If this is
;; ;; not present or true, the clause is formed with mk-ex, mk-and
;; ;; (generating extracted terms with the primitive product make-star).
;; ;; If this is present and #f, the clause is formed with the inductively
;; ;; defined existential quantifiers and conjunctions (generating
;; ;; extracted terms with the defined product yprod).

;; (define (add-co idpc-name . opt-prim-prod-flag)
;;   (let*
;;       ((info (assoc idpc-name IDS))
;;        (idpredconst-names-with-pvars-and-opt-alg-names
;; 	(if info (cadr info)
;; 	    (myerror "add-co" "idpredconst name expected" idpc-name)))
;;        (coidpc-names-with-pvars-and-opt-alg-names
;; 	(map (lambda (x)
;; 	       (cons (string-append "Co" (car x)) (cdr x)))
;; 	     idpredconst-names-with-pvars-and-opt-alg-names))
;;        (coidpc-names (map car coidpc-names-with-pvars-and-opt-alg-names))
;;        (clause-names (map (lambda (coidpc-name)
;; 			    (string-append coidpc-name "Clause"))
;; 			  coidpc-names))
;;        (idpc-names (map car idpredconst-names-with-pvars-and-opt-alg-names))
;;        (pvars (map cadr idpredconst-names-with-pvars-and-opt-alg-names))
;;        (opt-alg-names
;; 	(map cddr idpredconst-names-with-pvars-and-opt-alg-names))
;;        (arities (map pvar-to-arity pvars))
;;        (var-lists (map (lambda (arity)
;; 			 (map type-to-new-partial-var (arity-to-types arity)))
;; 		       arities))
;;        (idpc-clauses-with-names-list
;; 	(map (lambda (name)
;; 	       (cddr (assoc name IDS)))
;; 	     idpc-names))
;;        (idpc-clauses-list (map (lambda (idpc-clauses-with-names)
;; 				 (map car idpc-clauses-with-names))
;; 			       idpc-clauses-with-names-list))
;;        (prim-prod? (or (null? opt-prim-prod-flag) (car opt-prim-prod-flag)))
;;        (mr-idpc? (mr-idpredconst-name? idpc-name))
;;        (nc-idpc? (nc-idpredconst-name? idpc-name))
;;        (clauses-with-fvars ;one for each of idpc-names
;; 	(map
;; 	 (lambda (vars pvar idpc-clauses)
;; 	   (letrec
;; 	       ((make-cr-or-nc-andl (if mr-idpc? make-andu make-andl))
;; 		(make-cr-or-nc-andr (if mr-idpc? make-andu make-andr))
;; 		(make-cr-or-nc-andd
;; 		 (if prim-prod? make-and (if mr-idpc? make-andu make-andd)))
;; 		(m-andu (if prim-prod? mk-and mk-andu))
;; 		(make-cr-or-nc-exl (if mr-idpc? make-exu make-exl))
;; 		(make-cr-or-nc-exr (if mr-idpc? make-exu make-exr))
;; 		(make-cr-or-nc-exd
;; 		 (if prim-prod? make-ex (if mr-idpc? make-exu make-exd)))
;; 		(clause-to-exand-fla-and-c-flag
;; 		 (lambda (fla)
;; 		   (cond
;; 		    ((and (predicate-form? fla)
;; 			  (equal? pvar (predicate-form-to-predicate fla)))
;; 		     (let ((eqd-list (map make-eqd
;; 					  (map make-term-in-var-form vars)
;; 					  (predicate-form-to-args fla))))
;; 		       (list
;; 			(apply
;; 			 m-andu
;; 			 (if mr-idpc? ; change the order of eqd formulas
;; 			     (append (cdr eqd-list) (list (car eqd-list)))
;; 			     eqd-list))
;; 			#f)))
;; 		    ((imp-impnc-form? fla)
;; 		     (let* ((prem (imp-impnc-form-to-premise fla))
;; 			    (concl (imp-impnc-form-to-conclusion fla))
;; 			    (prev (clause-to-exand-fla-and-c-flag concl)))
;; 		       (if
;; 			(and (predicate-form? concl)
;; 			     (equal? pvar (predicate-form-to-predicate concl)))
;; 			(if (or (not (formula-of-nulltype? prem))
;; 				(intersection (formula-to-pvars prem) pvars))
;; 			    (list (make-cr-or-nc-andl prem (car prev)) #t)
;; 			    (list (m-andu prem (car prev)) #f))
;; 			(if (and (imp-form? fla)
;; 				 (or (not (formula-of-nulltype? prem))
;; 				     (intersection (formula-to-pvars prem) pvars)))
;; 			    (if (cadr prev)
;; 				(list (make-cr-or-nc-andd prem (car prev)) #t)
;; 				(list (make-cr-or-nc-andl prem (car prev)) #t))
;; 			    (if (cadr prev)
;; 				(list (make-cr-or-nc-andr prem (car prev)) #t)
;; 				(list (m-andu prem (car prev)) #f))))))
;; 		    ((all-allnc-form? fla)
;; 		     (let* ((var (all-allnc-form-to-var fla))
;; 			    (kernel (all-allnc-form-to-kernel fla))
;; 			    (prev (clause-to-exand-fla-and-c-flag kernel)))
;; 		       (if
;; 			(and (predicate-form? kernel)
;; 			     (equal? pvar (predicate-form-to-predicate kernel)))
;; 			(if (all-form? fla)
;; 			    (list (make-cr-or-nc-exl var (car prev)) #t)
;; 			    (list (make-exu var (car prev)) #f))
;; 			(if (all-form? fla)
;; 			    (if (cadr prev)
;; 				(list (make-cr-or-nc-exd var (car prev)) #t)
;; 				(list (make-cr-or-nc-exl var (car prev)) #t))
;; 			    (if (cadr prev)
;; 				(list (make-cr-or-nc-exr var (car prev)) #t)
;; 				(list (make-exu var (car prev)) #f))))))
;; 		    (else (myerror "clause-to-exand-fla-and-c-flag"
;; 				   "unexpected formula" fla))))))
;; 	     (let* ((exand-fla-and-c-flag-list
;; 		     (map clause-to-exand-fla-and-c-flag idpc-clauses))
;; 		    (exand-fla-list (map car exand-fla-and-c-flag-list)))
;; 	       (make-imp
;; 		(apply make-predicate-formula
;; 		       pvar (map make-term-in-var-form vars))
;; 		(apply (if nc-idpc? mk-ornc mk-ori)
;; 		       exand-fla-list)))))
;; 	 var-lists pvars idpc-clauses-list))
;;        (param-tvars (apply union (map formula-to-tvars clauses-with-fvars)))
;;        (clauses
;; 	(map (lambda (vars clause-with-fvars)
;; 	       (apply
;; 		mk-allnc
;; 		(append
;; 		 (if mr-idpc?
;; 		     (append (cdr vars) (list (car vars)))
;; 		     vars)
;; 		 (list clause-with-fvars))))
;; 	     var-lists clauses-with-fvars))
;;        (param-pvars
;; 	(set-minus
;; 	 (apply union (map formula-to-pvars clauses))
;; 	 pvars)))
;;     (for-each
;;      (lambda (coidpc-name clause-name clause arity)
;;        (let ((non-inferable-param-tvars
;; 	      (set-minus
;; 	       param-tvars
;; 	       (apply union (map type-to-tvars (arity-to-types arity))))))
;; 	 (comment "ok, coinductively defined predicate constant "
;; 		  coidpc-name " added")
;; 	 (set! COIDS (cons (list coidpc-name
;; 				 coidpc-names-with-pvars-and-opt-alg-names
;; 				 (list clause clause-name))
;; 			   COIDS))
;; 	 (set! IDS (cons (list coidpc-name
;; 			       coidpc-names-with-pvars-and-opt-alg-names
;; 			       (list clause clause-name))
;; 			 IDS))
;; 					;add tokens for idpc-names
;; 	 (cond
;; 	  ((and (null? param-pvars)
;; 		(null? non-inferable-param-tvars))
;; 	   (add-token
;; 	    coidpc-name
;; 	    'idpredconst-name
;; 	    (string-and-arity-and-cterms-to-idpc-parse-function
;; 	     coidpc-name arity '())))
;; 	  ((and (pair? param-pvars)
;; 		(pair? non-inferable-param-tvars))
;; 	   (add-token
;; 	    coidpc-name
;; 	    'idpredconstscheme-name
;; 	    coidpc-name))
;; 	  ((and (pair? param-pvars)
;; 		(null? non-inferable-param-tvars))
;; 	   (add-token
;; 	    coidpc-name
;; 	    'idpredconstscheme-name-wit ;wit=with-inferable-types
;; 	    (lambda (cterms)
;; 	      (string-and-arity-and-cterms-to-idpc-parse-function
;; 	       coidpc-name arity cterms))))
;; 	  (else
;; 	   (myerror
;; 	    "add-co"
;; 	    "unexpected coidpredconst without cterms whose param-tvars"
;; 	    "cannot be inferred from the arguments" coidpc-name)))))
;;      coidpc-names clause-names clauses arities)
;; 					;add clauses as theorems
;;     (for-each
;;      (lambda (coidpc-name clause-name)
;;        (let* ((cterms (map predicate-to-cterm param-pvars))
;; 	      (aconst (coidpredconst-to-closure-aconst
;; 		       (make-idpredconst coidpc-name param-tvars cterms)))
;; 	      (proof (make-proof-in-aconst-form aconst)))
;; 	 (add-theorem clause-name proof)))
;;      coidpc-names clause-names)
;; 					;and animate the c.r. ones
;;     (for-each animate (list-transform-positive
;; 			  clause-names
;; 			(lambda (clause-name)
;; 			  (not (formula-of-nulltype?
;; 				(proof-to-formula
;; 				 (theorem-name-to-proof clause-name)))))))))

