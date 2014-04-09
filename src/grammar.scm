; $Id: grammar.scm 2534 2012-03-13 22:03:25Z schwicht $
; 7-5. Parsing
; ============

(define minigram
  '(; Auxiliar Functions at runtime
"

(define (token-type-to-arity token)
  (case token
    ((postfix-typeop prefix-typeop postfix-op prefix-op postfix-jct prefix-jct)
     1)
    ((prod-typeop tensor-typeop sum-typeop binding-op add-op mul-op exp-op
      rel-op and-op or-op imp-op pair-op and-jct or-jct tensor-jct imp-jct)
     2)
    (else 0)))

(define (alg-name-to-token-value alg-name)
  (let ((token-type (alg-name-to-token-type alg-name)))
    (case (token-type-to-arity token-type)
      ((0) alg-name)
      ((1) (lambda (x) (make-alg alg-name x)))
      ((2) (lambda (x y) (make-alg alg-name x y)))
      (else (myerror \"unexpected arity\" token-type)))))

(define (const-to-token-value const)
  (let ((token-type (const-to-token-type const)))
    (case (token-type-to-arity token-type)
      ((0) (make-term-in-const-form const))
      ((1) (lambda (x)
	     (make-term-in-app-form
	      (make-term-in-const-form const) x)))
      ((2) (lambda (x y)
	     (make-term-in-app-form
	      (make-term-in-app-form
	       (make-term-in-const-form const) x) y)))
      (else (myerror \"unexpected arity\" token-type)))))

; added 01-07-14
(define (const-and-token-type-to-token-value const token-type)
  (case (token-type-to-arity token-type)
    ((0) (make-term-in-const-form const))
    ((1) (lambda (x)
	   (make-term-in-app-form
	    (make-term-in-const-form const) x)))
    ((2) (lambda (x y)
	   (make-term-in-app-form
	    (make-term-in-app-form
	     (make-term-in-const-form const) x) y)))
    (else (myerror \"unexpected arity\" token-type))))

(define (token-type-to-precedence token-type)
  (case token-type
    ((binding-op bindterm) 1)
    ((pair-op term) 2)
    ((imp-op impterm) 3)
    ((or-op orterm) 4)
    ((and-op andterm) 5)
    ((rel-op relterm) 6)
    ((add-op addterm) 7)
    ((mul-op multerm) 8)
    ((exp-op expterm) 9)
    ((appterm) 10)
    ((prefix-op preterm) 11)
    ((postfix-op postterm) 12)
    ((const var number rec-op grec-op grecguard-op
	    corec-op destr-op if-op atomic-term) 13)
    (else (myerror
	   \"token-type-to-precendence: token type expected\" token-type))))

(define (left-assoc? token-type)
  (memq token-type
	'(add-op addterm mul-op multerm exp-op expterm appterm)))

(define (right-assoc? token-type)
  (memq token-type
	'(pair-op term imp-op impterm and-op andterm or-op orterm)))

(define (type-var-name-to-type type-var-name)
  (if (eq? (car type-var-name) #f)
      (myerror \"Unknown variable name \" (cdr type-var-name))
      (car type-var-name)))

(define (type-var-name-to-name type-var-name)
  (cdr type-var-name))

(define (pt string)
  (let ((t (pf string)))
    (if (eq? (car t) 'atom)
	(cadr t)
	(myerror \"pt: term expected\" t))))

(define (py string)
  (let ((t (pt string)))
    (if (eq? (car t) 'term-in-var-form)
	(cadr t)
	(myerror \"py: type expected\" t))))

(define (pv string)
  (let ((t (pt string)))
    (if (eq? (car t) 'term-in-var-form)
	(term-in-var-form-to-var t)
	(myerror \"pv: variable expected\" t))))
"
; Terminals
    ( ;*EOI*  ;end of input built in
     number
     var-index
     tvar-name
     tconst
     var-name
     const
     pvar-name
     pvar-op
     pred-infix
     predconst-name
     idpredconst-name
     idpredconstscheme-name ;added 2005-02-24
     idpredconstscheme-name-wit ;added 2005-02-24.  wit = with-inferable-types
     type-symbol
     alg
     constscheme

     alg-typeop
     postfix-typeop
     prefix-typeop
     prod-typeop
     tensor-typeop
     sum-typeop
     arrow

     postfix-op
     prefix-op
     rec-op
     grec-op
     grecguard-op
     corec-op
     destr-op
     binding-op
     add-op
     mul-op
     exp-op
     rel-op
     and-op
     or-op
     imp-op
     pair-op
     pairscheme-op
     cterm-op
     if-op

     postfix-jct
     prefix-jct
     and-jct
     or-jct
     tensor-jct
     imp-jct
     quantor
     dot

     hat
     underscore
     comma
     semicolon
     prime

     hatprime
     hatprimeunderscore
     hatunderscore
     primeunderscore

     lpar
     rpar
     lbracket
     rbracket
     lcurl
     rcurl

; Finally we want to be able to parse yet undefined tokens
; the value will be the token string

     undefined-token

; for a programming language you need strings
; the value is again the string

     string

; for mpc we need
     mpc-mpc
     mpc-proof
     mpc-classic
     mpc-intuitionistic
     mpc-end
     mpc-load
     mpc-include
     mpc-scheme
     mpc-type
     mpc-pred
     mpc-algebra
     mpc-function
     mpc-partial
     mpc-rewrite
     mpc-syntax
     mpc-op
     )

; Predefined Tokens
    (
; Constants

; Predicate variables
     ("bot" pvar-name . (cons (make-arity) "bot"))

; Predicate constants
     ("Equal" predconst-name .
        (string-and-arity-to-predconst-parse-function
          "Equal" (make-arity (make-tvar -1 "alpha") (make-tvar -1 "alpha"))))
     ("Total" predconst-name .
        (string-and-arity-to-predconst-parse-function
          "Total" (make-arity (make-tvar -1 "alpha"))))
     ("TotalMR" predconst-name .
        (string-and-arity-to-predconst-parse-function
          "TotalMR"
          (make-arity (make-tvar -1 "alpha") (make-tvar -1 "alpha"))))

; Type Variables
     ("alpha" tvar-name . "alpha")

; Type Constants
     ("atomic" tconst . "atomic")
     ("existential" tconst . "existential")
     ("prop" tconst . "prop")
     ("nulltype" tconst . "nulltype")

; Type operators
     ("=>" arrow . make-arrow)
     ("@@" prod-typeop . make-star) ;added 01-09-17

; Quantors
     ("all" quantor . (lambda (v k) (apply mk-all (append v (list k)))))
     ("ex" quantor . (lambda (v k) (apply mk-ex (append v (list k)))))
     ("allnc" quantor . (lambda (v k) (apply mk-allnc (append v (list k)))))
     ("exnc" quantor . (lambda (v k) (apply mk-exnc (append v (list k)))))
     ("excl" quantor . (lambda (v k) (apply mk-excl (append v (list k)))))
     ("exca" quantor . (lambda (v k) (apply mk-exca (append v (list k)))))
     ("excu" quantor . (lambda (v k) (apply mk-excu (append v (list k)))))

; Junctors
     ("&" and-jct . make-and)
     ("!" tensor-jct . make-tensor)
     ("->" imp-jct . make-imp)
     ("-->" imp-jct . make-impnc)

; Operators
     ("Rec" rec-op . (lambda (l)
		       (make-term-in-const-form
			(apply type-info-to-rec-const l))))
     ("GRec" grec-op . (lambda (l)
		       (make-term-in-const-form
			(type-info-to-grec-const l))))
     ("GRecGuard" grecguard-op . (lambda (l)
		       (make-term-in-const-form
			(type-info-to-grecguard-const l))))
     ("CoRec" corec-op . (lambda (l)
                           (make-term-in-const-form
                            (apply alg-or-arrow-types-to-corec-const l))))
     ("coRec" corec-op . (lambda (l) ;obsolete
                       (make-term-in-const-form
                        (apply arrow-type-to-corec-const l))))
     ("Destr" destr-op . (lambda (term)
                       (make-term-in-const-form
                        (alg-to-destr-const term))))
     ("=" rel-op . (lambda (term1 term2)
		     (let ((type1 (term-to-type term1))
		     	   (type2 (term-to-type term2)))
		       (mk-term-in-app-form
		        (make-term-in-const-form
			(finalg-to-=-const  (if (equal? type1 type2)
						 type1
						 (types-lub type1 type2))))
		        term1 term2))))
     ("lambda" binding-op . (lambda (varlist kernel)
                               (apply mk-term-in-abst-form
                                      (append varlist (list kernel)))))
     ("E" prefix-op . (lambda (term)
                        (make-term-in-app-form
                          (make-term-in-const-form
                            (finalg-to-e-const (term-to-type term))) term)))
     ("SE" prefix-op . (lambda (term)
                         (make-term-in-app-form
                           (make-term-in-const-form
                             (sfinalg-to-se-const (term-to-type term))) term)))
     ("@" pair-op . make-term-in-pair-form)
     ("left" prefix-op . make-term-in-lcomp-form)
     ("right" prefix-op . make-term-in-rcomp-form)

; Comprehension terms
     ("cterm" cterm-op)

; The if
     ("if" if-op)

; Default name for predicate variables
     ("Pvar" pvar-op)

; Punctuation Marks
     ("^" hat)
     ("_" underscore)
     ("." dot)
     ("," comma)
     (";" semicolon)
     ("'" prime)
     ("(" lpar)
     (")" rpar)
     ("[" lbracket)
     ("]" rbracket)
     ("{" lcurl)
     ("}" rcurl)

; Special Punctuation Marks
     ("^'" hatprime)
     ("^'_" hatprimeunderscore)
     ("^_" hatunderscore)
     ("'_" primeunderscore)

; tokens for mpc
     ("MPC" mpc-mpc)
     ("PROOF" mpc-proof)
     ("CLASSIC" mpc-classic)
     ("INTUITIONISTIC" mpc-intuitionistic)
     ("END" mpc-end)
     ("LOAD" mpc-load)
     ("INCLUDE" mpc-include)
     ("SCHEME" mpc-scheme)
     ("TYPE" mpc-type)
     ("PRED" mpc-pred)
     ("ALGEBRA" mpc-algebra)
     ("FUNCTION" mpc-function)
     ("PARTIAL" mpc-partial)
     ("REWRITE" mpc-rewrite)
     ("SYNTAX" mpc-syntax)
     ("PAIROP" mpc-op . (list 'pair-op "PAIROP" 2))
     ("IMPOP" mpc-op . (list 'imp-op "IMPOP" 2))
     ("OROP" mpc-op . (list 'or-op "OROP" 2))
     ("ANDOP" mpc-op . (list 'and-op "ANDOP" 2))
     ("RELOP" mpc-op . (list 'rel-op "RELOP" 2))
     ("ADDOP" mpc-op . (list 'add-op "ADDOP" 2))
     ("MULOP" mpc-op . (list 'mul-op "MULOP" 2))
     ("PREFIXOP" mpc-op . (list 'prefix-op "PREFIXOP" 1))
     ("POSTFIXOP" mpc-op . (list 'postfix-op "POSTFIXOP" 1))
     ("CONST" mpc-op . (list 'const "CONST" 0))
)

; Productions
; for formulas we have
;    6 levels of binary junctors
;      the 4 top levels rightassociative
;      the 2 lower levels leftassociative
;    1 level of quantors and the
;    dot operator that extends the reach of a quantor as far as possible
;       tail-... is a subformula that uses such a dotted quantor and extends
;       to the end of the formula
;    1 level of prefix junctor
;    1 level of postfix junctors binding strongest
    (parse-item
      (formula) : $1
      (mpc-file) : $1)
    (formula (impformula) : $1)
    (impformula
      (tensorformula imp-jct impformula) : ($2 $1 $3)
      (tail-tensorformula) : $1
      (tensorformula) : $1)
    (tensorformula
      (orformula tensor-jct tensorformula) : ($2 $1 $3)
      (orformula) : $1)
    (tail-tensorformula
      (orformula tensor-jct tail-tensorformula) : ($2 $1 $3)
      (tail-orformula) : $1)
    (orformula
      (andformula or-jct orformula) : ($2 $1 $3)
      (andformula) : $1)
    (tail-orformula
      (tail-andformula or-jct orformula) : ($2 $1 $3)
      (tail-andformula) : $1)
    (andformula
      (qformula and-jct andformula) : ($2 $1 $3)
      (qformula) : $1)
    (tail-andformula
      (tail-qformula and-jct andformula) : ($2 $1 $3)
      (tail-qformula) : $1)
    (tail-qformula
      (quantor varlist dot formula): ($1 $2 $4)
      (quantor varlist tail-qformula) : ($1 $2 $3)
      (prefix-jct tail-qformula) : ($1 $2))
    (qformula
      (quantor varlist qformula) : ($1 $2 $3)
      (prefix-jct qformula) : ($1 $2)
      (postformula) : $1)
    (postformula
      (postformula postfix-jct) : ($2 $1)
      (atomic-formula) : $1)
    (atomic-formula
      (pred atomicterm-list) : (apply make-predicate-formula (cons $1 $2))
      (term pred-infix term) : ($2 $1 $3)
      (predconstformula) : $1
      (idpredconstformula) : $1
      (term) : (make-atomic-formula $1)
      (lpar formula rpar) : $2)

    (atomicterm-list
      () : '()
      (atomicterm-list atomic-term) : (append $1 (list $2)))

; Predicate constants
    (predconstformula
      (predconst-name atomicterm-list) : (apply $1 (cons -1 $2))
      (predconst-name var-index atomicterm-list) : (apply $1 (cons $2 $3))
      (predconst-name underscore var-index atomicterm-list) :
        (apply $1 (cons $3 $4))
      (predconst-name underscore atomicterm-list) : (apply $1 (cons -1 $3)))

; Inductively define predicate constants with inferable types, without cterms
    (idpredconstformula
      (idpredconst-name atomicterm-list) : (apply $1 $2)
      (idpred atomicterm-list) : (apply $1 $2))

; Inductively define predicate constants with cterms and with inferable types
    (idpred
      (lpar idpredconstscheme-name-wit cterms rpar) : ($2 $3)
      (lpar idpredconstscheme-name-wit typelist cterms rpar) : ($2 $4))

; Predicate variables or inductively defined predicate constants
    (pred
      (pvar-name) :
        (make-pvar (car $1) -1 h-deg-zero n-deg-zero (cdr $1))
      (pvar-name var-index) :
        (make-pvar (car $1) $2 h-deg-zero n-deg-zero (cdr $1))
      (pvar-name hat var-index) :
        (make-pvar (car $1) $3 h-deg-one n-deg-zero (cdr $1))
      (pvar-name hat) :
        (make-pvar (car $1) -1 h-deg-one n-deg-zero (cdr $1))
      (pvar-name underscore var-index) :
        (make-pvar (car $1) $3 h-deg-zero n-deg-zero (cdr $1))
      (pvar-name underscore) :
        (make-pvar (car $1) -1 h-deg-zero n-deg-zero (cdr $1))
      (pvar-name prime) :
        (make-pvar (car $1) -1 h-deg-zero n-deg-one (cdr $1))
      (pvar-name prime var-index) :
        (make-pvar (car $1) $3 h-deg-zero n-deg-one (cdr $1))
      (pvar-name hatprime var-index) :
        (make-pvar (car $1) $3 h-deg-one n-deg-one (cdr $1))
      (pvar-name hatprime) :
        (make-pvar (car $1) -1 h-deg-one n-deg-one (cdr $1))
      (pvar-name primeunderscore var-index) :
        (make-pvar (car $1) $3 h-deg-zero n-deg-one (cdr $1))
      (pvar-name primeunderscore) :
        (make-pvar (car $1) -1 h-deg-zero n-deg-one (cdr $1))
      (pvar-name hatunderscore) :
        (make-pvar (car $1) -1 h-deg-one n-deg-zero (cdr $1))
      (pvar-name hatunderscore var-index) :
        (make-pvar (car $1) $3 h-deg-one n-deg-zero (cdr $1))
      (pvar-name hatprimeunderscore var-index) :
        (make-pvar (car $1) $3 h-deg-one n-deg-one (cdr $1))
      (pvar-name hatprimeunderscore) :
        (make-pvar (car $1) -1 h-deg-one n-deg-one (cdr $1))

      (default-pvar-name) :
        (make-pvar $1 -1 h-deg-zero n-deg-zero "")
      (default-pvar-name var-index) :
        (make-pvar $1 $2 h-deg-zero n-deg-zero "")
      (default-pvar-name hat var-index) :
        (make-pvar $1 $3 h-deg-one n-deg-zero "")
      (default-pvar-name hat) :
        (make-pvar $1 -1 h-deg-one n-deg-zero "")
      (default-pvar-name underscore var-index) :
        (make-pvar $1 $3 h-deg-zero n-deg-zero "")
      (default-pvar-name underscore) :
        (make-pvar $1 -1 h-deg-zero n-deg-zero "")
      (default-pvar-name prime) :
        (make-pvar $1 -1 h-deg-zero n-deg-one "")
      (default-pvar-name prime var-index) :
        (make-pvar $1 $3 h-deg-zero n-deg-one "")
      (default-pvar-name hatprime) :
        (make-pvar $1 -1 h-deg-one n-deg-one "")
      (default-pvar-name hatprime var-index) :
        (make-pvar $1 $3 h-deg-one n-deg-one "")
      (default-pvar-name primeunderscore var-index) :
        (make-pvar $1 $3 h-deg-zero n-deg-one "")
      (default-pvar-name primeunderscore) :
        (make-pvar $1 -1 h-deg-zero n-deg-one "")
      (default-pvar-name hatunderscore) :
        (make-pvar $1 -1 h-deg-one n-deg-zero "")
      (default-pvar-name hatunderscore var-index) :
        (make-pvar $1 $3 h-deg-one n-deg-zero "")
      (default-pvar-name hatprimeunderscore var-index) :
        (make-pvar $1 $3 h-deg-one n-deg-one "")
      (default-pvar-name hatprimeunderscore) :
        (make-pvar $1 -1 h-deg-one n-deg-one "")

      (lpar idpredconstscheme-name typelist cterms rpar) :
        (idpredconst-name-and-types-and-cterms-to-idpredconst $2 $3 $4)
      (lpar idpredconstscheme-name typelist rpar) :
        (idpredconst-name-and-types-and-cterms-to-idpredconst $2 $3 '()))

; Comprehension terms
    (cterm
      (lpar cterm-op lpar varlist rpar formula rpar) :
        (apply make-cterm (append $4 (list $6)))
      (lpar cterm-op lpar rpar formula rpar) : (make-cterm $5))
    (cterms
      (cterm) : (list $1)
      (cterms cterm) : (append $1 (list $2)))

; Default names for predicate variables
    (default-pvar-name
      (pvar-op) : (make-arity)
      (lpar pvar-op typelist rpar) : (apply make-arity $3))

; Variable list for quantors
    (varlist
      (var comma varlist) : (cons $1 $3)
      (var) : (list $1))
; variables
    (var
      (var-name) :
        (make-var (type-var-name-to-type $1) -1 1 (type-var-name-to-name $1))
      (var-name var-index) :
        (make-var (type-var-name-to-type  $1) $2 1 (type-var-name-to-name $1))
      (var-name hat var-index) :
        (make-var (type-var-name-to-type $1) $3 0 (type-var-name-to-name $1))
      (var-name hat) :
        (make-var (type-var-name-to-type $1) -1 0 (type-var-name-to-name $1))
      (var-name underscore var-index) :
        (make-var (type-var-name-to-type $1) $3 1 (type-var-name-to-name $1))
      (var-name underscore) :
        (make-var (type-var-name-to-type $1) -1 1 (type-var-name-to-name $1))
      (type) : (make-var $1 -1 1 "")
      (type var-index) : (make-var $1 $2 1 "")
      (type hat var-index) : (make-var $1 $3 0 "")
      (type hat) : (make-var $1 -1 0 "")
      (type underscore var-index) : (make-var $1 $3 1 "")
      (type underscore) : (make-var $1 -1 1 "")
      (type underscore var-name) :
        (make-var $1 -1 1 (type-var-name-to-name $3))
      (type underscore var-name var-index) :
        (make-var $1 $4 1 (type-var-name-to-name $3))
      (type underscore var-name hat var-index) :
        (make-var $1 $5 0 (type-var-name-to-name $3))
      (type underscore var-name hat) :
        (make-var $1 -1 0 (type-var-name-to-name $3))
      (type underscore var-name underscore var-index) :
        (make-var $1 $5 1 (type-var-name-to-name $3))
      (type underscore var-name underscore) :
        (make-var $1 -1 1 (type-var-name-to-name $3)))

; For types we have
;    4 levels of rightassociative binary operators,
;    1 level of prefix operators
;    1 level of postfix operators binding strongest

      (type
        (sumtype arrow type) : ($2 $1 $3)
        (sumtype) : $1)
      (sumtype
        (tensortype sum-typeop sumtype) : ($2 $1 $3)
        (tensortype) : $1)
      (tensortype
        (prodtype tensor-typeop tensortype) : ($2 $1 $3)
        (prodtype) : $1)
      (prodtype
        (apptype prod-typeop prodtype) : ($2 $1 $3)
        (pretype prod-typeop prodtype) : ($2 $1 $3)
        (apptype) : $1
        (pretype) : $1)
      (apptype
        (apptype atomictype) : (apply make-alg
				      (cons (alg-form-to-name $1)
					    (append (alg-form-to-types $1)
						    (list $2))))
        (alg-typeop atomictype) : (make-alg $1 $2))
      (pretype
        (prefix-typeop pretype) : ($1 $2)
        (posttype) : $1)
      (posttype
        (posttype postfix-typeop) : ($2 $1)
        (atomictype) : $1)
      (atomictype
        (tvar) : $1
        (tconst) : (make-tconst $1)
        (alg) : (make-alg $1)
        (lpar type rpar) : $2)

; Type lists
    (typelist
      (type) : (list $1)
      (typelist type) : (append $1 (list $2)))

; Type variables
    (tvar
      (tvar-name) : (make-tvar -1 $1)
      (tvar-name var-index) : (make-tvar $2 $1))

; For terms we have
;    7 levels of binary operators,
;      the 4 top levels rightassociative
;      the 3 lower levels leftassociative
;    1 level of prefix operators
;    1 level of postfix operators binding strongest

    (term
      (impterm pair-op term) : ($2 $1 $3)
      (impterm pairscheme term) : ($2 $1 $3)
      (binding-op varlist dot term) : ($1 $2 $4)
      (lbracket varlist rbracket term) :
        (apply mk-term-in-abst-form (append $2 (list $4)))
      (impterm) : $1)
    (impterm
      (orterm imp-op impterm) : ($2 $1 $3)
      (orterm) : $1)
    (orterm
      (andterm or-op orterm) : ($2 $1 $3)
      (andterm) : $1)
    (andterm
      (relterm and-op andterm) : ($2 $1 $3)
      (relterm) : $1)
    (relterm
      (addterm rel-op addterm) : ($2 $1 $3)
      (addterm) : $1)
    (addterm
      (addterm add-op multerm) : ($2 $1 $3)
      (multerm) : $1)
    (multerm
      (multerm mul-op expterm) : ($2 $1 $3)
      (expterm) : $1)
    (expterm
      (expterm exp-op appterm) : ($2 $1 $3)
      (appterm) : $1)
    (appterm
      (appterm bindterm) : (make-gen-application $1 $2)
      (bindterm) : $1)
    (bindterm
      (binding-op varlist preterm) : ($1 $2 $3)
      (preterm) : $1)
    (preterm
      (prefix-op preterm) : ($1 $2)
      (postterm) : $1)
    (postterm
      (postterm postfix-op) : ($2 $1)
      (atomic-term) : $1)
    (atomic-term
      (lpar term rpar) : $2
      (const) : $1
      (var) : (make-term-in-var-form $1)
      (number) : (make-numeric-term $1)
      (lpar rec-op typelist rpar) : ($2 $3)
      (lpar rec-op number typelist rpar) : ($2 (cons $3 $4)) ;added 2002-01-01
      (lpar grec-op typelist rpar) : ($2 $3)
      (lpar grecguard-op typelist rpar) : ($2 $3)
      (lpar grecguard-op number typelist rpar) : ($2 (cons $3 $4)) ;added 2010
      (lpar corec-op typelist rpar) : ($2 $3)
      (lpar destr-op type rpar) : ($2 $3)
      (lpar constscheme typelist rpar) :
        (make-term-in-const-form
	 (let* ((tvars (const-to-tvars $2))
		(subst (make-substitution tvars $3)))
	   (const-substitute $2 subst #f)))
      (lbracket if-op atomic-term-list rbracket) :
        (make-term-in-if-form (car $3) (cdr $3)))

    (atomic-term-list
      (atomic-term) : (list $1)
      (atomic-term-list atomic-term) : (append $1 (list $2)))

    (pairscheme
      (pairscheme-op typelist) :
        (lambda (x y)
	  (make-term-in-app-form
	   (make-term-in-app-form
	    (make-term-in-const-form
	     (let* ((tvars (const-to-tvars $1))
		    (subst (make-substitution tvars $2)))
	       (const-substitute $1 subst #f))) x) y)))

; Grammar for mpc
    (mpc-file
      (mpc-mpc semicolon commandlist) : #t)
    (commandlist
      () : #t
      (commandlist command) : #t)
    (command
      (command-spec semicolon) : #t
      (assumption dot) : #t
      (claim semicolon) : #t
      (block) : #t
      (declaration-spec semicolon) : #t
      (syntax-spec semicolon) : #t)
    (command-spec
      (mpc-load string) : (mpc-command-load $2)
      (mpc-include string) : (mpc-command-include $2)
      (mpc-scheme string) : (mpc-command-scheme $2)
      (mpc-proof) : (mpc-start #f #f)
      (mpc-classic mpc-proof) : (mpc-start #t #t)
      (mpc-intuitionistic mpc-proof) : (mpc-start #t #f)
      (mpc-end) : (mpc-stop))
    (claim
      () : #t  ;the empty claim
      (formula) : (mpc-claim $1))
    (assumption
      (formula) : (mpc-assume $1))
    (block
      (lcurl block-start claimlist rcurl) : (mpc-block-stop))
    (block-start
      (formula dot) : (mpc-block-start $1))
    (claimlist
      (claim semicolon) : #t
      (block) : #t
      (claimlist block) : #t
      (claimlist claim semicolon) : #t)
    (declaration-spec
      (mpc-type dot tokenlist) : (mpc-declare-type $3)
      (type dot tokenlist) : (mpc-declare-var $1 $3)
      (mpc-pred typelist dot tokenlist) :
        (mpc-declare-pred (apply make-arity $2) $4)
      (mpc-pred dot tokenlist) : (mpc-declare-pred (make-arity) $3)
      (mpc-algebra-header lcurl constructor-list rcurl) :
	(mpc-declare-algebra (car $1) (cadr $1) (cddr $1) $3)
      (function-header
        function-rules-start function-rule-list function-rules-stop) :
        (mpc-function)
      (function-header) : (mpc-function))
    (function-rules-start
      (lcurl) : (mpc-function-rules-start))
    (function-rules-stop
      (rcurl) : (mpc-function-rules-stop))
    (mpc-algebra-header
      (mpc-algebra tokenlist number) : (mpc-declare-algebra-header $2 $3)
      (mpc-algebra tokenlist) : (mpc-declare-algebra-header $2 0))
    (tokenlist
      (undefined-token) : (list $1)
      (undefined-token tokenlist) : (cons $1 $2))
    (constructor-list
      () : '()
      (constructor-def constructor-list) : (cons $1 $2))
    (constructor-def
      (type dot undefined-token semicolon) : (list $3 $1))
    (function-header
      (mpc-function type dot undefined-token lpar typelist rpar) :
        (mpc-declare-function $4 $6 $2 1)
      (mpc-partial mpc-function type dot undefined-token lpar typelist rpar) :
        (mpc-declare-function $5 $7 $3 0))
    (function-rule-list
      () : #t
      (function-rule-list function-rule) : #t)
    (function-rule
      (syntax-spec semicolon ) : #t
      (term imp-jct term semicolon ) : (mpc-computation-rule $1 $3)
      (mpc-rewrite term imp-jct term semicolon ) : (mpc-rewrite-rule $2 $4))
    (syntax-spec
      (mpc-syntax redefinable-op mpc-op term) :
      (mpc-declare-syntax $2 (car $3) (cadr $3) (caddr $3) $4))
    (redefinable-op
      (undefined-token) : $1
      (pair-op ) : current-token
      (imp-op ) : current-token
      (or-op ) : current-token
      (and-op ) : current-token
      (rel-op ) : current-token
      (add-op ) : current-token
      (mul-op ) : current-token
      (prefix-op ) : current-token
      (postfix-op ) : current-token)
 ;      (rule-list () : '()
 ;                        (rule-def rule-list) : (cons $1 $2))
 ;
 ;      (optype mpc-addop : 'add-op )
 ;      (template () : '())
    ))

(display "Grammar loaded") (newline)

(load "lalr.scm")

(display "Generator loaded") (newline)

(gen-lalr1 minigram "minitab.scm")

(display "Completed") (newline)

(print-states)

(exit)

