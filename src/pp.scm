;; 2017-04-21

;; We define token-tree-to-string and use this for all display
;; purposes.  For line breaks, we define token-tree-to-pp-tree .

;; A token-tree consists of a token-tree-tag (short: tttag), an
;; op-string and finitely many argument token-trees.  There are few
;; token-tree-tags.  Each has an assigned precedence and
;; associativity.  Depending on these data parentheses are introduced.

;; For token-tree-tags we reuse available token types where this makes
;; sense.  Possibilities for tttag:

;; alg
;; alg-typeop
;; prod-typeop
;; tensor-typeop
;; sum-typeop
;; prefix-typeop
;; postfix-typeop  (up to now, possible values of alg-name-to-token-type)
;; atomic-type
;; arrow-typeop

;; number
;; if-op
;; appterm
;; var
;; const
;; binding-op
;; pair-op
;; prefix-op
;; postfix-op
;; rel-op  (used in DISPLAY-FUNCTIONS, e.g., for = and < on nat)
;; add-op  (used in nat.scm)
;; mul-op  (used in nat.scm)
;; exp-op  (used in numbers.scm)

;; pvar
;; predconst
;; idpredconst
;; idpredconst-op

;; atom
;; predapp
;; pred-infix
;; imp-op
;; and-op
;; tensor-op
;; or-op
;; all-op
;; ex-op
;; allnc-op
;; exd-op
;; exl-op
;; exr-op
;; exnc-op
;; exdt-op
;; exlt-op
;; exrt-op
;; exnct-op
;; exca-op
;; excl-op
;; excu-op
;; cterm

(define DOT-NOTATION #f)

(define (separator-string string1 string2)
  (if (or (string=? "" string1) (string=? "" string2))
      ""
      (let ((c1 (string-ref string1 (- (string-length string1) 1)))
	    (c2 (string-ref string2 0)))
	(cond
	 ((and (char-alphabetic? c1) (char-alphabetic? c2)) " ")
	 ((and (char-numeric? c1) (char-numeric? c2)) " ")
	 ((and (char-special? c1) (char-special? c2)) " ")
	 ((and (char=? #\^ c1) (char-numeric? c2)) " ") ;resolves Q^1 vs Q^ 1
	 ((and (char=? #\' c1) (char-numeric? c2)) " ") ;resolves Q'1 vs Q' 1
	 ((and (char-alphabetic? c1) (char-numeric? c2)) " ")
	 ((and (char-numeric? c1) (char-alphabetic? c2)) " ") ;for readability
	 ((and (char=? #\^ c1) (char-alphabetic? c2)) " ") ;for readability
	 ((and (char=? #\' c1) (char-alphabetic? c2)) " ") ;for readability
	 (else "")))))

(define (token-tree-to-string token-tree)
  (case (token-tree-to-tag token-tree)
    ((number) (number-to-string (cadr token-tree)))
    ((alg atomic-type var const pvar predconst idpredconst atom)
     (apply string-append
	    (token-tree-to-op-string token-tree)
	    (map token-tree-to-string (token-tree-to-args token-tree))))
    ((idpredconst-op)
     (apply string-append
	    "(" (token-tree-to-op-string token-tree)
	    (append (map (lambda (arg)
			   (string-append " " (token-tree-to-string arg)))
			 (token-tree-to-args token-tree))
		    (list ")"))))
    ((alg-typeop)
     (apply string-append
	    (token-tree-to-op-string token-tree)
	    (map (lambda (arg)
		   (if (< (token-tree-tag-to-precedence
			   (token-tree-to-tag arg))
			  (token-tree-tag-to-precedence 'atomic-type))
		       (string-append "(" (token-tree-to-string arg) ")")
		       (string-append " " (token-tree-to-string arg))))
		 (token-tree-to-args token-tree))))
    ((binding-op)
     (let* ((varstrings-and-kernel
	     (token-tree-to-varstrings-and-kernel token-tree))
	    (varstrings (car varstrings-and-kernel))
	    (kernel (cadr varstrings-and-kernel))
	    (comma-string (do ((l (cdr varstrings) (cdr l))
			       (res (car varstrings)
				    (string-append res "," (car l))))
			      ((null? l) res))))
       (string-append "[" comma-string "]"
		      (token-tree-to-string kernel))))
    ((all-op ex-op allnc-op
	     exd-op exl-op exr-op exnc-op
	     exdt-op exlt-op exrt-op exnct-op)
     (let* ((init-string
	     (case (token-tree-to-tag token-tree)
	       ((all-op) "all ")
	       ((ex-op) "ex ")
	       ((allnc-op) "allnc ")
	       ((exd-op exdt-op) "exd ")
	       ((exl-op exlt-op) "exl ")
	       ((exr-op exrt-op) "exr ")
	       ((exnc-op exnct-op) "exnc ")
	       (else (myerror "token-tree-to-string" "unexpected tag" tag))))
	    (varstrings-and-kernel
	     (token-tree-to-varstrings-and-kernel token-tree))
	    (varstrings (car varstrings-and-kernel))
	    (kernel (cadr varstrings-and-kernel))
	    (comma-string (do ((l (cdr varstrings) (cdr l))
			       (res (car varstrings)
				    (string-append res "," (car l))))
			      ((null? l) res)))
	    (kernel-string
	     (if (or (quant-token-tree? kernel) (prime-token-tree? kernel))
		 (token-tree-to-string kernel)
		 (if DOT-NOTATION
		     (string-append "." (token-tree-to-string kernel))
		     (string-append "(" (token-tree-to-string kernel) ")"))))
	    (sep-string (separator-string comma-string kernel-string)))
       (string-append init-string comma-string sep-string kernel-string)))
    ((exca-op excl-op excu-op)
     (let* ((init-string
	     (case (token-tree-to-tag token-tree)
	       ((exca-op) "exca ")
	       ((excl-op) "excl ")
	       ((excu-op) "excu ")
	       (else (myerror "token-tree-to-string" "unexpected tag" tag))))
	    (varstrings-and-kernel
	     (token-tree-to-varstrings-and-kernel token-tree))
	    (varstrings (car varstrings-and-kernel))
	    (kernel (cadr varstrings-and-kernel))
	    (comma-string (do ((l (cdr varstrings) (cdr l))
			       (res (car varstrings)
				    (string-append res "," (car l))))
			      ((null? l) res)))
	    (kernel-string
	     (if (or (quant-token-tree? kernel) (prime-token-tree? kernel))
		 (token-tree-to-string kernel)
		 (if DOT-NOTATION
		     (string-append "." (token-tree-to-string kernel))
		     (string-append "(" (token-tree-to-string kernel) ")"))))
	    (sep-string (separator-string comma-string kernel-string)))
       (string-append init-string comma-string sep-string kernel-string)))
    ((cterm)
     (string-append
      "("
      (token-tree-to-op-string token-tree) ;"cterm (vars) "
      (token-tree-to-string (car (token-tree-to-args token-tree)))
      ")"))
    ((prefix-typeop prefix-op)
     (let* ((args (token-tree-to-args token-tree))
	    (arg (if (pair? args) (car args)
		     (myerror "token-tree-to-string" "token-tree expected"
			      token-tree)))
	    (arg-string (token-tree-to-string arg))
	    (op-string (token-tree-to-op-string token-tree))
	    (prec-op (token-tree-tag-to-precedence
		      (token-tree-to-tag token-tree)))
	    (prec-arg (token-tree-tag-to-precedence (token-tree-to-tag arg))))
       (if (<= prec-op prec-arg)
	   (string-append
	    op-string (separator-string op-string arg-string) arg-string)
	   (string-append op-string "(" arg-string ")"))))
    ((postfix-typeop postfix-op)
     (let* ((args (token-tree-to-args token-tree))
	    (arg (if (pair? args) (car args)
		     (myerror "token-tree-to-string" "token-tree expected"
			      token-tree)))
	    (arg-string (token-tree-to-string arg))
	    (op-string (token-tree-to-op-string token-tree))
	    (prec-op (token-tree-tag-to-precedence
		      (token-tree-to-tag token-tree)))
	    (prec-arg (token-tree-tag-to-precedence (token-tree-to-tag arg))))
       (if (<= prec-op prec-arg)
	   (string-append
	    arg-string (separator-string arg-string op-string) op-string)
	   (string-append "(" arg-string ")" op-string))))
					;next the infix operators
    ((arrow-typeop prod-typeop tensor-typeop sum-typeop appterm pair-op
		   rel-op add-op mul-op exp-op imp-op and-op tensor-op or-op
		   predapp pred-infix caseitem-op)
     (let* ((args (token-tree-to-args token-tree))
	    (arg1 (if (pair? args) (car args)
		      (myerror "token-tree-to-string" "token-tree expected"
			       token-tree)))
	    (tag1 (token-tree-to-tag arg1))
	    (string1 (token-tree-to-string arg1))
	    (arg2 (if (pair? (cdr args)) (cadr args)
		      (myerror "token-tree-to-string" "token-tree expected"
			       token-tree)))
	    (tag2 (token-tree-to-tag arg2))
	    (string2 (token-tree-to-string arg2))
	    (op-string (token-tree-to-op-string token-tree))
	    (prec-op (token-tree-to-precedence token-tree))
	    (prec-arg1 (token-tree-to-precedence arg1))
	    (prec-arg2 (token-tree-to-precedence arg2))
	    (left-string
	     (if (or (< prec-arg1 prec-op)
		     (and (= prec-arg1 prec-op)
			  (not (token-tree-tag-left-assoc? tag1)))
		     (if DOT-NOTATION
			 (composed-with-quant-composed? arg1)
			 #f))
		 (string-append "(" string1 ")")
		 (string-append string1 (separator-string string1 op-string))))
	    (right-string
	     (if
	      (or (< prec-arg2 prec-op)
		  (and (= prec-arg2 prec-op)
		       (not (token-tree-tag-right-assoc? tag2)))
		  (if DOT-NOTATION
		      (and (eq? (token-tree-to-tag token-tree) 'and-op)
			   (not (quant-token-tree? arg2))
			   (not (prime-token-tree? arg2)))
		      #f))
	      (string-append "(" string2 ")")
	      (string-append (separator-string op-string string2) string2))))
       (string-append left-string
		      (if (string=? op-string "")
			  (separator-string left-string right-string)
			  op-string)
		      right-string)))
    ((if-op case-op)
     (apply
      string-append
      "[" (token-tree-to-op-string token-tree)
      (append (map (lambda (arg)
		     (if (< (token-tree-tag-to-precedence
			     (token-tree-to-tag arg))
			    (token-tree-tag-to-precedence 'atomic-term))
			 (string-append " (" (token-tree-to-string arg) ")")
			 (string-append " " (token-tree-to-string arg))))
		   (token-tree-to-args token-tree))
	      (list "]"))))
    (else (myerror "token-tree-to-string" "unknown token-tree-tag"
		   (token-tree-to-tag token-tree)))))

(define (token-tree-to-varstrings-and-kernel token-tree)
  (let ((tag1 (token-tree-to-tag token-tree)))
    (case tag1
      ((binding-op all-op ex-op allnc-op
		   exd-op exl-op exr-op exnc-op
		   exdt-op exlt-op exrt-op exnct-op)
       (let* ((arg (car (token-tree-to-args token-tree)))
	      (tag2 (token-tree-to-tag arg)))
	 (if (eq? tag1 tag2)
	     (let ((prev (token-tree-to-varstrings-and-kernel arg)))
	       (list (cons (token-tree-to-op-string token-tree) (car prev))
		     (cadr prev)))
	     (list (list (token-tree-to-op-string token-tree)) arg))))
      ((exca-op excl-op excu-op)
       (cons (token-tree-to-op-string token-tree) ;varstrings in this case
	     (token-tree-to-args token-tree)))
      (else (list '() token-tree)))))

(define (token-tree-tag-left-assoc? tttag)
  (memq tttag
	'(appterm add-op mul-op exp-op predapp)))

(define (token-tree-tag-right-assoc? tttag)
  (memq tttag
	'(prod-typeop tensor-typeop sum-typeop arrow-typeop pair-op
		      tensor-op imp-op and-op or-op)))

(define (token-tree-to-precedence token-tree)
  (token-tree-tag-to-precedence (token-tree-to-tag token-tree)))

(define (token-tree-tag-to-precedence tttag)
  (case tttag
    ((caseitem-op) 0)
    ((binding-op) 1)
    ((pair-op) 2)
    ((arrow-typeop imp-op) 3)
    ((sum-typeop or-op) 4)
    ((prod-typeop tensor-typeop and-op tensor-op) 5)
    ((rel-op pred-infix) 6)
    ((add-op) 7)
    ((mul-op) 8)
    ((exp-op) 9)
    ((appterm) 10)
    ((alg-typeop) 11)
    ((prefix-typeop prefix-op) 12)
    ((postfix-typeop postfix-op) 13)
    ((predapp) 14)
    ((alg atomic-type atomic-term const var number if-op case-op
	  pvar predconst idpredconst atom
	  all-op ex-op allnc-op exd-op exl-op exr-op exnc-op
	  exdt-op exlt-op exrt-op exnct-op exca-op excl-op excu-op
	   idpredconst-op cterm) 15)
    (else (myerror
	   "token-tree-tag-to-precedence" "token-tree-tag expected" tttag))))

(define (composed-token-tree? token-tree)
  (< (token-tree-to-precedence token-tree)
     (token-tree-tag-to-precedence 'atom)))

(define (prime-token-tree? token-tree)
  (memq (token-tree-to-tag token-tree)
	(list 'pred-infix 'predapp 'pvar 'predconst
	      'idpredconst 'idpredconst-op 'atom)))

(define (quant-token-tree? token-tree)
  (memq (token-tree-to-tag token-tree)
	'(all-op ex-op allnc-op exd-op exl-op exr-op exnc-op
		 exdt-op exlt-op exrt-op exnct-op exca-op excl-op excu-op)))

(define (quant-prime-token-tree? token-tree)
  (or (and (quant-token-tree? token-tree)
	   (quant-prime-token-tree? (car (token-tree-to-args token-tree))))
      (prime-token-tree? token-tree)))

(define (composed-with-quant-composed? token-tree)
  (or (and (quant-token-tree? token-tree)
	   (not (quant-prime-token-tree? token-tree)))
      (and (memq (token-tree-to-tag token-tree)
		 (list 'imp-op 'and-op 'tensor-op))
	   (composed-with-quant-composed?
	    (cadr (token-tree-to-args token-tree))))))

;; Now we adapt pp.scm (written originally by Stefan Schimanski), to
;; also introduce line breaks.

;; Main idea: compute the width of all trees, as if there were no line
;; break.  Store in pp-tree the information when and where there should
;; be a line break.

(define PP-WIDTH 77)

;; The nodes of a pp-tree are quadruples: (1) width (if in one line),
;; (2) indentation (relative), (3) kind of node: string, cat, newline,
;; (4) a string (for kind string), or a list of subnodes (for kinds
;; cat, newline).  In case cat they are appended, in case newline the
;; first is appended and the rest is indented (with given indentation)

(define (make-pp-tree width indent kind rest)
  (list width indent kind rest))

(define pp-tree-to-width car)
(define pp-tree-to-indent cadr)
(define pp-tree-to-kind caddr)
(define pp-tree-to-rest cadddr) ;string or list of pp-trees

(define (make-pp-line string)
  (list (string-length string) 0 'string string))

;; pp-tree-start searches for the first character in pp-tree.

(define (pp-tree-start pptree)
  (if (eq? (caddr pptree) 'string)
      (if (= (string-length (cadddr pptree)) 0)
	  'unknown
	  (make-string 1 (string-ref (cadddr pptree) 0)))
      (letrec ((subtrees (cadddr pptree))
	       (find-char (lambda (ts)
			    (if (null? ts)
				'unknown
				(let ((c (pp-tree-start (car ts))))
				  (if (eq? c 'unknown)
				      (find-char (cdr ts))
				      c))))))
	(find-char subtrees))))

;; pp-tree-end searches for the last character in pp-tree.

(define (pp-tree-end pptree)
  (if (eq? (caddr pptree) 'string)
      (let* ((string (cadddr pptree))
	     (l (string-length string)))
	(if (= l 0)
	    'unknown
	    (make-string 1 (string-ref string (- l 1)))))
      (letrec ((subtrees (cadddr pptree))
	       (find-char (lambda (ts)
			    (if (null? ts)
				'unknown
				(let ((c (pp-tree-end (car ts))))
				  (if (eq? c 'unknown)
				      (find-char (cdr ts))
				      c))))))
	(find-char (reverse subtrees)))))

(define (token-tree-to-pp-tree token-tree)
  (case (car token-tree)
    ((number) (make-pp-line (number-to-string (cadr token-tree))))
    ((alg atomic-type var const pvar predconst idpredconst)
     (make-pp-line (token-tree-to-op-string token-tree)))
    ((idpredconst-op)
     (let* ((args (map (lambda (x)
			 (let ((x-tree (token-tree-to-pp-tree x)))
			   (make-pp-tree (+ (pp-tree-to-width x-tree) 1)
					 0
					 'cat
					 (list (make-pp-line " ")
					       x-tree))))
		       (token-tree-to-args token-tree)))
	    (width (- (apply + (map pp-tree-to-width args)) 1))
	    (prefix (make-pp-line
		     (string-append "(" (token-tree-to-op-string token-tree))))
	    (postfix (make-pp-line ")")))
       (make-pp-tree
	(+ (pp-tree-to-width prefix) width (pp-tree-to-width postfix)) 0 'cat
	(list
	 (make-pp-tree
	  (+ (pp-tree-to-width prefix) width) 1 'newline
	  (cons (make-pp-tree (+ (pp-tree-to-width prefix)
				 (pp-tree-to-width (car args)))
			      0
			      'cat
			      (list prefix
				    (make-pp-tree
				     (pp-tree-to-width (car args))
				     (+ (pp-tree-to-width prefix) 1)
				     'cat
				     (list (car args)))))
		(cdr args)))
	 postfix))))
    ((atom)
     (cond
      ((string=? "T" (token-tree-to-op-string token-tree))
       (make-pp-line "T"))
      ((string=? "F" (token-tree-to-op-string token-tree))
       (make-pp-line "F"))
      (else (token-tree-to-pp-tree (car (token-tree-to-args token-tree))))))
    ((alg-typeop)
     (make-pp-line
      (apply
       string-append
       (cons (token-tree-to-op-string token-tree)
	     (map (lambda (arg)
		    (if (< (token-tree-tag-to-precedence
			    (token-tree-to-tag arg))
			   (token-tree-tag-to-precedence 'atomic-type))
			(string-append "(" (token-tree-to-string arg) ")")
			(string-append " " (token-tree-to-string arg))))
		  (token-tree-to-args token-tree))))))
    ((binding-op)
     (let* ((varstrings-and-kernel
	     (token-tree-to-varstrings-and-kernel token-tree))
	    (varstrings (car varstrings-and-kernel))
	    (kernel (cadr varstrings-and-kernel))
	    (comma-string (do ((l (cdr varstrings) (cdr l))
			       (res (car varstrings)
				    (string-append res "," (car l))))
			      ((null? l) res)))
	    (prefix (string-append "[" comma-string "]"))
	    (prefix-width (string-length prefix))
	    (postfix (token-tree-to-pp-tree kernel))
	    (postfix-width (pp-tree-to-width postfix)))
       (make-pp-tree (+ prefix-width postfix-width) 1 'newline
		     (list (make-pp-line prefix) postfix))))
    ((all-op ex-op allnc-op
	     exd-op exl-op exr-op exnc-op
	     exdt-op exlt-op exrt-op exnct-op
	     exca-op excl-op excu-op)
     (let* ((init-string
	     (case (token-tree-to-tag token-tree)
	       ((all-op) "all ")
	       ((ex-op) "ex ")
	       ((allnc-op) "allnc ")
	       ((exd-op exdt-op) "exd ")
	       ((exl-op exlt-op) "exl ")
	       ((exr-op exrt-op) "exr ")
	       ((exnc-op exnct-op) "exnc ")
	       ((exca-op) "exca ")
	       ((excl-op) "excl ")
	       ((excu-op) "excu ")
	       (else (myerror "token-tree-to-pp-tree" "unexpected tag"
			       (token-tree-to-tag token-tree)))))
	    (varstrings-and-kernel
	     (token-tree-to-varstrings-and-kernel token-tree))
	    (varstrings (car varstrings-and-kernel))
	    (kernel (cadr varstrings-and-kernel))
	    (comma-string (do ((l (cdr varstrings) (cdr l))
			       (res (car varstrings)
				    (string-append res "," (car l))))
			      ((null? l) res)))
	    (qp? (or (quant-token-tree? kernel) (prime-token-tree? kernel)))
	    (prefix (string-append init-string comma-string
				   (if qp? " " (if DOT-NOTATION "." "("))))
	    (kernel-pp-tree (token-tree-to-pp-tree kernel))
	    (postfix (if (or qp? DOT-NOTATION)
			 kernel-pp-tree
			 (make-pp-tree
			  (+ (pp-tree-to-width kernel-pp-tree) 1)
			  0
			  'cat
			  (list kernel-pp-tree (make-pp-line ")")))))
	    (prefix-width (string-length prefix))
	    (postfix-width (pp-tree-to-width postfix)))
       (make-pp-tree (+ prefix-width postfix-width) 1 'newline
		     (list (make-pp-line prefix) postfix))))
    ((cterm)
     (let* ((op-string (token-tree-to-op-string token-tree)) ;"cterm (vars) "
	    (prefix (string-append "(" op-string))
	    (formula-pp-tree (token-tree-to-pp-tree
			      (car (token-tree-to-args token-tree))))
	    (postfix (make-pp-tree
		      (+ (pp-tree-to-width formula-pp-tree) 1)
		      0
		      'cat
		      (list formula-pp-tree (make-pp-line ")"))))
	    (prefix-width (string-length prefix))
	    (postfix-width (pp-tree-to-width postfix)))
       (make-pp-tree (+ prefix-width postfix-width) 1 'newline
		     (list (make-pp-line prefix) postfix))))
    ((prefix-typeop prefix-op)
     (let* ((arg-token-trees (token-tree-to-args token-tree))
	    (arg-token-tree (if (pair? arg-token-trees) (car arg-token-trees)
				(myerror "token-tree-to-pp-tree"
					 "token-tree expected" token-tree)))
	    (arg (token-tree-to-pp-tree arg-token-tree))
	    (op (token-tree-to-op-string token-tree))
	    (prec-op (token-tree-tag-to-precedence
		      (token-tree-to-tag token-tree)))
	    (prec-arg (token-tree-tag-to-precedence
		       (token-tree-to-tag arg-token-tree)))
	    (prefix
	     (make-pp-line (if (<= prec-op prec-arg)
			       (string-append
				op (separator-string op (pp-tree-start arg)))
			       (string-append op "("))))
	    (postfix (make-pp-line (if (> prec-op prec-arg) ")" ""))))
       (make-pp-tree (+ (pp-tree-to-width prefix)
			(pp-tree-to-width arg)
			(pp-tree-to-width postfix))
		     (pp-tree-to-width prefix)
		     'cat
		     (list prefix arg postfix))))
    ((postfix-typeop postfix-op)
     (let* ((arg-token-trees (token-tree-to-args token-tree))
	    (arg-token-tree (if (pair? arg-token-trees) (car arg-token-trees)
				(myerror "token-tree-to-pp-tree"
					 "token-tree expected" token-tree)))
	    (arg (token-tree-to-pp-tree arg-token-tree))
	    (op (token-tree-to-op-string token-tree))
	    (prec-op (token-tree-tag-to-precedence
		      (token-tree-to-tag token-tree)))
	    (prec-arg (token-tree-tag-to-precedence
		       (token-tree-to-tag arg-token-tree)))
	    (prefix (make-pp-line (if (> prec-op prec-arg) "(" "")))
	    (postfix
	     (make-pp-line (if (<= prec-op prec-arg)
			       (string-append
				(separator-string (pp-tree-end arg) op) op)
			       (string-append ")" op)))))
       (make-pp-tree (+ (pp-tree-to-width prefix)
			(pp-tree-to-width arg)
			(pp-tree-to-width postfix))
		     (pp-tree-to-width prefix)
		     'cat
		     (list prefix arg postfix))))
					;next the infix operators:
    ((arrow-typeop prod-typeop tensor-typeop sum-typeop appterm pair-op
		   rel-op add-op mul-op exp-op imp-op and-op tensor-op or-op
		   predapp pred-infix caseitem-op)
     (let* ((arg-token-trees (token-tree-to-args token-tree))
	    (arg-token-tree1 (if (pair? arg-token-trees) (car arg-token-trees)
				 (myerror "token-tree-to-pp-tree"
					  "token-tree expected" token-tree)))
	    (tag1 (token-tree-to-tag arg-token-tree1))
	    (arg1 (token-tree-to-pp-tree arg-token-tree1))
	    (arg-token-tree2 (if (pair? (cdr arg-token-trees))
				 (cadr arg-token-trees)
				 (myerror "token-tree-to-pp-tree"
					  "token-tree expected" token-tree)))
	    (tag2 (token-tree-to-tag arg-token-tree2))
	    (arg2 (token-tree-to-pp-tree arg-token-tree2))
	    (op-string (token-tree-to-op-string token-tree))
	    (prec-op (token-tree-to-precedence token-tree))
	    (prec-arg1 (token-tree-to-precedence arg-token-tree1))
	    (prec-arg2 (token-tree-to-precedence arg-token-tree2))
	    (arg1-prefix (make-pp-line ""))
	    (arg1-postfix (make-pp-line ""))
	    (arg2-prefix (make-pp-line ""))
	    (arg2-postfix (make-pp-line "")))
       (if (or (< prec-arg1 prec-op)
	       (and (= prec-arg1 prec-op)
		    (not (token-tree-tag-left-assoc? tag1)))
	       (if DOT-NOTATION
		   (composed-with-quant-composed? arg-token-tree1)
		   #f))
	   (begin (set! arg1-prefix (make-pp-line "("))
		  (set! arg1-postfix (make-pp-line ")")))
	   (set! arg1-postfix
		 (make-pp-line
		  (separator-string (pp-tree-end arg1) op-string))))
       (if (or (< prec-arg2 prec-op)
	       (and (= prec-arg2 prec-op)
		    (not (token-tree-tag-right-assoc? tag2)))
	       (if DOT-NOTATION
		   (and (eq? (token-tree-to-tag token-tree) 'and-op)
			(not (quant-token-tree? arg-token-tree2))
			(not (prime-token-tree? arg-token-tree2)))
		   #f))
	   (begin (set! arg2-prefix (make-pp-line "("))
		  (set! arg2-postfix (make-pp-line ")"))))
       (let* ((arg1-tree (make-pp-tree (+ (pp-tree-to-width arg1-prefix)
					  (pp-tree-to-width arg1)
					  (pp-tree-to-width arg1-postfix))
				       (pp-tree-to-width arg1-prefix)
				       'cat
				       (list arg1-prefix arg1 arg1-postfix)))
	      (arg2-tree (make-pp-tree (+ (pp-tree-to-width arg2-prefix)
					  (pp-tree-to-width arg2)
					  (pp-tree-to-width arg2-postfix))
				       (pp-tree-to-width arg2-prefix)
				       'cat
				       (list arg2-prefix arg2 arg2-postfix)))
	      (op (if (string=? op-string "")
		      (make-pp-line (separator-string
				     (pp-tree-end arg1-tree)
				     (pp-tree-start arg2-tree)))
		      (make-pp-line op-string)))
	      (arg1-op-tree (make-pp-tree (+ (pp-tree-to-width arg1-tree)
					     (pp-tree-to-width op))
					  0
					  'cat
					  (list arg1-tree op)))
	      (op-arg2-sep (make-pp-line (separator-string
					  (pp-tree-end arg1-op-tree)
					  (pp-tree-start arg2-tree))))
	      (arg1-op-sep-tree
	       (make-pp-tree (+ (pp-tree-to-width arg1-op-tree)
				(pp-tree-to-width op-arg2-sep))
			     0
			     'cat
			     (list arg1-op-tree op-arg2-sep))))
	 (make-pp-tree (+ (pp-tree-to-width arg1-op-sep-tree)
			  (pp-tree-to-width arg2-tree))
		       0
		       'newline
		       (list arg1-op-sep-tree arg2-tree)))))
    ((if-op case-op)
     (let* ((args (map (lambda (x)
			 (let ((x-tree (token-tree-to-pp-tree x)))
			   (if (< (token-tree-tag-to-precedence
				   (token-tree-to-tag x))
				  (token-type-to-precedence 'atomic-term))
			       (make-pp-tree (+ (pp-tree-to-width x-tree) 3)
					     1
					     'cat
					     (list (make-pp-line " (")
						   x-tree
						   (make-pp-line ")")))
			       (make-pp-tree (+ (pp-tree-to-width x-tree) 1)
					     0
					     'cat
					     (list (make-pp-line " ")
						   x-tree)))))
		       (token-tree-to-args token-tree)))
	    (width (- (apply + (map pp-tree-to-width args)) 1))
	    (prefix (make-pp-line
		     (string-append "[" (token-tree-to-op-string token-tree))))
	    (postfix (make-pp-line "]")))
       (make-pp-tree
	(+ (pp-tree-to-width prefix) width (pp-tree-to-width postfix)) 0 'cat
	(list
	 (make-pp-tree
	  (+ (pp-tree-to-width prefix) width) 1 'newline
	  (cons (make-pp-tree (+ (pp-tree-to-width prefix)
				 (pp-tree-to-width (car args)))
			      0
			      'cat
			      (list prefix
				    (make-pp-tree
				     (pp-tree-to-width (car args))
				     (+ (pp-tree-to-width prefix) 1)
				     'cat
				     (list (car args)))))
		(cdr args)))
	 postfix))))
    (else (myerror "token-tree-to-pp-tree" "unknown token-tree-tag"
		   (token-tree-to-tag token-tree)))))

;; From pp-tree we first generate a list of lines;; each line is a list
;; of an indentation and a string.

;; pp-tree-line-append appends s to the last line of lines, if there is
;; one.  Otherwise a new line with indentation i and string s is
;; created.

(define (pp-tree-line-append lines i s)
  (if (null? lines)
      (list (list i ss))
      (if (null? (cdr lines))
	  (list (list (caar lines)
		      (string-append (cadar lines) s)))
	  (cons (car lines)
		(pp-tree-line-append (cdr lines) i s)))))

(define (pp-tree-to-lines i len pptree)
  (cond
   ((eq? 'string (pp-tree-to-kind pptree))
    (list (list i (pp-tree-to-rest pptree))))
   ((or (eq? 'cat (pp-tree-to-kind pptree))
	(< (+ i (pp-tree-to-width pptree)) len)) ;cat or newline without cr
    (let* ((prec-pptrees (pp-tree-to-rest pptree))
	   (indent (pp-tree-to-indent pptree))
	   (lines-list
	    (map (lambda (y) (pp-tree-to-lines (+ i indent) len y))
		 prec-pptrees)))
      (do ((l lines-list (cdr l))
	   (res (list (list i ""))
		(append (pp-tree-line-append res (caaar l) (cadaar l))
			(cdar l))))
	  ((null? l) res))))
   (else ;newline
    (let* ((lines-list
	    (letrec ((pp-trees-to-indented-lines-list
		      (lambda (ys)
			(if (null? ys) '()
			    (cons (pp-tree-to-lines
				   (+ i (pp-tree-to-indent pptree))
				   len
				   (car ys))
				  (pp-trees-to-indented-lines-list
				   (cdr ys)))))))
	      (pp-trees-to-indented-lines-list (pp-tree-to-rest pptree))))
	   (lines (apply append lines-list)))
      (if (not (null? lines))
	  (set-car! (car lines) i))
      lines))))

(define (pp-tree-lines-to-string lines)
  (let ((strings (cons (string-append (make-string (caar lines) #\space)
				      (cadar lines))
		       (map (lambda (line)
			      (string-append (make-string 1 #\newline)
					     (make-string (car line) #\space)
					     (cadr line)))
			    (cdr lines)))))
    (apply string-append strings)))

;; The first line is not indented.  The following lines are indented by
;; "indent" many spaces:

(define (pretty-print-string indent width x)
  (let ((pptree
	 (cond
	  ((term-form? x)
	   (token-tree-to-pp-tree
	    (term-to-token-tree x)))
	  ((formula-form? x)
	   (token-tree-to-pp-tree
	    (formula-to-token-tree x)))
	  ((string? x)
	   (token-tree-to-pp-tree
	    (formula-to-token-tree
	     (let ((info1 (assoc x THEOREMS)))
	       (if info1
		   (fold-formula
		    (rename-variables
		     (proof-to-formula (theorem-name-to-proof x))))
		   (let ((info2 (assoc x GLOBAL-ASSUMPTIONS)))
		     (if info2
			 (fold-formula
			  (rename-variables (aconst-to-formula (cadr info2))))
			 (myerror
			  "pretty-print"
			  "name of theorem or global assumption expected"
			  x))))))))
	  ((type-form? x)
	   (token-tree-to-pp-tree (type-to-token-tree x)))
	  (else (myerror "pretty-print" "unexpected argument" x)))))
    (set-car! (cdr pptree) (+ indent (cadr pptree)))
    (pp-tree-lines-to-string (pp-tree-to-lines 0 width pptree))))

(define (pretty-print x)
  (if COMMENT-FLAG
      (begin (display (pretty-print-string 0 PP-WIDTH x))
	     (newline))))

(define pp pretty-print)

(define (pretty-print-with-case-display x)
  (if COMMENT-FLAG
      (begin (set! OLD-CASE-DISPLAY CASE-DISPLAY)
	     (set! CASE-DISPLAY #t)
	     (display (pretty-print-string 0 PP-WIDTH x))
	     (set! CASE-DISPLAY OLD-CASE-DISPLAY)
	     (newline))))

(define ppc pretty-print-with-case-display)

;; We now define display functions for types, terms and formulas via
;; token-tree-to-string.

(define (type-to-string x)
  (token-tree-to-string (type-to-token-tree x)))

(define (type-to-space-free-string type)
  (list->string
   (map (lambda (c) (if (char=? c #\space) #\- c))
	(string->list (type-to-string type)))))

(define (term-to-string x)
  (token-tree-to-string (term-to-token-tree x)))

(define (formula-to-string x)
  (token-tree-to-string (formula-to-token-tree x)))

;; For backward compatibility we keep
(define (predicate-form-to-string formula)
  (formula-to-string formula))

(define (display-formula formula)
  (display (formula-to-string formula)))

(define df display-formula)

;; For display of comprehension terms we use

(define (cterm-to-string cterm)
  (let ((vars (cterm-to-vars cterm))
	(formula (cterm-to-formula cterm)))
    (string-append "(cterm " (vars-to-string vars) " "
		   (formula-to-string formula) ")")))
