; $Id: lr-dvr.scm 2198 2008-03-26 09:38:32Z schwicht $
;; ---------------------------------------------------------------------- ;;
;; FICHIER               : lr-dvr.scm                                     ;;
;; DATE DE CREATION      : Fri May 31 15:47:05 1996                       ;;
;; DERNIERE MODIFICATION : Fri May 31 15:51:13 1996                       ;;
;; ---------------------------------------------------------------------- ;;
;; Copyright (c) 1996 Dominique Boucher                                   ;;
;; ---------------------------------------------------------------------- ;;
;; The LR parser driver                                                   ;;
;;                                                                        ;;
;; lr-dvr.scm is part of the lalr.scm distribution which is free          ;;
;; software; you can redistribute it and/or modify                        ;;
;; it under the terms of the GNU General Public License as published by   ;;
;; the Free Software Foundation; either version 2, or (at your option)    ;;
;; any later version.                                                     ;;
;;                                                                        ;;
;; lalr.scm is distributed in the hope that it will be useful,            ;;
;; but WITHOUT ANY WARRANTY; without even the implied warranty of         ;;
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the          ;;
;; GNU General Public License for more details.                           ;;
;;                                                                        ;;
;; You should have received a copy of the GNU General Public License      ;;
;; along with lalr.scm; see the file COPYING.  If not, write to           ;;
;; the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.  ;;
;; ---------------------------------------------------------------------- ;;

(define max-stack-size 500)
(define lr-dvr-debug #f)

(define (push stack sp new-cat goto-table lval)
  (let* ((state     (vector-ref stack sp))
	 (new-state (cdr (assq new-cat (vector-ref goto-table state))))
	 (new-sp    (+ sp 2)))
    (if (>= new-sp max-stack-size)
	(myerror "PARSE ERROR" "stack overflow")
	(begin
	  (vector-set! stack new-sp new-state)
	  (vector-set! stack (- new-sp 1) lval)
	  new-sp))))

(define current-token "")

(define (make-parser action-table goto-table reduction-table token-defs)
  (lambda (lexerp errorp)

    (define (action x l)
      (let ((y (assq x l)))
	(if y
	    (cdr y)
	    (cdar l))))

    (let ((stack (make-vector max-stack-size 0)))
      (let loop ((sp 0) (input (lexerp)))
	(let* ((state (vector-ref stack sp))
	       (i     (car input))
	       (act   (action i (vector-ref action-table state))))

	  (if lr-dvr-debug
	      (begin
		(display "** PARSER TRACE:")
		(display "  input=")
		(display input)
		(display "  i=")
		(display (vector-ref token-defs i))
		(display "  state=")
		(display state)
		(display "  sp=")
		(display sp)
		(newline)))

	  (cond

	   ;Input successfully parsed
	   ((eq? act 'accept)
	    (vector-ref stack 1))

	   ;Syntax error in input
	   ((eq? act '*error*)
	    (errorp "PARSE ERROR : unexpected token"
		    (string-append
		     (vector-ref token-defs i) " "
		     (if (string? (cdr input))
			 (cdr input) ""))
		    (lexerp #t))) ;cause the lexer to output current position

	   ;Shift current token on top of the stack
	   ((>= act 0)
	    (vector-set! stack (+ sp 1) (cdr input))
	    (vector-set! stack (+ sp 2) act)
	    (set! current-token CURRENT-INPUT)
	    (loop (+ sp 2) (lexerp)))

	   ;Reduce by rule (- act)
	   (else
	    (loop ((vector-ref reduction-table (- act)) stack sp goto-table)
		  input))))))))

(define (token-string? string)
  (let ((l (string->list string)))
    (or (apply and-op (map char-alphabetic? l))
	(apply and-op (map char-special? l)))))

(define (hashindex char-list hsize)
; Warning a copy of this function is in lalr.scm
; to insert predefined tokens into the hashtable
; either change both or neither
  (let loop ((i 0) (l char-list))
    (if (null? l)
	(modulo i hsize)
	(loop (+ (* i 7) (char->integer (car l))) (cdr l)))))

(define (make-add-token token-table token-nrs)
  (let ((hsize (vector-length token-table)))
    (lambda (string token value)
      (let* ((token-nr (assoc token token-nrs))
	     (hindex (hashindex (string->list string) hsize))
	     (hlist (vector-ref token-table hindex)))
	(cond ((not token-nr)
	       (myerror "Not a valid tokenclass for " string))
	      ((not (token-string? string))
	       (myerror "Not a valid token string " string))
	      ((assoc string hlist)
	       (myerror "Attempt to redefine token" string))
	      (else
	       (vector-set! token-table hindex
			    (cons
			     (cons string (cons (cdr token-nr) value))
			     hlist))))))))

(define (make-remove-token token-table token-nrs)
  (letrec
      ((hsize (vector-length token-table))
       (remove (lambda (list string)
		 (if (null? list)
		     (myerror "Attempt to remove a non-existing token" string)
		     (if (string=? string (caar list))
			 (cdr list)
			 (cons (car list) (remove (cdr list) string)))))))
    (lambda (string)
      (let ((hindex (hashindex (string->list string) hsize)))
	(vector-set! token-table hindex
		     (remove (vector-ref token-table hindex) string))))))

(define (make-is-token? token-table token-defs)
  (letrec
      ((hsize (vector-length token-table))
       (info (lambda (list string)
		 (if (null? list)
		     #f
		     (if (string=? string (caar list))
			 (cons
			  (string->symbol (vector-ref token-defs (cadar list)))
			  (cddar list))
			 (info (cdr list) string))))))
    (lambda (string)
      (let ((hindex (hashindex (string->list string) hsize)))
	(info (vector-ref token-table hindex) string)))))

(define (char-punctuation? c)
  (or (char=? c #\( )
      (char=? c #\) )
      (char=? c #\[ )
      (char=? c #\] )
      (char=? c #\{ )
      (char=? c #\} )
      (char=? c #\. )
      (char=? c #\; )
      (char=? c #\, )
      (char=? c #\" ) ))

(define (char-special? c)
  (and (not (char-alphabetic? c))
       (not (char-whitespace? c))
       (not (char-punctuation? c))
       (not (char-numeric? c))))

(define CURRENT-INPUT "")

(define (make-lexer token-table token-nrs)
  (let ( (number-nr (cdr (assoc 'number token-nrs)))
	 (hat-nr (cdr (assoc 'hat token-nrs)))
	 (prime-nr (cdr (assoc 'prime token-nrs)))
	 (underscore-nr (cdr (assoc 'underscore token-nrs)))
	 (hatprime-nr (cdr (assoc 'hatprime token-nrs)))
	 (hatprimeunderscore-nr (cdr (assoc 'hatprimeunderscore token-nrs)))
	 (hatunderscore-nr (cdr (assoc 'hatunderscore token-nrs)))
	 (primeunderscore-nr (cdr (assoc 'primeunderscore token-nrs)))
	 (tvar-name-nr (cdr (assoc 'tvar-name token-nrs)))
	 (tconst-nr (cdr (assoc 'tconst token-nrs)))
	 (var-name-nr (cdr (assoc 'var-name token-nrs)))
	 (pvar-name-nr (cdr (assoc 'pvar-name token-nrs)))
	 (pvar-op-nr (cdr (assoc 'pvar-op token-nrs)))
	 (predconst-name-nr (cdr (assoc 'predconst-name token-nrs)))
	 (type-symbol-nr (cdr (assoc 'type-symbol token-nrs)))
	 (alg-nr (cdr (assoc 'alg token-nrs)))
	 (var-index-nr (cdr (assoc 'var-index token-nrs)))
 	 (string-nr (cdr (assoc 'string token-nrs)))
         (undefined-token-nr (cdr (assoc 'undefined-token token-nrs)))
        )
  (lambda (reader)
    (letrec
       ((current (reader))

	(previous-nr 0) ;contains the number of the previous token
                        ;or 0 for whitespace

	(next (lambda ()
		(set! current (reader))))

	(lex-number
	 (lambda (n)
	   (let ((m (+ (* 10 n) (- (char->integer current)
				   (char->integer #\0)))))
            (begin
               (next)
               (if (and current (char-numeric? current))
		     (lex-number m)
		     m)))))

       (lex-string
	(lambda ()
          (next)
	  (if current
              (if (char=? current #\" )
		  (begin (next) '())
		  (if (char=? current #\\ )
		      (begin (next) (cons current (lex-string)))
		      (cons current (lex-string))))
	      '())))

	(lex-symbol
	 (lambda ()
	   (let ((c current))
	     (if (and c (char-alphabetic? c))
		 (begin
		   (next)
		   (cons c (lex-symbol)))
		 '()))))


	(lex-special
	 (lambda ()
	   (let ((c current))
	     (if (and c (char-special? c))
		 (begin
		   (next)
		   (cons c (lex-special)))
		 '()))))

	(hsize (vector-length token-table))
	(lex-lookup
	 (lambda (char-list)
	   (let* ((hindex (hashindex char-list hsize))
		  (hlist (vector-ref token-table hindex))
		  (token (list->string char-list))
		  (t (assoc token hlist)))
	     (set! CURRENT-INPUT token)
	     (if t
		 (cdr t)
		 (cons undefined-token-nr (list->string char-list))))))

	(skip-comment
	 (lambda ()
	   (next)
	   (if (not (char=? current #\newline)) (skip-comment))))


	(lexical-analyser
	 (lambda args
	   (if (null? args)
	       (let loop ()
		 (if current
		     (let ((token
			    (cond
			     ((char-whitespace? current)
			      (set! previous-nr 0) (next) (loop))
			     ((char-numeric? current)
			      (if (or (= previous-nr tvar-name-nr)
				      (= previous-nr tconst-nr)
				      (= previous-nr var-name-nr)
				      (= previous-nr pvar-name-nr)
				      (= previous-nr predconst-name-nr)
				      (= previous-nr type-symbol-nr)
				      (= previous-nr alg-nr)
				      (= previous-nr hat-nr)
				      (= previous-nr underscore-nr)
				      (= previous-nr prime-nr)
				      (= previous-nr hatprime-nr)
				      (= previous-nr hatprimeunderscore-nr)
				      (= previous-nr hatunderscore-nr)
				      (= previous-nr primeunderscore-nr)
				      (= previous-nr pvar-op-nr))
				  (cons var-index-nr (lex-number 0))
				  (cons number-nr (lex-number 0))))
			     ((char=? current #\")
			      (cons string-nr (list->string (lex-string))))
			     ((char-punctuation? current)
			      (let ((token (lex-lookup (list current))))
				(next)
				token))
			     ((char-alphabetic? current)
			      (lex-lookup (lex-symbol)))
			     ((char=? current #\/)
			      (next)
			      (if (char=? current #\/)
				  (begin
				      (set! previous-nr 0)
				      (skip-comment)
				      (loop))
				  (lex-lookup (cons #\/ (lex-special)))))
			     (else (lex-lookup (lex-special))))))
		       (set! previous-nr (car token))
		       token)
		     '(0))) ;end of input
	       (reader #t)))))
	 lexical-analyser))))

(define (lexer-info terminal-table token-nrs)
  (define (insert l e) ;insert e = (string tokentype value)
     (if (null? l)     ;sorted by strings
	 (list e)
	 (if (string<? (car e) (caar l))
	     (cons e l)
	     (cons (car l) (insert (cdr l) e)))))
  (let  ((v (make-vector (length token-nrs) '())))
    (do ((i 0 (+ i 1)))
	((>= i (vector-length terminal-table)))
      (do ((l (vector-ref terminal-table i) (cdr l)))
	  ((null? l))
	(vector-set! v (cadar l) (insert (vector-ref v (cadar l)) (car l)))))
    (do ((i 0 (+ i 1))
	 (name token-nrs (cdr name)))
	((>= i (vector-length v)))
      (let ((l (vector-ref v i)))
	(if (pair? l)
	    (begin
	      (display (caar name)) (newline)
	      (do ((tl l (cdr tl)))
		  ((null? tl))
		(display tab)
		(display (caar tl))
	        (if (eq? 'var-name (caar name))
		    (begin
		      (display tab) (display ": ")
		      (display (if (caddar tl)
				   (type-to-string (caddar tl))))))
	        (if (eq? 'const (caar name))
		    (begin
		      (display tab) (display ": ")
		      (display (type-to-string (term-to-type (cddar tl))))))
		(newline))))))))

(define (string-reader string)
   (let ((pos 0)
         (l (string-length string)))
      (lambda args
         (if (null? args)
	     (if (< pos l)
		 (let ((c (string-ref string pos)))
		   (set! pos (+ pos 1))
		   c)
		 #f)
	     ;produce a string indicating current position
	     (if (> pos 20)
		 (string-append
		  (make-string 1 #\newline)
		  "..."
		  (substring string (- pos 17) (min (+ pos 20) l))
		  (make-string 1 #\newline)
                  (make-string 19 #\space)
		  "^")
		 (string-append
		  (make-string 1 #\newline)
		  (substring string 0 (min (+ pos 20) l))
		  (make-string 1 #\newline)
		  (make-string (if (zero? pos) pos (- pos 1))#\space)
		  "^"))))))

(define (port-reader filename port)
  (let ((line 1)
	(column 0))
    (lambda args
      (if (null? args)
	  (let ((c (read-char port)))
              (if (eof-object? c)
		  #f
		  (if (char=? c #\newline)
		      (begin
			(set! line (+ line 1))
			(set! column 0)
			c)
		      (begin
			(set! column (+ column 1))
			c))))
	  (string-append
	   (make-string 1 #\newline)
	   "; file: " filename
	   ", line: " (number->string line)
	   ", column: " (number->string (- column 1)))))))

