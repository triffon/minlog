;; $Id: list.scm 2657 2014-01-08 09:48:56Z schwicht $
;; 1. Preliminaries
;; ================

(define (list-head list k)
  (do ((l list (cdr l))
       (n 0 (+ n 1))
       (res '() (cons (car l) res)))
      ((= n k) (reverse res))))

(define (zip list1 list2)
  (do ((l1 list1 (cdr l1))
       (l2 list2 (cdr l2))
       (res '() (cons (car l2) (cons (car l1) res))))
      ((or (null? l1) (null? l2))
       (if (null? l1)
	   (if (null? l2)
	       (reverse res)
	       (append (reverse res) l2))
	   (append (reverse res) l1)))))

;; (zip '(1 3 5 ) '(2 4 6 ))
;; (1 2 3 4 5 6)

(define (rac xs)
  (let ((ys (cdr xs)))
    (if (null? ys) (car xs) (rac ys))))

(define (rdc xs)
  (let ((ys (cdr xs)))
    (if (null? ys) ys (cons (car xs) (rdc ys)))))

(define (snoc xs x)
  (if (null? xs)
      (list x)
      (cons (car xs) (snoc (cdr xs) x))))

(define (repeated f n)
  (cond ((= n 0) (lambda (x) x)) 
	((= n 1) f)
	(else (lambda (x) (f ((repeated f (- n 1)) x))))))

(define (remove x list)
  (do ((l list (cdr l))
       (res '() (if (equal? x (car l))
                    res
                    (cons (car l) res))))
      ((null? l) (reverse res))))

(define (adjoin x list) (if (member x list) list (cons x list)))

(define (remove-duplicates list)
  (do ((l list (cdr l))
       (res '() (if (member (car l) res)
                    res
                    (cons (car l) res))))
      ((null? l) (reverse res))))

(define (remove-common-head list1 list2)
  (if (and (pair? list1) (pair? list2) (equal? (car list1) (car list2)))
      (remove-common-head (cdr list1) (cdr list2))
      (list list1 list2)))

(define (remove-common-tail list1 list2)
  (let ((aux (remove-common-head (reverse list1) (reverse list2))))
    (list (reverse (car aux)) (reverse (cadr aux)))))

(define (union . x)
  (cond ((null? x) '())
	((list? (car x))
	 (remove-duplicates (append (car x) (apply union (cdr x)))))
	(else (myerror "union: list expected" (car x)))))

(define (intersection . x)
  (cond ((null? x)
	 (myerror "intersection should have at least one argument"))
	((list? (car x))
	 (if (null? (cdr x))
	     (car x)
	     (do ((list (apply intersection (cdr x)) (cdr list))
		  (res '() (if (member (car list) (car x))
			       (cons (car list) res)
			       res)))
		 ((null? list) (reverse res)))))
	(else (myerror "intersection: list expected" (car x)))))

(define (multiset-intersection-2 list1 list2)
  (do ((l1 list1 (cdr l1))
       (l2 list2 (if (member (car l1) l2)
                     (multiset-remove (car l1) l2)
                     l2))
       (res '() (if (member (car l1) l2)
                    (cons (car l1) res)
                    res)))
      ((or (null? l1) (null? l2)) (reverse res))))

(define (set-minus list1 list2)
  (do ((l list2 (cdr l))
       (res list1 (remove (car l) res)))
      ((null? l) res)))

(define (set-closure init-list closure-op)
  (do ((lists `(,(closure-op init-list) ,init-list)
	      (cons (closure-op (car lists)) lists)))
      ((null? (set-minus (car lists) (cadr lists)))
       (car lists))))

(define (multiset-remove x y)
  (do ((l y (cdr l))
       (res-and-flag (list '() #t)
                     (let ((res (car res-and-flag))
                           (flag (cadr res-and-flag)))
                       (if (and flag (equal? x (car l)))
                           (list res #f)
                           (list (cons (car l) res) flag)))))
      ((null? l) (reverse (car res-and-flag)))))

(define (multiset-intersection . x)
  (cond ((null? x)
	 (myerror "multiset-intersection should have at least one argument"))
	((list? (car x))
	 (if (null? (cdr x))
	     (car x)
	     (do ((l1 (car x) (cdr l1))
		  (l2 (apply multiset-intersection (cdr x))
		      (if (member (car l1) l2)
			  (multiset-remove (car l1) l2)
			  l2))
		  (res '() (if (member (car l1) l2)
			       (cons (car l1) res)
			       res)))
		 ((or (null? l1) (null? l2)) (reverse res)))))
	(else
	 (myerror "multiset-intersection: list expected" (car x)))))

(define (multiset-minus list1 list2)
  (do ((l list2 (cdr l))
       (res list1 (multiset-remove (car l) res)))
      ((null? l) res)))

(define (multiset-equal? list1 list2)
  (let multiset-equal?-aux ((l1 list1) (l2 list2))
    (cond ((null? l1) (null? l2))
	  ((member (car l1) l2)
	   (multiset-equal?-aux (cdr l1) (multiset-remove (car l1) l2)))
	  (else #f))))

;; We now relativize these (and other) procedures to a given equality:

(define (assoc-wrt equality? x alist)
  (cond ((null? alist) #f)
        ((equality? x (caar alist)) (car alist))
        (else (assoc-wrt equality? x (cdr alist)))))

(define (member-wrt equality? x list)
  (cond ((null? list) #f)
        ((equality? x (car list)) list)
        (else (member-wrt equality? x (cdr list)))))

(define (remove-wrt equality? x list)
  (do ((l list (cdr l))
       (res '() (if (equality? x (car l))
                    res
                    (cons (car l) res))))
      ((null? l) (reverse res))))

;; (define (remq x list) (remove-wrt eq? x list))
;; Already a global variable (detected by Bigloo)

(define (remv x list) (remove-wrt eqv? x list))

(define (adjoin-wrt equality? x list)
  (if (member-wrt equality? x list) list (cons x list)))

(define (remove-duplicates-wrt equality? list)
  (do ((l list (cdr l))
       (res '() (if (member-wrt equality? (car l) res)
                    res
                    (cons (car l) res))))
      ((null? l) (reverse res))))

(define (remq-duplicates list) (remove-duplicates-wrt eq? list))
(define (remv-duplicates list) (remove-duplicates-wrt eqv? list))

;; (duplicates-wrt equality? l) returns a list of two-element sublists
;; (x x') of equal elements of l whose transitive closure consists of
;; all such two-element sublists.

(define (duplicates-wrt equality? l)
  (if (null? l) '()
      (let* ((x (car l))
	     (xs (cdr l))
	     (duplicates-of-x-in-xs
	      (list-transform-positive xs
		(lambda (item) (equality? x item))))
	     (prev (duplicates-wrt equality? xs)))
	(if (null? duplicates-of-x-in-xs)
	    prev
	    (cons (list x (car duplicates-of-x-in-xs)) prev)))))

(define (union-wrt equality? . x)
  (cond ((null? x) '())
	((list? (car x))
	 (remove-duplicates-wrt
	  equality?
	  (append (car x) (apply union-wrt equality? (cdr x)))))
	(else (myerror "union-wrt: list expected" (car x)))))

(define (unionq . x) (apply union-wrt eq? x))
(define (unionv . x) (apply union-wrt eqv? x))

(define (intersection-wrt equality? . x)
  (cond ((null? x)
	 (myerror "intersection-wrt should have at least one argument"))
	((list? (car x))
	 (if (null? (cdr x))
	     (car x)
	     (do ((list (apply intersection-wrt equality? (cdr x))
			(cdr list))
		  (res '() (if (member-wrt equality? (car list) (car x))
			       (cons (car list) res)
			       res)))
		 ((null? list) (reverse res)))))
	(else (myerror "intersection-wrt: list expected" (car x)))))

(define (intersecq . x) (apply intersection-wrt eq? x))
(define (intersecv . x) (apply intersection-wrt eqv? x))

(define (set-minus-wrt equality? list1 list2)
  (do ((l list2 (cdr l))
       (res list1 (remove-wrt equality? (car l) res)))
      ((null? l) res)))

(define (set-minq list1 list2) (set-minus-wrt eq? list1 list2))
(define (set-minv list1 list2) (set-minus-wrt eqv? list1 list2))

(define (closure-wrt equality? init-list closure-op)
  (do ((lists `(,(closure-op init-list) ,init-list)
	      (cons (closure-op (car lists)) lists)))
      ((null? (set-minus-wrt equality? (car lists) (cadr lists)))
       (car lists))))

(define (closq init-list closure-op) (closure-wrt eq? init-list closure-op))
(define (closv init-list closure-op) (closure-wrt eqv? init-list closure-op))

(define (multiset-remove-wrt equality? x y)
  (do ((l y (cdr l))
       (res-and-flag (list '() #t)
                     (let ((res (car res-and-flag))
                           (flag (cadr res-and-flag)))
                       (if (and flag (equality? x (car l)))
                           (list res #f)
                           (list (cons (car l) res) flag)))))
      ((null? l) (reverse (car res-and-flag)))))

(define (multiset-remq x y) (multiset-remove-wrt eq? x y))
(define (multiset-remv x y) (multiset-remove-wrt eqv? x y))

(define (multiset-intersection-wrt equality? . x)
  (cond ((null? x)
	 (myerror
	  "multiset-intersection-wrt should have at least one argument"))
	((list? (car x))
	 (if (null? (cdr x))
	     (car x)
	     (do ((l1 (car x) (cdr l1))
		  (l2 (apply multiset-intersection-wrt
			     equality? (cdr x))
		      (if (member-wrt equality? (car l1) l2)
			  (multiset-remove-wrt equality? (car l1) l2)
			  l2))
		  (res '() (if (member-wrt equality? (car l1) l2)
			       (cons (car l1) res)
			       res)))
		 ((or (null? l1) (null? l2)) (reverse res)))))
	(else (myerror
	       "multiset-intersection-wrt: list expected" (car x)))))

(define (multiset-intersecq . x)
  (apply multiset-intersection-wrt eq? x))
(define (multiset-intersecv . x)
  (apply multiset-intersection-wrt eqv? x))

(define (multiset-minus-wrt equality? list1 list2)
  (do ((l list2 (cdr l))
       (res list1 (multiset-remove-wrt equality? (car l) res)))
      ((null? l) res)))

(define (multiset-minq list1 list2) (multiset-minus-wrt eq? list1 list2))
(define (multiset-minv list1 list2) (multiset-minus-wrt eqv? list1 list2))

(define (multiset-equal-wrt? equality? list1 list2)
  (let multiset-equal-wrt-aux ((l1 list1) (l2 list2))
    (cond ((null? l1) (null? l2))
	  ((member-wrt equality? (car l1) l2)
	   (multiset-equal-wrt-aux
	    (cdr l1) (multiset-remove-wrt equality? (car l1) l2)))
	  (else #f))))

(define (multiset-eq? list1 list2) (multiset-equal-wrt? eq? list1 list2))
(define (multiset-eqv? list1 list2) (multiset-equal-wrt? eqv? list1 list2))

;; alist-to-multivalued-alist-wrt transforms ((x1 y1) (x2 y2) ...) into
;; ((z1 y11 y12 ...) (z2 y21 y22 ...) ...) with distinct zi's.

(define (alist-to-multivalued-alist-wrt equality? alist)
  (letrec ((insert
	    (lambda (x y alist1)
	      (if (null? alist1)
		  (list (list x y))
		  (let* ((x-and-ys (car alist1))
			 (rest (cdr alist1)))
		    (if (equality? x (car x-and-ys))
			(cons (cons x (cons y (cdr x-and-ys))) rest)
			(cons x-and-ys (insert x y rest))))))))
    (if (null? alist) '()
	(let* ((prev (alist-to-multivalued-alist-wrt equality? (cdr alist)))
	       (x-and-y (car alist))
	       (x (car x-and-y))
	       (y (cadr x-and-y)))
	  (insert x y prev)))))

(define (list-to-left-associated-list x)
  (if (<= (length x) 2)
      x
      (let* ((l (length x))
	     (hd (list-head x (- l 1))))
	(list (list-to-left-associated-list hd) (car (last-pair x))))))

;; (list-to-left-associated-list '(0 1 2 3))
;; (((0 1) 2) 3)

;; Refined display for debugging

(define (display-more . x)
  (for-each display x)
  (newline))

(define (list-transform-positive l test)
  (if (null? l)
      l
      (let ((a (car l)))
	(if (test a)
	    (cons a (list-transform-positive (cdr l) test))
	    (list-transform-positive (cdr l) test)))))

(define (list-search-positive l test)
  (if (null? l)
      #f
      (let  ((a (car l)))
	(if (test a)
	    a
	    (list-search-positive (cdr l) test)))))

(define and-op
    (lambda  x
      (cond ((null? x) #t)
	    ((car x) (apply and-op (cdr x)))
	    (else #f))))

(define or-op
    (lambda  x
      (cond ((null? x) #f)
	    ((car x) #t)
	    (else (apply or-op (cdr x))))))

(define (remove-final-numeric-chars list-of-chars)
  (if (null? list-of-chars)
      (myerror "remove-final-numeric-chars applied to empty list")
      (do ((l (reverse list-of-chars) (cdr l)))
          ((not (char-numeric? (car l))) (reverse l)))))

(define (remove-final-^ list-of-chars)
  (if (or (null? list-of-chars)
          (not (char=? #\^ (car (reverse list-of-chars)))))
      list-of-chars
      (reverse (cdr (reverse list-of-chars)))))

(define (remove-^ list-of-chars)
  (do ((l list-of-chars (cdr l))
       (res '() (if (char=? #\^ (car l))
                    res
                    (cons (car l) res))))
      ((null? l) (reverse res))))

(define (index-of-first-occurrence x l)
  (let ((x-and-rest (member x l)))
    (if x-and-rest
	(- (length l) (length x-and-rest))
	(myerror "index-of-first-occurrence: element of list expected" x l))))

(define (minima rel xs)
  (if
   (null? xs) '()
   (let* ((x (car xs))
	  (ys (minima rel (cdr xs))))
     (if (apply or-op (map (lambda (y) (rel y x)) ys))
	 ys
	 (cons x (list-transform-positive ys (lambda (y) (not (rel x y)))))))))

;; As example we take rel to be the inclusion relation.  Then

;; (minima (lambda (x y) (null? (set-minus x y))) '((3) (1 2 3) (1 2) (1 3)))
;; returns ((3) (1 2))

(define (choices xss)
  (if (null? xss) (list (list))
      (let* ((xs (car xss))
	     (prev (choices (cdr xss))))
	(minima
	 (lambda (x y) (null? (set-minus x y)))
	 (apply append
		(map (lambda (ys)
		       (minima (lambda (x y) (null? (set-minus x y))) ys))
		     (map (lambda (x)
			    (map (lambda (y) (union x y))
				 prev))
			  xs)))))))

;; (choices '(((1 2) (1 3))  ((2) (3 4))))
;; returns ((1 2) (1 3 4))

;; (choices '(((1 2) (1 3))  ()  ((2) (3 4))))
;; returns ()

(define (curry f n)
  (if (= 1 n)
      f
      (lambda (x) (curry (lambda l (apply f x l)) (- n 1)))))

(define (uncurry g n)
  (if (= 1 n)
      g
      (lambda l (apply (uncurry (g (car l)) (- n 1)) (cdr l)))))

;; Insertion sort

(define (insert x lt? sorted-list)
  (if (null? sorted-list)
      (list x)
      (let ((fst (car sorted-list)))
	(if (lt? x fst)
	    (cons x sorted-list)
	    (cons fst (insert x lt? (cdr sorted-list)))))))

(define (insertsort lt? l)
  (if (null? l)
      l
      (insert (car l) lt? (insertsort lt? (cdr l)))))

;; (insertsort < '(4 2 8 6))
;; (insertsort > '(4 2 8 6))

(define (check-all test l)
  (or (null? l)
      (and (test (car l))
	   (check-all test (cdr l)))))

(define (check-exists test l)
  (and (pair? l)
       (or (test (car l))
	   (check-exists test (cdr l)))))

(define (list-and-test-to-head-up-to-last l test)
  (if (null? l) '()
      (let* ((head (car l))
	     (tail (cdr l))
	     (prev (list-and-test-to-head-up-to-last tail test)))
	(if (null? prev)
	    (if (test head) (list head) '())
	    (cons head prev)))))

;; (list-and-test-to-head-up-to-last '(#t #f #t #f #t #t) (lambda (x) (not x)))
;; (#t #f #t #f)

(define (list-tabulate n init-proc)
  (do ((i 0 (+ 1 i))
       (res '() (cons (init-proc i) res)))
      ((= i n) (reverse res))))

;; (list-tabulate 4 (lambda (x) x))
;; (0 1 2 3)
;; (list-tabulate 4 (lambda (x) (* x x)))
;; (0 1 4 9)

(define (find-tail test l)
  (cond ((null? l) #f)
	((test (car l)) l)
	(else (find-tail test (cdr l)))))

;; (find-tail even? '(3 5 4 7 2 1))
;; (4 7 2 1)

(define (init-segments l)
  (if (null? l)
      (list '())
      (cons '() (map (lambda (x) (cons (car l) x)) (init-segments (cdr l))))))

;; (init-segments '(0 1 2))
;; (() (0) (0 1) (0 1 2))

(define (nonnil-init-segments l)
  (cdr (init-segments l)))

;; (nonnil-init-segments '(0 1 2))
;; ((0) (0 1) (0 1 2))

;; Some useful string functions.

(define (string-downcase string)
  (list->string (map char-downcase (string->list string))))

(define (initial-substring? string1 string2)
  (let ((l1 (string-length string1))
	(l2 (string-length string2)))
    (and (<= l1 l2)
	 (string=? string1 (substring string2 0 l1)))))

;; (initial-substring? "abc" "abcde")

(define (final-substring? string1 string2)
  (let ((l1 (string-length string1))
	(l2 (string-length string2)))
    (and (<= l1 l2)
	 (string=? string1 (substring string2 (- l2 l1) l2)))))

;; (final-substring? "cde" "abcde")

(define (substring? string1 string2)
  (do ((s string2 (substring s 1 (string-length s)))
       (res #f (initial-substring? string1 s)))
      ((or res (zero? (string-length s)))
       res)))

;; (substring? "bcd" "abcde")

;; Added for Haskell translation.

;; non-null-list-to-app-expr takes a new argument lang

(define (non-null-list-to-app-expr lang x)
  (case lang
    ((haskell) (let ((body (apply string-append-with-sep " " x)))
		 (if (> (length x) 1) (string-append "(" body ")") body)))
    ((scheme) (let ((l (length x)))
		(cond ((= 1 l) (car x))
		      ((= 2 l) x)
		      (else (list-to-left-associated-list x)))))))

(define (string-append-with-sep sep . strings)
  (cond ((null? strings) "")
	((null? (cdr strings)) (car strings))
	(else (string-append (car strings) sep
			  (apply string-append-with-sep sep (cdr strings))))))

(define (string-replace-substring string before after)
  (define (string-replace-substring-from s bef aft start-index)
    (let ((idx (string-contains s bef start-index)))
      (if idx
	  (let* ((end (+ idx (string-length bef)))
		 (new-end (+ idx (string-length aft)))
		 (s0 (string-replace s aft idx end)))
	    (string-replace-substring-from s0 bef aft new-end))
	  s)))
  (string-replace-substring-from string before after 0))

(define (string-capitalize-first string)
  (let* ((xss (string->list string))
	 (x (car xss))
	 (xs (cdr xss)))
    (list->string (cons (char-upcase x) xs))))

(define (string-downcase-first string)
  (let* ((xss (string->list string))
	 (x (car xss))
	 (xs (cdr xss)))
    (list->string (cons (char-downcase x) xs))))

;; Given a string "(x)" or "x", returns "x".
;; Assumes that the string is not of the form "(x)(y)".
(define (string-remove-outer-parens string)
  (let* ((string-end (- (string-length string) 1)))
    (if (and (char=? (string-ref string 0) #\()
	     (char=? (string-ref string string-end) #\)))
	(substring string 1 string-end) string)))

(define (remove-last lst)
    (if (null? (cdr lst))
        '()
        (cons (car lst) (remove-last (cdr lst)))))

(define (remove-nth lst n)
    (cond ((null? lst) '())
          ((= 0 n) (cdr lst))
          (else (cons (car lst) (remove-nth (cdr lst) (- n 1))))))

;;;;;;; non-r5rs functions ;;;;;;;;;;;;;;;;

(define (repeat x n) (if (= n 0) '() (cons x (repeat x (- n 1)))))

 (define (compose f . rest)
    (if (null? rest)
      f
      (let ((g (apply compose rest)))
        (lambda args
          (call-with-values (lambda () (apply g args)) f)))))

(define (assoc-set! alist key value)
  (cond ((null? alist) (cons (cons key value) '()))
        ((equal? (caar alist) key) (cons (cons key value) (cdr alist)))
        (else (cons (car alist) (assoc-set! (cdr alist) key value)))))

(define (string-prefix? pre string)
  (equal? (string-contains string pre 0) 0))

;; (string-prefix? "pine" "pineapple")

;; from Kenji Miyamoto:

(define (string-contains s bef start-index)
  (define (string-contains-aux l bef index)
    (let ((bef-length (length bef)))
      (if (< (length l) bef-length)
	  #f
	  (let ((l-head (list-head l bef-length)))
	    (if (equal? bef l-head)
		index
		(string-contains-aux (cdr l) bef (+ index 1)))))))
  (let* ((l (string->list s))
	 (lbef (string->list bef))
	 (l-tail (list-tail l start-index))
	 (aux (string-contains-aux l-tail lbef 0)))
    (if aux
	(+ start-index aux)
	#f)))

;; (string-contains "string" "ring" 2)

(define (string-replace s aft idx end)
  (let* ((length-s (string-length s))
	 (head-s (substring s 0 idx))
	 (tail-s (substring s end length-s)))
    (string-append head-s aft tail-s)))

;; (string-replace "It's easy to code it up in Scheme." "lots of fun" 5 9)

(define (string-reverse str)
  (list->string (reverse (string->list str))))

(define (string-suffix? string suffix)
  (let ((n (string-length string))
	(m (string-length suffix)))
    (and (<= m n) (string=? (substring string (- n m) n) suffix))))

;; (string-suffix? "TotalMR" "MR")

(define (string-replace-substrings string before-list after-list)
  (if (null? before-list) string
      (string-replace-substrings
       (string-replace-substring string (car before-list) (car after-list))
       (cdr before-list) (cdr after-list))))

;; (string-replace-substrings "abcdefghi" '("bc" "fgh") '("cb" "hgf"))
;; "acbdehgfi"


