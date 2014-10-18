;; 2014-01-23.  dickson.scm.

;; (load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(set! COMMENT-FLAG #t)

(add-var-name "f" "g" (py "nat=>nat"))
(add-var-name "i" "j" "l" (py "nat"))

;; DicksonTwo
(set-goal "all f,g excl i,j(i<j ! (f j<f i -> bot) ! (g j<g i -> bot))")
(assume "f" "g")
(by-assume-minimal-wrt (pf "excl n T") "n" (pt "f") "MinH1" "H1")

;; Generates two new goals: excl n T (trivial), and the existence of the
;; minimal element (a hypothesis) implies our goal
(assume "u")
(use-with "u" (pt "0") "Truth")
(drop "H1")

;; By the minimum principle, applied with
;; excl n all m(n<m+1 -> f m<f n -> bot) and measure function g,
;; we obtain an element i that is a left-minimum of f and also minimal
;; w.r.t. g

(by-assume-minimal-wrt
 (pf "excl n all m(n<m+1 -> f m<f n -> bot)") "i" (pt "g") "MinH2" "H2")
(exc-intro (pt "n"))
(assume "i" "n<i+1" "f i<f n")
(use-with "MinH1" (pt "i") "f i<f n" "Truth")

;; By a third application of the minimum principle we choose the nex
;; left-minimum w.r.t. f

(by-assume-minimal-wrt (pf "excl l i < l") "j" (pt "f") "MinH3" "H3")
(exc-intro (pt "i+1"))
(use "Truth")

;; Now we have i and j as desired
(exc-intro (pt "i") (pt "j"))
(use "H3")

(use-with "H2" (pt "j") "?")
(use "NatLtTrans" (pt "j"))
(use "H3")
(use "Truth")

(assume "g j<g i")
(use-with "MinH2" (pt "j") "g j<g i" "?")

(assume "m" "j<m+1" "f m<f j")
(use-with "MinH3" (pt "m") "f m<f j" "?")
(use "NatLtLtSuccTrans" (pt "j"))
(use "H3")
(use "j<m+1")
;; Proof finished.
(save "DicksonTwo")

;; For normalization we need to block unfolding of GRecGuard (whose
;; last argument will be True)

(set! GRECGUARD-UNFOLDING-FLAG #f)

(define min-excl-proof
  (np (rm-exc (theorem-name-to-proof "DicksonTwo"))))

(define eterm (atr-min-excl-proof-to-structured-extracted-term
	       min-excl-proof))

(add-var-name "h" (py "nat=>nat@@nat"))
(add-var-name "xi" (py "nat=>(nat=>nat@@nat)=>nat@@nat"))

(define neterm (rename-variables (nt eterm)))
(pp neterm)

;; [f,f0]
;;  (GRecGuard nat nat@@nat)f 0
;;  ([n]
;;    (GRecGuard nat (nat=>nat@@nat)=>nat@@nat)f0 n
;;    ([n0,xi,h]
;;      (GRecGuard nat nat@@nat)f(Succ n0)
;;      ([n1,h0][if (f n1<f n0) (h n1) [if (f0 n1<f0 n0) (xi n1 h0) (n0@n1)]])
;;      True)
;;    True)
;;  True

(define t0 (pt "[n]n"))
(define t1 (pt "[n](Succ n)"))

(pp (nt (mk-term-in-app-form neterm t0 t1)))
(set! GRECGUARD-UNFOLDING-FLAG #t)
(pp (nt (mk-term-in-app-form neterm t0 t1)))
;; 0@1

(define t0 (pt "[n]2--n"))
(pp (nt (mk-term-in-app-form neterm t0 t1)))
;; 2@3

;; Comparison with brute force

;; (randomalist l b) returns an alist ((0 v0) (1 v1) ... (l-1 v_{l-1}))
;; with random values v auch that 0 <= v < b.

(define (randomalist l b)
  (do ((i l (- i 1))
       (res '() (cons (list (- i 1) (random b)) res)))
      ((= i 0) res)))

;; (randomalist 50 100)
;; ((0 54) (1 65) (2 24) (3 11) (4 8) (5 16) (6 20) (7 2) (8 78)
;;  (9 81) (10 73) (11 3) (12 48) (13 99) (14 69) (15 6) (16 62)
;;  (17 11) (18 47) (19 9) (20 38) (21 25) (22 29) (23 94)
;;  (24 6) (25 53) (26 85) (27 51) (28 88) (29 68) (30 10)
;;  (31 72) (32 38) (33 49) (34 37) (35 88) (36 19) (37 22)
;;  (38 24) (39 85) (40 41) (41 78) (42 91) (43 6) (44 18)
;;  (45 97) (46 72) (47 68) (48 69) (49 92))

(define (alist-to-function alist)
  (lambda (n)
    (let ((info (assq n alist)))
      (if info (cadr info) 0))))

;; Brute force computation of an increasing pair

(define (fip f g l)
  (letrec ((aux
	    (lambda (i j)
	      (display "i=") (display i)
	      (display " j=") (display j)
	      (display tab)
	      (display " f") (display i) (display "=") (display (f i))
	      (display tab)
	      (display " f") (display j) (display "=") (display (f j))
	      (display tab)
	      (display " g") (display i) (display "=") (display (g i))
	      (display tab)
	      (display " g") (display j) (display "=") (display (g j))
	      (newline)
	      (if (and (<= (f i) (f j)) (<= (g i) (g j)))
		  (cons i j)
		  (if (< (+ i 1) j)
		      (aux (+ i 1) j)
		      (if (< (+ j 1) l)
			  (aux 0 (+ j 1))
			  (display "no increasing pair found")))))))
    (newline)
    (aux 0 1)))

;; Computation of an increasing pair with the extracted algorithm

(term-to-scheme-expr neterm)

;; (lambda (f)
;;   (lambda (f0)
;;     ((((natGrecGuard f) 0)
;;       (lambda (n)
;; 	((((natGrecGuard f0) n)
;; 	  (lambda (n0)
;; 	    (lambda (xi)
;; 	      (lambda (h)
;; 		((((natGrecGuard f) (+ n0 1))
;; 		  (lambda (n1)
;; 		    (lambda (h0)
;; 		      (if (< (f n1) (f n0))
;; 			  (h n1)
;; 			  (if (< (f0 n1) (f0 n0))
;; 			      ((xi n1) h0)
;; 			      (cons n0 n1))))))
;; 		 #t)))))
;; 	 #t)))
;;      #t)))

;; Accordingly we define

(define (extr f g)
  ((((natGrecGuard f) 0)
    (lambda (n)
      ((((natGrecGuard g) n)
	(lambda (n0)
	  (lambda (xi)
	    (lambda (h)
	      ((((natGrecGuard f) (+ n0 1))
		(lambda (n1)
		  (lambda (h0)
		    (begin
		      (newline)
		      (display "i=") (display n0)
		      (display " j=") (display n1)
		      (display tab)
		      (display " f") (display n0) (display "=")
		      (display (f n0))
		      (display tab)
		      (display " f") (display n1) (display "=")
		      (display (f n1))
		      (display tab)
		      (if (< (f n1) (f n0))
			  (h n1)
			  (begin
			    (display " g") (display n0) (display "=")
			    (display (g n0))
			    (display tab)
			    (display " g") (display n1) (display "=")
			    (display (g n1))
			    (if (< (g n1) (g n0))
				((xi n1) h0)
				(begin (newline)
				       (cons n0 n1)))))))))
	       #t)))))
       #t)))
   #t))

(define l 20)
(define b 100)
(define alist1 (randomalist l b))
(define alist2 (randomalist l b))
(define f (alist-to-function alist1))
(define g (alist-to-function alist2))

;; (fip f g l)

;; i=0 j=1	 f0=92	 f1=90	 g0=42	 g1=42
;; i=0 j=2	 f0=92	 f2=73	 g0=42	 g2=79
;; i=1 j=2	 f1=90	 f2=73	 g1=42	 g2=79
;; i=0 j=3	 f0=92	 f3=86	 g0=42	 g3=68
;; i=1 j=3	 f1=90	 f3=86	 g1=42	 g3=68
;; i=2 j=3	 f2=73	 f3=86	 g2=79	 g3=68
;; i=0 j=4	 f0=92	 f4=37	 g0=42	 g4=79
;; i=1 j=4	 f1=90	 f4=37	 g1=42	 g4=79
;; i=2 j=4	 f2=73	 f4=37	 g2=79	 g4=79
;; i=3 j=4	 f3=86	 f4=37	 g3=68	 g4=79
;; i=0 j=5	 f0=92	 f5=31	 g0=42	 g5=67
;; i=1 j=5	 f1=90	 f5=31	 g1=42	 g5=67
;; i=2 j=5	 f2=73	 f5=31	 g2=79	 g5=67
;; i=3 j=5	 f3=86	 f5=31	 g3=68	 g5=67
;; i=4 j=5	 f4=37	 f5=31	 g4=79	 g5=67
;; i=0 j=6	 f0=92	 f6=97	 g0=42	 g6=60
;; (0 . 6)

(extr f g)

;; i=0 j=1	 f0=92	 f1=90	
;; i=1 j=2	 f1=90	 f2=73	
;; i=2 j=3	 f2=73	 f3=86	 g2=79	 g3=68
;; i=3 j=4	 f3=86	 f4=37	
;; i=2 j=4	 f2=73	 f4=37	
;; i=4 j=5	 f4=37	 f5=31	
;; i=5 j=6	 f5=31	 f6=97	 g5=67	 g6=60
;; i=6 j=7	 f6=97	 f7=69	
;; i=5 j=7	 f5=31	 f7=69	 g5=67	 g7=40
;; i=7 j=8	 f7=69	 f8=46	
;; i=5 j=8	 f5=31	 f8=46	 g5=67	 g8=64
;; i=8 j=9	 f8=46	 f9=88	 g8=64	 g9=22
;; i=9 j=10	 f9=88	 f10=55	
;; i=8 j=10	 f8=46	 f10=55	 g8=64	 g10=92
;; (8 . 10)

(define (test l b max)
  (do ((i 0 (+ i 1)))
      ((= i max) (newline) (display "max=") (display max) (display " reached")
       (newline))
    (let* ((alist1 (randomalist l b))
	   (alist2 (randomalist l b))
	   (f (begin (newline) (display "f: ") (display-alist alist1)
		     (alist-to-function alist1)))
	   (g (begin (newline) (display "g: ") (display-alist alist2)
		     (newline)
		     (alist-to-function alist2)))
	   (pair1 (fip f g l))
	   (pair2 (extr f g)))
      (newline)
      (display pair1)
      (display tab)
      (display pair2)
      (newline))))

(define (display-alist alist)
  (for-each (lambda (pair)
	      (begin (if (< (cadr pair) 10) (display " "))
		     (display (cadr pair))
		     (display " ")))
	    alist))

;; (test 20 100 5)

;; f:  8  5 28 85  0  9 77 29 36 46 83 23  4 23 59 33 88 39  8 54
;; g: 85 45 30 43 96 25 49 19 11 87 40 86 40 27 80 98 24 21 15 49

;; i=0 j=1	 f0=8	 f1=5	 g0=85	 g1=45
;; i=0 j=2	 f0=8	 f2=28	 g0=85	 g2=30
;; i=1 j=2	 f1=5	 f2=28	 g1=45	 g2=30
;; i=0 j=3	 f0=8	 f3=85	 g0=85	 g3=43
;; i=1 j=3	 f1=5	 f3=85	 g1=45	 g3=43
;; i=2 j=3	 f2=28	 f3=85	 g2=30	 g3=43

;; i=0 j=1	 f0=8	 f1=5	
;; i=1 j=2	 f1=5	 f2=28	 g1=45	 g2=30
;; i=2 j=3	 f2=28	 f3=85	 g2=30	 g3=43

;; (2 . 3)	(2 . 3)

;; f: 61  9 16 17 70 94 31 62 85  2 77 77 66 56 22 15 72 65 50 20
;; g: 89 44 53 34 46  6 63 38 60 88 43 55 22 16 56 46 13  5 66 78

;; i=0 j=1	 f0=61	 f1=9	 g0=89	 g1=44
;; i=0 j=2	 f0=61	 f2=16	 g0=89	 g2=53
;; i=1 j=2	 f1=9	 f2=16	 g1=44	 g2=53

;; i=0 j=1	 f0=61	 f1=9	
;; i=1 j=2	 f1=9	 f2=16	 g1=44	 g2=53

;; (1 . 2)	(1 . 2)

;; f: 93 66 75 15 57 53  6 16  0 93 65 31 86 16 40 68 84  4 92 11
;; g: 15 99 79  8 99 32 89 70 58 70 46 42 10 65 57 74 36 57 57 68

;; i=0 j=1	 f0=93	 f1=66	 g0=15	 g1=99
;; i=0 j=2	 f0=93	 f2=75	 g0=15	 g2=79
;; i=1 j=2	 f1=66	 f2=75	 g1=99	 g2=79
;; i=0 j=3	 f0=93	 f3=15	 g0=15	 g3=8
;; i=1 j=3	 f1=66	 f3=15	 g1=99	 g3=8
;; i=2 j=3	 f2=75	 f3=15	 g2=79	 g3=8
;; i=0 j=4	 f0=93	 f4=57	 g0=15	 g4=99
;; i=1 j=4	 f1=66	 f4=57	 g1=99	 g4=99
;; i=2 j=4	 f2=75	 f4=57	 g2=79	 g4=99
;; i=3 j=4	 f3=15	 f4=57	 g3=8	 g4=99

;; i=0 j=1	 f0=93	 f1=66	
;; i=1 j=2	 f1=66	 f2=75	 g1=99	 g2=79
;; i=2 j=3	 f2=75	 f3=15	
;; i=1 j=3	 f1=66	 f3=15	
;; i=3 j=4	 f3=15	 f4=57	 g3=8	 g4=99

;; (3 . 4)	(3 . 4)

;; f: 79 57  9 44 94 79  4 11 42  4 33 21 35  6 67 36 44 34 44  9
;; g: 98 44 58 56 38 53  1 77 50 80 47 17 17 33 39 95 12 82 79 84

;; i=0 j=1	 f0=79	 f1=57	 g0=98	 g1=44
;; i=0 j=2	 f0=79	 f2=9	 g0=98	 g2=58
;; i=1 j=2	 f1=57	 f2=9	 g1=44	 g2=58
;; i=0 j=3	 f0=79	 f3=44	 g0=98	 g3=56
;; i=1 j=3	 f1=57	 f3=44	 g1=44	 g3=56
;; i=2 j=3	 f2=9	 f3=44	 g2=58	 g3=56
;; i=0 j=4	 f0=79	 f4=94	 g0=98	 g4=38
;; i=1 j=4	 f1=57	 f4=94	 g1=44	 g4=38
;; i=2 j=4	 f2=9	 f4=94	 g2=58	 g4=38
;; i=3 j=4	 f3=44	 f4=94	 g3=56	 g4=38
;; i=0 j=5	 f0=79	 f5=79	 g0=98	 g5=53
;; i=1 j=5	 f1=57	 f5=79	 g1=44	 g5=53

;; i=0 j=1	 f0=79	 f1=57	
;; i=1 j=2	 f1=57	 f2=9	
;; i=2 j=3	 f2=9	 f3=44	 g2=58	 g3=56
;; i=3 j=4	 f3=44	 f4=94	 g3=56	 g4=38
;; i=4 j=5	 f4=94	 f5=79	
;; i=3 j=5	 f3=44	 f5=79	 g3=56	 g5=53
;; i=5 j=6	 f5=79	 f6=4	
;; i=3 j=6	 f3=44	 f6=4	
;; i=2 j=6	 f2=9	 f6=4	
;; i=6 j=7	 f6=4	 f7=11	 g6=1	 g7=77

;; (1 . 5)	(6 . 7)

;; f: 32 28 19  1 32 75 15 76 18 26 14 42  2 99 77 79  0 48  8  0
;; g: 47 72 12  1 36 58 92 49 10 84 62 15 53 65 11 71  2 43 13  0

;; i=0 j=1	 f0=32	 f1=28	 g0=47	 g1=72
;; i=0 j=2	 f0=32	 f2=19	 g0=47	 g2=12
;; i=1 j=2	 f1=28	 f2=19	 g1=72	 g2=12
;; i=0 j=3	 f0=32	 f3=1	 g0=47	 g3=1
;; i=1 j=3	 f1=28	 f3=1	 g1=72	 g3=1
;; i=2 j=3	 f2=19	 f3=1	 g2=12	 g3=1
;; i=0 j=4	 f0=32	 f4=32	 g0=47	 g4=36
;; i=1 j=4	 f1=28	 f4=32	 g1=72	 g4=36
;; i=2 j=4	 f2=19	 f4=32	 g2=12	 g4=36

;; i=0 j=1	 f0=32	 f1=28	
;; i=1 j=2	 f1=28	 f2=19	
;; i=2 j=3	 f2=19	 f3=1	
;; i=3 j=4	 f3=1	 f4=32	 g3=1	 g4=36

;; (2 . 4)	(3 . 4)

;; max=5 reached
