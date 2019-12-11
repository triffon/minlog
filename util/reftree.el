;; 2014-10-01.  reftree.el.  Written by Masahiko Sato.  Generates a
;; reference tree for each lemma in a file.  Usage:

;; 1.  Copy reftree.el into an emacs buffer and evaluate the buffer
;; (by M-x eval-buffer)

;; 2.  Go to buffer *scratch* (for instance)

;; 3.  As a test, type (nth3 '(1 2 3 4)) and evaluate (by C-j).  Result: 4

;; 4.  Type M-x minlog-ref.  You will be asked for a file name.

;; 5.  The resulting reference tree appears in the present buffer.

(defun cdddr (x)
  (cdr (cddr x)))

(defun nth0 (x)
  (car x))

(defun nth1 (x)
  (car (cdr x)))

(defun nth2 (x)
  (car (cddr x)))

(defun nth3 (x)
  (car (cdddr x)))

(defun nth4 (x)
  (car (cdr (cddr (cdr x)))))

(defun read-next-sexp ()
  (let (end sexp)
    (skip-chars-forward " \t\n")
    (forward-sexp)
    (setq end (point))
    (forward-sexp -1)
    (setq sexp (read-from-string (buffer-substring (point) end)))
    (goto-char end)
    sexp))

(defun erase-hash ()
  (goto-char (point-min))
  (while (search-forward "#" nil t)
    (delete-char -1)))

(defun minlog-ref (file &optional level)
  "Compute a reference tree of each lemma proved in a minlog file.
If a positive LEVEL is given, it will control the print level."
  (interactive "fFile:")
  (let ((cont t)
        (ignore-point nil)
        (lemmata nil)
        lemma lemmata2 goal
        total-lems
        (trees nil)
        tree tree2
        (sexp nil)
        here beg end)
    (with-temp-buffer
      ;; be sure to run scheme before calling the next function
      (with-syntax-table scheme-mode-syntax-table
        (insert-file file)
        (beginning-of-buffer)
        ;; scheme uses # which is not a valid char in Emacs Lisp
        (erase-hash)
        ;; record ignore-point
        (beginning-of-buffer)
        (when (re-search-forward "^;; ref-tree ignore up to here" nil t)
          (end-of-line)
          (setq ignore-point (point-marker)))
        ;; delete comment lines
        (beginning-of-buffer)
        (while (search-forward ";" nil t)
          (delete-region (1- (point))
                         (progn
                           (end-of-line)
                           (point))))
        ;; collect saved lemmata in the file
        (beginning-of-buffer)
        (while cont
          (setq here (point))
          (setq sexp (car (read-next-sexp)))
          (if (<= (point) here)
              (setq cont nil)
            (if (eq (and (consp sexp) (car sexp)) 'save)
                (setq lemmata 
                      (cons (list (nth1 sexp) "" 0 0 nil)
                            lemmata)))))
        (setq total-lems (length lemmata)
              cont t
              lemmata nil)
        ;; delete up to ignore
        (when ignore-point
          (delete-region (point-min) ignore-point))
        ;; collect saved lemmata in the file
        (beginning-of-buffer)
        (while cont
          (setq here (point))
          (setq sexp (car (read-next-sexp)))
          (if (<= (point) here)
              (setq cont nil)
            (if (eq (and (consp sexp) (car sexp)) 'save)
                (setq lemmata 
                      (cons (list (nth1 sexp) "" 0 0 nil)
                            lemmata)))))
        (beginning-of-buffer)
        ;; analyze proofs and with each lemma associates other
        ;; lemmata used in the proof of the lemma
        (while (re-search-forward "(set-goal[ \t]" nil t)
          (goto-char (match-beginning 0))
          ;(forward-sexp) 
          (setq goal (nth1 (car (read-next-sexp))))
          ;(message "Goal: %s" goal) (sit-for 2)
          (setq beg (point))
          (if (re-search-forward "(save[ \t]" nil t)
              (progn
                (setq end (match-beginning 0))
                (goto-char end)
                (setq sexp (car (read-next-sexp)))
                (setq lemma (nth1 sexp))
                ;; now start modifying lemmata
                ;; TREE = (name goal count depth used-lemmata)
                (setq tree (assoc-string lemma lemmata))
                ;(message "Tree: %s" tree) (sit-for 2)
                (if tree
                    (progn
                      ;; first rewrite the goal of the tree by the
                      ;; real goal
                      (setcar (cdr tree) goal)
                      ;(message "Tree: %s" tree) (sit-for 2)
                      (goto-char beg)
                      (while (re-search-forward "(use[ \t]" end t)
                        (goto-char (match-beginning 0))
                        ;; the next command moves the point forward
                        (setq sexp (car (read-next-sexp)))
                        (setq lemma (nth1 sexp)) ; just a candidate
                        ;; lemma may be a number, so check it
                        (when (stringp lemma)
                          (setq tree2 (assoc-string lemma lemmata))
                          (when tree2
                            ;; found a lemma used in the proof, so
                            ;; add it to TREE
                            (let ((l (cdddr (cdr tree))))
                              (setcar l (cons tree2 (nth4 tree))))))))
                  (error "Lemma %s not in the database" lemma)))
            (error "Proof started at %s but not finished" beg)))
        ;; update lemmata by computing the usage of each lemma
        (setq lemmata2 lemmata)
        (while lemmata2
          ;; (car lemmata2) == (name usage depth tree)
          (let* ((lemma (car lemmata2))
                 (l (cddr lemma)))
            (setcar l (length (nth4 lemma))))
          (setq lemmata2 (cdr lemmata2)))
        ;; we now compute the depth of each lemma
        ;; first reverse lemmata, so that basic lemmata will come first
        (setq lemmata2 (reverse lemmata))
        (while lemmata2
          ;; (car lemmata2) == (name goal usage depth tree)
          (let* ((lemma (car lemmata2))
                 (l (cdddr lemma))
                 (tree (nth4 lemma)))
            (when tree
              ;; we need to update depth only when TREE is non-empty
              (setcar l (1+ (apply (function max)
                                   (mapcar (function nth3) tree))))))
          (setq lemmata2 (cdr lemmata2)))
        ))
    (setq lemmata (reverse lemmata))
    ;; finally print it
    (insert (format "%s propositions are proved in the file:\n
        %s\n
Ignoring intial %s lemmata, the reference trees for the remaining
%s lemmata are as follows\n\n" 
                    total-lems file
                    (- total-lems (length lemmata)) (length lemmata)))
    (setq level (or level 10))
    (while lemmata
      (print-lemma (car lemmata) 0 level)
      (insert "\n")
      (setq lemmata (cdr lemmata))) ))

(defun print-lemmata (lemmata indent level)
  "Print LEMMATA in tree form."
  (let ((lemmata2 lemmata))
    (while lemmata2
      (print-lemma (car lemmata2) indent level)
      (setq lemmata2 (cdr lemmata2)))))

(defun print-lemma (lemma indent level)
  "Print LEMMA in tree form with INDENT"
  ;; LEMMA = (name count depth LEMMATA)
  (insert (make-string indent ?\ ))
  (if (= (nth2 lemma) 0)
      (insert (format "%s%s\n" (if (= indent 0) "" "| ") (nth0 lemma)))
    (insert 
     (format "%s%s [%s, %s]\n" 
             (if (= indent 0) "" "| ") 
             (nth0 lemma) (nth2 lemma) (nth3 lemma))))
  (when (= indent 0)
    ;; print the goal of the lemma
    (insert (format "|- %s\n" (nth1 lemma))))
  ;; print LEMMATA
  (if (> level 0)
      ;; we use reverse to print lemmas in the order they are used
      ;; in the proof
      (print-lemmata (reverse (nth4 lemma)) (+ 3 indent) (1- level))))

