(defun run-minlog (&optional filename)
  ;; Enable utf-8
  (setq default-enable-multibyte-characters t)
  (condition-case nil
      (set-language-environment "Greek")
    (error nil))
  (condition-case nil
      (set-language-environment "utf-8")
    (error nil))
  (set-input-method "TeX")

  ;; Start MINLOG
  (interactive)

  ;; MINLOG directory
  (if (getenv "MINLOGPATH")
      (setq minlogpath (getenv "MINLOGPATH"))
    (setq minlogpath "---MINLOGPATH---"))

  ;; which scheme to use ?
  (cond ((getenv "SCHEME") (setq scheme (getenv "SCHEME")))
	((and (file-readable-p "/usr/bin/petite")
	      (string= system-type "gnu/linux"))
	 (setq scheme "/usr/bin/petite"))
	((eq 0 (shell-command "which petite"))
	 (setq scheme "petite"))
	((eq 0 (shell-command "which mzscheme"))
	 (if (string-match "v4." (shell-command-to-string "mzscheme --version"))
	     (setq scheme "mzscheme -l mzscheme -l r5rs -i --load")
	   (setq scheme "mzscheme --load")))
	((eq 0 (shell-command "which guile"))
	 (setq scheme "guile -l"))
	(t (error "Neither petite nor mzscheme nor guile installed ")))

  ;; setup the frame
  (setq inhibit-startup-message t)
  (delete-other-frames)
  (delete-other-windows)
  (let* ((orig-frame (selected-frame))
	 (left-frame (make-frame))
	 (right-frame (make-frame))
	 (wh (frame-pixel-width left-frame))
	 (left-frame-lt (frame-parameter left-frame 'left))
	 (lt (if (< (+ left-frame-lt (* wh 2)) (x-display-pixel-width))
		 left-frame-lt 0))
	 (ht (/ (x-display-pixel-height) (frame-char-height)))
	 (border (frame-parameter left-frame 'border-width)))
    ;; is there a heap file ?
    (if (and (file-readable-p (concat minlogpath "/minlog.heap"))
	   (or (string= scheme "petite")
	       (string= scheme "/usr/bin/petite")))
	(setq heapload
	      (concat "-h " minlogpath "/minlog.heap "
		      minlogpath "/welcome.scm"))
      (setq heapload (concat minlogpath "/init.scm")))

    (set-frame-size left-frame 80 ht)
    (set-frame-size right-frame 80 ht)
    (set-frame-position left-frame lt 0)
    (set-frame-position right-frame (+ lt wh (* 2 border)) 0)
    (delete-frame orig-frame)

    ;; start scheme
    (run-scheme (concat scheme " " heapload))

    ;; open file
    (select-frame-set-input-focus right-frame)
    (if filename (find-file filename))))

    (load "---MINLOGPATH---/util/minlog-unicode.el")
