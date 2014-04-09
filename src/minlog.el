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

; MINLOG directory
(if (getenv "MINLOGPATH")
    (setq minlogpath (getenv "MINLOGPATH"))
  (setq minlogpath "---MINLOGPATH---"))

; Minlog minor mode
(load "---MINLOGELPATH---/minlog-mode.el")
(add-hook 'scheme-mode-hook 'minlog-font-lock-mode 'append)
(add-hook 'inferior-scheme-mode-hook 'minlog-font-lock-mode 'append)

; which scheme to use ?
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


; is there a heap file ?
(if (and (file-readable-p (concat minlogpath "/minlog.heap"))
         (or (string= scheme "petite")
             (string= scheme "/usr/bin/petite")))
    (setq heapload
          (concat "-h " minlogpath "/minlog.heap " minlogpath "/welcome.scm"))
  (setq heapload (concat minlogpath "/init.scm")))


(run-scheme(concat scheme " " heapload))

;; set-up windows
(delete-other-windows)
(split-window-vertically)
(other-window 1)
(set-buffer "*scheme*")
(rename-buffer "*minlog*" t)
(setq scheme-buffer "*minlog*")
(other-window 1)
(let ((text (concat
             "\t\t Minlog loading...\n\n\t\t To "
             (propertize "load" 'face '(foreground-color . "green"))
             " a file use "
             (propertize "Control-x Control-f" 'face '(foreground-color . "red"))
             ", \n\t\t to "
             (propertize "save" 'face '(foreground-color . "green"))
             " your minlog script in a new file \n\t\t use "
             (propertize "Control-x Control-w" 'face '(foreground-color . "red"))
             ", \n\t\t to "
             (propertize "begin" 'face '(foreground-color . "green") )
             " a new script just type in."))
      (splash-buffer (generate-new-buffer "Minlog loading...")))
  (switch-to-buffer splash-buffer)
  (insert "\n\n\n\n\n\n\n\n\n" text)
  (set-buffer-modified-p nil)
  (sit-for 100000) ; wait until eternity or a keypress
  (kill-buffer splash-buffer)
  (switch-to-buffer (get-buffer "*scratch*"))
  (scheme-mode)
  )
