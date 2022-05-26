(require 'easy-mmode)

(defconst minlog-font-lock-keywords-alist
    (mapcar (lambda (regex-char-pair)
        `(,(car regex-char-pair)
            (0 (prog1 ()
                (compose-region (match-beginning 1) (match-end 1)
                    ;; The first argument to concat is a string containing a literal tab
                    ,(concat "   " (list (decode-char 'ucs (cadr regex-char-pair)))))))))
        '(("[^-]\\(->\\)"                       #X27f6) ; implication arrow
          ("\\(-->\\)"                          #X27ff) ; nc-implication arrow
          ("[^=]\\(=>\\)"                       #X21d2) ; type arrow
          ("\\(==>\\)"                          #X27f9)
          ("[^=]\\(==\\)[^=>]"                  #X2261) ; equivalence
          ("[^=]\\(===\\)[^=>]"                 #X224b) ; equivalence of reals
          ("[^<]\\(<=\\)"                       #X2264) ; less-than
        ; ("\\(<<\\)="                          #X226a) ; real less-than
          ("[ \t\n(:\"]\\(all\\)n?c? "          #X2200) ; all, allc, allnc
        ; ("[ \t\n(:\"]all\\(nc\\) "            #X207f) ; allnc - nc superscript
          ("[ \t\n(:\"]\\(ex\\)n?c? "           #X2203) ; ex, exc, exnc
          ("[ \t\n)]\\(&\\)[ \t\n(]"            #X2227) ; and
          ("[ \t\n)]\\(&&\\)[ \t\n(]"           #X2227) ; and
          ("[ \t\n)]\\(or\\)[udlr][ \t\n(]"     #X2228) ; oru, ord, orl, orr
          ("[ \t\n():\"]\\(bot\\)[ \t\n()\"]"   #X22A5) ; bot
          ("[>@(\"]\\(boole\\)[=@)\"]"          #X1D539); boole
          ("[>@(\"]\\(nat\\)[=@)\"]"            #X2115) ; nat
          ("[>@(\"]\\(pos\\)[=@)\"]"            #X2119) ; pos
          ("[>@(\"]\\(int\\)[=@)\"]"            #X2124) ; int
          ("[>@(\"]\\(rat\\)[=@)\"]"            #X211a) ; rat
          ("[>@(\"]\\(rea\\)[=@)\"]"            #X211d) ; rea
        ; ("[ \t\n(\"]\\(lambda\\)[ \t\n]"      #X03bb) ; lambda ?
       )))

(defun add-minlog-symbol-keywords ()
  (font-lock-add-keywords nil minlog-font-lock-keywords-alist))
(defun remove-minlog-symbol-keywords ()
  (font-lock-remove-keywords nil minlog-font-lock-keywords-alist))

(easy-mmode-define-minor-mode minlog-font-lock-mode
 "Unicode formulas for minlog" nil " MinlogUnicode")

(add-hook 'minlog-font-lock-mode-on-hook 'add-minlog-symbol-keywords)
(add-hook 'minlog-font-lock-mode-off-hook 'remove-minlog-symbol-keywords)
;; do not automatically load unicode mode
;; (add-hook 'scheme-mode-hook 'minlog-font-lock-mode 'append)
;; (add-hook 'inferior-scheme-mode-hook 'minlog-font-lock-mode 'append)
