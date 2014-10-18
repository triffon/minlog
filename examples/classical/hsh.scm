;; 2014-10-13.  hsh.scm

;; We show classically the existence of an n such that h(s(h n)) \ne n
;; and extract a (somewhat unexpected) program from it (due to U.Berger)

;; (load "~/git/minlog/init.scm")

(set! COMMENT-FLAG #f)
(libload "nat.scm")
(set! COMMENT-FLAG #t)

(add-var-name "f" "g" "h" "s" (py "nat=>nat"))

;; SurjLemma
(set-goal "all f,g(all m excl n g(f n)=m -> all m excl n g n=m)")
(search)
;; Proof finished.
(save "SurjLemma")

;; InjLemma
(set-goal "all f,g(all n,m(g(f n)=g(f m) -> n=m) -> all n,m(f n=f m -> n=m))")
(assume "f" "g" "gf-inj" "n" "m" "fn=fm")
(use "gf-inj")
(simp "fn=fm")
(use "Truth")
;; Proof finished.
(save "InjLemma")

;; SurjInjLemma
(set-goal "all f,g(
 all m excl n g(f n)=m -> all n,m(g n=g m -> n=m) -> all m excl n f n=m)")
(search)
;; Proof finished.
(save "SurjInjLemma")

;; hshTheorem
(set-goal "all s,h(all n(s n=0 -> bot) -> all n h(s(h n))=n -> bot)")
(assume "s" "h" "s-not-0" "hsh-is-id")
(cut "all m excl n h(s(h n))=m")
(assume "hsh-surj")
(cut "all m excl n h(s n)=m")
(assume "hs-surj")
(cut "all n,m(h(s(h n))=h(s(h m)) -> n=m)")
(assume "hsh-inj")
(cut "all n,m(s(h n)=s(h m) -> n=m)")
(assume "sh-inj")
(cut "all n,m(h n=h m -> n=m)")
(assume "h-inj")
(cut "all m excl n s n=m")
(assume "s-surj")
(use-with "s-surj" (pt "0") "s-not-0")
(use "SurjInjLemma" (pt "h"))
(use "hs-surj")
(use "h-inj")
(use "InjLemma" (pt "s"))
(use "sh-inj")
(use-with "InjLemma" (pt "[n]s(h n)") (pt "h") "?")
(ng #t)
;; (use-with "InjLemma" (pt "C s h") (pt "h") "?")
(use "hsh-inj")
(assume "n" "m")
(inst-with-to "hsh-is-id" (pt "n") "hshn-is-n")
(simp "hshn-is-n")
(inst-with-to "hsh-is-id" (pt "m") "hshn-is-m")
(simp "hshn-is-m")
(assume "n=m")
(use "n=m")
(use-with "SurjLemma" (pt "h") (pt "[n]h(s n)") "?")
(ng #t)
;; (use-with "SurjLemma" (pt "h") (pt "C h s") "?")
(use "hsh-surj")
(assume "m" "m-not-hsh-value")
(use "m-not-hsh-value" (pt "m"))
(use "hsh-is-id")
;; Proof finished.
(save "hshTheorem")

(define min-excl-proof
  (np (expand-thm
       (proof-to-reduced-goedel-gentzen-translation
	(theorem-name-to-proof "hshTheorem"))
       "SurjLemma")))

(define eterm (atr-min-excl-proof-to-structured-extracted-term
	       min-excl-proof))
(define neterm (nt eterm))
(pp (rename-variables neterm))

;; [f,f0]
;;  [if (f0(f(f0(f0 0)))=f0 0)
;;    [if (f0(f(f0(f(f0(f0 0)))))=f(f0(f0 0))) 0 (f(f0(f0 0)))]
;;    (f0 0)]

;; With renaming (f -> s and f0 -> h)

;; [s,h]
;;  [if (h(s(h(h 0)))=h 0)
;;    [if (h(s(h(s(h(h 0)))))=s(h(h 0))) 0 (s(h(h 0)))]
;;    (h 0)]
