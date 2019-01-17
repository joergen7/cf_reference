#lang racket/base

(require redex)
(provide cfl)

(define-language cfl

  (e ::= x
         (λ ([x_!_ : T] ...) → T (ntv e))
         (λ ([x_!_ : T] ...) → T (frn l s))
         (app e ([x = e] ...))
         (fix e)
         (fut e)
         (str s)
         (file s)
         true
         false
         (e == e)
         (e ∧ e)
         (e ∨ e)
         (¬ e)
         (isnil e)
         (if e then e else e)
         (nil T)
         (cons e e)
         (e + e)
         (for ([x_!_ : T ← e] ...) do e : T)
         (fold [x_!_ : T = e] [x_!_ : T ← e] do e)
         (rcd ([x_!_ = e] ...))
         (π x e)
         (error s : T))

  (x ::= variable-not-otherwise-mentioned)
  
  (s ::= string)

  (l ::= Bash
         Erlang
         Elixir
         Java
         Javascript
         Matlab
         Octave
         Perl
         Python
         R
         Racket)

  (T ::= Str
         File
         Bool
         (Fn ([x : T] ...) → T)
         (Lst T)
         (Rcd ([x : T] ...)))

  #:binding-forms
  (λ ([x : T] ...) → T_ret (ntv e #:refers-to (shadow x ...)))
  (app e_f #:refers-to (shadow x ...) ([x = e] ...))
)

(module+ main
  (render-language cfl))


(module+ test

  (test-equal (redex-match? cfl T (term Str)) #t)
  (test-equal (redex-match? cfl T (term File)) #t)
  (test-equal (redex-match? cfl T (term Bool)) #t)

  (test-equal (alpha-equivalent? cfl
                                 (term (λ ([x : Str]) → Str (ntv x)))
                                 (term (λ ([y : Str]) → Str (ntv y))))
              #t)

  (test-equal (alpha-equivalent? cfl
                                 (term (app (λ ([x : Str]) → Str (ntv x)) ([x = (str "blub")])))
                                 (term (app (λ ([y : Str]) → Str (ntv y)) ([y = (str "blub")]))))
              #t)

  (test-equal (redex-match? cfl e (term (λ ([x : Str] [y : Str]) → Str (ntv x)))) #t)
  (test-equal (redex-match? cfl e (term (λ ([x : Str] [x : Str]) → Str (ntv x)))) #f)
  (test-equal (redex-match? cfl e (term (λ ([x : Str] [y : Str]) → Str (frn Bash "blub")))) #t)
  (test-equal (redex-match? cfl e (term (λ ([x : Str] [x : Str]) → Str (frn Bash "blub")))) #f)
  (test-equal (redex-match? cfl e (term (for ([x : Str ← l1] [y : Str ← l2]) do x : Str))) #t)
  (test-equal (redex-match? cfl e (term (for ([x : Str ← l1] [x : Str ← l2]) do x : Str))) #f)
  (test-equal (redex-match? cfl e (term (fold [x : Str = (str "0")] [y : Str ← l1] do x))) #t)
  (test-equal (redex-match? cfl e (term (fold [x : Str = (str "0")] [x : Str ← l1] do x))) #f)
  (test-equal (redex-match? cfl e (term (rcd ([x = (str "bla")] [y = (str "blub")])))) #t)
  (test-equal (redex-match? cfl e (term (rcd ([x = (str "bla")] [x = (str "blub")])))) #f)
  


  (test-results)
)