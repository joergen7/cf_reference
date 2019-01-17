#lang racket/base

(require redex
         "cfl-syntax-static.rkt")

(provide cfl-d)

(define-extended-language cfl-d cfl

  (v ::= (λ ([x_!_ : T] ...) → T (ntv e))
         (λ ([x_!_ : T] ...) → T (frn l s))
         (str s)
         (file s)
         true
         false
         (nil T)
         (cons v v)
         (rcd ([x_!_ = v] ...)))

  (E ::= hole
         (app E ([x = e] ...))
         (app (λ ([x : T] ...) → T (frn l s)) ([x = e] ... [x = E] [x = e] ...))
         (fix E)
         (E == e)
         (e == E)
         (E ∧ e)
         (e ∧ E)
         (E ∨ e)
         (e ∨ E)
         (¬ E)
         (isnil E)
         (if E then e else e)
         (cons E e)
         (cons e E)
         (E + e)
         (e + E)
         (for ([x : T ← e] ... [x : T ← E] [x : T ← e] ...) do e : T)
         (fold [x : T = E] [x : T ← e] do e)
         (fold [x : T = e] [x : T ← E] do e)
         (rcd ([x = e] ... [x = E] [x = e] ...))
         (π x E))

  (p ::= ((e ...) ([e v] ...) e)) 

)

(module+ main
  (render-language cfl-d))

(module+ test

  (define-term frn-lam1 (λ ([x : Str]) → Str (frn Bash "blub")))
  (define-term frn-app1 (app frn-lam1 ([x = (str "bla")])))
  
  (define-term frn-lam2 (λ ([y : Str]) → Str (frn Bash "blub")))
  (define-term frn-app2 (app frn-lam2 ([y = (str "bla")])))

  (test-equal (alpha-equivalent? cfl-d (term (() () frn-app1))
                                       (term (() () frn-app2)))
              #t)

  (test-results)
)
