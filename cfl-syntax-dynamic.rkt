;;-----------------------------------------------------------------------------
;;
;; Semantic reference of the Cuneiform distributed programming
;; language
;;
;; Copyright 2016-2019 Jörgen Brandt <joergen@cuneiform-lang.org>
;;
;; Licensed under the Apache License, Version 2.0 (the "License");
;; you may not use this file except in compliance with the License.
;; You may obtain a copy of the License at
;;
;;     http://www.apache.org/licenses/LICENSE-2.0
;;
;; Unless required by applicable law or agreed to in writing, software
;; distributed under the License is distributed on an "AS IS" BASIS,
;; WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
;; See the License for the specific language governing permissions and
;; limitations under the License.
;;
;;-----------------------------------------------------------------------------


#lang racket/base

(require redex
         "cfl-syntax-static.rkt")

(provide cfl-d)

(define-extended-language cfl-d cfl

  (v ::= (λ ([x_!_ : T] ...) (ntv e))
         (λ ([x_!_ : T] ...) (frn x T l s))
         (str s)
         (file s)
         true
         false
         (nil T)
         (cons v v)
         (rcd ([x_!_ = v] ...)))

  (E ::= hole
         (app E ([x = e] ...))
         (app (λ ([x : T] ...) (frn x T l s)) ([x = e] ... [x = E] [x = e] ...))
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
         (hd E e)
         (tl E e)
         (E + e)
         (e + E)
         (for T ([x : T ← e] ... [x : T ← E] [x : T ← e] ...) do e)
         (fold [x : T = e] [x : T ← E] do e)
         (rcd ([x = e] ... [x = E] [x = e] ...))
         (π x E))

  (p ::= ((e ...) ([e e] ...) e)) 

)

(module+ main
  (render-language cfl-d))

(module+ test

  (define-term frn-lam1 (λ ([x : Str]) (frn f Str Bash "blub")))
  (define-term frn-app1 (app frn-lam1 ([x = (str "bla")])))
  
  (define-term frn-lam2 (λ ([y : Str]) (frn f Str Bash "blub")))
  (define-term frn-app2 (app frn-lam2 ([y = (str "bla")])))

  (test-equal (alpha-equivalent? cfl-d (term (() () frn-app1))
                                       (term (() () frn-app2)))
              #t)

  (test-results)
)
