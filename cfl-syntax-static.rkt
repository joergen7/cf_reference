;;-----------------------------------------------------------------------------
;;
;; Semantic reference of the Cuneiform distributed programming
;; language
;;
;; Copyright 2016-2019 Jörgen Brandt <joergen.brandt@onlinehome.de>
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
         (for T ([x_!_ : T ← e] ...) do e)
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
  (for T_body ([x : T ← e] ...) do e_body #:refers-to (shadow x ...))
  (fold [x_acc : T_acc = e_acc] [x_1 : T_1 ← e_1] do e_body #:refers-to (shadow x_acc x_1))
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

  (test-equal (alpha-equivalent? cfl
                                 (term (for Str ([x : Str ← (nil Str)]) do x))
                                 (term (for Str ([y : Str ← (nil Str)]) do y)))
              #t)

  (test-equal (alpha-equivalent? cfl
                                 (term (fold [x : Str = (str "bla")] [y : Str ← (nil Str)] do x))
                                 (term (fold [a : Str = (str "bla")] [b : Str ← (nil Str)] do a)))
              #t)

  (test-equal (redex-match? cfl e (term (λ ([x : Str] [y : Str]) → Str (ntv x)))) #t)
  (test-equal (redex-match? cfl e (term (λ ([x : Str] [x : Str]) → Str (ntv x)))) #f)
  (test-equal (redex-match? cfl e (term (λ ([x : Str] [y : Str]) → Str (frn Bash "blub")))) #t)
  (test-equal (redex-match? cfl e (term (λ ([x : Str] [x : Str]) → Str (frn Bash "blub")))) #f)
  (test-equal (redex-match? cfl e (term (λ ([x : Str]) → Str (ntv x)))) #t)
  (test-equal (redex-match? cfl e (term (app (λ ([x : Str]) → Str (ntv x)) ([x = (str "bla")])))) #t)
  (test-equal (redex-match? cfl e (term (for Str ([x : Str ← l1] [y : Str ← l2]) do x))) #t)
  (test-equal (redex-match? cfl e (term (for Str ([x : Str ← l1] [x : Str ← l2]) do x))) #f)
  (test-equal (redex-match? cfl e (term (fold [x : Str = (str "0")] [y : Str ← l1] do x))) #t)
  (test-equal (redex-match? cfl e (term (fold [x : Str = (str "0")] [x : Str ← l1] do x))) #f)
  (test-equal (redex-match? cfl e (term (rcd ([x = (str "bla")] [y = (str "blub")])))) #t)
  (test-equal (redex-match? cfl e (term (rcd ([x = (str "bla")] [x = (str "blub")])))) #f)
  


  (test-results)
)