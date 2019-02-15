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

(module+ main

  (require redex
           "cfl-reduction.rkt")

  ;; reduction-bool01
  (define-term e1 ((¬ false) ∧ (¬ false)))
  (define-term p1 (() () e1))
  (traces cfl-> (term p1))

  ;; reduction-error01
  (define-term e2 (¬ (error "kaboom" : Bool)))
  (define-term p2 (() () e2))
  (traces cfl-> (term p2))

  ;; reduction-error02
  (define-term e3
    (app (λ ([x : Bool]) → Str (ntv (str "blub")))
         ([x = (error "kaboom" : Bool)])))
  (define-term p3 (() () e3))
  (traces cfl-> (term p3))

  ;; reduction-error03
  (define-term e4 (true ∨ (error "kaboom" : Bool)))
  (define-term p4 (() () e4))
  (traces cfl-> (term p4))

  ;; reduction-cmp
  (define-term e5 (false == ((str "bla") == (str "blub"))))
  (define-term p5 (() () e5))
  (traces cfl-> (term p5))

  ;; reduction-cnd
  (define-term e6 (if (¬ true) then false else (¬ false)))
  (define-term p6 (() () e6))
  (traces cfl-> (term p6))

  ;; reduction-app
  (define-term e16 (app (λ ([x : Str]) → Str (ntv x)) ([x = (str "bla")])))
  (define-term p16 (() () e16))
  (traces cfl-> (term p16))
  
  ;; reduction-append
  (define-term e17 (  (cons (str "a") (cons (str "b") (nil Str)))
                    + (cons (str "c") (cons (str "d") (nil Str)))))
  (define-term p17 (() () e17))
  (traces cfl-> (term p17))

  ;; reduction-for
  (define-term e18 (for Bool
                        ([x : Bool ← (cons true (cons false (cons false (nil Bool))))])
                    do  (¬ x)))
  (define-term p18 (() () e18))
  (traces cfl-> (term p18))

  ;; reduction-fold
  (define-term e19 (fold [acc : (Lst Str) = (nil Str)]
                         [x : Str ← (cons (str "a") (cons (str "b") (nil Str)))]
                    do   (cons x acc)))
  (define-term p19 (() () e19))
  (traces cfl-> (term p19))


  
  ;; reduction-proj
  (define-term e20 (π b (rcd ([a = (str "ok")] [b = true]))))
  (define-term p20 (() () e20))
  (traces cfl-> (term p20))

  
  )
