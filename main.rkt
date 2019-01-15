#lang racket/base

(module+ main

  (require redex
           "cfl-reduction.rkt")

  ;; example-bool01
  (define-term e1 ((¬ false) ∧ (¬ false)))
  (define-term p1 (() () e1))
  (traces cfl-> (term p1))

  ;; example-error01
  (define-term e2 (¬ (error "kaboom" : Bool)))
  (define-term p2 (() () e2))
  (traces cfl-> (term p2))

  ;; example-error02
  (define-term e3
    (app (λ ([x : Bool]) → Str (ntv (str "blub")))
         ([x = (error "kaboom" : Bool)])))
  (define-term p3 (() () e3))
  (traces cfl-> (term p3))

  ;; example-error03
  (define-term e4 (true ∨ (error "kaboom" : Bool)))
  (define-term p4 (() () e4))
  (traces cfl-> (term p4))

  ;; example-cmp
  (define-term e5 (false == ((str "bla") == (str "blub"))))
  (define-term p5 (() () e5))
  (traces cfl-> (term p5))

  ;; example-cnd
  (define-term e6 (if (¬ true) then false else (¬ false)))
  (define-term p6 (() () e6))
  (traces cfl-> (term p6))



  )
