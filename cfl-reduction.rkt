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

(require redex
         "cfl-syntax-dynamic.rkt")

(provide cfl->)

(define cfl->
  (reduction-relation
   cfl-d
   #:domain p

   (~> (app (λ () → T_ret (ntv e_body)) ())
      e_body
      E-β-base)

   (~> (app (λ ([x_1 : T_1] [x_i : T_i] ...) → T_ret (ntv e_body))
           ([x_2 = e_1] [x_j = e_j] ...))

      (app (λ ([x_i : T_i] ...) → T_ret (ntv (substitute e_body x_1 e_1)))
           ([x_j = e_j] ...))

      E-β-ind)

   (~> (fix (λ ([x_f : T_f] [x_i : T_i] ...) → T_ret (ntv e_body)))

        (λ ([x_i : T_i] ...)
          (ntv (app (λ ([x_f : T_f]) (ntv e_body))
                    ([x_f = (fix (λ ([x_f : T_f] [x_i : T_i] ...) → T_ret (ntv e_body)))]))))

       E-fix)

   (~> ((str s_1) == (str s_1))
       true
       E-cmp-seq)

   (~> ((str s_1) == (str s_2))
       false
       (side-condition (not (equal? (term s_1) (term s_2))))
       E-cmp-sneq)

   (~> (true == true)   true  E-cmp-tt)
   (~> (true == false)  false E-cmp-tf)
   (~> (false == true)  false E-cmp-ft)
   (~> (false == false) true  E-cmp-ff)

   (~> ((nil T_1) == (nil T_2))
       true
       E-cmp-lst-base)

   (~> ((nil T_1) == (cons e_21 e_22))
       false
       E-cmp-lst-nil1)

   (~> ((cons e_11 e_12) == (nil T_2))
       false
       E-cmp-lst-nil2)

   (~> ((cons e_11 e_12) == (cons e_21 e_22))
       ((e_11 == e_21) ∧ (e_12 == e_22))
       E-cmp-lst-ind)

   (~> ((rcd ()) == (rcd ()))
       true
       E-cmp-rcd-base)

   (~> (   (rcd ([x_1 = e_1] [x_i = e_i] ...))
        == (rcd ([x_j = e_j] ... [x_1 = e_2] [x_k = e_k] ...)))
       (   (e_1 == e_2) ∧ ((rcd ([x_i = e_i] ...))
        == (rcd ([x_j = e_j] ... [x_k = e_k] ...))))
       E-cmp-rcd-ind)

   (~> (true ∧ true)    true  E-and-tt)
   (~> (false ∧ e_2)    false E-and-f1)
   (~> (e_1 ∧ false)    false E-and-f2)

   (~> (false ∨ false)  false E-or-ff)
   (~> (true ∨ e_2)     true  E-or-t1)
   (~> (e_1 ∨ true)     true  E-or-t2)

   (~> (¬ true)         false E-not-t)
   (~> (¬ false)        true  E-not-f)

   (~> (isnil (nil T_1))      true  E-isnil-nil)
   (~> (isnil (cons e_1 e_2)) false E-isnil-cons)

   (~> (if true then e_1 else e_2)  e_1 E-if-t)
   (~> (if false then e_1 else e_2) e_2 E-if-f)

   (~> (hd (nil T_1) e_2)        e_2  E-hd-nil)
   (~> (hd (cons e_11 e_12) e_2) e_11 E-hd-cons)

   (~> (tl (nil T_1) e_2)        e_2  E-tl-nil)
   (~> (tl (cons e_11 e_12) e_2) e_12 E-tl-cons)

   (~> ((nil T_1) + e_2)        e_2                      E-append-base)
   (~> ((cons e_11 e_12) + e_2) (cons e_11 (e_12 + e_2)) E-append-ind)

   (~> (for T_body ([x_i : T_i ← e_i] ... [x_1 : T_1 ← (nil T_2)] [x_j : T_j ← e_j] ...) do
         e_body)
       (nil T_body)
       E-for-base)

   (~> (for T_body ([x_i : T_i ← (cons e_i1 e_i2)] ...) do e_body)
       (cons (app (λ ([x_i : T_i] ...) → T_body (ntv e_body)) ([x_i = e_i1] ...))
             (for T_body ([x_i : T_i ← e_i2] ...) do e_body))
       E-for-ind)

   (~> (fold [x_acc : T_acc = e_acc] [x_1 : T_1 ← (nil T_2)] do e_body)
       e_acc
       E-fold-base)

   (~> (fold [x_acc : T_acc = e_acc]
             [x_1 : T_1 ← (cons e_11 e_12)]
             do e_body)
      
       (fold [x_acc : T_acc = (app (λ ([x_acc : T_acc] [x_1 : T_1]) → T_acc (ntv e_body))
                                   ([x_acc = e_acc] [x_1 = e_11]))]
             [x_1 : T_1 ← e_12]
             do e_body)

       E-fold-ind)

   (~> (π x_1 (rcd ([x_i = e_i] ... [x_1 = e_1] [x_j = e_j] ...)))
       e_1
       E-π)
        
   (--> ((e_i ...)
         ([e_j v_j] ...)
         (in-hole E (app (λ ([x_k : T_k] ...) → T_ret (frn l s))
                         ([x_l = v_l] ...))))

        (((app (λ ([x_l : T_k] ...) → T_ret (frn l s)) ([x_l = v_l] ...))
          e_i ...)
         ([e_j v_j] ...)
         (in-hole E (fut (app (λ ([x_k : T_k] ...) → T_ret (frn l s))
                              ([x_l = v_l] ...)))))
        E-σ)

   (--> ((e_i ...)
         ([e_j v_j] ... [e_1 v_1] [e_k v_k] ...)
         (in-hole E (fut e_1)))

        ((e_i ...)
         ([e_j v_j] ... [e_1 v_1] [e_k v_k] ...)
         (in-hole E v_1))

        E-ρ)

   (--> ((e_i ...)
         ([e_j v_j] ...)
         (in-hole E (error s : T)))

        (() ([e_j v_j] ...) (error s : T))

        (side-condition
         (not (and (equal? (term E) (term hole))
                   (equal? (term (e_i ...)) (term ())))))
        
        E-error)
        
   
   with

   ((--> ((e_i ...) ([e_j v_j] ...) (in-hole E a))
         ((e_i ...) ([e_j v_j] ...) (in-hole E b)))

    (~> a b))))

(module+ main
  (render-reduction-relation cfl->))

(module+ test

  (define-term str1 (str "blub"))
  (define-term str2 (app (λ () → Str (ntv str1)) ()))

  (define-term frn-lam0 (λ () → Str (frn Bash "blub")))
  (define-term frn-app0 (app frn-lam0 ()))

  (define-term frn-lam1 (λ ([x : Str]) → Str (frn Bash "blub")))
  (define-term frn-app1 (app frn-lam1 ([x = (str "bla")])))
  
  (test-->
   cfl->
   (term (() () str2))
   (term (() () str1)))

  (test-->
   cfl->
   (term (() () frn-app0))
   (term ((frn-app0) () (fut frn-app0))))

  (test-->
   cfl->
   #:equiv (λ (a b) (alpha-equivalent? cfl-d a b))
   (term (() () frn-app1))
   (term ((frn-app1) () (fut frn-app1))))

  (test--> cfl-> (term (() () (error "blub" : Str))))
         

  (test-results))

