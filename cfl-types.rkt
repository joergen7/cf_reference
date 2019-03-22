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

(define-extended-language cfl-t cfl

  (Γ ::= ([x : T] ...)))

(define-judgment-form cfl-t
  #:mode (comparable I I)
  #:contract (comparable T T)

  [---------------------- C-bool
   (comparable Bool Bool)]

  [-------------------- C-str
   (comparable Str Str)]

  [(comparable T_1 T_2)
   -------------------------------- C-lst
   (comparable (Lst T_1) (Lst T_2))]

  [------------------------------ C-rcd-base
   (comparable (Rcd ()) (Rcd ()))]

  [(comparable T_1 T_2)
   (comparable (Rcd ([x_i : T_i] ...))
               (Rcd ([x_j : T_j] ... [x_k : T_k] ...)))
   ---------------------------------------------------------------- C-rcd-ind
   (comparable (Rcd ([x_1 : T_1] [x_i : T_i] ...))
               (Rcd ([x_j : T_j] ... [x_1 : T_2] [x_k : T_k] ...)))]
  )


(define-judgment-form cfl-t
  #:mode (type I I I I O)
  #:contract (type Γ ⊢ e : T)

  [(side-condition ,(not (member (term x_1) (term (x_i ...)))))
   ------------------------------------------------------------ T-var
   (type ([x_i : T_i] ... [x_1 : T_1] [x_j : T_j] ...)
       ⊢ x_1
       : T_1)]

  [(type ([x_j : T_j] ... [x_i : T_i] ...) ⊢ e_body : T_ret)
   --------------------------------------------------------- T-λ-ntv
   (type ([x_i : T_i] ...)
       ⊢ (λ ([x_j : T_j] ...) → T_ret (ntv e_body))
       : (Fn ([x_j : T_j] ...) → T_ret))]

  [--------------------------------------------- T-λ-frn
   (type Γ
       ⊢ (λ ([x_i : T_i] ...) → T_ret (frn l s))
       : (Fn ([x_i : T_i] ...) → T_ret))]

  [(type Γ ⊢ e_f : (Fn ([x_i : T_i] ...) → T_ret))
   (type Γ ⊢ e_i : T_i) ...
   ---------------------------------------------- T-app
   (type Γ ⊢ (app e_f ([x_i = e_i] ...)) : T_ret)]

  [(type Γ ⊢ e_f : (Fn ([x_f : (Fn ([x_i : T_i] ...) → T_ret)]
                        [x_i : T_i] ...) → T_ret))
   ----------------------------------------------------------- T-fix
   (type Γ ⊢ (fix e_f) : (Fn ([x_i : T_i] ...) → T_ret))]

  [------------------------ T-str
   (type Γ ⊢ (str s) : Str)]

  [-------------------------- T-file
   (type Γ ⊢ (file s) : File)]

  [---------------------- T-true
   (type Γ ⊢ true : Bool)]

  [----------------------- T-false
   (type Γ ⊢ false : Bool)]

  [(type Γ ⊢ e_1 : T_1)
   (type Γ ⊢ e_2 : T_2)
   (comparable T_1 T_2)
   ------------------------------ T-cmp
   (type Γ ⊢ (e_1 == e_2) : Bool)]

  [(type Γ ⊢ e_1 : Bool)
   (type Γ ⊢ e_2 : Bool)
   ----------------------------- T-conj
   (type Γ ⊢ (e_1 ∧ e_2) : Bool)]

  [(type Γ ⊢ e_1 : Bool)
   (type Γ ⊢ e_2 : Bool)
   ----------------------------- T-disj
   (type Γ ⊢ (e_1 ∨ e_2) : Bool)]

  [(type Γ ⊢ e_1 : Bool)
   ------------------------- T-neg
   (type Γ ⊢ (¬ e_1) : Bool)]

  [(type Γ ⊢ e_1 : (Lst T_1))
   ----------------------------- T-isnil
   (type Γ ⊢ (isnil e_1) : Bool)]

  [(type Γ ⊢ e_1 : Bool)
   (type Γ ⊢ e_2 : T_23)
   (type Γ ⊢ e_3 : T_23)
   -------------------------------------------- T-if
   (type Γ ⊢ (if e_1 then e_2 else e_3) : T_23)]

  [-------------------------------- T-nil
   (type Γ ⊢ (nil T_1) : (Lst T_1))]

  [(type Γ ⊢ e_1 : T_12)
   (type Γ ⊢ e_2 : (Lst T_12))
   -------------------------------------- T-cons
   (type Γ ⊢ (cons e_1 e_2) : (Lst T_12))]

  [(type Γ ⊢ e_1 : (Lst T_12))
   (type Γ ⊢ e_2 : T_12)
   ----------------------------- T-hd
   (type Γ ⊢ (hd e_1 e_2) : T_12)]

  [(type Γ ⊢ e_1 : (Lst T_12))
   (type Γ ⊢ e_2 : (Lst T_12))
   ----------------------------------- T-tl
   (type Γ ⊢ (tl e_1 e_2) : (Lst T_12))]

  [(type Γ ⊢ e_1 : (Lst T_12))
   (type Γ ⊢ e_2 : (Lst T_12))
   ----------------------------------- T-append
   (type Γ ⊢ (e_1 + e_2) : (Lst T_12))]

  [(type ([x_i : T_i] ...) ⊢ e_j : (Lst T_j)) ...
   (type ([x_j : T_j] ... [x_i : T_i] ...)
       ⊢ e_body
       : T_body)
   ------------------------------------------------------ T-for
   (type ([x_i : T_i] ...)
       ⊢ (for T_body ([x_j : T_j ← e_j] ...) do e_body)
       : (Lst T_body))]

  [(type ([x_i : T_i] ...) ⊢ e_acc : T_acc)
   (type ([x_i : T_i] ...) ⊢ e_1 : (Lst T_1))
   (type ([x_acc : T_acc] [x_1 : T_1] [x_i : T_i] ...)
       ⊢ e_body
       : T_acc)
   --------------------------------------------------- T-fold
   (type ([x_i : T_i] ...)
       ⊢ (fold [x_acc : T_acc = e_acc]
               [x_1 : T_1 ← e_1] do e_body)
       : T_acc)]

  [(type Γ ⊢ e_i : T_i) ...
   ------------------------------ T-rcd
   (type Γ
       ⊢ (rcd ([x_i = e_i] ...))
       : (Rcd ([x_i : T_i] ...)))]

  [(type Γ ⊢ e_rcd : (Rcd ([x_i : T_i] ...
                           [x_1 : T_1]
                           [x_j : T_j] ...)))
   ------------------------------------------ T-π
   (type Γ ⊢ (π x_1 e_rcd) : T_1)]

  [-------------------------------- T-error
   (type Γ ⊢ (error s : T_1) : T_1)]
  
  )

(module+ test
  (test-equal (judgment-holds (type () ⊢ x : T) T) '())
  (test-judgment-holds (type ([x : Str]) ⊢ x : Str))
  (test-judgment-holds (type ([x : Str] [y : File]) ⊢ x : Str))
  (test-judgment-holds (type ([y : File] [x : Str]) ⊢ x : Str))
  (test-equal (judgment-holds (type ([x : Str] [x : File]) ⊢ x : T) T) '(Str))
  (test-judgment-holds (type () ⊢ (λ ([x : Str]) → Str (ntv x)) : (Fn ([x : Str]) → Str)))
  (test-equal (judgment-holds (type () ⊢ (λ ([x : Str]) → Str (ntv (file "bla"))) : T) T) '())
  (test-judgment-holds (type () ⊢ (λ ([x : Str]) → Str (frn Bash "blub")) : (Fn ([x : Str]) → Str)))
  (test-judgment-holds (type () ⊢ (str "blub") : Str))
  (test-judgment-holds (type () ⊢ (file "bla") : File))
  (test-judgment-holds (type () ⊢ true : Bool))
  (test-judgment-holds (type () ⊢ false : Bool))
  

  (test-results))