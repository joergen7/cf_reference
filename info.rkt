;;-----------------------------------------------------------------------------
;;
;; cf_reference
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

#lang info
(define collection "cf_reference")
(define deps '("base"))
(define build-deps '("scribble-lib" "racket-doc" "rackunit-lib"))
(define scribblings '(("scribblings/cf_reference.scrbl" ())))
(define pkg-desc "semantic reference of the Cuneiform distributed programming language")
(define version "0.1.1")
(define pkg-authors '(joergen7))
