;;; Test framework using CHICKEN's test egg.
(import (srfi 1)
        (srfi 128)
        (srfi 158)
        (integer-map)
        (test))

;; SRFI 64 shim.

(define-syntax test-eqv
  (syntax-rules ()
    ((test-eqv expected expr)
     (test expected expr))))

(define-syntax test-equal
  (syntax-rules ()
    ((test-equal expected expr)
     (test expected expr))))

(include "test-generic.scm")

(test-exit)
