;;; Generic test framework using SRFI 64.
(import (srfi 1)
        (srfi 128)
        (srfi 189)
        (srfi 64)
        (integer-map))

(define-syntax test
  (syntax-rules ()
    ((test . rest) (test-equal . rest))))

(include "test-generic.scm")
