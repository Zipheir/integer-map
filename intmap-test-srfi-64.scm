;;; Generic test framework using SRFI 64.
(import (srfi 64))

(define-syntax test
  (syntax-rules ()
    ((test . rest) (test-equal . rest))))

(include "test-generic.scm")
