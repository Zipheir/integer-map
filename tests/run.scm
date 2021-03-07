;;; CHICKEN test framework using the test egg.
(import (srfi 1)
        (srfi 128)
        (srfi 189)
        (integer-map)
        (test))

(include "../test-generic.scm")
(test-exit)
