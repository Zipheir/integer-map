(define-library (integer-map)
  (import (scheme base)
          (scheme case-lambda)
          (only (srfi 1) fold every)
          (only (srfi 128) comparator? =?)
          (srfi 189)
          (srfi 143))

  (cond-expand
    ((library (srfi 145))
     (import (srfi 145)))
    (else
     (begin
      (define-syntax assume
        (syntax-rules ()
          ((_ expr . _)
           (or expr (car 0))))))))

  (export
   imapping-delete-min imapping-delete-max
   imapping-update-min imapping-update-max
   imapping-update-min/key imapping-update-max/key
   imapping-size
   imapping-count
   )

  (include "trie.scm")
  (include "integer-map-impl.scm"))
