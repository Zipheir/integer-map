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

  (cond-expand
    (chibi (import (chibi match)))
    (chicken (import (matchable)))
    (else (import (srfi 204))))

  (export
   imapping
   imapping-unfold imapping-unfold-maybe
   imapping? imapping-contains? imapping-empty? imapping-disjoint?
   imapping-min imapping-max
   imapping-lookup imapping-lookup/default imapping-adjoin
   imapping-adjoin/combine imapping-adjust imapping-adjust/key
   imapping-delete imapping-delete-all imapping-alter imapping-update
   imapping-update/key
   imapping-delete-min imapping-delete-max
   imapping-update-min imapping-update-max
   imapping-update-min/key imapping-update-max/key
   imapping-size
   imapping-count
   imapping-any? imapping-every?
   imapping-keys imapping-values
   imapping-fold-left imapping-fold-right
   imapping-fold-left/key imapping-fold-right/key
   imapping-map imapping-map/key
   imapping-map->list imapping-map/key->list
   imapping-for-each imapping-for-each/key
   imapping-filter imapping-filter/key imapping-remove imapping-remove/key
   imapping-partition imapping-partition/key
   imapping->alist
   imapping=? imapping<? imapping>? imapping<=? imapping>=?
   imapping-union imapping-intersection imapping-difference imapping-xor
   alist->imapping
   imapping-open-interval imapping-closed-interval
   imapping-open-closed-interval imapping-closed-open-interval
   isubmapping= isubmapping< isubmapping<= isubmapping>=
   isubmapping>
   )

  (begin
   (define-syntax λ
     (syntax-rules ()
       ((λ . rest) (lambda . rest)))))

  (include "trie.scm")
  (include "integer-map-impl.scm"))
