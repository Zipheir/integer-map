(module (integer-map)
  (
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
   )

  (import scheme
          (chicken base)
          (only (srfi 1) fold every)
          (only (srfi 128) comparator? =?)
          (srfi 143)
          (srfi 145)
          (srfi 189)
          (matchable))

  ;; R7RS shim
  (define exact inexact->exact)

  (include "trie.scm")
  (include "integer-map-impl.scm"))
