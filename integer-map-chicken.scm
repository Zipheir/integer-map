(module (integer-map)
  (
   imapping-delete-min imapping-delete-max
   imapping-update-min imapping-update-max
   )

  (import scheme
          (chicken base)
          (only (srfi 1) fold every)
          (only (srfi 128) comparator? =?)
          (srfi 143)
          (srfi 145)
          (matchable))

  ;; R7RS shim
  (define exact inexact->exact)

  (include "trie.scm")
  (include "integer-map-impl.scm"))
