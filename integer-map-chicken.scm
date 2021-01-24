(module (integer-map)

  (import scheme
          (chicken base)
          (only (srfi 1) fold every)
          (srfi 143)
          (srfi 145)
          (matchable))

  ;; R7RS shim
  (define exact inexact->exact)

  (include "trie.scm")
  (include "integer-map-impl.scm"))
