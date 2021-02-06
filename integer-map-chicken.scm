(module (integer-map)
  (
   imapping
   imapping-unfold imapping-unfold-maybe
   imapping? imapping-contains? imapping-empty? imapping-disjoint?
   imapping-lookup imapping-lookup/default imapping-adjoin imapping-adjoin/proc
   imapping-delete imapping-delete-all imapping-alter imapping-update
   imapping-update/key imapping-adjust imapping-adjust/key
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
   ; imapping-open-interval imapping-closed-interval
   ; imapping-open-closed-interval imapping-closed-open-interval
   ; isubmapping= isubmapping< isubmapping<= isubmapping>=
   )

  (import scheme
          (except (chicken base) constantly)
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
