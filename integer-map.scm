(module (integer-map)
  (;; Constructors
   fxmapping fxmapping-unfold fxmapping-accumulate alist->fxmapping
   alist->fxmapping/combinator

   ;; Predicates
   fxmapping? fxmapping-contains? fxmapping-empty? fxmapping-disjoint?

   ;; Accessors
   fxmapping-min fxmapping-max fxmapping-ref fxmapping-ref/default

   ;; Updaters
   fxmapping-adjoin fxmapping-adjoin/combinator fxmapping-adjust
   fxmapping-set fxmapping-delete fxmapping-delete-all fxmapping-alter
   fxmapping-update fxmapping-delete-min fxmapping-delete-max
   fxmapping-update-min fxmapping-update-max fxmapping-pop-min
   fxmapping-pop-max

   ;; The whole fxmapping
   fxmapping-size fxmapping-count fxmapping-any? fxmapping-find
   fxmapping-every?

   ;; Traversal
   fxmapping-fold fxmapping-fold-right fxmapping-map fxmapping-map->list
   fxmapping-for-each
   fxmapping-relation-map

   ;; Filter
   fxmapping-filter fxmapping-remove fxmapping-partition

   ;; Copying and conversion
   fxmapping-keys fxmapping-values fxmapping->alist
   fxmapping->decreasing-alist fxmapping->generator
   fxmapping->decreasing-generator

   ;; Comparison
   fxmapping=? fxmapping<? fxmapping>? fxmapping<=? fxmapping>=?

   ;; Set theory operations
   fxmapping-union fxmapping-intersection fxmapping-difference fxmapping-xor
   fxmapping-union/combinator fxmapping-intersection/combinator

   ;; Submappings
   fxmapping-open-interval fxmapping-closed-interval
   fxmapping-open-closed-interval fxmapping-closed-open-interval
   fxsubmapping= fxsubmapping< fxsubmapping<= fxsubmapping>= fxsubmapping>
   fxmapping-split
   )

  (import scheme
          (except (chicken base) constantly assert)
          (chicken condition)
          (chicken platform)
          (chicken type)
          (only (srfi 1) fold every)
          (only (srfi 128) comparator? =?)
          (srfi 143)
          (srfi 158))

  (register-feature! 'integer-map)
  (register-feature! 'srfi-224)

  ;; R7RS shim
  (define exact inexact->exact)

  (define-syntax assert
    (syntax-rules ()
      ((assert loc expr)
       (unless expr
         (abort
          (make-composite-condition
           (make-property-condition 'exn
            'location loc
            'arguments 'expr)
           (make-property-condition 'assertion)))))))

  (include "matchers.scm")
  (include "trie.scm")
  (include "integer-map-impl.scm"))
