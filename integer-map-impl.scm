;;; Copyright (C) 2020 Wolfgang Corcoran-Mathe
;;;
;;; Permission is hereby granted, free of charge, to any person obtaining a
;;; copy of this software and associated documentation files (the
;;; "Software"), to deal in the Software without restriction, including
;;; without limitation the rights to use, copy, modify, merge, publish,
;;; distribute, sublicense, and/or sell copies of the Software, and to
;;; permit persons to whom the Software is furnished to do so, subject to
;;; the following conditions:
;;;
;;; The above copyright notice and this permission notice shall be included
;;; in all copies or substantial portions of the Software.
;;;
;;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
;;; OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;;; MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
;;; IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
;;; CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
;;; TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
;;; SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

;;;; Utility

(define (plist-fold loc proc nil plist)
  (let loop ((b nil) (ps plist))
    (pmatch ps
      (() b)
      ((,k ,v . ,ps*)
       (loop (proc k v b) ps*))
      (else
       (abort
        (make-arity-condition loc "invalid argument list" plist))))))

(define (first-arg _k x _y) x)
(define (second-arg _k _x y) y)

(define (constantly x)
  (lambda (_) x))

;;;; Conditions and exceptions

(define (make-type-condition loc msg . args)
  (make-composite-condition
   (make-property-condition 'exn
    'location loc
    'message msg
    'arguments args)
   (make-property-condition 'type)
   (make-property-condition 'assertion)))

;; Raised by fxmapping-ref, etc. when a key is not found in a map
;; and there is no other recourse.
(define (make-access-condition loc msg . args)
  (make-composite-condition
   (make-property-condition 'exn
    'location loc
    'message msg
    'arguments args)
   (make-property-condition 'access)))

;; Raised by variadic procedures when an incorrect number of arguments
;; is passed.
(define (make-arity-condition loc msg . args)
  (make-composite-condition
   (make-property-condition 'exn
    'location loc
    'message msg
    'arguments args)
   (make-property-condition 'arity)
   (make-property-condition 'assertion)))

(define-syntax assert-type
  (syntax-rules ()
    ((assert-type loc expr . args)
     (unless expr
       (abort
        (make-type-condition loc
                             "assertion violation: type check failed"
                             'expr
                             . args))))))

(define (assert-arity loc bool . args)
  (unless bool
    (abort
     (apply make-arity-condition loc "invalid argument count" args))))

(define (assert-fxmap-non-empty loc fxmap)
  (when (fxmapping-empty? fxmap)
    (abort
     (make-access-condition loc "empty fxmapping"))))

;;;; Type

(define-record-type <fxmapping>
  (raw-fxmapping trie)
  fxmapping?
  (trie fxmapping-trie))

(define-type fxmap-t (struct <fxmapping>))

;;;; Constructors

(: fxmapping (#!rest -> fxmap-t))
(define (fxmapping . args)
  (raw-fxmapping
    (plist-fold 'fxmapping
                (lambda (k v trie) (trie-adjoin trie k v))
                the-empty-trie
                args)))

(define (pair-or-null? x)
  (or (pair? x) (null? x)))

(: alist->fxmapping/combinator
   (procedure (list-of (pair fixnum *)) -> fxmap-t))
(define (alist->fxmapping/combinator comb as)
  (assert-type 'alist->fxmapping/combinator (procedure? comb))
  (assert-type 'alist->fxmapping/combinator (pair-or-null? as))
  (raw-fxmapping
    (fold (lambda (p trie)
            (assert-type 'alist->fxmapping/combinator (pair? p) p)
            (trie-insert/combine trie (car p) (cdr p) comb))
          the-empty-trie
          as)))

(: alist->fxmapping ((list-of (pair fixnum *)) -> fxmap-t))
(define (alist->fxmapping as)
  (alist->fxmapping/combinator second-arg as))

(: fxmapping-unfold
   (procedure procedure procedure #!rest -> fxmap-t))
(define fxmapping-unfold
  (case-lambda
    ((stop? mapper successor seed)                ; fast path
     (assert-type 'fxmapping-unfold (procedure? stop?))
     (assert-type 'fxmapping-unfold (procedure? mapper))
     (assert-type 'fxmapping-unfold (procedure? successor))
     (let lp ((trie the-empty-trie) (seed seed))
       (if (stop? seed)
           (raw-fxmapping trie)
           (let-values (((k v) (mapper seed)))
             (assert-type 'fxmapping-unfold (fixnum? k))
             (lp (trie-adjoin trie k v) (successor seed))))))
    ((stop? mapper successor . seeds)             ; variadic path
     (assert-type 'fxmapping-unfold (procedure? stop?))
     (assert-type 'fxmapping-unfold (procedure? mapper))
     (assert-type 'fxmapping-unfold (procedure? successor))
     (assert-type 'fxmapping-unfold (pair? seeds))
     (let lp ((trie the-empty-trie) (seeds seeds))
       (if (apply stop? seeds)
           (raw-fxmapping trie)
           (let-values (((k v) (apply mapper seeds))
                        (seeds* (apply successor seeds)))
             (assert-type 'fxmapping-unfold (fixnum? k))
             (lp (trie-adjoin trie k v) seeds*)))))))

(: fxmapping-accumulate (procedure #!rest -> fxmap-t))
(define fxmapping-accumulate
  (case-lambda
    ((proc seed)                                ; fast path
     (assert-type 'fxmapping-accumulate (procedure? proc))
     (call-with-current-continuation
      (lambda (k)
        (let lp ((trie the-empty-trie) (seed seed))
          (let-values (((k v seed*)
                        (proc (lambda xs (apply k (raw-fxmapping trie) xs))
                              seed)))
            (lp (trie-adjoin trie k v) seed*))))))
    ((proc . seeds)                             ; variadic path
     (assert-type 'fxmapping-accumulate (procedure? proc))
     (assert-type 'fxmapping-accumulate (pair? seeds))
     (call-with-current-continuation
      (lambda (k)
        (let lp ((trie the-empty-trie) (seeds seeds))
          (let-values (((k v . seeds*)
                        (apply proc
                               (lambda xs (apply k (raw-fxmapping trie) xs))
                               seeds)))
            (lp (trie-adjoin trie k v) seeds*))))))))

;;;; Predicates

(: fxmapping-contains? (fxmap-t fixnum --> boolean))
(define (fxmapping-contains? fxmap n)
  (assert-type 'fxmapping-contains? (fxmapping? fxmap))
  (assert-type 'fxmapping-contains? (fixnum? n))
  (trie-contains? (fxmapping-trie fxmap) n))

(: fxmapping-empty? (fxmap-t --> boolean))
(define (fxmapping-empty? fxmap)
  (assert-type 'fxmapping-empty? (fxmapping? fxmap))
  (eqv? (fxmapping-trie fxmap) the-empty-trie))

(: fxmapping-disjoint? (fxmap-t fxmap-t --> boolean))
(define (fxmapping-disjoint? fxmap1 fxmap2)
  (assert-type 'fxmapping-disjoint? (fxmapping? fxmap1))
  (assert-type 'fxmapping-disjoint? (fxmapping? fxmap2))
  (trie-disjoint? (fxmapping-trie fxmap1) (fxmapping-trie fxmap2)))

;;;; Accessors

(: fxmapping-ref
   (or (fxmap-t fixnum -> *)
       (fxmap-t fixnum procedure -> *)
       (fxmap-t fixnum procedure procedure -> *)))
(define fxmapping-ref
  (case-lambda
    ((fxmap key)
     (fxmapping-ref fxmap
                    key
                    (lambda ()
                      (abort
                       (make-access-condition 'fxmapping-ref
                                              "no such key in fxmapping"
                                              key
                                              fxmap)))
                    values))
    ((fxmap key failure)
     (fxmapping-ref fxmap key failure values))
    ((fxmap key failure success)
     (assert-type 'fxmapping-ref (fxmapping? fxmap))
     (assert-type 'fxmapping-ref (fixnum? key))
     (assert-type 'fxmapping-ref (procedure? failure))
     (assert-type 'fxmapping-ref (procedure? success))
     (trie-assoc (fxmapping-trie fxmap) key failure success))))

(: fxmapping-ref/default (fxmap-t fixnum * --> *))
(define (fxmapping-ref/default fxmap key default)
  (assert-type 'fxmapping-ref/default (fxmapping? fxmap))
  (assert-type 'fxmapping-ref/default (fixnum? key))
  (trie-assoc/default (fxmapping-trie fxmap) key default))

(: fxmapping-min (fxmap-t --> *))
(define (fxmapping-min fxmap)
  (assert-type 'fxmapping-min (fxmapping? fxmap))
  (assert-fxmap-non-empty 'fxmapping-min fxmap)
  (trie-min (fxmapping-trie fxmap)))

(: fxmapping-max (fxmap-t --> *))
(define (fxmapping-max fxmap)
  (assert-type 'fxmapping-max (fxmapping? fxmap))
  (assert-fxmap-non-empty 'fxmapping-max fxmap)
  (trie-max (fxmapping-trie fxmap)))

;;;; Updaters

(: fxmapping-adjoin/combinator (fxmap-t procedure #!rest -> fxmap-t))
(define fxmapping-adjoin/combinator
  (case-lambda
    ((fxmap combine key value)      ; one-assoc fast path
     (assert-type 'fxmapping-adjoin/combinator (fxmapping? fxmap))
     (assert-type 'fxmapping-adjoin/combinator (procedure? combine))
     (assert-type 'fxmapping-adjoin/combinator (fixnum? key))
     (raw-fxmapping
      (trie-insert/combine (fxmapping-trie fxmap) key value combine)))
    ((fxmap combine . ps)
     (assert-type 'fxmapping-adjoin/combinator (fxmapping? fxmap))
     (raw-fxmapping
      (plist-fold 'fxmapping-adjoin/combinator
                  (lambda (k v t)
                    (assert-type 'fxmapping-adjoin/combinator
                                 (fixnum? k))
                    (trie-insert/combine t k v combine))
                  (fxmapping-trie fxmap)
                  ps)))))

;; Preserve existing associations for keys.
(: fxmapping-adjoin (fxmap-t #!rest --> fxmap-t))
(define fxmapping-adjoin
  (case-lambda
    ((fxmap key value)              ; one-assoc fast path
     (assert-type 'fxmapping-adjoin (fxmapping? fxmap))
     (assert-type 'fxmapping-adjoin (fixnum? key))
     (raw-fxmapping
      (trie-adjoin (fxmapping-trie fxmap) key value)))
    ((fxmap . ps)
     (assert-type 'fxmapping-adjoin (fxmapping? fxmap))
     (raw-fxmapping
      (plist-fold 'fxmapping-adjoin
                  (lambda (k v t)
                    (assert-type 'fxmapping-adjoin (fixnum? k))
                    (trie-adjoin t k v))
                  (fxmapping-trie fxmap)
                  ps)))))

;; Replace existing associations for keys.
(: fxmapping-set (fxmap-t #!rest --> fxmap-t))
(define fxmapping-set
  (case-lambda
    ((fxmap key value)      ; one-assoc fast path
     (assert-type 'fxmapping-set (fxmapping? fxmap))
     (assert-type 'fxmapping-set (fixnum? key))
     (raw-fxmapping
      (trie-insert (fxmapping-trie fxmap) key value)))
    ((fxmap . ps)
     (assert-type 'fxmapping-set (fxmapping? fxmap))
     (raw-fxmapping
      (plist-fold 'fxmapping-set
                  (lambda (k v t)
                    (assert-type 'fxmapping-set (fixnum? k))
                    (trie-insert t k v))
                  (fxmapping-trie fxmap)
                  ps)))))

(: fxmapping-adjust (fxmap-t fixnum procedure -> fxmap-t))
(define (fxmapping-adjust fxmap key proc)
  (assert-type 'fxmapping-adjust (fxmapping? fxmap))
  (assert-type 'fxmapping-adjust (fixnum? key))
  (assert-type 'fxmapping-adjust (procedure? proc))
  (raw-fxmapping (trie-adjust (fxmapping-trie fxmap) key proc)))

(: fxmapping-delete (fxmap-t #!rest fixnum --> fxmap-t))
(define fxmapping-delete
  (case-lambda
    ((fxmap key)      ; fast path
     (assert-type 'fxmapping-delete (fxmapping? fxmap))
     (assert-type 'fxmapping-delete (fixnum? key))
     (raw-fxmapping (trie-delete (fxmapping-trie fxmap) key)))
    ((fxmap . keys)
     (fxmapping-delete-all fxmap keys))))

(: fxmapping-delete-all (fxmap-t (list-of fixnum) --> fxmap-t))
(define (fxmapping-delete-all fxmap keys)
  (assert-type 'fxmapping-delete-all (fxmapping? fxmap))
  (assert-type 'fxmapping-delete-all (pair-or-null? keys))
  (let ((key-map (fxmapping-unfold null?
                                   (lambda (ks) (values (car ks) #t))
                                   cdr
                                   keys)))
    (fxmapping-remove (lambda (k _) (fxmapping-contains? key-map k))
                      fxmap)))

(: fxmapping-update
   (or (fxmap-t fixnum procedure -> *)
       (fxmap-t fixnum procedure procedure -> *)))
(define fxmapping-update
  (case-lambda
    ((fxmap key success)
     (fxmapping-update fxmap
                       key
                       success
                       (lambda ()
                         (abort
                          (make-access-condition 'fxmapping-update
                                                 "key not found"
                                                 key)))))
    ((fxmap key success failure)
     (assert-type 'fxmapping-update (fxmapping? fxmap))
     (assert-type 'fxmapping-update (fixnum? key))
     (assert-type 'fxmapping-update (procedure? success))
     (assert-type 'fxmapping-update (procedure? failure))
     (trie-update (fxmapping-trie fxmap) key success failure raw-fxmapping))))

(: fxmapping-alter (fxmap-t fixnum procedure procedure -> *))
(define (fxmapping-alter fxmap key failure success)
  (assert-type 'fxmapping-alter (fxmapping? fxmap))
  (assert-type 'fxmapping-alter (fixnum? key))
  (assert-type 'fxmapping-alter (procedure? failure))
  (assert-type 'fxmapping-alter (procedure? success))
  (trie-alter (fxmapping-trie fxmap) key failure success raw-fxmapping))

(: fxmapping-delete-min (fxmap-t --> fxmap-t))
(define (fxmapping-delete-min fxmap)
  (assert-type 'fxmapping-delete-min (fxmapping? fxmap))
  (assert-fxmap-non-empty 'fxmapping-delete-min fxmap)
  (fxmapping-update-min fxmap
                        (lambda (_k _v _rep delete)
                          (delete))))

(: fxmapping-update-min (fxmap-t procedure --> fxmap-t))
(define (fxmapping-update-min fxmap success)
  (assert-type 'fxmapping-update-min (fxmapping? fxmap))
  (assert-type 'fxmapping-update-min (procedure? success))
  (assert-fxmap-non-empty 'fxmapping-update-min fxmap)
  (trie-update-min (fxmapping-trie fxmap) success raw-fxmapping))

(: fxmapping-pop-min (fxmap-t --> fxmap-t))
(define (fxmapping-pop-min fxmap)
  (assert-type 'fxmapping-pop-min (fxmapping? fxmap))
  (assert-fxmap-non-empty 'fxmapping-pop-min fxmap)
  (let-values (((k v trie) (trie-pop-min (fxmapping-trie fxmap))))
    (values k v (raw-fxmapping trie))))

(: fxmapping-delete-max (fxmap-t --> fxmap-t))
(define (fxmapping-delete-max fxmap)
  (assert-type 'fxmapping-delete-max (fxmapping? fxmap))
  (assert-fxmap-non-empty 'fxmapping-delete-max fxmap)
  (fxmapping-update-max fxmap
                        (lambda (_k _v _rep delete)
                          (delete))))

(: fxmapping-update-max (fxmap-t procedure --> fxmap-t))
(define (fxmapping-update-max fxmap success)
  (assert-type 'fxmapping-update-max (fxmapping? fxmap))
  (assert-type 'fxmapping-update-max (procedure? success))
  (assert-fxmap-non-empty 'fxmapping-update-max fxmap)
  (trie-update-max (fxmapping-trie fxmap) success raw-fxmapping))

(: fxmapping-pop-max (fxmap-t --> fxmap-t))
(define (fxmapping-pop-max fxmap)
  (assert-type 'fxmapping-pop-max (fxmapping? fxmap))
  (assert-fxmap-non-empty 'fxmapping-pop-max fxmap)
  (let-values (((k v trie) (trie-pop-max (fxmapping-trie fxmap))))
    (values k v (raw-fxmapping trie))))

;;;; The whole fxmapping

(: fxmapping-size (fxmap-t --> integer))
(define (fxmapping-size fxmap)
  (assert-type 'fxmapping-size (fxmapping? fxmap))
  (trie-size (fxmapping-trie fxmap)))

(: fxmapping-find (procedure fxmap-t procedure procedure -> *))
(define fxmapping-find
  (case-lambda
    ((pred fxmap failure)
     (fxmapping-find pred fxmap failure values))
    ((pred fxmap failure success)
     (assert-type 'fxmapping-find (procedure? pred))
     (assert-type 'fxmapping-find (fxmapping? fxmap))
     (assert-type 'fxmapping-find (procedure? failure))
     (assert-type 'fxmapping-find (procedure? success))
     (trie-find pred (fxmapping-trie fxmap) failure success))))

(: fxmapping-count (procedure fxmap-t -> integer))
(define (fxmapping-count pred fxmap)
  (assert-type 'fxmapping-count (procedure? pred))
  (assert-type 'fxmapping-count (fxmapping? fxmap))
  (fxmapping-fold (lambda (k v acc)
                    (if (pred k v) (+ 1 acc) acc))
                  0
                  fxmap))

(: fxmapping-any? (procedure fxmap-t -> boolean))
(define (fxmapping-any? pred fxmap)
  (assert-type 'fxmapping-any? (procedure? pred))
  (assert-type 'fxmapping-any? (fxmapping? fxmap))
  (call-with-current-continuation
   (lambda (return)
     (fxmapping-fold (lambda (k v _)
                       (and (pred k v) (return #t)))
                     #f
                     fxmap))))

(: fxmapping-every? (procedure fxmap-t -> boolean))
(define (fxmapping-every? pred fxmap)
  (assert-type 'fxmapping-every? (procedure? pred))
  (assert-type 'fxmapping-every? (fxmapping? fxmap))
  (call-with-current-continuation
   (lambda (return)
     (fxmapping-fold (lambda (k v _)
                       (or (pred k v) (return #f)))
                     #t
                     fxmap))))

;;;; Mapping and folding

;; Map proc over the assocs. of fxmap, inserting result values under
;; the same key.
;; This is *not* the same as SRFI 146's mapping-map.
(: fxmapping-map (procedure fxmap-t -> fxmap-t))
(define (fxmapping-map proc fxmap)
  (assert-type 'fxmapping-map (procedure? proc))
  (assert-type 'fxmapping-map (fxmapping? fxmap))
  (raw-fxmapping (trie-map proc (fxmapping-trie fxmap))))

(: unspecified (-> undefined))
(define unspecified void)

(: fxmapping-for-each (procedure fxmap-t -> undefined))
(define (fxmapping-for-each proc fxmap)
  (assert-type 'fxmapping-for-each (procedure? proc))
  (assert-type 'fxmapping-for-each (fxmapping? fxmap))
  (fxmapping-fold (lambda (k v _)
                    (proc k v)
                    (unspecified))
                  (unspecified)
                  fxmap))

(: fxmapping-fold (procedure * fxmap-t -> *))
(define (fxmapping-fold proc nil fxmap)
  (assert-type 'fxmapping-fold (procedure? proc))
  (assert-type 'fxmapping-fold (fxmapping? fxmap))
  (let ((trie (fxmapping-trie fxmap)))
    (tmatch trie
      ((branch ? ,m ,l ,r) (guard (negative? m))
       (trie-fold-left proc (trie-fold-left proc nil r) l))
      ((branch ? ? ,l ,r)
       (trie-fold-left proc (trie-fold-left proc nil l) r))
      (else (trie-fold-left proc nil trie)))))

(: fxmapping-fold-right (procedure * fxmap-t -> *))
(define (fxmapping-fold-right proc nil fxmap)
  (assert-type 'fxmapping-fold-right (procedure? proc))
  (assert-type 'fxmapping-fold-right (fxmapping? fxmap))
  (let ((trie (fxmapping-trie fxmap)))
    (tmatch trie
      ((branch ? ,m ,l ,r) (guard (negative? m))
       (trie-fold-right proc (trie-fold-right proc nil l) r))
      ((branch ? ? ,l ,r)
       (trie-fold-right proc (trie-fold-right proc nil r) l))
      (else (trie-fold-right proc nil trie)))))

(: fxmapping-map->list (procedure fxmap-t -> list))
(define (fxmapping-map->list proc fxmap)
  (assert-type 'fxmapping-map->list (procedure? proc))
  (assert-type 'fxmapping-map->list (fxmapping? fxmap))
  (fxmapping-fold-right (lambda (k v us)
                          (cons (proc k v) us))
                        '()
                        fxmap))

(: fxmapping-filter (procedure fxmap-t -> fxmap-t))
(define (fxmapping-filter pred fxmap)
  (assert-type 'fxmapping-filter (procedure? pred))
  (assert-type 'fxmapping-filter (fxmapping? fxmap))
  (raw-fxmapping (trie-filter pred (fxmapping-trie fxmap))))

(: fxmapping-remove (procedure fxmap-t -> fxmap-t))
(define (fxmapping-remove pred fxmap)
  (fxmapping-filter (lambda (k v) (not (pred k v))) fxmap))

(: fxmapping-partition (procedure fxmap-t -> fxmap-t fxmap-t))
(define (fxmapping-partition pred fxmap)
  (assert-type 'fxmapping-partition (procedure? pred))
  (assert-type 'fxmapping-partition (fxmapping? fxmap))
  (let-values (((tin tout)
                (trie-partition pred (fxmapping-trie fxmap))))
    (values (raw-fxmapping tin) (raw-fxmapping tout))))

;;;; Conversion

(: fxmapping->alist (fxmap-t --> (list-of (pair fixnum *))))
(define (fxmapping->alist fxmap)
  (fxmapping-fold-right (lambda (k v as) (cons (cons k v) as))
                        '()
                        fxmap))

(: fxmapping->decreasing-alist (fxmap-t --> (list-of (pair fixnum *))))
(define (fxmapping->decreasing-alist fxmap)
  (fxmapping-fold (lambda (k v as) (cons (cons k v) as))
                  '()
                  fxmap))

(: fxmapping-keys (fxmap-t --> (list-of fixnum)))
(define (fxmapping-keys fxmap)
  (fxmapping-fold-right (lambda (k _ ks) (cons k ks)) '() fxmap))

(: fxmapping-values (fxmap-t --> list))
(define (fxmapping-values fxmap)
  (fxmapping-fold-right (lambda (_ v vs) (cons v vs)) '() fxmap))

(: fxmapping->generator (fxmap-t -> procedure))
(define (fxmapping->generator fxmap)
  (assert-type 'fxmapping->generator (fxmapping? fxmap))
  (make-coroutine-generator
   (lambda (yield)
     (fxmapping-fold (lambda (k v _) (yield (cons k v)))
                     #f
                     fxmap))))

(: fxmapping->decreasing-generator (fxmap-t -> procedure))
(define (fxmapping->decreasing-generator fxmap)
  (assert-type 'fxmapping->decreasing-generator (fxmapping? fxmap))
  (make-coroutine-generator
   (lambda (yield)
     (fxmapping-fold-right (lambda (k v _) (yield (cons k v)))
                           #f
                           fxmap))))

;;;; Comparison

;;; Comparators have type *, because types can't be exported. :-(

(: fxmapping=? (* fxmap-t fxmap-t #!rest fxmap-t -> boolean))
(define (fxmapping=? comp fxmap1 fxmap2 . imaps)
  (assert-type 'fxmapping=? (comparator? comp))
  (assert-type 'fxmapping=? (fxmapping? fxmap1))
  (let ((fxmap-eq1 (lambda (fxmap)
                     (assert-type 'fxmapping=? (fxmapping? fxmap))
                     (or (eqv? fxmap1 fxmap)
                         (trie=? comp
                                 (fxmapping-trie fxmap1)
                                 (fxmapping-trie fxmap))))))
    (and (fxmap-eq1 fxmap2)
         (or (null? imaps)
             (every fxmap-eq1 imaps)))))

(: fxmapping<? (* fxmap-t fxmap-t #!rest fxmap-t --> boolean))
(define (fxmapping<? comp fxmap1 fxmap2 . imaps)
  (assert-type 'fxmapping<? (comparator? comp))
  (assert-type 'fxmapping<? (fxmapping? fxmap1))
  (assert-type 'fxmapping<? (fxmapping? fxmap2))
  (let lp ((t1 (fxmapping-trie fxmap1))
           (t2 (fxmapping-trie fxmap2))
           (imaps imaps))
    (and (trie-proper-subset? comp t1 t2)
         (pmatch imaps
           (() #t)
           ((,m . ,imaps*) (lp t2 (fxmapping-trie m) imaps*))))))

(: fxmapping>? (* fxmap-t fxmap-t #!rest fxmap-t --> boolean))
(define (fxmapping>? comp fxmap1 fxmap2 . imaps)
  (assert-type 'fxmapping>? (comparator? comp))
  (assert-type 'fxmapping>? (fxmapping? fxmap1))
  (assert-type 'fxmapping>? (fxmapping? fxmap2))
  (let lp ((t1 (fxmapping-trie fxmap1))
           (t2 (fxmapping-trie fxmap2))
           (imaps imaps))
    (and (trie-proper-subset? comp t2 t1)
         (pmatch imaps
           (() #t)
           ((,m . ,imaps*) (lp t2 (fxmapping-trie m) imaps*))))))

(: fxmapping<=? (* fxmap-t fxmap-t #!rest fxmap-t --> boolean))
(define (fxmapping<=? comp fxmap1 fxmap2 . imaps)
  (assert-type 'fxmapping<=? (comparator? comp))
  (assert-type 'fxmapping<=? (fxmapping? fxmap1))
  (assert-type 'fxmapping<=? (fxmapping? fxmap2))
  (let lp ((t1 (fxmapping-trie fxmap1))
           (t2 (fxmapping-trie fxmap2))
           (imaps imaps))
    (and (memv (trie-subset-compare comp t1 t2) '(less equal))
         (pmatch imaps
           (() #t)
           ((,m . ,imaps*) (lp t2 (fxmapping-trie m) imaps*))))))

(: fxmapping>=? (* fxmap-t fxmap-t #!rest fxmap-t --> boolean))
(define (fxmapping>=? comp fxmap1 fxmap2 . imaps)
  (assert-type 'fxmapping>=? (comparator? comp))
  (assert-type 'fxmapping>=? (fxmapping? fxmap1))
  (assert-type 'fxmapping>=? (fxmapping? fxmap2))
  (let lp ((t1 (fxmapping-trie fxmap1))
           (t2 (fxmapping-trie fxmap2))
           (imaps imaps))
    (and (memv (trie-subset-compare comp t2 t1) '(less equal))
         (pmatch imaps
           (() #t)
           ((,m . ,imaps*) (lp t2 (fxmapping-trie m) imaps*))))))

;;;; Set theory operations

(: fxmapping-union (fxmap-t fxmap-t #!rest fxmap-t --> fxmap-t))
(define (fxmapping-union . args)
  (apply fxmapping-union/combinator first-arg args))

(: fxmapping-intersection (fxmap-t fxmap-t #!rest fxmap-t --> fxmap-t))
(define (fxmapping-intersection . args)
  (apply fxmapping-intersection/combinator first-arg args))

(: fxmapping-difference (fxmap-t fxmap-t #!rest fxmap-t --> fxmap-t))
(define fxmapping-difference
  (case-lambda
    ((fxmap1 fxmap2)
     (assert-type 'fxmapping-difference (fxmapping? fxmap1))
     (assert-type 'fxmapping-difference (fxmapping? fxmap2))
     (raw-fxmapping
      (trie-difference (fxmapping-trie fxmap1)
                       (fxmapping-trie fxmap2))))
    ((fxmap . rest)
     (assert-type 'fxmapping-difference (fxmapping? fxmap))
     (assert-arity 'fxmapping-difference (pair? rest))
     (raw-fxmapping
      (trie-difference (fxmapping-trie fxmap)
                       (fxmapping-trie
                        (apply fxmapping-union rest)))))))

(: fxmapping-xor (fxmap-t fxmap-t --> fxmap-t))
(define (fxmapping-xor fxmap1 fxmap2)
  (assert-type 'fxmapping-xor (fxmapping? fxmap1))
  (assert-type 'fxmapping-xor (fxmapping? fxmap2))
  (raw-fxmapping
   (trie-xor (fxmapping-trie fxmap1) (fxmapping-trie fxmap2))))

(: fxmapping-union/combinator
   (procedure fxmap-t fxmap-t #!rest fxmap-t -> fxmap-t))
(define (fxmapping-union/combinator proc fxmap . rest)
  (assert-type 'fxmapping-union/combinator (procedure? proc))
  (assert-type 'fxmapping-union/combinator (fxmapping? fxmap))
  (assert-arity 'fxmapping-union/combinator (pair? rest))
  (raw-fxmapping
   (fold (lambda (im t)
           (assert-type 'fxmapping-union/combinator (fxmapping? im))
           (trie-merge proc t (fxmapping-trie im)))
         (fxmapping-trie fxmap)
         rest)))

(: fxmapping-intersection/combinator
   (procedure fxmap-t fxmap-t #!rest fxmap-t -> fxmap-t))
(define (fxmapping-intersection/combinator proc fxmap . rest)
  (assert-type 'fxmapping-intersection/combinator (procedure? proc))
  (assert-type 'fxmapping-intersection/combinator (fxmapping? fxmap))
  (assert-arity 'fxmapping-intersection/combinator (pair? rest))
  (raw-fxmapping
   (fold (lambda (im t)
           (assert-type 'fxmapping-intersection/combinator (fxmapping? im))
           (trie-intersection proc t (fxmapping-trie im)))
         (fxmapping-trie fxmap)
         rest)))

;;;; Subsets

(: fxsubmapping= (fxmap-t fixnum --> fxmap-t))
(define (fxsubmapping= fxmap key)
  (fxmapping-ref fxmap
                 key
                 fxmapping
                 (lambda (v) (fxmapping key v))))

(: fxmapping-open-interval (fxmap-t fixnum fixnum --> fxmap-t))
(define (fxmapping-open-interval fxmap low high)
  (assert-type 'fxmapping-open-interval (fxmapping? fxmap))
  (assert-type 'fxmapping-open-interval (fixnum? low))
  (assert-type 'fxmapping-open-interval (fixnum? high))
  (assert 'fxmapping-open-interval (fx>=? high low))
  (raw-fxmapping
   (subtrie-interval (fxmapping-trie fxmap) low high #f #f)))

(: fxmapping-closed-interval (fxmap-t fixnum fixnum --> fxmap-t))
(define (fxmapping-closed-interval fxmap low high)
  (assert-type 'fxmapping-closed-interval (fxmapping? fxmap))
  (assert-type 'fxmapping-closed-interval (fixnum? low))
  (assert-type 'fxmapping-closed-interval (fixnum? high))
  (assert 'fxmapping-closed-interval (fx>=? high low))
  (raw-fxmapping
   (subtrie-interval (fxmapping-trie fxmap) low high #t #t)))

(: fxmapping-open-closed-interval (fxmap-t fixnum fixnum --> fxmap-t))
(define (fxmapping-open-closed-interval fxmap low high)
  (assert-type 'fxmapping-open-closed-interval (fxmapping? fxmap))
  (assert-type 'fxmapping-open-closed-interval (fixnum? low))
  (assert-type 'fxmapping-open-closed-interval (fixnum? high))
  (assert 'fxmapping-open-closed-interval (fx>=? high low))
  (raw-fxmapping
   (subtrie-interval (fxmapping-trie fxmap) low high #f #t)))

(: fxmapping-closed-open-interval (fxmap-t fixnum fixnum --> fxmap-t))
(define (fxmapping-closed-open-interval fxmap low high)
  (assert-type 'fxmapping-closed-open-interval (fxmapping? fxmap))
  (assert-type 'fxmapping-closed-open-interval (fixnum? low))
  (assert-type 'fxmapping-closed-open-interval (fixnum? high))
  (assert 'fxmapping-closed-open-interval (fx>=? high low))
  (raw-fxmapping
   (subtrie-interval (fxmapping-trie fxmap) low high #t #f)))

(: fxsubmapping< (fxmap-t fixnum --> fxmap-t))
(define (fxsubmapping< fxmap key)
  (assert-type 'fxsubmapping< (fxmapping? fxmap))
  (assert-type 'fxsubmapping< (fixnum? key))
  (raw-fxmapping (subtrie< (fxmapping-trie fxmap) key #f)))

(: fxsubmapping<= (fxmap-t fixnum --> fxmap-t))
(define (fxsubmapping<= fxmap key)
  (assert-type 'fxsubmapping<= (fxmapping? fxmap))
  (assert-type 'fxsubmapping<= (fixnum? key))
  (raw-fxmapping (subtrie< (fxmapping-trie fxmap) key #t)))

(: fxsubmapping> (fxmap-t fixnum --> fxmap-t))
(define (fxsubmapping> fxmap key)
  (assert-type 'fxsubmapping> (fxmapping? fxmap))
  (assert-type 'fxsubmapping> (fixnum? key))
  (raw-fxmapping (subtrie> (fxmapping-trie fxmap) key #f)))

(: fxsubmapping>= (fxmap-t fixnum --> fxmap-t))
(define (fxsubmapping>= fxmap key)
  (assert-type 'fxsubmapping>= (fxmapping? fxmap))
  (assert-type 'fxsubmapping>= (fixnum? key))
  (raw-fxmapping (subtrie> (fxmapping-trie fxmap) key #t)))

(: fxmapping-split (fxmap-t fixnum --> fxmap-t fxmap-t))
(define (fxmapping-split fxmap k)
  (assert-type 'fxmapping-split (fxmapping? fxmap))
  (assert-type 'fxmapping-split (integer? k))
  (let-values (((trie-low trie-high)
                (trie-split (fxmapping-trie fxmap) k)))
    (values (raw-fxmapping trie-low) (raw-fxmapping trie-high))))

;;;; fxmappings as relations

(: fxmapping-relation-map (procedure fxmap-t -> fxmap-t))
(define (fxmapping-relation-map proc fxmap)
  (assert-type 'fxmapping-relation-map (procedure? proc))
  (assert-type 'fxmapping-relation-map (fxmapping? fxmap))
  (raw-fxmapping (trie-relation-map proc (fxmapping-trie fxmap))))
