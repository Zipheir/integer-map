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

(: plist-fold ((* * * -> *) * (list-of *) -> *))
(define (plist-fold proc nil ps)
  (let loop ((b nil) (ps ps))
    (pmatch ps
      (() b)
      ((,k ,v . ,ps*)
       (loop (proc k v b) ps*))
      (else (error "plist-fold: invalid plist")))))

(: first-arg (* * * --> *))
(define (first-arg _k x _y) x)

(: second-arg (* * * --> *))
(define (second-arg _k _x y) y)

(: constantly (* --> (* -> *)))
(define (constantly x)
  (lambda (_) x))

;;;; Type

(define-record-type <fxmapping>
  (raw-fxmapping trie)
  fxmapping?
  (trie fxmapping-trie : trie-t))

(define-type fxmapping-t (struct <fxmapping))

;;;; Constructors

(: fxmapping (#!rest * --> (struct <fxmapping>)))
(define (fxmapping . args)
  (raw-fxmapping
    (plist-fold (lambda (k v trie) (trie-adjoin trie k v))
                the-empty-trie
                args)))

(: pair-or-null? (* --> boolean))
(define (pair-or-null? x)
  (or (pair? x) (null? x)))

(: alist->fxmapping/combinator
   ((fixnum * * -> *) (list-of (pair fixnum *)) -> (struct <fxmapping>)))
(define (alist->fxmapping/combinator comb as)
  (assume (procedure? comb))
  (assume (pair-or-null? as))
  (raw-fxmapping
    (fold (lambda (p trie)
            (assume (pair? p) "alist->fxmapping/combinator: not a pair")
            (trie-insert/combine trie (car p) (cdr p) comb))
          the-empty-trie
          as)))

(: alist->fxmapping ((list-of (pair fixnum *)) -> (struct <fxmapping>)))
(define (alist->fxmapping as)
  (alist->fxmapping/combinator second-arg as))

(: fxmapping-unfold
   ((#!rest -> boolean)
    (#!rest -> fixnum *)
    (#!rest -> *)
    #!rest
    -> fxmapping-t))
(define fxmapping-unfold
  (case-lambda
    ((stop? mapper successor seed)                ; fast path
     (assume (procedure? stop?))
     (assume (procedure? mapper))
     (assume (procedure? successor))
     (let lp ((trie the-empty-trie) (seed seed))
       (if (stop? seed)
           (raw-fxmapping trie)
           (let-values (((k v) (mapper seed)))
             (assume (valid-integer? k))
             (lp (trie-adjoin trie k v) (successor seed))))))
    ((stop? mapper successor . seeds)             ; variadic path
     (assume (procedure? stop?))
     (assume (procedure? mapper))
     (assume (procedure? successor))
     (assume (pair? seeds))
     (let lp ((trie the-empty-trie) (seeds seeds))
       (if (apply stop? seeds)
           (raw-fxmapping trie)
           (let-values (((k v) (apply mapper seeds))
                        (seeds* (apply successor seeds)))
             (assume (valid-integer? k))
             (lp (trie-adjoin trie k v) seeds*)))))))

(: fxmapping-accumulate ((procedure #!rest -> *) #!rest -> fxmapping-t))
(define fxmapping-accumulate
  (case-lambda
    ((proc seed)                                ; fast path
     (assume (procedure? proc))
     (call-with-current-continuation
      (lambda (k)
        (let lp ((trie the-empty-trie) (seed seed))
          (let-values (((k v seed*)
                        (proc (lambda xs (apply k (raw-fxmapping trie) xs))
                              seed)))
            (lp (trie-adjoin trie k v) seed*))))))
    ((proc . seeds)                             ; variadic path
     (assume (procedure? proc))
     (assume (pair? seeds))
     (call-with-current-continuation
      (lambda (k)
        (let lp ((trie the-empty-trie) (seeds seeds))
          (let-values (((k v . seeds*)
                        (apply proc
                               (lambda xs (apply k (raw-fxmapping trie) xs))
                               seeds)))
            (lp (trie-adjoin trie k v) seeds*))))))))

;;;; Predicates

(: fxmapping-contains? ((struct <fxmapping>) fixnum -> boolean))
(define (fxmapping-contains? fxmap n)
  (assume (fxmapping? fxmap))
  (assume (valid-integer? n))
  (trie-contains? (fxmapping-trie fxmap) n))

(: fxmapping-empty? ((struct <fxmapping>) -> boolean))
(define (fxmapping-empty? fxmap)
  (assume (fxmapping? fxmap))
  (eqv? (fxmapping-trie fxmap) the-empty-trie))

(: fxmapping-disjoint? ((struct <fxmapping>) (struct <fxmapping>) -> boolean))
(define (fxmapping-disjoint? fxmap1 fxmap2)
  (assume (fxmapping? fxmap1))
  (assume (fxmapping? fxmap2))
  (trie-disjoint? (fxmapping-trie fxmap1) (fxmapping-trie fxmap2)))

;;;; Accessors

(: fxmapping-ref ((struct <fxmapping>) fixnum #!rest -> *))
(define fxmapping-ref
  (case-lambda
    ((fxmap key)
     (fxmapping-ref fxmap
                    key
                    (lambda () (error "fxmapping-ref: key not found"
                                      key
                                      fxmap))
                    values))
    ((fxmap key failure)
     (fxmapping-ref fxmap key failure values))
    ((fxmap key failure success)
     (assume (fxmapping? fxmap))
     (assume (valid-integer? key))
     (assume (procedure? failure))
     (assume (procedure? success))
     (trie-assoc (fxmapping-trie fxmap) key failure success))))

(: fxmapping-ref/default ((struct <fxmapping>) fixnum * -> *))
(define (fxmapping-ref/default fxmap key default)
  (assume (fxmapping? fxmap))
  (assume (valid-integer? key))
  (trie-assoc/default (fxmapping-trie fxmap) key default))

(: fxmapping-min ((struct <fxmapping>) -> fixnum *))
(define (fxmapping-min fxmap)
  (if (fxmapping-empty? fxmap)
      (error "fxmapping-min: empty fxmapping" fxmap)
      (trie-min (fxmapping-trie fxmap))))

(: fxmapping-max ((struct <fxmapping>) -> fixnum *))
(define (fxmapping-max fxmap)
  (if (fxmapping-empty? fxmap)
      (error "fxmapping-max: empty fxmapping" fxmap)
      (trie-max (fxmapping-trie fxmap))))

;;;; Updaters

(: fxmapping-adjoin/combinator
   (fxmapping-t (fixnum * * -> *) #!rest -> fxmapping-t))
(define fxmapping-adjoin/combinator
  (case-lambda
    ((fxmap combine key value)      ; one-assoc fast path
     (raw-fxmapping
      (trie-insert/combine (fxmapping-trie fxmap) key value combine)))
    ((fxmap combine . ps)
     (raw-fxmapping
      (plist-fold (lambda (k v t)
                    (trie-insert/combine t k v combine))
                  (fxmapping-trie fxmap)
                  ps)))))

;; Preserve existing associations for keys.
(: fxmapping-adjoin (fxmapping-t #!rest -> fxmapping-t))
(define fxmapping-adjoin
  (case-lambda
    ((fxmap key value)              ; one-assoc fast path
     (raw-fxmapping
      (trie-adjoin (fxmapping-trie fxmap) key value)))
    ((fxmap . ps)
     (raw-fxmapping
      (plist-fold (lambda (k v t) (trie-adjoin t k v))
                  (fxmapping-trie fxmap)
                  ps)))))

;; Replace existing associations for keys.
(: fxmapping-set (fxmapping-t #!rest -> fxmapping-t))
(define fxmapping-set
  (case-lambda
    ((fxmap key value)      ; one-assoc fast path
     (raw-fxmapping
      (trie-insert (fxmapping-trie fxmap) key value)))
    ((fxmap . ps)
     (raw-fxmapping
      (plist-fold (lambda (k v t) (trie-insert t k v))
                  (fxmapping-trie fxmap)
                  ps)))))

(: fxmapping-adjust (fxmapping-t fixnum (fixnum * -> *) -> fxmapping-t))
(define (fxmapping-adjust fxmap key proc)
  (assume (fxmapping? fxmap))
  (assume (valid-integer? key))
  (assume (procedure? proc))
  (raw-fxmapping (trie-adjust (fxmapping-trie fxmap) key proc)))

(: fxmapping-delete (fxmapping-t #!rest -> fxmapping-t))
(define fxmapping-delete
  (case-lambda
    ((fxmap key)      ; fast path
     (assume (fxmapping? fxmap))
     (assume (valid-integer? key))
     (raw-fxmapping (trie-delete (fxmapping-trie fxmap) key)))
    ((fxmap . keys)
     (fxmapping-delete-all fxmap keys))))

(: fxmapping-delete (fxmapping-t (list-of fixnum) -> fxmapping-t))
(define (fxmapping-delete-all fxmap keys)
  (assume (fxmapping? fxmap))
  (assume (or (pair? keys) (null? keys)))
  (let ((key-map (fxmapping-unfold null?
                                   (lambda (ks) (values (car ks) #t))
                                   cdr
                                   keys)))
    (fxmapping-remove (lambda (k _) (fxmapping-contains? key-map k))
                      fxmap)))

(: fxmapping-update
   (fxmapping-t fixnum (-> *) #!rest -> *))
(define fxmapping-update
  (case-lambda
    ((fxmap key success)
     (fxmapping-update fxmap
                       key
                       success
                       (lambda ()
                         (error "fxmapping-update: key not found" key fxmap))))
    ((fxmap key success failure)
     (assume (fxmapping? fxmap))
     (assume (valid-integer? key))
     (assume (procedure? success))
     (assume (procedure? failure))
     (trie-update (fxmapping-trie fxmap) key success failure raw-fxmapping))))

(: fxmapping-alter (fxmapping-t
                    fixnum
                    (procedure procedure -> *)
                    (fixnum * procedure procedure -> *)
                    -> *))
(define (fxmapping-alter fxmap key failure success)
  (assume (fxmapping? fxmap))
  (assume (valid-integer? key))
  (assume (procedure? failure))
  (assume (procedure? success))
  (trie-alter (fxmapping-trie fxmap) key failure success raw-fxmapping))

(: fxmapping-delete-min (fxmapping-t --> fxmapping-t))
(define (fxmapping-delete-min fxmap)
  (fxmapping-update-min fxmap
                        (lambda (_k _v _rep delete)
                          (delete))))

(: fxmapping-update-min
   (fxmapping-t (fixnum * procedure procedure -> *) -> *))
(define (fxmapping-update-min fxmap success)
  (assume (fxmapping? fxmap))
  (assume (not (fxmapping-empty? fxmap)))
  (assume (procedure? success))
  (trie-update-min (fxmapping-trie fxmap) success raw-fxmapping))

(: fxmapping-pop-min (fxmapping-t --> fixnum * fxmapping-t))
(define (fxmapping-pop-min fxmap)
  (assume (fxmapping? fxmap))
  (if (fxmapping-empty? fxmap)
      (error "fxmapping-pop-min: empty fxmapping" fxmap)
      (let-values (((k v trie) (trie-pop-min (fxmapping-trie fxmap))))
        (values k v (raw-fxmapping trie)))))

(: fxmapping-delete-max (fxmapping-t --> fxmapping-t))
(define (fxmapping-delete-max fxmap)
  (fxmapping-update-max fxmap
                        (lambda (_k _v _rep delete)
                          (delete))))

(: fxmapping-update-max
   (fxmapping-t (fixnum * procedure procedure -> *) -> *))
(define (fxmapping-update-max fxmap success)
  (assume (fxmapping? fxmap))
  (assume (not (fxmapping-empty? fxmap)))
  (assume (procedure? success))
  (trie-update-max (fxmapping-trie fxmap) success raw-fxmapping))

(: fxmapping-pop-max (fxmapping-t --> fixnum * fxmapping-t))
(define (fxmapping-pop-max fxmap)
  (assume (fxmapping? fxmap))
  (if (fxmapping-empty? fxmap)
      (error "fxmapping-pop-max: empty fxmapping" fxmap)
      (let-values (((k v trie) (trie-pop-max (fxmapping-trie fxmap))))
        (values k v (raw-fxmapping trie)))))

;;;; The whole fxmapping

(: fxmapping-size (fxmapping-t --> fixnum))
(define (fxmapping-size fxmap)
  (assume (fxmapping? fxmap))
  (trie-size (fxmapping-trie fxmap)))

(: fxmapping-find
   ((fixnum * -> boolean) fxmapping-t (-> *) #!rest -> *))
(define fxmapping-find
  (case-lambda
    ((pred fxmap failure)
     (fxmapping-find pred fxmap failure values))
    ((pred fxmap failure success)
     (assume (procedure? pred))
     (assume (fxmapping? fxmap))
     (assume (procedure? failure))
     (assume (procedure? success))
     (trie-find pred (fxmapping-trie fxmap) failure success))))

(: fxmapping-count ((fixnum * -> boolean) fxmapping-t --> fixnum))
(define (fxmapping-count pred fxmap)
  (assume (procedure? pred))
  (fxmapping-fold (lambda (k v acc)
                    (if (pred k v) (+ 1 acc) acc))
                  0
                  fxmap))

(: fxmapping-any? ((fixnum * -> boolean) fxmapping-t -> boolean))
(define (fxmapping-any? pred fxmap)
  (assume (procedure? pred))
  (call-with-current-continuation
   (lambda (return)
     (fxmapping-fold (lambda (k v _)
                       (and (pred k v) (return #t)))
                     #f
                     fxmap))))

(: fxmapping-every? ((fixnum * -> boolean) fxmapping-t -> boolean))
(define (fxmapping-every? pred fxmap)
  (assume (procedure? pred))
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
(: fxmapping-map ((fixnum * -> *) fxmapping-t -> fxmapping-t))
(define (fxmapping-map proc fxmap)
  (assume (procedure? proc))
  (assume (fxmapping? fxmap))
  (raw-fxmapping (trie-map proc (fxmapping-trie fxmap))))

(define (unspecified)
  (if #f #f))

(: fxmapping-for-each ((fixnum * -> *) fxmapping-t -> undefined))
(define (fxmapping-for-each proc fxmap)
  (assume (procedure? proc))
  (fxmapping-fold (lambda (k v _)
                    (proc k v)
                    (unspecified))
                  (unspecified)
                  fxmap))

(: fxmapping-fold ((fixnum * * -> *) * fxmapping-t -> *))
(define (fxmapping-fold proc nil fxmap)
  (assume (procedure? proc))
  (assume (fxmapping? fxmap))
  (let ((trie (fxmapping-trie fxmap)))
    (tmatch trie
      ((branch ? ,m ,l ,r) (guard (negative? m))
       (trie-fold-left proc (trie-fold-left proc nil r) l))
      ((branch ? ? ,l ,r)
       (trie-fold-left proc (trie-fold-left proc nil l) r))
      (else (trie-fold-left proc nil trie)))))

(: fxmapping-fold-right ((fixnum * * -> *) * fxmapping-t -> *))
(define (fxmapping-fold-right proc nil fxmap)
  (assume (procedure? proc))
  (assume (fxmapping? fxmap))
  (let ((trie (fxmapping-trie fxmap)))
    (tmatch trie
      ((branch ? ,m ,l ,r) (guard (negative? m))
       (trie-fold-right proc (trie-fold-right proc nil l) r))
      ((branch ? ? ,l ,r)
       (trie-fold-right proc (trie-fold-right proc nil r) l))
      (else (trie-fold-right proc nil trie)))))

(: fxmapping-map->list ((fixnum * -> *) fxmapping-t -> (list-of *)))
(define (fxmapping-map->list proc fxmap)
  (assume (procedure? proc))
  (fxmapping-fold-right (lambda (k v us)
                          (cons (proc k v) us))
                        '()
                        fxmap))

(: fxmapping-filter ((fixnum * -> boolean) fxmapping-t -> fxmapping-t))
(define (fxmapping-filter pred fxmap)
  (assume (procedure? pred))
  (assume (fxmapping? fxmap))
  (raw-fxmapping (trie-filter pred (fxmapping-trie fxmap))))

(: fxmapping-remove ((fixnum * -> boolean) fxmapping-t -> fxmapping-t))
(define (fxmapping-remove pred fxmap)
  (fxmapping-filter (lambda (k v) (not (pred k v))) fxmap))

(: fxmapping-partition
   ((fixnum * -> boolean) fxmapping-t -> fxmapping-t fxmapping-t))
(define (fxmapping-partition pred fxmap)
  (assume (procedure? pred))
  (assume (fxmapping? fxmap))
  (let-values (((tin tout)
                (trie-partition pred (fxmapping-trie fxmap))))
    (values (raw-fxmapping tin) (raw-fxmapping tout))))

;;;; Conversion

(: fxmapping->alist (fxmapping-t --> (list-of (pair fixnum *))))
(define (fxmapping->alist fxmap)
  (fxmapping-fold-right (lambda (k v as) (cons (cons k v) as))
                        '()
                        fxmap))

(: fxmapping->decreasing-alist
   (fxmapping-t --> (list-of (pair fixnum *))))
(define (fxmapping->decreasing-alist fxmap)
  (fxmapping-fold (lambda (k v as) (cons (cons k v) as))
                  '()
                  fxmap))

(: fxmapping-keys (fxmapping-t --> (list-of fixnum)))
(define (fxmapping-keys fxmap)
  (fxmapping-fold-right (lambda (k _ ks) (cons k ks)) '() fxmap))

(: fxmapping-values (fxmapping-t --> list))
(define (fxmapping-values fxmap)
  (fxmapping-fold-right (lambda (_ v vs) (cons v vs)) '() fxmap))

(: fxmapping->generator (fxmapping-t -> procedure))
(define (fxmapping->generator fxmap)
  (assume (fxmapping? fxmap))
  (make-coroutine-generator
   (lambda (yield)
     (fxmapping-fold (lambda (k v _) (yield (cons k v)))
                     #f
                     fxmap))))

(: fxmapping->decreasing-generator (fxmapping-t --> procedure))
(define (fxmapping->decreasing-generator fxmap)
  (assume (fxmapping? fxmap))
  (make-coroutine-generator
   (lambda (yield)
     (fxmapping-fold-right (lambda (k v _) (yield (cons k v)))
                           #f
                           fxmap))))

;;;; Comparison

(: fxmapping=?
   ((struct comparator) fxmapping-t fxmapping-t #!rest --> boolean))
(define (fxmapping=? comp fxmap1 fxmap2 . imaps)
  (assume (comparator? comp))
  (assume (fxmapping? fxmap1))
  (let ((fxmap-eq1 (lambda (fxmap)
                     (assume (fxmapping? fxmap))
                     (or (eqv? fxmap1 fxmap)
                         (trie=? comp
                                 (fxmapping-trie fxmap1)
                                 (fxmapping-trie fxmap))))))
    (and (fxmap-eq1 fxmap2)
         (or (null? imaps)
             (every fxmap-eq1 imaps)))))

(: fxmapping<?
   ((struct comparator) fxmapping-t fxmapping-t #!rest --> boolean))
(define (fxmapping<? comp fxmap1 fxmap2 . imaps)
  (assume (comparator? comp))
  (assume (fxmapping? fxmap1))
  (assume (fxmapping? fxmap2))
  (let lp ((t1 (fxmapping-trie fxmap1))
           (t2 (fxmapping-trie fxmap2))
           (imaps imaps))
    (and (trie-proper-subset? comp t1 t2)
         (pmatch imaps
           (() #t)
           ((,m . ,imaps*) (lp t2 (fxmapping-trie m) imaps*))))))

(: fxmapping>?
   ((struct comparator) fxmapping-t fxmapping-t #!rest --> boolean))
(define (fxmapping>? comp fxmap1 fxmap2 . imaps)
  (assume (comparator? comp))
  (assume (fxmapping? fxmap1))
  (assume (fxmapping? fxmap2))
  (let lp ((t1 (fxmapping-trie fxmap1))
           (t2 (fxmapping-trie fxmap2))
           (imaps imaps))
    (and (trie-proper-subset? comp t2 t1)
         (pmatch imaps
           (() #t)
           ((,m . ,imaps*) (lp t2 (fxmapping-trie m) imaps*))))))

(: fxmapping<=?
   ((struct comparator) fxmapping-t fxmapping-t #!rest --> boolean))
(define (fxmapping<=? comp fxmap1 fxmap2 . imaps)
  (assume (comparator? comp))
  (assume (fxmapping? fxmap1))
  (assume (fxmapping? fxmap2))
  (let lp ((t1 (fxmapping-trie fxmap1))
           (t2 (fxmapping-trie fxmap2))
           (imaps imaps))
    (and (memv (trie-subset-compare comp t1 t2) '(less equal))
         (pmatch imaps
           (() #t)
           ((,m . ,imaps*) (lp t2 (fxmapping-trie m) imaps*))))))

(: fxmapping>=?
   ((struct comparator) fxmapping-t fxmapping-t #!rest --> boolean))
(define (fxmapping>=? comp fxmap1 fxmap2 . imaps)
  (assume (comparator? comp))
  (assume (fxmapping? fxmap1))
  (assume (fxmapping? fxmap2))
  (let lp ((t1 (fxmapping-trie fxmap1))
           (t2 (fxmapping-trie fxmap2))
           (imaps imaps))
    (and (memv (trie-subset-compare comp t2 t1) '(less equal))
         (pmatch imaps
           (() #t)
           ((,m . ,imaps*) (lp t2 (fxmapping-trie m) imaps*))))))

;;;; Set theory operations

(: fxmapping-union (#!rest fxmapping-t --> fxmapping-t))
(define (fxmapping-union . args)
  (apply fxmapping-union/combinator first-arg args))

(: fxmapping-intersection (#!rest fxmapping-t --> fxmapping-t))
(define (fxmapping-intersection . args)
  (apply fxmapping-intersection/combinator first-arg args))

(: fxmapping-difference (#!rest fxmapping-t --> fxmapping-t))
(define fxmapping-difference
  (case-lambda
    ((fxmap1 fxmap2)
     (assume (fxmapping? fxmap1))
     (assume (fxmapping? fxmap2))
     (raw-fxmapping
      (trie-difference (fxmapping-trie fxmap1)
                       (fxmapping-trie fxmap2))))
    ((fxmap . rest)
     (assume (fxmapping? fxmap))
     (assume (pair? rest))
     (raw-fxmapping
      (trie-difference (fxmapping-trie fxmap)
                       (fxmapping-trie
                        (apply fxmapping-union rest)))))))

(: fxmapping-xor (fxmapping-t fxmapping-t --> fxmapping-t))
(define (fxmapping-xor fxmap1 fxmap2)
  (assume (fxmapping? fxmap1))
  (assume (fxmapping? fxmap2))
  (raw-fxmapping
   (trie-xor (fxmapping-trie fxmap1) (fxmapping-trie fxmap2))))

(: fxmapping-union/combinator
   ((fixnum * * -> *) #!rest fxmapping-t --> fxmapping-t))
(define (fxmapping-union/combinator proc fxmap . rest)
  (assume (procedure? proc))
  (assume (fxmapping? fxmap))
  (assume (pair? rest))
  (raw-fxmapping
   (fold (lambda (im t)
           (assume (fxmapping? im))
           (trie-merge proc t (fxmapping-trie im)))
         (fxmapping-trie fxmap)
         rest)))

(: fxmapping-intersection/combinator
   ((fixnum * * -> *) #!rest fxmapping-t --> fxmapping-t))
(define (fxmapping-intersection/combinator proc fxmap . rest)
  (assume (procedure? proc))
  (assume (fxmapping? fxmap))
  (assume (pair? rest))
  (raw-fxmapping
   (fold (lambda (im t)
           (assume (fxmapping? im))
           (trie-intersection proc t (fxmapping-trie im)))
         (fxmapping-trie fxmap)
         rest)))

;;;; Subsets

(: fxsubmapping= (fxmapping-t fixnum --> fxmapping-t))
(define (fxsubmapping= fxmap key)
  (fxmapping-ref fxmap
                 key
                 fxmapping
                 (lambda (v) (fxmapping key v))))

(: fxmapping-open-interval (fxmapping-t fixnum fixnum --> fxmapping-t))
(define (fxmapping-open-interval fxmap low high)
  (assume (fxmapping? fxmap))
  (assume (valid-integer? low))
  (assume (valid-integer? high))
  (assume (fx>=? high low))
  (raw-fxmapping
   (subtrie-interval (fxmapping-trie fxmap) low high #f #f)))

(: fxmapping-closed-interval (fxmapping-t fixnum fixnum --> fxmapping-t))
(define (fxmapping-closed-interval fxmap low high)
  (assume (fxmapping? fxmap))
  (assume (valid-integer? low))
  (assume (valid-integer? high))
  (assume (fx>=? high low))
  (raw-fxmapping
   (subtrie-interval (fxmapping-trie fxmap) low high #t #t)))

(: fxmapping-open-closed-interval
   (fxmapping-t fixnum fixnum --> fxmapping-t))
(define (fxmapping-open-closed-interval fxmap low high)
  (assume (fxmapping? fxmap))
  (assume (valid-integer? low))
  (assume (valid-integer? high))
  (assume (fx>=? high low))
  (raw-fxmapping
   (subtrie-interval (fxmapping-trie fxmap) low high #f #t)))

(: fxmapping-closed-open-interval
   (fxmapping-t fixnum fixnum --> fxmapping-t))
(define (fxmapping-closed-open-interval fxmap low high)
  (assume (fxmapping? fxmap))
  (assume (valid-integer? low))
  (assume (valid-integer? high))
  (assume (fx>=? high low))
  (raw-fxmapping
   (subtrie-interval (fxmapping-trie fxmap) low high #t #f)))

(: fxsubmapping< (fxmapping-t fixnum --> fxmapping-t))
(define (fxsubmapping< fxmap key)
  (assume (fxmapping? fxmap))
  (assume (valid-integer? key))
  (raw-fxmapping (subtrie< (fxmapping-trie fxmap) key #f)))

(: fxsubmapping<= (fxmapping-t fixnum --> fxmapping-t))
(define (fxsubmapping<= fxmap key)
  (assume (fxmapping? fxmap))
  (assume (valid-integer? key))
  (raw-fxmapping (subtrie< (fxmapping-trie fxmap) key #t)))

(: fxsubmapping> (fxmapping-t fixnum --> fxmapping-t))
(define (fxsubmapping> fxmap key)
  (assume (fxmapping? fxmap))
  (assume (valid-integer? key))
  (raw-fxmapping (subtrie> (fxmapping-trie fxmap) key #f)))

(: fxsubmapping>= (fxmapping-t fixnum --> fxmapping-t))
(define (fxsubmapping>= fxmap key)
  (assume (fxmapping? fxmap))
  (assume (valid-integer? key))
  (raw-fxmapping (subtrie> (fxmapping-trie fxmap) key #t)))

(: fxmapping-split (fxmapping-t fixnum --> fxmapping-t))
(define (fxmapping-split fxmap k)
  (assume (fxmapping? fxmap))
  (assume (integer? k))
  (let-values (((trie-low trie-high)
                (trie-split (fxmapping-trie fxmap) k)))
    (values (raw-fxmapping trie-low) (raw-fxmapping trie-high))))

;;;; fxmappings as relations

(: fxmapping-relation-map
   ((fixnum * -> fixnum *) fxmapping-t -> fxmapping-t))
(define (fxmapping-relation-map proc fxmap)
  (assume (procedure? proc))
  (assume (fxmapping? fxmap))
  (raw-fxmapping (trie-relation-map proc (fxmapping-trie fxmap))))
