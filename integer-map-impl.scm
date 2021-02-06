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

(define (plist-fold proc nil ps)
  (let loop ((b nil) (ps ps))
    (match ps
      (() b)
      ((k v . ps*)
       (loop (proc k v b) ps*)))))

(define (first x _) x)
(define (second _ y) y)

(define (constantly x)
  (lambda _ x))

;;;; Type

(define-record-type <imapping>
  (raw-imapping trie)
  imapping?
  (trie imapping-trie))

;;;; Constructors

(define (imapping . args)
  (raw-imapping
    (plist-fold (lambda (k v trie)
                  (trie-insert/combine trie k v second))
                #f
                args)))

(define (pair-or-null? x)
  (or (pair? x) (null? x)))

(define (alist->imapping as)
  (assume (pair-or-null? as))
  (imapping-unfold-maybe (match-lambda
                           (() (nothing))
                           (((k . v) . as*) (just k v as*)))
                         as))

(define (imapping-unfold stop? mapper successor seed)
  (assume (procedure? stop?))
  (assume (procedure? mapper))
  (assume (procedure? successor))
  (let lp ((trie #f) (seed seed))
    (if (stop? seed)
        (raw-imapping trie)
        (let-values (((k v) (mapper seed)))
          (assume (valid-integer? k))
          (lp (trie-insert trie k v) (successor seed))))))

(define (imapping-unfold-maybe proc seed)
  (assume (procedure? proc))
  (let lp ((trie #f) (seed seed))
    (maybe-ref
     (proc seed)
     (lambda () (raw-imapping trie))
     (lambda (k v seed*)
       (lp (trie-insert trie k v) seed*)))))

;;;; Predicates

(define (imapping-contains? imap n)
  (assume (imapping? imap))
  (assume (valid-integer? n))
  (and (trie-assoc (imapping-trie imap) n) #t))

(define (imapping-empty? imap)
  (assume (imapping? imap))
  (not (imapping-trie imap)))

(define (imapping-disjoint? imap1 imap2)
  (assume (imapping? imap1))
  (assume (imapping? imap2))
  (trie-disjoint? (imapping-trie imap1) (imapping-trie imap1)))

;;;; Accessors

(define (imapping-lookup imap key)
  (assume (imapping? imap))
  (assume (valid-integer? key))
  (truth->maybe (trie-assoc (imapping-trie imap) key)))

(define (imapping-lookup/default imap key default)
  (maybe-ref/default (imapping-lookup imap key) default))

(define (imapping-min imap)
  (assume (imapping? imap))
  (let ((trie (imapping-trie imap)))
    (if (branch? trie)
        (%trie-find-leftmost
         (if (negative? (branch-branching-bit trie))
             (branch-right trie)
             (branch-left trie)))
        (%trie-find-leftmost trie))))

(define (imapping-max imap)
  (assume (imapping? imap))
  (let ((trie (imapping-trie imap)))
    (if (branch? trie)
        (%trie-find-rightmost
         (if (negative? (branch-branching-bit trie))
             (branch-left trie)
             (branch-right trie)))
        (%trie-find-rightmost trie))))

;;;; Updaters

(define imapping-adjoin/combine
  (case-lambda
    ((imap combine key value)      ; one-assoc fast path
     (raw-imapping
      (trie-insert/combine (imapping-trie imap) key value combine)))
    ((imap combine . ps)
     (raw-imapping
      (plist-fold (lambda (k v t)
                    (trie-insert/combine t k v combine))
                  (imapping-trie imap)
                  ps)))))

(define imapping-adjoin
  (case-lambda
    ((imap key value)              ; one-assoc fast path
     (raw-imapping
      (trie-insert (imapping-trie imap) key value)))
    ((imap . ps)
     (raw-imapping
      (plist-fold (lambda (k v t) (trie-insert t k v))
                  (imapping-trie imap)
                  ps)))))

(define (imapping-adjust imap key proc)
  (assume (imapping? imap))
  (assume (valid-integer? key))
  (assume (procedure? proc))
  (raw-imapping (trie-adjust (imapping-trie imap) key proc #f)))

(define (imapping-adjust/key imap key proc)
  (assume (imapping? imap))
  (assume (valid-integer? key))
  (assume (procedure? proc))
  (raw-imapping (trie-adjust (imapping-trie imap) key proc #t)))

(define imapping-delete
  (case-lambda
    ((imap key)      ; fast path
     (assume (imapping? imap))
     (assume (valid-integer? key))
     (raw-imapping (trie-delete (imapping-trie imap) key)))
    ((imap . keys)
     (imapping-delete-all imap keys))))

;; FIXME: Uses keys as an lset, which is inefficient.
(define (imapping-delete-all imap keys)
  (assume (imapping? imap))
  (assume (or (pair? keys) (null? keys)))
  (imapping-filter (lambda (k _) (memv k keys)) imap))

;; Update the association (key, value) in trie with the result of
;; (mproc value), which is a Maybe value.
(define (imapping-update imap key mproc)
  (assume (imapping? imap))
  (assume (valid-integer? key))
  (assume (procedure? mproc))
  (raw-imapping (trie-update (imapping-trie imap) key mproc #f)))

;; Update the association (key, value) in trie with the result of
;; (mproc key value), which is a Maybe value.
(define (imapping-update/key imap key mproc)
  (assume (imapping? imap))
  (assume (valid-integer? key))
  (assume (procedure? mproc))
  (raw-imapping (trie-update (imapping-trie imap) key mproc #t)))

;; Update the association (key, value) (or lack thereof) in imap
;; using proc, which is an endomap on Maybes.
(define (imapping-alter imap key proc)
  (assume (imapping? imap))
  (assume (valid-integer? key))
  (assume (procedure? proc))
  (raw-imapping (trie-alter (imapping-trie imap) key proc)))

;; Delete the element with the least key, or return an empty
;; mapping if `imap' is empty.
(define (imapping-delete-min imap)
  (imapping-update-min/key imap (constantly (nothing))))

;; Call success on the value of the element of `imap' with the least
;; key and use the value, a Maybe, to update the mapping.
(define (imapping-update-min imap success)
  (imapping-update-min/key imap (lambda (_ v) (success v))))

;; Call success on the least key and corresponding value of `imap'
;; and use the value, a Maybe, to update the mapping.
(define (imapping-update-min/key imap success)
  (assume (imapping? imap))
  (assume (procedure? success))
  (raw-imapping
   (%trie-update-min/key
    (let ((trie (imapping-trie imap)))
      (if (branch? trie)
          (if (negative? (branch-branching-bit trie))
              (branch-right trie)
              (branch-left trie))
          trie))
    success)))

;; Delete the element with the greatest key, or return an empty
;; mapping if `imap' is empty.
(define (imapping-delete-max imap)
  (imapping-update-max/key imap (constantly (nothing))))

;; Call success on the value of the element of `imap' with the
;; greatest key and use the value, a Maybe, to update the mapping.
(define (imapping-update-max imap success)
  (imapping-update-max/key imap (lambda (_ v) (success v))))

;; Call success on the greatest key and corresponding value of `imap'
;; and use the value, a Maybe, to update the mapping.
(define (imapping-update-max/key imap success)
  (assume (imapping? imap))
  (assume (procedure? success))
  (raw-imapping
   (%trie-update-max/key
    (let ((trie (imapping-trie imap)))
      (if (branch? trie)
          (if (negative? (branch-branching-bit trie))
              (branch-left trie)
              (branch-right trie))
          trie))
    success)))

;;;; The whole imapping

(define (imapping-size imap)
  (assume (imapping? imap))
  (let lp ((acc 0) (t (imapping-trie imap)))
    (cond ((not t) acc)
          ((leaf? t) (+ acc 1))
          (else
           (lp (lp acc (branch-left t)) (branch-right t))))))

(define (imapping-count pred imap)
  (assume (procedure? pred))
  (imapping-fold-left (lambda (v acc)
                        (if (pred v) (+ 1 acc) acc))
                      0
                      imap))

(define (imapping-any? pred imap)
  (assume (procedure? pred))
  (call-with-current-continuation
   (lambda (return)
     (imapping-fold-left (lambda (v _)
                           (and (pred v) (return #t)))
                         #f
                         imap))))

(define (imapping-every? pred imap)
  (assume (procedure? pred))
  (call-with-current-continuation
   (lambda (return)
     (imapping-fold-left (lambda (v _)
                           (or (pred v) (return #f)))
                         #t
                         imap))))

;;;; Mapping and folding

;; Map proc over the values of imap, inserting result values under
;; the same key.
;; This is *not* the same as SRFI 146's mapping-map.
(define (imapping-map proc imap)
  (assume (procedure? proc))
  (raw-imapping
   (imapping-fold-left/key (lambda (k v t)
                             (trie-insert t k (proc v)))
                           #f
                           imap)))

(define (imapping-map/key proc imap)
  (assume (procedure? proc))
  (raw-imapping
   (imapping-fold-left/key (lambda (k v t)
                             (trie-insert t k (proc k v)))
                           #f
                           imap)))

(define (unspecified)
  (if #f #f))

(define (imapping-for-each proc imap)
  (assume (procedure? proc))
  (imapping-fold-left (lambda (v _)
                        (proc v)
                        (unspecified))
                      (unspecified)
                      imap))

(define (imapping-for-each/key proc imap)
  (assume (procedure? proc))
  (imapping-fold-left/key (lambda (k v _)
                            (proc k v)
                            (unspecified))
                          (unspecified)
                          imap))

(define (imapping-fold-left proc nil imap)
  (assume (procedure? proc))
  (assume (imapping? imap))
  (let ((trie (imapping-trie imap)))
    (if (branch? trie)
        (let*-branch (((p m l r) trie))
          (if (negative? m)
              (trie-fold-left proc (trie-fold-left proc nil r) l)
              (trie-fold-left proc (trie-fold-left proc nil l) r)))
        (trie-fold-left proc nil trie))))

(define (imapping-fold-left/key proc nil imap)
  (assume (procedure? proc))
  (assume (imapping? imap))
  (let ((trie (imapping-trie imap)))
    (if (branch? trie)
        (let*-branch (((p m l r) trie))
          (if (negative? m)
              (trie-fold-left/key proc (trie-fold-left/key proc nil r) l)
              (trie-fold-left/key proc (trie-fold-left/key proc nil l) r)))
        (trie-fold-left/key proc nil trie))))

(define (imapping-fold-right proc nil imap)
  (assume (procedure? proc))
  (assume (imapping? imap))
  (let ((trie (imapping-trie imap)))
    (if (branch? trie)
        (let*-branch (((p m l r) trie))
          (if (negative? m)
              (trie-fold-right proc (trie-fold-right proc nil l) r)
              (trie-fold-right proc (trie-fold-right proc nil r) l)))
        (trie-fold-right proc nil trie))))

(define (imapping-fold-right/key proc nil imap)
  (assume (procedure? proc))
  (assume (imapping? imap))
  (let ((trie (imapping-trie imap)))
    (if (branch? trie)
        (let*-branch (((p m l r) trie))
          (if (negative? m)
              (trie-fold-right/key proc (trie-fold-right/key proc nil l) r)
              (trie-fold-right/key proc (trie-fold-right/key proc nil r) l)))
        (trie-fold-right/key proc nil trie))))

(define (imapping-map->list proc imap)
  (assume (procedure? proc))
  (imapping-fold-right (lambda (v us)
                         (cons (proc v) us))
                       '()
                       imap))

(define (imapping-map/key->list proc imap)
  (assume (procedure? proc))
  (imapping-fold-right (lambda (k v us)
                         (cons (proc k v) us))
                       '()
                       imap))

(define (imapping-filter pred imap)
  (assume (procedure? pred))
  (assume (imapping? imap))
  (raw-imapping (trie-filter pred (imapping-trie imap))))

(define (imapping-filter/key pred imap)
  (assume (procedure? pred))
  (assume (imapping? imap))
  (raw-imapping (trie-filter/key pred (imapping-trie imap))))

(define (imapping-remove pred imap)
  (imapping-filter (lambda (v) (not (pred v))) imap))

(define (imapping-remove/key pred imap)
  (imapping-filter/key (lambda (k v) (not (pred v))) imap))

(define (imapping-partition pred imap)
  (assume (procedure? pred))
  (assume (imapping? imap))
  (let-values (((tin tout)
                (trie-partition pred (imapping-trie imap) #f)))
    (values (raw-imapping tin) (raw-imapping tout))))

(define (imapping-partition/key pred imap)
  (assume (procedure? pred))
  (assume (imapping? imap))
  (let-values (((tin tout)
                (trie-partition pred (imapping-trie imap) #t)))
    (values (raw-imapping tin) (raw-imapping tout))))

;;;; Conversion

(define (imapping->alist imap)
  (imapping-fold-right/key (lambda (k v as) (cons (cons k v) as))
                           '()
                           imap))

(define (imapping-keys imap)
  (imapping-fold-right/key (lambda (k _ ks) (cons k ks)) '() imap))

(define (imapping-values imap)
  (imapping-fold-right cons '() imap))

;;;; Comparison

(define (imapping=? comp imap1 imap2 . imaps)
  (assume (comparator? comp))
  (assume (imapping? imap1))
  (let ((imap-eq1 (lambda (imap)
                    (assume (imapping? imap))
                    (or (eqv? imap1 imap)
                        (trie=? comp
                                (imapping-trie imap1)
                                (imapping-trie imap))))))
    (and (imap-eq1 imap2)
         (or (null? imaps)
             (every imap-eq1 imaps)))))

(define (imapping<? comp imap1 imap2 . imaps)
  (assume (comparator? comp))
  (assume (imapping? imap1))
  (assume (imapping? imap2))
  (let lp ((t1 (imapping-trie imap1))
           (t2 (imapping-trie imap2))
           (imaps imaps))
    (and (trie-proper-subset? comp t1 t2)
         (match imaps
           (() #t)
           ((m . imaps*) (lp t2 (imapping-trie m) imaps*))))))

(define (imapping>? comp imap1 imap2 . imaps)
  (assume (comparator? comp))
  (assume (imapping? imap1))
  (assume (imapping? imap2))
  (let lp ((t1 (imapping-trie imap1))
           (t2 (imapping-trie imap2))
           (imaps imaps))
    (and (trie-proper-subset? comp t2 t1)
         (match imaps
           (() #t)
           ((m . imaps*) (lp t2 (imapping-trie m) imaps*))))))

(define (imapping<=? comp imap1 imap2 . imaps)
  (assume (comparator? comp))
  (assume (imapping? imap1))
  (assume (imapping? imap2))
  (let lp ((t1 (imapping-trie imap1))
           (t2 (imapping-trie imap2))
           (imaps imaps))
    (and (memv (trie-subset-compare comp t1 t2) '(less equal))
         (match imaps
           (() #t)
           ((m . imaps*) (lp t2 (imapping-trie m) imaps*))))))

(define (imapping>=? comp imap1 imap2 . imaps)
  (assume (comparator? comp))
  (assume (imapping? imap1))
  (assume (imapping? imap2))
  (let lp ((t1 (imapping-trie imap1))
           (t2 (imapping-trie imap2))
           (imaps imaps))
    (and (memv (trie-subset-compare comp t1 t2) '(greater equal))
         (match imaps
           (() #t)
           ((m . imaps*) (lp t2 (imapping-trie m) imaps*))))))

;;;; Set theory operations

(define (imapping-union imap . rest)
  (assume (imapping? imap))
  (assume (pair? rest))
  (raw-imapping
   (fold (lambda (im t)
           (assume (imapping? im))
           (trie-merge second (imapping-trie im) t))
         (imapping-trie imap)
         rest)))

(define (imapping-intersection imap . rest)
  (assume (imapping? imap))
  (assume (pair? rest))
  (raw-imapping
   (fold (lambda (im t)
           (assume (imapping? im))
           (trie-intersection (imapping-trie im) t))
         (imapping-trie imap)
         rest)))

(define (imapping-difference imap . rest)
  (assume (imapping? imap))
  (assume (pair? rest))
  (raw-imapping
   (trie-difference (imapping-trie imap)
                    (imapping-trie
                     (match rest
                       ((imap2) imap2)
                       ((imap2 . imaps)
                        (apply imapping-union imap2 imaps)))))))

(define (imapping-xor imap1 imap2)
  (assume (imapping? imap1))
  (assume (imapping? imap2))
  (raw-imapping
   (trie-xor (imapping-trie mapping1) (imapping-trie mapping2))))

;;;; Subsets

(define (isubmapping= imap key)
  (assume (imapping? imap))
  (assume (valid-integer? key))
  (cond ((imapping-assoc imap key) => (lambda (v) (imapping key v)))
        (else (imapping))))

(define (imapping-open-interval imap low high)
  (assume (imapping? imap))
  (assume (valid-integer? low))
  (assume (valid-integer? high))
  (assume (fx>=? high low))
  (raw-imapping
   (subtrie-interval (imapping-trie imap) low high #f #f)))

(define (imapping-closed-interval imap low high)
  (assume (imapping? imap))
  (assume (valid-integer? low))
  (assume (valid-integer? high))
  (assume (fx>=? high low))
  (raw-imapping
   (subtrie-interval (imapping-trie imap) low high #t #t)))

(define (imapping-open-closed-interval imap low high)
  (assume (imapping? imap))
  (assume (valid-integer? low))
  (assume (valid-integer? high))
  (assume (fx>=? high low))
  (raw-imapping
   (subtrie-interval (imapping-trie imap) low high #f #t)))

(define (imapping-closed-open-interval imap low high)
  (assume (imapping? imap))
  (assume (valid-integer? low))
  (assume (valid-integer? high))
  (assume (fx>=? high low))
  (raw-imapping
   (subtrie-interval (imapping-trie imap) low high #t #f)))

(define (imapping< imap key)
  (assume (imapping? imap))
  (assume (valid-integer? key))
  (raw-imapping (subtrie< (imapping-trie imap) key #f)))

(define (imapping-range<= imap key)
  (assume (imapping? imap))
  (assume (valid-integer? key))
  (raw-imapping (subtrie< (imapping-trie imap) key #t)))

(define (imapping-range> imap key)
  (assume (imapping? imap))
  (assume (valid-integer? key))
  (raw-imapping (subtrie> (imapping-trie imap) key #f)))

(define (imapping-range>= imap key)
  (assume (imapping? imap))
  (assume (valid-integer? key))
  (raw-imapping (subtrie> (imapping-trie imap) key #t)))
