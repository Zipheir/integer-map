;;; This file implements integers maps as compressed binary radix
;;; trees (AKA Patricia tries), as described by Chris Okasaki and
;;; Andrew Gill in "Fast Mergeable Integer Maps" (1998).  Integers
;;; in big-endian binary encoding are stored in a trie structure
;;; which allows fast lookup, insertion, and set-theoretical
;;; operations (union, intersection, etc.)
;;;
;;; A trie is represented by #f (the empty trie), a leaf, or a branch.
;;;
;;; Throughout this code, the empty trie (#f) is always returned
;;; as an explicit value, not, e.g. as the default value of an
;;; (and ...) expression, to clarify its use as a trie value.

;;;; Utility

(define (swap-args proc)
  (lambda (x y) (proc y x)))

(define-record-type <leaf>
  (leaf key value)
  leaf?
  (key leaf-key)
  (value leaf-value))

;; Shorthand for extracting leaf elements.
(define-syntax let*-leaf
  (syntax-rules ()
    ((_ () e1 e2 ...) (begin e1 e2 ...))
    ((_ (((k v) expr) . binds) . body)
     (let ((lf expr))
       (let ((k (leaf-key lf))
             (v (leaf-value lf)))
         (let*-leaf binds . body))))))

(define-record-type <branch>
  (raw-branch prefix branching-bit left right)
  branch?
  (prefix branch-prefix)
  (branching-bit branch-branching-bit)
  (left branch-left)
  (right branch-right))

;; Shorthand for extracting branch elements.
(define-syntax let*-branch
  (syntax-rules ()
    ((_ () e1 e2 ...) (begin e1 e2 ...))
    ((_ (((p m l r) expr) . binds) . body)
     (let ((b expr))
       (let ((p (branch-prefix b))
             (m (branch-branching-bit b))
             (l (branch-left b))
             (r (branch-right b)))
         (let*-branch binds . body))))))

(define (valid-integer? x) (fixnum? x))

;; Zero the bits of k at and below (BE) the set bit of m.
(define (mask k m)
  (if (fx=? m fx-least)
      0
      (fxand k (fxxor (fxnot (fx- m 1)) m))))

;; Does the m-masked prefix of k match p?
(define (match-prefix? k p m)
  (fx=? (mask k m) p))

(define (branching-bit p1 m1 p2 m2)
  (if (fxnegative? (fxxor p1 p2))
      fx-least        ; different signs
      (highest-bit-mask (fxxor p1 p2) (fxmax 1 (fx* 2 (fxmax m1 m2))))))

;; Two's-complement trick.
(define (lowest-set-bit b)
  (fxand b (fxneg b)))

(define (highest-bit-mask k guess-m)
  (let lp ((x (fxand k (fxnot (fx- guess-m 1)))))
    (let ((m (lowest-set-bit x)))
      (if (fx=? x m)
          m
          (lp (fx- x m))))))

(define (zero-bit? k m)
  (fxzero? (fxand k m)))

;; Insert the association (key, value) into trie, replacing any old
;; association.
(define (trie-insert trie key value)
  (trie-insert/combine trie key value (lambda (new _) new)))

;; Insert (key, value) into trie if key doesn't already have an
;; association.  If it does, add a new association for key and
;; the result of calling combine on the new and old values.
(define (trie-insert/combine trie key value combine)
  (let-values (((trie* _)
                (trie-search trie
                             key
                             (lambda (ins _ig) (ins #t))
                             (lambda (_key old up _rem)
                               (up key (combine value old) #t)))))
    trie*))

(define (trie-join prefix1 mask1 trie1 prefix2 mask2 trie2)
  (let ((m (branching-bit prefix1 mask1 prefix2 mask2)))
    (if (zero-bit? prefix1 m)
        (branch (mask prefix1 m) m trie1 trie2)
        (branch (mask prefix1 m) m trie2 trie1))))

;; Return the value associated with key in trie; if there is
;; none, return #f.
(define (trie-assoc trie key)
  (and trie
       (if (leaf? trie)
           (and (fx=? (leaf-key trie) key) (leaf-value trie))
           (let*-branch (((p m l r) trie))
             (and (match-prefix? key p m)
                  (if (zero-bit? key m)
                      (trie-contains? l key)
                      (trie-contains? r key)))))))

(define (branching-bit-higher? mask1 mask2)
  (if (negative? (fxxor mask1 mask2))  ; signs differ
      (negative? mask1)
      (fx>? mask1 mask2)))

;; Merge two tries.  `combine' is used to merge duplicated mappings.
(define (trie-merge combine trie1 trie2)
  (letrec
    ((merge
      (lambda (s t)
        (cond ((not s) t)
              ((not t) s)
              ((leaf? s)
               (let*-leaf (((k v) s))
                 (trie-insert/combine t k v combine)))
              ((leaf? t)
               (let*-leaf (((k v) t))
                 (trie-insert/combine s k v (swap-args combine))))
              (else (merge-branches s t)))))
     (merge-branches
      (lambda (s t)
        (let*-branch (((p m s1 s2) s)
                      ((q n t1 t2) t))
          (cond ((and (fx=? m n) (fx=? p q))
                 ;; the prefixes match, so merge the subtries
                 (branch p m (merge s1 t1) (merge s2 t2)))
                ((and (branching-bit-higher? m n) (match-prefix? q p m))
                 ;; p is a prefix of q, so merge t with a subtrie of s.
                 (if (zero-bit? q m)
                     (branch p m (merge s1 t) s2)
                     (branch p m s1 (merge s2 t))))
                ((and (branching-bit-higher? n m) (match-prefix? p q n))
                 ;; q is a prefix of p, so merge s with a subtrie of t.
                 (if (zero-bit? p n)
                     (branch q n (merge s t1) t2)
                     (branch q n t1 (merge s t2))))
                (else    ; the prefixes disagree
                 (trie-join p m s q n t)))))))
    (merge trie1 trie2)))

;; Construct a branch only if the subtrees are non-empty.
(define (branch prefix mask trie1 trie2)
  (cond ((not trie1) trie2)
        ((not trie2) trie1)
        (else (branch prefix mask trie1 trie2))))

(define (trie-union s t)
  (trie-merge trie-insert s t))

(define (trie-partition pred trie with-key)
  (letrec
   ((part
     (lambda (t)
       (cond ((not t) (values #f #f))
             ((leaf? t)
              (if (if with-key
                      (pred (leaf-key t) (leaf-value t))
                      (pred (leaf-value t)))
                  (values t #f)
                  (values #f t)))
             (else
              (let-values (((p) (branch-prefix t))
                           ((m) (branch-branching-bit t))
                           ((il ol) (part (branch-left t)))
                           ((ir or) (part (branch-right t))))
                (values (branch p m il ir) (branch p m ol or))))))))
    (part trie)))

(define (trie-fold-left proc nil trie)
  (letrec
   ((cata
     (lambda (b t)
       (cond ((not t) b)
             ((leaf? t) (proc (leaf-value t) b))
             (else
              (cata (cata b (branch-left t)) (branch-right t)))))))
    (cata nil trie)))

(define (trie-fold-left/key proc nil trie)
  (letrec
   ((cata
     (lambda (b t)
       (cond ((not t) b)
             ((leaf? t) (proc (leaf-key t) (leaf-value t) b))
             (else
              (cata (cata b (branch-left t)) (branch-right t)))))))
    (cata nil trie)))

(define (trie-fold-right proc nil trie)
  (letrec
   ((cata
     (lambda (b t)
       (cond ((not t) b)
             ((leaf? t) (proc (leaf-value t) b))
             (else
              (cata (cata b (branch-right t)) (branch-left t)))))))
    (cata nil trie)))

(define (trie-fold-right/key proc nil trie)
  (letrec
   ((cata
     (lambda (b t)
       (cond ((not t) b)
             ((leaf? t) (proc (leaf-key t) (leaf-value t) b))
             (else
              (cata (cata b (branch-right t)) (branch-left t)))))))
    (cata nil trie)))

(define (trie-filter pred trie with-key)
  (and trie
       (if (leaf? trie)
           (and (if with-key
                    (pred (leaf-key trie) (leaf-value trie))
                    (pred (leaf-value trie)))
                trie)
           (branch (branch-prefix trie)
                   (branch-branching-bit trie)
                   (trie-filter pred (branch-left trie))
                   (trie-filter pred (branch-right trie))))))

(define (%trie-find-leftmost trie)
  (cond ((not trie) (nothing))
        ((leaf? trie) (just (leaf-key trie) (leaf-value trie)))
        (else (%trie-find-leftmost (branch-left trie)))))

;; Call success on the key and value of the leftmost leaf and use
;; the resulting Maybe to update the value.
(define (%trie-update-min/key trie success)
  (letrec
   ((traverse
     (lambda (t)
       (cond ((not t) #f)
             ((leaf? t)
              (let*-leaf (((k v) t))
                (maybe-ref (success k v)
                           (lambda () #f)
                           (lambda (v*) (leaf k v*)))))
             (else
              (let*-branch (((p m l r) t))
                (branch p m (traverse l) r)))))))
    (traverse trie)))

(define (%trie-find-rightmost trie)
  (cond ((not trie) (nothing))
        ((leaf? trie) (just (leaf-key trie) (leaf-value trie)))
        (else (%trie-find-rightmost (branch-right trie)))))

;; Call success on the key and value of the greatest-keyed leaf
;; and use the resulting Maybe to update the value.
(define (%trie-update-max/key trie success)
  (letrec
   ((traverse
     (lambda (t)
       (cond ((not t) #f)
             ((leaf? t)
              (let*-leaf (((k v) t))
                (maybe-ref (success k v)
                           (lambda () #f)
                           (lambda (v*) (leaf k v*)))))
             (else
              (let*-branch (((p m l r) t))
                (branch p m l (traverse r))))))))
    (traverse trie)))

;;;; Comparisons

(define (trie=? comp trie1 trie2)
  (let loop ((s trie1) (t trie2))
    (cond ((not (or s t)) #t)
          ((leaf? s)
           (and (leaf? t)
                (fx=? (leaf-key s) (leaf-key t))
                (=? comp (leaf-value s) (leaf-value t))))
          ((and (branch? s) (branch? t))
           (let*-branch (((p m l1 r1) s) ((q n l2 r2) t))
             (and (fx=? m n) (fx=? p q) (loop l1 l2) (loop r1 r2))))
          (else #f))))

;; Returns the symbol 'less' if trie1 is a proper subset of trie2,
;; 'equal' if they are the same, and 'greater' otherwise.  NB that
;; disjoint sets will compare as greater.
(define (trie-subset-compare comp trie1 trie2)
  (letrec
   ((compare
     (lambda (s t)
       (cond ((eqv? s t) 'equal)
             ((not s) 'less)
             ((not t) 'greater)  ; disjoint
             ((and (leaf? s) (leaf? t))
              (let*-leaf (((sk sv) s)) (((tk tv) t))
                (if (and (fx=? sk tk) (=? comp sv tv))
                    'equal
                    'greater)))
             ((leaf? s)             ; leaf / branch
              (let*-branch (((p m l r) t))
                (let ((k (leaf-key s)))
                  (if (match-prefix? k p m)
                      (case (compare s (if (zero-bit? k m) l r))
                        ((greater) 'greater)
                        (else 'less))))))
             ((leaf? t) 'greater)   ; branch / leaf
             (else (compare-branches s t)))))
    (compare-branches
     (lambda (s t)
       (let*-branch (((p m sl sr) s) ((q n tl tr) t))
         (cond ((branching-bit-higher? m n) 'greater)
               ((branching-bit-higher? n m)
                (if (match-prefix? p q n)
                    (let ((comp (if (zero-bit? p n)
                                    (compare s tl)
                                    (compare s tr))))
                      (if (eqv? comp 'greater) comp 'less))
                    'greater))
               ((fx=? p q)  ; same prefix, compare subtrees
                (let ((cl (compare sl tl)) (cr (compare sr tr)))
                  (cond ((or (eqv? cl 'greater) (eqv? cr 'greater))
                         'greater)
                        ((and (eqv? cl 'equal) (eqv? cr 'equal))
                         'equal)
                        (else 'less))))
               (else 'greater))))))  ; disjoint
    (compare trie1 trie2)))

(define (trie-proper-subset? comp trie1 trie2)
  (eqv? (trie-subset-compare comp trie1 trie2) 'less))

;; Two tries are disjoint if they have no keys in common.
(define (trie-disjoint? trie1 trie2)
  (letrec
   ((disjoint?
     (lambda (s t)
       (or (not s)
           (not t)
           (cond ((leaf? s)
                  (if (leaf? t)
                      (not (fx=? (leaf-key s) (leaf-key t)))
                      (not (trie-contains? t s))))
                 ((leaf? t) (not (trie-contains? s t)))
                 (else (branches-disjoint? s t))))))
    (branches-disjoint?
     (lambda (s t)
       (let*-branch (((p m sl sr) s) ((q n tl tr) t))
         (cond ((and (fx=? m n) (fx=? p q))
                (and (disjoint? sl tl) (disjoint? sr tr)))
               ((and (branching-bit-higher? m n) (match-prefix? q p m))
                (if (zero-bit? q m)
                    (disjoint? sl t)
                    (disjoint? sr t)))
               ((and (branching-bit-higher? n m) (match-prefix? p q n))
                (if (zero-bit? p n)
                    (disjoint? s tl)
                    (disjoint? s tr)))
               (else #t))))))      ; the prefixes disagree
    (disjoint? trie1 trie2)))

(define (trie-delete trie key)
  (letrec
   ((update
     (lambda (t)
       (cond ((not t) #f)
             ((leaf? t) (if (fx=? (leaf-key t) key) #f t))
             (else (update-branch t)))))
    (update-branch
     (lambda (t)
       (let*-branch (((p m l r) t))
         (if (match-prefix? key p m)
             (if (zero-bit? key m)
                 (branch p m (update l) r)
                 (branch p m l (update r)))
             t)))))  ; key doesn't occur in t
    (update trie)))

;; Identical to trie-insert, but delete key if it exists.
(define (trie-xor-insert trie key)
  (letrec
   ((ins
     (lambda (t)
       (cond ((not t) key)  ; new leaf
             ((integer? t)
              (if (fx=? t key) #f (trie-join key 0 key t 0 t)))
             (else
              (let*-branch (((p m l r) t))
                (if (match-prefix? key p m)
                    (if (zero-bit? key m)
                        (branch p m (ins l) r)
                        (branch p m l (ins r)))
                    (trie-join key 0 key p m t))))))))
    (ins trie)))

(define (trie-intersection trie1 trie2)
  (letrec
   ((intersect
     (lambda (s t)
       (cond ((or (not s) (not t)) #f)
             ((and (integer? s) (integer? t)) (and (fx=? s t) s))
             ((integer? s) (ins-int s t))
             ((integer? t) (ins-int t s))
             (else (intersect-branches s t)))))
    (ins-int
     (lambda (n t)
       (let lp ((t t))
         (cond ((and (integer? t) (fx=? n t)) n)
               ((branch? t)
                (let*-branch (((p m l r) t))
                  (and (match-prefix? n p m)
                       (if (zero-bit? n m) (lp l) (lp r)))))
               (else #f)))))
    (intersect-branches
     (lambda (s t)
       (let*-branch (((p m sl sr) s) ((q n tl tr) t))
         (cond ((branching-bit-higher? m n)
                (and (match-prefix? q p m)
                     (if (zero-bit? q m)
                         (intersect sl t)
                         (intersect sr t))))
               ((branching-bit-higher? n m)
                (and (match-prefix? p q n)
                     (if (zero-bit? p n)
                         (intersect s tl)
                         (intersect s tr))))
               ((fx=? p q)
                (branch p m (intersect sl tl) (intersect sr tr)))
               (else #f))))))
    (intersect trie1 trie2)))

(define (trie-difference trie1 trie2)
  (letrec
   ((difference
     (lambda (s t)
       (cond ((not s) #f)
             ((not t) s)
             ((integer? s) (diff-int s t))
             ((integer? t) (trie-delete s t))
             (else (branch-difference s t)))))
    (diff-int
     (lambda (n t)
       (cond ((not t) n)
             ((integer? t) (if (fx=? t n) #f n))
             (else
              (let*-branch (((p m l r) t))
                (if (match-prefix? n p m)
                    (if (zero-bit? n m)
                        (diff-int n l)
                        (diff-int n r))
                    n))))))
    (branch-difference
     (lambda (s t)
       (let*-branch (((p m sl sr) s) ((q n tl tr) t))
         (cond ((and (fx=? m n) (fx=? p q))
                (branch p m (difference sl tl) (difference sr tr)))
               ((and (branching-bit-higher? m n) (match-prefix? q p m))
                (if (zero-bit? q m)
                    (branch p m (difference sl t) sr)
                    (branch p m sl (difference sr t))))
               ((and (branching-bit-higher? n m) (match-prefix? p q n))
                (if (zero-bit? p n)
                    (difference s tl)
                    (difference s tr)))
               (else s))))))
    (difference trie1 trie2)))

;; Return a trie containing all the elements of `trie' which are
;; less than k, if `inclusive' is false, or less than or equal to
;; k if `inclusive' is true.
(define (subtrie< trie k inclusive)
  (letrec
    ((split
      (lambda (t)
        (cond ((not t) #f)
	      ((integer? t)
	       (cond ((fx<? t k) t)
		     ((and (fx=? t k) inclusive) t)
		     (else #f)))
              (else
               (let*-branch (((p m l r) t))
                 (if (match-prefix? k p m)
                     (if (zero-bit? k m)
                         (split l)
                         (trie-union l (split r)))
                     (and (fx<? p k) t))))))))
    (if (and (branch? trie) (fxnegative? (branch-branching-bit trie)))
        (if (fxnegative? k)
            (split (branch-right trie))
            (trie-union (split (branch-left trie)) (branch-right trie)))
        (split trie))))

;; Return a trie containing all the elements of `trie' which are
;; greater than k, if `inclusive' is false, or greater than or equal
;; to k if `inclusive' is true.
(define (subtrie> trie k inclusive)
  (letrec
   ((split
     (lambda (t)
       (cond ((not t) #f)
	     ((integer? t)
	      (cond ((fx>? t k) t)
		    ((and (fx=? t k) inclusive) t)
		    (else #f)))
	     (else
	      (let*-branch (((p m l r) t))
		(if (match-prefix? k p m)
		    (if (zero-bit? k m)
			(trie-union (split l) r)
			(split r))
		    (and (fx>? p k) t))))))))
    (if (and (branch? trie) (fxnegative? (branch-branching-bit trie)))
	(if (fxnegative? k)
	    (trie-union (split (branch-right trie)) (branch-left trie))
	    (split (branch-left trie)))
	(split trie))))

;; Return a trie containing all the elements of `trie' which are
;; greater than/greater than or equal to a and less than/less than
;; or equal to b, depending on the truth values of
;; low-/high-inclusive.
(define (subtrie-interval trie a b low-inclusive high-inclusive)
  (letrec
   ((interval
     (lambda (t)
       (cond ((not t) #f)
             ((integer? t) (and ((if low-inclusive fx>=? fx>?) t a)
                                ((if high-inclusive fx<=? fx<?) t b)
                                t))
             (else (branch-interval t)))))
    (branch-interval
     (lambda (t)
       (let*-branch (((p m l r) t))
         (if (match-prefix? a p m)
             (if (zero-bit? a m)
                 (if (match-prefix? b p m)
                     (if (zero-bit? b m)
                         (interval l)  ; all x < b is in l
                         (trie-union (subtrie> l a low-inclusive)
                                     (subtrie< r b high-inclusive)))
                     ;; everything or nothing is less than b
                     (and (fx<? b p)
                          (trie-union (subtrie> l a low-inclusive) r)))
                 (interval r)) ; all x > b is in r
             ;; everything or nothing is greater than a
             (and (fx>? p a) (subtrie< t b high-inclusive)))))))
    (if (and (branch? trie) (fxnegative? (branch-branching-bit trie)))
	(cond ((and (fxnegative? a) (fxnegative? b))
	       (interval (branch-right trie)))
	      ((and (fxpositive? a) (fxpositive? b))
	       (interval (branch-left trie)))
	      ;; (a, 0) U (0, b)
	      (else (trie-union (subtrie> (branch-right trie) a low-inclusive)
	                        (subtrie< (branch-left trie) b high-inclusive))))
	(interval trie))))

;; Search trie for key, and construct a new trie using the results of
;; failure and success.
(define (trie-search trie key failure success)
  (let lp ((t trie) (build values))
    (cond ((not t)
           (failure (lambda (value obj) (build (raw-leaf key value) obj))
                    (lambda (obj) (build #f obj))))
          ((leaf? t)
           (let*-leaf (((key* value) t))
             (if (fx=? key key*)
                 (success (lambda (new-key new-value obj)
                            (assume (fx=? key new-key)) ; may be changed
                            (build (raw-leaf key new-value) obj))
                          (lambda (obj) (build #f obj)))
                 (failure
                  (lambda (value obj)
                    (build (trie-join key 0 (raw-leaf key value) key* 0 t)
                           obj))
                  (lambda (obj) (build t obj))))))
          (else
           (let*-branch (((p m l r) t))
             (if (match-prefix? key p m)
                 (if (zero-bit? key m)
                     (lp l (lambda (l* obj)
                             (build (branch p m l* r) obj)))
                     (lp r (lambda (r* obj)
                             (build (branch p m l r*) obj))))
                 (failure (lambda (obj)
                            (build (trie-join kp 0 key-leaf p m t)
                                   obj))
                          (lambda (obj) (build t obj)))))))))
