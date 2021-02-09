(include "integer-map-chicken.scm")

(import (srfi 1)
        (srfi 128)
        (srfi 189)
        (chicken base)
        (integer-map))

(import (test))

(define-syntax λ
  (syntax-rules ()
    ((λ . rest) (lambda . rest))))

;;;; Utility

(define default-comp (make-default-comparator))

(define (first x _) x)
(define (second _ y) y)

;;;; Test imappings

(define empty-imap (imapping))

(define letter-imap
  (let* ((cs "abcdefghijklmnopqrstuvwxyz")
         (len (string-length cs)))
    (imapping-unfold
     (λ (i) (= i len))
     (λ (i) (values i (string->symbol (string (string-ref cs i)))))
     (λ (i) (+ i 1))
     0)))

;; (-100 . -100), (-75 . -75), ..., (0 . 0), ..., (100 . 100)
(define mixed-seq
  (unfold (λ (i) (> i 100))
          (λ (i) (cons i i))
          (λ (i) (+ i 25))
          -100))

(define mixed-imap (alist->imapping mixed-seq))

;; From -65536 to 65536 in steps of 4096.  Key = value.
(define sparse-seq
  (unfold (λ (i) (> i 65536))
          (λ (i) (cons i i))
          (λ (i) (+ i 4096))
          -65536))

(define sparse-imap (alist->imapping sparse-seq))

;;; imapping=? and the alist conversions are used in many other tests,
;;; so we test these first.  These also test the basic imapping
;;; constructor.

(test-group "Equality"
  (test #t (imapping=? default-comp empty-imap (imapping)))
  (test #t (imapping=? default-comp (imapping 10 'a) (imapping 10 'a)))
  (test #f (imapping=? default-comp empty-imap (imapping 10 'a)))
  (test #t (imapping=? default-comp mixed-imap mixed-imap))
  (test #t (imapping=? default-comp letter-imap letter-imap))
  )

(test-group "Conversion"
  (test #t (null? (imapping->alist empty-imap)))
  (test '((10 . a)) (imapping->alist (imapping 10 'a)))
  (test mixed-seq (imapping->alist mixed-imap))
  (test sparse-seq (imapping->alist sparse-imap))
  )

(test-group "Constructors"
  (test '((1 . a) (2 . b) (3 . c))
        (imapping->alist (imapping 1 'a 2 'b 3 'c)))

  ;;; unfolds

  (test #t (null? (imapping->alist (imapping-unfold
                                    values
                                    (λ (b) (values 1 b))
                                    (λ (b) (not b))
                                    #t))))
  (test '((1 . #f)) (imapping->alist (imapping-unfold
                                      values
                                      (λ (b) (values 1 b))
                                      (λ (b) (not b))
                                      #f)))
  (test '((-3 . -3) (-2 . -2) (-1 . -1))
        (imapping->alist (imapping-unfold
                          (λ (i) (< i -3))
                          (λ (i) (values i i))
                          (λ (i) (- i 1))
                          -1)))

  (test #t (null? (imapping->alist (imapping-unfold-maybe
                                    (λ (b) (if b (nothing) (just 1 b (not b))))
                                    #t))))
  (test '((1 . #f))
        (imapping->alist (imapping-unfold-maybe
                          (λ (b) (if b (nothing) (just 1 b (not b))))
                          #f)))
  (test '((-3 . -3) (-2 . -2) (-1 . -1))
        (imapping->alist (imapping-unfold-maybe
                          (λ (i) (if (< i -3) (nothing) (just i i (- i 1))))
                          -1)))

  ;;; alist->imapping

  (test #t (null? (imapping->alist (alist->imapping '()))))
  (test mixed-seq (imapping->alist (alist->imapping mixed-seq)))
  (test sparse-seq (imapping->alist (alist->imapping sparse-seq)))
  )

(test-group "Predicates"
  (test #f (imapping-contains? empty-imap 1))
  (test #t (imapping-contains? letter-imap 0))
  (test #f (imapping-contains? letter-imap 100))
  (test #t (imapping-contains? sparse-imap 4096))
  (test #f (imapping-contains? sparse-imap -4097))

  (test #t (imapping-empty? empty-imap))
  (test #f (imapping-empty? letter-imap))
  (test #f (imapping-empty? mixed-imap))
  (test #f (imapping-empty? sparse-imap))

  (test #t (imapping-disjoint? empty-imap letter-imap))
  (test #t (imapping-disjoint? (imapping 1 'a) (imapping 2 'b)))
  (test #f (imapping-disjoint? (imapping 1 'a) (imapping 1 'b)))
  )

(test-group "Accessors"
  ;;; lookups

  (test #t (nothing? (imapping-lookup empty-imap 1)))
  (test 'a (maybe-ref/default (imapping-lookup letter-imap 0) #f))
  (test -50 (maybe-ref/default (imapping-lookup mixed-imap -50) #f))
  (test #t (nothing? (imapping-lookup mixed-imap -51)))
  (test 36864 (maybe-ref/default (imapping-lookup sparse-imap 36864) #f))
  (test #t (nothing? (imapping-lookup sparse-imap 36800)))

  (test 'z (imapping-lookup/default empty-imap 1 'z))
  (test 'a (imapping-lookup/default letter-imap 0 #f))
  (test -50 (imapping-lookup/default mixed-imap -50 #f))
  (test 'z (imapping-lookup/default mixed-imap -51 'z))
  (test 36864 (imapping-lookup/default sparse-imap 36864 #f))
  (test 'z (imapping-lookup/default sparse-imap 36800 'z))

  ;;; min/max

  (test #t (nothing? (imapping-min empty-imap)))
  (test '(0 a) (maybe-ref (imapping-min letter-imap) (λ () #f) list))
  (test '(-100 -100) (maybe-ref (imapping-min mixed-imap) (λ () #f) list))
  (test '(-65536 -65536) (maybe-ref (imapping-min sparse-imap) (λ () #f) list))

  (test #t (nothing? (imapping-max empty-imap)))
  (test '(25 z) (maybe-ref (imapping-max letter-imap) (λ () #f) list))
  (test '(100 100) (maybe-ref (imapping-max mixed-imap) (λ () #f) list))
  (test '(65536 65536) (maybe-ref (imapping-max sparse-imap) (λ () #f) list))
  )

(test-group "Updaters"
  ;;; adjoins

  (test #t (imapping=? default-comp
                       (imapping 0 'a)
                       (imapping-adjoin empty-imap 0 'a)))
  (test #t (imapping-contains? (imapping-adjoin mixed-imap 200 #t) 200))
  (test #t (imapping-contains? (imapping-adjoin sparse-imap -200 #t) -200))
  (test #t (imapping=? default-comp
                       (imapping 0 'a 1 'b 2 'c)
                       (imapping-adjoin empty-imap 0 'a 1 'b 2 'c)))

  (test 'U (imapping-lookup/default
            (imapping-adjoin/combine letter-imap first 20 'U)
            20
            #f))
  (test 'u (imapping-lookup/default
            (imapping-adjoin/combine letter-imap second 20 'U)
            20
            #f))
  (test #t
        (imapping=? default-comp
                    (imapping 0 'a 1 'b 2 'c)
                    (imapping-adjoin/combine empty-imap first 0 'a 1 'b 2 'c)))

  ;;; adjusts

  (test 'U (imapping-lookup/default
            (imapping-adjust letter-imap 20 (constantly 'U))
            20
            #f))
  (test 'x (imapping-lookup/default
            (imapping-adjust sparse-imap 8192 (constantly 'x))
            8192
            #f))
  (test #t (imapping-empty? (imapping-adjust empty-imap 1 (constantly 'x))))

  (test '(20 u) (imapping-lookup/default
                 (imapping-adjust/key letter-imap 20 list)
                 20
                 #f))
  (test 16384 (imapping-lookup/default
               (imapping-adjust/key sparse-imap 8192 (λ (k v) (+ k v)))
               8192
               #f))
  (test #t (imapping-empty? (imapping-adjust/key empty-imap 1 list)))

  ;;; delete & delete-all

  (test #f (imapping-contains? (imapping-delete letter-imap 10) 10))
  (test #f (imapping-contains? (imapping-delete mixed-imap 50) 50))
  (test #t (imapping=? default-comp mixed-imap (imapping-delete mixed-imap 1)))
  (let* ((ks '(4096 8192 16384))
         (sm (apply imapping-delete sparse-imap ks)))
    (test #f (any (λ (k) (imapping-contains? sm k)) ks)))

  (test #f (imapping-contains? (imapping-delete-all letter-imap '(10)) 10))
  (test #f (imapping-contains? (imapping-delete-all mixed-imap '(50)) 50))
  (test #t (imapping=? default-comp
                       mixed-imap
                       (imapping-delete-all mixed-imap '(1))))
  (let* ((ks '(4096 8192 16384))
         (sm (imapping-delete-all sparse-imap ks)))
    (test #f (any (λ (k) (imapping-contains? sm k)) ks)))

  ;;; update

  (test #t (imapping=? default-comp
                 (imapping 0 'b)
                 (imapping-update (imapping 0 'a) 0 (constantly (just 'b)))))
  (test 'U (imapping-lookup/default
            (imapping-update letter-imap 20 (constantly (just 'U)))
            20
            #f))
  (test #f (imapping-contains?
            (imapping-update letter-imap 20 (constantly (nothing)))
            20))
  (test #f (imapping-contains?
            (imapping-update sparse-imap -8192 (constantly (nothing)))
            -8192))

  (test #t (imapping=?
            default-comp
            (imapping 0 '(0 a))
            (imapping-update/key (imapping 0 'a)
                                 0
                                 (λ (k v) (just (list k v))))))
  (test 'U (imapping-lookup/default
            (imapping-update/key letter-imap 20 (constantly (just 'U)))
            20
            #f))
  (test #f (imapping-contains?
            (imapping-update/key letter-imap 20 (constantly (nothing)))
            20))
  (test #f (imapping-contains?
            (imapping-update/key sparse-imap -8192 (constantly (nothing)))
            -8192))

  )
