(include "integer-map-chicken.scm")

(import (srfi 1)
        (srfi 128)
        (srfi 189)
        (integer-map))

(import (test))

(define-syntax λ
  (syntax-rules ()
    ((λ . rest) (lambda . rest))))

;;;; Utility

(define default-comp (make-default-comparator))

;;;; Test imappings

(define empty-imap (imapping))

(define char-imap
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
  (test #t (imapping=? default-comp char-imap char-imap))
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
  (test #t (imapping-contains? char-imap 0))
  (test #f (imapping-contains? char-imap 100))
  (test #t (imapping-contains? sparse-imap 4096))
  (test #f (imapping-contains? sparse-imap -4097))

  (test #t (imapping-empty? empty-imap))
  (test #f (imapping-empty? char-imap))
  (test #f (imapping-empty? mixed-imap))
  (test #f (imapping-empty? sparse-imap))

  (test #t (imapping-disjoint? empty-imap char-imap))
  (test #t (imapping-disjoint? (imapping 1 'a) (imapping 2 'b)))
  (test #f (imapping-disjoint? (imapping 1 'a) (imapping 1 'b)))
  )
