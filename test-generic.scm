;;;; Utility

(define default-comp (make-default-comparator))

(define (constantly x) (lambda _ x))

(define (first x _) x)
(define (second _ y) y)
(define (nth n) (lambda args (list-ref args n)))

(define (square x) (* x x))

(define (list->dup-alist xs)
  (map cons xs xs))

;; From SRFI 210, reduced.
(define-syntax value/mv
  (syntax-rules ()
    ((value/mv i producer)
     (let-values ((vs producer))
       (list-ref vs i)))))

;;;; Test imappings

(define empty-imap (imapping))

(define letter-imap
  (let* ((cs "abcdefghijklmnopqrstuvwxyz")
         (len (string-length cs)))
    (imapping-unfold
     (lambda (i) (= i len))
     (lambda (i) (values i (string->symbol (string (string-ref cs i)))))
     (lambda (i) (+ i 1))
     0)))

;; (-100 . -100), (-75 . -75), ..., (0 . 0), ..., (100 . 100)
(define mixed-seq
  (unfold (lambda (i) (> i 100))
          (lambda (i) (cons i i))
          (lambda (i) (+ i 25))
          -100))

(define mixed-imap (alist->imapping mixed-seq))

;; From -65536 to 65536 in steps of 4096.  Key = value.
(define sparse-seq
  (unfold (lambda (i) (> i 65536))
          (lambda (i) (cons i i))
          (lambda (i) (+ i 4096))
          -65536))

(define sparse-imap (alist->imapping sparse-seq))

(define all-test-imaps
  (list empty-imap mixed-imap letter-imap sparse-imap))

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
                                    (lambda (b) (values 1 b))
                                    (lambda (b) (not b))
                                    #t))))
  (test '((1 . #f)) (imapping->alist (imapping-unfold
                                      values
                                      (lambda (b) (values 1 b))
                                      (lambda (b) (not b))
                                      #f)))
  (test '((-3 . -3) (-2 . -2) (-1 . -1))
        (imapping->alist (imapping-unfold
                          (lambda (i) (< i -3))
                          (lambda (i) (values i i))
                          (lambda (i) (- i 1))
                          -1)))

  (test #t (null? (imapping->alist (imapping-unfold-maybe
                                    (lambda (b)
                                      (if b (nothing) (just 1 b (not b))))
                                    #t))))
  (test '((1 . #f))
        (imapping->alist (imapping-unfold-maybe
                          (lambda (b) (if b (nothing) (just 1 b (not b))))
                          #f)))
  (test '((-3 . -3) (-2 . -2) (-1 . -1))
        (imapping->alist (imapping-unfold-maybe
                          (lambda (i)
                            (if (< i -3) (nothing) (just i i (- i 1))))
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

  (test #f (imapping-lookup empty-imap 1))
  (test 'a (imapping-lookup letter-imap 0))
  (test -50 (imapping-lookup mixed-imap -50))
  (test #f (imapping-lookup mixed-imap -51))
  (test 36864 (imapping-lookup sparse-imap 36864))
  (test #f (imapping-lookup sparse-imap 36800))

  (test 'z (imapping-lookup/default empty-imap 1 'z))
  (test 'a (imapping-lookup/default letter-imap 0 #f))
  (test -50 (imapping-lookup/default mixed-imap -50 #f))
  (test 'z (imapping-lookup/default mixed-imap -51 'z))
  (test 36864 (imapping-lookup/default sparse-imap 36864 #f))
  (test 'z (imapping-lookup/default sparse-imap 36800 'z))

  ;;; min/max

  (test #t (nothing? (imapping-min empty-imap)))
  (test '(0 a) (maybe-ref (imapping-min letter-imap) (lambda () #f) list))
  (test '(-100 -100) (maybe-ref (imapping-min mixed-imap) (lambda () #f) list))
  (test '(-65536 -65536) (maybe-ref (imapping-min sparse-imap)
                                    (lambda () #f)
                                    list))

  (test #t (nothing? (imapping-max empty-imap)))
  (test '(25 z) (maybe-ref (imapping-max letter-imap) (lambda () #f) list))
  (test '(100 100) (maybe-ref (imapping-max mixed-imap) (lambda () #f) list))
  (test '(65536 65536) (maybe-ref (imapping-max sparse-imap)
                                  (lambda () #f)
                                  list))
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
               (imapping-adjust/key sparse-imap 8192 (lambda (k v) (+ k v)))
               8192
               #f))
  (test #t (imapping-empty? (imapping-adjust/key empty-imap 1 list)))

  ;;; delete & delete-all

  (test #f (imapping-contains? (imapping-delete letter-imap 10) 10))
  (test #f (imapping-contains? (imapping-delete mixed-imap 50) 50))
  (test #t (imapping=? default-comp mixed-imap (imapping-delete mixed-imap 1)))
  (let* ((ks '(4096 8192 16384))
         (sm (apply imapping-delete sparse-imap ks)))
    (test #f (any (lambda (k) (imapping-contains? sm k)) ks)))

  (test #f (imapping-contains? (imapping-delete-all letter-imap '(10)) 10))
  (test #f (imapping-contains? (imapping-delete-all mixed-imap '(50)) 50))
  (test #t (imapping=? default-comp
                       mixed-imap
                       (imapping-delete-all mixed-imap '(1))))
  (let* ((ks '(4096 8192 16384))
         (sm (imapping-delete-all sparse-imap ks)))
    (test #f (any (lambda (k) (imapping-contains? sm k)) ks)))

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
                                 (lambda (k v) (just (list k v))))))
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

  ;;; alter

  (test #t (imapping=? default-comp
                       (imapping 0 'a)
                       (imapping-alter (imapping 0 'a)
                                       1
                                       (constantly (nothing)))))
  (test #t (imapping=? default-comp
                       (imapping 0 'a 1 'b)
                       (imapping-alter (imapping 0 'a)
                                       1
                                       (constantly (just 'b)))))
  (test 101 (imapping-lookup/default
             (imapping-alter mixed-imap
                             101
                             (constantly (just 101)))
             101
             #f))
  (test 101 (imapping-lookup/default
             (imapping-alter mixed-imap
                             100
                             (lambda (m) (maybe-map (lambda (n) (+ n 1)) m)))
             100
             #f))
  (test 'z (imapping-lookup/default
            (imapping-alter mixed-imap
                            100
                            (constantly (nothing)))
            100
            'z))
  (test -16383 (imapping-lookup/default
                (imapping-alter sparse-imap
                                -16384
                                (lambda (m)
                                  (maybe-map (lambda (n) (+ n 1)) m)))
                -16384
                #f))
  (test 'z (imapping-lookup/default
            (imapping-alter sparse-imap
                            -16384
                            (constantly (nothing)))
            -16384
            'z))

  ;;; delete-min/-max

  (test #t (imapping=? default-comp
                       empty-imap
                       (imapping-delete-min (imapping 0 'a))))
  (test #f (imapping-contains? (imapping-delete-min letter-imap) 0))
  (test #f (imapping-contains? (imapping-delete-min sparse-imap) -65536))

  (test #t (imapping=? default-comp
                       empty-imap
                       (imapping-delete-max (imapping 0 'a))))
  (test #f (imapping-contains? (imapping-delete-max letter-imap) 25))
  (test #f (imapping-contains? (imapping-delete-max sparse-imap) 65536))

  ;;; min updaters

  (test 'A (imapping-lookup/default
            (imapping-update-min letter-imap (constantly (just 'A)))
            0
            #f))
  (test #f (imapping-contains?
            (imapping-update-min letter-imap (constantly (nothing)))
            0))
  (test -65535 (imapping-lookup/default
                (imapping-update-min sparse-imap (lambda (v) (just (+ v 1))))
                -65536
                #f))

  (test -200 (imapping-lookup/default
              (imapping-update-min/key mixed-imap
                                       (lambda (k v) (just (+ k v))))
              -100
              #f))
  (test '(0 a)
        (imapping-lookup/default
         (imapping-update-min/key letter-imap (lambda (k v) (just (list k v))))
         0
         #f))

  ;;; max updaters

  (test 'Z (imapping-lookup/default
            (imapping-update-max letter-imap (constantly (just 'Z)))
            25
            #f))
  (test #f (imapping-contains?
            (imapping-update-max letter-imap (constantly (nothing)))
            25))
  (test 65537 (imapping-lookup/default
                (imapping-update-max sparse-imap (lambda (v) (just (+ v 1))))
                65536
                #f))

  (test 200 (imapping-lookup/default
             (imapping-update-max/key mixed-imap
                                      (lambda (k v) (just (+ k v))))
             100
             #f))
  (test '(25 z)
        (imapping-lookup/default
         (imapping-update-max/key letter-imap (lambda (k v) (just (list k v))))
         25
         #f))
  )

(test-group "Whole imappings"
  (test 0 (imapping-size empty-imap))
  (test 26 (imapping-size letter-imap))

  (test 0 (imapping-count even? empty-imap))
  (test 26 (imapping-count symbol? letter-imap))
  (let ((ss '(f r o b)))
    (test (length ss) (imapping-count (lambda (s) (memv s ss)) letter-imap))
    (test (- (imapping-size letter-imap) (length ss))
          (imapping-count (lambda (s) (not (memv s ss))) letter-imap)))
  (test 4 (imapping-count positive? mixed-imap))

  (test 2 (imapping-count/key (lambda (k v) (and (even? k) (positive? v)))
                              mixed-imap))

  ;;; any?/every?

  (test #f (imapping-any? even? empty-imap))
  (test #t (imapping-any? positive? mixed-imap))
  (test #f (imapping-any? odd? sparse-imap))
  (test #t (imapping-any? negative? sparse-imap))

  (test #t (imapping-every? even? empty-imap))
  (test #f (imapping-every? positive? mixed-imap))
  (test #t (imapping-every? even? sparse-imap))
  (test #f (imapping-every? negative? sparse-imap))
  )

(test-group "Iterators"
  ;;; map

  (test #t (imapping=? default-comp
                       empty-imap
                       (imapping-map (constantly #t) empty-imap)))
  (test #t (imapping=? default-comp
                       mixed-imap
                       (imapping-map values mixed-imap)))
  (test #t (imapping=? default-comp
                       (imapping 0 "" 1 "a" 2 "aa")
                       (imapping-map (lambda (m) (make-string m #\a))
                                     (imapping 0 0 1 1 2 2))))
  (test #f (imapping-any? negative? (imapping-map abs sparse-imap)))

  (test #t (imapping=? default-comp
                       empty-imap
                       (imapping-map/key (constantly #t) empty-imap)))
  (test #t (imapping=? default-comp
                       mixed-imap
                       (imapping-map/key (nth 1) mixed-imap)))
  (test #t (imapping=? default-comp
                       (imapping 0 "" 1 "b" 2 "cc")
                       (imapping-map/key make-string
                                         (imapping 0 #\a 1 #\b 2 #\c))))

  ;;; for-each

  (test 26
        (let ((size 0))
          (imapping-for-each (lambda (_) (set! size (+ size 1))) letter-imap)
          size))
  (test '(c b a)
        (let ((xs '()))
          (imapping-for-each (lambda (x) (set! xs (cons x xs)))
                             (imapping 0 'a 1 'b 2 'c))
          xs))

  (test '((2 . c) (1 . b) (0 . a))
        (let ((xs '()))
          (imapping-for-each/key (lambda (k x) (set! xs (cons (cons k x) xs)))
                                 (imapping 0 'a 1 'b 2 'c))
          xs))

  ;;; fold-left

  (test 'z (imapping-fold-left (nth 1) 'z empty-imap))
  (test (reverse '(a b c d e f g h i j k l m n o p q r s t u v w x y z))
        (imapping-fold-left cons '() letter-imap))
  (test (reverse (iota 9 -100 25)) (imapping-fold-left cons '() mixed-imap))
  (test (fold + 0 (iota 9 -100 25)) (imapping-fold-left + 0 mixed-imap))

  (test (reverse '((0 . "") (1 . "b") (2 . "cc")))
        (imapping-fold-left/key (lambda (k c as)
                                  (cons (cons k (make-string k c)) as))
                                '()
                                (imapping 0 #\a 1 #\b 2 #\c)))

  ;;; fold-right

  (test 'z (imapping-fold-right (nth 1) 'z empty-imap))
  (test '(a b c d e f g h i j k l m n o p q r s t u v w x y z)
        (imapping-fold-right cons '() letter-imap))
  (test (iota 9 -100 25) (imapping-fold-right cons '() mixed-imap))
  (test (fold + 0 (iota 9 -100 25)) (imapping-fold-right + 0 mixed-imap))

  (test '((0 . "") (1 . "b") (2 . "cc"))
        (imapping-fold-right/key (lambda (k c as)
                                  (cons (cons k (make-string k c)) as))
                                 '()
                                 (imapping 0 #\a 1 #\b 2 #\c)))

  ;;; map->list

  (test #t (null? (imapping-map->list (constantly #t) empty-imap)))
  (test '(a b c d e f g h i j k l m n o p q r s t u v w x y z)
        (imapping-map->list values letter-imap))
  (test (map square (iota 9 -100 25))
        (imapping-map->list square mixed-imap))
  (test '("" "a" "aa")
        (imapping-map->list (lambda (n) (make-string n #\a))
                            (imapping 0 0 1 1 2 2)))

  (test (iota 26) (imapping-map/key->list (nth 0) letter-imap))
  (test '((0 . "") (1 . "b") (2 . "cc"))
        (imapping-map/key->list (lambda (k c) (cons k (make-string k c)))
                                (imapping 0 #\a 1 #\b 2 #\c)))

  ;;; filter

  (test #t
        (every values
               (map (lambda (m)
                      (imapping=? default-comp
                                  m
                                  (imapping-filter (constantly #t) m)))
                    (list empty-imap letter-imap mixed-imap sparse-imap))))
  (test #t
        (every imapping-empty?
               (map (lambda (m) (imapping-filter (constantly #f) m))
                    (list empty-imap letter-imap mixed-imap sparse-imap))))
  (test #t (imapping=? default-comp
                       (imapping 25 25 50 50 75 75 100 100)
                       (imapping-filter positive? mixed-imap)))
  (test #t (imapping=? default-comp
                       (imapping 22 'w)
                       (imapping-filter (lambda (s) (eqv? s 'w)) letter-imap)))

  (test #t
        (every values
               (map (lambda (m)
                      (imapping=? default-comp
                                  m
                                  (imapping-filter/key (constantly #t) m)))
                    (list empty-imap letter-imap mixed-imap sparse-imap))))
  (test #t
        (every imapping-empty?
               (map (lambda (m) (imapping-filter/key (constantly #f) m))
                    (list empty-imap letter-imap mixed-imap sparse-imap))))
  (test #t (imapping=? default-comp
                       (imapping 25 25 75 75)
                       (imapping-filter/key (lambda (k v)
                                              (and (odd? k) (positive? v)))
                                            mixed-imap)))

  ;;; remove

  (test #t
        (every values
               (map (lambda (m) (imapping=? default-comp
                                       m
                                       (imapping-remove (constantly #f) m)))
                    (list empty-imap letter-imap mixed-imap sparse-imap))))
  (test #t
        (every imapping-empty?
               (map (lambda (m) (imapping-remove (constantly #t) m))
                    (list empty-imap letter-imap mixed-imap sparse-imap))))
  (test #t (imapping=? default-comp
                       (imapping 0 0 25 25 50 50 75 75 100 100)
                       (imapping-remove negative? mixed-imap)))
  (test #t (imapping=? default-comp
                 (imapping 22 'w)
                 (imapping-remove (lambda (s) (not (eqv? s 'w))) letter-imap)))

  (test #t
        (every (lambda (m)
                 (imapping=? default-comp
                             m
                             (imapping-remove/key (constantly #f) m)))
               all-test-imaps))
  (test #t
        (every imapping-empty?
               (map (lambda (m) (imapping-remove/key (constantly #t) m))
                    (list empty-imap letter-imap mixed-imap sparse-imap))))
  (test #t (imapping=? default-comp
                       (imapping -100 -100 -50 -50 0 0)
                       (imapping-remove/key (lambda (k v)
                                              (or (odd? k) (positive? v)))
                                            mixed-imap)))

  ;;; partition

  (test #t
        (every (lambda (m)
                 (imapping=?
                  default-comp
                  m
                  (value/mv 0 (imapping-partition (constantly #t) m))))
               all-test-imaps))
  (test (call-with-values (lambda () (partition even? (map car mixed-seq)))
                          list)
        (let-values (((em om) (imapping-partition even? mixed-imap)))
          (list (imapping-values em) (imapping-values om))))
  (test #t
        (let-values (((zm not-zm) (imapping-partition (lambda (s) (eqv? s 'z))
                                                      letter-imap)))
          (and (imapping=? default-comp zm (imapping 25 'z))
               (imapping=? default-comp
                           not-zm
                           (imapping-delete letter-imap 25)))))

  (test (unfold (lambda (i) (= i 26))
                (lambda (i)
                  (string->symbol (string (integer->char (+ i #x61)))))
                (lambda (i) (+ i 2))
                0)
        (let-values (((em _) (imapping-partition/key (lambda (k _) (even? k))
                                                     letter-imap)))
          (imapping-values em)))
  )

(test-group "Comparison"
  (let ((subimap (imapping-filter even? mixed-imap)))
    (test #t (imapping<? default-comp (imapping) mixed-imap))
    (test #t (imapping<? default-comp subimap mixed-imap))
    (test #f (imapping<? default-comp mixed-imap subimap))
    (test #f (imapping<? default-comp mixed-imap mixed-imap))

    (test #t (imapping>? default-comp mixed-imap (imapping)))
    (test #f (imapping>? default-comp subimap mixed-imap))
    (test #t (imapping>? default-comp mixed-imap subimap))
    (test #f (imapping>? default-comp mixed-imap mixed-imap))

    (test #t (imapping<=? default-comp (imapping) mixed-imap))
    (test #t (imapping<=? default-comp subimap mixed-imap))
    (test #f (imapping<=? default-comp mixed-imap subimap))
    (test #t (imapping<=? default-comp mixed-imap mixed-imap))

    (test #t (imapping>=? default-comp mixed-imap (imapping)))
    (test #f (imapping>=? default-comp subimap mixed-imap))
    (test #t (imapping>=? default-comp mixed-imap subimap))
    (test #t (imapping>=? default-comp mixed-imap mixed-imap))

    ;; Variadic comparisons.
    (let ((subimap1 (imapping-filter positive? subimap)))
      (test #t (imapping<? default-comp subimap1 subimap mixed-imap))
      (test #f (imapping<? default-comp subimap1 empty-imap mixed-imap))

      (test #t (imapping>? default-comp mixed-imap subimap subimap1))
      (test #f (imapping>? default-comp mixed-imap empty-imap subimap1))

      (test #t (imapping<=? default-comp subimap1 subimap subimap mixed-imap))
      (test #f (imapping<=? default-comp subimap1 empty-imap mixed-imap))

      (test #t (imapping>=? default-comp mixed-imap subimap subimap subimap1))
      (test #f (imapping>=? default-comp mixed-imap empty-imap subimap1))
      ))
  )

(test-group "Set theory"
  (let ((imap1 (imapping -5 'a -2 'b 1 'c))
        (imap2 (imapping -2 'b 3 'd 5 'e))
        (imap3 (imapping 3 'd 5 'g 7 'f)))  ; assoc for 5 differs from imap2
    (test #t (imapping=? default-comp
                         sparse-imap
                         (imapping-union sparse-imap empty-imap)))
    (test #t (imapping=? default-comp
                         (imapping -5 'a -2 'b 1 'c 3 'd 5 'e)
                         (imapping-union imap1 imap2)))
    (test #t (imapping=? default-comp
                         (imapping -2 'b 3 'd 5 'e 7 'f)
                         (imapping-union imap2 imap3)))
    (test #t (imapping=? default-comp
                         (imapping -5 'a -2 'b 1 'c 3 'd 5 'e 7 'f)
                         (imapping-union imap1 imap2 imap3)))

    (test #t (imapping-empty? (imapping-intersection sparse-imap empty-imap)))
    (test #t (imapping=? default-comp
                         (imapping -2 'b)
                         (imapping-intersection imap1 imap2)))
    (test #t (imapping=? default-comp
                         (imapping 3 'd 5 'e)
                         (imapping-intersection imap2 imap3)))
    (test #t (imapping=? default-comp
                         (imapping -2 'b)
                         (imapping-intersection imap1 imap2 (imapping -2 'b))))

    (test #t (imapping=? default-comp
                         sparse-imap
                         (imapping-difference sparse-imap empty-imap)))
    (test #t (imapping=? default-comp
                         (imapping -5 'a 1 'c)
                         (imapping-difference imap1 imap2)))
    (test #t (imapping=? default-comp
                         (imapping -2 'b)
                         (imapping-difference imap2 imap3)))
    (test #t (imapping=? default-comp
                         (imapping -5 'a 1 'c)
                         (imapping-difference imap1 imap2 imap3)))

    (test #t (imapping=? default-comp
                         sparse-imap
                         (imapping-xor sparse-imap empty-imap)))
    (test #t (imapping=? default-comp
                         (imapping -5 'a 1 'c 3 'd 5 'e)
                         (imapping-xor imap1 imap2)))
    (test #t (imapping=? default-comp
                         (imapping -2 'b 7 'f)
                         (imapping-xor imap2 imap3)))
    ))

(test-group "Intervals"
  (test (list->dup-alist '(-25 0 25))
        (imapping->alist
         (imapping-open-interval mixed-imap -50 50)))
  (test '((6 . g) (7 . h) (8 . i) (9 . j))
        (imapping->alist
         (imapping-open-interval letter-imap 5 10)))
  (test (list->dup-alist '(-8192 -4096 0 4096 8192))
        (imapping->alist
         (imapping-open-interval sparse-imap -12288 12288)))

  (test (list->dup-alist '(-50 -25 0 25 50))
        (imapping->alist
         (imapping-closed-interval mixed-imap -50 50)))
  (test '((5 . f) (6 . g) (7 . h) (8 . i) (9 . j) (10 . k))
        (imapping->alist
         (imapping-closed-interval letter-imap 5 10)))
  (test (list->dup-alist '(-12288 -8192 -4096 0 4096 8192 12288))
        (imapping->alist
         (imapping-closed-interval sparse-imap -12288 12288)))

  (test (list->dup-alist '(-25 0 25 50))
        (imapping->alist
         (imapping-open-closed-interval mixed-imap -50 50)))
  (test '((6 . g) (7 . h) (8 . i) (9 . j) (10 . k))
        (imapping->alist
         (imapping-open-closed-interval letter-imap 5 10)))
  (test (list->dup-alist '(-8192 -4096 0 4096 8192 12288))
        (imapping->alist
         (imapping-open-closed-interval sparse-imap -12288 12288)))

  (test (list->dup-alist '(-50 -25 0 25))
        (imapping->alist
         (imapping-closed-open-interval mixed-imap -50 50)))
  (test '((5 . f) (6 . g) (7 . h) (8 . i) (9 . j))
        (imapping->alist
         (imapping-closed-open-interval letter-imap 5 10)))
  (test (list->dup-alist '(-12288 -8192 -4096 0 4096 8192))
        (imapping->alist
         (imapping-closed-open-interval sparse-imap -12288 12288)))
  )

(test-group "Submappings"
  (test '((100 . 100)) (imapping->alist (isubmapping= mixed-imap 100)))
  (test '((7 . h)) (imapping->alist (isubmapping= letter-imap 7)))
  (test '((16384 . 16384)) (imapping->alist (isubmapping= sparse-imap 16384)))
  (test #t (imapping-empty? (isubmapping= sparse-imap 1)))

  (test (list->dup-alist '(-100 -75 -50 -25))
        (imapping->alist (isubmapping< mixed-imap 0)))
  (test '((0 . a) (1 . b) (2 . c))
        (imapping->alist (isubmapping< letter-imap 3)))
  (test (list->dup-alist '(-65536 -61440 -57344))
        (imapping->alist (isubmapping< sparse-imap -53248)))

  (test (list->dup-alist '(25 50 75 100))
        (imapping->alist (isubmapping> mixed-imap 0)))
  (test '((23 . x) (24 . y) (25 . z))
        (imapping->alist (isubmapping> letter-imap 22)))
  (test (list->dup-alist '(57344 61440 65536))
        (imapping->alist (isubmapping> sparse-imap 53248)))

  (test (list->dup-alist '(-100 -75 -50 -25 0))
        (imapping->alist (isubmapping<= mixed-imap 0)))
  (test '((0 . a) (1 . b) (2 . c) (3 . d))
        (imapping->alist (isubmapping<= letter-imap 3)))
  (test (list->dup-alist '(-65536 -61440 -57344 -53248))
        (imapping->alist (isubmapping<= sparse-imap -53248)))

  (test (list->dup-alist '(0 25 50 75 100))
        (imapping->alist (isubmapping>= mixed-imap 0)))
  (test '((22 . w) (23 . x) (24 . y) (25 . z))
        (imapping->alist (isubmapping>= letter-imap 22)))
  (test (list->dup-alist '(53248 57344 61440 65536))
        (imapping->alist (isubmapping>= sparse-imap 53248)))
  )
