;
; miscellaneous utilities and demos
;

(define (caar x) (car (car x)))
(define (cadr x) (car (cdr x)))
(define (cdar x) (cdr (car x)))
(define (cddr x) (cdr (cdr x)))
(define (caaar x) (car (car (car x))))
(define (caadr x) (car (car (cdr x))))
(define (cadar x) (car (cdr (car x))))
(define (caddr x) (car (cdr (cdr x))))
(define (cdaar x) (cdr (car (car x))))
(define (cdadr x) (cdr (car (cdr x))))
(define (cddar x) (cdr (cdr (car x))))
(define (cdddr x) (cdr (cdr (cdr x))))
(define (caaaar x) (car (car (car (car x)))))
(define (caaadr x) (car (car (car (cdr x)))))
(define (caadar x) (car (car (cdr (car x)))))
(define (caaddr x) (car (car (cdr (cdr x)))))
(define (cadaar x) (car (cdr (car (car x)))))
(define (cadadr x) (car (cdr (car (cdr x)))))
(define (caddar x) (car (cdr (cdr (car x)))))
(define (cadddr x) (car (cdr (cdr (cdr x)))))
(define (cdaaar x) (cdr (car (car (car x)))))
(define (cdaadr x) (cdr (car (car (cdr x)))))
(define (cdadar x) (cdr (car (cdr (car x)))))
(define (cdaddr x) (cdr (car (cdr (cdr x)))))
(define (cddaar x) (cdr (cdr (car (car x)))))
(define (cddadr x) (cdr (cdr (car (cdr x)))))
(define (cdddar x) (cdr (cdr (cdr (car x)))))
(define (cddddr x) (cdr (cdr (cdr (cdr x)))))

(define (caaaaar x) (car (car (car (car (car x))))))
(define (caaaadr x) (car (car (car (car (cdr x))))))
(define (caaadar x) (car (car (car (cdr (car x))))))
(define (caaaddr x) (car (car (car (cdr (cdr x))))))
(define (caadaar x) (car (car (cdr (car (car x))))))
(define (caadadr x) (car (car (cdr (car (cdr x))))))
(define (caaddar x) (car (car (cdr (cdr (car x))))))
(define (caadddr x) (car (car (cdr (cdr (cdr x))))))
(define (cadaaar x) (car (cdr (car (car (car x))))))
(define (cadaadr x) (car (cdr (car (car (cdr x))))))
(define (cadadar x) (car (cdr (car (cdr (car x))))))
(define (cadaddr x) (car (cdr (car (cdr (cdr x))))))
(define (caddaar x) (car (cdr (cdr (car (car x))))))
(define (caddadr x) (car (cdr (cdr (car (cdr x))))))
(define (cadddar x) (car (cdr (cdr (cdr (car x))))))
(define (caddddr x) (car (cdr (cdr (cdr (cdr x))))))

(define (cdaaaar x) (cdr (car (car (car (car x))))))
(define (cdaaadr x) (cdr (car (car (car (cdr x))))))
(define (cdaadar x) (cdr (car (car (cdr (car x))))))
(define (cdaaddr x) (cdr (car (car (cdr (cdr x))))))
(define (cdadaar x) (cdr (car (cdr (car (car x))))))
(define (cdadadr x) (cdr (car (cdr (car (cdr x))))))
(define (cdaddar x) (cdr (car (cdr (cdr (car x))))))
(define (cdadddr x) (cdr (car (cdr (cdr (cdr x))))))
(define (cddaaar x) (cdr (cdr (car (car (car x))))))
(define (cddaadr x) (cdr (cdr (car (car (cdr x))))))
(define (cddadar x) (cdr (cdr (car (cdr (car x))))))
(define (cddaddr x) (cdr (cdr (car (cdr (cdr x))))))
(define (cdddaar x) (cdr (cdr (cdr (car (car x))))))
(define (cdddadr x) (cdr (cdr (cdr (car (cdr x))))))
(define (cddddar x) (cdr (cdr (cdr (cdr (car x))))))
(define (cdddddr x) (cdr (cdr (cdr (cdr (cdr x))))))

(define (even? x) (zero? (remainder x 2)))

(define (odd? x) (not (zero? (remainder x 2))))

(define (debug l s) (display l) (display ": ") (display s) (newline) s)

(define (make-rational n d) (cons 'rational (cons n (cons d '()))))
 
(define (numerator x) (if (rational? x) (cadr x) x))

(define (denominator x) (if (rational? x) (caddr x) 1))

(define (rational->real x) (/ (exact->inexact (cadr x)) (exact->inexact (caddr x))))

;; adapted from stklos
(define (rationalize x e)
        (define (simplest-rational x y)
                (define (sr x y)
                        (let ((fx (floor x))
                              (fy (floor y)))
                        (cond ((>= fx x) fx)
                              ((= fx fy) (+ fx (/ (sr (/ (- y fy)) (/ (- x fx))))))
                              (else      (+ 1 fx)))))
                (cond ((>= x y)      x)
                      ((positive? x) (sr x y))
                      ((negative? y) (- (sr (- y) (- x))))
                      (else          (if (and (exact? x) (exact? y)) 0 0.0))))
        (when (eq? e void)
              (set! e 1e-7))
        (let ((x (- x e))
              (y (+ x e)))
             (if (< y x)
                 (simplest-rational y x)
                 (simplest-rational x y))))

(define (make-complex re im) (cons 'rectangular (cons re (cons im '()))))

(define (real-part x) (if (complex? x) (cadr x) x))

(define (imag-part x) (if (complex? x) (caddr x) 0))

(define (fib x) (if (<= x 0) 1 (+ (fib (- x 2)) (fib (- x 1)))))

(define (fac x) (if (<= x 0) 1 (* x (fac (- x 1)))))

(define (ack n m)
        (if (= 0 n)
            (+ m 1)
            (if (= 0 m)
                (ack (- n 1) 1)
                (ack (- n 1) (ack n (- m 1))))))

(define (tak x y z)
        (if (< y x)
            (tak (tak (- x 1) y z)
                 (tak (- y 1) z x)
                 (tak (- z 1) x y))
            z))

(define (expt x n)
        (cond
              ((positive? n)
               (if (odd? n)
                   (* x (expt x (- n 1)))
                   (let ((y (expt x (/ n 2)))) (* y y))))
              ((negative? n)
               (/ (expt x (neg n))))
              (else 1)))

(define (length s) (if (null? s) 0 (+ 1 (length (cdr s)))))

(define (list . s) s)

(define (list? s) (or (null? s) (and (pair? s) (list? (cdr s)))))

(define (alist? s) (or (null? s) (and (pair? s) (pair? (car s)) (alist? (cdr s)))))

(define (assq a e)
        (if (null? e)
            e
            (if (eq? a (caar e))
                (car e)
                (assq a (cdr e)))))

(define (del-assq a e)
        (if (null? e)
            e
            (if (eq? a (caar e))
                (cdr e)
                (cons (car e)
                      (del-assq a (cdr e))))))

(define (assv a e)
        (if (null? e)
            e
            (if (eqv? a (caar e))
                (cdar e)
                (assv a (cdr e)))))

(define (del-assv a e)
        (if (null? e)
            e
            (if (eqv? a (caar e))
                (cdr e)
                (cons (car e)
                      (del-assv a (cdr e))))))

(define (assoc a e)
        (if (null? e)
            e
            (if (equal? a (caar e))
                (car e)
                (assoc a (cdr e)))))

(define (del-assoc a e)
        (if (null? e)
            e
            (if (equal? a (caar e))
                (cdr e)
                (cons (car e) (del-assoc a (cdr e))))))

(define (memq a e)
        (if (null? e)
            e
            (if (eq? a (caar e))
                (car e)
                (memq a (cdr e)))))

(define (memv a e)
        (if (null? e)
            e
            (if (eqv? a (caar e))
                (car e)
                (memv a (cdr e)))))

(define (member a e)
        (if (null? e)
            e
            (if (equal? a (caar e))
                (car e)
                (memv a (cdr e)))))

(define (fold f i s) (if (null? s) 1 (f (car s) (fold f i (cdr s)))))

(define (reverse! s)
   (let ((q '())
         (u '()))
        (while (pair? s)
               (set! u (cdr s))
               (set-cdr! s q)
               (set! q s)
               (set! s u))
         q))

(define (iota n)
        (define (riota n)
                (cond ((negative? n) (cons n (riota (+ n  1))))
                      ((positive? n) (cons n (riota (+ n -1))))
                      (else (cons 0 '()))))
        (reverse! (cdr (riota n))))

(define (pairs a b)
        (if (null? b)
            b
            (cons (cons a (cons (car b) '())) (pairs a (cdr b)))))

(define (cross a b)
        (if (null? a)
            a
            (cons (pairs (car a) b)
                  (cross (cdr a) b))))

(define (abs x) (if (negative? x) (neg x) x))

(define (max . l)
        (letrec ((maxi
                  (lambda (x y) (if (< x y) y x)))
                 (maxx
                  (lambda (l)
                          (if (null? (cdr l))
                               (car l)
                               (if (null? (cddr l))
                                   (maxi (car l) (cadr l))
                                   (maxi (car l) (maxx (cdr l))))))))
                maxi(maxx l)))

(define (min . l)
        (letrec ((mini
                  (lambda (x y) (if (< x y) x y)))
                 (minx
                  (lambda (l)
                          (if (null? (cdr l))
                              (car l)
                              (if (null? (cddr l))
                                  (mini (car l) (cadr l))
                                  (mini (car l) (minx (cdr l))))))))
                (minx l)))

(define (list-tail s i)
        (if (null? s)
            s
            (if (positive? i)
                (list-tail (cdr s) (- i 1))
                s)))

(define (list-ref s i) (car (list-tail s i)))

(define (map* i f s) (if (null? s) i (cons (f (car s)) (map* i f (cdr s)))))

(define (for-each f s)
        (while (pair? s)
               (f (car s))
               (set! s (cdr s))))

(define (map f s) (if (null? s) s (cons (f (car s)) (map f (cdr s)))))

(define (make-counter) (let ((n 0)) (lambda () (begin (set! n (+ n 1)) n))))

(define (polar->rectangular r theta)
    (cons 'complex (cons (* r (cos theta)) (cons (* r (sin theta)) '()))))

(define (env-head l t) (if (eq? l t) '() (cons (list (caar l) (caddar l)) (env-head (cdr l) t))))

(define (definition name)
        (let ((value (eval name (environment))))
             (if (closure? value)
                 (cons 'define (cons (cons name (cadadr value)) (cddadr value)))
                 (list 'define name value))))

(define (definitions)
        (for-each (lambda (x)
                  (if (closure? (cdr x))
                      (begin (display (definition (car x))) (newline) (newline))))
                  (reverse (environment))))

(define (ttytest)
        (while (not (char=? #\newline (peek-char)))
               (write (read-char))
               (newline))
        (read-char))

(define (edit s)

        (define paste-buffer '())

        (define (cursor-insert s)
                (cons 'cursor s))

        (define (cursor-replace s)
                (if (not (pair? s))
                    s
                    (if (eq? 'cursor (car s))
                        (cons (cursor-replace (car s)) (cons (read) (cursor-replace (cdr s))))
                        (cons (cursor-replace (car s)) (cursor-replace (cdr s))))))

        (define (cursor-remove s)
                (if (pair? s)
                    (if (eq? 'cursor (car s))
                        (cdr s)
                        (cons (cursor-remove (car s)) (cursor-remove (cdr s))))
                    s))

        (define (cursor-write s)
                (begin (eval (cursor-remove s) (environment))
                       s))

        (define (cursor-cdr s)
                (if (not (pair? s))
                    s
                    (if (and (pair? (cdr s))
                             (eq? 'cursor (car s)))
                        (cons (cadr s) (cons 'cursor (cddr s)))
                        (cons (cursor-cdr (car s)) (cursor-cdr (cdr s))))))

        (define (cursor-car s)
                (if (and (pair? s)
                         (pair? (cdr s))
                         (eq? 'cursor (cadr s))) 
                    (cons 'cursor (cons (car s) (cddr s)))
                    (if (pair? s)
                        (cons (cursor-car (car s)) (cursor-car (cdr s)))
                        s)))

        (define (cursor-in s)
                (if (not (pair? s))
                    s
                    (if (and (eq? 'cursor (car s))
                             (pair? (cdr s))
                             (pair? (cadr s)))
                        (cons (cons 'cursor (cadr s)) (cddr s))
                        (cons (cursor-in (car s)) (cursor-in (cdr s))))))

        (define (cursor-out s)
                (if (not (pair? s))
                    s
                    (if (and (pair? (car s))
                             (pair? (cdr s))
                             (eq? 'cursor (caar s)))
                        (cons 'cursor (cons (cdar s) (cddr s)))
                        (cons (cursor-out (car s)) (cursor-out (cdr s))))))

        (define (cursor-cut s)
                (if (not (pair? s))
                    s
                    (if (eq? 'cursor (car s))
                        (begin (set! paste-buffer (cadr s))
                               (cons (cursor-cut (car s)) (cursor-cut (cddr s))))
                        (cons (cursor-cut (car s)) (cursor-cut (cdr s))))))

        (define (cursor-paste s)
                (if (not (pair? s))
                    s
                    (if (eq? 'cursor (car s))
                        (cons (cursor-paste (car s)) (cons paste-buffer (cursor-paste (cdr s))))
                        (cons (cursor-paste (car s)) (cursor-paste (cdr s))))))

        (if (not (pair? s))
            (read)
            (begin (set! s (cursor-insert s))
                   (display s)
                   (newline)
                   (while (not (eqv? #\return (peek-char)))
                          (set! s
                                (cond
                                 ((eqv? (peek-char) #\d) (cursor-cdr s))
                                 ((eqv? (peek-char) #\a) (cursor-car s))
                                 ((eqv? (peek-char) #\r) (cursor-replace s))
                                 ((eqv? (peek-char) #\x) (cursor-cut s))
                                 ((eqv? (peek-char) #\p) (cursor-paste s))
                                 ((eqv? (peek-char) #\i) (cursor-in s))
                                 ((eqv? (peek-char) #\o) (cursor-out s))
                                 ((eqv? (peek-char) #\w) (cursor-write s))
                                 (else s)))
                          (display s)
                          (space)
                          (write-char (read-char))
                          (newline))
                    (while (char-ready?)
                           (read-char))
                    (cursor-remove s))))

(define (merge f p q)
  (cond ((null? p) q)
        ((null? q) p)
        (else (if (f (car p) (car q))
                  (cons (car p) (merge f (cdr p) q))
                  (cons (car q) (merge f (cdr q) p))))))

(define (alternate p)
  (if (or (null? p) (null? (cdr p)))
      p
      (cons (car p) (alternate (cdr (cdr p))))))

(define (sort f p)
  (if (or (null? p) (null? (cdr p)))
      p
      (merge f (sort f (alternate p))
               (sort f (alternate (cdr p))))))

(define (numeric-sort p) (sort < p))

(define (char-sort p) (sort char<? p))

(define (string-sort p) (sort string<? p))

(define (make-random)
    (let ((a 69069)
          (c 1)
          (m (<< 1 31))
          (seed 19380110))
          (lambda () (set! seed (remainder (+ (* seed a) c) m)) 
                     (exact->inexact (abs (/ seed m))))))
 
(define (shuffle random s)
        (sort (lambda (x y) (<= 0.5 (random))) s))

(define polynomials
        [6, 12, 20, 48, 72, 178, 272, 576, 1128, 2224, 4320,
        8592, 16512, 33568, 66560, 132096, 266112, 527488,
        1053440, 2103552, 4202496, 8418816, 16790528,
        33604608, 67177472, 134234112, 268576768, 537145344,
        1073848320, 2147880960])

(define (make-lfsr n)
        (let ((r 0)
              (p (vector-ref polynomials (- n 3))))
             (lambda () (set! r (^ (>> r 1) (& (~ (- (& r 1))) p))) (if (zero? (& r 1)) #f #t))))

(define (bits lfsr) (while #t (write-char (if (lfsr) #\1 #\0))))

;; (display (map car (environment))) (newline)

