;
; miscellaneous utilities and demos
;

;; (define builtin-environment (null-environment))

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

(define (boolean? x) (or (eq? x #t) (eq? x #f)))

(define (zero? x) (= 0 x))

(define (negative? x) (< x 0))

(define (positive? x) (> x 0))

(define (even? x) (zero? (% x 2)))

(define (odd? x) (= 1 (% x 2)))

;; (define (gcd x y) (if (zero? y) x (gcd y (% x y))))

;; (define (lcm x y) (let ((g (gcd x y))) (* (/ x g) (/ y g))))

(define (make-rational n d) (cons 'rational (cons n (cons d #f))))

(define (rationalize real)
        (let ((maxden 268435456)
              (t 0) (x real)
              (m00 1) (m11 1) (m01 0) (m10 0)
              (ai (inexact->exact real)))
             (while (<= (+ (* m10 ai) m11) maxden)
                    (set! t (+ (* m00 ai) m01)) (set! m01 m00) (set! m00 t)
                    (set! t (+ (* m10 ai) m11)) (set! m11 m10) (set! m10 t)
                    (set! x (/ 1.0 (- x (exact->inexact ai))))
                    (set! ai (inexact->exact x)))
             (make-rational m00 m10)))

(define (rational? r)
        (and (eq? 'rational (car r))
             (integer? (cadr r))
             (integer? (caddr r))
             (null? (cdddr r))))

(define numerator cadr)

(define denominator caddr)

(define (rational->real x) (/ (exact->inexact (cadr x)) (exact->inexact (caddr x))))

(define (rectangular? z)
        (and (eq? 'rectangular (car z))
             (real? (cadr z))
             (real? (caddr z))
             (null? (cdddr z))))

(define (make-rectangular re im) (cons 'rectangular (cons re (cons im #f))))

(define (polar? z)
        (and (eq? 'polar (car z))
             (real? (cadr z))
             (real? (caddr z))
             (null? (cdddr z))))

(define (make-polar r theta) (cons 'polar (cons r (cons theta #f))))

(define (real-part z) (if (rectangular? z) (cadr z) (* (cadr z) (cos (caddr z)))))

(define (imag-part z) (if (rectangular? z) (caddr z) (* (cadr z) (sin (caddr z)))))

(define (polar->rectangular z) (make-rectangular (* (cadr z) (cos (caddr z))) (* (cadr z) (sin (caddr z)))))

(define (mag-part z) (if (rectangular? z) (magnitude z) (cadr z)))

(define (theta-part z) (if (rectangular? z) (angle z) (caddr z)))

(define (rectangular->polar z) (make-polar (magnitude z) (angle z)))

(define (complex? z) (or (rectangular? z) (polar? z)))

(define (fib x) (if (<= x 0) 1 (+ (fib (- x 2)) (fib (- x 1)))))

(define (fac x) (if (<= x 0) 1 (* x (fac (- x 1)))))

(define (ack n m)
        (if (zero? n)
            (+ m 1)
            (if (zero? m)
                (ack (- n 1) 1)
                (ack (- n 1) (ack n (- m 1))))))

(define (tak x y z)
        (if (< y x)
            (tak (tak (- x 1) y z)
                 (tak (- y 1) z x)
                 (tak (- z 1) x y))
            z))

(define (expt x n)
        (if (zero? n)
            1
            (if (odd? n)
                (* x (expt x (- n 1)))
                (let ((y (expt x (/ n 2))))
                     (* y y)))))

(define (length s) (if s (+ 1 (length (cdr s))) 0))

(define (list . s) s)

(define (list? s) (and (pair? s) (or (null? (cdr s)) (list? (cdr s)))))

(define (alist? s)
        (and (pair? s)
             (pair? (car s))
             (or (null? (cdr s))
                 (alist? (cdr s)))))

(define (assq a e)
        (if (null? e)
            #f
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
            #f
            (if (eqv? a (caar e))
                (cdar e)
                (assv a (cdr e)))))

(define (del-assv a e)
        (if (null? e)
            e
            (if (eqv? a (caar e))
                (cdr e)
                (cons (car e)
                      (del-assq a (cdr e))))))

(define (assoc a e)
        (if (null? e)
            #f
            (if (equal? a (caar e))
                (car e)
                (assoc a (cdr e)))))

(define (del-assoc a e)
        (if (null? e)
            e
            (if (equal? a (caar e))
                (cdr e)
                (cons (car e) (del-asoc a (cdr e))))))

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

(define (fold f i s) (if s (f (car s) (fold f i (cdr s))) i))

(define (iota n)
        (letrec ((riot
                  (lambda (n m)
                          (if (> n 0)
                              (cons (- m n) (riot (- n 1) m))
                              #f))))
                 (riot n n)))

(define (pairs a b)
        (if b
            (cons (cons a (cons (car b) '())) (pairs a (cdr b)))
            b))

(define (cross a b)
        (if a
            (cons (pairs (car a) b)
                  (cross (cdr a) b)) a))

(define (abs x) (if (< x 0) (- x) x))

(define (max . l)
        (letrec ((maxi
                  (lambda (x y) (if (< x y) y x)))
                 (maxx
                  (lambda (l)
                          (if (cdr l)
                               (if (cddr l)
                                   (maxi (car l) (maxx (cdr l)))
                                   (maxi (car l) (cadr l)))
                               (car l)))))
                maxi(maxx l)))

(define (min . l)
        (letrec ((mini
                  (lambda (x y) (if (< x y) x y)))
                 (minx
                  (lambda (l)
                          (if (cdr l)
                              (if (cddr l)
                                  (mini (car l) (minx (cdr l)))
                                  (mini (car l) (cadr l)))
                              (car l)))))
                (minx l)))

(define (reverse! s)
        (let ((p s)
              (q '())
              (u '()))
             (begin (while p
                           (set! u (cdr p))
                           (set-cdr! p q)
                           (set! q p)
                           (set! p u))
                    q)))

(define (list-tail s i)
        (if (null? s)
            #f
            (if (zero? i)
                s
                (list-tail (cdr s) (- i 1)))))

(define (list-ref s i) (car (list-tail s i)))

(define (map* i f s) (if s (cons (f (car s)) (map* i f (cdr s)))  i))

(define (for-each f s) (while s (f (car s)) (set! s (cdr s))))

(define (map f s) (if s (cons (f (car s)) (map f (cdr s))) s))

(define (make-counter i)
        (let ((n i))
             (lambda (j) (begin (set! n (+ n 1)) n))))

;; (define (env-head l t) (if (eq? l t) #f (cons (list (caar l) (caddar l)) (env-head (cdr l) t))))

;; (define (builtin-defs) (env-head (null-environment) builtin-environment))

;; (define (init-defs) (env-head (null-environment) builtin-environment))

(display (map car (interaction-environment))) (newline)

;; (define init-environment (null-environment))

