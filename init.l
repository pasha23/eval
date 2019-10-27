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

(define (boolean? x) (or (eqv? x #t) (eqv? x #f)))

(define (even? x) (eqv? 0 (mod x 2)))

(define (negative? x) (< x 0))

(define (odd? x) (eqv? 1 (mod x 2)))

(define (positive? x) (> x 0))

(define (zero? x) (eqv? 0 x))

(define (truncate x) #f)            ;; not done
(define (angle z) #f)               ;; not done
(define (make-polar r theta) #f)    ;; not done

(define (rational? r)
        (and (eq? 'rational (car r))
             (integer? (cadr r))
             (integer? (caddr r))
             (null? (cdddr r))))

(define (rationalize real)
        (let ((maxden 268435456)
              (t 0) (x real)
              (m00 1) (m11 1) (m01 0) (m10 0)
              (ai (inexact->exact real)))
             (while (<= (add (mul m10 ai) m11) maxden)
                    (set! t (add (mul m00 ai) m01)) (set! m01 m00) (set! m00 t)
                    (set! t (add (mul m10 ai) m11)) (set! m11 m10) (set! m10 t)
                    (set! x (div 1.0 (sub x (exact->inexact ai))))
                    (set! ai (inexact->exact x)))
             (cons 'rational (cons m00 (cons m10 #f)))))

(define (numerator r)   (if (rational? r) (cadr r) #f))
(define (denominator r) (if (rational? r) (caddr r) #f))

(define (rational-add x y)
        (if (and (rational? x)
                 (rational? y))
            (let ((d (lcm (denominator x) (denominator y))))
                  (let ((xn (mul (numerator x) (div d (denominator x))))
                        (yn (mul (numerator y) (div d (denominator y)))))
                       (cons 'rational (cons (add xn yn) (cons d #f)))))
            #f))

(define (rational-sub x y)
        (if (and (rational? x)
                 (rational? y))
            (let ((d (lcm (denominator x) (denominator y))))
                  (let ((xn (mul (numerator x) (div d (denominator x))))
                        (yn (mul (numerator y) (div d (denominator y)))))
                       (cons 'rational (cons (sub xn yn) (cons d #f)))))
            #f))

(define (rational-mul x y)
        (if (and (rational? x)
                 (rational? y))
            (let ((g (gcd (denominator x) (denominator y))))
                 (cons 'rational
                 (cons (div (mul (numerator x) (numerator y)) g)
                 (cons (div (mul (denominator x) (denominator y)) g)
                       #f))))
            #f))

(define (rational-div x y)
        (if (and (rational? x)
                 (rational? y))
            (let ((g (gcd (denominator x) (numerator y))))
                 (cons 'rational
                 (cons (div (mul (numerator x) (denominator y)) g)
                 (cons (div (mul (denominator x) (numerator y)) g)
                       #f))))
            #f))

(define (complex? z)
        (and (eq? 'complex (car z))
             (real? (cadr z))
             (real? (caddr z))
             (null? (cdddr z))))

(define (real-part z) (if (complex? z) (cadr z) #f))
(define (imag-part z) (if (complex? z) (caddr z) #f))

(define (square x) (mul x x))

(define (magnitude z)
        (if (complex? z)
            (sqrt (add (square (real-part z)) (square (imag-part z))))
            #f))

(define (make-rectangular x y) (cons 'complex (cons x (cons y #f))))

(define (fib x) (if (<= x 0) 1 (add (fib (sub x 2)) (fib (sub x 1)))))

(define (fac x) (if (<= x 0) 1 (mul x (fac (sub x 1)))))

(define (ack n m)
        (if (eqv? n 0)
            (add m 1)
            (if (eqv? m 0)
                (ack (sub n 1) 1)
                (ack (sub n 1) (ack n (sub m 1))))))

(define (tak x y z)
        (if (< y x)
            (tak (tak (sub x 1) y z)
                 (tak (sub y 1) z x)
                 (tak (sub z 1) x y))
            z))

(define (expt x n)
        (if (eqv? 0 n)
            1
            (if (odd? n)
                (mul x (expt x (sub n 1)))
                (let ((y (expt x (div n 2))))
                     (mul y y)))))

(define (length s) (if s (add 1 (length (cdr s))) 0))

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

(define (gcd x y) (if (eqv? y 0) x (gcd y (mod x y))))

(define (lcm x y) (let ((g (gcd x y))) (mul (div x g) (div y g))))

(define (fold f i s) (if s (f (car s) (fold f i (cdr s))) i))

(define (iota n)
        (let ((riot
               (lambda (n m)
                       (if (> n 0)
                           (cons (sub m n) (riot (sub n 1) m))
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

(define (append l m)
        (if l
            (cons (car l) (append (cdr l) m))
            m))

(define (abs x) (if (< x 0) (sub 0 x) x))

(define (max . l)
        (let ((maxi
               (lambda (x y) (if (< x y) y x)))
              (maxx
               (lambda (l)
                       (if (cdr l)
                            (if (cddr l)
                                (maxi (car l) (maxx (cdr l)))
                                (maxi (car l) (cadr l)))
                            (car l)))))
             (maxx l)))

(define (min . l)
        (let ((mini
               (lambda (x y) (if (< x y) x y)))
              (minx
               (lambda (l)
                       (if (cdr l)
                           (if (cddr l)
                               (mini (car l) (minx (cdr l)))
                               (mini (car l) (cadr l)))
                           (car l)))))
             (minx l)))

(define (sum l)
        (if l (add (car l) (sum (cdr l))) 0))

(define (diff l)
        (if l
            (if (cdr l)
                (if (cddr l)
                    (sub (car l) (sum(cdr l)))
                    (sub (car l) (cadr l)))
                (sub 0 (car l)))
            0))

(define (product l)
        (if l
            (mul (car l) (product (cdr l)))
            1))

(define (quotient l)
        (if l
            (if (cdr l)
                (if (cddr l)
                    (div (car l) (quotient (cdr l)))
                    (div (car l) (cadr l)))
                (div 1 (exact->inexact (car l))))
            1))

(define (remainder l)
        (if l
            (if (cdr l)
                (if (cddr l)
                    (mod (car l) (remainder (cdr l)))
                    (mod (car l) (cadr l)))
                (mod 1 (car l)))
            1))

(define (+ . l) (sum l))

(define (- . l) (diff l))

(define (* . l) (product l))

(define (/ . l) (quotient l))

(define (% . l) (remainder l))

(define (make-counter i)
        (let ((n i))
             (lambda (j) (begin (set! n (add n 1)) n))))

(define counter (make-counter 0))

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

(define (map* i f s) (if s (cons (f (car s)) (map* i f (cdr s)))  i))

(define (for-each f s) (while s (f (car s)) (set! s (cdr s))))

(define (map f s) (if s (cons (f (car s)) (map f (cdr s))) s))

(display (map car (interaction-environment)) (newline))

