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

(define (even? x) (eqv? 0 (mod x 2)))

(define (negative? x) (< x 0))

(define (odd? x) (eqv? 1 (mod x 2)))

(define (positive? x) (> x 0))

(define (zero? x) (eqv? 0 x))

(define (fib x) (if (<= x 0) 1 (+ (fib (sub x 2)) (fib (sub x 1)))))

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

(define (expt x n) (if (eqv? 0 n) 1 (if (odd? n) (mul x (expt x (sub n 1))) (let ((y (expt x (div n 2)))) (mul y y)))))

(define (length s) (if s (add 1 (length (cdr s))) 0))

(define (list . s) s)

(define (list? s) (and (pair? s) (or (null? (cdr s)) (list? (cdr s)))))

(define (gcd x y) (if (eqv? y 0) x (gcd y (mod x y))))

(define (lcm x y) (let ((g (gcd x y))) (mul (div x g) (div y g))))

(define (fold f i s) (if s (f (car s) (fold f i (cdr s))) i))

(define (iota n) (let ((riot (lambda (n m) (if (> n 0) (cons (sub m n) (riot (sub n 1) m)) '())))) (riot n n)))

(define (pairs a b) (if b (cons (cons a (cons (car b) '())) (pairs a (cdr b))) b))

(define (cross a b) (if a (cons (pairs (car a) b) (cross (cdr a) b)) a))

(define (abs x) (if (< x 0) (sub 0 x) x))

(define (mapcar f s) (if s (cons (f (car s)) (mapcar f (cdr s))) s))

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

(define (min . x)
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

(define (+ . l)
        (let ((sum
               (lambda (l)
                       (if l
                           (add (car l) (sum (cdr l)))
                           0))))
             (sum l)))

(define (- . l)
        (let ((diff
              (lambda (l)
                      (if l
                          (if (cdr l)
                              (if (cddr l)
                                  (sub (car l) (sum(cdr l)))
                                  (sub (car l) (cadr l)))
                              (sub 0 (car l)))
                          0))))
             (diff l)))

(define (* . l)
        (let ((product
              (lambda (l)
                      (if l
                          (mul (car l) (product (cdr l)))
                          1))))
             (product l)))

(define (/ . l)
        (let ((quotient
               (lambda (l)
                       (if l
                           (if (cdr l)
                               (if (cddr l)
                                   (div (car l) (quotient (cdr l)))
                                   (div (car l) (cadr l)))
                               (div 1 (exact->inexact (car l))))
                           1))))
             (quotient l)))

(define (% . l)
        (let ((remainder
               (lambda (l)
                       (if l
                           (if (cdr l)
                               (if (cddr l)
                                   (mod (car l) (remainder (cdr l)))
                                   (mod (car l) (cadr l)))
                               (mod 1 (car l)))
                           1))))
             (remainder l)))

(display (mapcar car (globals)) (newline))

