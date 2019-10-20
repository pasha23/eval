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

(define (fib x)
        (if (<= x 0)
            1
            (+ (fib (- x 2))
               (fib (- x 1)))))

(define (fac x)
        (if (<= x 0)
            1
            (* x (fac (- x 1)))))

(define (ack n m)
        (if (eqv? n 0)
            (+ m 1)
            (if (eqv? m 0)
                (ack (- n 1) 1)
                (ack (- n 1) (ack n (- m 1))))))

(define (tak x y z)
        (if (< y x)
            (tak (tak (- x 1) y z)
                 (tak (- y 1) z x)
                 (tak (- z 1) x y))
            z))

(define (even x)
        (eqv? 0 (% x 2)))

(define (odd x)
        (not (even x)))

(define (expt x n)
        (if (eqv? 0 n)
            1
            (if (odd n)
                (* x (expt x (- n 1)))
                (let ((y (expt x (/ n 2)))) (* y y)))))

(define (gcd x y)
  (if (eqv? y 0)
      x
      (gcd y (% x y))))

(define (lcm x y)
        (let ((t (gcd x y)))
             (* (/ x t) (/ y t))))

(define (fold f i s)
    (if s
        (f (car s) (fold f i (cdr s)))
        i))

(define (iota n)
    (if (> n 0)
        (cons n (iota (- n 1)))
        '()))

(define (pairs a b)
    (if b
        (cons (cons a (cons (car b) '())) (pairs a (cdr b)))
        b))

(define (cross a b)
    (if a
        (cons (pairs (car a) b) (cross (cdr a) b))
        a))

(define (mapcar f s)
        (if s (cons (f (car s)) (mapcar f (cdr s))) s))

(display (mapcar car (globals)) (newline))

