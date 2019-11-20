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

(define (make-rational n d)
   (cons 'rational (cons n (cons d '()))))
 
(define numerator cadr)

(define denominator caddr)

(define (rational->real x) (/ (exact->inexact (cadr x)) (exact->inexact (caddr x))))

;; adapted from stklos
(define (rationalize x e)
        (letrec ((simplest-rational
                  (lambda (x y)
                          (letrec ((sr
                                   (lambda (x y)
                                       (let ((fx (floor x))
                                             (fy (floor y)))
                                       (cond ((>= fx x) fx)
                                             ((= fx fy) (+ fx (/ (sr (/ (- y fy)) (/ (- x fx))))))
                                             (else      (+ 1 fx)))))))
                                  (cond ((>= x y)      x)
                                        ((positive? x) (sr x y))
                                        ((negative? y) (- (sr (- y) (- x))))
                                        (else          (if (and (exact? x) (exact? y)) 0 0.0)))))))
                   (when (eq? e void)
                         (set! e 1e-15))
                   (let ((x (- x e))
                         (y (+ x e)))
                        (if (< y x)
                            (simplest-rational y x)
                            (simplest-rational x y)))))

(define (make-complex re im)
    (cons 'rectangular (cons re (cons im '()))))

(define real-part cadr)

(define imag-part caddr)

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
        (if (positive? n)
            (if (= 1 (% n 2))
                (* x (expt x (- n 1)))
                (let ((y (expt x (/ n 2))))
                     (* y y)))
            1))

(define (length s) (if (null? s) 0 (+ 1 (length (cdr s)))))

(define (list . s) s)

(define (list? s) (or (null? s) (and (pair? s) (list? (cdr s)))))

(define (alist? s) (or (null? s) (and (pair? s) (pair? (car s)) (alist? (cdr s)))))

(define (assq a e)
        (if (null? e)
            '()
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
            '()
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
            '()
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

(define (iota n)
    (let ((s '())
          (i (- n 1)))
         (while (>= i 0)
                (set! s (cons i s))
                (set! i (- i 1)))
         s))

;; (define (iota n) (if (= 0 n) '() (cons n (iota (- n 1)))))

(define (pairs a b)
        (if (null? b)
            b
            (cons (cons a (cons (car b) '())) (pairs a (cdr b)))))

(define (cross a b)
        (if (null? a)
            a
            (cons (pairs (car a) b)
                  (cross (cdr a) b))))

(define (abs x) (if (< x 0) (- x) x))

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

(define (reverse! s)
   (let ((p s)
         (q '())
         (u '()))
        (while (pair? p)
               (set! u (cdr p))
               (set-cdr! p q)
               (set! q p)
               (set! p u))
         q))

(define (list-tail s i)
        (if (null? s)
            '()
            (if (positive? i)
                (list-tail (cdr s) (- i 1))
                s)))

(define (list-ref s i) (car (list-tail s i)))

(define (map* i f s) (if (null? s) i (cons (f (car s)) (map* i f (cdr s)))))

(define (for-each f s)
        (while (pair? s)
               (f (car s))
               (set! s (cdr s))))

(define (map f s) (if (null? s) '() (cons (f (car s)) (map f (cdr s)))))

(define (make-counter)
        (let ((n 0))
             (lambda () (begin (set! n (+ n 1)) n))))

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

;; (display (map car (interaction-environment))) (newline)

