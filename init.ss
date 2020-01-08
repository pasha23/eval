
;;
;; miscellaneous utilities and demos
;;

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

(define (even? x) (not (odd? x)))

(define (square x) (* x x))

(define (debug l s) (display l) (display ": ") (display s) (newline) s)

;; adapted from stklos
(define (rationalize x e)
        (define (simplest-rational x y)
                (define (sr x y)
                        (let ((fx (floor x))
                              (fy (floor y)))
                             (cond ((>= fx x) fx)
                                   ((= fx fy)
                                    (+ fx (/ (sr (/ (- y fy)) (/ (- x fx))))))
                                   (else (+ 1 fx)))))
                (cond ((>= x y) x) ((positive? x) (sr x y))
                      ((negative? y) (- (sr (- y) (- x))))
                      (else (if (and (exact? x) (exact? y)) 0 0.0))))
        (when (eq? e void) (set! e 1e-07))
        (let ((x (- x e)) (y (+ x e)))
             (if (< y x) (simplest-rational y x)
                 (simplest-rational x y))))

(define (real-part x) (if (complex? x) (cadr x) x))

(define (imag-part x) (if (complex? x) (caddr x) 0))

(define (nan? x)
    (if (complex? x)
        (or (nan? (real-part x)) (nan? (imag-part x)))
        (and (real? x) (not (= x x)))))

(define (finite? x)
        (if (real? x)
            (and (not (nan? x)) (not (= x +inf.0)) (not (= x -inf.0)))
            (and (complex? x) (finite? (real-part x)) (finite? (imag-part x)))))

(define (infinite? x)
        (and (number? x) (not (finite? x)) (not (nan? x))))

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
        (cond ((positive? n)
               (if (odd? n)
                   (* x (expt x (- n 1)))
                   (let ((y (expt x (/ n 2)))) (* y y))))
              ((negative? n) (/ (expt x (neg n))))
              (else 1)))

(define (length s) (if (null? s) 0 (+ 1 (length (cdr s)))))

(define (append! p q)
    (if (null? p)
        q
        (let ((r p))
             (while (pair? (cdr r))
                    (set! r (cdr r)))
             (set-cdr! r q)
             p)))

(define (nth i s)
        (if (zero? i)
            (car s)
            (nth (- i 1) (cdr s))))

(define (list . s) s)

(define (list? s) (or (null? s) (and (pair? s) (list? (cdr s)))))

(define (make-list n v)
    (let ((l '()))
         (while (> n 0)
                (set! n (- n 1))
                (set! l (cons v l)))
         l))

(define (list-set! l i v)
        (while (> i 0)
               (set! i (- i 1))
               (set! l (cdr l)))
        (set-car! l v))

(define (alist? s)
        (or (null? s) (and (pair? s) (pair? (car s)) (alist? (cdr s)))))

(define (assq a e)
        (if (null? e) e (if (eq? a (caar e)) (car e) (assq a (cdr e)))))

(define (del-assq a e)
        (if (null? e) e
            (if (eq? a (caar e)) (cdr e)
                (cons (car e) (del-assq a (cdr e))))))

(define (assv a e)
        (if (null? e) e
            (if (eqv? a (caar e)) (cdar e) (assv a (cdr e)))))

(define (del-assv a e)
        (if (null? e) e
            (if (eqv? a (caar e)) (cdr e)
                (cons (car e) (del-assv a (cdr e))))))

(define (assoc a e p)
        (if (null? e)
            e
            (if (eq? void p)
                (if (equal? a (caar e)) (car e) (assoc a (cdr e) p))
                (if (p      a (caar e)) (car e) (assoc a (cdr e) p)))))

(define (del-assoc a e)
        (if (null? e) e
            (if (equal? a (caar e)) (cdr e)
                (cons (car e) (del-assoc a (cdr e))))))

(define (memq a e)
        (if (null? e) #f (if (eq? a (caar e)) (car e) (memq a (cdr e)))))

(define (memv a e)
        (if (null? e) #f (if (eqv? a (caar e)) (car e) (memv a (cdr e)))))

(define (member a e p)
        (if (null? e)
            e
            (if (eq? void p)
                (if (equal? a (car e)) e (member a (cdr e) p))
                (if (p      a (car e)) e (member a (cdr e) p)))))

(define (fold f i s) (if (null? s) i (f (car s) (fold f i (cdr s)))))

(define (reverse s)
    (let ((r '()))
         (while (pair? s)
                (set! r (cons (car s) r))
                (set! s (cdr s)))
         r))

(define (iota n)
        (define (riota n)
                (cond ((negative? n) (cons n (riota (+ n 1))))
                      ((positive? n) (cons n (riota (+ n -1))))
                      (else (cons 0 '())))) (reverse! (cdr (riota n))))

(define (abs x) (if (negative? x) (neg x) x))

(define (max . l)

        (define (maxi x y) (if (< x y) y x))

        (define (maxx l)
                (if (null? (cdr l))
                    (car l)
                    (maxi (car l) (maxx (cdr l)))))
        (maxx l))

(define (min . l)

        (define (mini x y) (if (< x y) x y))

        (define (minx l)
                (if (null? (cdr l))
                    (car l)
                    (mini (car l) (minx (cdr l)))))
        (minx l))

(define (list-tail s i)
        (if (null? s) s
            (if (positive? i) (list-tail (cdr s) (- i 1)) s)))

(define (list-ref s i) (car (list-tail s i)))

(define (map* i f s)
        (if (null? s) i (cons (f (car s)) (map* i f (cdr s)))))

(define (for-each f s) (while (pair? s) (f (car s)) (set! s (cdr s))))

(define (cars lists)
        (if (null? lists)
            '()
            (cons (caar lists) (cars (cdr lists)))))

(define (cdrs lists)
        (if (null? lists)
            '()
            (cons (cdar lists) (cdrs (cdr lists)))))

(define (map f . lists)
        (if (and (pair? lists) (pair? (car lists)))
            (cons (apply f (cars lists))
                  (apply map (cons f (cdrs lists))))
            '()))

(define (any f . lists)
        (if (and (pair? lists) (pair? (car lists)))
            (or (apply f (cars lists))
                (apply any (cons f (cdrs lists))))
            #f))

(define (every f . lists)
        (if (and (pair? lists) (pair? (car lists)))
            (and (apply f (cars lists))
                 (apply every (cons f (cdrs lists))))
            #t))

(define (cross op a b)

        (define (each op a b)
                (if (null? b)
                    b
                    (cons (op a (car b)) (each op a (cdr b)))))

        (if (null? a)
            a
            (cons (each op (car a) b) (cross op (cdr a) b))))

(define (matrix-identity n)
        (cross (lambda (x y) (if (= x y) 1 0))
               (iota n)
               (iota n)))

(define (matrix-multiply m1 m2)
        (map (lambda (row)
                     (apply map
                            (cons (lambda column
                                          (apply + (map * row column)))
                                  m2)))
             m1))

(define (matrix-transpose m)
        (if (pair? (car m))
            (cons (cars m) (matrix-transpose (cdrs m)))
            '()))

(define (make-counter)
        (let ((n 0)) (lambda () (begin (set! n (+ n 1)) n))))

(define (polar->rectangular r theta)
        (cons 'complex
              (cons (* r (cos theta)) (cons (* r (sin theta)) '()))))

(define (env-head l t)
        (if (eq? l t) '()
            (cons (list (caar l) (caddar l)) (env-head (cdr l) t))))

(define (definition name)
        (let ((value (eval name (environment))))
             (if (closure? value)
                 (cons 'define
                       (cons (cons name (cadr (car (unbox value)))) (cddr (car (unbox value)))))
                 (list 'define name value))))

(define (definitions)
        (for-each (lambda (x)
                          (if (or (closure? (cdr x)) (vector? (cdr x))
                                  (string? (cdr x)) (number? (cdr x)))
                              (begin (write (definition (car x)))
                                     (newline) (newline))))
                  (reverse! (environment))))

(define (random-char)
        (call-with-input-file "/dev/random"
                              (lambda (port) (read-char port))))

(define (ttytest)
        (while (not (char=? #\newline (peek-char)))
               (write (read-char))
               (newline))
        (read-char))

(define (edit s) (define paste-buffer '())

        (define (cursor-insert s) (cons 'cursor s))

        (define (cursor-replace s)
                (if (not (pair? s)) s
                    (if (eq? 'cursor (car s))
                        (cons (cursor-replace (car s))
                              (cons (read) (cursor-replace (cdr s))))
                        (cons (cursor-replace (car s))
                              (cursor-replace (cdr s))))))

        (define (cursor-remove s)
                (if (pair? s)
                    (if (eq? 'cursor (car s)) (cdr s)
                        (cons (cursor-remove (car s))
                              (cursor-remove (cdr s)))) s))

        (define (cursor-write s)
                (begin (eval (cursor-remove s) (environment)) s))

        (define (cursor-cdr s)
                (if (not (pair? s)) s
                    (if (and (pair? (cdr s)) (eq? 'cursor (car s)))
                        (cons (cadr s) (cons 'cursor (cddr s)))
                        (cons (cursor-cdr (car s)) (cursor-cdr (cdr s))))))

        (define (cursor-car s)
                (if (and (pair? s) (pair? (cdr s))
                         (eq? 'cursor (cadr s)))
                    (cons 'cursor (cons (car s) (cddr s)))
                    (if (pair? s)
                        (cons (cursor-car (car s)) (cursor-car (cdr s)))
                        s)))

        (define (cursor-in s)
                (if (not (pair? s)) s
                    (if (and (eq? 'cursor (car s)) (pair? (cdr s))
                             (pair? (cadr s)))
                        (cons (cons 'cursor (cadr s)) (cddr s))
                        (cons (cursor-in (car s)) (cursor-in (cdr s))))))

        (define (cursor-out s)
                (if (not (pair? s)) s
                    (if (and (pair? (car s)) (pair? (cdr s))
                             (eq? 'cursor (caar s)))
                        (cons 'cursor (cons (cdar s) (cddr s)))
                        (cons (cursor-out (car s)) (cursor-out (cdr s))))))

        (define (cursor-cut s)
                (if (not (pair? s)) s
                    (if (eq? 'cursor (car s))
                        (begin (set! paste-buffer (cadr s))
                               (cons (cursor-cut (car s))
                                     (cursor-cut (cddr s))))
                        (cons (cursor-cut (car s)) (cursor-cut (cdr s))))))

        (define (cursor-paste s)
                (if (not (pair? s)) s
                    (if (eq? 'cursor (car s))
                        (cons (cursor-paste (car s))
                              (cons paste-buffer (cursor-paste (cdr s))))
                        (cons (cursor-paste (car s))
                              (cursor-paste (cdr s))))))

        (define (tch c) (char=? (peek-char) c))

        (if (not (pair? s))
            (read)
            (begin (set! s (cursor-insert s))
                   (display s)
                   (newline)
                   (while (not (tch #\return))
                          (set! s
                                (cond ((tch #\d) (cursor-cdr s))
                                      ((tch #\a) (cursor-car s))
                                      ((tch #\r) (cursor-replace s))
                                      ((tch #\x) (cursor-cut s))
                                      ((tch #\p) (cursor-paste s))
                                      ((tch #\i) (cursor-in s))
                                      ((tch #\o) (cursor-out s))
                                      ((tch #\w) (cursor-write s))
                                      (else s))) (display s) (space)
                          (write-char (read-char))
                          (newline))
                   (while (char-ready?)
                          (read-char))
                          (cursor-remove s))))

(define (timer thunk) (let ((start (cputime))) (thunk) (- (cputime) start)))

(define (tmt) (timer (lambda () (fib 30))))

(define (epsilon)
        (let ((e 1.0))
             (while (not (= 1.0 (+ 1.0 e))) (set! e (/ e 2)))
             (+ e e)))

(define (fibs)
        (let ((f (list 1 1)))
             (while (positive? (car f))
                    (set! f (cons (+ (car f) (cadr f)) f))) (cdr f)))


(define polynomials
        #(#x0 #x1 #x3 #x5 #x9 #x12 #x21 #x41 #x8e #x108 #x204 #x402 #x829 #x100d
          #x2015 #x4001 #x8016 #x10004 #x20013 #x40013 #x80004 #x100002 #x200001
          #x400010 #x80000d #x1000004 #x2000023 #x4000013 #x8000004 #x10000002
          #x20000029 #x40000004 #x80000057 #x100000029 #x200000073 #x400000002
          #x80000003b #x100000001f #x2000000031 #x4000000008 #x800000001c
          #x10000000004 #x2000000001f #x4000000002c #x80000000032 #x10000000000d
          #x200000000097 #x400000000010 #x80000000005b #x1000000000038 #x200000000000e
          #x4000000000025 #x8000000000004 #x10000000000023 #x2000000000003e
          #x40000000000023 #x8000000000004a #x100000000000016 #x200000000000031
          #x40000000000003d #x800000000000001 #x1000000000000013 #x2000000000000034
          #x4000000000000001))

(define (make-lfsr n)
        (let ((r 0)
              (p (vector-ref polynomials n)))
             (lambda (b) (set! b (odd? r)) (set! r (lfsr-shift r p)) b)))

(define (allbits n)
        (let ((r 0)
              (p (vector-ref polynomials n))
              (busy #t))
             (while busy
                    (write-char (if (odd? r) #\1 #\0))
                    (set! r (lfsr-shift r p))
                    (set! busy (not (zero? r)))) (newline)))

(define (bitstring n)
        (let ((r 0)
              (p (vector-ref polynomials n))
              (o '())
              (busy #t))
             (while busy
                    (set! o (cons (if (odd? r) #\1 #\0) o))
                    (set! r (lfsr-shift r p))
                    (set! busy (not (zero? r))))
             (list->string o)))

(define (filter p l)
    (cond ((null? l) l)
          ((p (car l)) (cons (car l) (filter p (cdr l))))
          (else (filter p (cdr l)))))

(define (sort cmp p)

    (define (alternate p)
            (if (or (null? p) (null? (cdr p))) p
                (cons (car p) (alternate (cdr (cdr p))))))

    (define (merge p q)
            (cond ((null? p) q)
                  ((null? q) p)
                  (else (if (cmp (car p) (car q))
                            (cons (car p) (merge (cdr p) q))
                            (cons (car q) (merge (cdr q) p))))))

    (if (or (null? p) (null? (cdr p))) p
        (merge (sort cmp (alternate p))
               (sort cmp (alternate (cdr p))))))

;; (display (map car (environment))) (newline)

;; (trace #t)

