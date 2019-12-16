;
; miscellaneous utilities and demos
;

(define (list? s) (or (null? s) (and (pair? s) (list? (cdr s)))))

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

(define (make-complex re im)
        (cons 'rectangular (cons re (cons im '()))))

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
        (cond ((positive? n)
               (if (odd? n)
                   (* x (expt x (- n 1)))
                   (let ((y (expt x (/ n 2)))) (* y y))))
              ((negative? n) (/ (expt x (neg n))))
              (else 1)))

(define (length s) (if (null? s) 0 (+ 1 (length (cdr s)))))

(define (nth i s)
        (if (zero? i)
            (car s)
            (nth (- i 1) (cdr s))))

(define (list . s) s)

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

(define (assoc a e)
        (if (null? e) e
            (if (equal? a (caar e)) (car e) (assoc a (cdr e)))))

(define (del-assoc a e)
        (if (null? e) e
            (if (equal? a (caar e)) (cdr e)
                (cons (car e) (del-assoc a (cdr e))))))

(define (memq a e)
        (if (null? e) e (if (eq? a (caar e)) (car e) (memq a (cdr e)))))

(define (memv a e)
        (if (null? e) e (if (eqv? a (caar e)) (car e) (memv a (cdr e)))))

(define (member a e)
        (if (null? e) e
            (if (equal? a (caar e)) (car e) (memv a (cdr e)))))

(define (fold f i s) (if (null? s) 1 (f (car s) (fold f i (cdr s)))))

(define (iota n)
        (define (riota n)
                (cond ((negative? n) (cons n (riota (+ n 1))))
                      ((positive? n) (cons n (riota (+ n -1))))
                      (else (cons 0 '())))) (reverse! (cdr (riota n))))

(define (pairs a b)
        (if (null? b)
            b
            (cons (cons a (cons (car b) '())) (pairs a (cdr b)))))

(define (cross a b)
        (if (null? a)
            a
            (cons (pairs (car a) b) (cross (cdr a) b))))

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

(define (map f s) (if (null? s) s (cons (f (car s)) (map f (cdr s)))))

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
                       (cons (cons name (cadadr value)) (cddadr value)))
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

(define (hexout n)

        (define (hexo n)
                (if (< n 10)
                    (integer->char (+ 48 (& n 15)))
                    (integer->char (+ 87 (& n 15)))))

        (let ((r '()))
             (when (zero? n) (set! r (cons #\0 r)))
             (while (> n 0)
                    (set! r (cons (hexo (& n 15)) r))
                    (set! n (>> n 4)))
             (list->string r)))

(define (hexdigit d)
        (vector-ref [#\0, #\1, #\2, #\3, #\4, #\5, #\6, #\7, #\8, #\9, #\A, #\B, #\C, #\D, #\E, #\F ] d))

(define (hexin s)

        (define (decimal c) (and (char<=? #\0 c) (char<=? c #\9)))

        (define (smallhex c) (and (char<=? #\a c) (char<=? c #\f)))

        (define (bighex c) (and (char<=? #\A c) (char<=? c #\F)))

        (define (hexi c)
                (cond ((decimal c) (- (char->integer c) 48))
                      ((smallhex c) (- (char->integer c) 87))
                      ((bighex c) (- (char->integer c) 55))))

        (let ((l (string->list s))
              (n 0))
             (while (pair? l)
                    (set! n (+ (<< n 4) (hexi (car l))))
                    (set! l (cdr l)))
             n))

(define (timer thunk) (let ((start (time))) (thunk) (- (time) start)))

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
        [0, 1, 3, 5, 9, 18, 33, 65, 142, 264, 516, 1026, 2089, 4109,
            8213, 16385, 32790, 65540, 131091, 262163, 524292, 1048578,
            2097153, 4194320, 8388621, 16777220, 33554467, 67108883,
            134217732, 268435458, 536870953, 1073741828, 2147483735,
            4294967337, 8589934707, 17179869186, 34359738427, 68719476767,
            137438953521, 274877906952, 549755813916, 1099511627780,
            2199023255583, 4398046511148, 8796093022258, 17592186044429,
            35184372088983, 70368744177680, 140737488355419,
            281474976710712, 562949953421326, 1125899906842661,
            2251799813685252, 4503599627370531, 9007199254741054,
            18014398509482019, 36028797018964042, 72057594037927958,
            144115188075855921, 288230376151711805, 576460752303423489,
            1152921504606846995, 2305843009213694004, 4611686018427387905])

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

(define (merge cmp p q)
        (cond ((null? p) q)
              ((null? q) p)
              (else (if (cmp (car p) (car q))
                        (cons (car p) (merge cmp (cdr p) q))
                        (cons (car q) (merge cmp (cdr q) p))))))

(define (alternate p)
        (if (or (null? p) (null? (cdr p))) p
            (cons (car p) (alternate (cdr (cdr p))))))

(define (sort cmp p)
        (if (or (null? p) (null? (cdr p))) p
            (merge cmp (sort cmp (alternate p))
                   (sort cmp (alternate (cdr p))))))

;; (display (map car (environment))) (newline)

;; (trace #t)

