(define tests '(
    (eqv? (^ 7 2) 5)
    (eqv? (~ 0) -1)
    (< 2 3)
    (eqv? 8 (<< 1 3))
    (<= 3 3)
    (= 3 3)
    (> 5 3)
    (>= 3 3)
    (eqv? 1 (>> 8 3))
    (eqv? 5 (| 4 1))
    (eqv? (- 1 2 3) -4)
    (eqv? (/ 4 2) 2)
    (eqv? (* 3 4) 12)
    (eqv? (& 5 2) 0)
    (eqv? (% 3 2) 1)
    (eqv? (+ 3 4) 7)
    (eqv? (abs -7) 7)
    (= 29 (ack 3 2))
    (eqv? 1.0 (cos (acos 1.0)))
    (eqv? (add 3 4) 7)
    (alist? '((a . b) (c . d)))
    (and #t #t)
    (< (sub (angle '(complex 1.0 1.0)) 0.785398163397448) 1e-15)
    (eqv? '(a b c d e) (append '(a b c) '(d e)))
    (eq? 'a (apply car '((a b))))
    (eqv? 1.0 (sin (asin 1.0)))
    (eqv? '(c . d) (assoc 'c '((a . b) (c . d))))
    (eqv? '(c . d) (assq 'c '((a . b) (c . d))))
    (eq? 'd (assv 'c '((a . b) (c . d))))
    (<= (abs (- 1.0 (tan (atan 1.0)))) 1e-15)
    ;; atoms
    (= 3 (begin 1 2 3))
    (not (boolean? 5))
    ;; caaaar
    ;; caaadr
    ;; caaar
    ;; caadar
    ;; caaddr
    ;; caadr
    ;; caar
    ;; cadaar
    ;; cadadr
    ;; cadar
    ;; caddar
    ;; cadddr
    ;; caddr
    ;; cadr
    ;; car
    ;; cdaaar
    ;; cdaadr
    ;; cdaar
    ;; cdadar
    ;; cdaddr
    ;; cdadr
    ;; cdar
    ;; cddaar
    ;; cddadr
    ;; cddar
    ;; cdddar
    ;; cddddr
    ;; cdddr
    ;; cddr
    ;; cdr
    (eqv? (ceiling 1.5) 2.0)
    (char<=? #\a #\b)
    (char<? #\a #\b)
    (char=? #\a #\a)
    (char>=? #\b #\a)
    (char>? #\b #\a)
    (char? #\a)
    (char-alphabetic? #\a)
    (char-ci<=? #\A #\b)
    (char-ci<? #\B #\c)
    (char-ci=? #\A #\a)
    (char-ci>=? #\B #\a)
    (char-ci>? #\B #\a)
    (char=? #\a (char-downcase #\A))
    (= 65 (char->integer #\A))
    (char-lower-case? #\a)
    (char-numeric? #\0)
    ;; char-ready?
    (char=? #\A (char-upcase #\a))
    (char-upper-case? #\A)
    (char-whitespace? (space))
    (complex? '(complex 3.0 4.0))
    ;; cond
    (eqv? '(a b c) (cons 'a '(b c)))
    ;; (eqv? 1 (counter))
    ;; (eqv? 2 (counter))
    ;; cross
    ;; cyclic?
    ;; define
    ;; del-assoc
    ;; del-assq
    ;; del-assv
    ;; delay
    ;; (= 3 (denominator (rationalize 1.5)))
    ;; display
    (= 3 (div 12 4))
    ;; eof-object?
    (eq? 'a 'a)
    (eqv? '(1 2 3) '(1 2 3))
    (= 7 (eval '(add 3 4) (interaction-environment)))
    (even? 2)
    (exact? 2)
    (= 2.0 (exact->inexact 2))
    (= 1.0 (exp 0.0))
    (= 128 (expt 2 7))
    (not #f)
    (= 6 (fac 3))
    (= 13 (fib 5))
    (= 1.0 (floor 1.5))
    ;; fold
    ;; (= 5 (force (delay 5)))
    ;; for-each
    (= 2 (gcd 12 10))
    (= 3 (if #t 3 2))
    (= (imag-part '(complex 3.0 4.0)) 4.0)
    (inexact? 3.0)
    (= 3 (inexact->exact 3.0))
    (integer? 3)
    (char=? #\A (integer->char 65))
    ;; interaction-environment
    ;; iota
    ;; lambda
    (= 30 (lcm 12 10))
    (= 3 (length '(a b c)))
    ;; let
    (eqv? '(1 2 3) (list 1 2 3))
    (list? '(1 2 3))
    (eqv? '(c d e) (list-tail '(a b c d e) 2))
    (eqv? 'c (list-ref '(a b c d e) 2))
    ;; load
    (<= (abs (- 1.0 (log (exp 1.0)))) 1e-15)
    (<= (abs (- (sqrt 2.0) (magnitude '(complex 1.0 1.0)))) 1e-15)
    ;; make-counter
    ;; make-polar
    ;; make-rectangular
    (= 45 (string-length (make-string 45)))
    ;; map
    ;; map*
    (= 3 (max 1 3 2))
    ;; member
    ;; memq
    ;; memv
    (= 3 (min 4 3 6))
    (= 1 (mod 3 2))
    (= 6 (mul 2 3))
    (negative? -3)
    ;; newline
    (not #f)
    (null? #f)
    ;; null-environment
    (number? 3)
    (eqv? "3" (number->string 3))
    ;; numerator
    (odd? 3)
    (or #f #f #t #f)
    (pair? '(a . b))
    ;; pairs
    ;; peek-char
    (positive? 3)
    (<= (abs (- 8.0 (pow 2.0 3.0))) 1e-15)
    (procedure? procedure?)
    (procedure? fib)
    ;; promise?
    ;; promise-forced?
    ;; promise-value
    (= '3 (add 2 1))
    (eqv? `(a ,(add 3 4) b) '(a 7 b))
    (rational? '(rational 5 6))
    (eqv? '(rational 5 6) (rational-add '(rational 1 2) '(rational 1 3)))
    (eqv? '(rational 3 2) (rational-div '(rational 3 4) '(rational 1 2)))
    (eqv? (rationalize 3.14159265358979) '(rational 789453460 251290841))
    (eqv? '(rational 1 1) (rational-mul '(rational 2 3) '(rational 3 2)))
    (eqv? '(rational 1 6) (rational-sub '(rational 1 2) '(rational 1 3)))
    ;; read
    ;; read-char
    (real? 45.0)
    (= 45.0 (real-part '(complex 45.0 18.0)))
    (eqv? '(3 2 1) (reverse '(1 2 3)))
    (eqv? '(3 2 1) (reverse! '(1 2 3)))
    (= 3.0 (round 3.1))
    ;; set!
    (eqv? '(a b) (begin (let ((s '(b b))) (set-car! s 'a) s)))
    (eqv? '(a b) (begin (let ((s '(a a))) (set-cdr! s '(b)) s )))
    (= (sin (asin 1.0)) 1.0)
    (= 3.0 (sqrt 9.0))
    (= 3 (string->number "3"))
    (string<=? "abc" "abd")
    (string<? "abc" "abd")
    (string=? "abc" "abc")
    (string>=? "abd" "abc")
    (string>? "abd" "abc")
    (string? "abc")
    (string-ci<=? "ABC" "abc")
    (string-ci<? "ABC" "abd")
    (string-ci=? "ABC" "aBc")
    (string-ci>=? "aBc" "ABB")
    (string-ci>? "ABd" "abC")
    (string=? "abc" (string-copy "abc"))
    (string=? "AAA" (string-fill! (make-string 3) #\A))
    (= 3 (string-length "abc"))
    (char=? #\A (string-ref "aAa" 1))
    (string=? "aBc" (string-set! "abc" 1 #\B ))
    (= 2 (sub 5 3))
    (string=? "aA" (substring "baA" 1 3))
    (symbol? 'a)
    (eqv? "abc" (symbol->string 'abc))
    (= 6 (tak 7 6 5))
    (<= (abs (- 1.0 (tan (atan 1.0)))) 1e-15)
    ;; truncate
    ;; while
    ;; write
    ;; write-char
    (zero? 0)
    #t
))

(let ((t tests))
     (while t
            (if (eqv? #t (eval (car t) (interaction-environment)))
                (display (car t) " " 'pass (newline))
                (display (car t) " " 'fail (newline)))
            (set! t (cdr t))))

