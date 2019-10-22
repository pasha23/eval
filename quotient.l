
(define (quotient l)
    (if l
        (if (cdr l)
            (if (cddr l)
                (div (car l) (product (cdr l)))
                (div (car l) (cadr l)))
            (div 1.0 (car l)))
        1))

(define (/ . l) (quotient l))

(define (remainder l)
    (if l
        (if (cdr l)
            (if (cddr l)
                (mod (car l) (remainder (cdr l)))
                (mod (car l) (cadr l)))
            (mod 1.0 (car l)))
        1))

(define (% . l) (modulus l))

