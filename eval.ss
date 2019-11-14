
;;
;; metacircular evaluator
;;

(define (read-tail)
        (let ((q (read)))
             (cond ((eq? rparen  q) #f)
                   ((eof-object? q) #f)
                   ((eq? dot     q) (car (read-tail)))
                   (else (cons q (read-tail))))))

(define (read)
        (let ((p (scan)))
             (cond ((eq? #f      p) #f)
                   ((eof-object? p) p)
                   ((eq? lparen  p) (read-tail))
                   ((eq? qchar   p) (cons 'quote (cons (read) #f)))
                   ((eq? tick    p) (cons 'quasiquote (cons (read) #f)))
                   ((eq? comma   p) (cons 'unquote (cons (read) #f)))
                   ((eq? commaat p) (cons 'unquotesplicing (cons (read) #f)))
                   (else            p))))

(define (evlis p env)
        (if p (cons (eval (car p) env) (evlis (cdr p) env)) #f))

(define (assoc formals actuals env)
        (cond ((not (pair? formals))
               (cons (cons formals actuals) env))
              ((not actuals)
               (cons (cons (car formals) void)
                     (assoc (cdr formals) actuals env)))
              (else (cons (cons (car formals) (car actuals))
                          (assoc (cdr formals) (cdr actuals) env)))))

(define (find exp env)
        (if (null? env)
            #f
            (if (eq? exp (caar env))
                (car env)
                (find exp (cdr env)))))

(define (get exp env)
        (let ((binding (find exp env)))
             (if (pair? binding)
                 (cdr binding)
                 #f)))

(define (defineform exp env)
        (let ((binding (find (car exp) env)))
             (if (pair? binding)
                 (begin (set-cdr binding (eval (cadr exp) env)) env)
                 (cons (cons (car exp) (eval (cadr exp))) env))))
    
(define (setform exp env)
        (let ((binding (find (car exp) env)))
             (if (pair? binding)
                 (set-cdr! binding (eval (cadr exp) env))
                 #f)))

(define (begintail exp env)
        (if (not (cdr exp))
            (eval (car exp) env)
            (begintail (cdr s) env)))

(define (append p q)
        (if p (cons (car p) (append (cdr p) q)) q))

(define (unquoteform exp env)
        (cond ((not exp) exp)
              ((not (pair? exp)) exp)
              ((and (eq? 'unquote (car exp))
                    (pair? (cdr exp)))
               (eval (cadr exp) env))
              ((and (car exp) (eq? 'unquotesplicing (caar exp)))
               (append (eval (cadar exp) env)
                       (unquoteform (cdr exp) env)))
              (else (cons (unquoteform (car exp) env)
                          (unquoteform (cdr exp) env)))))

(define (quasiquoteform exp env) (unquoteform (car exp) env))

(define (andform exp env)
        (if exp
            (if (eval (car exp) env)
                (andform (cdr exp) env)
                #f)
            #t))

(define (orform exp env)
        (if exp
            (if (eval (car exp) env)
                #t
                (orform (cdr exp) env))
            #f))

(define (whenform exp env)
        (if (eval (car exp) env)
            (begintail (cdr exp) env)))

(define (unlessform exp env)
        (if (not (eval (car exp) env))
            (begintail (cdr exp env))))

(define (whileform exp env)
        (while (eval (car exp))
               (begintail (cdr exp) env)))

;; complex delay do lambda let let* letrec rational

(define (quoteform exp env)
        (car exp))

(define (ifform exp env)
        (if (eval (car exp) env)
            (eval (cadr exp) env)
            (eval (caddr exp) env)))

(define (condform exp env)
        (if (or (eq? 'else (caar exp))
                (eval (caar exp) env))
            (eval (cadr exp) env)
            (condform (cdr exp) env)))

(define (member key s)
        (if s
            (if (eqv? key (car s))
                #t
                (member key (cdr s)))
            #f))

(define (casetail key exp env)
        (if (null? exp)
            void
            (if (or (eq? 'else (caar exp))
                    (member key (caar exp)))
                (begintail (cadr exp) env)
                (casetail key (cdr exp) env))))

(define (caseform exp env)
        (let ((key (eval (car exp))))
             (casetail key (cdr exp) env)))

(define (eval exp env)
        (cond ((null? exp) exp)
              ((eq? #t exp) exp)
              ((symbol? exp) (get exp env))
              ((not (pair? exp)) exp)
              (else (cond ((eq? 'and        (car exp)) (andform        (cdr exp) env))
                          ((eq? 'begin      (car exp)) (beginform      (cdr exp) env))
                          ((eq? 'cond       (car exp)) (condform       (cdr exp) env))
                          ((eq? 'if         (car exp)) (ifform         (cdr exp) env))
                          ((eq? 'or         (car exp)) (orform         (cdr exp) env))
                          ((eq? 'quasiquote (car exp)) (quasiquoteform (cdr exp) env))
                          ((eq? 'quote      (car exp)) (quoteform      (cdr exp) env))
                          ((eq? 'set!       (car exp)) (setform        (cdr exp) env))
                          ((eq? 'unless     (car exp)) (unlessform     (cdr exp) env))
                          ((eq? 'when       (car exp)) (whenform       (cdr exp) env))
                          ((eq? 'while      (car exp)) (whileform      (cdr exp) env))
                          (else (let ((fun (eval (car exp) env))
                                      (args (evlis (cdr exp) env)))
                                     (apply fun args)))))))

(define display-primitive display)

(undefine 'display)

(define (display s)
    (cond ((null? s) #f)
          ((pair? s)
           (begin (write-char #\()
                  (while s
                         (if (pair? s)
                             (begin (display (car s))
                                    (set! s (cdr s))
                                    (when s (space)))
                             (begin (display-primitive dot)
                                    (write-char #\space)
                                    (display-primitive s)
                                    (set! s #f))))
                   (write-char #\))))
          (else (display-primitive s))))

(define (repl)
        (let ((env (null-environment)))
             (while #t
                    (let ((exp (read)))
                         (if (and (pair? exp) (eq? 'define (car exp)))
                             (set! env (defineform exp env))
                             (let ((value (eval exp env)))
                                  (display value)
                                  (unless (eq? void value)
                                          (newline))))))))

