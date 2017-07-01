#lang racket

(require racket/trace)

(define meta-cons
  (λ (k)
    (λ (mk)
      (λ (theta)
        ((theta k) mk)))))

(define K->BF
  (curry (kl e r k)
         (if (= (length e) 1)
             (C denotation (first e) r
                (lambda (v) (C shift-down (kl v) k)))
             (wrong (list
                     "K->BF: wrong number of args"
                     e)))))

(define tower
  (letrec
      ([loop
        (λ (n)
          (λ (theta)
            ((theta (R-E-P n)) (loop (add1 n)))))])
    (loop 0)))

(trace tower)

(define (f x)
  f)

(define Y
  (λ (f)
    (let ([d (λ (x)
               (f (λ (arg) (C x x arg))))])
      (d d))))

(trace Y)

(define (C . aloex)
  (cond [(empty? (cdr aloex)) (car aloex)]
        [else (C (cons ((car aloex) (cadr aloex)) (cddr aloex)))]))

(C (list (λ (a) (λ (b) (+ a b)))
         4 5))

(define prompt&read
  (lambda (prompt)
    (print prompt) (print "-> ") (read)))
(define print&prompt
  (lambda (prompt v)
    (printf "~a~a~a\n" prompt "::" v) prompt))

(define-syntax (curry stx)
  (syntax-case stx ()
    [(curry (i) b ...) #'(lambda (i) b ...)]
    [(curry (i j ...) b ...)
     #'(lambda (i)
         (curry (j ...) b ...))]))

(define R-E-P
  (lambda (prompt)
    (Y (curry (loop v)
              ((prompt&read (print&prompt prompt v))
               (lambda (v)
                 (if (eof-object? v)
                     (lambda (mk) '---done---)
                     (C denotation v global-env loop))))))))

(define make-reifier
  (curry (bf e r k)
         (shift-up (bf (list e (U->BF r) (K->BF k))))))

(define U->BF
  (curry (rl e r k)
         (if (= (length e) 1)
             (C denotation (first e) r
                (lambda (var) (C rl var k)))
             (wrong (list
                     "U->BF: wrong number of args"
                     e)))))

(define NAMESPACE (variable-reference->namespace (#%variable-reference)))

(define primop-name-table
  (list 'car 'cdr 'cons 'eq? 'atom? 'symbol?
        'null? 'not 'add1 'sub1 'zero? '+ '- '*
        'set-mcar! 'set-mcdr!
        'print 'length 'read 'newline 'reset
        'make-cell 'deref-cell 'set-cell!
        'ef 'readloop 'make-reifier))

(define reset 'garbage)

(define ef
  (lambda (bool x y)
    (if bool x y)))

(define readloop
  (lambda (prompt)
    (K->BF (R-E-P prompt))))

(define host-value
  (lambda (id) (eval id NAMESPACE)))

(define deref-cell car)
(define make-cell (lambda (x) (cons x '())))
(define set-cell!
  (lambda (x y) (set-mcar! x y) y))

(define denotation-of-application 
  (curry (e r k)
         (C denotation (first e) r
            (lambda (f) (C f (rest e) r k)))))

(define denotation-of-abstraction (curry (e r k)
                                         (k (F->BF
                                             (lambda (v*)
                                               (C denotation (third e)
                                                  (extend r (second e) v*)))))))

(define F->BF (curry (fun e r k)
                     (C Y (curry (eval-args e k) (if (null? e) (k '())
                                                     (C denotation (first e) r (lambda (v)
                                                                                 (C eval-args (rest e) (lambda (w)
                                                                                                         (k (cons v w)))))))) e (curry (v* mk) (C fun v* k mk)))))

(define denotation-of-identifier (curry (e r k)
                                        (C r e
                                           (lambda (cell)
                                             (let ([v (deref-cell cell)]) (if (eq? v 'UNASSIGNED)
                                                                              (wrong (list "Brown: unbound id " e)) (k v )))))))

(define (atom? e)
  (or (symbol? e)
      (number? e)
      (string? e)
      (char? e)))

(define denotation (lambda (e)
                     (cond
                       [(atom? e) (denotation-of-identifier e)]
                       [(eq? (first e) 'lambda) (denotation-of-abstraction e)] [else (denotation-of-application e)])))

(define initk
  (λ (v)
    (λ (mk)
      (mk (λ (k) (k v))))))


(define global-env 'undef)

(define id->BF
  (let ([host->F
         (curry (f v* k) (k (apply f v*)))])
    (lambda (x)
      (F->BF (host->F (host-value x))))))

(define terminate-level
  (lambda (v)
    (shift-up (lambda (k) (k v)))))

(define meaning
  (curry (erk)
         (shift-down
          (C denotation
             (first erk)
             (BF->U (second erk))
             (BF->K (third erk))))))

(define rib-lookup
  (lambda (id names cells sk fk)
    (C Y (curry (lookup names cells)
                (cond
                  [(null? names) (fk)]
                  [(eq? (first names) id) (sk (first cells))]
                  [else (C lookup (rest names) (rest cells))]))
       names cells)))

(define extend
  (lambda (r names vals)
    (if (= (length names) (length vals))
        (let ([cells (map make-cell vals)])
          (curry (name k)
                 (rib-lookup name names cells k
                             (lambda () (C r name k)))))
        (curry (name k)
               (wrong (list "extend:"
                            "Formals: " names
                            "Actuals: " vals))))))

(define wrong
  (curry (v mk)
         (writeln "wrong: " v)
         (C terminate-level 'wrong mk)))


(define shift-down
  (lambda (d)
    (lambda (k)
      (lambda (mk)
        (d ((meta-cons k) mk))))))

(define shift-up
  (lambda (theta)
    (lambda (mk)
      (mk theta))))

(define BF->U
  (let ([z '
           (v)])
    (curry (bf v)
           (C bf z
              (extend global-env z (list v))))))

(define BF->K
  (let ([z '(v)])
    (curry (bf v)
           (shift-up
            (C bf z
               (extend global-env z (list v)))))))

(define boot-global-env
  (let ([id->F-cell (lambda (x) (make-cell (id->BF x)))])
    (lambda ()
      (let ([initnames
             (append
              (list 'nil 't 'wrong 'meaning)
              primop-name-table)]
            [initcells
             (append
              (map make-cell
                   (list null 't
                         (K->BF terminate-level)
                         (F->BF meaning)))
              (map id->F-cell
                   primop-name-table))])
        (define global-env-1
          (curry (id k)
                 (rib-lookup
                  id initnames initcells k
                  (lambda ()
                    (let
                        ([c (make-cell 'UNASSIGNED)])
                      (set! initnames (cons id initnames))
                      (set! initcells (cons c initcells))
                      (k c))))))
        (set! global-env global-env-1)))))

(trace R-E-P)
(trace f)

(boot-global-env)
