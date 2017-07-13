#lang racket

(define (val? e)
  (or (number? e) (string? e)))

(define (substitute val var expr)
  (cond [(empty? expr) empty]
        [(equal? var expr) val]
        [(or (symbol? expr) (string? expr) (number? expr)) expr]
        [(equal? var (first expr)) (cons val (substitute val var (rest expr)))] 
        [(cons? (first expr)) (cons (substitute val var (first expr)) (substitute val var (rest expr)))]
        [else (cons (first expr) (substitute val var (rest expr)))]))

(define (meta-evaluate e k mk)
  (match e
    [(? val? v) (k v)]
    [`(+ ,(? val? e1) ,(? val? e2)) (k (+ e1 e2))]
    [`(+ ,(? val? e1) ,e2)
     (meta-evaluate e2 (λ (v) (meta-evaluate `(+ ,e1 ,v) k mk)) mk)]
    [`(+ ,e1 ,e2)
     (meta-evaluate e1 (λ (v) (meta-evaluate `(+ ,v ,e2) k mk)) mk)]
    [`(let ,x ,(? val? e1) ,e2) (meta-evaluate (substitute e1 x e2) k mk)]
    [`(let ,x ,e1 ,e2)
     (meta-evaluate e1 (λ (v) (meta-evaluate `(let ,x ,v ,e2) k mk)) mk)]
    [(? eof-object? eof) (k eof)]
    [x (mk x k)]))

(define (K n)
  (λ (v)
    (printf "(~a)))> ~a\n" n v)
    (if (eof-object? v)
        (displayln "done!")
        (meta-evaluate (read) (K n) (MK (add1 n))))))

(define (MK n)
  (λ (v k)
    (printf "You've reached metalevel ~a!\n" n)
    (printf "Enter a definition for ~a\n" v)
    (meta-evaluate (read) k (MK (add1 n)))))

(define (start-meta-evaluator)
  (meta-evaluate (read) (K 0) (MK 1)))