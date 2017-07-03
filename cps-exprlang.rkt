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

(define (evaluate e k)
  (match e
       [(? val? v) (k v)]
       [`(+ ,(? val? e1) ,(? val? e2)) (k (+ e1 e2))]
       [`(+ ,(? val? e1) ,e2)
        (evaluate e2 (λ (v) (evaluate `(+ ,e1 ,v) k)))]
       [`(+ ,e1 ,e2)
        (evaluate e1 (λ (v) (evaluate `(+ ,v ,e2) k)))]
       [`(let ,x ,(? val? e1) ,e2) (evaluate (substitute e1 x e2) k)]
       [`(let ,x ,e1 ,e2)
        (evaluate e1 (λ (v) (evaluate `(let ,x ,v ,e2) k)))]
       [(? eof-object? eof) (k eof)]))

(define (K n)
  (λ (v)
    (printf "(~a)))> ~a\n" n v)
    (if (eof-object? v)
        (displayln "done!")
        (evaluate (read) (K n)))))

(define (start-evaluator)
  (evaluate (read) (K 0)))