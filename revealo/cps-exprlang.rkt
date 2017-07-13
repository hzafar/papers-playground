#lang racket

(define (evaluate expr env k)
  (printf "~a\t~a\n" expr env)
  (match expr
    [(? val? e) (k e)]
    [`(succ ,expr) (evaluate expr env (λ (v) (evaluate `(succ ,v) env k)))]
    [`(ap (lam ,x ,body) ,(? val? arg)) (evaluate (substitute arg x body) env k)]
    [`(ap ,(? val? fn) ,arg) (evaluate arg env (λ (v) (evaluate `(ap ,fn ,v) env k)))]
    [`(ap ,fn ,arg) (evaluate fn env (λ (v) (evaluate `(ap ,v ,arg) env k)))]
    [`(rec ,(? z? e) ,e0 ,x ,y ,e1) (evaluate e0 env k)]
    [`(rec ,(? val? (list 'succ expr)) ,e0 ,x ,y ,e1)
     (evaluate (substitute `(rec ,expr ,e0 ,x ,y ,e1) y (substitute expr x e1)) env k)]
    [`(rec ,e ,e0 ,x ,y ,e1) (evaluate e env (λ (v) (evaluate `(rec ,v ,e0 ,x ,y ,e1) env k)))]
    [(? eof-object? e) (k e)]
    [`(custom-eval ,evaldef) ((eval evaldef) expr env k)]
    [`(custom-cont ,k-) (evaluate expr env (eval k-))]
    [`(,operator ,operand) ;; add new forms to the language! (almost)
     (if (hash-ref env operator #f)
         (evaluate `(ap ,(hash-ref env operator) ,operand) env k)
         (begin
           (printf "Enter an evaluator for ~a\n" expr)
           (let ([new-eval (eval (read))])
             (printf "Enter a continuation-generator:\n")
             (let ([new-cont ((eval (read)) expr env k)])
               (new-eval expr env new-cont)))))]))

(define (K env)
  (λ (v)
    (printf ">>> ~a\n" v)
    (if (eof-object? v)
        (printf "done!\n")
        (evaluate (read) env (K env)))))

(define (start-repl)
  (define env0 (make-hash))
  (evaluate (read) env0 (K env0)))

;; Auxilliary functions
(define (z? e) (and (number? e) (zero? e)))

(define (val? e)
  (match e
    [(or (? z? _)
         `(succ ,(? val? _))
         `(lam ,_ ,_)) #t]
    [_ #f]))

(define (substitute val var expr)
  (cond [(empty? expr) empty]
        [(equal? var expr) val]
        [(or (symbol? expr) (string? expr) (number? expr)) expr]
        [(equal? var (first expr)) (cons val (substitute val var (rest expr)))] 
        [(cons? (first expr)) (cons (substitute val var (first expr)) (substitute val var (rest expr)))]
        [else (cons (first expr) (substitute val var (rest expr)))]))

(define (to-number e)
  (match e
    [(? z? _) 0]
    [`(succ ,expr) (add1 (to-number expr))]))