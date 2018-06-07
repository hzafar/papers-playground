#lang racket

(require rackunit
         rackunit/log)

(provide (all-defined-out))

;;->>--->>--------->>--------------------------------------------------------------------------------->>
;; Type definitions
(define B '(buddy))
(define Z '(zooey))
(struct LinArr (Arg Result) #:transparent)
(struct Valid (A) #:transparent)
(struct Tensor (A B) #:transparent)
(struct Ampersand (A B) #:transparent)
;(struct Either (A B) #:transparent)

;;->>--->>--------->>--------------------------------------------------------------------------------->>
;; Term definitions
(define (var v) `(var ,v))
(define (λlin x T b) `(linlam ,x ,T ,b))
(define (linapply e1 e2) `(linapply ,e1 ,e2))
(define (! e) `(valid ,e))
(define (case! s x u) `(case-valid ,s ,x u))
(define (⊗ e1 e2) `(pair ,e1 ,e2))
(define (case⊗ s p1 p2 v) `(case-both ,s ,p1 ,p2 ,v))
(define (& e1 e2) `(choice ,e1 ,e2))
(define (fst e) `(fst ,e))
(define (snd e) `(snd ,e))
;(define (inl e) `(inl ,e))
;(define (inr e) `(inr ,e))
;(define (case⊕ s left v right w) `(case-or ,s ,left ,v ,right ,w))

;;->>--->>--------->>--------------------------------------------------------------------------------->>
;; Inference functions

(define-syntax ☠ (λ (stx) (syntax-case stx () [_ #'(values #f empty)])))

(define (infer Γ Δ expr)
  (match expr
    [`(var ,v) (infer-var Γ Δ v)]
    [`(linlam (var ,x) ,T ,b) (infer-λ-lin Γ Δ x T b)]
    [`(linapply ,e1 ,e2) (infer-linapply Γ Δ e1 e2)]
    [`(valid ,e) (infer-valid Γ Δ e)]
    [`(case-valid ,s ,x ,u) (infer-valid-case Γ Δ s x u)]
    [`(pair ,e1 ,e2) (infer-tensor Γ Δ e1 e2)]
    [`(case-both ,s ,p1 ,p2 ,v) (infer-tensor-case Γ Δ s p1 p2 v)]
    [`(choice ,e1 ,e2) (infer-ampersand Γ Δ e1 e2)]
    [`(fst ,e) (infer-choice-fst Γ Δ e)]
    [`(snd ,e) (infer-choice-snd Γ Δ e)]
;    [`(inl ,e) (infer-inl G D e)]
;    [`(inr ,e) (infer-inr G D e)]
;    [`(case⊕ ,s ,left ,v ,right ,y ,w) (infer-either-case G D s left v right y w)]
    [_ (error "Unknown expression" expr)]))

; ..............................................................................
(define (infer-var Γ Δ e)
  (define (lookup ctx var)
    (findf (λ (v) (equal? var (car v))) ctx))
  (define (remove ctx var)
    (filter (λ (v) (not (equal? var (car v)))) ctx))
  (cond [(empty? Δ) ; unrestricted var
         (let ([v (lookup Γ e)])
           (if v (values (cdr v) Δ) ☠))]
        [else ; linear var
         (let ([v (lookup Δ e)])
           (if v (values (cdr v) (remove Δ e)) ☠))]))

; ..............................................................................
(define (infer-λ-lin Γ Δ x T b)
  (let-values ([(T2 Δ1) (infer Γ (cons (cons x T) Δ) b)])
    (if T2 (values (LinArr T T2) Δ) ☠)))

; ..............................................................................
(define (infer-linapply Γ Δ e1 e2)
  (let*-values ([(Tapp Δ1) (infer Γ Δ e1)]
                [(Targ Δ2) (infer Γ Δ1 e2)])
    (if (and Tapp Targ (equal? (LinArr-Result Tapp) Targ))
        (values (LinArr-Result Tapp) Δ2)
        ☠)))

; ..............................................................................
(define (infer-valid Γ Δ e)
  (let-values ([(T Δ1) (infer Γ empty e)]) ; want to only use intuitionistic hyps
    (if T (values (Valid T) Δ) ☠)))

; ..............................................................................
(define (infer-valid-case Γ Δ s x u)
  (let-values ([(T Δ1) (infer Γ Δ s)])
    (if (and T (Valid? T))
        (let-values ([(B Δ2) (infer Γ (cons (cons x (Valid-A T)) Δ1) u)])
          (if B (values B Δ2) ☠))
        ☠)))

; ..............................................................................
(define (infer-tensor Γ Δ e1 e2)
  (let*-values ([(T1 Δ1) (infer Γ Δ e1)]
                [(T2 Δ2) (infer Γ Δ1 e2)])
    (if (and T1 T2)
        (values (Tensor T1 T2) Δ2)
        ☠)))

; ..............................................................................
(define (infer-tensor-case Γ Δ s p1 p2 v)
  (let-values ([(T1 Δ1) (infer Γ Δ s)])
    (if (and T1 (Tensor? T1))
        (let*-values ([(A) (Tensor-A T1)]
                      [(B) (Tensor-B T1)]
                      [(C Δ2) (infer Γ (append (list (cons p1 A) (cons p2 B)) Δ1) v)])
          (if C (values C Δ)
              ☠))
        ☠)))

; ..............................................................................
(define (infer-ampersand Γ Δ e1 e2)
  (let-values ([(T1 Δ1) (infer Γ Δ e1)]
               [(T2 Δ2) (infer Γ Δ e2)])
    (if (and T1 T2)
        (values (Ampersand T1 T2) (append Δ1 Δ2))
        ☠)))

; ..............................................................................
(define (infer-choice-fst Γ Δ e)
  (let-values ([(T Δ1) (infer Γ Δ e)])
    (if (and T (Ampersand? T))
        (values (Ampersand-A T) Δ1)
        ☠)))

; ..............................................................................
(define (infer-choice-snd Γ Δ e)
  (let-values ([(T Δ1) (infer Γ Δ e)])
    (if (and T (Ampersand? T))
        (values (Ampersand-B T) Δ1)
        ☠)))

; ..............................................................................
;(define (infer-inl G D e)
;  (let-values ([(T G1 D1) (infer G D e)])
;    (if T (values (Either T #f) G1 D1) ☠)))

; ..............................................................................
;(define (infer-inr G D e)
;  (let-values ([(T G1 D1) (infer G D e)])
;    (if T (values (Either #f T) G1 D1) ☠)))

; ..............................................................................
;(define (infer-either-case G D s left v right y w)
;  (let-values ([(T G1 D1) (infer G D s)])
;    (if (and T (Tensor? T))
;        ((let-values ([()
;        ☠))

;;->>--->>--------->>--------------------------------------------------------------------------------->>
;; Tests

(define (typecheck Γ Δ e)
  (let-values ([(t Δ-) (infer Γ Δ e)])
    (and (empty? Δ-) ; linear hypothesis is satisfied
         t))) ; type is not #f

(define linctx1 (list (cons 'x B) (cons 'y B) (cons 'z Z)))
(define linctx2 (list (cons 'x Z)))
(define linctx3 (list (cons 'x B)))
(define linctx4 (list (cons 'thing1 Z) (cons 'thing2 B)))

(check-equal? (typecheck (list (cons 'v B)) empty (var 'v)) B)
(check-equal? (typecheck empty empty (var 'x)) #f)
(check-equal? (typecheck empty linctx1 (var 'x)) #f)
(check-equal? (typecheck empty linctx2 (var 'x)) Z)
(check-equal? (typecheck empty empty (λlin (var 'x) B (var 'x))) (LinArr B B))
(check-equal? (typecheck empty linctx2 (λlin (var 'x) B (var 'x))) #f)
(check-equal? (typecheck empty linctx2 (linapply (λlin (var 'y) B (var 'y)) (var 'x))) #f)
(check-equal? (typecheck empty linctx3 (linapply (λlin (var 'y) B (var 'y)) (var 'x))) B);
(check-equal? (typecheck empty linctx4 (⊗ (var 'thing1) (var 'thing2))) (Tensor Z B))
(check-equal? (typecheck empty linctx2 (& (var 'x) (var 'x))) (Ampersand Z Z))
(check-equal? (typecheck (list (cons 'v B)) (list (cons 'u Z)) (⊗ (var 'u) (var 'v))) (Tensor Z B))
(check-equal? (typecheck (list (cons 'v B)) empty (⊗ (var 'v) (var 'v))) (Tensor B B))
(check-equal? (typecheck empty (list (cons 'v B)) (⊗ (var 'v) (var 'v))) #f)

(test-log #:display? #t #:exit? #t)