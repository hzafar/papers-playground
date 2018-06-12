#lang racket

(require
  "llc.rkt"
  "typechecker.rkt"
  rackunit
  rackunit/log)

;;->>--->>--------->>--------------------------------------------------------------------------------->>
;; Tests

; ------------------------------------------------------------------------------
(define linctx1 (list (cons 'x B) (cons 'y B) (cons 'z Z)))
(define linctx2 (list (cons 'x Z)))
(define intctx1 (list (cons 'v B)))

; v:B ; . ⊢ v:B
(check-true (typecheck intctx1 empty (var 'v) B))

; . ; . !⊢ x:B
(check-false (typecheck empty empty (var 'x) B))

; . ; x:B, y:B, z:Z !⊢ x:B
(check-false (typecheck empty linctx1 (var 'x) B))

; . ; x:Z ⊢ x:Z
(check-true (typecheck empty linctx2 (var 'x) Z))

; ------------------------------------------------------------------------------
(define intctx2 (list (cons 'y Z)))
(define linctx3 (list (cons 'x B)))

(check-true (typecheck empty empty (λlin (var 'x) B (var 'x)) (LinArr B B)))

(check-false (typecheck empty linctx3 (λlin (var 'w) B (var 'w)) (LinArr B B)))

(check-exn exn:fail?
  (lambda () (typecheck intctx2 empty (λlin (var 'x) B (⊗ (var 'y) (var 'y)))
                        (LinArr B (Tensor Z Z)))))

; ------------------------------------------------------------------------------
(define linctx4 (list (cons 'x Z)))
(define linctx5 (list (cons 'x B)))

(check-false (typecheck empty linctx4 (linapply (λlin (var 'y) B (var 'y)) (var 'x)) B))
(check-true (typecheck empty linctx5 (linapply (λlin (var 'y) B (var 'y)) (var 'x)) B))

; ------------------------------------------------------------------------------
; Not sure if I understand these ones fully tbh
(define intctx3 (list (cons 'x Z)))

(check-true (typecheck intctx3 empty (! (var 'x)) (Valid Z)))
(check-true (typecheck intctx3 empty (case! (! (var 'x)) 'x (var 'x)) Z))

; ------------------------------------------------------------------------------
(define linctx6 (list (cons 'thing1 Z) (cons 'thing2 B)))
(define linctx7 (list (cons 'v B)))
(define intctx4 (list (cons 'u Z)))
(define intctx5 (list (cons 'v B)))

(check-true (typecheck empty linctx6 (⊗ (var 'thing1) (var 'thing2)) (Tensor Z B)))
(check-true (typecheck intctx4 linctx7 (⊗ (var 'u) (var 'v)) (Tensor Z B)))
(check-true (typecheck intctx5 empty (⊗ (var 'v) (var 'v)) (Tensor B B)))
(check-false (typecheck empty linctx7 (⊗ (var 'v) (var 'v)) (Tensor B B)))

; ------------------------------------------------------------------------------
(define linctx8 (list (cons 'x B) (cons 'y Z)))

(check-exn exn:fail?
  (lambda () (typecheck empty linctx8 (case⊗ (⊗ (var 'x) (var 'y)) 'p1 'p2 (var 'p1)) B)))

; ------------------------------------------------------------------------------
(define linctx9 (list (cons 'x Z)))

(check-true (typecheck empty linctx9 (& (var 'x) (var 'x)) (Ampersand Z Z)))

; ------------------------------------------------------------------------------
(define intctx6 (list (cons 'x B) (cons 'y Z)))
(define linctx10 (list (cons 'w Z) (cons 'u B)))

(check-true (typecheck intctx6 empty (fst (& (var 'x) (var 'y))) B))
(check-true (typecheck intctx6 empty (snd (& (var 'x) (var 'y))) Z))
(check-true (typecheck empty linctx10 (fst (& (⊗ (var 'w) (var 'u)) (⊗ (var 'u) (var 'w))))
                       (Tensor Z B)))

; ------------------------------------------------------------------------------
(define linctx11 (list (cons 'x B)))

(check-true (typecheck empty linctx11 (inl Z (var 'x)) (Either B Z)))
(check-true (typecheck empty linctx11 (inr Z (var 'x)) (Either Z B)))

; ------------------------------------------------------------------------------
(define intctx7 (list (cons 'w Z)))
(define linctx12 (list (cons 'x B)))
(check-exn exn:fail?
  (lambda() (typecheck intctx7 linctx12 
                       (case⊕ (inr B (var 'x)) 
                         'l (linapply (λlin (var 'x) B (var 'x)) (var 'l))
                         'r (var 'w))
                       Z)))

(test-log #:display? #t #:exit? #t)