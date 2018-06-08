#lang racket

(require rackunit
         rackunit/log)

(provide (all-defined-out))

;;->>--->>--------->>--------------------------------------------------------------------------------->>
;; Type definitions

; Some base types for testing purposes.
(define B 'buddy)
(define Z 'zooey)

(struct LinArr (Arg Result) #:transparent)
(struct Valid (A) #:transparent)
(struct Tensor (A B) #:transparent)
(struct Ampersand (A B) #:transparent)
(struct Either (A B) #:transparent)

;;->>--->>--------->>--------------------------------------------------------------------------------->>
;; Term definitions
(define (var v) `(var ,v))
(define (λlin x T b) `(linlam ,x ,T ,b))
(define (linapply e1 e2) `(linapply ,e1 ,e2))
(define (! e) `(valid ,e))
(define (case! s x u) `(case-valid ,s ,x ,u))
(define (⊗ e1 e2) `(pair ,e1 ,e2))
(define (case⊗ s p1 p2 v) `(case-both ,s ,p1 ,p2 ,v))
(define (& e1 e2) `(choice ,e1 ,e2))
(define (fst e) `(fst ,e))
(define (snd e) `(snd ,e))
(define (inl B e) `(inl ,B ,e))
(define (inr A e) `(inr ,A ,e))
(define (case⊕ s left v right w) `(case-or ,s ,left ,v ,right ,w))

; One difference in the above from the Wadler paper is that the ⊕ injections are
; annotated with the 'missing' type to make inference easier (and to ensure that
; expressions have a unique type).

;;->>--->>--------->>--------------------------------------------------------------------------------->>
;; Inference functions

; Using #f to indicate type inference failure.
(define-syntax ☠ (λ (stx) (syntax-case stx () [_ #'(values #f empty)])))

; Each of the inference functions defined here produce two values: a type (or #f),
; and a linear context that contains all of the still unconsumed resources.
; Thus, for a term to typecheck, 1) the type returned must not be #f, and 2) the
; linear context must ultimately be empty.

(define (typecheck Γ Δ e expected)
  (let-values ([(t Δ-) (infer Γ Δ e)])
    (and (empty? Δ-) (equal? t expected))))


; The idea for the inferences follows the main part of what's described in section
; 6.2 of https://www.cs.cmu.edu/~fp/courses/linear/handouts/linear.pdf. Each function
; consumes two contexts: Γ and Δ. Γ contains the unrestricted (intuitionistic)
; hypotheses, while Δ contains the linear ones. [Note that Wadler in his paper
; does not use "Γ" and "Δ" to distinguish hypotheses of different types this way.]
; For multiplicative connectives, Δ must be split amongst the premises, so rather
; than non-deterministically determining this split we first pass all the
; hypotheses to the first premise, then the leftover ones to the next premise,
; and so on. If the term is well-typed, we should end up with no linear
; hypotheses unconsumed.
;
; For the additive connectives, the premises must be checked in the same
; context, so we pass Δ whole to each (parallel) premise. Note that the complication
; with checking the ⊕ unit that the above book mentions thankfully doesn't matter
; here as Wadler's LLC doesn't contain such a term. :]

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
    [`(inl ,B ,e) (infer-inl Γ Δ B e)]
    [`(inr ,A ,e) (infer-inr Γ Δ A e)]
    [`(case-or ,s ,left ,v ,right ,w) (infer-either-case Γ Δ s left v right w)]
    [_ (error "Unknown expression" expr)]))

; ..............................................................................
(define (infer-var Γ Δ e)
  (define (lookup ctx var)
    (findf (λ (v) (equal? var (car v))) ctx))
  (define (remove ctx var)
    (filter (λ (v) (not (equal? var (car v)))) ctx))
  (let ([v (lookup Γ e)])
       (if v
           (values (cdr v) Δ)
           (let ([v (lookup Δ e)])
             (if v (values (cdr v) (remove Δ e)) ☠)))))

; ..............................................................................
(define (infer-λ-lin Γ Δ x T b)
  (let-values ([(T2 Δ1) (infer Γ (cons (cons x T) Δ) b)])
    (if (and T2 (equal? Δ Δ1)) (values (LinArr T T2) Δ) ☠)))

; ..............................................................................
(define (infer-linapply Γ Δ e1 e2)
  (let*-values ([(Tapp Δ1) (infer Γ Δ e1)]
                [(Targ Δ2) (infer Γ Δ1 e2)])
    (if (and Tapp Targ (empty? Δ2) (LinArr? Tapp) (equal? (LinArr-Arg Tapp) Targ))
        (values (LinArr-Result Tapp) empty)
        ☠)))

; ..............................................................................
(define (infer-valid Γ Δ e)
  (let-values ([(T Δ1) (infer Γ empty e)])
    (if T (values (Valid T) Δ) ☠)))

; The ! connective is related to "validity" from modal logic, where we said a
; proposition was valid if it could be inferred using only valid hypotheses.
; Here, "valid" means it consumes only unrestricted hypotheses (see the empty
; passed in as the linear context to infer).

; ..............................................................................
(define (infer-valid-case Γ Δ s x u)
  (let-values ([(T Δ1) (infer Γ Δ s)])
    (if (and T (Valid? T))
        (let-values ([(B Δ2) (infer (cons (cons x (Valid-A T)) Γ) Δ1 u)])
          (if (and B (empty? Δ2)) (values B Δ2) ☠))
        ☠)))

; ..............................................................................
(define (infer-tensor Γ Δ e1 e2)
  (let*-values ([(T1 Δ1) (infer Γ Δ e1)]
                [(T2 Δ2) (infer Γ Δ1 e2)])
    (if (and T1 T2 (empty? Δ2))
        (values (Tensor T1 T2) Δ2)
        ☠)))

; ..............................................................................
(define (infer-tensor-case Γ Δ s p1 p2 v)
  (let-values ([(T1 Δ1) (infer Γ Δ s)])
    (if (and T1 (Tensor? T1))
        (let*-values ([(A) (Tensor-A T1)]
                      [(B) (Tensor-B T1)]
                      [(C Δ2) (infer Γ (append (list (cons p1 A) (cons p2 B)) Δ1) v)])
          (if (and C (empty? Δ2)) (values C Δ2)
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
(define (infer-inl Γ Δ B e)
  (let-values ([(T Δ1) (infer Γ Δ e)])
    (if T (values (Either T B) Δ1) ☠)))

; ..............................................................................
(define (infer-inr Γ Δ A e)
  (let-values ([(T Δ1) (infer Γ Δ e)])
    (if T (values (Either A T) Δ1) ☠)))

; ..............................................................................
(define (infer-either-case Γ Δ s x v y w)
  (let-values ([(T Δ1) (infer Γ Δ s)])
    (if (and T (Either? T))
        (let-values ([(Cl Δ1) (infer Γ (cons (cons x (Either-A T)) Δ1) v)]
                     [(Cr Δ2) (infer Γ (cons (cons y (Either-B T)) Δ1) w)])
          (if (and Cl Cr (equal? Cl Cr) (empty? Δ1) (empty? Δ2))
              (values Cl empty)
              ☠))        
        ☠)))

; Note that this rule initially splits the context to typecheck s, but then has
; to check both branches using the same linear context.

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

; . ; x:B ⊢ x:B
;----------------------
; . ; . ⊢ λ(x:B).x : B
(check-true (typecheck empty empty (λlin (var 'x) B (var 'x)) (LinArr B B)))

; . ; x:B, w:B !⊢ x:B
;------------------------
; . ; x:B !⊢ λ(w:B).w : B
(check-false (typecheck empty linctx3 (λlin (var 'w) B (var 'w)) (LinArr B B)))

; y:Z ; . ⊢ y:Z     y:Z ; x:B !⊢ y:Z
; y:Z ; x:B !⊢ y ⊗ y): Z ⊗ Z
;-------------------------------------
; y:Z ; . !⊢ λ(x:B).y ⊗ y : B ⊗ B
(check-false (typecheck intctx2 empty (λlin (var 'x) B (⊗ (var 'y) (var 'y)))
                        (LinArr B (Tensor Z Z))))

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

(check-true (typecheck empty linctx8 (case⊗ (⊗ (var 'x) (var 'y)) 'x 'y (⊗ (var 'y) (var 'x)))
                       (Tensor Z B)))

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
(define linctx12 (list (cons 'x B)))
(check-true (typecheck empty linctx12 
                       (case⊕ (inr B (var 'x)) 
                         'l (linapply (λlin (var 'x) B (var 'x)) (var 'l))
                         'r (linapply (λlin (var 'x) B (var 'x)) (var 'r)))
                       B))

(test-log #:display? #t #:exit? #t)