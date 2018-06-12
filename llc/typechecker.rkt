#lang racket

(require "llc.rkt")

(provide (all-defined-out))

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

; We arbitrarily look in Γ first, then in Δ; this shouldn't matter since we
; assume all hypotheses (across both contexts) have been labelled uniquely.

; ..............................................................................
(define (infer-λ-lin Γ Δ x T b)
  (let-values ([(T2 Δ1) (infer Γ (cons (cons x T) Δ) b)])
    (if (member x (map car Δ1))
        (error 'infer-λ-lin "Unused argument ~a" x)
        (if T2 (values (LinArr T T2) Δ) ☠))))

; ..............................................................................
(define (infer-linapply Γ Δ e1 e2)
  (let*-values ([(Tapp Δ1) (infer Γ Δ e1)]
                [(Targ Δ2) (infer Γ Δ1 e2)])
    (if (and Tapp Targ (LinArr? Tapp) (equal? (LinArr-Arg Tapp) Targ))
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
          (if (or (member p1 (map car Δ2)) (member p2 (map car Δ2)))
              (error 'infer-tensor-case "Unused arguments ~a or ~a" p1 p2)
              (if C (values C Δ2) ☠)))
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
          (if (or (member x (map car Δ1)) (member y (map car Δ2)))
              (error 'infer-either-case "Unused arguments ~a or ~a" x y)
              (if (and Cl Cr (equal? Cl Cr) (empty? Δ1) (empty? Δ2))
                  (values Cl empty)
                  ☠)))        
        ☠)))

; Note that this rule initially splits the context to typecheck s, but then has
; to check both branches using the same linear context.