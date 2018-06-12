#lang racket

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
