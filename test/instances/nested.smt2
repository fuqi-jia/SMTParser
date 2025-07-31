; Deep nesting tests that stress parsers
(set-logic QF_LIA)

; ========================================
; Section 1: Deeply Nested Arithmetic
; ========================================

(declare-const x Int)

; Deep nesting with same operator
(assert (= x (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ 1 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)))

; Deep nesting with alternating operators  
(assert (= x (- (+ (- (+ (- (+ (- (+ (- (+ 10 1) 1) 1) 1) 1) 1) 1) 1) 1) 1)))

; Deep nesting with multiplication
(assert (= x (* (* (* (* (* 2 2) 2) 2) 2) 2)))

; ========================================
; Section 2: Deeply Nested Boolean Logic
; ========================================

(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)

; Deep boolean nesting
(assert (= p (and (or (and (or (and p q) r) p) (and q r)) (or p (and q r)))))

; Deep implication chain
(assert (=> (=> (=> (=> p q) r) p) (and p q)))

; Deep ite nesting
(assert (= x (ite p (ite q (ite r 1 2) 3) (ite q 4 (ite r 5 6)))))

; ========================================
; Section 3: Deeply Nested Function Calls
; ========================================

; Function definition for nesting test
(define-fun f ((n Int)) Int (+ n 1))

; Deep function call nesting
(assert (= x (f (f (f (f (f (f (f (f (f (f 0))))))))))))

; ========================================
; Section 4: Deeply Nested Quantifiers
; ========================================

; Note: This would require QF to be removed, but included for completeness
; (assert (forall ((a Int)) (exists ((b Int)) (forall ((c Int)) (exists ((d Int)) (= (+ a b) (+ c d)))))))

; ========================================
; Section 5: Complex Nested Structure
; ========================================

; Combining multiple types of nesting
(assert 
  (and 
    (= (+ (- (* (+ 1 2) 3) 4) 5) x)
    (or 
      (and (> x 0) (< x 100))
      (and (< x 0) (> x (- 100)))
    )
    (ite 
      (= x (f (f (f 0))))
      (> (* x x) (+ x x))
      (< (- x x) (div x (ite (= x 0) 1 x)))
    )
  )
)

(check-sat)
(exit)