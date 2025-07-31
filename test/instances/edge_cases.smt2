; Edge cases that commonly trigger parser bugs
(set-logic QF_LIA)

; ========================================
; Section 1: Unusual Number Formats
; ========================================

; Large numbers
(declare-const huge Int)
(assert (= huge 123456789012345678901234567890))

; Negative zero
(declare-const neg_zero Int)
(assert (= neg_zero (- 0)))

; Multiple signs
(declare-const x Int)
(assert (= x (+ (- (- 5)))))

; ========================================
; Section 2: Unusual Identifier Cases
; ========================================

; Single character identifiers
(declare-const a Int)
(declare-const z Int)
(declare-const _ Int)

; Numbers at start/end of identifiers
(declare-const var1 Int)
(declare-const var_2_test Int)

; Special characters in quoted identifiers
(declare-const |weird name with spaces| Int)
(declare-const |name-with-dashes| Int)
(declare-const |name.with.dots| Int)
(declare-const |name$with$dollars| Int)

; ========================================
; Section 3: Empty and Minimal Cases
; ========================================

; Minimal assertion
(assert true)

; Assertion with just false
(assert (not false))

; ========================================
; Section 4: Boundary Operator Cases
; ========================================

; Single operand where multiple expected
(declare-const single Int)
(assert (= (+ single) single))

; Many operands
(declare-const many Int)
(assert (= many (+ 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15)))

; Nested same operators
(assert (= (+ (+ (+ 1 2) 3) 4) 10))

(check-sat)
(exit)