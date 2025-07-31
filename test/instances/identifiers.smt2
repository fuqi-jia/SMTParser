; Identifier edge cases that can break parsers
(set-logic QF_LIA)

; ========================================
; Section 1: Unusual Simple Identifiers
; ========================================

; Single character identifiers
(declare-const a Int)
(declare-const Z Int)
(declare-const _ Int)

; Identifiers with numbers
(declare-const a1 Int)
(declare-const var123 Int)
(declare-const x_2_y_3 Int)

; ========================================
; Section 2: Quoted Identifiers
; ========================================

; Spaces in identifiers
(declare-const |my variable| Int)
(declare-const |  spaces  | Int)

; Special characters
(declare-const |name-with-dashes| Int)
(declare-const |name.with.dots| Int)
(declare-const |name$with$symbols| Int)
(declare-const |name@with@at| Int)
(declare-const |name#with#hash| Int)
(declare-const |name%with%percent| Int)

; Keywords as identifiers
(declare-const |assert| Int)
(declare-const |declare-const| Int)
(declare-const |set-logic| Int)
(declare-const |check-sat| Int)

; Numbers as identifiers
(declare-const |123| Int)
(declare-const |0| Int)
(declare-const |-456| Int)

; Empty-like identifiers
(declare-const |_| Int)
(declare-const |__| Int)

; ========================================
; Section 3: Very Long Identifiers
; ========================================

; Extremely long identifier
(declare-const very_very_very_very_very_very_very_very_very_very_long_identifier_name_that_goes_on_and_on_and_on_and_on_and_on Int)

; Long quoted identifier
(declare-const |this is an extremely long quoted identifier with many words and spaces that should test the parser limits for handling long names| Int)

; ========================================
; Section 4: Unicode and Special Cases
; ========================================

; Unicode characters (if supported)
(declare-const café Int)
(declare-const naïve Int)
(declare-const résumé Int)

; Mixed case sensitivity tests
(declare-const TestVar Int)
(declare-const testvar Int)
(declare-const TESTVAR Int)

; ========================================
; Section 5: Usage Tests
; ========================================

; Use all the special identifiers
(assert (= a 1))
(assert (= |my variable| 2))
(assert (= |assert| 3))
(assert (= very_very_very_very_very_very_very_very_very_very_long_identifier_name_that_goes_on_and_on_and_on_and_on_and_on 4))
(assert (= café 5))

; Complex expression with unusual identifiers
(assert 
  (= 
    (+ |my variable| |name-with-dashes| |123|)
    (- very_very_very_very_very_very_very_very_very_very_long_identifier_name_that_goes_on_and_on_and_on_and_on_and_on a)
  )
)

(check-sat)
(exit)