; Whitespace and formatting edge cases
(set-logic QF_LIA)

; ========================================
; Section 1: Unusual Spacing
; ========================================

; No spaces around parentheses
(declare-const x Int)
(assert(= x 1))

; Extra spaces everywhere
(declare-const    y     Int   )
(assert   (   =    y     2   )   )

; Tabs instead of spaces
(declare-const	z	Int)
(assert	(=	z	3))

; Mixed tabs and spaces
(declare-const 	  w   	Int)
(assert	 (=  	w 	  4)   )

; ========================================
; Section 2: Line Break Edge Cases
; ========================================

; Expression split across multiple lines
(assert 
  (= 
    (+ 
      x 
      y
    ) 
    (+ 
      z 
      w
    )
  )
)

; Very long line
(assert (= (+ x y z w x y z w x y z w x y z w x y z w x y z w x y z w x y z w x y z w x y z w) 100))

; Multiple blank lines between statements


(declare-const a Int)


(assert (= a 5))



; ========================================
; Section 3: Comments and Whitespace
; ========================================

; Comment at end of line
(declare-const b Int) ; this is a comment

; Comment with unusual characters
(declare-const c Int) ; comment with symbols: !@#$%^&*()_+-={}[]|\"':;?/>.<,

; Multiple semicolons
(declare-const d Int) ;;; multiple semicolons ;;;

; Empty comment
(declare-const e Int) ;

; ========================================
; Section 4: Minimal Spacing Tests
; ========================================

; Minimal valid spacing
(declare-const minimal Int)(assert(= minimal 0))(check-sat)

; No spacing in numbers
(assert(=(+ 1 2 3)(- 10 4)))

; ========================================
; Section 5: Unicode Whitespace
; ========================================

; Non-breaking space (if supported)
(declare-const non_break Int)
(assert (= non_break 42))

(exit)