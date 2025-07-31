; Test file for function definitions including recursive functions
; This file tests all function-related features from test_functions.cpp

; Set logic for quantifier-free non-linear integer arithmetic
(set-logic QF_NIA)

; ========================================
; Section 1: Basic Function Declarations
; ========================================

; Declare a function with no arguments (constant)
(declare-fun c () Int)

; Declare a unary function f: Int -> Int
(declare-fun f (Int) Int)

; Declare a binary function g: Int x Int -> Int
(declare-fun g (Int Int) Int)

; Declare a predicate function p: Int x Int -> Bool
(declare-fun p (Int Int) Bool)

; Declare a function with mixed argument types h: Int x Real x Bool -> Real
(declare-fun h (Int Real Bool) Real)

; ========================================
; Section 2: Basic Function Definitions
; ========================================

; Basic function definition using define-fun
(define-fun inc ((x Int)) Int (+ x 1))

; Test function application
(assert (= (inc 5) 6))

; More complex function definition
(define-fun max2 ((x Int) (y Int)) Int (ite (>= x y) x y))

; Test max2 function
(assert (= (max2 10 20) 20))
(assert (= (max2 15 8) 15))

; Function that doubles a number
(define-fun double ((x Int)) Int (* x 2))

; Test double function
(assert (= (double 5) 10))
(assert (= (double 0) 0))

; ========================================
; Section 3: Recursive Function Definitions
; ========================================

; Recursive function definition using define-fun-rec
(define-fun-rec factorial ((n Int)) Int 
  (ite (<= n 1) 1 (* n (factorial (- n 1)))))

; Test factorial function
(assert (= (factorial 5) 120))
(assert (= (factorial 0) 1))
(assert (= (factorial 1) 1))
(assert (= (factorial 3) 6))

; Another recursive function: Fibonacci
(define-fun-rec fib ((n Int)) Int
  (ite (<= n 1) n (+ (fib (- n 1)) (fib (- n 2)))))

; Test Fibonacci function
(assert (= (fib 0) 0))
(assert (= (fib 1) 1))
(assert (= (fib 2) 1))
(assert (= (fib 3) 2))
(assert (= (fib 4) 3))
(assert (= (fib 5) 5))

; ========================================
; Section 4: Mutually Recursive Functions
; ========================================

; Mutually recursive functions using define-funs-rec
(define-funs-rec 
  ((is-even ((n Int)) Bool) 
   (is-odd ((n Int)) Bool)) 
  ((ite (= n 0) true (is-odd (- n 1))) 
   (ite (= n 0) false (is-even (- n 1)))))

; Test mutually recursive functions
(assert (= (is-even 4) true))
(assert (= (is-odd 3) true))
(assert (= (is-even 7) false))
(assert (= (is-odd 8) false))
(assert (= (is-even 0) true))
(assert (= (is-odd 0) false))

; ========================================
; Section 5: Function Combinations
; ========================================

; Test combinations of functions
(assert (= (inc (factorial 3)) 7))  ; inc(factorial(3)) = inc(6) = 7
(assert (= (max2 (factorial 3) (inc 10)) 11))  ; max2(6, 11) = 11
(assert (= (double (inc 5)) 12))  ; double(inc(5)) = double(6) = 12
(assert (= (inc (double 5)) 11))  ; inc(double(5)) = inc(10) = 11

; Test with recursive and non-recursive function combinations
(assert (= (max2 (fib 5) (factorial 3)) 6))  ; max2(5, 6) = 6
(assert (= (inc (fib 4)) 4))  ; inc(fib(4)) = inc(3) = 4

; ========================================
; Section 6: Function Constraints and Properties
; ========================================

; Assert properties about declared functions
(assert (= (f 0) 0))
(assert (= (f 1) 1))

; Test that our defined functions satisfy expected properties
(assert (> (inc 5) 5))  ; inc always increases
(assert (>= (max2 10 5) 10))  ; max2 returns at least the first argument when it's larger
(assert (>= (max2 5 10) 10))  ; max2 returns at least the second argument when it's larger

; Test factorial properties
(assert (> (factorial 5) (factorial 4)))  ; factorial is increasing for positive values
(assert (= (factorial 4) (* 4 (factorial 3))))  ; factorial property

; Test even/odd properties
(assert (= (is-even 2) true))
(assert (= (is-odd 1) true))
(assert (not (= (is-even 3) (is-odd 3))))  ; a number can't be both even and odd

; ========================================
; Section 7: Complex Function Applications
; ========================================

; Create some complex expressions using multiple function calls
(assert (= (max2 (inc (double 3)) (factorial 3)) 7))  ; max2(inc(6), 6) = max2(7, 6) = 7

; Test nested recursive calls
(assert (= (factorial (inc 3)) 24))  ; factorial(inc(3)) = factorial(4) = 24

; Test with mutually recursive functions
(assert (= (is-even (double 3)) true))  ; is-even(6) = true
(assert (= (is-odd (inc (double 2))) true))  ; is-odd(inc(4)) = is-odd(5) = true

; ========================================
; Section 8: Edge Cases and Boundary Conditions
; ========================================

; Test edge cases for factorial
(assert (= (factorial 0) (factorial 1)))  ; Both should be 1

; Test edge cases for even/odd
(assert (= (is-even 0) (not (is-odd 0))))

; Test with negative numbers where applicable
; Note: Some functions may not be defined for negative inputs

; ========================================
; Final Check
; ========================================

; Check satisfiability of all constraints
(check-sat)
