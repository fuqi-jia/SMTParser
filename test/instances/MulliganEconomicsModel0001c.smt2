(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :source |
Generated by: Casey Mulligan, Russell Bradford, James H. Davenport, Matthew England, and ZakTonks
Generated on: 2018-04-19
Generator: TheoryGuru
Application: Supply-Demand: Determinants of quantity, counterexample set
Target solver: Z3
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")
(set-info :status sat)

; Code written by TheoryGuru
; Mulligan model #0001
;   is part of the example library included in "Quantifier Elimination for Reasoning in Economics" April 2018
;   by Mulligan, Bradford, Davenport, England, and Tonks
;   available at bathpaper.economicreasoning.com .
; Economics background for this and other examples is provided at examples.economicreasoning.com .

(declare-fun v1 () Real)
(declare-fun v2 () Real)
(declare-fun v3 () Real)
(declare-fun v4 () Real)
(declare-fun v5 () Real)
(declare-fun v6 () Real)
(declare-fun v7 () Real)
(declare-fun v8 () Real)

; input assumptions
(define-fun assumptions () Bool (and 
(= (+ (* v1 v5) (* v3 v7)) v4)
(= (+ (* v2 v6) (* v3 v8)) v4)
(= v5 1)
(= v6 1)
(< v7 0)
(> v8 0)
(> v4 0)
))

; input hypothesis
(define-fun hypothesis () Bool
(> v1 0)
)

(assert assumptions)
(assert (not hypothesis))
(minimize v1 )
(check-sat) ; checking the existence of a counterexample to assumptions => hypothesis
(get-objectives)
(exit)