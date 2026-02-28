(set-info :smt-lib-version 2.6)
(set-logic QF_AX)
(set-info :source |
Translated from old SVC processor verification benchmarks.  Contact Clark
Barrett at barrett@cs.nyu.edu for more information.

This benchmark was automatically translated into SMT-LIB format from
CVC format using CVC Lite
|)
(set-info :category "crafted")
(set-info :status unsat)

;; --- Simple (Array Int Int) example (original ax.smt2) ---
(declare-const a0 (Array Int Int))
(declare-const b0 (Array Int Int))
(assert (= (select a0 1) 10))
(assert (= (select a0 2) 20))
(assert (= b0 (store a0 3 30)))
(assert (= (select b0 3) 30))
(assert (= (select b0 1) (select a0 1)))

;; --- (Array Index Element) with custom sorts (from read5.smt2) ---
(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun a () Index)
(declare-fun aaa () Index)
(declare-fun aa () Index)
(declare-fun S () (Array Index Element))
(declare-fun vvv () Element)
(declare-fun v () Element)
(declare-fun vv () Element)
(declare-fun bbb () Index)
(declare-fun www () Element)
(declare-fun bb () Index)
(declare-fun ww () Element)
(declare-fun b () Index)
(declare-fun w () Element)
(declare-fun SS () (Array Index Element))
(assert (let ((?v_3 (ite (= a aa) false true)) (?v_4 (ite (= aa aaa) false true)) (?v_1 (store (store (store S a v) aa vv) aaa vvv)) (?v_0 (store S aaa vvv)) (?v_2 (store S aa vv))) (not (ite (ite (ite (ite (= a aaa) false true) (ite ?v_3 ?v_4 false) false) (ite (= (store (store ?v_0 a v) aa vv) ?v_1) (ite (= (store (store ?v_0 aa vv) a v) ?v_1) (ite (= (store (store ?v_2 a v) aaa vvv) ?v_1) (= (store (store ?v_2 aaa vvv) a v) ?v_1) false) false) false) true) (ite (ite (= ?v_1 (store (store (store S bbb www) bb ww) b w)) (ite (ite ?v_3 (ite ?v_4 (ite (ite (= aa b) false true) (ite (ite (= aa bb) false true) (ite (= aa bbb) false true) false) false) false) false) (= (select S aa) vv) true) true) (ite (= S (store SS a v)) (= S (store SS a (select S a))) true) false) false))))

(check-sat)
(exit)
