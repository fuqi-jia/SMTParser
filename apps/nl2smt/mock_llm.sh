#!/bin/sh
# Mock LLM: ignore arguments and print fixed SMT-LIB2. Use in tests: NL2SMT_LLM_CMD="bash /path/to/mock_llm.sh"
printf '%s\n' '(set-logic QF_LIA)'
printf '%s\n' '(declare-fun x () Int)'
printf '%s\n' '(declare-fun y () Int)'
printf '%s\n' '(assert (> x 0))'
printf '%s\n' '(assert (< (+ x y) 5))'
printf '%s\n' '(minimize x)'
printf '%s\n' '(check-sat)'
printf '%s\n' '(exit)'
