This directory holds the expected answers (reference SMT-LIB2) for each test case.

- Files correspond 1:1 with inputs/ and cases.md (e.g. 01_simple_int_bounds.smt2).
- Use for manual comparison or automation: after running parseNL, compare output (e.g. artifacts/emit.smt2) with the matching .smt2.
- When comparing: declaration order, parentheses, and whitespace may differ; semantic equivalence is sufficient (same logic, same variable and constraint semantics, same objective).
