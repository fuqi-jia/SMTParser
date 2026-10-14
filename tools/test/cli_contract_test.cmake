# CTest script verifying somt-convert's stream and exit-code contract.
#
# This is a CMake script test (`cmake -P`), not a compiled C++ test: the
# property under test -- what the *process* writes to stdout/stderr and what
# it exits with -- lives entirely in main()'s I/O, so a unit test linking a
# library function cannot observe it. Driving the actual built binary is the
# only way to catch a regression here, which is exactly why this property
# was previously guarded only by a paragraph in a report file that CI never
# reads.
#
# This also sidesteps the NDEBUG/assert() trap that has bitten this project
# before (Task 12): a script test has no assert() and no NDEBUG-conditional
# compilation to accidentally compile out under a default Release build --
# every check below is an unconditional message(FATAL_ERROR ...), so there is
# no separate "did the compile flags keep the check alive" question to get
# wrong.
#
# Usage:
#   cmake -DEXE=<path-to-somt-convert> -DOK_FILE=<path> -DREJECT_FILE=<path>
#         -DILL_SORTED_FILE=<path> -DWORK_DIR=<scratch dir>
#         -P cli_contract_test.cmake
#
# Two rejecting fixtures, not one, and the reason matters. REJECT_FILE fails in
# the MiniZinc tokenizer, so its diagnostic never goes near the Parser -- and
# the Parser was the only thing that ever wrote a diagnostic to stdout. The
# stdout-purity check below therefore could not fail for as long as that was
# its only failing input. ILL_SORTED_FILE parses cleanly and is refused later,
# on the path that used to print to stdout and then abort.

foreach(var EXE OK_FILE REJECT_FILE ILL_SORTED_FILE WORK_DIR)
    if(NOT DEFINED ${var})
        message(FATAL_ERROR "${var} must be defined (pass -D${var}=...)")
    endif()
endforeach()

file(MAKE_DIRECTORY "${WORK_DIR}")

function(read_file out_var path)
    if(EXISTS "${path}")
        file(READ "${path}" content)
    else()
        set(content "")
    endif()
    set(${out_var} "${content}" PARENT_SCOPE)
endfunction()

function(check_empty label path)
    read_file(content "${path}")
    string(LENGTH "${content}" len)
    if(NOT len EQUAL 0)
        message(FATAL_ERROR "${label}: expected empty, got ${len} bytes:\n${content}")
    endif()
endfunction()

function(check_not_empty label path)
    read_file(content "${path}")
    string(LENGTH "${content}" len)
    if(len EQUAL 0)
        message(FATAL_ERROR "${label}: expected non-empty, but it is empty")
    endif()
endfunction()

function(check_contains label path needle)
    read_file(content "${path}")
    string(FIND "${content}" "${needle}" pos)
    if(pos EQUAL -1)
        message(FATAL_ERROR "${label}: expected to contain '${needle}':\n${content}")
    endif()
endfunction()

function(check_not_contains label path needle)
    read_file(content "${path}")
    string(FIND "${content}" "${needle}" pos)
    if(NOT pos EQUAL -1)
        message(FATAL_ERROR "${label}: unexpectedly contains '${needle}':\n${content}")
    endif()
endfunction()

function(check_exit label actual expected)
    if(NOT actual EQUAL expected)
        message(FATAL_ERROR "${label}: expected exit ${expected}, got ${actual}")
    endif()
endfunction()

# GOMT is the public dialect name; the older proposal spelling stays an alias.
set(gomt_input "${WORK_DIR}/gomt_goal.smt2")
file(WRITE "${gomt_input}" "(declare-const x Int)(assert (>= x 2))(minimize x)(check-sat)(get-objectives)\n")
foreach(gomt_dialect "gomt" "smtlib-omt-2025")
    set(gomt_out "${WORK_DIR}/${gomt_dialect}_stdout.txt")
    execute_process(
        COMMAND "${EXE}" "--from" "smtlib2" "--dialect" "${gomt_dialect}" "${gomt_input}"
        OUTPUT_FILE "${gomt_out}"
        RESULT_VARIABLE gomt_result)
    check_exit("${gomt_dialect} objective export" "${gomt_result}" 0)
    check_contains("GOMT objective" "${gomt_out}" "(define-objective ")
    check_contains("GOMT query" "${gomt_out}" "(optimize-sat ")
    check_contains("GOMT response" "${gomt_out}" "(get-value (")
    check_not_contains("no duplicate ordinary query" "${gomt_out}" "(check-sat)")
endforeach()
file(READ "${WORK_DIR}/gomt_stdout.txt" gomt_text)
file(READ "${WORK_DIR}/smtlib-omt-2025_stdout.txt" legacy_gomt_text)
if(NOT gomt_text STREQUAL legacy_gomt_text)
    message(FATAL_ERROR "GOMT alias changes emitted script")
endif()

# --- Case 1: a successful translation writes SMT-LIB to stdout only. -------
# This is the property the evaluation harness depends on: stdout must pipe
# straight into a solver with no filtering step.
set(ok_out "${WORK_DIR}/ok_stdout.txt")
set(ok_err "${WORK_DIR}/ok_stderr.txt")
execute_process(
    COMMAND "${EXE}" "${OK_FILE}"
    OUTPUT_FILE "${ok_out}"
    ERROR_FILE "${ok_err}"
    RESULT_VARIABLE ok_result)
check_exit("successful translation" "${ok_result}" 0)
check_not_empty("successful translation stdout" "${ok_out}")
check_contains("successful translation stdout" "${ok_out}" "(set-logic")
check_contains("successful translation stdout" "${ok_out}" "declare-fun")
check_not_contains("successful translation stdout" "${ok_out}" "error:")
check_empty("successful translation stderr" "${ok_err}")

# --- Case 2: a rejected input writes nothing to stdout at all. -------------
# This is the case the success-only fixture cannot exercise: trivial.mzn
# never raises a diagnostic, so a diagnostic-to-stdout regression is only
# observable here, where translation fails and a diagnostic definitely
# exists. If it leaked to stdout, this file would be non-empty.
set(reject_out "${WORK_DIR}/reject_stdout.txt")
set(reject_err "${WORK_DIR}/reject_stderr.txt")
execute_process(
    COMMAND "${EXE}" "${REJECT_FILE}"
    OUTPUT_FILE "${reject_out}"
    ERROR_FILE "${reject_err}"
    RESULT_VARIABLE reject_result)
check_exit("rejected input" "${reject_result}" 1)
check_empty("rejected input stdout" "${reject_out}")
check_not_empty("rejected input stderr" "${reject_err}")
check_contains("rejected input stderr" "${reject_err}" "E_PARSE")

# --- Case 3: a --report path that cannot be opened is an I/O fault (exit 3),
# not a translation failure (exit 1) -- the input above translates fine, so
# a caller must be able to tell "your report path is bad" from "your
# benchmark could not be translated". -----------------------------------
set(bad_report "${WORK_DIR}/no-such-directory/report.json")
set(report_out "${WORK_DIR}/report_stdout.txt")
set(report_err "${WORK_DIR}/report_stderr.txt")
execute_process(
    COMMAND "${EXE}" "--report" "${bad_report}" "${OK_FILE}"
    OUTPUT_FILE "${report_out}"
    ERROR_FILE "${report_err}"
    RESULT_VARIABLE report_result)
check_exit("unwritable --report path" "${report_result}" 3)
check_empty("unwritable --report path stdout" "${report_out}")
check_not_empty("unwritable --report path stderr" "${report_err}")

# --- Case 4: a model that parses but does not type-check. ------------------
# The path that used to pollute stdout. Before Uir::Hir::typeCheck existed,
# this input reached Parser::mkAdd, which printed
#   error: Kind mismatch of command "Type mismatch in add" in line 0.
# to *stdout* -- where it survived 2>/dev/null and was spliced into the
# SMT-LIB stream -- and then aborted with SIGABRT (exit 134).
set(ill_out "${WORK_DIR}/ill_stdout.txt")
set(ill_err "${WORK_DIR}/ill_stderr.txt")
execute_process(
    COMMAND "${EXE}" "${ILL_SORTED_FILE}"
    OUTPUT_FILE "${ill_out}"
    ERROR_FILE "${ill_err}"
    RESULT_VARIABLE ill_result)
check_exit("ill-sorted input" "${ill_result}" 1)
check_empty("ill-sorted input stdout" "${ill_out}")
check_not_empty("ill-sorted input stderr" "${ill_err}")
check_contains("ill-sorted input stderr" "${ill_err}" "E_TYPE")
# The diagnostic names a location, so a benchmark author can find the term.
check_contains("ill-sorted input stderr" "${ill_err}" "ill_sorted.mzn:")

# --- Case 5: a mistyped id is a usage error, not a translation outcome. ----
# `--from nosuch` exited 1 with E_UNSUPPORTED_CONSTRUCT -- the bucket that is
# supposed to measure how much of each *language* we cover -- so a typo in a
# batch script inflated the number the evaluation reports. `--profile nosuch`
# did the same to E_PASS_PIPELINE. Both are now exit 2, like `--dialect
# bogus` already was.
foreach(bad_option "--from" "--profile")
    set(typo_out "${WORK_DIR}/typo_stdout.txt")
    set(typo_err "${WORK_DIR}/typo_stderr.txt")
    execute_process(
        COMMAND "${EXE}" "${bad_option}" "nosuch" "${OK_FILE}"
        OUTPUT_FILE "${typo_out}"
        ERROR_FILE "${typo_err}"
        RESULT_VARIABLE typo_result)
    check_exit("${bad_option} typo" "${typo_result}" 2)
    check_empty("${bad_option} typo stdout" "${typo_out}")
    check_not_empty("${bad_option} typo stderr" "${typo_err}")
    # Naming the bucket would mean it had been counted.
    check_not_contains("${bad_option} typo stderr" "${typo_err}" "E_UNSUPPORTED_CONSTRUCT")
    check_not_contains("${bad_option} typo stderr" "${typo_err}" "E_PASS_PIPELINE")
endforeach()

# An option that swallows the next option as its value translated the file
# under a language nobody asked for.
set(swallow_out "${WORK_DIR}/swallow_stdout.txt")
set(swallow_err "${WORK_DIR}/swallow_stderr.txt")
execute_process(
    COMMAND "${EXE}" "--from" "--profile" "${OK_FILE}"
    OUTPUT_FILE "${swallow_out}"
    ERROR_FILE "${swallow_err}"
    RESULT_VARIABLE swallow_result)
check_exit("option as option value" "${swallow_result}" 2)
check_empty("option as option value stdout" "${swallow_out}")

# --- Case 6: "--" ends the options, and "-" is stdin. ----------------------
# language.h documents main_path == "-" as stdin; the CLI rejected it as an
# unknown option, and had no "--" either, so a file named "-lead.mzn" was
# unreachable except as "./-lead.mzn".
set(dashdash_out "${WORK_DIR}/dashdash_stdout.txt")
set(dashdash_err "${WORK_DIR}/dashdash_stderr.txt")
execute_process(
    COMMAND "${EXE}" "--" "${OK_FILE}"
    OUTPUT_FILE "${dashdash_out}"
    ERROR_FILE "${dashdash_err}"
    RESULT_VARIABLE dashdash_result)
check_exit("-- end of options" "${dashdash_result}" 0)
check_contains("-- end of options stdout" "${dashdash_out}" "(set-logic")
check_empty("-- end of options stderr" "${dashdash_err}")

set(stdin_out "${WORK_DIR}/stdin_stdout.txt")
set(stdin_err "${WORK_DIR}/stdin_stderr.txt")
execute_process(
    COMMAND "${EXE}" "--from" "minizinc" "-"
    INPUT_FILE "${OK_FILE}"
    OUTPUT_FILE "${stdin_out}"
    ERROR_FILE "${stdin_err}"
    RESULT_VARIABLE stdin_result)
check_exit("stdin input" "${stdin_result}" 0)
check_contains("stdin input stdout" "${stdin_out}" "(set-logic")
check_empty("stdin input stderr" "${stdin_err}")

# Detection is by file extension and stdin has none, so "-" without --from is
# a usage error rather than a silently mis-detected language.
set(stdin_nofrom_out "${WORK_DIR}/stdin_nofrom_stdout.txt")
set(stdin_nofrom_err "${WORK_DIR}/stdin_nofrom_stderr.txt")
execute_process(
    COMMAND "${EXE}" "-"
    INPUT_FILE "${OK_FILE}"
    OUTPUT_FILE "${stdin_nofrom_out}"
    ERROR_FILE "${stdin_nofrom_err}"
    RESULT_VARIABLE stdin_nofrom_result)
check_exit("stdin without --from" "${stdin_nofrom_result}" 2)
check_empty("stdin without --from stdout" "${stdin_nofrom_out}")

# Streaming must retain the requested objective dialect.
set(opt_file "${WORK_DIR}/objective.smt2")
file(WRITE "${opt_file}" "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (>= x 0))\n(minimize x)\n(check-sat)\n")
foreach(dialect "smtlib-omt-2025" "z3")
    set(opt_out "${WORK_DIR}/objective_${dialect}.txt")
    set(opt_err "${WORK_DIR}/objective_${dialect}.err")
    execute_process(COMMAND "${EXE}" --dialect "${dialect}" "${opt_file}"
        OUTPUT_FILE "${opt_out}" ERROR_FILE "${opt_err}"
        RESULT_VARIABLE opt_result)
    check_exit("${dialect} objective" "${opt_result}" 0)
    check_empty("${dialect} objective stderr" "${opt_err}")
    if(dialect STREQUAL "z3")
        check_contains("Z3 objective" "${opt_out}" "(minimize ")
        check_not_contains("Z3 objective" "${opt_out}" "(define-objective")
    else()
        check_contains("SMT-LIB objective" "${opt_out}" "(define-objective")
    endif()
endforeach()

# /dev/full opens successfully but rejects writes. Small outputs can stay
# buffered until flush/close, so checking open() alone falsely reports success.
if(UNIX AND EXISTS "/dev/full")
    set(full_err "${WORK_DIR}/full_stderr.txt")
    execute_process(COMMAND "${EXE}" "${OK_FILE}"
        OUTPUT_FILE /dev/full ERROR_FILE "${full_err}"
        RESULT_VARIABLE full_result)
    check_exit("unwritable stdout" "${full_result}" 3)
    check_contains("unwritable stdout diagnostic" "${full_err}" "cannot write SMT-LIB output")

    set(module_file "${WORK_DIR}/library.aag")
    file(WRITE "${module_file}" "aag 0 0 0 0 0\n")
    execute_process(COMMAND "${EXE}" --module "${module_file}"
        OUTPUT_FILE /dev/full ERROR_FILE "${full_err}"
        RESULT_VARIABLE full_result)
    check_exit("unwritable module stdout" "${full_result}" 3)
    check_contains("unwritable module stdout diagnostic" "${full_err}" "cannot write SMT-LIB output")

    set(full_out "${WORK_DIR}/full_report_stdout.txt")
    execute_process(COMMAND "${EXE}" --report /dev/full "${OK_FILE}"
        OUTPUT_FILE "${full_out}" ERROR_FILE "${full_err}"
        RESULT_VARIABLE full_result)
    check_exit("unwritable open report" "${full_result}" 3)
    check_empty("unwritable open report stdout" "${full_out}")
    check_contains("unwritable open report diagnostic" "${full_err}" "cannot write report")
endif()

message(STATUS "somt-convert CLI stream/exit-code contract: PASS")
