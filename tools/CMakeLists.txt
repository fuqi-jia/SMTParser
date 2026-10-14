add_executable(somt-convert somt-convert/main.cpp)
target_compile_features(somt-convert PRIVATE cxx_std_17)
target_link_libraries(somt-convert PRIVATE SOMTParser::languages)
install(TARGETS somt-convert RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR})

# The public-corpus PDDL driver must use the same core and language library as
# somt-convert, including in qualification runs of newly added HIR APIs.
add_executable(pddl_translate pddl_translate.cpp)
target_compile_features(pddl_translate PRIVATE cxx_std_17)
target_link_libraries(pddl_translate PRIVATE SOMTParser::languages)
install(TARGETS pddl_translate RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR})

# somt-convert's stdout/stderr/exit-code contract is what the evaluation
# harness pipes straight into a solver -- guard it with a real CTest rather
# than a manual procedure. This whole directory is only added when
# SOMTPARSER_BUILD_TOOLS built the binary in the first place (see the
# top-level CMakeLists.txt), so the somt-convert target always exists here;
# still gate on SOMTPARSER_BUILD_TESTS, matching languages/CMakeLists.txt's
# own convention, so a tools-only configure does not also require tests.
if(SOMTPARSER_BUILD_TESTS)
    add_test(NAME SOMTParser.test_somt_convert_cli_contract
        COMMAND "${CMAKE_COMMAND}"
                -DEXE=$<TARGET_FILE:somt-convert>
                -DOK_FILE=${PROJECT_SOURCE_DIR}/languages/minizinc/instances/ok/trivial.mzn
                -DREJECT_FILE=${PROJECT_SOURCE_DIR}/languages/minizinc/instances/reject/bad_syntax.mzn
                -DILL_SORTED_FILE=${PROJECT_SOURCE_DIR}/languages/minizinc/instances/reject/ill_sorted.mzn
                -DWORK_DIR=${CMAKE_CURRENT_BINARY_DIR}/cli_contract_work
                -P "${CMAKE_CURRENT_SOURCE_DIR}/test/cli_contract_test.cmake")
    set_tests_properties(SOMTParser.test_somt_convert_cli_contract PROPERTIES
        WORKING_DIRECTORY "${PROJECT_SOURCE_DIR}")
endif()

# Optional helpers for semantic regression tests; these are not installed CLIs.
if(SOMTPARSER_BUILD_TESTS)
    # Independent exact certificate; does not link the frontend or HIR implementation.
    add_executable(somt-wcnf-certificate semantic_checks/wcnf_exact_certificate.cpp)
    target_compile_features(somt-wcnf-certificate PRIVATE cxx_std_17)

    # Whole-module parser bridge; exact source/cost checking is a separate tool.
    add_executable(somt-wcnf-load-bridge semantic_checks/wcnf_load_bridge.cpp)
    target_compile_features(somt-wcnf-load-bridge PRIVATE cxx_std_17)
endif()
