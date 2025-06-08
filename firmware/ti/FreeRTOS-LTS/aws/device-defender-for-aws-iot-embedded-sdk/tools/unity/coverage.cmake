cmake_minimum_required( VERSION 3.13 )
set( BINARY_DIR ${CMAKE_BINARY_DIR} )

# Reset coverage counters.
execute_process( COMMAND lcov --directory ${CMAKE_BINARY_DIR}
                         --base-directory ${CMAKE_BINARY_DIR}
                         --zerocounters )

# Create directory for results.
execute_process( COMMAND mkdir -p  ${CMAKE_BINARY_DIR}/coverage )

# Generate "baseline" coverage data with zero coverage for every instrumented
# line. This is later combined with the coverage data from test run to ensure
# that the percentage of total lines covered is correct even when not all source
# code files were loaded during the test.
execute_process( COMMAND lcov --directory ${CMAKE_BINARY_DIR}
                         --base-directory ${CMAKE_BINARY_DIR}
                         --initial
                         --capture
                         --rc lcov_branch_coverage=1
                         --rc genhtml_branch_coverage=1
                         --output-file=${CMAKE_BINARY_DIR}/base_coverage.info )

# Capture all the test binaries.
file( GLOB files "${CMAKE_BINARY_DIR}/bin/tests/*" )

# Create an empty report file.
set( REPORT_FILE ${CMAKE_BINARY_DIR}/utest_report.txt )
file( WRITE ${REPORT_FILE} "" )

# Execute all test binaries and capture all the output in the report file.
foreach( testname ${files} )
    get_filename_component( test ${testname} NAME_WLE )
    message( "Running ${testname}" )
    execute_process( COMMAND ${testname} OUTPUT_FILE ${CMAKE_BINARY_DIR}/${test}_out.txt )

    # Append the test run output to the report file.
    file( READ ${CMAKE_BINARY_DIR}/${test}_out.txt CONTENTS )
    file( APPEND ${REPORT_FILE} "${CONTENTS}" )
endforeach()

# Generate Junit style xml output.
execute_process( COMMAND ruby
                         ${UNITY_DIR}/auto/parse_output.rb
                         -xml ${REPORT_FILE}
                         WORKING_DIRECTORY ${CMAKE_BINARY_DIR} )

# Capture coverage data after test run.
execute_process( COMMAND lcov --capture
                         --rc lcov_branch_coverage=1
                         --rc genhtml_branch_coverage=1
                         --base-directory ${CMAKE_BINARY_DIR}
                         --directory ${CMAKE_BINARY_DIR}
                         --output-file ${CMAKE_BINARY_DIR}/second_coverage.info )

# Combine baseline coverage data (zeros) with the coverage data from test run.
execute_process( COMMAND lcov --base-directory ${CMAKE_BINARY_DIR}
                         --directory ${CMAKE_BINARY_DIR}
                         --add-tracefile ${CMAKE_BINARY_DIR}/base_coverage.info
                         --add-tracefile ${CMAKE_BINARY_DIR}/second_coverage.info
                         --output-file ${CMAKE_BINARY_DIR}/coverage.info
                         --no-external
                         --rc lcov_branch_coverage=1 )

# Generate HTML Report.
execute_process( COMMAND genhtml --rc lcov_branch_coverage=1
                         --branch-coverage
                         --output-directory ${CMAKE_BINARY_DIR}/coverage
                         ${CMAKE_BINARY_DIR}/coverage.info )
