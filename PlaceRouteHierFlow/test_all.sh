#!/bin/bash

# Resetting counters
lcov --directory . --zerocounters

# Run tests
(cd PnRDB && ./unit_tests --gtest_output=xml:junit.xml)
(cd cap_placer && ./unit_tests --gtest_output=xml:junit.xml)
(cd placer && ./unit_tests --gtest_output=xml:junit.xml)
(cd router && ./unit_tests --gtest_output=xml:junit.xml)
./pnr_compiler ./testcase_example switched_capacitor_filter.lef switched_capacitor_filter.v switched_capacitor_filter.map layers.json switched_capacitor_filter 2 0 > PnR.log

# Capturing the current coverage state to a file
lcov --directory . --capture --output-file coverage.info

# Get HTML output
genhtml coverage.info --output-directory htmlcov


