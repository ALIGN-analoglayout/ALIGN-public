#!/bin/bash

# Resetting counters
make coverage-init

# Run tests
(cd PnRDB && ./unit_tests --gtest_output=xml:junit.xml)
(cd cap_placer && ./unit_tests --gtest_output=xml:junit.xml)
(cd placer && ./unit_tests --gtest_output=xml:junit.xml)
(cd router && ./unit_tests --gtest_output=xml:junit.xml)
./pnr_compiler ./testcase_example switched_capacitor_filter.lef switched_capacitor_filter.v switched_capacitor_filter.map layers.json switched_capacitor_filter 2 0 > PnR.log

# Make coverage report
make coverage-report
