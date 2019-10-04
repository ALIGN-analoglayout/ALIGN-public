#! /bin/csh

./pnr_compiler ./testcase_example switched_capacitor_filter.lef switched_capacitor_filter.v switched_capacitor_filter.map layers.json switched_capacitor_filter 2 0 | tee log
#./pnr_compiler ./testcase_latest2 sc.lef sc_block.v sc.map NO.rul switched_capacitor_filter 1 0 | tee log
#./pnr_compiler ./testcase_small sc.lef sc_block.v sc.map NO.rul switched_capacitor_filter 1 0 | tee log
#./pnr_compiler ./testcase_cap common_centroid.lef common_centroid.v common_centroid.map NO.rul common_centroid 1 0 | tee log
##
##gdb pnr_compiler
##set args ./testcase_latest2 sc.lef sc_block.v sc.map NO.rul switched_capacitor_filter 1 0

