#! /bin/csh

#./tester -I ./testcase_latest2 --lef sc.lef --verilog sc_block.v --map sc.map --pdk NO.rul --topDesign switched_capacitor_filter --maxLayout 1 | tee log
./tester -I ./testcase_small --lef sc.lef --verilog sc_block.v --map sc.map --pdk NO.rul --topDesign switched_capacitor_filter --maxLayout 1 | tee log
#./tester -I ./testcase_cap --lef common_centroid.lef --verilog common_centroid.v --map common_centroid.map --pdf NO.rul --topDesign common_centroid --maxLayout 1 | tee log
##
##gdb tester
##set args -I ./testcase_latest2 --lef sc.lef --verilog sc_block.v --map sc.map --pdk NO.rul --topDesign switched_capacitor_filter --maxLayout 1

