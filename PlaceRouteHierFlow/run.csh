#! /bin/csh

#./tester ./USC_testcase_BS_AMP_flat BS_AMP.lef netlist_BS_AMP_part1.v BS_AMP.map NO.rul netlist_BS_AMP | tee log
#./tester ./USC_testcase_BS_AMP_current_mirror_bank BS_AMP.lef netlist_BS_AMP_part1.v BS_AMP.map NO.rul netlist_BS_AMP | tee log
#./tester ./USC_testcase_diff_aspect_ratio track_hold.lef track_hold.v track_hold.map NO.rul top | tee log
#./tester ./USC_testcase track_hold.lef track_hold.v track_hold.map NO.rul top | tee log
./tester ./testcase_latest2 sc.lef sc_block.v sc.map NO.rul switched_capacitor_filter | tee log
#./tester ./testcase_common_centroid common_centroid.lef common_centroid.v common_centroid.map NO.rul common_centroid
##
##gdb tester
##set args ./testcase_latest2 sc.lef sc_block.v sc.map drcRules_calibre_asap7_Rule_Deck.rul switched_capacitor_filter

