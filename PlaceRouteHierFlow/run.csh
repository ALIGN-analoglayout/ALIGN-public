#! /bin/csh

#./pnr_compiler ./testcase_example switched_capacitor_filter.lef switched_capacitor_filter.v switched_capacitor_filter.map layers.json switched_capacitor_filter 2 0 | tee log
./pnr_compiler ./ota_asap7 ota_asap7.lef ota_asap7.v ota_asap7.map layers.json ota_asap7 1 0 | tee log
./pnr_compiler ./current_mirror_ota current_mirror_ota.lef current_mirror_ota.v current_mirror_ota.map layers.json current_mirror_ota 1 0 | tee log
./pnr_compiler ./cascode_current_mirror_ota cascode_current_mirror_ota.lef cascode_current_mirror_ota.v cascode_current_mirror_ota.map layers.json cascode_current_mirror_ota 1 0 | tee log
./pnr_compiler ./strong_arm_latch strong_arm_latch.lef strong_arm_latch.v strong_arm_latch.map layers.json strong_arm_latch 1 0 | tee log
./pnr_compiler ./comparator_1 comparator_1.lef comparator_1.v comparator_1.map layers.json comparator_1 1 0 | tee log
./pnr_compiler ./comparator_3 comparator_3.lef comparator_3.v comparator_3.map layers.json comparator_3 1 0 | tee log
./pnr_compiler ./comparator_4 comparator_4.lef comparator_4.v comparator_4.map layers.json comparator_4 1 0 | tee log
#./pnr_compiler ./testcase_latest2 sc.lef sc_block.v sc.map NO.rul switched_capacitor_filter 1 0 | tee log
#./pnr_compiler ./testcase_small sc.lef sc_block.v sc.map NO.rul switched_capacitor_filter 1 0 | tee log
#./pnr_compiler ./testcase_cap common_centroid.lef common_centroid.v common_centroid.map NO.rul common_centroid 1 0 | tee log
##
##gdb pnr_compiler
##set args ./testcase_latest2 sc.lef sc_block.v sc.map NO.rul switched_capacitor_filter 1 0

