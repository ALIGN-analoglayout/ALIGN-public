#!/bin/bash

rm -f __json
rm -f __json_grs
rm -f $ALIGN_HOME/Viewer/INPUT/comparator_kbc.json

python -m intel_p1222p2.generate_comparator_kbc

./flow2.py $* -sgr -iv comparator_kbcInputVol -ov comparator_kbcOutputVol -src comparator_kbc -td Intel/DR_COLLATERAL_Generator/22nm --placer_json __json --gr_json __json_grs --no_interface --router_executable /home/smburns/DARPA/analog-Feb18/analog/bin/amsr.exe
