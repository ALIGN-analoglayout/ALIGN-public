#!/bin/bash
 
(cd testcase_small; tar cvf - .) | docker run --rm -i --mount source=placerInputVol,target=/PlaceRouteHierFlow/INPUT ubuntu /bin/bash -c "cd /PlaceRouteHierFlow/INPUT; tar xvf -"

docker run --rm --mount source=placerInputVol,target=/PlaceRouteHierFlow/INPUT --mount source=placerOutputVol,target=/PlaceRouteHierFlow/OUTPUT placeroute_image /bin/bash -c "cd /PlaceRouteHierFlow; ./tester -I ./INPUT --lef sc.lef --verilog sc_block.v --map sc.map --pdk NO.rul --topDesign switched_capacitor_filter --maxLayout 1"


