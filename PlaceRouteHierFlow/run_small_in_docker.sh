#!/bin/bash
 
(cd testcase_example; tar cvf - .) | docker run --rm -i --mount source=placerInputVol,target=/PlaceRouteHierFlow/INPUT ubuntu /bin/bash -c "cd /PlaceRouteHierFlow/INPUT; tar xvf -"

docker run --rm --mount source=placerInputVol,target=/PlaceRouteHierFlow/INPUT --mount source=placerOutputVol,target=/PlaceRouteHierFlow/OUTPUT placeroute_image /bin/bash -c "cd /PlaceRouteHierFlow; ./pnr_compiler ./testcase_example switched_capacitor_filter.lef switched_capacitor_filter.v switched_capacitor_filter.map FinFET_Mock_PDK_Abstraction.json switched_capacitor_filter 2 0 | tee log"


