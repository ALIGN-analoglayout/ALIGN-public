#!/bin/bash
 
(cd testcase_example; tar cvf - .) | docker run --rm -i --mount source=placerInputVol,target=/PlaceRouteHierFlow/INPUT ubuntu /bin/bash -c "cd /PlaceRouteHierFlow/INPUT; tar xvf -"

docker run --name PnR --mount source=placerInputVol,target=/PlaceRouteHierFlow/INPUT --mount source=placerOutputVol,target=/PlaceRouteHierFlow/OUTPUT placeroute_coverage_image /bin/bash -c "cd /PlaceRouteHierFlow && lcov -z ; ./pnr_compiler ./testcase_example switched_capacitor_filter.lef switched_capacitor_filter.v switched_capacitor_filter.map FinFET_Mock_PDK_Abstraction.json switched_capacitor_filter 2 0 > PnR.log && PnRDB/unit_tests --gtest_output=xml:junit.xml && lcov --capture --directory . --output-file coverage.info ; genhtml coverage.info --output-directory coverage.out"


