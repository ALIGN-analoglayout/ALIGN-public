#!/bin/bash
 
(cd testcase_example; tar cvf - .) | docker run --rm -i --mount source=placerInputVol,target=/PlaceRouteHierFlow/INPUT ubuntu /bin/bash -c "cd /PlaceRouteHierFlow/INPUT; tar xvf -"

# Disable
#(cd . && ./unit_tests --gtest_output=xml:junit.xml > LOG-ut) && \

docker run --name PnR \
       --mount source=placerInputVol,target=/PlaceRouteHierFlow/INPUT \
       --mount source=placerOutputVol,target=/PlaceRouteHierFlow/OUTPUT \
       placeroute_coverage_image /bin/bash -c "\
cd /PlaceRouteHierFlow && \
lcov -z ; \
(cd PnRDB && ./unit_tests --gtest_output=xml:junit.xml) && \
(cd cap_placer && ./unit_tests --gtest_output=xml:junit.xml) && \
(cd placer && ./unit_tests --gtest_output=xml:junit.xml) && \
(cd router && ./unit_tests --gtest_output=xml:junit.xml) && \
./pnr_compiler ./testcase_example switched_capacitor_filter.lef switched_capacitor_filter.v switched_capacitor_filter.map layers.json switched_capacitor_filter 2 0 > PnR.log && \
./pnr_compiler ./testcase_guardring switched_capacitor_filter.lef switched_capacitor_filter.v switched_capacitor_filter.map layers.json switched_capacitor_filter 1 0 > PnR-guardring.log && \
./pnr_compiler ./testcase_guardringpowernet high_speed_comparator.lef high_speed_comparator.v high_speed_comparator.map layers.json high_speed_comparator 1 0 > PnR-guardringpowernet.log && \
lcov --capture --directory . --output-file coverage.info && \
genhtml coverage.info --output-directory coverage.out"

#docker cp PnR:/PlaceRouteHierFlow
