#!/bin/bash

tar cvf - ota_placer_out.json ota_global_router_out.json | docker run --rm --mount source=inputVol,target=/INPUT -i ubuntu bash -c "cd /INPUT && tar xvf -"

cd ../Cktgen

docker build -t cktgen .

./flow.sh -sv -s cktgen_ota_from_json.py -td ../DetailedRouter/DR_COLLATERAL_Generator/strawman1_ota --show_global_routes --placer_json INPUT/ota_placer_out.json
