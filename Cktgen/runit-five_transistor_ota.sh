#!/bin/bash


#(cd ../PnRPython && pytest --capture=no tests/test_cktgen_dump.py)

docker run --mount source=equalizerInputVol,target=/INPUT --name sam ubuntu
docker cp ../PnRPython/tests/__json_five_transistor_ota_dump sam:INPUT
docker cp ../PnRPython/tests/__json_five_transistor_ota_gr sam:INPUT/five_transistor_ota_global_router_out.json
docker rm sam

docker build -t cktgen .

./flow.sh $* -sgr -p 8086 -iv equalizerInputVol -ov equalizerOutputVol -s "-m cktgen.cktgen_physical_from_json" -src five_transistor_ota -td ../DetailedRouter/DR_COLLATERAL_Generator/hack84 --placer_json INPUT/__json_five_transistor_ota_dump --no_interface

docker run --mount source=equalizerInputVol,target=/INPUT --name sam ubuntu
rm -rf INPUT-copy
docker cp sam:INPUT INPUT-copy
docker rm sam

cp INPUT-copy/mydesign_dr_globalrouting.json ../PnRPython/tests/five_transistor_ota_adr_dr_globalrouting.json

(cd ../PnRPython && pytest --capture=no tests/test_check_adr.py)

