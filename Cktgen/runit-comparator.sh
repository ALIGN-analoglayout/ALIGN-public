#!/bin/bash


(cd Intel; python3 generate_comparator_v2.py)

docker run --mount source=comparatorInputVol,target=/INPUT --name sam ubuntu
docker cp Intel/__json sam:INPUT
docker cp Intel/__json_grs sam:INPUT
docker rm sam

docker build --build-arg http_proxy=$http_proxy --build-arg https_proxy=$https_proxy -t cktgen .

./flow.sh $* -sgr -p 8086 -iv comparatorInputVol -ov comparatorOutputVol -s "-m cktgen.cktgen_physical_from_json" -src comparator -td Intel/DR_COLLATERAL_Generator/22nm --placer_json INPUT/__json --gr_json INPUT/__json_grs --no_interface
