#!/bin/bash

rm __json
rm __json_grs
rm $ALIGN_HOME/Viewer/INPUT/comparator.json

python -m intel_p1222p2.generate_comparator

docker run --mount source=comparatorInputVol,target=/INPUT --name sam ubuntu
docker cp __json     sam:INPUT
docker cp __json_grs sam:INPUT

docker build --build-arg http_proxy --build-arg https_proxy -t cktgen .

./flow.sh $* -sgr -p 8086 -iv comparatorInputVol -ov comparatorOutputVol -s "-m cktgen.cktgen_physical_from_json" -src comparator -td Intel/DR_COLLATERAL_Generator/22nm --placer_json INPUT/__json --gr_json INPUT/__json_grs --no_interface

docker cp sam:INPUT/mydesign_dr_globalrouting.json comparator.json

docker rm sam

cp comparator.json $ALIGN_HOME/Viewer/INPUT

python ./check_results.py --circuit comparator --power vcc_0p9 --ground vssx

cp comparator_drc.json $ALIGN_HOME/Viewer/INPUT 


