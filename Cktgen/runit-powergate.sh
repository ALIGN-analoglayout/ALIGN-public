#!/bin/bash

rm __json
rm __json_grs
rm $ALIGN_HOME/Viewer/INPUT/powergate.json

python -m intel_p1222p2.generate_powergate

docker run --mount source=powergateInputVol,target=/INPUT --name sam ubuntu
docker cp __json     sam:INPUT
docker cp __json_grs sam:INPUT

docker build --build-arg http_proxy --build-arg https_proxy -t cktgen .

./flow.sh $* -sgr -p 8086 -iv powergateInputVol -ov powergateOutputVol -s "-m cktgen.cktgen_physical_from_json" -src powergate -td Intel/DR_COLLATERAL_Generator/22nm --placer_json INPUT/__json --gr_json INPUT/__json_grs --no_interface

docker cp sam:INPUT/mydesign_dr_globalrouting.json powergate.json

docker rm sam

cp powergate.json $ALIGN_HOME/Viewer/INPUT
