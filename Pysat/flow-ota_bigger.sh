#!/bin/bash

PORT=8091
INPUTVOL=otaBiggerInputVol
OUTPUTVOL=otaBiggerOutputVol
NM=ota_bigger
DR_COLLATERAL=../DetailedRouter/DR_COLLATERAL_Generator/strawman5_ota

docker build -t tally .

docker run --rm --mount source=${INPUTVOL},target=/INPUT tally bash -c "source sympy/bin/activate && cd /scripts && python placer.py -n ${NM} && python global_router.py -n ${NM} && cp ${NM}_placer_out.json ${NM}_global_router_out.json /INPUT"

cd ../Cktgen

docker build -t cktgen .

./flow.sh -p ${PORT} -iv ${INPUTVOL} -ov ${OUTPUTVOL} -sv -s cktgen_${NM}_from_json.py -td ${DR_COLLATERAL} --placer_json INPUT/${NM}_placer_out.json

docker run --mount source=${INPUTVOL},target=/public/INPUT --rm -d -p ${PORT}:8000 viewer_image bash -c "source /sympy/bin/activate && cd /public && python -m http.server"
