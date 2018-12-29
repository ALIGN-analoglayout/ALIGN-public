#!/bin/bash

PORT=8090
INPUTVOL=equalizerInputVol
OUTPUTVOL=equalizerOutputVol
NM=wcap

#docker build -t tally .

#docker run --rm --mount source=${INPUTVOL},target=/INPUT tally bash -c "source sympy/bin/activate && cd /scripts && python placer_equalizer.py -n ${NM} && python global_router.py -n ${NM} && cp ${NM}_placer_out.json ${NM}_global_router_out.json /INPUT"

tar cvf - ${NM}_placer_out_scaled.json ${NM}_global_router_out.json | docker run --rm --mount source=${INPUTVOL},target=/INPUT -i ubuntu /bin/bash -c "cd /INPUT && tar xvf -"

cd ../Cktgen

docker build -t cktgen .

# -sar -sgr -smt 
./flow.sh -p ${PORT} -iv ${INPUTVOL} -ov ${OUTPUTVOL} -sv -s cktgen_from_json.py -src ${NM} -td ../DetailedRouter/DR_COLLATERAL_Generator/strawman1_ota --placer_json INPUT/${NM}_placer_out_scaled.json

docker run --mount source=${INPUTVOL},target=/public/INPUT --rm -d -p ${PORT}:8000 viewer_image bash -c "source /sympy/bin/activate && cd /public && python -m http.server"
