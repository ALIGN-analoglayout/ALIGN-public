#!/bin/bash

NM=comp
PORT=8090
INPUTVOL=equalizerInputVol
OUTPUTVOL=equalizerOutputVol
ROUTE=""
SHOWGLOBALROUTES=""
SMALL=""
SCRIPT=""
POSITIONAL=()
while [[ $# -gt 0 ]]
do
key="$1"

case $key in
    -n|--block)
    NM="$2"
    shift
    shift
    ;;
    -s|--script)
    SCRIPT="$2"
    shift
    shift
    ;;
    -p|--port)
    PORT="$2"
    shift
    shift
    ;;
    -iv|--inputvolume)
    INPUTVOL="$2"
    shift
    shift
    ;;
    -ov|--outputvolume)
    OUTPUTVOL="$2"
    shift
    shift
    ;;
    -sgr|--show_global_routes)
    SHOWGLOBALROUTES=" --show_global_routes"
    shift
    ;;
    -sar|--skipactualrouting)
    ROUTE=" -sar"
    shift
    ;;
    --small)
    SMALL=" --small"
    shift
    shift
    ;;
    *)    # unknown option
    POSITIONAL+=("$1") # save it in an array for later
    shift
    ;;
esac
done
set -- "${POSITIONAL[@]}" # restore positional parameters

#docker build -t tally .
if [ "${SCRIPT}" != "" ]; then

  docker run --rm --mount source=${INPUTVOL},target=/INPUT tally bash -c "source sympy/bin/activate && cd /scripts && cp /INPUT/\*_interface.json . && python ${SCRIPT}.py && cp ${NM}_placer_out.json ${NM}_global_router_out.json /INPUT"

else

tar cvf - ${NM}_placer_out_scaled.json ${NM}_global_router_out.json | docker run --rm --mount source=${INPUTVOL},target=/INPUT -i ubuntu /bin/bash -c "cd /INPUT && tar xvf -"

fi

cd ../Cktgen

docker build -t cktgen .

# -sar -sgr -smt 
./flow.sh ${SMALL}${SHOWGLOBALROUTES}${ROUTE} -p ${PORT} -iv ${INPUTVOL} -ov ${OUTPUTVOL} -sv -s cktgen_from_json.py -src ${NM} -td ../DetailedRouter/DR_COLLATERAL_Generator/strawman1_ota --placer_json INPUT/${NM}_placer_out_scaled.json

docker run --mount source=${INPUTVOL},target=/public/INPUT --rm -d -p ${PORT}:8000 viewer_image bash -c "source /sympy/bin/activate && cd /public && python -m http.server"
