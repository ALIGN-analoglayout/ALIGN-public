#!/bin/bash

SCRIPT=cktgen.py
PORT=8082
TECHDIR=../DetailedRouter/DR_COLLATERAL_Generator/strawman1
TECHFILE=Process.json
INPUTVOL=inputVol
OUTPUTVOL=outputVol
ROUTERVOL=routerStrawman
SKIPROUTER=NO
SKIPGENERATE=NO
SKIPVIEWER=NO
SHOWGLOBALROUTES=""
ROUTE=" --route"

POSITIONAL=()
while [[ $# -gt 0 ]]
do
key="$1"

case $key in
    -s|--script)
    SCRIPT="$2"
    shift # past argument
    shift # past value
    ;;
    -p|--port)
    PORT="$2"
    shift # past argument
    shift # past value
    ;;
    -td|--techdir)
    TECHDIR="$2"
    shift # past argument
    shift # past value
    ;;
    -tf|--techfile)
    TECHFILE="$2"
    shift # past argument
    shift # past value
    ;;
    -iv|--inputvolume)
    INPUTVOL="$2"
    shift # past argument
    shift # past value
    ;;
    -ov|--outputvolume)
    OUTPUTVOL="$2"
    shift # past argument
    shift # past value
    ;;
    -rv|--routervolume)
    ROUTERVOL="$2"
    shift # past argument
    shift # past value
    ;;
    -sr|--skiprouter)
    SKIPROUTER=YES
    shift # past argument
    ;;
    -sg|--skipgenerate)
    SKIPGENERATE=YES
    shift # past argument
    ;;
    -sv|--skipviewer)
    SKIPVIEWER=YES
    shift # past argument
    ;;
    -sgr|--show_global_routes)
    SHOWGLOBALROUTES=" --show_global_routes"
    shift # past value
    ;;
    -sar|--skipactualrouting)
    ROUTE=""
    shift # past value
    ;;
    *)    # unknown option
    POSITIONAL+=("$1") # save it in an array for later
    shift # past argument
    ;;
esac
done
set -- "${POSITIONAL[@]}" # restore positional parameters

echo SCRIPT  = "${SCRIPT}"
echo PORT    = "${PORT}"
echo TECHDIR = "${TECHDIR}"
echo TECHFILE = "${TECHFILE}"
echo INPUTVOL = "${INPUTVOL}"
echo OUTPUTVOL = "${OUTPUTVOL}"
echo ROUTERVOL = "${ROUTERVOL}"
echo SKIPROUTER = "${SKIPROUTER}"
echo SKIPGENERATE = "${SKIPGENERATE}"
echo SKIPVIEWER = "${SKIPVIEWER}"

M_INPUT="--mount source=${INPUTVOL},target=/Cktgen/INPUT"
M_INPUT_VIEWER="--mount source=${INPUTVOL},target=/public/INPUT"
M_out="--mount source=${OUTPUTVOL},target=/Cktgen/out"
M_DR_COLLATERAL="--mount source=${ROUTERVOL},target=/Cktgen/DR_COLLATERAL"

docker volume rm ${ROUTERVOL}
(cd ${TECHDIR} && tar cvf - .) | docker run --rm ${M_DR_COLLATERAL} -i ubuntu bash -c "cd /Cktgen/DR_COLLATERAL && tar xvf -"

if [ ${SKIPGENERATE} = "NO" ]; then
    if [ ${SKIPVIEWER} = "NO" ]; then
	docker volume rm ${INPUTVOL}
    fi
    docker volume rm ${OUTPUTVOL}
    docker run --rm ${M_INPUT} ${M_DR_COLLATERAL} cktgen bash -c "source /sympy/bin/activate && cd /Cktgen && python ${SCRIPT} -n mydesign ${ROUTE}${SHOWGLOBALROUTES}"
fi

if [ ${SKIPROUTER} = "NO" ]; then
    docker run --rm ${M_out} ${M_INPUT} ${M_DR_COLLATERAL} darpaalign/detailed_router bash -c "cd /Cktgen && amsr.exe -file INPUT/ctrl.txt"

    docker run --rm ${M_out} ${M_INPUT} ${M_DR_COLLATERAL} cktgen bash -c "source /sympy/bin/activate; cd /Cktgen && python ${SCRIPT} --consume_results -n mydesign"
fi

if [ ${SKIPVIEWER} = "NO" ]; then
    docker run --rm ${M_INPUT_VIEWER} -p${PORT}:8000 -d viewer_image /bin/bash -c "source /sympy/bin/activate && cd /public && python -m http.server"
fi
