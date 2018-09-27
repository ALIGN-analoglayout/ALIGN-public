#!/bin/bash

exe=cktgen_river8.py

M_INPUT="--mount source=inputVol,target=/Cktgen/INPUT"
M_out="--mount source=outputVol,target=/Cktgen/out"
M_DR_COLLATERAL="--mount source=routerStrawman,target=/Cktgen/DR_COLLATERAL"

docker volume rm routerStrawman
(cd ../DetailedRouter/DR_COLLATERAL_Strawman; tar cvf - . | docker run --rm ${M_DR_COLLATERAL} -i ubuntu bash -c "cd /Cktgen/DR_COLLATERAL; tar xvf -")

docker volume rm inputVol
docker volume rm outputVol
docker run --rm ${M_INPUT} ${M_DR_COLLATERAL} cktgen bash -c "source /sympy/bin/activate; cd /Cktgen; python ${exe} -n mydesign --route"

docker run --rm --mount source=inputVol,target=/public/INPUT -p8082:8000 -d viewer_image /bin/bash -c "source /sympy/bin/activate; cd /public; python -m http.server"

