#!/bin/bash

docker run --rm --mount source=inputVol,target=/Cktgen/INPUT cktgen bash -c "source /sympy/bin/activate; cd /Cktgen; python cktgen.py -n mydesign --route --show_global_routes"

#docker volume rm routerStrawman
#tar cvf - . | docker run --rm --mount source=routerStrawman,target=/DR_COLLATERAL -i ubuntu bash -c "cd DR_COLLATERAL; tar xvf -"

docker run --rm --mount source=outputVol,target=/Cktgen/out --mount source=inputVol,target=/Cktgen/INPUT --mount source=routerStrawman,target=/Cktgen/DR_COLLATERAL darpaalign/detailed_router bash -c "cd /Cktgen; amsr.exe -file INPUT/ctrl.txt"

docker run --rm --mount source=outputVol,target=/Cktgen/out --mount source=inputVol,target=/Cktgen/INPUT --mount source=routerStrawman,target=/Cktgen/DR_COLLATERAL cktgen bash -c "source /sympy/bin/activate; cd /Cktgen; python cktgen.py --consume_results -n mydesign"

docker run --rm --mount source=inputVol,target=/public/INPUT -p8082:8000 -d viewer_image /bin/bash -c "source /sympy/bin/activate; cd /public; python -m http.server"

