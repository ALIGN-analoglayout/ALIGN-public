# Simple test layout collateral generator

Will generate input files for the detailed router. Here is a complete flow including running the router


This "installs" the python scripts in a docker image.
````bash
docker build -t cktgen .
````

This puts the detailed routing process collateral (for the strawman process) in the docker volume named "routerStrawman". Change to the directory with the collateral before doing the docker run.
````bash
docker volume rm routerStrawman
(cd ../DetailedRouter/DR_COLLATERAL_Generator/strawman1; tar cvf - . ) | docker run --rm --mount source=routerStrawman,target=/DR_COLLATERAL -i ubuntu bash -c "cd DR_COLLATERAL; tar xvf -"
cd -
````

This runs the script that generates a two device placement and global routing
````bash
docker run --rm --mount source=routerStrawman,target=/Cktgen/DR_COLLATERAL --mount source=inputVol,target=/Cktgen/INPUT cktgen bash -c "source /sympy/bin/activate; cd /Cktgen; python cktgen.py -n mydesign --route"
````
The input collateral for the router is placed in the docker volume named "inputVol". Also try cktgen4.py and cktgen8.py for circuits with more devices.


This runs the router. (The image containing the router needs to be downloaded from docker hub. Please get a login at hub.docker.com, send steven.m.burns@intel.com an email with your docker user name, and you'll be granted permission to download this docker image.)
````bash
docker run --rm --mount source=outputVol,target=/Cktgen/out --mount source=inputVol,target=/Cktgen/INPUT --mount source=routerStrawman,target=/Cktgen/DR_COLLATERAL darpaalign/detailed_router bash -c "cd /Cktgen; amsr.exe -file INPUT/ctrl.txt"
````

This backannotates the router results into a json file for viewer/
````bash
docker run --rm --mount source=outputVol,target=/Cktgen/out --mount source=inputVol,target=/Cktgen/INPUT --mount source=routerStrawman,target=/Cktgen/DR_COLLATERAL cktgen bash -c "source /sympy/bin/activate; cd /Cktgen; python cktgen.py --consume_results -n mydesign"
````

This starts up the viewer on localhoast:8082. Point your browser there to see the layout.
````bash
docker run --rm --mount source=inputVol,target=/public/INPUT -p8082:8000 -d viewer_image /bin/bash -c "source /sympy/bin/activate; cd /public; python -m http.server"
````
