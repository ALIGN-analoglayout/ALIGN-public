# Simple test layout collateral generator

Will generate input files for the detailed router. Here is a complete flow including running the router


This "installs" the python scripts in a docker image.
````bash
docker build -t cktgen .
````

This runs the script that generates a two device placement and global routing
````bash
docker run --mount source=inputVol,target=/Cktgen/INPUT cktgen bash -c "source /sympy/bin/activate; cd /Cktgen; python cktgen.py -n mydesign --route --show_global_routes"
````
The input collateral for the router is placed in the docker volume named "inputVol". Also try cktgen-bigger.py and cktgen8.py for circuits with more devices.

This puts the detailed routing process collateral (for the strawman process) in the docker volume named "routerStrawman". Change to the directory with the collateral before doing the docker run.
````bash
cd ../DetailedRouter/DR_COLLATERAL_Strawman
#docker volume rm routerStrawman
tar cvf - . | docker run --mount source=routerStrawman,target=/DR_COLLATERAL -i ubuntu bash -c "cd DR_COLLATERAL; tar xvf -"
cd -
````

This runs the router. (The image containing the router needs to be downloaded from docker hub. Please get a login at hub.docker.com, send steven.m.burns@intel.com an email with your docker user name, and you'll be granted permission to download this docker image.)
````bash
docker run --mount source=outputVol,target=/Cktgen/out --mount source=inputVol,target=/Cktgen/INPUT --mount source=routerStrawman,target=/Cktgen/DR_COLLATERAL darpaalign/detailed_router bash -c "cd /Cktgen; amsr.exe -file INPUT/ctrl.txt"
````

This backannotates the router results into a json file for viewer/
````bash
docker run --mount source=outputVol,target=/Cktgen/out --mount source=inputVol,target=/Cktgen/INPUT --mount source=routerStrawman,target=/Cktgen/DR_COLLATERAL cktgen bash -c "source /sympy/bin/activate; cd /Cktgen; python cktgen.py --consume_results -n mydesign"
````

This starts up the viewer on localhoast:8082. Point your browser there to see the layout.
````bash
docker run --mount source=inputVol,target=/public/INPUT -p8082:8000 -d viewer_image /bin/bash -c "source /sympy/bin/activate; cd /public; python -m http.server"
````
