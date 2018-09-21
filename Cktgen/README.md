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
The input collateral for the router is placed in the docker volume named "inputVol".

This puts the detailed routing process collateral (for the strawman process) in the docker volume names "routerStrawman"
````bash
#docker volume rm routerStrawman
tar cvf - . | docker run --mount source=routerStrawman,target=/DR_COLLATERAL -i ubuntu bash -c "cd DR_COLLATERAL; tar xvf -"
````

This runs the router.
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
