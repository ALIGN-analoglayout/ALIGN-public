# Simple test layout collateral generator

Will generate input files for the detailed router. Here is a complete flow including running the router


This "installs" the python scripts in a docker image.
````bash
docker build -t cktgen .
````

Use the `flow.sh` script to run a complete flow.
This script does the following:
1) Copies the detailed routing collateral (specified by the `-td` or `--techdir` options) to a docker volume (specified by the `-rv` or `routervolume` options.)

2) Generates the input collateral for the detailed router by running a circuit generation script (generates leaf cells, connections, placement, and global routes.) Which script to run is specified with the `-s` or `--script` options. The input collateral is put in a docker volume (specified by the `-iv` or `--inputvolume` options.)

3) Optionally, run the detailed router (to disable use the `-sr` or `--skiprouter` options) and process the router results so that it can be shown in the viewer. The output of the router goes to a docker volume (specified by the `-ov` or `--outputVolume` options.)

4) Run the web-based layout viewer. The port of the viewer is specified using the `-p` or `--port` option.

Here are several examples:
First, this will stop all running docker containers and free up ports so the viewer can use them.
````bash
docker stop $(docker ps -a)
````

This runs the river routing example with the strawman1 collateral.
````
./flow.sh
````
and is the same as executing this:
````
./flow.sh -s cktgen_river.py -p 8082 -td ../DetailedRouter/DR_COLLATERAL_Generator/strawman1 -tf Process.json -iv inputVol -ov outputVol -rv routerStrawman
````
You can view the results by visiting lcoalhost:8082 in your web browser.

If you want to run several at the same time do this:
````
./flow.sh -s cktgen_river.py -p 8081 -td ../DetailedRouter/DR_COLLATERAL_Generator/strawman1 -iv inputVol1 -ov outputVol1 -rv routerStrawman1 &
./flow.sh -s cktgen_river.py -p 8082 -td ../DetailedRouter/DR_COLLATERAL_Generator/strawman2 -iv inputVol2 -ov outputVol2 -rv routerStrawman2 &
./flow.sh -s cktgen_river.py -p 8083 -td ../DetailedRouter/DR_COLLATERAL_Generator/strawman3 -iv inputVol3 -ov outputVol3 -rv routerStrawman3 &
````
