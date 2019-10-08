# PlaceRouteHierFlow

## A. Syntax
``` Shell
./pnr_compiler testcase_DIR testcase.lef testcase.v testcase.map testcase.json testcaseTop numOfLayout optEffort
```
Inputs
>-   testcase_DIR: string type; the directory of input data
>-   testcase.lef: string type; LEF file
>-   testcase.v: string type; Verilog file
>-   testcase.map: string type; map file for gds.json
>-   testcase.json: string type; PDK file in.json format
>-   testcaseTop: string type; top module name in netlist
>-   numOfLayout: integer type; the max number of generated layouts
>-   optEffort: integer type; optimization effort in range of 0 to 2 (0: low, 1: median, 2: high)

Outputs: all the results will be saved under 'Results' folder by default
>-   xx.plt: GNU plot file of placement results
>-   xx_PL.gds.json: JSON format of placement layout
>-   xx_GL.gds.json: JSON format of global routing layout
>-   xx_DR.gds.json: JSON format of detailed routing layout
>-   xx_PR.gds.json: JSON format of power routing layout

## B. Setup & Kickoff

### Build the image 
1.  Build prerequisite image with_protobuf under [Build](https://github.com/ALIGN-analoglayout/ALIGN-public/tree/master/Build)
``` Shell
docker build -f Dockerfile.build -t with_protobuf .
```
Googletest is now required to build this tool. (Build instruction are documents in `Dockerfile.build`.)

2.  Build the image for place&route
``` Shell
docker build -t placeroute_image .
```
### Run the test case
``` Shell
(cd testcase_example; tar cvf - .) | docker run --rm -i --mount source=placerInputVol,target=/PlaceRouteHierFlow/INPUT ubuntu /bin/bash -c "cd /PlaceRouteHierFlow/INPUT; tar xvf -"

docker run --rm --mount source=placerInputVol,target=/PlaceRouteHierFlow/INPUT --mount source=placerOutputVol,target=/PlaceRouteHierFlow/OUTPUT placeroute_image /bin/bash -c "cd /PlaceRouteHierFlow; ./pnr_compiler ./testcase_example switched_capacitor_filter.lef switched_capacitor_filter.v switched_capacitor_filter.map layers.json switched_capacitor_filter 2 0"
```

## C. Conversion between JSON and GDS for layouts
Currently we support the input/output layout files in JSON format.

To convert the format, please use the codes under [GDSConv](https://github.com/ALIGN-analoglayout/ALIGN-public/tree/master/GDSConv)

To configure the Python environment, please follow Dockerfile.python3 under GDSConv.

## D. About third-party solvers/libraries
1.  In our router, a third-party ILP solver lp_solve is required. The current supported version is lp_solve 5.5.2.5.
Please download the codes from <http://lpsolve.sourceforge.net/5.5/>.

2.  All the output layouts are written in JSON format. To write JSON files, we use a third-party c++ json library. Please download the codes from <https://github.com/nlohmann/json.git>.

3.  In our mixed-size block placement, C++ boost libraries are employed to implement some arithmetical calculation. Please download the codes from <https://github.com/boostorg/boost>.
