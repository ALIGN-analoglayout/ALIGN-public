[![CircleCI](https://circleci.com/gh/ALIGN-analoglayout/ALIGN-public.svg?style=svg)](https://circleci.com/gh/ALIGN-analoglayout/ALIGN-public)
[![Codacy Badge](https://api.codacy.com/project/badge/Grade/2aeb84c0f14949909bcd342b19721d01)](https://app.codacy.com/app/ALIGN-analoglayout/ALIGN-public?utm_source=github.com&utm_medium=referral&utm_content=ALIGN-analoglayout/ALIGN-public&utm_campaign=Badge_Grade_Settings)

# ALIGN: Analog Layout, Intelligently Generated from Netlists
ALIGN is an open source automatic layout generator for analog circuits developed under IDEA program led by University of Minnesota funded by DARPA. The ALIGN flow includes circuit annotation, cell generation and placement and routing steps to generate a GDS from an input spice netlist. Circuit annotation creates multiple hierarchies in the input netlist to implement the design in using a hierarchical approach. Design rules are abstracted from PDK into a JSON format. A mock PDK based on FinFET technology is provided with this repository which is being used by cell generator and Placer and Router to generate layout.

## Inputs:
 * Unannotated [spice netlist](examples/telescopic_ota/telescopic_ota.sp)
 * [Setup file](examples/telescopic_ota/telescopic_ota.setup)
    - Power and Gnd signals (First power signal is used for global power grid)
    - Clk signal (optional)
    - Digital blocks (optional)
 * Library:(spice format)
    - A basic built-in [template library](align/config/basic_template.sp) is provided, which is used to identify hierachies in the design.
    - More library elements can be added in the [user_template library](align/config/user_template.sp).
 * PDK: Abstracted [design rules](pdks/FinFET14nm_Mock_PDK)
    - A mock FinFET 14nm PDK [rules file](pdks/FinFET14nm_Mock_PDK/layers.json) is provided, which is used by cell generator and Place and Route.
    - New design rule abstraction can be added in JSON format similar to design rules file provided.
    - Primitive cells(NMOS/PMOS/[Resistor](pdks/FinFET14nm_Mock_PDK/fabric_Res.py)/[Capacitor](pdks/FinFET14nm_Mock_PDK/fabric_Cap.py)) need to be redefined for any new PDK 
 * LEF:
    - A list of parameterized cells supported by cell generator is stored in file [param_lef](align/config/param_lef).
## Outputs:
 * Design Layout GDS: Final layout of the design. The output gds can be imported into any 
 * Design json: Final layout which can be viewed using ALIGN Viewer created by Intel
 * Layout image: .jpg format of layout saved using klayout

## Getting started
 Suggested way to run the end-to-end ALIGN flow is using a Docker container-based flow for which you need to have a Docker, docker-compose installed. The software get installed in a container image and we use Make to run the flow through the containers. Us can also use the Makefile to run the ALIGN flow through the native Linux build of all the componennts in the current environment (assuming you have all software prerequisites installed).
Two environment variables need to be set to run the Makefile in any environment. First is the ALIGN\_HOME variable which should point the top directory of the ALIGN analog system.

		% export ALIGN_HOME=<top of ALIGN source area>

Second is a working directory ALIGN\_WORK\_DIR, which can either be the full path to a working directory or a docker volume name.  
        % docker volume create <volumeName>
		% export ALIGN_WORK_DIR=<volumeName for docker flow / full work dir path for native flow>
#### Docker flow
 * Requirements
    - Docker-ce > 17.12
    - Docker compose > 3.6

#### Native Linux Environment Flow
 * Requirements
    - Python > 3.6
    - gcc > 7.2
    - [Boost]( https://github.com/boostorg/boost.git) >= 1.68.0
    - [Lpsolve](https://sourceforge.net/projects/lpsolve/files/lpsolve/5.5.2.5/lp_solve_5.5.2.5_source.tar.gz/download) >= 5.5.2.5
    - [JSON]( https://github.com/nlohmann/json.git)>=3.7.3
    - [Googletest]( https://github.com/google/googletest)>=1.10

 * Setting up local environment variables if installations are not in system search path 

        % export BOOST_LP= <boost installation path, e.g., $ALIGN_HOME/boost>
        % export LP_DIR=<lpsolve installation path, e.g., $ALIGN_HOME/lpsolve>
        % export JSON= <json installation path, e.g., $ALIGN_HOME/json>
        % export LD_LIBRARY_PATH=<lpsolve library path, e.g., $ALIGN_HOME/lpsolve/lp_solve_5.5.2.5_dev_ux64/>
        % export GTEST_DIR=<googletest installation path, e.g., $ALIGN_HOME/googletest/googletest/>
## Usage
Design directory is by default set to examples directory and can be modfied in the Makefile 
* Docker based run

        % cd $ALIGN_HOME/build
        % make docker DESIGN=<design>
* Native environment flow

        % cd $ALIGN_WORK_DIR
        % ln -s $ALIGN_HOME/build/Makefile
        % source general/bin/activate <general is python virtual environment name>
        % make DESIGN=<design>
    
## Design database:
* Contain example circuits with netlist, schematic running on circleci
* [Other design examples](dev/Design%20Database) 
 
## Viewer :
The final output GDS can be viewed using by importing in virtuoso or any GDS viewer
* [KLayout](https://github.com/KLayout/klayout): GDS viewer
* [Viewer](Viewer): Layout viewer to view output JSON file

