[![CircleCI](https://circleci.com/gh/ALIGN-analoglayout/ALIGN-public.svg?style=svg)](https://circleci.com/gh/ALIGN-analoglayout/ALIGN-public)
[![Codacy Badge](https://api.codacy.com/project/badge/Grade/2aeb84c0f14949909bcd342b19721d01)](https://app.codacy.com/app/ALIGN-analoglayout/ALIGN-public?utm_source=github.com&utm_medium=referral&utm_content=ALIGN-analoglayout/ALIGN-public&utm_campaign=Badge_Grade_Settings)

# ALIGN: Analog Layout, Intelligently Generated from Netlists
ALIGN is an open source automatic layout generator for analog circuits jointly developed under the DARPA IDEA program by the University of Minnesota, Texas A&M University, and Intel Corporation. 

The goal of ALIGN (Analog Layout, Intelligently Generated from Netlists) is to automatically translate an unannotated (or partially annotated) SPICE netlist of an analog circuit to a GDSII layout. The repository also releases a set of analog circuit designs. 

The ALIGN flow includes the following steps:
* _Circuit annotation_ creates a multilevel hierarchical representation of the input netlist. This representation is used to implement the circuit layout in using a hierarchical manner. 
* _Design rule abstraction_ creates a compact JSON-format represetation of the design rules in a PDK. This repository provides a mock PDK based on a FinFET technology (where the parameters are based on published data). These design rules are used to guide the layout and ensure DRC-correctness.
* _Primitive cell generation_ works with primitives, i.e., blocks the lowest level of design hierarchy, and generates their layouts. Primitives typically contain a small number of transistor structures (each of which may be implemented using multiple fins and/or fingers). A parameterized instance of a primitive is automatically translated to a GDSII layout in this step.
* _Placement and routing_ performs block assembly of the hierarchical blocks in the netlist and routes connections between these blocks, while obeying a set of analog layout constraints. At the end of this step, the translation of the input SPICE netlist to a GDSII layout is complete. 

## Inputs:
 * A [SPICE netlist](examples/telescopic_ota/telescopic_ota.sp) of the analog circuit
 * [Setup file](examples/telescopic_ota/telescopic_ota.setup)
    - Power and Gnd signals (First power signal is used for global power grid)
    - Clk signal (optional)
    - Digital blocks (optional)
 * Library:(SPICE format)
    - A basic built-in [template library](align/config/basic_template.sp) is provided, which is used to identify hierachies in the design.
    - More library elements can be added in the [user_template library](align/config/user_template.sp).
 * PDK: Abstracted [design rules](pdks/FinFET14nm_Mock_PDK)
    - A mock FinFET 14nm PDK [rules file](pdks/FinFET14nm_Mock_PDK/layers.json) is provided, which is used by the primitive cell generator and the place and route engine.
    - A new PDK can be represented using a JSON-format design rule abstraction, similar to mock-PDK design rules file provided.
    - Primitive cells(NMOS/PMOS/[Resistor](pdks/FinFET14nm_Mock_PDK/fabric_Res.py)/[Capacitor](pdks/FinFET14nm_Mock_PDK/fabric_Cap.py)) must be redefined for any new PDK.
 * LEF:
    - A list of parameterized cells supported by cell generator is stored in file [param_lef](align/config/param_lef).
## Outputs:
 * Layout GDS: Final layout of the design. The output GDS can be imported into any GDSII viewer.
 * Design JSON: Final layout which can be viewed using the ALIGN Viewer.
 * Layout image: .jpg format of the layout saved using the [KLayout tool](https://github.com/KLayout/klayout).

## Getting started
The suggested way to run the end-to-end ALIGN flow uses a Docker container-based flow for which the user must have docker-compose installed. The ALIGN software is installed in a container image and Make is used to run the flow through the containers. The user may also use the Makefile to run the ALIGN flow through the native Linux build of all the components in the current environment (assuming that all software prerequisites have been installed).
Two environment variables must be set to run the Makefile in any environment. The first is the ALIGN\_HOME variable, which should point the top directory of the ALIGN analog system.

	    % export ALIGN_HOME=<top of ALIGN source area>

The second is a working directory ALIGN\_WORK\_DIR, which can either be the full path to a working directory or a docker volume name.  

        % docker volume create <volumeName>
        % export ALIGN_WORK_DIR=<volumeName for docker flow / full work dir path for native flow>
#### Docker flow
 * Requirements
    - Docker-ce > 17.12
    - Docker compose > 3.6

#### Native Linux Environment Flow
You can use [install.sh](install.sh) (for bash shell) or [install_tcsh.sh](install_tcsh.sh) (for tcsh/ Red Hat) to install the requirements and the native flow. Please go through [Running_your_first_design](docs/Running_your_first_design.pdf) for detailed explanation and common errors during installation.
 * Requirements
    - Python > 3.6
    - gcc > 4.2
    - [Boost]( https://github.com/boostorg/boost.git) >= 1.68.0
    - [Lpsolve](https://sourceforge.net/projects/lpsolve/files/lpsolve/5.5.2.5/lp_solve_5.5.2.5_source.tar.gz/download) >= 5.5.2.5
    - [JSON]( https://github.com/nlohmann/json.git)>=3.7.3
    - [Googletest]( https://github.com/google/googletest)>=1.10
    - You can look into [setup file](setup.sh) for exact set of commands used for installing these requirements.

 * Setting up local environment variables if installations are not in system search path.

        % export BOOST_LP= <boost installation path, e.g., $ALIGN_HOME/boost>
        % export LP_DIR=<lpsolve installation path, e.g., $ALIGN_HOME/lpsolve>
        % export JSON= <json installation path, e.g., $ALIGN_HOME/json>
        % export LD_LIBRARY_PATH=<lpsolve library path, e.g., $ALIGN_HOME/lpsolve/lp_solve_5.5.2.5_dev_ux64/>
        % export GTEST_DIR=<googletest installation path, e.g., $ALIGN_HOME/googletest/googletest/>
        % export VENV= <python virtual environment path, e.g., ./align_venv>
 * Installation

        % cd PlaceRouteHierFlow
        % make
        % cd $ALIGN_HOME
        % python3.6 -m venv $VENV 
        % source $VENV/bin/activate 
        % pip install --upgrade pip
        % pip install -e .

## Usage
By default, the design directory is set to the examples directory. This can be modfied in the Makefile.
* Docker based run

        % cd $ALIGN_HOME/build
        % make docker DESIGN=<design>
* Native environment flow
    -make flow
        % cd $ALIGN_WORK_DIR
        % ln -s $ALIGN_HOME/build/Makefile
        % make VENV=$VENV DESIGN=<design>
    - python command 
        % source $VENV/bin/acitivate
        % schematic2layout.py <input_directory> -f <spice file> -s <design_name> -p <pdk path> -flat <0/1> -c -g (to check drc)
        % e.g., > schematic2layout.py $ALIGN_HOME/examples/buffer/ -f $ALIGN_HOME/examples/buffer/buffer.sp -s buffer -p $ALIGN_HOME/pdks/FinFET14nm_Mock_PDK -flat 0 -c -g

    
## Design database:
* Contain example circuits with netlist, schematic running on circleci
* [Other design examples](dev/Design%20Database) 
 
## Viewer :
The final output GDS can be viewed using by importing in virtuoso or any GDS viewer
* [KLayout](https://github.com/KLayout/klayout): GDS viewer
* [Viewer](Viewer): Layout viewer to view output JSON file

