.. circuit annotation documentation master file, created by
   sphinx-quickstart on Sat Dec 28 18:45:43 2019.
   You can adapt this file completely to your liking, but it should at least
   contain the root `toctree` directive.

ALIGN: Analog Layout, Intelligently Generated from Netlists!
============================================================
Automatic circuit annotation documentation!
--------------------------------------------
This is an introduction to the auto annotation module of the ALIGN project. This work was performed at the University of Minnesota.

Circuit annotation automatically identifies hierarchies in the design using a combination of a library-based and rule-based approach.

- Input:
    * Unannotated spice netlist
    * setup file
        - Power and Gnd signals (First power signal is used for global power grid)
        - Clk signal (optional)
        - Digital blocks (optional)
    * Library:(spice format)
        - A basic built-in template library is provided, which is used to identify elements in the design.
        - The user can add more template library elements in the user_template library.
        - The user can also specify dont_use_cells.txt to ask annotation to ignore a subset of library elements during annotation.
    * LEF:
        - This folder is used to maintain a list of modules for which cell generator/LEF is available.
        - The list of parameterized cells is stored in param_lef.
        - Any LEF file in this directory will be used to identify available modules.
- Outputs:
    * Verilog file (used for PnR): A hierarchical netlist
    * Inputs for the cell generator: parameters for the parameterized cell generator (the next stage of the ALIGN flow)

Getting started
----------------
**Run on docker**

Create a Docker image:

``docker build -t topology .``

**Direct run on terminal**

Requirements:
    Python3.6, networkx, matplotlib, pyyaml

Usage
------
An integrated flow using a combination of library-based and rule-based methods is used for automatic annotation. We support a Docker-based flow as it helps in minimizing environment setup issues.

**Library-based annotation**
    - Library based annotation is used for identifying smaller circuits (primitives) in the design. We use VF2 based subgraph isomorphism to map library elements to the circuit.

**Rule-based annotation**
    - Analog designs are dominated by arrays in the circuits which need a structured layout. To identify array structures in the layout, we use graph traversal, which is then used to identify common centroid constraints that must be enforced.

Run a Python-based test using docker

``docker run --name topology_container --mount source=inputVol,target=/INPUT topology bash -c "source /sympy/bin/activate && cd /DEMO && make ota && cp -r ./Results /INPUT"``

``docker cp topology_container:/INPUT/results .``


Using make:

``make <design name>``

Python command:

``python3 src/compiler.py --dir ./input_circuit -f `basename $< .sp`.sp --subckt <design name> --flat 0 --unit_size_mos 12 --unit_size_cap 12``


