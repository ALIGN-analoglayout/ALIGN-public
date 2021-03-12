# ALIGN: Analog Layout, Intelligently Generated from Netlists!
## Automatic circuit annotation documentation!
This is an introduction to the auto-annotation module of the ALIGN project. This work was performed at the University of Minnesota.

Circuit annotation automatically identifies hierarchies in the design using a combination of a library-based and rule-based approach.

#### Inputs:
    * Unannotated spice netlist
    * setup file
        - Power and Gnd signals (First power signal is used for global power grid)
        - Clk signal (optional)
        - Digital blocks (optional)
    * Library:(spice format)
        - A basic built-in template library is provided, which is used to identify elements in the design.
        - The user can add more template library elements in the user_template library.
    * param_lef:
        - A list of modules for which parameterized cell generator is available.
#### Outputs:
    * Verilog file (used for PnR): A hierarchical netlist
    * Inputs for the cell generator: parameters for the parameterized cell generator (the next stage of the ALIGN flow)

#### Getting started

    * Requirements:
        - Python3.8
        - networkx
        - matplotlib
        - pyyaml
    * Installation and usage is integrated with top level ALIGN flow

#### Features
An integrated flow using a combination of library-based and rule-based methods is used for automatic annotation. We support a Docker-based flow as it helps in minimizing environment setup issues.

**Library-based annotation**
    - Library based annotation is used for identifying smaller circuits (primitives) in the design. We use VF2 based subgraph isomorphism to map library elements to the circuit.

**Rule-based annotation**
    - Analog designs are dominated by arrays in the circuits which need a structured layout. To identify array structures in the layout, we use graph traversal, which is then used to identify common centroid constraints that must be enforced.
