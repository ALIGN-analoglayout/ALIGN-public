ALIGN: flow
===========================================================

The ALIGN flow includes the following steps:

* *Circuit annotation* creates a multilevel hierarchical representation of the input netlist. This representation is used to implement the circuit layout in using a hierarchical manner. 

* *Design rule abstraction* creates a compact JSON-format represetation of the design rules in a PDK. This repository provides a mock PDK based on a FinFET technology (where the parameters are based on published data). These design rules are used to guide the layout and ensure DRC-correctness.

* *Primitive cell generation* works with primitives, i.e., blocks the lowest level of design hierarchy, and generates their layouts. Primitives typically contain a small number of transistor structures (each of which may be implemented using multiple fins and/or fingers). A parameterized instance of a primitive is automatically translated to a GDSII layout in this step.

* *Placement and routing* performs block assembly of the hierarchical blocks in the netlist and routes connections between these blocks, while obeying a set of analog layout constraints. At the end of this step, the translation of the input SPICE netlist to a GDSII layout is complete. 

Inputs
---------

 * A `SPICE netlist <https://github.com/ALIGN-analoglayout/ALIGN-public/tree/master/examples/telescopic_ota/telescopic_ota.sp>`_ of the analog circuit

 * `Setup file <https://github.com/ALIGN-analoglayout/ALIGN-public/tree/master/examples/telescopic_ota/telescopic_ota.setup>`_

	* Power and Gnd signals (First power signal is used for global power grid)

	* Clk signal (optional)

	* Digital blocks (optional)

 * Library:(SPICE format)

	* A basic built\-in `template library <https://github.com/ALIGN-analoglayout/ALIGN-public/blob/master/align/config/basic_template.sp>`_ is provided, which is used to identify hierachies in the design.

	* More library elements can be added in the `user_template_library <https://github.com/ALIGN-analoglayout/ALIGN-public/blob/master/align/config/user_template.sp>`_.

 * PDK: Abstracted `design rules <https://github.com/ALIGN-analoglayout/ALIGN-public/tree/master/pdks/FinFET14nm_Mock_PDK>`_

	* A mock FinFET 14nm PDK `rules file <https://github.com/ALIGN-analoglayout/ALIGN-public/tree/master/pdks/FinFET14nm_Mock_PDK/layers.json>`_ is provided, which is used by the primitive cell generator and the place and route engine.

	* A new PDK can be represented using a JSON\-format design rule abstraction, similar to mock\-PDK design rules file provided.

	* Primitive cells (NMOS/PMOS/Resistor/Capacitor) must be redefined for any new PDK.

 * LEF:

	* A list of parameterized cells supported by cell generator is stored in file `param_lef <https://github.com/ALIGN-analoglayout/ALIGN-public/blob/master/align/config/param_lef>`_.

Outputs
---------

 * Layout GDS: Final layout of the design. The output GDS can be imported into any GDSII viewer.

 * Design JSON: Final layout which can be viewed using the ALIGN Viewer.

 * Layout image: .jpg format of the layout saved using the `KLayout tool <https://github.com/KLayout/klayout>`_.

	

