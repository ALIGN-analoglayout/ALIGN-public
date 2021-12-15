ALIGN: flow
===========================================================

The ALIGN flow includes the following steps:

* *Circuit annotation* creates a multilevel hierarchical representation of the input netlist. This representation is used to implement the circuit layout in using a hierarchical manner.

* *Design rule abstraction* creates a compact JSON-format represetation of the design rules in a PDK. This repository provides a mock PDK based on a FinFET technology (where the parameters are based on published data). These design rules are used to guide the layout and ensure DRC-correctness.

* *Primitive cell generation* works with primitives, i.e., blocks the lowest level of design hierarchy, and generates their layouts. Primitives typically contain a small number of transistor structures (each of which may be implemented using multiple fins and/or fingers). A parameterized instance of a primitive is automatically translated to a GDSII layout in this step.

* *Placement and routing* performs block assembly of the hierarchical blocks in the netlist and routes connections between these blocks, while obeying a set of analog layout constraints. At the end of this step, the translation of the input SPICE netlist to a GDSII layout is complete.

.. image:: ../images/architecture.png

Inputs
---------

* Design netlist (SPICE format): Input from designers

	* `Example <https://github.com/ALIGN-analoglayout/ALIGN-public/tree/master/examples/telescopic_ota/telescopic_ota.sp>`_ of the analog circuit.

* Library (SPICE format): Commonly used basic building blocks for analog design

	* Basic built\-in `template library <https://github.com/ALIGN-analoglayout/ALIGN-public/blob/master/align/config/basic_template.sp>`_ is provided to identify hierachies in the design.

	* More library elements can be added in the `user_template_library <https://github.com/ALIGN-analoglayout/ALIGN-public/blob/master/align/config/user_template.sp>`_.

	* Each of the library elements can be associated with a set of constraints.

* PDK rules (JSON format): Abstracted `design rules <https://github.com/ALIGN-analoglayout/ALIGN-public/tree/master/pdks/FinFET14nm_Mock_PDK>`_

	* Mock FinFET 14nm PDK `rules file <https://github.com/ALIGN-analoglayout/ALIGN-public/tree/master/pdks/FinFET14nm_Mock_PDK/layers.json>`_ is provided, which is used by the primitive cell generator and the place and route engine.

	* New PDK can be represented using a JSON\-format design rule abstraction, similar to mock\-PDK design rules file provided.

	* Primitive cells (NMOS/PMOS/Resistor/Capacitor) must be redefined for any new PDK.

* Generators (JSON format): PDK specific primitive generators

	* List of parameterized generators supported by PDK cell generator (`generators <https://github.com/ALIGN-analoglayout/ALIGN-public/blob/master/pdks/FinFET14nm_Mock_PDK/generators.json>`_).

* User constraints (JSON format): Design constraints provided for each netlist hierachy by the designer.

	* ALIGN auto-generates constraints and also provide the designers to control the generated layout using a set of constraints e.g., `file.const.json <https://github.com/ALIGN-analoglayout/ALIGN-public/blob/master/examples/high_speed_comparator/high_speed_comparator.const.json>`_ of user defined constraints.


Outputs
---------

* Layout GDS: Final layout of the design. The output GDS can be imported into any GDSII viewer.

* Design JSON: Final layout which can be viewed using the ALIGN Viewer.

* Layout image: .jpg format of the layout saved using the `KLayout tool <https://github.com/KLayout/klayout>`_.
