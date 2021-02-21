Writing your setup file
===========================================================

The ALIGN flow provides multiple configuration options to designers using the setup file.
The ALIGN flow creates array-based hierarchies and library-based hierarchies. It also generates automatic symmetry constraints. 
The symmetry constraints between caps uses a common-centroid cap placer.
The setup file uses text format and can be used as a switch to turn some of these features on/off. 
This file is defined only for top hierarchy with the name ``<top>.setup`` . Format for this file is space separated names

    * Format: ``Property = a1 a2 a3`` 

Here are the list of controls available to designers.

Setup options
---------------

* DONT_USE_CELLS:
	Defines the list of library cells which should not be used during annotation.

	* Example: ``DONT_USE_CELLS = l1 l2 l3``

* POWER:
    Defines power nets in the design. The first net name will be used for grid. 
    During preprocessing we identify source and drain ports of the transistors based on the condition, that for NMOS cells, Drain should have higher potential than Source pin, while for PMOS cells, Source pin should have higher potential. 	During constraint generation POWER, GND, and CLOCK nets will be used as stop-points.

	* Example: ``POWER = vdd avdd``

* GND:
    Defines power nets in the design. The first net name will be used for grid. 
    During preprocessing we identify source and drain ports of the transistors based on the condition, that for NMOS cells, Drain should have higher potential than Source pin, while for PMOS cells, Source pin should have higher potential. During constraint generation POWER, GND, and CLOCK nets will be used as stop-points.

	* Example: ``GND = vss avss``

* CLOCK:
	Defines clock nets in the design.
	During constraint generation POWER,GND,and CLOCK nets will be used as stop-points.

	* Example: ``CLOCK = clk``

* DIGITAL: 
	For the blocks defined under this condition the annotation only matches them to transistors. Annotation and constraint generation will be skipped for these blocks.

	* Example: ``DIGITAL = NAND NOR``

* NO_CONST: 
	For the blocks defined under this condition the annotation identifies further hierarchies in them but no constraints will be generated for these blocks. 
	
	* Example: ``NO_CONST = TGATE BIAS``

* NO_ARRAY: 
	Array hierarchies are identified in the design and new hierarchies are created for these. You can turn this feature off by defining the hierarchy in which arrays are generated.

	* Example: ``NO_ARRAY = DAC CDAC``

* MERGE_SYMM_CAPS:
	For the symmetrical caps in the design, align generates a common centroid layout. You can turn this feature off by using this switch.

	* Example: ``MERGE_SYMM_CAPS = True``

Example setup file
---------------------
.. code-block:: none

	#filename: high_speed_comparator.setup
	POWER = vcc
	GND = vss
	CLOCK = clk
	DIGITAL =