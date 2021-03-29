How to add your own constraints
===========================================================

The ALIGN flow generates symmetry constraints automatically but users can add their own constraint for better control.
Here, are the list of constraints used in align. These constraints are applied on the blocks (instances of NMOS/PMOS/Resistor/Capacitor/Subcircuit) or on nets.
These constraints need to be defined seperately for each of the hierachies with name ``<hier name>.const``, defined in the schematic.

Constraint options
--------------------

* CreateAlias:
	Defines an alias for group of blocks. These aliases can be later used in the const file in place of list of blocks or nets.

	* Example: ``CreateAlias -blocks [B1,B2,B3] -name alias1``

* GroupBlocks:
	We can create extra hierarchies in the design by grouping blocks. This helps in bringing the blocks closer. 
	We are planning to implement placement type, such as common-centroid, interdigitated for these hierarchies.

	* Format: ``GroupBlocks -blocks <list of blocks> -name <name of the group>``
	* Example1: ``GroupBlocks -blocks [B1,B2,B3] -name group1``
	* Example2: ``GroupBlocks -blocks alias1 -name group1``

* OrderBlocks:
	Pleaces the blocks in the specified order.

	* Format: ``OrderBlocks -blocks <list of blocks> -direction H/V``
	* Example: ``OrderBlocks -blocks alias1 -direction H``

	.. image:: images/OrderBlocks.PNG

* MatchBlocks:
	Assigns two blocks as close as possible.

	* Format: ``MatchBlocks -blocks <list of two blocks>``
	* Example: ``MatchBlocks -blocks [B1,B2]``

* HorizontalDistance: 
	Set the minimum horizontal distance between all blocks in the hierarchy.

	* Format: ``HorizontalDistance -abs_distance <in nanometers>``
	* Example: ``HorizontalDistance -abs_distance 108``

	.. image:: images/HorizontalDistance.PNG

* VerticalDistance: 
	Set the minimum vertical distance between all blocks in the hierarchy.

	* Format: ``VerticalDistance -abs_distance <in nanometers>``
	* Example: ``VerticalDistance -abs_distance 108``

	.. image:: images/VerticalDistance.PNG

* BlockDistance: 
	Set the minimum vertical and horizontal distance between all blocks in the hierarchy.

	* Format: ``BlockDistance -abs_distance <in nanometers>``
	* Example: ``BlockDistance -abs_distance 108``

	.. image:: images/VerticalDistance.PNG
	.. image:: images/HorizontalDistance.PNG

* AspectRatio:
	Sets the aspect ratio of hierarchy 

	* Format: ``AspectRatio -weight <value>``
	* Example: ``AspectRatio -weight 500``

* SymmetricBlocks:
	Placed pairs of modules symmetrically along a vertical or horizontal symmetry axis. 
	In case of one block in the pair, the block gets placed self-symmetrically.

	* Format: ``SymmetricBlocks -pairs <list of pairs> -direction H/V``
	* Example: ``SymmetricBlocks -pairs [alias1,[B3],[B4,B5]] -direction V``

	.. image:: images/SymmetricBlocks.PNG

* AlignBlocks:
	Aligns blocks horizontally or vertically.

	* Format: ``AlignBlocks -blocks <list of blocks> -direction H/V``
	* Example: ``AlignBlocks -blocks -alias1 -direction V``

	.. image:: images/AlignBlocks.PNG

* GroupCaps:
	Common centroid capacitor placement and routing. Adds an extra level of hierarchy for the group of capacitors.

	* Format: ``GroupCaps -blocks <list of blocks> -name (optional) <name of cap hierarchy> -unit_cap <unit capacitor name" -num_units <list of units of each capacitor> -dummy True/False``
	* Example: ``GroupCaps -blocks [c1,c2,c3] -name c1_c2_c3 -unit_cap Cap_12f -num_units [1,2,4] -dummy False``

* NetConst:
	Adds constraints on each of the nets in the list.

	* Format: ``NetConst -nets <list of nets> -shield (optional) None/vss -criticality (optional) <value>``
	* Example: ``NetConst -nets [n1,n2,n3] -shield vss -criticality 200``

* PortLocation:
	Set the terminal location. This constraint only works in top level. Currently, there are 9 locations:  TL, TC, TR; RT, RC, RB; BL, BC, BR; LB, LC, LT.
	T (top), L (left), C (center), R (right), B (bottom).

	* Format: ``PortLocation -ports <list of ports> -location <TL/TC/...>``
	* Example: ``PortLocation -ports [P1,P2,P3] -location TL``

* SymmetricNets:
	Routes two nets in mirror symmetric fashion. For each symmetric net pair you can optionally add pins connected to the nets. For transistor pins please use [D, G, S, B] and for resistors use [PLUS, MINUS] as pin names.

	* Format: ``SymmetricNets -net1 < name of net1> -net2 <name of net2> -pins1(optional) <list of pins of net1> -pins2(optional) <list of nets in same order as pins1> -direction H/V``
	* Example: ``SymmetricNets -net1 neta -net2 netb -pins1 [M1/D,B2/out1] -pins2(optional) [M2/D,B2/out2] -direction V``
	* Example: ``SymmetricNets -net1 neta -net2 netb -direction V``

* MultiConnection:
	Uses multiple parallel wires to route these nets.

	* Format: ``MultiConnection -nets <list of nets> -multiplier <value>``
	* Example: ``MultiConnection -nets [n1,n2] -multiplier 5``


Using JSON format as input:
	ALIGN can also take JSON format input of the constraints. There is direct translation from cmdline format to JSON format. The file names for these JSON constraints should be ``<hier name>.const.json``.
	If both formats are provided as input, only JSON format will be read for that hierarchy

	* Format (cmd): ``CreateAlias -blocks [B1,B2,B3] -name alias1``
	* Format (JSON): ``{"const_name":"CreateAlias", "blocks": ["B1","B2","B3"], "name"  : "alias1"}``

Example constraints (command-line interface)
---------------------------------------------
.. code-block:: python3

	#filename: high_speed_comparator.const
	HorizontalDistance -abs_distance 0
	VerticalDistance -abs_distance 0
	GroupBlocks -blocks [mmn0,mmn1] -name diffpair
	GroupBlocks -blocks [mmn4,mmn3] -name ccn
	GroupBlocks -blocks [mmp1,mmp0] -name ccp
	SymmetricBlocks -pairs [[mmn2], [diffpair] , [ccn] , [ccp]] -direction V
	OrderBlocks -blocks [mmn2, diffpair, ccn, ccp] -direction V

Example constraints (JSON format)
-----------------------------------
.. code-block:: python3

	#filename: high_speed_comparator.const.json
	{
	"constraints":[
		{   "const_name":"HorizontalDistance",
			"abs_distance":0
		},
		{   "const_name":"VerticalDistance",
			"abs_distance":0
		},
		{   "const_name": "GroupBlocks",
			"blocks": ["mmn0", "mmn1"],
			"name": "diffpair"
		},
		{   "const_name":"GroupBlocks",
			"blocks": ["mmn4", "mmn3"],
			"name": "ccn"
		},
		{   "const_name": "GroupBlocks",
			"blocks": ["mmp1", "mmp0"],
			"name": "ccp"
		},
		{   "const_name": "SymmetricBlocks",
			"direction" : "V",
			"pairs": [["mmn2"], ["diffpair"], ["ccn"], ["ccp"]]
		},
		{   "const_name": "OrderBlocks",
			"blocks": ["mmn2", "diffpair", "ccn", "ccp"],
			"direction": "V"
		}
		]
	}
