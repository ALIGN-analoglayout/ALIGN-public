# What should we store on disk so we can do flow stage runs?

Currently: (no --skipGDS switch)

```
<toplevel>_0.errors
<toplevel>_0.gds
<toplevel>_0.lef
<toplevel>_0.python.gds

1_topology/
	__primitives_library__.json
	<toplevel>.verilog.json
	
2_primitives/
	__primitives__.json
	<<for each leaf>>
		<leaf>.gds.json
		<leaf>.json
		<leaf>.lef
		<leaf>.placement_lef
		
3_pnr/
	__capacitors__.json

	global_router.plt
	global_router_plt.json

	<<for each CC capacitor>>
		<cap>.gds.json
		<cap>.json
		
	<<for each intermediate block>>
		<block>_0_0.errors
		<block>_0_0.json
		<block>_0_0.python.gds.json
		
	<toplevel>_0.errors
	<toplevel>_0.json
	<toplevel>_0.python.gds.json

	inputs/
		layers.json
		<<for each leaf>>
			<leaf>.gds.json
			<leaf>.json
		<<for each intermediate block>>
			<block>.pnr.const.json
		<toplevel>.verilog.json
		<toplevel>.abstract_verilog.json
		<toplevel>.scaled_placement_verilog.json
		<toplevel>.lef
		<toplevel>.placement_lef
		<toplevel>.map
		<toplevel>.pnr.const.json

	Results/
		Router_Report.txt
		<<for each CC capacitor>>
			<cap>.gds.json
			<cap>.json
			<cap>.lef
			<cap>.plt
		<<for each intermediate block>>
			<block>_0_0.gds.json
			<block>_0_0.lef
			<block>_0.pl
			<block>_0.plt
			<block>_0.placement_verilog.json
			<block>_0.scaled_placement_verilog.json
			<block>_DR_0_0.json
			<block>_GcellGlobalRoute_0_0.json

	    <toplevel>_0.gds.json
		<toplevel>_0.lef
		<toplevel>_0.pl
		<toplevel>_0.plt
		<toplevel>_0.placement_verilog.json
		<toplevel>_0.scaled_placement_verilog.json
		<toplevel>_DR_0.gds.json
		<toplevel>_PG_0.gds.json
		<toplevel>_PR_0.gds.json
		<toplevel>_GcellGlobalRoute_0.json
```

Currently: (no --skipGDS switch)

```
<toplevel>_0.errors

1_topology/
	__primitives_library__.json
	<toplevel>.verilog.json
	
2_primitives/
	__primitives__.json
	<<for each leaf>>
		<leaf>.gds.json
		<leaf>.json
		<leaf>.lef
		<leaf>.placement_lef
		
3_pnr/
	__capacitors__.json                                        Only needed to know which files to move

	global_router.plt                                          No idea what this does.
	global_router_plt.json                                     Or this

	<<for each CC capacitor>>
                <cap>.gds.json                                     cap collateral is copied to here
		<cap>.json                                         ""
		
	<<for each intermediate block>>
		<block>_0_0.errors                                 Error list
		<block>_0_0.json                                   Output rectangles
		
	<toplevel>_0.errors                                        Error list
	<toplevel>_0.json                                          Output rectangles

	inputs/
		layers.json                                        Copied from PDK
		<<for each leaf>>
			<leaf>.gds.json                            Copied from primitives
			<leaf>.json                                ""
		<<for each intermediate block>>
			<block>.pnr.const.json                     Std Constraints translated to PNR constraints
		<toplevel>.verilog.json                            Original input (possibly modified from 1_topology/
		<toplevel>.placement_lef			   Rollup of all lef files needed for placement (abstract pins)
		<toplevel>.lef                                     Rollup of all lef files needed for routing (concrete pins)
		<toplevel>.map                                     Which concrete names implement with abstract names
		<toplevel>.pnr.const.json                          Std Constraints translated to PNR constraints
		<toplevel>.abstract_verilog.json                   Choosen placement result (placement info removed)
		<toplevel>.scaled_placement_verilog.json           Choosen placement result (in scale factor units)


	Results/
		Router_Report.txt
		<<for each CC capacitor>>
			<cap>.gds.json                             GDS json for cap
			<cap>.json                                 Rectangles for cap
			<cap>.lef                                  LEF for cap
			<cap>.plt                                  GNUplot placement vis.
		<<for each intermediate block>>
			<block>_0.pl                               GNUplot placement vis.
			<block>_0.plt                              GNUplot placement vis. 

		<toplevel>_0.pl                                    GNUplot placement vis.
		<toplevel>_0.plt                                   GNUplot placement vis.
```		
