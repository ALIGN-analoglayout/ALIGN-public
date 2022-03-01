# What should we store on disk so we can do flow stage runs?

Currently:

```
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
		
