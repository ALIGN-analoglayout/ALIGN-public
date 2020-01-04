# INPUT for PnR tool
sc_block.v : block level netlist for switched capacitor  
&nbsp;&nbsp;&nbsp;This netlist contains two modules which need to be placed and routed hierarchicaly.  
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;1.switched_capacitor_filter : top level module , corresponding constraint are there in switched_capacitor_filter.const  
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;2.telescopic_ota : sub module , corresponding constraint are there in telescopic_ota.const  
        
sc.lef : lef file with block dimensions and pin locations

# BLOCKS used (defined in lef, used in netlist)
1.CMC_NMOS_25_1 : common centroid transistors with gate connection  
2.CMC_PMOS_10_1 : common centroid transistors with gate connection  
3.CMC_PMOS_15_1 : common centroid transistors with gate connection  
4.DP_NMOS_70_1 : Differential pair  
5.SCM_NMOS_50 : current mirror  
6.Cap_xxf: capacitance  
7.Switch_NMOS_10 : transistor building block with 10 fins  
8.Switch_PMOS_10 : transistor building block with 10 fins
