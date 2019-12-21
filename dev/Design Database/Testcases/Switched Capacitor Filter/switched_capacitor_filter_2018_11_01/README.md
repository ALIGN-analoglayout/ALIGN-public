# INPUT for PnR tool
sc_block.v : block level netlist for switched capacitor  
&nbsp;&nbsp;&nbsp;This netlist contains two modules which need to be placed and routed hierarchicaly.  
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;1.switched_capacitor_filter : top level module , corresponding constraint are there in switched_capacitor_filter.const  
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;2.cascode_current_mirror_ota : sub module , corresponding constraint are there in cascode_current_mirror_ota.const  
        
sc.lef : lef file with block dimensions and pin locations

sc_transistor.v : transistor level netlist (not required for PnR/ redundant)

# BLOCKS used (defined in lef, used in netlist)
1.CMC_NMOS_X40 : common centroid transistors with gate connection  
2.CMC_PMOS_X40 : common centroid transistors with gate connection  
3.CMC_PMOS_X70 : common centroid transistors with gate connection  
4.DP_NMOS_X50 : Differential pair  
5.SCM_NMOS_X50 : current mirror  
6.matching_cap_X1: capacitance  
7.nmos_rvt : transistor building block with 10 fins  
8.pmos_rvt : transistor building block with 10 fins  

X50 : denotes number of fins in parallel

