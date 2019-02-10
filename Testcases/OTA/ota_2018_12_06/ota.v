// Verilog HDL and netlist files of
// "pcell switched_capacitor_filter schematic"

// Netlisted models

// Library - pcell, Cell - cascode_current_mirror_ota, View - schematic
// LAST TIME SAVED: Aug 30 07:09:12 2018
// NETLIST TIME: Nov 13 07:44:10 2018


module cascode_current_mirror_ota ( Voutn, Voutp, Vinn, Vinp, Id );

//output  Voutn, Voutp;

//input  Vbiasn, Vbiasp1, Vbiasp2, Vinn, Vinp;

SCM_NMOS_50_1x12 L1_MM4_MM3 ( .D1(Id), .D2(net6), .S(GND) );
CMC_NMOS_25_1x10 L1_MM10_MM2 ( .D1(Voutn), .D2(Voutp), .G(net_vbiasn), .S1(net10), .S2(net11) );
CMC_PMOS_15_1x6 L1_MM7_MM6 ( .D1(Voutn), .D2(Voutp), .G(net_vbiasp), .S1(net13), .S2(net12) );
CMC_PMOS_10_1x4 L1_MM8_MM9 ( .D1(net13), .D2(net12), .G(net_vbiasp1), .S(VDD) );
DP_NMOS_75_3x10 L1_MM1_MM0 ( .D1(net10), .D2(net11), .G1(Vinp), .G2(Vinn), .S(net6) );
//bias transistors
DiodeConnected_NMOS_5_1x1 L0_MM17 ( .D(net_vbiasn), .S(net6) );

DiodeConnected_PMOS_10_1x2 L0_MM11 ( .D(net_vbiasp1), .S(VDD) );

//DiodeConnected_PMOS_20_1x4 L0_MM13 ( .D(net_vbiasp), .S(net1_vbiasp) );
DiodeConnected_PMOS_10_1x2 L0_MM131 ( .D(net_vbiasp), .S(net1_vbiasp) );
DiodeConnected_PMOS_10_1x2 L0_MM132 ( .D(net_vbiasp), .S(net1_vbiasp) );
DiodeConnected_PMOS_20_1x4 L0_MM14 ( .D(net1_vbiasp), .S(VDD) );

Switch_NMOS_10_1x1 L0_MM12 ( .D(net_vbiasp1), .G(Id), .S(GND) );
Switch_NMOS_10_1x1 L0_MM15 ( .D(net_vbiasp), .G(Id), .S(GND) );
Switch_PMOS_10_1x1 L0_MM16 ( .D(net_vbiasn), .G(net_vbiasp), .S(VDD) );

//dummy transistors
DiodeConnected_NMOS_5_1x1 L0_MM18 ( .D(GND), .S(GND) );


//idc  I3 ( .PLUS(cds_globals.vdd_), .MINUS(net1)); 

endmodule

// End HDL models

`endcelldefine
