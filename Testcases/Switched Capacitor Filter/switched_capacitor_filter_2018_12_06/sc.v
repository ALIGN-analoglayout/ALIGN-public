// Verilog HDL and netlist files of
// "pcell switched_capacitor_filter schematic"

// Netlisted models

// Library - pcell, Cell - switched_capacitor_filter, View -
//schematic
// LAST TIME SAVED: Aug 30 07:08:50 2018
// NETLIST TIME: Nov 13 07:44:10 2018
`timescale 1ns / 1ns 


module switched_capacitor_filter ( Vinp, Vinn, Vbiasp2_ota, Vbiasp1_ota, Vbiasn_ota, phi2, phi1, agnd );


specify 
    specparam CDS_LIBNAME  = "pcell";
    specparam CDS_CELLNAME = "switched_capacitor_filter";
    specparam CDS_VIEWNAME = "schematic";
endspecify

//vdc  V5 ( .PLUS(cds_globals.vdd_), .MINUS(cds_globals.gnd_));
//vdc  V4 ( .PLUS(Vinp), .MINUS(cds_globals.gnd_));
//vdc  V3 ( .PLUS(Vinn), .MINUS(cds_globals.gnd_));
//vdc  V2 ( .PLUS(Vbiasp2), .MINUS(cds_globals.gnd_));
//vdc  V1 ( .PLUS(Vbiasp1), .MINUS(cds_globals.gnd_));
//vdc  V0 ( .PLUS(Vbiasn), .MINUS(cds_globals.gnd_));
SCM_NMOS_50_1x12 L1_MM4_MM3 ( .D1(net1_ota), .D2(net6_ota), .S(GND) );
CMC_NMOS_25_1x10 L1_MM10_MM2 ( .D1(Voutn), .D2(Voutp), .G(Vbiasn_ota), .S1(net10_ota), .S2(net11_ota) );
CMC_PMOS_15_1x6 L1_MM7_MM6 ( .D1(Voutn), .D2(Voutp), .G(Vbiasp1_ota), .S1(net13_ota), .S2(net12_ota) );
CMC_PMOS_10_1x4 L1_MM8_MM9 ( .D1(net13_ota), .D2(net12_ota), .G(Vbiasp2_ota), .S(VDD) );
DP_NMOS_75_3x10 L1_MM1_MM0 ( .D1(net10_ota), .D2(net11_ota), .G1(Vinp_ota), .G2(Vinn_ota), .S(net6_ota) );
//cascode_current_mirror_ota I0 ( .Voutn(Voutn), .Voutp(Voutp), .Vbiasn(Vbiasn), .Vbiasp1(Vbiasp1), .Vbiasp2(Vbiasp2), .Vinn(net23), .Vinp(net7));
Cap_60f_2x3 CC8 ( .PLUS(Voutp), .MINUS(GND));
Cap_60f_2x3 CC9 ( .PLUS(Voutn), .MINUS(GND));
Cap_60f_2x3 CC2 ( .PLUS(Vinp_ota), .MINUS(Vinp));
Cap_60f_2x3 CC6 ( .PLUS(net5), .MINUS(net4));
Cap_60f_2x3 CC0 ( .PLUS(Vinn_ota), .MINUS(Vinn));
Cap_60f_2x3 CC4 ( .PLUS(net6), .MINUS(net3));
Cap_32f_1x1 CC3 ( .PLUS(net6), .MINUS(net12));
Cap_32f_1x1 CC7 ( .PLUS(Vinp_ota), .MINUS(Voutn));
Cap_32f_1x1 CC1 ( .PLUS(net5), .MINUS(net11));
Cap_32f_1x1 CC5 ( .PLUS(Vinn_ota), .MINUS(Voutp));
Switch_NMOS_10_1x1  L0_MM11 ( .S(net12), .G(phi1), .D(agnd));
Switch_NMOS_10_1x1  L0_MM10 ( .S(net3), .G(phi2), .D(agnd));
Switch_NMOS_10_1x1  L0_MM9 ( .S(net6), .G(phi2), .D(agnd));
Switch_NMOS_10_1x1  L0_MM8 ( .S(Voutp), .G(phi2), .D(net12));
Switch_NMOS_10_1x1  L0_MM7 ( .S(net11), .G(phi2), .D(Voutn));
Switch_NMOS_10_1x1  L0_MM6 ( .S(agnd), .G(phi1), .D(net11));
Switch_NMOS_10_1x1  L0_MM5 ( .S(agnd), .G(phi2), .D(net5));
Switch_NMOS_10_1x1  L0_MM4 ( .S(agnd), .G(phi2), .D(net4));
Switch_NMOS_10_1x1  L0_MM3 ( .S(net5), .G(phi1), .D(Vinp_ota));
Switch_NMOS_10_1x1  L0_MM2 ( .S(Vinn), .G(phi1), .D(net4));
Switch_NMOS_10_1x1  L0_MM1 ( .S(Vinn_ota), .G(phi1), .D(net6));
Switch_NMOS_10_1x1  L0_MM0 ( .S(net3), .G(phi1), .D(Vinp));
//vpulse  V7 ( .PLUS(phi2), .MINUS(cds_globals.gnd_));
//vpulse  V6 ( .PLUS(phi1), .MINUS(cds_globals.gnd_));

endmodule

`endcelldefine
// End HDL models
// Global nets module 
