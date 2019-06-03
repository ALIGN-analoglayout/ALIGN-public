// Verilog HDL and netlist files of
// "pcell switched_capacitor_filter schematic"

// Netlisted models

// Library - pcell, Cell - cascode_current_mirror_ota, View - schematic
// LAST TIME SAVED: Aug 30 07:09:12 2018
// NETLIST TIME: Nov 13 07:44:10 2018
`timescale 1ns / 1ns 


module cascode_current_mirror_ota ( Voutn, Voutp, Vbiasn, Vbiasp1, Vbiasp2, Vinn, Vinp );

output  Voutn, Voutp;

input  Vbiasn, Vbiasp1, Vbiasp2, Vinn, Vinp;


specify 
    specparam CDS_LIBNAME  = "pcell";
    specparam CDS_CELLNAME = "cascode_current_mirror_ota";
    specparam CDS_VIEWNAME = "schematic";
endspecify

SCM_NMOS_50_1x12 L1_MM4_MM3 ( .D1(net1), .D2(net6), .S(cds_globals.gnd_) );
CMC_NMOS_25_1x10 L1_MM10_MM2 ( .D1(Voutn), .D2(Voutp), .G(Vbiasn), .S1(net10), .S2(net11) );
CMC_PMOS_15_1x6 L1_MM7_MM6 ( .D1(Voutn), .D2(Voutp), .G(Vbiasp1), .S1(net13), .S2(net12) );
CMC_PMOS_10_1x4 L1_MM8_MM9 ( .D1(net13), .D2(net12), .G(Vbiasp2), .S(cds_globals.vdd_) );
DP_NMOS_75_3x10 L1_MM1_MM0 ( .D1(net10), .D2(net11), .G1(Vinp), .G2(Vinn), .S(net6) );
//idc  I3 ( .PLUS(cds_globals.vdd_), .MINUS(net1)); 

endmodule
// Library - pcell, Cell - switched_capacitor_filter, View -
//schematic
// LAST TIME SAVED: Aug 30 07:08:50 2018
// NETLIST TIME: Nov 13 07:44:10 2018
`timescale 1ns / 1ns 


module switched_capacitor_filter ( Vinp, Vinn, Vbiasp2, Vbiasp1, Vbiasn, phi2, phi1 );


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
cascode_current_mirror_ota I0 ( .Voutn(Voutn), .Voutp(Voutp), .Vbiasn(Vbiasn), .Vbiasp1(Vbiasp1), .Vbiasp2(Vbiasp2), .Vinn(net23), .Vinp(net7) );
Cap_60f_2x3 CC7 ( .PLUS(net7), .MINUS(Vinp) );
Cap_60f_2x3 CC6 ( .PLUS(net5), .MINUS(net4) );
Cap_60f_2x3 CC5 ( .PLUS(net23), .MINUS(Vinn) );
Cap_60f_2x3 CC4 ( .PLUS(net6), .MINUS(net3) );
Cap_32f_1x1 CC3 ( .PLUS(net6), .MINUS(net12) );
Cap_32f_1x1 CC2 ( .PLUS(net7), .MINUS(Voutn) );
Cap_32f_1x1 CC1 ( .PLUS(net5), .MINUS(net11) );
Cap_32f_1x1 CC0 ( .PLUS(net23), .MINUS(Voutp) );
Switch_NMOS_10_1x1 L0_MM11 ( .S(net12), .G(phi1), .D(cds_globals.gnd_) );
Switch_NMOS_10_1x1 L0_MM10 ( .S(net3), .G(phi2), .D(cds_globals.gnd_) );
Switch_NMOS_10_1x1 L0_MM9 ( .S(net6), .G(phi2), .D(cds_globals.gnd_) );
Switch_NMOS_10_1x1 L0_MM8 ( .S(Voutp), .G(phi2), .D(net12) );
Switch_NMOS_10_1x1 L0_MM7 ( .S(net11), .G(phi2), .D(Voutn) );
Switch_NMOS_10_1x1 L0_MM6 ( .S(cds_globals.gnd_), .G(phi1), .D(net11) );
Switch_NMOS_10_1x1 L0_MM5 ( .S(cds_globals.gnd_), .G(phi2), .D(net5) );
Switch_NMOS_10_1x1 L0_MM4 ( .S(cds_globals.gnd_), .G(phi2), .D(net4) );
Switch_NMOS_10_1x1 L0_MM3 ( .S(net5), .G(phi1), .D(net7) );
Switch_NMOS_10_1x1 L0_MM2 ( .S(Vinn), .G(phi1), .D(net4) );
Switch_NMOS_10_1x1 L0_MM1 ( .S(net23), .G(phi1), .D(net6) );
Switch_NMOS_10_1x1 L0_MM0 ( .S(net3), .G(phi1), .D(Vinp) );
//vpulse  V7 ( .PLUS(phi2), .MINUS(cds_globals.gnd_));
//vpulse  V6 ( .PLUS(phi1), .MINUS(cds_globals.gnd_));

endmodule


// End HDL models
// Global nets module 

`celldefine
module cds_globals;


supply0 gnd_;

supply1 vdd_;


endmodule
`endcelldefine
