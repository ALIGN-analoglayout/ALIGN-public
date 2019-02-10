// Verilog HDL and netlist files of
// "pcell switched_capacitor_filter schematic"

// Netlisted models

// Library - pcell, Cell - cascode_current_mirror_ota, View - schematic
// LAST TIME SAVED: Aug 30 07:09:12 2018
// NETLIST TIME: Nov 13 07:44:10 2018
`timescale 1ns / 1ns 


module cascode_current_mirror_ota ( Voutn, Voutp, Vbiasn, Vbiasp1,
     Vbiasp2, Vinn, Vinp );

output  Voutn, Voutp;

input  Vbiasn, Vbiasp1, Vbiasp2, Vinn, Vinp;


specify 
    specparam CDS_LIBNAME  = "pcell";
    specparam CDS_CELLNAME = "cascode_current_mirror_ota";
    specparam CDS_VIEWNAME = "schematic";
endspecify

SCM_NMOS_X50 L1_MM4_MM3 ( .D1(net1), .D2(net6), .S(cds_globals.gnd_) );
CMC_NMOS_X40 L1_MM10_MM2 ( .D1(Voutn), .D2(Voutp), .G(Vbiasn), .S1(net10), .S2(net11) );
CMC_PMOS_X40 L1_MM7_MM6 ( .D1(Voutn), .D2(Voutp), .G(Vbiasp1), .S1(net13), .S2(net12) );
CMC_PMOS_X70 L1_MM8_MM9 ( .D1(net13), .D2(net12), .G(Vbiasp2), .S1(cds_globals.vdd_), .S1(cds_globals.vdd_) );
DP_NMOS_X50 L1_MM1_MM0 ( .D1(net10), .D2(net11), .G1(Vinp), .G2(Vinn), .S(net6) )
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
cascode_current_mirror_ota I0 ( Voutn, Voutp, Vbiasn, Vbiasp1, Vbiasp2,
     net23, net7);
matching_cap_X1 L1_CC0_CC2 ( .CN1(Voutp), .CN2(Voutn), .CP1(net23), .CP2(net7));
matching_cap_X1 L1_CC5_CC7 ( .CN1(Vinp), .CN2(Vinn), .CP1(net23), .CP2(net7));
matching_cap_X1 L1_CC1_CC3 ( .CN1(net11), .CN2(net12), .CP1(net5), .CP2(net6));
matching_cap_X1 L1_CC4_CC6 ( .CN1(net3), .CN2(net4), .CP1(net6), .CP2(net5));
nmos_rvt  L0_MM11 ( .B(cds_globals.gnd_), .S(net12), .G(phi1),
     .D(cds_globals.gnd_));
nmos_rvt  L0_MM10 ( .B(cds_globals.gnd_), .S(net3), .G(phi2),
     .D(cds_globals.gnd_));
nmos_rvt  L0_MM9 ( .B(cds_globals.gnd_), .S(net6), .G(phi2),
     .D(cds_globals.gnd_));
nmos_rvt  L0_MM8 ( .B(cds_globals.gnd_), .S(Voutp), .G(phi2), .D(net12));
nmos_rvt  L0_MM7 ( .B(cds_globals.gnd_), .S(net11), .G(phi2), .D(Voutn));
nmos_rvt  L0_MM6 ( .B(cds_globals.gnd_), .S(cds_globals.gnd_), .G(phi1),
     .D(net11));
nmos_rvt  L0_MM5 ( .B(cds_globals.gnd_), .S(cds_globals.gnd_), .G(phi2),
     .D(net5));
nmos_rvt  L0_MM4 ( .B(cds_globals.gnd_), .S(cds_globals.gnd_), .G(phi2),
     .D(net4));
nmos_rvt  L0_MM3 ( .B(cds_globals.gnd_), .S(net5), .G(phi1), .D(net7));
nmos_rvt  L0_MM2 ( .B(cds_globals.gnd_), .S(Vinn), .G(phi1), .D(net4));
nmos_rvt  L0_MM1 ( .B(cds_globals.gnd_), .S(net23), .G(phi1), .D(net6));
nmos_rvt  L0_MM0 ( .B(cds_globals.gnd_), .S(net3), .G(phi1), .D(Vinp));
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
