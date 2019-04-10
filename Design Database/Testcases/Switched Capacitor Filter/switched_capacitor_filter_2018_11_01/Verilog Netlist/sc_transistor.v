// Verilog HDL and netlist files of
// "pcell switched_capacitor_filter schematic"

// Netlisted models

// Library - pcell, Cell - cascode_current_mirror_ota, View - schematic
// LAST TIME SAVED: Aug 30 07:09:12 2018
// NETLIST TIME: Nov 13 07:44:10 2018
`timescale 1ns / 1ns 
module SCM_NMOS_X50 ( D1, S, D2 );

inout D1, S, D2;

nmos_rvt  M4 ( .B(cds_globals.gnd_), .S(S), .G(D1),
     .D(D1));
nmos_rvt  M3 ( .B(cds_globals.gnd_), .S(S), .G(D1),
     .D(D2));

endmodule
        
module CMC_NMOS_X40 ( D1, S1, S2, D2, G );

inout D1, S1, S2, D2, G;

nmos_rvt  M10 ( .B(cds_globals.gnd_), .S(S1), .G(G),
     .D(D1));
nmos_rvt  M2 ( .B(cds_globals.gnd_), .S(S2), .G(G), .D(D2));

endmodule

module CMC_PMOS_X40 ( D1, S1, S2, D2, G );

inout D1, S1, S2, D2, G;

pmos_rvt  M7 ( .B(S1), .S(S1), .G(G), .D(D1));
pmos_rvt  M6 ( .B(S2), .S(S2), .G(G), .D(D1));

endmodule


module CMC_PMOS_X70 ( D1, S1, S2, D2, G );

inout D1, S1, S2, D2, G;

pmos_rvt  M9 ( .B(S1), .S(S1), .G(G), .D(D1));
pmos_rvt  M8 ( .B(S2), .S(S2), .G(G), .D(D1));

endmodule
 
module DP_NMOS_X50 ( D1, S, D2, G1, G2 );

inout D1, S, D2, G1, G2;

nmos_rvt  M1 ( .B(cds_globals.gnd_), .S(S), .G(G1), .D(D1));
nmos_rvt  M0 ( .B(cds_globals.gnd_), .S(S), .G(G2), .D(D2));

endmodule

module cascode_current_mirror_ota ( Voutn, Voutp, Vbiasn, Vbiasp1,
     Vbiasp2, Vinn, Vinp );

output  Voutn, Voutp;

input  Vbiasn, Vbiasp1, Vbiasp2, Vinn, Vinp;


specify 
    specparam CDS_LIBNAME  = "pcell";
    specparam CDS_CELLNAME = "cascode_current_mirror_ota";
    specparam CDS_VIEWNAME = "schematic";
endspecify

SCM_NMOS_X50 L1_MM4_MM3 ( net1, net6, cds_globals.gnd_ );
CMC_NMOS_X40 L1_MM10_MM2 ( Voutn, Voutp, Vbiasn, net10, net11 );
CMC_PMOS_X40 L1_MM7_MM6 ( Voutn, Voutp, Vbiasp1, net13, net12 )
CMC_PMOS_X70 L1_MM8_MM9 ( net13, net12, Vbiasp2, cds_globals.vdd_ );
DP_NMOS_X50 L1_MM1_MM0 ( net10, net11, Vinp, Vinn, net6 )
idc  I3 ( .PLUS(cds_globals.vdd_), .MINUS(net1));

endmodule
// Library - pcell, Cell - switched_capacitor_filter, View -
//schematic
// LAST TIME SAVED: Aug 30 07:08:50 2018
// NETLIST TIME: Nov 13 07:44:10 2018
`timescale 1ns / 1ns 

module matching_cap_X1 ( CN1, CN2, CP1, CP2 );

output  CP1, CP2;
input IN1, IN2;

cap  C0 ( .MINUS(CN1), .PLUS(CP1));
cap  C2 ( .MINUS(CN2), .PLUS(CP2));

endmodule


module switched_capacitor_filter (  );


specify 
    specparam CDS_LIBNAME  = "pcell";
    specparam CDS_CELLNAME = "switched_capacitor_filter";
    specparam CDS_VIEWNAME = "schematic";
endspecify

vdc  V5 ( .PLUS(cds_globals.vdd_), .MINUS(cds_globals.gnd_));
vdc  V4 ( .PLUS(Vinp), .MINUS(cds_globals.gnd_));
vdc  V3 ( .PLUS(Vinn), .MINUS(cds_globals.gnd_));
vdc  V2 ( .PLUS(Vbiasp2), .MINUS(cds_globals.gnd_));
vdc  V1 ( .PLUS(Vbiasp1), .MINUS(cds_globals.gnd_));
vdc  V0 ( .PLUS(Vbiasn), .MINUS(cds_globals.gnd_));
cascode_current_mirror_ota I0 ( Voutn, Voutp, Vbiasn, Vbiasp1, Vbiasp2,
     net23, net7);
matching_cap_X1 L1_CC0_CC2 ( Voutp, Voutn, net23, net7);
matching_cap_X1 L1_CC5_CC7 ( Vinp, Vinn, net23, net7);
matching_cap_X1 L1_CC1_CC3 ( net11, net12, net5, net6);
matching_cap_X1 L1_CC4_CC6 ( net3, net4, net6, net5);
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
vpulse  V7 ( .PLUS(phi2), .MINUS(cds_globals.gnd_));
vpulse  V6 ( .PLUS(phi1), .MINUS(cds_globals.gnd_));

endmodule


// End HDL models
// Global nets module 

`celldefine
module cds_globals;


supply0 gnd_;

supply1 vdd_;


endmodule
`endcelldefine
