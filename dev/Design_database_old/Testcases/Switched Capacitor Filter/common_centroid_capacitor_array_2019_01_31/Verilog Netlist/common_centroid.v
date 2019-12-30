// Verilog HDL and netlist files of
// "pcell switched_capacitor_filter schematic"

// Netlisted models

// Library - pcell, Cell - cascode_current_mirror_ota, View - schematic
// LAST TIME SAVED: Aug 30 07:09:12 2018
// NETLIST TIME: Nov 13 07:44:10 2018
`timescale 1ns / 1ns 
// Library - pcell, Cell - switched_capacitor_filter, View -
//schematic
// LAST TIME SAVED: Aug 30 07:08:50 2018
// NETLIST TIME: Nov 13 07:44:10 2018
`timescale 1ns / 1ns 

module switched_capacitor_combination ( Vout, Vin_ota, Vin, phi2, phi1, agnd );

output Vout, Vin_ota;

input Vin, phi2, phi1, agnd;

specify 
    specparam CDS_LIBNAME  = "pcell";
    specparam CDS_CELLNAME = "switched_capacitor_combination";
    specparam CDS_VIEWNAME = "schematic";
endspecify

Switch_NMOS_10_1x1  L0_MM0 ( .S(net3), .G(phi1), .D(Vin));
Switch_NMOS_10_1x1  L0_MM10 ( .S(net3), .G(phi2), .D(agnd));
Cap_60f CC4 ( .PLUS(net6), .MINUS(net3));
Switch_NMOS_10_1x1  L0_MM9 ( .S(net6), .G(phi2), .D(agnd));
Cap_30f CC3 ( .PLUS(net6), .MINUS(net12));
Switch_NMOS_10_1x1  L0_MM11 ( .S(net12), .G(phi1), .D(agnd));
Switch_NMOS_10_1x1  L0_MM8 ( .S(Vout), .G(phi2), .D(net12));
Switch_NMOS_10_1x1  L0_MM1 ( .S(Vin_ota), .G(phi1), .D(net6));
Cap_60f CC0 ( .PLUS(Vin_ota), .MINUS(Vout));

endmodule

module common_centroid ( Voutn, Voutp, Vinp, Vinn, Id, agnd, clk );


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
//cascode_current_mirror_ota I0 ( .Voutn(Voutn), .Voutp(Voutp), .Vbiasn(Vbiasn), .Vbiasp1(Vbiasp1), .Vbiasp2(Vbiasp2), .Vinn(Vinn_ota), .Vinp(Vinp_ota));
//telescopic_ota I0 ( .Voutn(Voutn), .Voutp(Voutp), .Vinn(Vinn), .Vinp(Vinp), .Id(Id), .Vg(Vg));
switched_capacitor_combination I1 ( .Vout(Voutp), .Vin_ota(Vinn_ota), .Vin(Vinp), .phi2(phi2), .phi1(phi1), .agnd(agnd));
switched_capacitor_combination I2 ( .Vout(Voutn), .Vin_ota(Vinp_ota), .Vin(Vinn), .phi2(phi2), .phi1(phi1), .agnd(agnd));
//common_mode_feedback I3 ( .Vg(Vg), .Va(Voutp), .Vb(Voutn), .phi1(phi1), .phi2(phi2), .Vbias_in(Id), .Vcm_in(agnd));
//non_overlapping_clock_generator I4 ( .digital_vdd(cds_globals.vdd_), .digital_vss(cds_globals.gnd_), .clk(clk), .phi1(phi1), .phi2(phi2));
//Cap_30f_1x3 CC5 ( .PLUS(Vinn_ota), .MINUS(Vinn));
//Cap_30f_1x3 CC7 ( .PLUS(Vinp_ota), .MINUS(Vinp));
//Cap_60f_2x3 CC8 ( .PLUS(Voutp), .MINUS(cds_globals.gnd_));
//Cap_60f_2x3 CC9 ( .PLUS(Voutn), .MINUS(cds_globals.gnd_));



//Cap_60f_2x3 CC7 ( .PLUS(net7), .MINUS(Vinp));
//Cap_60f_2x3 CC6 ( .PLUS(net5), .MINUS(net4));
//Cap_60f_2x3 CC5 ( .PLUS(net23), .MINUS(Vinn));
//Cap_60f_2x3 CC4 ( .PLUS(net6), .MINUS(net3));
//Cap_32f_1x1 CC3 ( .PLUS(net6), .MINUS(net12));
//Cap_32f_1x1 CC2 ( .PLUS(net7), .MINUS(Voutn));
//Cap_32f_1x1 CC1 ( .PLUS(net5), .MINUS(net11));
//Cap_32f_1x1 CC0 ( .PLUS(net23), .MINUS(Voutp));
//Switch_NMOS_10_1x1  L0_MM11 ( .S(net12), .G(phi1), .D(cds_globals.gnd_));
//Switch_NMOS_10_1x1  L0_MM10 ( .S(net3), .G(phi2), .D(cds_globals.gnd_));
//Switch_NMOS_10_1x1  L0_MM9 ( .S(net6), .G(phi2), .D(cds_globals.gnd_));
//Switch_NMOS_10_1x1  L0_MM8 ( .S(Voutp), .G(phi2), .D(net12));
//Switch_NMOS_10_1x1  L0_MM7 ( .S(net11), .G(phi2), .D(Voutn));
//Switch_NMOS_10_1x1  L0_MM6 ( .S(cds_globals.gnd_), .G(phi1), .D(net11));
//Switch_NMOS_10_1x1  L0_MM5 ( .S(cds_globals.gnd_), .G(phi2), .D(net5));
//Switch_NMOS_10_1x1  L0_MM4 ( .S(cds_globals.gnd_), .G(phi2), .D(net4));
//Switch_NMOS_10_1x1  L0_MM3 ( .S(net5), .G(phi1), .D(net7));
//Switch_NMOS_10_1x1  L0_MM2 ( .S(Vinn), .G(phi1), .D(net4));
//Switch_NMOS_10_1x1  L0_MM1 ( .S(net23), .G(phi1), .D(net6));
//Switch_NMOS_10_1x1  L0_MM0 ( .S(net3), .G(phi1), .D(Vinp));
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
