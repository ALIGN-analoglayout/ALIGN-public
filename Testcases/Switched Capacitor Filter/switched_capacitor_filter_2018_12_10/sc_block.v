// Verilog HDL and netlist files of
// "pcell switched_capacitor_filter schematic"

// Netlisted models

// Library - pcell, Cell - cascode_current_mirror_ota, View - schematic
// LAST TIME SAVED: Aug 30 07:09:12 2018
// NETLIST TIME: Nov 13 07:44:10 2018
`timescale 1ns / 1ns 


module telescopic_ota ( Voutn, Voutp, Vinn, Vinp, Id, Vg );

output  Voutn, Voutp;

input  Vinn, Vinp, Id, Vg;


specify 
    specparam CDS_LIBNAME  = "pcell";
    specparam CDS_CELLNAME = "telescopic_ota";
    specparam CDS_VIEWNAME = "schematic";
endspecify

SCM_CMFB_NMOS_50_1x12 L1_MM4_MM3 ( .D1(Id), .G2(Vg), .D2(net6), .S(cds_globals.gnd_) );
CMC_NMOS_25_1x10 L1_MM10_MM2 ( .D1(Voutn), .D2(Voutp), .G(Vbiasn), .S1(net10), .S2(net11) );
CMC_PMOS_15_1x6 L1_MM7_MM6 ( .D1(Voutn), .D2(Voutp), .G(Vbiasp1), .S1(net13), .S2(net12) );
CMC_PMOS_10_1x4 L1_MM8_MM9 ( .D1(net13), .D2(net12), .G(Vbiasp2), .S(cds_globals.vdd_) );
DP_NMOS_75_3x10 L1_MM1_MM0 ( .D1(net10), .D2(net11), .G1(Vinp), .G2(Vinn), .S(net6) );
//idc  I3 ( .PLUS(cds_globals.vdd_), .MINUS(net1)); 
//bias transistors
DiodeConnected_NMOS_5_1x1 L0_MM17 ( .D(Vbiasn), .S(net6) );

DiodeConnected_PMOS_10_1x2 L0_MM11 ( .D(Vbiasp1), .S(cds_globals.vdd_) );

//DiodeConnected_PMOS_20_1x4 L0_MM13 ( .D(net_vbiasp), .S(net1_vbiasp) );
DiodeConnected_PMOS_10_1x2 L0_MM131 ( .D(Vbiasp), .S(net1_vbiasp) );
DiodeConnected_PMOS_10_1x2 L0_MM132 ( .D(Vbiasp), .S(net1_vbiasp) );
DiodeConnected_PMOS_20_1x4 L0_MM14 ( .D(net1_vbiasp), .S(cds_globals.vdd_);

Switch_NMOS_10_1x1 L0_MM12 ( .D(Vbiasp1), .G(Id), .S(cds_globals.gnd_) );
Switch_NMOS_10_1x1 L0_MM15 ( .D(Vbiasp), .G(Id), .S(cds_globals.gnd_) );
Switch_PMOS_10_1x1 L0_MM16 ( .D(Vbiasn), .G(net_vbiasp), .S(cds_globals.vdd_);

//dummy transistors
DiodeConnected_NMOS_5_1x1 L0_MM18 ( .D(cds_globals.gnd_), .S(cds_globals.gnd_) );

endmodule


module non_overlapping_clock_generator ( digital_vdd, digital_vss, clk, phi1, phi2 );

output phi1, phi2;

input digital_vdd, digital_vss, clk;

specify 
    specparam CDS_LIBNAME  = "pcell";
    specparam CDS_CELLNAME = "non_overlapping_clock_generator";
    specparam CDS_VIEWNAME = "schematic";
endspecify

Inv_3_1x1 L1_INV1 (.VDD(digital_vdd), .VSS(digital_vss), .IN(clk), .OUT(net5) );
Inv_3_1x1 L1_INV2 (.VDD(digital_vdd), .VSS(digital_vss), .IN(net2), .OUT(net3) );
Inv_3_1x1 L1_INV3 (.VDD(digital_vdd), .VSS(digital_vss), .IN(net3), .OUT(net4) );
Inv_3_1x1 L1_INV5 (.VDD(digital_vdd), .VSS(digital_vss), .IN(net6), .OUT(net7) );
Inv_3_1x1 L1_INV6 (.VDD(digital_vdd), .VSS(digital_vss), .IN(net7), .OUT(net8) );
Inv_21_1x7 L1_INV4 (.VDD(digital_vdd), .VSS(digital_vss), .IN(net4), .OUT(phi1) );
Inv_21_1x7 L1_INV7 (.VDD(digital_vdd), .VSS(digital_vss), .IN(net8), .OUT(phi2) );
NAND_1_1x1 L1_NAND1 (.VDD(digital_vdd), .VSS(digital_vss), .IN_A(net1), .IN_B(net8), .OUT(net2) );
NAND_1_1x1 L1_NAND2 (.VDD(digital_vdd), .VSS(digital_vss), .IN_A(net5), .IN_B(net4), .OUT(net6) );
TG_3_1x1 L1_TG1 (.VDD(digital_vdd), .VSS(digital_vss), .IN(clk), .OUT(net1) );

endmodule


module common_mode_feedback ( Vg, Va, Vb, phi1, phi2, Vbias_in, Vcm_in );

output Vg;

input Va, Vb, phi1, phi2, Vbias_in, Vcm_in;

specify 
    specparam CDS_LIBNAME  = "pcell";
    specparam CDS_CELLNAME = "common_mode_feedback";
    specparam CDS_VIEWNAME = "schematic";
endspecify

Switch_NMOS_10_1x1  L0_MM0 ( .S(Va), .G(phi1), .D(net1));
Switch_NMOS_10_1x1  L0_MM1 ( .S(Vcm_in), .G(phi2), .D(net1));
Switch_NMOS_10_1x1  L0_MM2 ( .S(net2), .G(phi1), .D(Vb));
Switch_NMOS_10_1x1  L0_MM3 ( .S(net2), .G(phi2), .D(Vcm_in));
Switch_NMOS_10_1x1  L0_MM4 ( .S(Vg), .G(phi2), .D(Vbias_in));
Cap_30f_1x3 CC10 ( .PLUS(net1), .MINUS(Vg));
Cap_30f_1x3 CC11 ( .PLUS(Vg), .MINUS(net2));

endmodule

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
Cap_60f_2x3 CC4 ( .PLUS(net6), .MINUS(net3));
Switch_NMOS_10_1x1  L0_MM9 ( .S(net6), .G(phi2), .D(agnd));
Cap_30f_1x3 CC3 ( .PLUS(net6), .MINUS(net12));
Switch_NMOS_10_1x1  L0_MM11 ( .S(net12), .G(phi1), .D(agnd));
Switch_NMOS_10_1x1  L0_MM8 ( .S(Vout), .G(phi2), .D(net12));
Switch_NMOS_10_1x1  L0_MM1 ( .S(Vin_ota), .G(phi1), .D(net6));
Cap_60f_2x3 CC0 ( .PLUS(Vin_ota), .MINUS(Vout));

endmodule

module switched_capacitor_filter ( Voutn, Voutp, Vinp, Vinn, Id, agnd, clk );


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
telescopic_ota I0 ( .Voutn(Voutn), .Voutp(Voutp), .Vinn(Vinn), .Vinp(Vinp), .Id(Id), .Vg(Vg));
switched_capacitor_combination I1 ( .Vout(Voutp), .Vin_ota(Vinn_ota), .Vin(Vinp), .phi2(phi2), .phi1(phi1), .agnd(agnd));
switched_capacitor_combination I2 ( .Vout(Voutn), .Vin_ota(Vinp_ota), .Vin(Vinn), .phi2(phi2), .phi1(phi1), .agnd(agnd));
common_mode_feedback I3 ( .Vg(Vg), .Va(Voutp), .Vb(Voutn), .phi1(phi1), .phi2(phi2), .Vbias_in(Id), .Vcm_in(agnd));
non_overlapping_clock_generator I4 ( .digital_vdd(cds_globals.vdd_), .digital_vss(cds_globals.gnd_), .clk(clk), .phi1(phi1), .phi2(phi2));
Cap_30f_1x3 CC5 ( .PLUS(Vinn_ota), .MINUS(Vinn));
Cap_30f_1x3 CC7 ( .PLUS(Vinp_ota), .MINUS(Vinp));
Cap_60f_2x3 CC8 ( .PLUS(Voutp), .MINUS(cds_globals.gnd_));
Cap_60f_2x3 CC9 ( .PLUS(Voutn), .MINUS(cds_globals.gnd_));



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
