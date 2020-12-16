
module SCM_NMOS ( B, DA, DB, S ); 
input B, DA, DB, S;

DCL_NMOS M0 ( .B(B), .D(DA), .S(S) ); 
Switch_NMOS M1 ( .B(B), .D(DB), .G(DA), .S(S) ); 

endmodule

module CMC_PMOS_S ( DA, DB, G, S ); 
input DA, DB, G, S;

Switch_PMOS M0 ( .B(vdd), .D(DA), .G(G), .S(S) ); 
Switch_PMOS M1 ( .B(vdd), .D(DB), .G(G), .S(S) ); 

endmodule

module DP_NMOS ( DA, DB, GA, GB, S ); 
input DA, DB, GA, GB, S;

Switch_NMOS M0 ( .B(B), .D(DA), .G(GA), .S(S) ); 
Switch_NMOS M1 ( .B(B), .D(DB), .G(GB), .S(S) ); 

endmodule

module CMC_PMOS ( DA, DB, G, SA, SB ); 
input DA, DB, G, SA, SB;

Switch_PMOS M0 ( .B(B), .D(DA), .G(G), .S(SA) ); 
Switch_PMOS M1 ( .B(B), .D(DB), .G(G), .S(SB) ); 

endmodule

module CMC_NMOS ( DA, DB, G, SA, SB ); 
input DA, DB, G, SA, SB;

Switch_NMOS M0 ( .B(B), .D(DA), .G(G), .S(SA) ); 
Switch_NMOS M1 ( .B(B), .D(DB), .G(G), .S(SB) ); 

endmodule

module ota ( vbiasn, vbiasp1, vinn, vinp, voutn, voutp ); 
input vbiasn, vbiasp1, vinn, vinp, voutn, voutp;

SCM_NMOS m4_m3 ( .B(vss), .DA(id), .DB(net10), .S(vss) ); 
CMC_PMOS_S m9_m8 ( .DA(net06), .DB(net012), .G(vbiasp1), .S(vdd!) ); 
DP_NMOS m1_m0 ( .DA(net8), .DB(net014), .GA(vinp), .GB(vinn), .S(net10) ); 
CMC_PMOS m7_m6 ( .DA(voutn), .DB(voutp), .G(vbiasp), .SA(net06), .SB(net012) ); 
CMC_NMOS m2_m10 ( .DA(voutp), .DB(voutn), .G(vbiasn), .SA(net014), .SB(net8) ); 

endmodule
