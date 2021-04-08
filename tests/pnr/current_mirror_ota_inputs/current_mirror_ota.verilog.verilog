module current_mirror_ota ( id, vbiasnd, vinn, vinp, voutp );
input id, vbiasnd, vinn, vinp, voutp;

DCL_PMOS_nfin60_n12_X5_Y1_RVT m21 ( .D(net16), .S(vdd) );
Switch_PMOS_nfin240_n12_X5_Y4_ST2_RVT m20s ( .D(vbiasnd), .G(net16), .S(vdd) );
DCL_PMOS_nfin60_n12_X5_Y1_RVT m19 ( .D(net27), .S(vdd) );
Switch_PMOS_nfin240_n12_X5_Y4_ST2_RVT m18s ( .D(voutp), .G(net27), .S(vdd) );
SCM_NMOS_nfin10_n12_X1_Y1_RVT m14_m16 ( .DA(id), .DB(net24), .S(vss) );
SCM_NMOS_nfin24_n12_X2_Y1_RVT m11_m10 ( .DA(vbiasnd), .DB(voutp), .S(vss) );
DP_NMOS_B_nfin28_n12_X3_Y1_RVT m17_m15 ( .B(vss), .DA(net16), .DB(net27), .GA(vinn), .GB(vinp), .S(net24) );

endmodule

`celldefine
module global_power;
supply0 vss;
supply1 vdd;
endmodule
`endcelldefine
