//Verilog block level netlist file for high_speed_comparator
//Generated by UMN for ALIGN project 


module high_speed_comparator ( clk, vin, vip, von, vop ); 
input clk, vin, vip, von, vop;

Switch_PMOS_nfin12_m1_n12_X1_Y1 mmp5 ( .D(vip_d), .G(clk), .S(vcc) ); 
Switch_PMOS_nfin12_m1_n12_X1_Y1 mmp4 ( .D(vip_o), .G(clk), .S(vcc) ); 
Switch_PMOS_nfin12_m1_n12_X1_Y1 mmp3 ( .D(vin_d), .G(clk), .S(vcc) ); 
Switch_PMOS_nfin12_m1_n12_X1_Y1 mmp2 ( .D(vin_o), .G(clk), .S(vcc) ); 
Switch_NMOS_nfin12_m8_n12_X4_Y2 mmn2 ( .D(vcom), .G(clk), .S(vss) ); 
CCP_S_NMOS_B_nfin12_m8_n12_X8_Y1 mmn4_mmn3 ( .B(vss), .DA(vin_o), .DB(vip_o), .SA(vin_d), .SB(vip_d) ); 
CCP_PMOS_nfin12_m4_n12_X2_Y2 mmp1_mmp0 ( .DA(vin_o), .DB(vip_o), .S(vcc) ); 
INV mmn5_mmp6 ( .i(vin_o), .zn(von) ); 
INV mmn6_mmp7 ( .i(vip_o), .zn(vop) ); 
DP_NMOS_B_nfin12_m16_n12_X8_Y2 mmn1_mmn0 ( .B(vss), .DA(vip_d), .DB(vin_d), .GA(vip), .GB(vin), .S(vcom) ); 

endmodule

module INV ( i, zn ); 
input i, zn;

Switch_NMOS_nfin12_m1_n12_X1_Y1 M0 ( .D(zn), .G(i), .S(vss) ); 
Switch_PMOS_nfin12_m1_n12_X1_Y1 M1 ( .D(zn), .G(i), .S(vcc) ); 

endmodule

`celldefine
module global_power;
supply0 vss;
supply1 vcc;
endmodule
`endcelldefine
