//Verilog block level netlist file for strong_arm_latch_1
//Generated by UMN for ALIGN project 


module strong_arm_latch_1 ( von, vin, vss, vip, clk, vcc, vop ); 
input von, vin, vss, vip, clk, vcc, vop;

Switch_NMOS_n12_X3_Y2 mn0 ( .D(net44), .G(net16), .S(net42), .Bg(vss) ); 
Switch_NMOS_n12_X3_Y2 mn1 ( .D(net16), .G(net44), .S(net8), .Bg(vss) ); 
Switch_NMOS_n12_X5_Y4 mn2 ( .D(net8), .G(vip), .S(net34), .Bg(vss) ); 
Switch_NMOS_n12_X5_Y4 mn3 ( .D(net42), .G(vin), .S(net34), .Bg(vss) ); 
Switch_NMOS_n12_X17_Y1 mn4 ( .D(net34), .G(clk), .S(vss), .Bg(vss) ); 
Switch_NMOS_n12_X1_Y1 mn5 ( .D(von), .G(net16), .S(vss), .Bg(vss) ); 
Switch_NMOS_n12_X1_Y1 mn6 ( .D(vop), .G(net44), .S(vss), .Bg(vss) ); 
Switch_PMOS_n12_X1_Y1 mp0 ( .D(net44), .G(net16), .S(vcc), .Bg(vcc) ); 
Switch_PMOS_n12_X3_Y2 mp1 ( .D(net16), .G(clk), .S(vcc), .Bg(vcc) ); 
Switch_PMOS_n12_X1_Y1 mp2 ( .D(net16), .G(net44), .S(vcc), .Bg(vcc) ); 
Switch_PMOS_n12_X3_Y2 mp3 ( .D(net44), .G(clk), .S(vcc), .Bg(vcc) ); 
Switch_PMOS_n12_X1_Y1 mp4 ( .D(net8), .G(clk), .S(vcc), .Bg(vcc) ); 
Switch_PMOS_n12_X1_Y1 mp5 ( .D(net42), .G(clk), .S(vcc), .Bg(vcc) ); 
Switch_PMOS_n12_X1_Y1 mp6 ( .D(von), .G(net16), .S(vcc), .Bg(vcc) ); 
Switch_PMOS_n12_X1_Y1 mp7 ( .D(vop), .G(net44), .S(vcc), .Bg(vcc) ); 

endmodule
