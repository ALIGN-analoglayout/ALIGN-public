from satplacer.verilog_parser import *


def test_str():
    txt = """
module vga ( vps, vgnd, vin1, vin2, vmirror, s0, s1, s2, vga_out1, vga_out2 ); 
output vps, vgnd, vin1, vin2, vmirror, s0, s1, s2, vga_out1, vga_out2;

Cap_10f C1 ( .MINUS(vgnd), .PLUS(vga_out1) ); 
Cap_10f C2 ( .MINUS(vgnd), .PLUS(vga_out2) ); 
Switch_NMOS_n10_X4_Y4 Nsw0 ( .D(net5), .G(s0), .S(net5p) ); 
Switch_NMOS_n10_X4_Y4 Nsw1 ( .D(net4), .G(s1), .S(net4p) ); 
Switch_NMOS_n10_X4_Y4 Nsw2 ( .D(net6), .G(s2), .S(net6p) ); 
Res_400 R0 ( .MINUS(vga_out1), .PLUS(vps) ); 
Res_400 R1 ( .MINUS(vga_out2), .PLUS(vps) ); 
CMB_4_n10_A1_B1_C2_D4 xM03|MN0_xM02|MN0_xM32|MN0_xM12|MN0_xM22|MN0 ( .D0(vmirror), .D1(net3), .D2(net6p), .D3(net5p), .D4(net4p), .S(vgnd) ); 
DP_NMOS_n10_X5_Y4 xM20|MN0_xM21|MN0 ( .D1(vga_out1), .G1(vin1), .S(net4), .D2(vga_out2), .G2(vin2) ); 
DP_NMOS_n10_X8_Y5 xM30|MN0_xM31|MN0 ( .D1(vga_out1), .G1(vin1), .S(net6), .D2(vga_out2), .G2(vin2) ); 
DP_NMOS_n10_X5_Y2 xM10|MN0_xM11|MN0 ( .D1(vga_out1), .G1(vin1), .S(net5), .D2(vga_out2), .G2(vin2) ); 
DP_NMOS_n10_X5_Y2 xM00|MN0_xM01|MN0 ( .D1(vga_out1), .G1(vin1), .S(net3), .D2(vga_out2), .G2(vin2) ); 

endmodule

"""

#    print(list(generate_tokens(txt)))

    lp = VerilogParser()
    lp.parse( txt)

