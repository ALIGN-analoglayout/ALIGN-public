module testcase_EA_placer ( 0, 1 ); 
input 0, 1;

CMC_PMOS_S_n12_X1_Y1_Pin_1 m1 ( .G1(2) );
CMC_PMOS_S_n12_X1_Y1_Pin_2 m2_c1 ( .G1(2), .G2(3) );
CMC_PMOS_S_n12_X1_Y1_Pin_3 m3_c1 ( .G1(0), .G2(4), .G3(4) );
CMC_PMOS_S_n12_X1_Y1_Pin_4 m4_c2 ( .G1(3), .G2(4), .G3(1), .G4(1) );

endmodule

