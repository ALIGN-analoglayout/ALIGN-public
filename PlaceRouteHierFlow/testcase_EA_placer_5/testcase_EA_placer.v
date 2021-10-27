module testcase_EA_placer ( 0, 1 ); 
input 0, 1;

CMC_PMOS_S_n12_X1_Y1_Pin_2 m1 ( .G1(0), .G2(3) );
CMC_PMOS_S_n12_X1_Y1_Pin_2 m2 ( .G1(2), .G2(5) );
CMC_PMOS_S_n12_X1_Y1_Pin_4 m3 ( .G1(2), .G2(3), .G3(4), .G4(6) );
CMC_PMOS_S_n12_X1_Y1_Pin_2 m4 ( .G1(4), .G2(7) );
CMC_PMOS_S_n12_X1_Y1_Pin_3 m5 ( .G1(5), .G2(8), .G3(10) );
CMC_PMOS_S_n12_X1_Y1_Pin_4 m6 ( .G1(6), .G2(8), .G3(11), .G4(9) );
CMC_PMOS_S_n12_X1_Y1_Pin_3 m7 ( .G1(7), .G2(9), .G3(12) );
CMC_PMOS_S_n12_X1_Y1_Pin_2 m8 ( .G1(10), .G2(13) );
CMC_PMOS_S_n12_X1_Y1_Pin_4 m9 ( .G1(11), .G2(13), .G3(15), .G4(14) );
CMC_PMOS_S_n12_X1_Y1_Pin_2 m10 ( .G1(12), .G2(14) );
CMC_PMOS_S_n12_X1_Y1_Pin_2 m11 ( .G1(15), .G2(1) );

endmodule

