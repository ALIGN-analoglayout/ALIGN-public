
.subckt SW_Cres_v3_5 VRN VRNX VRP VRPX CK VRCTL DVDD DVSS
xMM3 VRN CLK DVSS Dcap_NMOS_n12_X1_Y1
xMM2 VRN net010 VRNX DVSS Switch_NMOS_n12_X1_Y1
xMM4 VRP net018 DVDD Dcap_PMOS_n12_X1_Y1
xMM1 VRP CLK VRPX DVDD Switch_PMOS_n12_X1_Y1
XI11 CK VRCTL net010 DVDD DVSS ND2D1LVT
XI5 CLK net018 DVDD DVSS INVD0LVT
XI6 net010 CLK DVDD DVSS INVD0LVT
.ends SW_Cres_v3_5

.subckt Dcap_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  l=1e-08 w=1e-08 m=1
m1 S1 G S B nmos_rvt  l=1e-08 w=1e-08 m=1
.ends Dcap_NMOS_n12_X1_Y1

.subckt Switch_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  l=1e-08 w=1e-08 m=1
m1 S1 G S B nmos_rvt  l=1e-08 w=1e-08 m=1
.ends Switch_NMOS_n12_X1_Y1

.subckt Dcap_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  l=1e-08 w=1e-08 m=1
m1 S1 G S B nmos_rvt  l=1e-08 w=1e-08 m=1
.ends Dcap_PMOS_n12_X1_Y1

.subckt Switch_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  l=1e-08 w=1e-08 m=1
m1 S1 G S B nmos_rvt  l=1e-08 w=1e-08 m=1
.ends Switch_PMOS_n12_X1_Y1

.subckt ND2D1LVT A1 A2 ZN VDD VSS
xMMI1_M_u3 ZN A1 net1 VSS Switch_NMOS_n12_X1_Y1
xMMI1_M_u4 net1 A2 VSS VSS Switch_NMOS_n12_X1_Y1
xMMI1_M_u1 ZN A1 VDD VDD Switch_PMOS_n12_X1_Y1
xMMI1_M_u2 ZN A2 VDD VDD Switch_PMOS_n12_X1_Y1
.ends ND2D1LVT

.subckt INVD0LVT I ZN VDD VSS
xMMU1_M_u2 ZN I VSS VSS Switch_NMOS_n12_X1_Y1
xMMU1_M_u3 ZN I VDD VDD Switch_PMOS_n12_X1_Y1
.ends INVD0LVT
