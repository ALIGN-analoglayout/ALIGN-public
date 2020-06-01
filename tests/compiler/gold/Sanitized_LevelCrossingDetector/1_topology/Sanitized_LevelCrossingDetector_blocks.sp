
.subckt Sanitized_LevelCrossingDetector QPHASE SQ VDD QD VSS VCP SS VCPS
XI2 QPHASE SQ VDD QD VSS CrossingDetector_Mux
XI0 VCP SS VDD VCPS VSS CrossingDetector_Mux
.ends Sanitized_LevelCrossingDetector

.subckt CrossingDetector_Mux IN SS VDD VO VSS
XI18 net012 net032 SS VDD VSS VO MUX2D2LVT
XI16 net033 VDD VSS net012 CKBD1LVT
XI10 net012 VDD VSS net032 CKBD1LVT
XI9 net015 VDD VSS net033 CKBD1LVT
xMM2 net06 IN VDD VDD Switch_PMOS_n12_X1_Y1
xMM1 net06 IN VSS VSS Switch_NMOS_n12_X1_Y1
XI15 net06 VDD VSS net015 CKND1LVT
.ends CrossingDetector_Mux

.subckt Switch_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  l=1e-08 w=1e-08 m=2
m1 S1 G S B nmos_rvt  l=1e-08 w=1e-08 m=2
.ends Switch_PMOS_n12_X1_Y1

.subckt Switch_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  l=1e-08 w=1e-08 m=2
m1 S1 G S B nmos_rvt  l=1e-08 w=1e-08 m=2
.ends Switch_NMOS_n12_X1_Y1

.subckt tgate D GA S GB
xM0 D GA S BN Switch_NMOS_n12_X1_Y1
xM1 D GB S BP Switch_PMOS_n12_X1_Y1
.ends tgate

.subckt MUX2D2LVT I0 I1 S VDD VSS Z
xMMI16_M_u2 net25 I0 VSS VSS Switch_NMOS_n12_X1_Y1
xMMI17_M_u2 net17 S VSS VSS Switch_NMOS_n12_X1_Y1
xMMI14_M_u2 net9 I1 VSS VSS Switch_NMOS_n12_X1_Y1
xMMU29_0_M_u2 Z net7 VSS VSS Switch_NMOS_n12_X1_Y1
xMMI17_M_u3 net17 S VDD VDD Switch_PMOS_n12_X1_Y1
xMMI14_M_u3 net9 I1 VDD VDD Switch_PMOS_n12_X1_Y1
xMMU29_1_M_u3 Z net7 VDD VDD Switch_PMOS_n12_X1_Y1
xMMI16_M_u3 net25 I0 VDD VDD Switch_PMOS_n12_X1_Y1
MMI13_M_u3_MMI13_M_u2 S net7 net17 net9 tgate
MMU18_M_u3_MMU18_M_u2 net17 net7 S net25 tgate
.ends MUX2D2LVT

.subckt INV_LVT zn i SN SP
xxm0 zn i SN SN Switch_NMOS_n12_X1_Y1
xxm1 zn i SP SP Switch_PMOS_n12_X1_Y1
.ends INV_LVT

.subckt stage2_inv G1 SN G2 SP
MM0_MM2 D SN SP G1 INV_LVT
MM1_MM3 G2 SN SP D INV_LVT
.ends stage2_inv

.subckt CKBD1LVT I VDD VSS Z
MMU23_MM_u15_MMU21_MM_u3 VSS I VDD Z stage2_inv
.ends CKBD1LVT

.subckt CKND1LVT I VDD VSS ZN
xMM_u2 ZN I VSS VSS Switch_NMOS_n12_X1_Y1
xMM_u1 ZN I VDD VDD Switch_PMOS_n12_X1_Y1
.ends CKND1LVT
