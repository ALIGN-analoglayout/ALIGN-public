
.subckt SCM_NMOS_n12_X1_Y1 B DA S DB
xM0 DA DA S B DCL_NMOS_n12_X1_Y1
xM1 DB DA S B Switch_NMOS_n12_X1_Y1
.ends SCM_NMOS_n12_X1_Y1

.subckt DCL_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends DCL_NMOS_n12_X1_Y1

.subckt Switch_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Switch_NMOS_n12_X1_Y1

.subckt CMB_NMOS_2 B DA S DB DC
xM2 DC DA S B Switch_NMOS_n12_X1_Y1
xM0_M1 DA S DB B SCM_NMOS_n12_X1_Y1
.ends CMB_NMOS_2

.subckt SCM_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends SCM_NMOS_n12_X1_Y1

.subckt CMB_NMOS_3 B DA S DB DC DD
xM3 DD DA S B Switch_NMOS_n12_X1_Y1
M0_M2_M1 DA S DC DB B CMB_NMOS_2
.ends CMB_NMOS_3

.subckt CMB_NMOS_4 B DA S DB DC DD DE
xM4 DE DA S B Switch_NMOS_n12_X1_Y1
M0_M3_M2_M1 DA S DD DC DB B CMB_NMOS_3
.ends CMB_NMOS_4

.subckt CASCODED_SCM_PMOS B DA GA S DC
xM0 DA GA DB B Switch_PMOS_n12_X1_Y1
xM1 DB DA S B Switch_PMOS_n12_X1_Y1
xM2 DC DA S B Switch_PMOS_n12_X1_Y1
.ends CASCODED_SCM_PMOS

.subckt Switch_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Switch_PMOS_n12_X1_Y1

.subckt CASCODED_CMC_PMOS B DA GA DB S
xM0 DA GA SA B Switch_PMOS_n12_X1_Y1
M1_M3_M2 DB GA S SA B CASCODED_SCM_PMOS
.ends CASCODED_CMC_PMOS

.subckt SCM_PMOS_n12_X1_Y1 B DA S DB
xM0 DA S S B DCL_PMOS_n12_X1_Y1
xM1 DB DA S B Switch_PMOS_n12_X1_Y1
.ends SCM_PMOS_n12_X1_Y1

.subckt DCL_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends DCL_PMOS_n12_X1_Y1

.subckt CMB_PMOS_2 B DA S DB DC
xM2 DC DA S B Switch_PMOS_n12_X1_Y1
xM0_M1 DA S DB B SCM_PMOS_n12_X1_Y1
.ends CMB_PMOS_2

.subckt SCM_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends SCM_PMOS_n12_X1_Y1

.subckt CMB_PMOS_3 B DA S DB DC DD
xM3 DD DA S B Switch_PMOS_n12_X1_Y1
M0_M2_M1 DA S DC DB B CMB_PMOS_2
.ends CMB_PMOS_3

.subckt LS_NMOS_n12_X1_Y1 B DA SA DB SB
xM0 DA DA SA B DCL_NMOS_n12_X1_Y1
xM1 DB DA SB B Switch_NMOS_n12_X1_Y1
.ends LS_NMOS_n12_X1_Y1

.subckt LSB_NMOS_2 B DA SA DB SB DC SC
xM2 DC DA SC B Switch_NMOS_n12_X1_Y1
xM0_M1 DA SA DB SB B LS_NMOS_n12_X1_Y1
.ends LSB_NMOS_2

.subckt LS_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends LS_NMOS_n12_X1_Y1

.subckt DP_PMOS_n12_X1_Y1 B DA GA S DB GB
xM0 DA GA S B Switch_PMOS_n12_X1_Y1
xM1 DB GB S B Switch_PMOS_n12_X1_Y1
.ends DP_PMOS_n12_X1_Y1

.subckt BUFFER_VCM_FINAL1 gnd vout ibias vdd vcm_in
xxm10 vout net065 vout Dcap_PMOS_n12_X1_Y1
xxm1 vout net138 vdd vdd Switch_PMOS_n12_X1_Y1
xxm7 net122 vdd vdd vdd DCL_PMOS_n12_X1_Y1
xm31_xm0_xm25_xm6_xm24 net132 gnd vout net125 net122 net065 gnd CMB_NMOS_4
xm4_xm5_xm32_xm33 net138 net122 net128 vdd vdd CASCODED_CMC_PMOS
xm29_xm30_xm3_xm17 ibias vdd net132 net123 net028 vdd CMB_PMOS_3
xm2_xm27_xm26 net123 gnd net128 net125 net138 net065 gnd LSB_NMOS_2
xxm21_xm19 net125 vout net028 net065 vcm_in vdd DP_PMOS_n12_X1_Y1
.ends BUFFER_VCM_FINAL1

.subckt Dcap_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Dcap_PMOS_n12_X1_Y1

.subckt DP_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends DP_PMOS_n12_X1_Y1
