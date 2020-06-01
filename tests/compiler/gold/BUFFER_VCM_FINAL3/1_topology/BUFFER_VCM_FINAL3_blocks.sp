
.subckt SCM_PMOS_n12_X1_Y1 B DA S DB
xM0 DA S S B DCL_PMOS_n12_X1_Y1
xM1 DB DA S B Switch_PMOS_n12_X1_Y1
.ends SCM_PMOS_n12_X1_Y1

.subckt DCL_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends DCL_PMOS_n12_X1_Y1

.subckt Switch_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Switch_PMOS_n12_X1_Y1

.subckt CMC_PMOS_S_n12_X1_Y1 B DA G S DB
xM0 DA G S B Switch_PMOS_n12_X1_Y1
xM1 DB G S B Switch_PMOS_n12_X1_Y1
.ends CMC_PMOS_S_n12_X1_Y1

.subckt DP_PAIR_PMOS B DC S DA DB GB DD
xM0_M1 DC S DA B SCM_PMOS_n12_X1_Y1
xM3_M2 DD GB S DB B CMC_PMOS_S_n12_X1_Y1
.ends DP_PAIR_PMOS

.subckt SCM_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends SCM_PMOS_n12_X1_Y1

.subckt CMC_PMOS_S_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends CMC_PMOS_S_n12_X1_Y1

.subckt CMB_PMOS_2 B DA S DB DC
xM2 DC DA S B Switch_PMOS_n12_X1_Y1
xM0_M1 DA S DB B SCM_PMOS_n12_X1_Y1
.ends CMB_PMOS_2

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

.subckt BUFFER_VCM_FINAL3 gnd vout ibias vdd vcm_in
xxm3 net050 gnd Dummy1_NMOS_n12_X1_Y1
xxm11 net044 gnd Dummy1_NMOS_n12_X1_Y1
xxm4 net053 gnd Dummy1_NMOS_n12_X1_Y1
xxm5 gnd gnd Dummy1_NMOS_n12_X1_Y1
xxm7 vout gnd Dummy1_NMOS_n12_X1_Y1
xxm9 net061 gnd Dummy1_NMOS_n12_X1_Y1
xxm8 net047 gnd Dummy1_NMOS_n12_X1_Y1
xxm12 gnd gnd Dummy1_NMOS_n12_X1_Y1
xxm10 net060 gnd Dummy1_NMOS_n12_X1_Y1
xxm1 net052 vdd Dummy1_PMOS_n12_X1_Y1
xxm0 vdd vdd Dummy1_PMOS_n12_X1_Y1
xxm13 vdd vdd Dummy1_PMOS_n12_X1_Y1
xm20_xm21_xm19_xm18 vout net052 net050 net053 vcm_in net047 vdd DP_PAIR_PMOS
xm29_xm17_xm30 ibias vdd net052 net044 vdd CMB_PMOS_2
xxm22_xm25 net050 gnd net061 gnd SCM_NMOS_n12_X1_Y1
xxm23_xm24 net053 gnd net060 gnd SCM_NMOS_n12_X1_Y1
xxm33_xm32 net047 vdd vout vdd SCM_PMOS_n12_X1_Y1
xm31_xm26_xm27 net044 gnd vout net060 net047 net061 gnd LSB_NMOS_2
.ends BUFFER_VCM_FINAL3

.subckt Dummy1_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Dummy1_NMOS_n12_X1_Y1

.subckt Dummy1_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08 m=2
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08 m=2
.ends Dummy1_PMOS_n12_X1_Y1

.subckt SCM_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends SCM_NMOS_n12_X1_Y1
