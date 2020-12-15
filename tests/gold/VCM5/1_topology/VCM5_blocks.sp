
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

.subckt VCM5 gnd vout ibias vdd vcm
xm20_xm21_xm19_xm18 vout net022 net80 net84 vcm net77 vdd DP_PAIR_PMOS
xm29_xm30_xm17 ibias vdd net039 net022 vdd CMB_PMOS_2
xxm22_xm25 net80 gnd net91 gnd SCM_NMOS_n12_X1_Y1
xxm23_xm24 net84 gnd net92 gnd SCM_NMOS_n12_X1_Y1
xxm33_xm32 net77 vdd vout vdd SCM_PMOS_n12_X1_Y1
xm31_xm26_xm27 net039 gnd vout net92 net77 net91 gnd LSB_NMOS_2
.ends VCM5

.subckt SCM_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends SCM_NMOS_n12_X1_Y1
