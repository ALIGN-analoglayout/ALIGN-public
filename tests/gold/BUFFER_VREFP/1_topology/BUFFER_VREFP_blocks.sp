
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

.subckt LS_PMOS_n12_X1_Y1 B DA SA DB SB
xM0 DA SA SA B DCL_PMOS_n12_X1_Y1
xM1 DB DA SB B Switch_PMOS_n12_X1_Y1
.ends LS_PMOS_n12_X1_Y1

.subckt LSB_PMOS_2 B DA SA DB SB DC SC
xM2 DC DA SC B Switch_PMOS_n12_X1_Y1
xM0_M1 DA SA DB SB B LS_PMOS_n12_X1_Y1
.ends LSB_PMOS_2

.subckt LS_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends LS_PMOS_n12_X1_Y1

.subckt DP_NMOS_n12_X1_Y1 B DA GA S DB GB
xM0 DA GA S B Switch_NMOS_n12_X1_Y1
xM1 DB GB S B Switch_NMOS_n12_X1_Y1
.ends DP_NMOS_n12_X1_Y1

.subckt dummy_hier_xm12_xm10 net054 net207 net036 net204 net051 net211 net215
xxm46 net054 gnd Dummy1_NMOS_n12_X1_Y1
xm22_xm14_xm13 net204 vdd net207 net054 net036 net051 vdd LSB_PMOS_2
xxm41 net054 vdd Dummy1_PMOS_n12_X1_Y1
xxm25_xm26 net211 vdd net054 vdd SCM_PMOS_n12_X1_Y1
xxm42 net051 vdd Dummy1_PMOS_n12_X1_Y1
xxm23_xm24 net215 vdd net051 vdd SCM_PMOS_n12_X1_Y1
xxm45 net051 gnd Dummy1_NMOS_n12_X1_Y1
.ends dummy_hier_xm12_xm10

.subckt Dummy1_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Dummy1_NMOS_n12_X1_Y1

.subckt Dummy1_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Dummy1_PMOS_n12_X1_Y1

.subckt SCM_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends SCM_PMOS_n12_X1_Y1

.subckt dummy_hier_xm11_xm8 net211 net207 net036 net204 net215 net054 net051
xm46_xm22_xm14_xm13_xm41_xm25_xm26_xm42_xm23_xm24_xm45 net207 net036 net204 net051 vdd net211 net215 net054 dummy_hier_xm12_xm10
xxm43 net211 gnd Dummy1_NMOS_n12_X1_Y1
xxm35 net211 vdd Dummy1_PMOS_n12_X1_Y1
xxm36 net215 vdd Dummy1_PMOS_n12_X1_Y1
xxm44 net215 gnd Dummy1_NMOS_n12_X1_Y1
.ends dummy_hier_xm11_xm8

.subckt BUFFER_VREFP vrefp vdd gnd ibias vref
xxm60 vrefp vdd Dummy1_PMOS_n12_X1_Y1
xxm37 vdd net057 vdd Dcap_PMOS_n12_X1_Y1
xxm28 vrefp net052 vdd vdd Switch_PMOS_n12_X1_Y1
xxm15 net049 net036 vdd vdd Switch_PMOS_n12_X1_Y1
xxm59 net057 vdd Dummy1_PMOS_n12_X1_Y1
xxm57 vdd vdd Dummy1_PMOS_n12_X1_Y1
xxm58 net049 vdd Dummy1_PMOS_n12_X1_Y1
xxm55 vdd vdd Dummy1_PMOS_n12_X1_Y1
xxm54 net049 vdd Dummy1_PMOS_n12_X1_Y1
xxm38 vdd net036 vdd Dcap_PMOS_n12_X1_Y1
xxm63 gnd gnd Dummy1_NMOS_n12_X1_Y1
xxm62 gnd gnd Dummy1_NMOS_n12_X1_Y1
xxm56 net057 gnd Dummy1_NMOS_n12_X1_Y1
xxm53 gnd gnd Dummy1_NMOS_n12_X1_Y1
xxm52 net036 gnd Dummy1_NMOS_n12_X1_Y1
xxm47 net212 gnd Dummy1_NMOS_n12_X1_Y1
xxm50 net207 gnd Dummy1_NMOS_n12_X1_Y1
xxm40 net204 gnd Dummy1_NMOS_n12_X1_Y1
xxm39 ibias gnd Dummy1_NMOS_n12_X1_Y1
xxm33 vdd vdd Dummy1_PMOS_n12_X1_Y1
xxm32 vdd vdd Dummy1_PMOS_n12_X1_Y1
xxm31 net204 vdd Dummy1_PMOS_n12_X1_Y1
xm4_xm3_xm5_xm21_xm30 ibias gnd net212 net204 net057 net052 gnd CMB_NMOS_4
xxm1_xm6 net207 gnd net036 gnd SCM_NMOS_n12_X1_Y1
xxm27_xm29 net057 net049 net052 vrefp vdd LS_PMOS_n12_X1_Y1
xxm12_xm10 net051 vref net212 net054 net049 gnd DP_NMOS_n12_X1_Y1
xxm11_xm8 net211 vref net212 net215 net049 gnd DP_NMOS_n12_X1_Y1
xm46_xm22_xm14_xm13_xm41_xm25_xm26_xm42_xm23_xm24_xm45_xm43_xm35_xm36_xm44 net207 net036 net204 net215 net054 net051 vdd net211 dummy_hier_xm11_xm8
.ends BUFFER_VREFP

.subckt Dcap_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Dcap_PMOS_n12_X1_Y1

.subckt DP_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends DP_NMOS_n12_X1_Y1
