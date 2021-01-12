
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

.subckt BUFFER_VREFP_ud vrefp vdd ibias2 gnd vref ibias1
xm60 vrefp vdd Dummy1_PMOS_n12_X1_Y1
xm37 vdd net057 vdd Dcap_PMOS_n12_X1_Y1
xm28 vrefp net052 vdd vdd Switch_PMOS_n12_X1_Y1
xm15 net050 net036 vdd vdd Switch_PMOS_n12_X1_Y1
xm59 net057 vdd Dummy1_PMOS_n12_X1_Y1
xm57 vdd vdd Dummy1_PMOS_n12_X1_Y1
xm58 net050 vdd Dummy1_PMOS_n12_X1_Y1
xm55 vdd vdd Dummy1_PMOS_n12_X1_Y1
xm54 net050 vdd Dummy1_PMOS_n12_X1_Y1
xm38 vdd net036 vdd Dcap_PMOS_n12_X1_Y1
xm65 ibias2 gnd Dummy1_NMOS_n12_X1_Y1
xm63 gnd gnd Dummy1_NMOS_n12_X1_Y1
xm61 gnd gnd Dummy1_NMOS_n12_X1_Y1
xm56 net057 gnd Dummy1_NMOS_n12_X1_Y1
xm43 net211 gnd Dummy1_NMOS_n12_X1_Y1
xm53 gnd gnd Dummy1_NMOS_n12_X1_Y1
xm52 net036 gnd Dummy1_NMOS_n12_X1_Y1
xm47 net212 gnd Dummy1_NMOS_n12_X1_Y1
xm50 net207 gnd Dummy1_NMOS_n12_X1_Y1
xm45 net051 gnd Dummy1_NMOS_n12_X1_Y1
xm49 gnd gnd Dummy1_NMOS_n12_X1_Y1
xm40 net204 gnd Dummy1_NMOS_n12_X1_Y1
xm46 net054 gnd Dummy1_NMOS_n12_X1_Y1
xm44 net215 gnd Dummy1_NMOS_n12_X1_Y1
xm39 ibias1 gnd Dummy1_NMOS_n12_X1_Y1
xm42 net051 vdd Dummy1_PMOS_n12_X1_Y1
xm35 net211 vdd Dummy1_PMOS_n12_X1_Y1
xm33 vdd vdd Dummy1_PMOS_n12_X1_Y1
xm41 net054 vdd Dummy1_PMOS_n12_X1_Y1
xm32 vdd vdd Dummy1_PMOS_n12_X1_Y1
xm36 net215 vdd Dummy1_PMOS_n12_X1_Y1
xm31 net204 vdd Dummy1_PMOS_n12_X1_Y1
m4_m5_m3 ibias1 gnd net204 net212 gnd CMB_NMOS_2
m64_m30_m21 ibias2 gnd net052 net057 gnd CMB_NMOS_2
xm1_m6 net207 gnd net036 gnd SCM_NMOS_n12_X1_Y1
xm23_m24 net215 vdd net051 vdd SCM_PMOS_n12_X1_Y1
xm25_m26 net211 vdd net054 vdd SCM_PMOS_n12_X1_Y1
m22_m14_m13 net204 vdd net207 net054 net036 net051 vdd LSB_PMOS_2
xm27_m29 net057 net050 net052 vrefp vdd LS_PMOS_n12_X1_Y1
xm12_m10 net051 vref net212 net054 net050 gnd DP_NMOS_n12_X1_Y1
xm8_m11 net215 net050 net212 net211 vref gnd DP_NMOS_n12_X1_Y1
.ends BUFFER_VREFP_ud

.subckt Dummy1_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Dummy1_PMOS_n12_X1_Y1

.subckt Dcap_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Dcap_PMOS_n12_X1_Y1

.subckt Dummy1_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Dummy1_NMOS_n12_X1_Y1

.subckt SCM_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends SCM_PMOS_n12_X1_Y1

.subckt DP_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends DP_NMOS_n12_X1_Y1
