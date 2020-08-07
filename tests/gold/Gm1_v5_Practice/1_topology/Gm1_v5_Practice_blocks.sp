
.subckt SCM_PMOS_n12_X1_Y1 B DA S DB
xM0 DA S S B DCL_PMOS_n12_X1_Y1
xM1 DB DA S B Switch_PMOS_n12_X1_Y1
.ends SCM_PMOS_n12_X1_Y1

.subckt DCL_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08 m=2
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08 m=2
.ends DCL_PMOS_n12_X1_Y1

.subckt Switch_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Switch_PMOS_n12_X1_Y1

.subckt CMB_PMOS_2 B DA S DB DC
xM2 DC DA S B Switch_PMOS_n12_X1_Y1
xM0_M1 DA S DB B SCM_PMOS_n12_X1_Y1
.ends CMB_PMOS_2

.subckt SCM_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08 m=2
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08 m=2
.ends SCM_PMOS_n12_X1_Y1

.subckt DP_NMOS_n12_X1_Y1 B DA GA S DB GB
xM0 DA GA S B Switch_NMOS_n12_X1_Y1
xM1 DB GB S B Switch_NMOS_n12_X1_Y1
.ends DP_NMOS_n12_X1_Y1

.subckt Switch_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Switch_NMOS_n12_X1_Y1

.subckt Gm1_v5_Practice vss vdd ibias vom vop vim vip
xm8 net074 ntail1 vss vss Switch_NMOS_n12_X1_Y1
xm2 vdd ibias vdd Dcap_PMOS_n12_X1_Y1
c21 vom ntail1 Cap_12f
c22 vop ntail1 Cap_12f
r12 vop ntail1 Res_100
r11 vom ntail1 Res_100
xm3 vss ntail1 vss Dcap_NMOS_n12_X1_Y1
m12_m14_m11 ibias vdd vop vom vdd CMB_PMOS_2
xm27_m26 vom vip net074 vop vim net074 DP_NMOS_n12_X1_Y1
.ends Gm1_v5_Practice

.subckt Dcap_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08 m=2
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08 m=2
.ends Dcap_PMOS_n12_X1_Y1

.subckt Dcap_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08 m=2
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08 m=2
.ends Dcap_NMOS_n12_X1_Y1

.subckt DP_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends DP_NMOS_n12_X1_Y1
