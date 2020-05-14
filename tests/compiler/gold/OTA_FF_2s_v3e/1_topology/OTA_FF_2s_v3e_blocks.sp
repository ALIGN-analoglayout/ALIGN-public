
.subckt CASCODED_SCM_PMOS B DA GA S DC
xM0 DA GA DB B Switch_PMOS_n12_X1_Y1
xM1 DB DA S B Switch_PMOS_n12_X1_Y1
xM2 DC DA S B Switch_PMOS_n12_X1_Y1
.ends CASCODED_SCM_PMOS

.subckt Switch_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Switch_PMOS_n12_X1_Y1

.subckt CASCODED_CMB_PMOS_2 B DA GA S DC DD
xM3 DD DA S B Switch_PMOS_n12_X1_Y1
M0_M1_M2 DA GA S DC B CASCODED_SCM_PMOS
.ends CASCODED_CMB_PMOS_2

.subckt CASCODED_CMB_PMOS_3 B DA GA S DC DD DE
xM4 DE DA S B Switch_PMOS_n12_X1_Y1
M0_M1_M3_M2 DA GA S DD DC B CASCODED_CMB_PMOS_2
.ends CASCODED_CMB_PMOS_3

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

.subckt DP_PMOS_n12_X1_Y1 B DA GA S DB GB
xM0 DA GA S B Switch_PMOS_n12_X1_Y1
xM1 DB GB S B Switch_PMOS_n12_X1_Y1
.ends DP_PMOS_n12_X1_Y1

.subckt dummy_hier_m50_m20 on1 cmfb op1 op on
xm2 avss on1 avss Dcap_NMOS_n12_X1_Y1
m29_m14_m13 cmfb avss op1 on1 avss CMB_NMOS_2
xm19 op on1 avss avss Switch_NMOS_n12_X1_Y1
xm66 avss on1 avss Dcap_NMOS_n12_X1_Y1
xm64 avss op1 avss Dcap_NMOS_n12_X1_Y1
xm21 on op1 avss avss Switch_NMOS_n12_X1_Y1
xm7 avss op1 avss Dcap_NMOS_n12_X1_Y1
.ends dummy_hier_m50_m20

.subckt Dcap_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Dcap_NMOS_n12_X1_Y1

.subckt dummy_hier_m23_m37 on1 on op cmfb op1 vcmo
m2_m29_m14_m13_m19_m66_m64_m21_m7 avss cmfb op1 op on on1 dummy_hier_m50_m20
r13_3__dmy0 vcmo on Res_400
r12_3__dmy0 vcmo op Res_400
.ends dummy_hier_m23_m37
