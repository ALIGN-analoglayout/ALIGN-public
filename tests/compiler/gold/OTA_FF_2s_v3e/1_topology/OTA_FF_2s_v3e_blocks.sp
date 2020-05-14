
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

.subckt dummy_hier_m23_m37 op on1 vcmo on op1
xm19 op on1 avss avss Switch_NMOS_n12_X1_Y1
r12_3__dmy0 vcmo op Res_400
r13_3__dmy0 vcmo on Res_400
xm21 on op1 avss avss Switch_NMOS_n12_X1_Y1
.ends dummy_hier_m23_m37

.subckt dummy_hier_m50_m20 op1 op on vcmo on1 cmfb
m19_r12_3__dmy0_r13_3__dmy0_m21 on1 avss vcmo on op1 op dummy_hier_m23_m37
m29_m14_m13 cmfb avss op1 on1 avss CMB_NMOS_2
xm66 avss on1 avss Dcap_NMOS_n12_X1_Y1
xm2 avss on1 avss Dcap_NMOS_n12_X1_Y1
xm64 avss op1 avss Dcap_NMOS_n12_X1_Y1
xm7 avss op1 avss Dcap_NMOS_n12_X1_Y1
.ends dummy_hier_m50_m20

.subckt Dcap_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Dcap_NMOS_n12_X1_Y1

.subckt OTA_FF_2s_v3e ibin avdd vcmi op in on ip vcas avss
xm62 avdd ibin avdd Dcap_PMOS_n12_X1_Y1
xm54 net59 net59 Dummy1_PMOS_n12_X1_Y1
xm43 net5 net5 Dummy1_PMOS_n12_X1_Y1
xm53 avdd ibin avdd Dcap_PMOS_n12_X1_Y1
xm57 avdd ibin avdd Dcap_PMOS_n12_X1_Y1
xm63 net75 vcas net75 Dcap_PMOS_n12_X1_Y1
xm58 net057 vcmo net057 Dcap_PMOS_n12_X1_Y1
xm41 avdd ibin avdd Dcap_PMOS_n12_X1_Y1
xm48 net057 vcmi net057 Dcap_PMOS_n12_X1_Y1
xm0 avss cmfb avss Dcap_NMOS_n12_X1_Y1
xm55 avss avss Dummy1_NMOS_n12_X1_Y1
xm59 avss net044 avss Dcap_NMOS_n12_X1_Y1
xm30 net044 net044 avss avss DCL_NMOS_n12_X1_Y1
xm56 avss cmfb avss Dcap_NMOS_n12_X1_Y1
c4 vcmo on Cap_10f
c5 vcmo op Cap_10f
m16_m6_m4_m36_m35 ibin vcas avdd net5 net59 net057 avdd CASCODED_CMB_PMOS_3
xm33_m34 net044 vcmi net057 cmfb vcmo net057 DP_PMOS_n12_X1_Y1
xm50_m20 on1 ip net5 op1 in net5 DP_PMOS_n12_X1_Y1
xm23_m37 on ip net59 op in net59 DP_PMOS_n12_X1_Y1
m19_r12_3__dmy0_r13_3__dmy0_m21_m29_m14_m13_m66_m2_m64_m7 op avss on vcmo on1 cmfb op1 dummy_hier_m50_m20
.ends OTA_FF_2s_v3e

.subckt Dcap_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Dcap_PMOS_n12_X1_Y1

.subckt Dummy1_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Dummy1_PMOS_n12_X1_Y1

.subckt Dummy1_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Dummy1_NMOS_n12_X1_Y1

.subckt DP_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends DP_PMOS_n12_X1_Y1
