
.subckt CASCODED_SCM_NMOS B DA GA S DC
xM0 DA GA DB B Switch_NMOS_n12_X2_Y1
xM1 DB DA S B Switch_NMOS_n12_X2_Y1
xM2 DC DA S B Switch_NMOS_n12_X2_Y1
.ends CASCODED_SCM_NMOS

.subckt Switch_NMOS_n12_X2_Y1 D G S B
m0 D G S1 B nmos_rvt  nfin=24
m1 S1 G S B nmos_rvt  nfin=24
.ends Switch_NMOS_n12_X2_Y1

.subckt CASCODED_CMC_NMOS B DA GA DB S
xM1 DB GA SB B Switch_NMOS_n12_X2_Y1
M0_M2_M3 DA GA S SB B CASCODED_SCM_NMOS
.ends CASCODED_CMC_NMOS

.subckt SCM_PMOS_n12_X3_Y1 B DA S DB
xM0 DA S S B DCL_PMOS_n12_X1_Y1
xM1 DB DA S B Switch_PMOS_n12_X3_Y1
.ends SCM_PMOS_n12_X3_Y1

.subckt DCL_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  nfin=12
m1 S1 G S B nmos_rvt  nfin=12
.ends DCL_PMOS_n12_X1_Y1

.subckt Switch_PMOS_n12_X3_Y1 D G S B
m0 D G S1 B nmos_rvt  nfin=36
m1 S1 G S B nmos_rvt  nfin=36
.ends Switch_PMOS_n12_X3_Y1

.subckt CMB_PMOS_2 B DA S DB DC
xM2 DC DA S B Switch_PMOS_n12_X3_Y1
xM0_M1 DA S DB B SCM_PMOS_n12_X3_Y1
.ends CMB_PMOS_2

.subckt SCM_PMOS_n12_X3_Y1 D G S B
m0 D G S1 B nmos_rvt  nfin=36
m1 S1 G S B nmos_rvt  nfin=36
.ends SCM_PMOS_n12_X3_Y1

.subckt SCM_PMOS_type1 B DA S DB
xM0 DA S S B DCL_PMOS_n12_X1_Y1
xM1 DB DA S B Switch_PMOS_n12_X2_Y1
.ends SCM_PMOS_type1

.subckt Switch_PMOS_n12_X2_Y1 D G S B
m0 D G S1 B nmos_rvt  nfin=24
m1 S1 G S B nmos_rvt  nfin=24
.ends Switch_PMOS_n12_X2_Y1

.subckt LS_PMOS_n12_X3_Y1 B DA SA DB SB
xM0 DA SA SA B DCL_PMOS_n12_X4_Y2
xM1 DB DA SB B Switch_PMOS_n12_X3_Y1
.ends LS_PMOS_n12_X3_Y1

.subckt DCL_PMOS_n12_X4_Y2 D G S B
m0 D G S1 B nmos_rvt  nfin=96
m1 S1 G S B nmos_rvt  nfin=96
.ends DCL_PMOS_n12_X4_Y2

.subckt LSB_PMOS_2 B DA SA DB SB DC SC
xM2 DC DA SC B Switch_PMOS_n12_X3_Y1
xM0_M1 DA SA DB SB B LS_PMOS_n12_X4_Y2
.ends LSB_PMOS_2

.subckt LS_PMOS_n12_X4_Y2 D G S B
m0 D G S1 B nmos_rvt  nfin=96
m1 S1 G S B nmos_rvt  nfin=96
.ends LS_PMOS_n12_X4_Y2

.subckt DP_NMOS_n12_X5_Y1 B DA GA S DB GB
xM0 DA GA S B Switch_NMOS_n12_X5_Y1
xM1 DB GB S B Switch_NMOS_n12_X5_Y1
.ends DP_NMOS_n12_X5_Y1

.subckt Switch_NMOS_n12_X5_Y1 D G S B
m0 D G S1 B nmos_rvt  nfin=60
m1 S1 G S B nmos_rvt  nfin=60
.ends Switch_NMOS_n12_X5_Y1

.subckt ldo_error_amp vbias_bf vss_x vbias_an vref vfb vg vcc_nom
xmn56 vbias6 vbias_bf vss_x vss_x Switch_NMOS_n12_X1_Y1
xmn40 vss_x vbias_bf vss_x Dcap_NMOS_n12_X1_Y1
xmn41 vbias4 vbias_an vss_x vss_x Switch_NMOS_n12_X1_Y1
xmn21 vbias2 vbias1 vbias3 vss_x Switch_NMOS_n12_X1_Y1
xmn55 v3_d vbias_bf vss_x vss_x Switch_NMOS_n12_X2_Y1
xmn3 vss_x vbias_an vss_x Dcap_NMOS_n12_X1_Y1
xmn2 vcom1 vbias_an vss_x vss_x Switch_NMOS_n12_X2_Y1
xmmp5 vg vcc_nom vcc_nom vcc_nom DCL_PMOS_n12_X1_Y1
xmmp1 v3_d v3 vg vcc_nom Switch_PMOS_n12_X2_Y1
xmmn322 vg v3_d vss_x vss_x Switch_NMOS_n12_X1_Y1
xmmn42 vbias3 vbias3 vbias4 vss_x DCL_NMOS_n12_X2_Y2
mn38_mn39_mn37_mn20 v4 vbias3 v3 vss_x vss_x CASCODED_CMC_NMOS
mp34_mp28_mp22 vbias1 vcc_nom v2 v1 vcc_nom CMB_PMOS_2
xmp41_mp4 vbias6 vcc_nom vg vcc_nom SCM_PMOS_n12_X2_Y1
mmp33_mmp30_mmp29 vbias2 vbias1 v3 v1 v4 v2 vcc_nom LSB_PMOS_2
xmn23_mn22 v2 vfb vcom1 v1 vref vss_x DP_NMOS_n12_X5_Y1
.ends ldo_error_amp

.subckt Switch_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  nfin=12
m1 S1 G S B nmos_rvt  nfin=12
.ends Switch_NMOS_n12_X1_Y1

.subckt Dcap_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  nfin=12
m1 S1 G S B nmos_rvt  nfin=12
.ends Dcap_NMOS_n12_X1_Y1

.subckt DCL_NMOS_n12_X2_Y2 D G S B
m0 D G S1 B nmos_rvt  nfin=48
m1 S1 G S B nmos_rvt  nfin=48
.ends DCL_NMOS_n12_X2_Y2

.subckt SCM_PMOS_n12_X2_Y1 D G S B
m0 D G S1 B nmos_rvt  nfin=24
m1 S1 G S B nmos_rvt  nfin=24
.ends SCM_PMOS_n12_X2_Y1

.subckt DP_NMOS_n12_X5_Y1 D G S B
m0 D G S1 B nmos_rvt  nfin=60
m1 S1 G S B nmos_rvt  nfin=60
.ends DP_NMOS_n12_X5_Y1
