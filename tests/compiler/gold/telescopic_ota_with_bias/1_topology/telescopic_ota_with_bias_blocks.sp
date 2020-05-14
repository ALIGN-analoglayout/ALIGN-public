
.subckt CASCODED_SCM_PMOS B DA GA S DC
xM0 DA GA DB B Switch_PMOS_n12_X5_Y2
xM1 DB DA S B Switch_PMOS_n12_X2_Y2
xM2 DC DA S B Switch_PMOS_n12_X2_Y2
.ends CASCODED_SCM_PMOS

.subckt Switch_PMOS_n12_X5_Y2 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=4e-08 nfin=110
m1 S1 G S B nmos_rvt  w=2.7e-07 l=4e-08 nfin=110
.ends Switch_PMOS_n12_X5_Y2

.subckt Switch_PMOS_n12_X2_Y2 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=4e-08 nfin=45
m1 S1 G S B nmos_rvt  w=2.7e-07 l=4e-08 nfin=45
.ends Switch_PMOS_n12_X2_Y2

.subckt CASCODED_CMC_PMOS B DA GA DB S
xM0 DA GA SA B Switch_PMOS_n12_X5_Y2
M1_M3_M2 DB GA S SA B CASCODED_SCM_PMOS
.ends CASCODED_CMC_PMOS

.subckt SCM_NMOS_n12_X3_Y3 B DA S DB
xM0 DA DA S B DCL_NMOS_n12_X2_Y1
xM1 DB DA S B Switch_NMOS_n12_X3_Y3
.ends SCM_NMOS_n12_X3_Y3

.subckt DCL_NMOS_n12_X2_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=4e-08 nfin=20
m1 S1 G S B nmos_rvt  w=2.7e-07 l=4e-08 nfin=20
.ends DCL_NMOS_n12_X2_Y1

.subckt Switch_NMOS_n12_X3_Y3 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=4e-08 nfin=100
m1 S1 G S B nmos_rvt  w=2.7e-07 l=4e-08 nfin=100
.ends Switch_NMOS_n12_X3_Y3

.subckt SCM_PMOS_n12_X1_Y1 B DA S DB
xM0 DA S S B DCL_PMOS_n12_X1_Y1
xM1 DB DA S B Switch_PMOS_n12_X1_Y1
.ends SCM_PMOS_n12_X1_Y1

.subckt DCL_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=4e-08 nfin=10
m1 S1 G S B nmos_rvt  w=2.7e-07 l=4e-08 nfin=10
.ends DCL_PMOS_n12_X1_Y1

.subckt Switch_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=4e-08 nfin=10
m1 S1 G S B nmos_rvt  w=2.7e-07 l=4e-08 nfin=10
.ends Switch_PMOS_n12_X1_Y1

.subckt CMC_NMOS_S_n12_X1_Y1 B DA G S DB
xM0 DA G S B Switch_NMOS_n12_X1_Y1
xM1 DB G S B Switch_NMOS_n12_X1_Y1
.ends CMC_NMOS_S_n12_X1_Y1

.subckt Switch_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=4e-08 nfin=10
m1 S1 G S B nmos_rvt  w=2.7e-07 l=4e-08 nfin=10
.ends Switch_NMOS_n12_X1_Y1

.subckt LS_NMOS_n12_X3_Y2 B DA SA DB SB
xM0 DA DA SA B DCL_NMOS_n12_X1_Y1
xM1 DB DA SB B Switch_NMOS_n12_X3_Y2
.ends LS_NMOS_n12_X3_Y2

.subckt DCL_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=8e-08 nfin=5
m1 S1 G S B nmos_rvt  w=2.7e-07 l=8e-08 nfin=5
.ends DCL_NMOS_n12_X1_Y1

.subckt Switch_NMOS_n12_X3_Y2 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=4e-08 nfin=70
m1 S1 G S B nmos_rvt  w=2.7e-07 l=4e-08 nfin=70
.ends Switch_NMOS_n12_X3_Y2

.subckt LSB_NMOS_2 B DA SA DB SB DC SC
xM2 DC DA SC B Switch_NMOS_n12_X3_Y2
xM0_M1 DA SA DB SB B LS_NMOS_n12_X3_Y2
.ends LSB_NMOS_2

.subckt LS_NMOS_n12_X3_Y2 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=8e-08 nfin=70
m1 S1 G S B nmos_rvt  w=2.7e-07 l=8e-08 nfin=70
.ends LS_NMOS_n12_X3_Y2

.subckt DP_NMOS_n12_X4_Y3 B DA GA S DB GB
xM0 DA GA S B Switch_NMOS_n12_X4_Y3
xM1 DB GB S B Switch_NMOS_n12_X4_Y3
.ends DP_NMOS_n12_X4_Y3

.subckt Switch_NMOS_n12_X4_Y3 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=4e-08 nfin=140
m1 S1 G S B nmos_rvt  w=2.7e-07 l=4e-08 nfin=140
.ends Switch_NMOS_n12_X4_Y3

.subckt telescopic_ota_with_bias vout vss vinn vinp vdd d1
xm13 vbiasp vdd vdd vdd DCL_PMOS_n12_X1_Y1
m7_m6_m2_m1 vout vbiasp vpgate vdd vdd CASCODED_CMC_PMOS
xm5_m4 D1 vss net10 vss SCM_NMOS_n12_X3_Y3
xm16_m17 net9 vdd vbiasn vdd SCM_PMOS_n12_X1_Y1
xm15_m12 net9 d1 vss vbiasp vss CMC_NMOS_S_n12_X1_Y1
m10_m9_m8 vbiasn net10 vpgate net8 vout net014 vss LSB_NMOS_2
xm3_m0 net014 vinn net10 net8 vinp vss DP_NMOS_n12_X4_Y3
.ends telescopic_ota_with_bias

.subckt SCM_NMOS_n12_X3_Y3 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=4e-08 nfin=100
m1 S1 G S B nmos_rvt  w=2.7e-07 l=4e-08 nfin=100
.ends SCM_NMOS_n12_X3_Y3

.subckt SCM_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=4e-08 nfin=10
m1 S1 G S B nmos_rvt  w=2.7e-07 l=4e-08 nfin=10
.ends SCM_PMOS_n12_X1_Y1

.subckt CMC_NMOS_S_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=4e-08 nfin=10
m1 S1 G S B nmos_rvt  w=2.7e-07 l=4e-08 nfin=10
.ends CMC_NMOS_S_n12_X1_Y1

.subckt DP_NMOS_n12_X4_Y3 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=4e-08 nfin=140
m1 S1 G S B nmos_rvt  w=2.7e-07 l=4e-08 nfin=140
.ends DP_NMOS_n12_X4_Y3
