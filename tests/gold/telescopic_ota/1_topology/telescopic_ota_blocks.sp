
.subckt SCM_NMOS_n12_X3_Y1 B DA S DB
xM0 DA DA S B DCL_NMOS_n12_X2_Y1
xM1 DB DA S B Switch_NMOS_n12_X3_Y1
.ends SCM_NMOS_n12_X3_Y1

.subckt DCL_NMOS_n12_X2_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=2e-08 nfin=24
m1 S1 G S B nmos_rvt  w=2.7e-07 l=2e-08 nfin=24
.ends DCL_NMOS_n12_X2_Y1

.subckt Switch_NMOS_n12_X3_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=2e-08 nfin=36
m1 S1 G S B nmos_rvt  w=2.7e-07 l=2e-08 nfin=36
.ends Switch_NMOS_n12_X3_Y1

.subckt CMC_PMOS_S_n12_X1_Y1 B DA G S DB
xM0 DA G S B Switch_PMOS_n12_X1_Y1
xM1 DB G S B Switch_PMOS_n12_X1_Y1
.ends CMC_PMOS_S_n12_X1_Y1

.subckt Switch_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=2e-08 nfin=12
m1 S1 G S B nmos_rvt  w=2.7e-07 l=2e-08 nfin=12
.ends Switch_PMOS_n12_X1_Y1

.subckt DP_NMOS_n12_X3_Y3 B DA GA S DB GB
xM0 DA GA S B Switch_NMOS_n12_X3_Y3
xM1 DB GB S B Switch_NMOS_n12_X3_Y3
.ends DP_NMOS_n12_X3_Y3

.subckt Switch_NMOS_n12_X3_Y3 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=2e-08 nfin=108
m1 S1 G S B nmos_rvt  w=2.7e-07 l=2e-08 nfin=108
.ends Switch_NMOS_n12_X3_Y3

.subckt CMC_PMOS_n12_X2_Y1 B DA G SA DB SB
xM0 DA G SA B Switch_PMOS_n12_X2_Y1
xM1 DB G SB B Switch_PMOS_n12_X2_Y1
.ends CMC_PMOS_n12_X2_Y1

.subckt Switch_PMOS_n12_X2_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=2e-08 nfin=24
m1 S1 G S B nmos_rvt  w=2.7e-07 l=2e-08 nfin=24
.ends Switch_PMOS_n12_X2_Y1

.subckt CMC_NMOS_n12_X3_Y1 B DA G SA DB SB
xM0 DA G SA B Switch_NMOS_n12_X3_Y1
xM1 DB G SB B Switch_NMOS_n12_X3_Y1
.ends CMC_NMOS_n12_X3_Y1

.subckt telescopic_ota voutn vbiasn voutp d1 vss vinn vinp vbiasp2 vbiasp1 vdd
xm5_m4 d1 vss net10 vss SCM_NMOS_n12_X3_Y1
xm2_m1 net012 vbiasp1 vdd net06 vdd CMC_PMOS_S_n12_X1_Y1
xm3_m0 net014 vinn net10 net8 vinp vss DP_NMOS_n12_X3_Y3
xm7_m6 voutp vbiasp2 net012 voutn net06 net06 CMC_PMOS_n12_X2_Y1
xm9_m8 voutn vbiasn net8 voutp net014 vss CMC_NMOS_n12_X3_Y1
.ends telescopic_ota

.subckt SCM_NMOS_n12_X3_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=2e-08 nfin=36
m1 S1 G S B nmos_rvt  w=2.7e-07 l=2e-08 nfin=36
.ends SCM_NMOS_n12_X3_Y1

.subckt CMC_PMOS_S_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=2e-08 nfin=12
m1 S1 G S B nmos_rvt  w=2.7e-07 l=2e-08 nfin=12
.ends CMC_PMOS_S_n12_X1_Y1

.subckt DP_NMOS_n12_X3_Y3 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=2e-08 nfin=108
m1 S1 G S B nmos_rvt  w=2.7e-07 l=2e-08 nfin=108
.ends DP_NMOS_n12_X3_Y3

.subckt CMC_PMOS_n12_X2_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=2e-08 nfin=24
m1 S1 G S B nmos_rvt  w=2.7e-07 l=2e-08 nfin=24
.ends CMC_PMOS_n12_X2_Y1

.subckt CMC_NMOS_n12_X3_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=2e-08 nfin=36
m1 S1 G S B nmos_rvt  w=2.7e-07 l=2e-08 nfin=36
.ends CMC_NMOS_n12_X3_Y1
