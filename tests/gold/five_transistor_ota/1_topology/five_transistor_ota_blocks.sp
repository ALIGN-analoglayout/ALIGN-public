
.subckt SCM_NMOS_n12_X1_Y1 B DA S DB
xM0 DA DA S B DCL_NMOS_n12_X1_Y1
xM1 DB DA S B Switch_NMOS_n12_X1_Y1
.ends SCM_NMOS_n12_X1_Y1

.subckt DCL_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=2e-08 nfin=5
m1 S1 G S B nmos_rvt  w=2.7e-07 l=2e-08 nfin=5
.ends DCL_NMOS_n12_X1_Y1

.subckt Switch_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=2e-08 nfin=5
m1 S1 G S B nmos_rvt  w=2.7e-07 l=2e-08 nfin=5
.ends Switch_NMOS_n12_X1_Y1

.subckt SCM_PMOS_n12_X1_Y1 B DA S DB
xM0 DA S S B DCL_PMOS_n12_X1_Y1
xM1 DB DA S B Switch_PMOS_n12_X1_Y1
.ends SCM_PMOS_n12_X1_Y1

.subckt DCL_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=2e-08 nfin=5
m1 S1 G S B nmos_rvt  w=2.7e-07 l=2e-08 nfin=5
.ends DCL_PMOS_n12_X1_Y1

.subckt Switch_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=2e-08 nfin=5
m1 S1 G S B nmos_rvt  w=2.7e-07 l=2e-08 nfin=5
.ends Switch_PMOS_n12_X1_Y1

.subckt DP_NMOS_n12_X1_Y1 B DA GA S DB GB
xM0 DA GA S B Switch_NMOS_n12_X1_Y1
xM1 DB GB S B Switch_NMOS_n12_X1_Y1
.ends DP_NMOS_n12_X1_Y1

.subckt five_transistor_ota id vss vout vinn vinp vdd
xm5_m4 id vss net10 vss SCM_NMOS_n12_X1_Y1
xm1_m2 net8 vdd vout vdd SCM_PMOS_n12_X1_Y1
xm3_m0 vout vinn net10 net8 vinp vss DP_NMOS_n12_X1_Y1
.ends five_transistor_ota

.subckt SCM_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=2e-08 nfin=5
m1 S1 G S B nmos_rvt  w=2.7e-07 l=2e-08 nfin=5
.ends SCM_NMOS_n12_X1_Y1

.subckt SCM_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=2e-08 nfin=5
m1 S1 G S B nmos_rvt  w=2.7e-07 l=2e-08 nfin=5
.ends SCM_PMOS_n12_X1_Y1

.subckt DP_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=2e-08 nfin=5
m1 S1 G S B nmos_rvt  w=2.7e-07 l=2e-08 nfin=5
.ends DP_NMOS_n12_X1_Y1
