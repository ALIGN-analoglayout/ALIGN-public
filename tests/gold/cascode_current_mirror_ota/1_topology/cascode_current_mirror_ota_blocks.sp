
.subckt CASCODED_CMC_PMOS B DA GA DB S
xM0 DA GA SA B Switch_PMOS_n12_X5_Y2
xM1 DB GA SB B Switch_PMOS_n12_X5_Y1
xM2 SA DB S B Switch_PMOS_n12_X1_Y1
xM3 SB DB S B Switch_PMOS_n12_X1_Y1
.ends CASCODED_CMC_PMOS

.subckt Switch_PMOS_n12_X5_Y2 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-08 l=2e-08 nfin=120
m1 S1 G S B nmos_rvt  w=2.7e-08 l=2e-08 nfin=120
.ends Switch_PMOS_n12_X5_Y2

.subckt Switch_PMOS_n12_X5_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-08 l=2e-08 nfin=60
m1 S1 G S B nmos_rvt  w=2.7e-08 l=2e-08 nfin=60
.ends Switch_PMOS_n12_X5_Y1

.subckt Switch_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-08 l=2e-08 nfin=10
m1 S1 G S B nmos_rvt  w=2.7e-08 l=2e-08 nfin=10
.ends Switch_PMOS_n12_X1_Y1

.subckt CMC_NMOS_S_n12_X3_Y1 B DA G S DB
xM0 DA G S B Switch_NMOS_n12_X3_Y1
xM1 DB G S B Switch_NMOS_n12_X3_Y1
.ends CMC_NMOS_S_n12_X3_Y1

.subckt Switch_NMOS_n12_X3_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-08 l=2e-08 nfin=30
m1 S1 G S B nmos_rvt  w=2.7e-08 l=2e-08 nfin=30
.ends Switch_NMOS_n12_X3_Y1

.subckt CMC_NMOS_n12_X2_Y1 B DA G SA DB SB
xM0 DA G SA B Switch_NMOS_n12_X2_Y1
xM1 DB G SB B Switch_NMOS_n12_X2_Y1
.ends CMC_NMOS_n12_X2_Y1

.subckt Switch_NMOS_n12_X2_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-08 l=2e-08 nfin=24
m1 S1 G S B nmos_rvt  w=2.7e-08 l=2e-08 nfin=24
.ends Switch_NMOS_n12_X2_Y1

.subckt CASCODED_CMC_NMOS B DA GA DB S
xM3_M2 SB DA S SA B CMC_NMOS_S_n12_X3_Y1
xM1_M0 DB GA SB DA SA B CMC_NMOS_n12_X2_Y1
.ends CASCODED_CMC_NMOS

.subckt CMC_NMOS_S_n12_X3_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-08 l=2e-08 nfin=30
m1 S1 G S B nmos_rvt  w=2.7e-08 l=2e-08 nfin=30
.ends CMC_NMOS_S_n12_X3_Y1

.subckt CMC_NMOS_n12_X2_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-08 l=2e-08 nfin=24
m1 S1 G S B nmos_rvt  w=2.7e-08 l=2e-08 nfin=24
.ends CMC_NMOS_n12_X2_Y1

.subckt SCM_NMOS_n12_X2_Y1 B DA S DB
xM0 DA DA S B DCL_NMOS_n12_X2_Y1
xM1 DB DA S B Switch_NMOS_n12_X2_Y1
.ends SCM_NMOS_n12_X2_Y1

.subckt DCL_NMOS_n12_X2_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-08 l=2e-08 nfin=15
m1 S1 G S B nmos_rvt  w=2.7e-08 l=2e-08 nfin=15
.ends DCL_NMOS_n12_X2_Y1

.subckt DP_NMOS_n12_X3_Y1 B DA GA S DB GB
xM0 DA GA S B Switch_NMOS_n12_X3_Y1
xM1 DB GB S B Switch_NMOS_n12_X3_Y1
.ends DP_NMOS_n12_X3_Y1

.subckt cascode_current_mirror_ota voutp vbiasn vbiasnd vinn id vss vinp vdd vbiasp
xm1nup vbiasn vbiasn net9b vss DCL_NMOS_n12_X1_Y1
xm1ndown net9b net9b vss vss DCL_NMOS_n12_X1_Y1
xm1pup net8b vdd vdd vdd DCL_PMOS_n12_X1_Y1
xm1pdown vbiasp net8b net8b vdd DCL_PMOS_n12_X1_Y1
m23_m27_m18_m19 voutp vbiasp net27 vdd vdd CASCODED_CMC_PMOS
m22_m26_m20_m21 vbiasnd vbiasp net16 vdd vdd CASCODED_CMC_PMOS
m24_m25_m11_m10 vbiasnd vbiasn voutp vss vss CASCODED_CMC_NMOS
xm14_m16 id vss net24 vss SCM_NMOS_n12_X2_Y1
xm17_m15 net16 vinn net24 net27 vinp vss DP_NMOS_n12_X3_Y1
.ends cascode_current_mirror_ota

.subckt DCL_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=2e-08 nfin=3
m1 S1 G S B nmos_rvt  w=2.7e-07 l=2e-08 nfin=3
.ends DCL_NMOS_n12_X1_Y1

.subckt DCL_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=2e-08 nfin=5
m1 S1 G S B nmos_rvt  w=2.7e-07 l=2e-08 nfin=5
.ends DCL_PMOS_n12_X1_Y1

.subckt SCM_NMOS_n12_X2_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-08 l=2e-08 nfin=15
m1 S1 G S B nmos_rvt  w=2.7e-08 l=2e-08 nfin=15
.ends SCM_NMOS_n12_X2_Y1

.subckt DP_NMOS_n12_X3_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-08 l=2e-08 nfin=30
m1 S1 G S B nmos_rvt  w=2.7e-08 l=2e-08 nfin=30
.ends DP_NMOS_n12_X3_Y1
