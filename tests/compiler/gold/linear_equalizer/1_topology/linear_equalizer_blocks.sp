
.subckt SCM_NMOS_n12_X3_Y2 B DA S DB
xM0 DA DA S B DCL_NMOS_n12_X3_Y2
xM1 DB DA S B Switch_NMOS_n12_X3_Y2
.ends SCM_NMOS_n12_X3_Y2

.subckt DCL_NMOS_n12_X3_Y2 D G S B
m0 D G S1 B nmos_rvt  l=2.8e-08 nfin=72
m1 S1 G S B nmos_rvt  l=2.8e-08 nfin=72
.ends DCL_NMOS_n12_X3_Y2

.subckt Switch_NMOS_n12_X3_Y2 D G S B
m0 D G S1 B nmos_rvt  l=2.8e-08 nfin=72
m1 S1 G S B nmos_rvt  l=2.8e-08 nfin=72
.ends Switch_NMOS_n12_X3_Y2

.subckt CMB_NMOS_2 B DA S DB DC
xM2 DC DA S B Switch_NMOS_n12_X3_Y2
xM0_M1 DA S DB B SCM_NMOS_n12_X3_Y2
.ends CMB_NMOS_2

.subckt SCM_NMOS_n12_X3_Y2 D G S B
m0 D G S1 B nmos_rvt  l=2.8e-08 nfin=72
m1 S1 G S B nmos_rvt  l=2.8e-08 nfin=72
.ends SCM_NMOS_n12_X3_Y2

.subckt linear_equalizer vout_ctle2 vin2 vout_ctle1 vin1 vmirror_ctle vgnd vps s3_ctle s0_ctle
xxI0|MN0 vout_ctle2 vin2 net8 b Switch_NMOS_n12_X2_Y2
xxI1|MN0 vout_ctle1 vin1 net5 b Switch_NMOS_n12_X2_Y2
R1 vps vout_ctle2 Res_800
R0 vps vout_ctle1 Res_800
C4 net8 net021 Cap_24f
C3 net5 net022 Cap_24f
R4 net5 net016 Res_100
R3 net8 net015 Res_100
xMN9 net021 s3_ctle net022 vgnd Switch_NMOS_n12_X2_Y2
xMN6 net015 s0_ctle net016 vgnd Switch_NMOS_n12_X2_Y2
xI4|MN0_xI2|MN0_xI3|MN0 vmirror_ctle vgnd net8 net5 b CMB_NMOS_2
.ends linear_equalizer

.subckt Switch_NMOS_n12_X2_Y2 D G S B
m0 D G S1 B nmos_rvt  l=2.8e-08 nfin=48
m1 S1 G S B nmos_rvt  l=2.8e-08 nfin=48
.ends Switch_NMOS_n12_X2_Y2
