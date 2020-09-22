
.subckt single_to_differential_converter vb vgnd vps vout_sdc2 vout_sdc1 vin
xxI0|MN0 vd net1 vs b Switch_NMOS_n12_X2_Y1
R2 vb net1 Res_20000
R1 vs vgnd Res_900
R0 vps vd Res_900
C2 vs vout_sdc2 Cap_12f
C1 vout_sdc1 vd Cap_12f
C0 vin net1 Cap_48f
.ends single_to_differential_converter

.subckt Switch_NMOS_n12_X2_Y1 D G S B
m0 D G S1 B nmos_rvt  l=2.8e-08 nfin=24
m1 S1 G S B nmos_rvt  l=2.8e-08 nfin=24
.ends Switch_NMOS_n12_X2_Y1
