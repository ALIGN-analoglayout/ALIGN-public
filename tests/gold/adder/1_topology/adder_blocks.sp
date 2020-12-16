
.subckt adder vout vgnd vps n1 vin n2
xxI0|MN0 vout vbn1 vgnd b Switch_NMOS_n12_X2_Y2
xxI1|MP0 vout vbp1 vps b Switch_PMOS_n12_X2_Y2
R0 vbn1 n1 Res_20000
C0 vin vbn1 Cap_48f
R1 vbp1 n2 Res_20000
C1 vin vbp1 Cap_48f
R2 vps vout Res_500
.ends adder

.subckt Switch_NMOS_n12_X2_Y2 D G S B
m0 D G S1 B nmos_rvt  l=2.8e-08 nfin=48
m1 S1 G S B nmos_rvt  l=2.8e-08 nfin=48
.ends Switch_NMOS_n12_X2_Y2

.subckt Switch_PMOS_n12_X2_Y2 D G S B
m0 D G S1 B nmos_rvt  l=2.8e-08 nfin=48
m1 S1 G S B nmos_rvt  l=2.8e-08 nfin=48
.ends Switch_PMOS_n12_X2_Y2
