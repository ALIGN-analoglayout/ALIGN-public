
.subckt INV_LVT zn i SN SP
xxm0 zn i SN SN Switch_NMOS_n12_X2_Y2
xxm1 zn i SP SP Switch_PMOS_n12_X2_Y1
.ends INV_LVT

.subckt Switch_NMOS_n12_X2_Y2 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=2e-08 nfin=48
m1 S1 G S B nmos_rvt  w=2.7e-07 l=2e-08 nfin=48
.ends Switch_NMOS_n12_X2_Y2

.subckt Switch_PMOS_n12_X2_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=2e-08 nfin=24
m1 S1 G S B nmos_rvt  w=2.7e-07 l=2e-08 nfin=24
.ends Switch_PMOS_n12_X2_Y1

.subckt INV_LVT_type1 zn i SN SP
xxm0 zn i SN SN Switch_NMOS_n12_X1_Y1
xxm1 zn i SP SP Switch_PMOS_n12_X1_Y1
.ends INV_LVT_type1

.subckt Switch_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=2e-08 nfin=12
m1 S1 G S B nmos_rvt  w=2.7e-07 l=2e-08 nfin=12
.ends Switch_NMOS_n12_X1_Y1

.subckt Switch_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=2e-08 nfin=12
m1 S1 G S B nmos_rvt  w=2.7e-07 l=2e-08 nfin=12
.ends Switch_PMOS_n12_X1_Y1

.subckt stage2_inv G1 SN G2 SP
MM0_MM2 D SN SP G1 INV_LVT
xMM1_MM3 G2 SN SP D INV_LVT_type1
.ends stage2_inv

.subckt INV_LVT_type1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=2e-08 nfin=12
m1 S1 G S B nmos_rvt  w=2.7e-07 l=2e-08 nfin=12
.ends INV_LVT_type1

.subckt buffer vdd vin vss vout
mn2_mn1_mp2_mp1 vss vin vdd vout stage2_inv
.ends buffer
