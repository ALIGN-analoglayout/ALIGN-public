
.subckt INV_LVT zn i SN SP
xxm0 zn i SN SN Switch_NMOS_n12_X1_Y1
xxm1 zn i SP SP Switch_PMOS_n12_X1_Y1
.ends INV_LVT

.subckt Switch_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=2e-08 nfin=12
m1 S1 G S B nmos_rvt  w=2.7e-07 l=2e-08 nfin=12
.ends Switch_NMOS_n12_X1_Y1

.subckt Switch_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=2.7e-07 l=2e-08 nfin=12
m1 S1 G S B nmos_rvt  w=2.7e-07 l=2e-08 nfin=12
.ends Switch_PMOS_n12_X1_Y1

.subckt inverter_v2 vdd vin vout vss
mn1_mp1 vin vss vdd vout INV_LVT
.ends inverter_v2
