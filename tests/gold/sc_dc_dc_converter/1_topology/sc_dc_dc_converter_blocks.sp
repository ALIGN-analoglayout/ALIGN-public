
.subckt CMC_NMOS_S_n12_X139_Y6 B DA G S DB
xM0 DA G S B Switch_NMOS_n12_X139_Y6
xM1 DB G S B Switch_NMOS_n12_X139_Y6
.ends CMC_NMOS_S_n12_X139_Y6

.subckt Switch_NMOS_n12_X139_Y6 D G S B
m0 D G S1 B nmos_rvt  w=00027 l=2e-08 nfin=10000
m1 S1 G S B nmos_rvt  w=00027 l=2e-08 nfin=10000
.ends Switch_NMOS_n12_X139_Y6

.subckt DP_NMOS_n12_X139_Y6 B DA GA S DB GB
xM0 DA GA S B Switch_NMOS_n12_X139_Y6
xM1 DB GB S B Switch_NMOS_n12_X139_Y6
.ends DP_NMOS_n12_X139_Y6

.subckt CMC_NMOS_n12_X139_Y6 B DA G SA DB SB
xM0 DA G SA B Switch_NMOS_n12_X139_Y6
xM1 DB G SB B Switch_NMOS_n12_X139_Y6
.ends CMC_NMOS_n12_X139_Y6

.subckt sc_dc_dc_converter vout phi1 phi2 vss vin
xm3 vout phi2 net10 vss Switch_NMOS_n12_X139_Y6
c1 net8 net7 Cap_1000000f
c0 net9 net10 Cap_1000000f
xm7_m4 net7 phi2 vss net9 vss CMC_NMOS_S_n12_X139_Y6
xm6_m5 vout phi2 net8 net9 phi1 vss DP_NMOS_n12_X139_Y6
xm8_m0 vout phi1 net7 net10 vin vss CMC_NMOS_n12_X139_Y6
.ends sc_dc_dc_converter

.subckt CMC_NMOS_S_n12_X139_Y6 D G S B
m0 D G S1 B nmos_rvt  w=00027 l=2e-08 nfin=10000
m1 S1 G S B nmos_rvt  w=00027 l=2e-08 nfin=10000
.ends CMC_NMOS_S_n12_X139_Y6

.subckt DP_NMOS_n12_X139_Y6 D G S B
m0 D G S1 B nmos_rvt  w=00027 l=2e-08 nfin=10000
m1 S1 G S B nmos_rvt  w=00027 l=2e-08 nfin=10000
.ends DP_NMOS_n12_X139_Y6

.subckt CMC_NMOS_n12_X139_Y6 D G S B
m0 D G S1 B nmos_rvt  w=00027 l=2e-08 nfin=10000
m1 S1 G S B nmos_rvt  w=00027 l=2e-08 nfin=10000
.ends CMC_NMOS_n12_X139_Y6
