
.subckt Santized_BTSW VBTSW AVDD CKSBT CKSBTB AVSS VIN
xMM9 VBTSW net7 net12 net12 Switch_PMOS_n12_X1_Y1
xMM8 AVDD VBTSW net12 net12 Switch_PMOS_n12_X1_Y1
xMM7 net7 CKSBT AVDD AVDD Switch_PMOS_n12_X1_Y1
xMM10 net013 net12 AVSS Dcap_NMOS_n12_X1_Y1
xMM6 net27 CKSBTB AVSS AVSS Switch_NMOS_n12_X1_Y1
xMM5 VBTSW AVDD net27 AVSS Switch_NMOS_n12_X1_Y1
xMM3 VIN VBTSW net013 AVSS Switch_NMOS_n12_X1_Y1
xMM2 net7 VBTSW net013 AVSS Switch_NMOS_n12_X1_Y1
xMM1 net013 CKSBTB AVSS AVSS Switch_NMOS_n12_X1_Y1
xMM0 net7 CKSBT net013 AVSS Switch_NMOS_n12_X1_Y1
.ends Santized_BTSW

.subckt Switch_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  l=1e-08 w=1e-08 m=1
m1 S1 G S B nmos_rvt  l=1e-08 w=1e-08 m=1
.ends Switch_PMOS_n12_X1_Y1

.subckt Dcap_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  l=1e-08 w=1e-08 m=4
m1 S1 G S B nmos_rvt  l=1e-08 w=1e-08 m=4
.ends Dcap_NMOS_n12_X1_Y1

.subckt Switch_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  l=1e-08 w=1e-08 m=1
m1 S1 G S B nmos_rvt  l=1e-08 w=1e-08 m=1
.ends Switch_NMOS_n12_X1_Y1
