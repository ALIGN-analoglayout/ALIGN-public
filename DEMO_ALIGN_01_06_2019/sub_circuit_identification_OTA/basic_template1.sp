.subckt Switch_NMOS_10_1x1  D G S
M0 (D G S 0) NMOS_VTL w=w1 l=l1
.ends Switch_NMOS_10_1x1

.subckt Switch_PMOS_10_1x1  D G S
M0 (D G S 0) PMOS_VTL w=w1 l=l1
.ends Switch_PMOS_10_1x1

.subckt SCM_NMOS_50_1x12 D1 D2 S
M0 (D1 D1 S 0) NMOS_VTL w=w l=90n
M1 (D2 D1 S 0) NMOS_VTL w=w l=90n
.ends L1_scm

.subckt DL2_PMOS_10_1x6  D1 D2 G S
M0 (D1 G S 0) PMOS_VTL w=w l=90n
M1 (D2 G S 0) PMOS_VTL w=w l=90n
.ends DL2_PMOS_10_1x6

.subckt DL2_PMOS_10_1x4  D1 D2 G S
M0 (D1 G S 0) PMOS_VTL w=w l=90n
M1 (D2 G S 0) PMOS_VTL w=w l=90n
.ends DL2_PMOS_10_1x4

.subckt DP_NMOS_75_3x10  D1 D2 G1 G2 S
M0 (D1 G1 S 0) NMOS_VTL w=w l=90n
M1 (D2 G2 S 0) NMOS_VTL w=w l=90n
.ends DP_NMOS_75_3x10

.subckt DL1_PMOS_15_1x6 D1 D2 S1 S2 G
M0 (D1 G S1 0) PMOS_VTL w=w l=90n
M1 (D2 G S2 0) PMOS_VTL w=w l=90n
.ends DL1_PMOS_15_1x6

.subckt DL1_NMOS_25_1x10 D1 D2 S1 S2 G
M0 (D1 G S1 0) NMOS_VTL w=w l=90n
M1 (D2 G S2 0) NMOS_VTL w=w l=90n
.ends DL1_NMOS_25_1x10

.subckt Cap_60f_2x3 PLUS MINUS
CC1 PLUS MINUS cap 60f
.ends Cap_60f_2x3

.subckt DiodeConnected_NMOS_5_1x1 D S
M0 (D D S 0) NMOS_VTL w=w l=90n
.ends DiodeConnected_NMOS_5_1x1

.subckt DiodeConnected_PMOS_5_1x1 D S
M0 (D D S 0) PMOS_VTL w=w l=90n
.ends DiodeConnected_PMOS_5_1x1
