.subckt Switch_NMOS  D G S
M0 (D G S 0) NMOS_VTL w=w1 l=l1
.ends Switch_NMOS

.subckt Switch_PMOS  D G S
M0 (D G S 0) PMOS_VTL w=w1 l=l1
.ends Switch_PMOS

.subckt SCM_NMOS D1 D2 S
M0 (D1 D1 S 0) NMOS_VTL w=w l=90n
M1 (D2 D1 S 0) NMOS_VTL w=w l=90n
.ends SCM_NMOS

.subckt CMC_PMOS_S  D1 D2 G S
M0 (D1 G S 0) PMOS_VTL w=w l=90n
M1 (D2 G S 0) PMOS_VTL w=w l=90n
.ends CMC_PMOS

.subckt DP_NMOS  D1 D2 G1 G2 S
M0 (D1 G1 S 0) NMOS_VTL w=w l=90n
M1 (D2 G2 S 0) NMOS_VTL w=w l=90n
.ends DP_NMOS

.subckt CMC_PMOS D1 D2 S1 S2 G
M0 (D1 G S1 0) PMOS_VTL w=w l=90n
M1 (D2 G S2 0) PMOS_VTL w=w l=90n
.ends CMC_PMOS

.subckt CMC_NMOS D1 D2 S1 S2 G
M0 (D1 G S1 0) NMOS_VTL w=w l=90n
M1 (D2 G S2 0) NMOS_VTL w=w l=90n
.ends CMC_NMOS

.subckt Cap PLUS MINUS
CC1 PLUS MINUS cap 60f
.ends Cap

.subckt DCL D S
M0 (D D S 0) NMOS_VTL w=w l=90n
.ends DiodeConnected_NMOS

.subckt DiodeConnected_PMOS D S
M0 (D D S 0) PMOS_VTL w=w l=90n
.ends DiodeConnected_PMOS

.subckt Res PLUS MINUS
RR1 PLUS MINUS res 10k
.ends Res
