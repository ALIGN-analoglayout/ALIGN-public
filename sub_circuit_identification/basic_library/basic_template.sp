.subckt Switch_NMOS  D G S
M0 (D G S 0) NMOS_VTL w=w1 l=l1
.ends Switch_NMOS

.subckt Switch_PMOS  D G S
M0 (D G S 0) PMOS_VTL w=w1 l=l1
.ends Switch_PMOS

.subckt SCM_NMOS D0 DA S
M0 (D0 D0 S 0) NMOS_VTL w=w l=90n
M1 (DA D0 S 0) NMOS_VTL w=w l=90n
.ends SCM_NMOS

.subckt CMC_PMOS_S  DA DB G S
M0 (DA G S 0) PMOS_VTL w=w l=90n
M1 (DB G S 0) PMOS_VTL w=w l=90n
.ends CMC_PMOS

.subckt DP_NMOS  DA DB GA GB S
M0 (DA GA S 0) NMOS_VTL w=w l=90n
M1 (DB GB S 0) NMOS_VTL w=w l=90n
.ends DP_NMOS

.subckt CMC_PMOS DA DB SA SB G
M0 (DA G SA 0) PMOS_VTL w=w l=90n
M1 (DB G SB 0) PMOS_VTL w=w l=90n
.ends CMC_PMOS

.subckt CMC_NMOS DA DB SA SB G
M0 (DA G SA 0) NMOS_VTL w=w l=90n
M1 (DB G SB 0) NMOS_VTL w=w l=90n
.ends CMC_NMOS

.subckt Cap PLUS MINUS BULK
CC1 PLUS MINUS BULK cap cap=60f
.ends Cap

.subckt DCL_NMOS D S
M0 (D D S 0) NMOS_VTL w=w l=90n
.ends DCL_NMOS

.subckt DCL_PMOS D S
M0 (D D S 0) PMOS_VTL w=w l=90n
.ends DCL_PMOS

.subckt Res PLUS MINUS
RR1 PLUS MINUS res res=10k
.ends Res

.subckt spiral_ind PLUS MINUS BULK CTAP
L0 PLUS MINUS BULK CTAP spiral_sym_ct_mu_z w=9u
.ends spiral_ind
