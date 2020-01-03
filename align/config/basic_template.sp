.subckt Switch_NMOS  D G S
M0 (D G S B) NMOS w=w1 l=l1
.ends Switch_NMOS

.subckt Switch_PMOS  D G S
M0 (D G S B) PMOS w=w1 l=l1
.ends Switch_PMOS

.subckt SCM_NMOS DA DB S
M0 (DA DA S B) NMOS w=w l=90n
M1 (DB DA S B) NMOS w=w l=90n
.ends SCM_NMOS

.subckt SCM_PMOS DA DB S
M0 (DA DA S B) PMOS w=w l=90n
M1 (DB DA S B) PMOS w=w l=90n
.ends SCM_PMOS

.subckt CMFB_NMOS DA DB GB S
M0 (DA DA S B) NMOS w=w l=90n
M1 (DB GB S B) NMOS w=w l=90n
.ends CMFB_NMOS

.subckt CMFB_PMOS DA DB GB S
M0 (DA DA S B) PMOS w=w l=90n
M1 (DB GB S B) PMOS w=w l=90n
.ends CMFB_PMOS

.subckt CASCODED_CMC_PMOS DA GA DB S
M0 DA GA SA B PMOS w=27e-9 l=20e-9 nfin=120
M1 DB GA SB B PMOS w=27e-9 l=20e-9 nfin=60
M2 SA DB S B PMOS w=27e-9 l=20e-9 nfin=10
M3 SB DB S B PMOS w=27e-9 l=20e-9 nfin=5
.ends CASCODED_CMC_PMOS

.subckt CASCODED_CMC_NMOS DA S DB GA
M0 DA GA SA B NMOS w=27e-9 l=20e-9 nfin=24
M1 DB GA SB B NMOS w=27e-9 l=20e-9 nfin=24
M2 SA DA S B NMOS w=27e-9 l=20e-9 nfin=30
M3 SB DA S B NMOS w=27e-9 l=20e-9 nfin=30
.ends CASCODED_CMC_NMOS

.subckt CMC_NMOS_S  DA DB G S
M0 (DA G S B) NMOS w=w l=90n
M1 (DB G S B) NMOS w=w l=90n
.ends CMC_NMOS_S

.subckt CMC_PMOS_S  DA DB G S
M0 (DA G S B) PMOS w=w l=90n
M1 (DB G S B) PMOS w=w l=90n
.ends CMC_PMOS_S

.subckt DP_NMOS  DA DB GA GB S
M0 (DA GA S B) NMOS w=w l=90n
M1 (DB GB S B) NMOS w=w l=90n
.ends DP_NMOS

.subckt DP_PMOS  DA DB GA GB S
M0 (DA GA S B) PMOS w=w l=90n
M1 (DB GB S B) PMOS w=w l=90n
.ends DP_PMOS

.subckt CMC_PMOS DA DB SA SB G
M0 (DA G SA B) PMOS w=w l=90n
M1 (DB G SB B) PMOS w=w l=90n
.ends CMC_PMOS

.subckt CCP_NMOS DA DB SA SB
M0 (DA DB SA B) NMOS w=w l=90n
M1 (DB DA SB B) NMOS w=w l=90n
.ends CCP_NMOS

.subckt CCP_PMOS DA DB SA SB
M0 (DA DB SA B) PMOS w=w l=90n
M1 (DB DA SB B) PMOS w=w l=90n
.ends CCP_PMOS

.subckt CCP_NMOS_S DA DB S
M0 (DA DB S B) NMOS w=w l=90n
M1 (DB DA S B) NMOS w=w l=90n
.ends CCP_NMOS_S

.subckt CCP_PMOS_S DA DB S
M0 (DA DB S B) PMOS w=w l=90n
M1 (DB DA S B) PMOS w=w l=90n
.ends CCP_PMOS_S

.subckt LS_NMOS DA DB SA SB
M0 (DA DA SA B) NMOS w=w l=90n
M1 (DB DA SB B) NMOS w=w l=90n
.ends LS_NMOS

.subckt LS_PMOS DA DB SA SB
M0 (DA DA SA B) PMOS w=w l=90n
M1 (DB DA SB B) PMOS w=w l=90n
.ends LS_PMOS

.subckt CMC_NMOS DA DB SA SB G
M0 (DA G SA B) NMOS w=w l=90n
M1 (DB G SB B) NMOS w=w l=90n
.ends CMC_NMOS

.subckt Cap_b PLUS MINUS BULK
CC1 PLUS MINUS BULK cap cap=60f
.ends Cap_b

.subckt Cap PLUS MINUS
CC1 PLUS MINUS cap cap=60f
.ends Cap

.subckt DCL_NMOS D S
M0 (D D S B) NMOS w=w l=90n
.ends DCL_NMOS

.subckt DCL_PMOS D S
M0 (D D S B) PMOS w=w l=90n
.ends DCL_PMOS

.subckt Dummy_NMOS D S
M0 (D S S B) NMOS w=w l=90n
.ends Dummy_NMOS

.subckt Dummy_PMOS D S
M0 (D S S B) PMOS w=w l=90n
.ends Dummy_PMOS

.subckt Dcap_NMOS G S
M0 (S G S B) NMOS w=w l=90n
.ends Dcap_NMOS

.subckt Dcap_PMOS G S
M0 (S G S B) PMOS w=w l=90n
.ends Dcap_PMOS

.subckt Dcap1_NMOS S
M0 (S S S B) NMOS w=w l=90n
.ends Dcap1_NMOS

.subckt Dcap1_PMOS S
M0 (S S S B) PMOS w=w l=90n
.ends Dcap1_PMOS

.subckt Res PLUS MINUS
RR1 PLUS MINUS res res=10k
.ends Res


.subckt spiral_ind PLUS MINUS BULK CTAP
L0 PLUS MINUS BULK CTAP spiral_sym_ct_mu_z w=9u
.ends spiral_ind

.subckt stage2_inv G1 G2 SN SP
MM0 G1 D SN SN NMOS l=60n w=1u m=1
MM1 D G2 SN SN NMOS l=60n w=1u m=1
MM2 G1 D SP SP PMOS l=60n w=1u m=1
MM3 D G2 SP SP PMOS l=60n w=1u m=1
.ends stage2_inv


