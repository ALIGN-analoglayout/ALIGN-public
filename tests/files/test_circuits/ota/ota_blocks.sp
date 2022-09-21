
.subckt SCM_NMOS_nfin50_n12_X5_Y1_RVT B DA S DB
M0 DA DA S B DCL_NMOS
M1 DB DA S B Switch_NMOS
.ends SCM_NMOS_nfin50_n12_X5_Y1_RVT

.subckt CMC_PMOS_S_nfin10_n12_X1_Y1_RVT DA G S DB
M0 DA G S vdd Switch_PMOS
M1 DB G S vdd Switch_PMOS
.ends CMC_PMOS_S_nfin10_n12_X1_Y1_RVT

.subckt x_dp_mn1_mn2_NMOS_nfin75_n12_X7_Y1_RVT DA GA S DB GB
M0 DA GA S B Switch_NMOS
M1 DB GB S B Switch_NMOS
.ends x_dp_mn1_mn2_NMOS_nfin75_n12_X7_Y1_RVT

.subckt CMC_PMOS_nfin15_n12_X2_Y1_RVT DA G SA DB SB
M0 DA G SA B Switch_PMOS
M1 DB G SB B Switch_PMOS
.ends CMC_PMOS_nfin15_n12_X2_Y1_RVT

.subckt CMC_NMOS_nfin25_n12_X3_Y1_RVT DA G SA DB SB
M0 DA G SA B Switch_NMOS
M1 DB G SB B Switch_NMOS
.ends CMC_NMOS_nfin25_n12_X3_Y1_RVT
