.model NMOS_VTL NMOS
.model PMOS_VTL PMOS

.subckt CMC_PMOS_VTL_S_n12_X1_Y1 DA G S DB
M0 DA G S vdd PMOS_VTL  w=2.7e-07 l=2e-08 nfin=10
M1 DB G S vdd PMOS_VTL  w=2.7e-07 l=2e-08 nfin=10
.ends CMC_PMOS_VTL_S_n12_X1_Y1

.subckt DP_NMOS_VTL_n12_X7_Y1 DA GA S DB GB
M0 DA GA S vss NMOS_VTL  w=2.7e-07 l=2e-08 nfin=75
M1 DB GB S vss NMOS_VTL  w=2.7e-07 l=2e-08 nfin=75
.ends DP_NMOS_VTL_n12_X7_Y1

.subckt CMC_PMOS_VTL_n12_X2_Y1 DA G SA DB SB
M0 DA G SA vdd PMOS_VTL  w=2.7e-07 l=2e-08 nfin=15
M1 DB G SB vdd PMOS_VTL  w=2.7e-07 l=2e-08 nfin=15
.ends CMC_PMOS_VTL_n12_X2_Y1

.subckt CMC_NMOS_VTL_n12_X3_Y1 DA G SA DB SB
M0 DA G SA vss NMOS_VTL  w=2.7e-07 l=2e-08 nfin=25
M1 DB G SB vss NMOS_VTL  w=2.7e-07 l=2e-08 nfin=25
.ends CMC_NMOS_VTL_n12_X3_Y1
