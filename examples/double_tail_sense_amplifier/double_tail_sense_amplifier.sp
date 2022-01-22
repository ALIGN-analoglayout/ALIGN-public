.subckt double_tail_sense_amplifier CLK CLK_B DIN DIP VDD VIN VIP VON VOP VSS
MTAIL_P_1 REGEN_SOURCE CLK_B VDD VDD pmos_rvt w=200e-9 l=60e-9  nf=12
MTAIL_P_2 REGEN_SOURCE CLK_B VDD VDD pmos_rvt w=200e-9 l=60e-9  nf=12
MINV_P_P VOP VON REGEN_SOURCE VDD pmos_rvt w=200e-9 l=60e-9  nf=12
MINV_P_N VON VOP REGEN_SOURCE VDD pmos_rvt w=200e-9 l=60e-9  nf=12
MLOAD_P DIN CLK VDD VDD pmos_rvt w=200e-9 l=60e-9  nf=16
MLOAD_N DIP CLK VDD VDD pmos_rvt w=200e-9 l=60e-9  nf=16
MRESET_P VOP DIN VSS VSS nmos_rvt w=200e-9 l=60e-9  nf=8
MRESET_N VON DIP VSS VSS nmos_rvt w=200e-9 l=60e-9  nf=8
MINV_N_P VOP VON VSS VSS nmos_rvt w=200e-9 l=60e-9  nf=8
MINV_N_N VON VOP VSS VSS nmos_rvt w=200e-9 l=60e-9  nf=8
MIN_P DIN VIP PRE_AMP_SOURCE VSS nmos_rvt w=200e-9 l=60e-9  nf=12
MIN_N DIP VIN PRE_AMP_SOURCE VSS nmos_rvt w=200e-9 l=60e-9  nf=12
MTAIL_2 PRE_AMP_SOURCE CLK VSS VSS nmos_rvt w=200e-9 l=60e-9  nf=8
MTAIL_1 PRE_AMP_SOURCE CLK VSS VSS nmos_rvt w=200e-9 l=60e-9  nf=8
.ends double_tail_sense_amplifier
