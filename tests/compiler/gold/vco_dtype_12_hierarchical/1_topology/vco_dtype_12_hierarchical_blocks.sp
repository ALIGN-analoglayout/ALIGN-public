
.subckt vco_dtype_12_hierarchical VSS VDD on<1> op<1> oo<1> on<2> op<2> oo<2> on<3> op<3> oo<3> on<4> op<4> oo<4> on<5> op<5> oo<5> on<6> op<6> oo<6> on<7> op<7> oo<7> on<8> op<8> oo<8> vbias
I6<1> VSS VDD VSS on<1> op<1> oo<1> diff2sing_v1
I6<2> VSS VDD VSS on<2> op<2> oo<2> diff2sing_v1
I6<3> VSS VDD VSS on<3> op<3> oo<3> diff2sing_v1
I6<4> VSS VDD VSS on<4> op<4> oo<4> diff2sing_v1
I6<5> VSS VDD VSS on<5> op<5> oo<5> diff2sing_v1
I6<6> VSS VDD VSS on<6> op<6> oo<6> diff2sing_v1
I6<7> VSS VDD VSS on<7> op<7> oo<7> diff2sing_v1
I6<8> VSS VDD VSS on<8> op<8> oo<8> diff2sing_v1
I1 VDD VSS op<1> op<2> op<3> op<4> op<5> op<6> op<7> op<8> on<1> vbias VCO_type2_65
I0 VDD VSS on<1> on<2> on<3> on<4> on<5> on<6> on<7> on<8> op<1> vbias VCO_type2_65
.ends vco_dtype_12_hierarchical

.subckt SCM_NMOS_n8_X5_Y1 B DA S DB
xM0 DA DA S B DCL_NMOS_n8_X5_Y1
xM1 DB DA S B Switch_NMOS_n8_X5_Y1
.ends SCM_NMOS_n8_X5_Y1

.subckt DCL_NMOS_n8_X5_Y1 D G S B
m0 D G S1 B nmos_rvt  m=1 l=2.8000000000000003e-08 nfin=4 nf=10
m1 S1 G S B nmos_rvt  m=1 l=2.8000000000000003e-08 nfin=4 nf=10
.ends DCL_NMOS_n8_X5_Y1

.subckt Switch_NMOS_n8_X5_Y1 D G S B
m0 D G S1 B nmos_rvt  m=1 l=2.8000000000000003e-08 nfin=4 nf=10
m1 S1 G S B nmos_rvt  m=1 l=2.8000000000000003e-08 nfin=4 nf=10
.ends Switch_NMOS_n8_X5_Y1

.subckt DP_PMOS_n12_X4_Y2 B DA GA S DB GB
xM0 DA GA S B Switch_PMOS_n12_X4_Y2
xM1 DB GB S B Switch_PMOS_n12_X4_Y2
.ends DP_PMOS_n12_X4_Y2

.subckt Switch_PMOS_n12_X4_Y2 D G S B
m0 D G S1 B nmos_rvt  m=1 l=2.8000000000000003e-08 nfin=6 nf=15
m1 S1 G S B nmos_rvt  m=1 l=2.8000000000000003e-08 nfin=6 nf=15
.ends Switch_PMOS_n12_X4_Y2

.subckt diff2sing_v1 B in1 in2 o
xP2 net3 B VDD VDD Switch_PMOS_n12_X4_Y2
xN1_N0 net8 VSS o VSS SCM_NMOS_n8_X5_Y1
xP1_P0 o in2 net3 net8 in1 VDD DP_PMOS_n12_X4_Y2
.ends diff2sing_v1

.subckt SCM_NMOS_n8_X5_Y1 D G S B
m0 D G S1 B nmos_rvt  m=1 l=2.8000000000000003e-08 nfin=4 nf=10
m1 S1 G S B nmos_rvt  m=1 l=2.8000000000000003e-08 nfin=4 nf=10
.ends SCM_NMOS_n8_X5_Y1

.subckt DP_PMOS_n12_X4_Y2 D G S B
m0 D G S1 B nmos_rvt  m=1 l=2.8000000000000003e-08 nfin=6 nf=15
m1 S1 G S B nmos_rvt  m=1 l=2.8000000000000003e-08 nfin=6 nf=15
.ends DP_PMOS_n12_X4_Y2

.subckt VCO_type2_65 o<1> o<2> o<3> o<4> o<5> o<6> o<7> o<8> op<1> VBIAS
I1<1> VDD VSS VBIAS o<1> o<2> three_terminal_inv
I1<2> VDD VSS VBIAS o<2> o<3> three_terminal_inv
I1<3> VDD VSS VBIAS o<3> o<4> three_terminal_inv
I1<4> VDD VSS VBIAS o<4> o<5> three_terminal_inv
I1<5> VDD VSS VBIAS o<5> o<6> three_terminal_inv
I1<6> VDD VSS VBIAS o<6> o<7> three_terminal_inv
I1<7> VDD VSS VBIAS o<7> o<8> three_terminal_inv
I1<8> VDD VSS VBIAS o<8> op<1> three_terminal_inv
.ends VCO_type2_65

.subckt three_terminal_inv VBIAS VIN VOUT
xN34 VOUT VIN VSS VSS Switch_NMOS_n8_X13_Y1
xP34 VOUT VBIAS VDD VDD Switch_PMOS_n12_X2_Y1
.ends three_terminal_inv

.subckt Switch_NMOS_n8_X13_Y1 D G S B
m0 D G S1 B nmos_rvt  m=1 l=2.8000000000000003e-08 nfin=4 nf=25
m1 S1 G S B nmos_rvt  m=1 l=2.8000000000000003e-08 nfin=4 nf=25
.ends Switch_NMOS_n8_X13_Y1

.subckt Switch_PMOS_n12_X2_Y1 D G S B
m0 D G S1 B nmos_rvt  m=1 l=2.8000000000000003e-08 nfin=6 nf=4
m1 S1 G S B nmos_rvt  m=1 l=2.8000000000000003e-08 nfin=6 nf=4
.ends Switch_PMOS_n12_X2_Y1
