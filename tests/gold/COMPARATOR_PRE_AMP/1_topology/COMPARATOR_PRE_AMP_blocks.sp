
.subckt CCP_PMOS_S_n12_X1_Y1 B DA DB S
xM0 DA DB S B Switch_PMOS_n12_X1_Y1
xM1 DB DA S B Switch_PMOS_n12_X1_Y1
.ends CCP_PMOS_S_n12_X1_Y1

.subckt Switch_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Switch_PMOS_n12_X1_Y1

.subckt CMC_PMOS_S_n12_X1_Y1 B DA G S DB
xM0 DA G S B Switch_PMOS_n12_X1_Y1
xM1 DB G S B Switch_PMOS_n12_X1_Y1
.ends CMC_PMOS_S_n12_X1_Y1

.subckt CCP_NMOS_n12_X1_Y1 B DA DB SA SB
xM0 DA DB SA B Switch_NMOS_n12_X1_Y1
xM1 DB DA SB B Switch_NMOS_n12_X1_Y1
.ends CCP_NMOS_n12_X1_Y1

.subckt Switch_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Switch_NMOS_n12_X1_Y1

.subckt INV_LVT zn i SN SP
xxm0 zn i SN SN Switch_NMOS_n12_X1_Y1
xxm1 zn i SP SP Switch_PMOS_n12_X1_Y1
.ends INV_LVT

.subckt DP_NMOS_n12_X1_Y1 B DA GA S DB GB
xM0 DA GA S B Switch_NMOS_n12_X1_Y1
xM1 DB GB S B Switch_NMOS_n12_X1_Y1
.ends DP_NMOS_n12_X1_Y1

.subckt COMPARATOR_PRE_AMP gnd intern interp outm crossp outp crossn clk _net0 _net1 vdd
xxm0 gnd intern gnd Dcap_NMOS_n12_X1_Y1
xxm22 gnd interp gnd Dcap_NMOS_n12_X1_Y1
xxm7 net050 clk gnd gnd Switch_NMOS_n12_X1_Y1
xxm13_xm14 crossp crossn vdd vdd CCP_PMOS_S_n12_X1_Y1
xxm12_xm10 crossp clk vdd crossn vdd CMC_PMOS_S_n12_X1_Y1
xxm19_xm18 interp clk vdd intern vdd CMC_PMOS_S_n12_X1_Y1
xxm3_xm4 crossp crossn interp intern gnd CCP_NMOS_n12_X1_Y1
xm17_xm15 crossn gnd vdd outp INV_LVT
xm16_xm8 crossp gnd vdd outm INV_LVT
xxm6_xm5 interp _net1 net050 intern _net0 gnd DP_NMOS_n12_X1_Y1
.ends COMPARATOR_PRE_AMP

.subckt Dcap_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Dcap_NMOS_n12_X1_Y1

.subckt CCP_PMOS_S_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends CCP_PMOS_S_n12_X1_Y1

.subckt CMC_PMOS_S_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends CMC_PMOS_S_n12_X1_Y1

.subckt CCP_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends CCP_NMOS_n12_X1_Y1

.subckt DP_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends DP_NMOS_n12_X1_Y1
