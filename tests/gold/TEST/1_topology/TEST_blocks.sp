
.subckt CMC_NMOS_S_n12_X1_Y1 B DA G S DB
xM0 DA G S B Switch_NMOS_n12_X1_Y1
xM1 DB G S B Switch_NMOS_n12_X1_Y1
.ends CMC_NMOS_S_n12_X1_Y1

.subckt Switch_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Switch_NMOS_n12_X1_Y1

.subckt CMC_PMOS_S_n12_X1_Y1 B DA G S DB
xM0 DA G S B Switch_PMOS_n12_X1_Y1
xM1 DB G S B Switch_PMOS_n12_X1_Y1
.ends CMC_PMOS_S_n12_X1_Y1

.subckt Switch_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Switch_PMOS_n12_X1_Y1

.subckt LS_NMOS_n12_X1_Y1 B DA SA DB SB
xM0 DA DA SA B DCL_NMOS_n12_X1_Y1
xM1 DB DA SB B Switch_NMOS_n12_X1_Y1
.ends LS_NMOS_n12_X1_Y1

.subckt DCL_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends DCL_NMOS_n12_X1_Y1

.subckt LSB_NMOS_2 B DA SA DB SB DC SC
xM2 DC DA SC B Switch_NMOS_n12_X1_Y1
xM0_M1 DA SA DB SB B LS_NMOS_n12_X1_Y1
.ends LSB_NMOS_2

.subckt LS_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends LS_NMOS_n12_X1_Y1

.subckt LS_PMOS_n12_X1_Y1 B DA SA DB SB
xM0 DA SA SA B DCL_PMOS_n12_X1_Y1
xM1 DB DA SB B Switch_PMOS_n12_X1_Y1
.ends LS_PMOS_n12_X1_Y1

.subckt DCL_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends DCL_PMOS_n12_X1_Y1

.subckt LSB_PMOS_2 B DA SA DB SB DC SC
xM2 DC DA SC B Switch_PMOS_n12_X1_Y1
xM0_M1 DA SA DB SB B LS_PMOS_n12_X1_Y1
.ends LSB_PMOS_2

.subckt LS_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends LS_PMOS_n12_X1_Y1

.subckt DP_NMOS_n12_X1_Y1 B DA GA S DB GB
xM0 DA GA S B Switch_NMOS_n12_X1_Y1
xM1 DB GB S B Switch_NMOS_n12_X1_Y1
.ends DP_NMOS_n12_X1_Y1

.subckt TEST gnd vdd ibias vref vrefp
xxm72 net0211 gnd Dummy1_NMOS_n12_X1_Y1
xxm71 gnd gnd Dummy1_NMOS_n12_X1_Y1
xxm70 net0176 gnd Dummy1_NMOS_n12_X1_Y1
xxm69 net0211 gnd Dummy1_NMOS_n12_X1_Y1
xxm54 net0144 gnd Dummy1_NMOS_n12_X1_Y1
xxm51 net0111 gnd Dummy1_NMOS_n12_X1_Y1
xxm48 net0129 gnd Dummy1_NMOS_n12_X1_Y1
xxm43 net0109 gnd Dummy1_NMOS_n12_X1_Y1
xxm68 net0160 gnd Dummy1_NMOS_n12_X1_Y1
xxm62 net0147 gnd Dummy1_NMOS_n12_X1_Y1
xxm65 net0149 gnd Dummy1_NMOS_n12_X1_Y1
xxm58 net0103 gnd Dummy1_NMOS_n12_X1_Y1
xxm55 net0103 gnd Dummy1_NMOS_n12_X1_Y1
xxm57 net0111 gnd Dummy1_NMOS_n12_X1_Y1
xxm59 net0144 gnd Dummy1_NMOS_n12_X1_Y1
xxm61 net0149 gnd Dummy1_NMOS_n12_X1_Y1
xxm24 net0148 vdd gnd gnd Switch_NMOS_n12_X1_Y1
xxm67 net0211 vdd gnd gnd Switch_NMOS_n12_X1_Y1
xxm21 net0160 ibias net0211 gnd Switch_NMOS_n12_X1_Y1
xxm64 net0147 gnd Dummy1_NMOS_n12_X1_Y1
xxm30 net0176 ibias net0207 gnd Switch_NMOS_n12_X1_Y1
xxm14 net0140 gnd Dummy1_NMOS_n12_X1_Y1
xxm6 net017 vdd gnd gnd Switch_NMOS_n12_X1_Y1
xxm3 net016 vdd gnd gnd Switch_NMOS_n12_X1_Y1
xxm9 gnd gnd Dummy1_NMOS_n12_X1_Y1
xxm10 net016 gnd Dummy1_NMOS_n12_X1_Y1
xxm11 ibias gnd Dummy1_NMOS_n12_X1_Y1
xxm66 net0207 vdd gnd gnd Switch_NMOS_n12_X1_Y1
xxm13 net016 gnd Dummy1_NMOS_n12_X1_Y1
xxm12 net017 gnd Dummy1_NMOS_n12_X1_Y1
xxm35 vdd net0144 vdd Dcap_PMOS_n12_X1_Y1
xxm2 vfb vdd Dummy1_PMOS_n12_X1_Y1
xxm4 net0168 vdd Dummy1_PMOS_n12_X1_Y1
xxm5 vrefp vdd Dummy1_PMOS_n12_X1_Y1
xxm31 net0160 vdd Dummy1_PMOS_n12_X1_Y1
xxm28 vrefp net0176 net0168 vdd Switch_PMOS_n12_X1_Y1
xxm26 vfb vdd Dummy1_PMOS_n12_X1_Y1
xxm0 net0156 vdd Dummy1_PMOS_n12_X1_Y1
xxm34 vdd net0160 vdd Dcap_PMOS_n12_X1_Y1
xxm15 vfb net0144 net0156 vdd Switch_PMOS_n12_X1_Y1
xxm79 net0122 vdd Dummy1_PMOS_n12_X1_Y1
xxm75 vdd vdd Dummy1_PMOS_n12_X1_Y1
xxm49 net093 gnd vdd vdd Switch_PMOS_n12_X1_Y1
xxm85 net0133 vdd Dummy1_PMOS_n12_X1_Y1
xxm84 net0102 vdd Dummy1_PMOS_n12_X1_Y1
xxm83 net0134 vdd Dummy1_PMOS_n12_X1_Y1
xxm82 net0101 vdd Dummy1_PMOS_n12_X1_Y1
xxm81 net0129 vdd Dummy1_PMOS_n12_X1_Y1
xxm80 net0109 vdd Dummy1_PMOS_n12_X1_Y1
xxm73 net0140 vdd Dummy1_PMOS_n12_X1_Y1
xxm77 net0118 vdd Dummy1_PMOS_n12_X1_Y1
xxm78 net0118 vdd Dummy1_PMOS_n12_X1_Y1
xxm74 net093 vdd Dummy1_PMOS_n12_X1_Y1
xxm89 net0156 vdd Dummy1_PMOS_n12_X1_Y1
xxm88 vdd vdd Dummy1_PMOS_n12_X1_Y1
xxm86 net0168 gnd vdd vdd Switch_PMOS_n12_X1_Y1
xxm87 net0156 gnd vdd vdd Switch_PMOS_n12_X1_Y1
xxm76 net0122 vdd Dummy1_PMOS_n12_X1_Y1
xxm23_xm25 net0149 vdd gnd net0147 gnd CMC_NMOS_S_n12_X1_Y1
xxm60_xm52 net0134 gnd vdd net0101 vdd CMC_PMOS_S_n12_X1_Y1
xxm53_xm56 net0122 gnd vdd net0118 vdd CMC_PMOS_S_n12_X1_Y1
xm7_xm8_xm20 ibias net017 net0140 net016 net0111 net0148 gnd LSB_NMOS_2
xm45_xm47_xm46 net0140 net093 net0144 net0133 net0103 net0102 vdd LSB_PMOS_2
xxm1_xm22 net0103 net0149 net0144 net0147 gnd LS_NMOS_n12_X1_Y1
xxm41_xm40 net0109 net0118 net0102 net0101 vdd LS_PMOS_n12_X1_Y1
xxm44_xm42 net0129 net0122 net0133 net0134 vdd LS_PMOS_n12_X1_Y1
xxm27_xm29 net0160 vfb net0176 vrefp vdd LS_PMOS_n12_X1_Y1
xxm16_xm18 net0144 vref net0111 net0103 vfb gnd DP_NMOS_n12_X1_Y1
xxm19_xm17 net0129 vfb net0111 net0109 vref gnd DP_NMOS_n12_X1_Y1
.ends TEST

.subckt Dummy1_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Dummy1_NMOS_n12_X1_Y1

.subckt Dcap_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Dcap_PMOS_n12_X1_Y1

.subckt Dummy1_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Dummy1_PMOS_n12_X1_Y1

.subckt CMC_NMOS_S_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends CMC_NMOS_S_n12_X1_Y1

.subckt CMC_PMOS_S_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends CMC_PMOS_S_n12_X1_Y1

.subckt DP_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends DP_NMOS_n12_X1_Y1
