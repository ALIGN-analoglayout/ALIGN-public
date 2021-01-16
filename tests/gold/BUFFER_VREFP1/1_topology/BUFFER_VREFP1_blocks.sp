
.subckt INV_LVT zn i SN SP
xxm0 zn i SN SN Switch_NMOS_n12_X1_Y1
xxm1 zn i SP SP Switch_PMOS_n12_X1_Y1
.ends INV_LVT

.subckt Switch_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Switch_NMOS_n12_X1_Y1

.subckt Switch_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Switch_PMOS_n12_X1_Y1

.subckt stage2_inv G1 SN G2 SP
MM0_MM2 D SN SP G1 INV_LVT
MM1_MM3 G2 SN SP D INV_LVT
.ends stage2_inv

.subckt CMC_NMOS_S_n12_X1_Y1 B DA G S DB
xM0 DA G S B Switch_NMOS_n12_X1_Y1
xM1 DB G S B Switch_NMOS_n12_X1_Y1
.ends CMC_NMOS_S_n12_X1_Y1

.subckt CMC_PMOS_S_n12_X1_Y1 B DA G S DB
xM0 DA G S B Switch_PMOS_n12_X1_Y1
xM1 DB G S B Switch_PMOS_n12_X1_Y1
.ends CMC_PMOS_S_n12_X1_Y1

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

.subckt CMC_NMOS_n12_X1_Y1 B DA G SA DB SB
xM0 DA G SA B Switch_NMOS_n12_X1_Y1
xM1 DB G SB B Switch_NMOS_n12_X1_Y1
.ends CMC_NMOS_n12_X1_Y1

.subckt BUFFER_VREFP1 vrefp vdd ibias vref gnd sw<0> sw<1> sw<2>
xxm34 vrefp net459 net0121 vdd Switch_PMOS_n12_X1_Y1
xxm33 vrefp net459 net0140 vdd Switch_PMOS_n12_X1_Y1
xxm106 vdd net078 vdd Dcap_PMOS_n12_X1_Y1
xxm27 net078 vfb vfb vdd DCL_PMOS_n12_X1_Y1
xxm28 vrefp net459 net0127 vdd Switch_PMOS_n12_X1_Y1
xxm15 vfb net450 net0138 vdd Switch_PMOS_n12_X1_Y1
xxm58 vrefp net459 net0125 vdd Switch_PMOS_n12_X1_Y1
xxm21 net078 ibias net426 net426 Switch_NMOS_n12_X1_Y1
xxm5 net410 ibias net468 gnd Switch_NMOS_n12_X1_Y1
xxm3 net417 ibias net467 gnd Switch_NMOS_n12_X1_Y1
xxm0 net469 vdd gnd gnd Switch_NMOS_n12_X1_Y1
xxm2 net468 vdd gnd gnd Switch_NMOS_n12_X1_Y1
xxm9 net467 vdd gnd gnd Switch_NMOS_n12_X1_Y1
xxm17 net426 vdd gnd gnd Switch_NMOS_n12_X1_Y1
xxm18 net470 vdd gnd gnd Switch_NMOS_n12_X1_Y1
xxm19 net463 swn0 gnd gnd Switch_NMOS_n12_X1_Y1
xxm20 net464 swn1 gnd gnd Switch_NMOS_n12_X1_Y1
xxm55 net465 swn2 gnd gnd Switch_NMOS_n12_X1_Y1
xxm37 net0132 gnd vdd vdd Switch_PMOS_n12_X1_Y1
xxm42 net0138 gnd vdd vdd Switch_PMOS_n12_X1_Y1
xxm56 net0125 swp2 vdd vdd Switch_PMOS_n12_X1_Y1
xxm44 net0127 gnd vdd vdd Switch_PMOS_n12_X1_Y1
xxm45 net0140 swp0 vdd vdd Switch_PMOS_n12_X1_Y1
xxm46 net0121 swp1 vdd vdd Switch_PMOS_n12_X1_Y1
xm50_xm48_xm49_xm47 gnd sw<0> vdd swn0 stage2_inv
xm54_xm51_xm53_xm52 gnd sw<1> vdd swn1 stage2_inv
xm62_xm59_xm61_xm60 gnd sw<2> vdd swn2 stage2_inv
xxm16_xm7 net471 vdd gnd net466 gnd CMC_NMOS_S_n12_X1_Y1
xxm41_xm38 net0130 gnd vdd net0126 vdd CMC_PMOS_S_n12_X1_Y1
xxm39_xm40 net0139 gnd vdd net0134 vdd CMC_PMOS_S_n12_X1_Y1
xxm43_xm35 net0135 net078 vrefp net0116 vdd CMC_PMOS_S_n12_X1_Y1
xxm29_xm32 net459 net078 vrefp net0118 vdd CMC_PMOS_S_n12_X1_Y1
xm4_xm31_xm36 ibias net469 net0118 net463 net0116 net464 gnd LSB_NMOS_2
xm22_xm13_xm14 net410 net0132 net450 net0129 net411 net0119 vdd LSB_PMOS_2
xxm1_xm6 net411 net466 net450 net471 gnd LS_NMOS_n12_X1_Y1
xxm25_xm26 net416 net0134 net0119 net0126 vdd LS_PMOS_n12_X1_Y1
xxm23_xm24 net422 net0139 net0129 net0130 vdd LS_PMOS_n12_X1_Y1
xxm12_xm10 net450 vref net417 net411 vfb gnd DP_NMOS_n12_X1_Y1
xxm8_xm11 net422 vfb net417 net416 vref gnd DP_NMOS_n12_X1_Y1
xxm30_xm57 net459 ibias net470 net0135 net465 gnd CMC_NMOS_n12_X1_Y1
.ends BUFFER_VREFP1

.subckt Dcap_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Dcap_PMOS_n12_X1_Y1

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

.subckt CMC_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends CMC_NMOS_n12_X1_Y1
