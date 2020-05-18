
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

.subckt BUFFER_VREFP_FINAL2 vrefp vdd gnd sw<2> ibias sw<1> sw<0> vref
xxm58 vrefp net459 net0129 vdd Switch_PMOS_n12_X1_Y1
xxm15 vfb net450 net0115 vdd Switch_PMOS_n12_X1_Y1
xxm28 vrefp net459 net0127 vdd Switch_PMOS_n12_X1_Y1
xxm106 vdd net431 vdd Dcap_PMOS_n12_X1_Y1
xxm33 vrefp net459 net0113 vdd Switch_PMOS_n12_X1_Y1
xxm34 vrefp net459 net0135 vdd Switch_PMOS_n12_X1_Y1
xxm35 net0134 net431 vrefp vdd Switch_PMOS_n12_X1_Y1
xxm55 net468 swn2 gnd gnd Switch_NMOS_n12_X1_Y1
xxm20 net469 swn1 gnd gnd Switch_NMOS_n12_X1_Y1
xxm19 net470 swn0 gnd gnd Switch_NMOS_n12_X1_Y1
xxm18 net463 vdd gnd gnd Switch_NMOS_n12_X1_Y1
xxm17 net427 vdd gnd gnd Switch_NMOS_n12_X1_Y1
xxm9 net466 vdd gnd gnd Switch_NMOS_n12_X1_Y1
xxm2 net465 vdd gnd gnd Switch_NMOS_n12_X1_Y1
xxm0 net464 vdd gnd gnd Switch_NMOS_n12_X1_Y1
xxm3 net418 ibias net466 gnd Switch_NMOS_n12_X1_Y1
xxm5 net411 ibias net465 gnd Switch_NMOS_n12_X1_Y1
xxm21 net431 ibias net427 net427 Switch_NMOS_n12_X1_Y1
xxm30 net459 ibias net463 gnd Switch_NMOS_n12_X1_Y1
xxm36 net0134 ibias net469 gnd Switch_NMOS_n12_X1_Y1
xxm46 net0135 swp1 vdd vdd Switch_PMOS_n12_X1_Y1
xxm45 net0113 swp0 vdd vdd Switch_PMOS_n12_X1_Y1
xxm44 net0127 gnd vdd vdd Switch_PMOS_n12_X1_Y1
xxm56 net0129 swp2 vdd vdd Switch_PMOS_n12_X1_Y1
xxm42 net0115 gnd vdd vdd Switch_PMOS_n12_X1_Y1
xxm37 net0121 gnd vdd vdd Switch_PMOS_n12_X1_Y1
xm50_xm48_xm49_xm47 gnd sw<0> vdd swn0 stage2_inv
xm54_xm51_xm53_xm52 gnd sw<1> vdd swn1 stage2_inv
xm62_xm59_xm61_xm60 gnd sw<2> vdd swn2 stage2_inv
xxm7_xm16 net467 vdd gnd net462 gnd CMC_NMOS_S_n12_X1_Y1
xxm40_xm39 net0119 gnd vdd net0114 vdd CMC_PMOS_S_n12_X1_Y1
xxm38_xm41 net0128 gnd vdd net0124 vdd CMC_PMOS_S_n12_X1_Y1
xxm29_xm32 net459 net431 vrefp net0132 vdd CMC_PMOS_S_n12_X1_Y1
xm4_xm31_xm57 ibias net464 net0132 net470 net0125 net468 gnd LSB_NMOS_2
xm22_xm13_xm14 net411 net0121 net450 net0137 net412 net0122 vdd LSB_PMOS_2
xxm1_xm6 net412 net467 net450 net462 gnd LS_NMOS_n12_X1_Y1
xxm23_xm24 net423 net0114 net0137 net0124 vdd LS_PMOS_n12_X1_Y1
xxm25_xm26 net417 net0119 net0122 net0128 vdd LS_PMOS_n12_X1_Y1
xxm27_xm43 net431 vfb net0125 vrefp vdd LS_PMOS_n12_X1_Y1
xxm12_xm10 net450 vref net418 net412 vfb gnd DP_NMOS_n12_X1_Y1
xxm8_xm11 net423 vfb net418 net417 vref gnd DP_NMOS_n12_X1_Y1
.ends BUFFER_VREFP_FINAL2

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
