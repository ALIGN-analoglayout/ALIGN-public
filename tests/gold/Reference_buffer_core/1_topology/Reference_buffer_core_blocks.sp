
.subckt LS_NMOS_n12_X1_Y1 B DA SA DB SB
xM0 DA DA SA B DCL_NMOS_n12_X1_Y1
xM1 DB DA SB B Switch_NMOS_n12_X1_Y1
.ends LS_NMOS_n12_X1_Y1

.subckt DCL_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends DCL_NMOS_n12_X1_Y1

.subckt Switch_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Switch_NMOS_n12_X1_Y1

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

.subckt Switch_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Switch_PMOS_n12_X1_Y1

.subckt Reference_buffer_core gnd vbiasp vdd vbiasp2 vbias vref vref_in
xxm97 net017 gnd Dummy1_NMOS_n12_X1_Y1
xxm104 vbiasp gnd net034 gnd Switch_NMOS_n12_X1_Y1
xxm103 gnd gnd Dummy1_NMOS_n12_X1_Y1
xxm102 net036 gnd Dummy1_NMOS_n12_X1_Y1
xxm100 net017 gnd Dummy1_NMOS_n12_X1_Y1
xxm62 net034 vdd gnd gnd Switch_NMOS_n12_X1_Y1
xxm98 net034 gnd Dummy1_NMOS_n12_X1_Y1
xxm19 net017 vdd gnd gnd Switch_NMOS_n12_X1_Y1
xxm17 net036 vdd gnd gnd Switch_NMOS_n12_X1_Y1
xxm115 net022 vdd vdd Dummy_PMOS_n12_X1_Y1
xxm114 net029 vdd Dummy1_PMOS_n12_X1_Y1
xxm113 vref vdd Dummy1_PMOS_n12_X1_Y1
xxm117 net061 vdd vdd vdd DCL_PMOS_n12_X1_Y1
xxm112 net061 vdd Dummy1_PMOS_n12_X1_Y1
xxm108 vdd vdd Dummy1_PMOS_n12_X1_Y1
xxm110 net022 vdd vdd Dummy_PMOS_n12_X1_Y1
xxm111 vdd vdd Dummy1_PMOS_n12_X1_Y1
xxm107 vdd vdd Dummy1_PMOS_n12_X1_Y1
xxm18 net022 gnd vdd vdd Switch_PMOS_n12_X1_Y1
xxm16 net029 gnd vdd vdd Switch_PMOS_n12_X1_Y1
xxm118 vdd vbiasp vdd Dcap_PMOS_n12_X1_Y1
xxm99 net061 net018 net022 vdd Switch_PMOS_n12_X1_Y1
xxm105 vdd net061 vdd Dcap_PMOS_n12_X1_Y1
xxm9 vref vbiasp2 net029 vdd Switch_PMOS_n12_X1_Y1
xxm116 vbiasp vdd vdd vdd DCL_PMOS_n12_X1_Y1
xi12 gnd vbias vdd net061 net018 vref_in Reference_OTA
xm66_xm64_xm7 vbias net034 vbiasp2 net036 vbiasp net017 gnd LSB_NMOS_2
xxm77_xm0 vbiasp net061 vbiasp2 vref vdd LS_PMOS_n12_X1_Y1
.ends Reference_buffer_core

.subckt Dummy1_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Dummy1_NMOS_n12_X1_Y1

.subckt Dummy_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Dummy_PMOS_n12_X1_Y1

.subckt Dummy1_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Dummy1_PMOS_n12_X1_Y1

.subckt Dcap_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Dcap_PMOS_n12_X1_Y1

.subckt LS_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends LS_PMOS_n12_X1_Y1

.subckt SCM_PMOS_n12_X1_Y1 B DA S DB
xM0 DA S S B DCL_PMOS_n12_X1_Y1
xM1 DB DA S B Switch_PMOS_n12_X1_Y1
.ends SCM_PMOS_n12_X1_Y1

.subckt DP_NMOS_n12_X1_Y1 B DA GA S DB GB
xM0 DA GA S B Switch_NMOS_n12_X1_Y1
xM1 DB GB S B Switch_NMOS_n12_X1_Y1
.ends DP_NMOS_n12_X1_Y1

.subckt Reference_OTA vbias vmir vout vref_in
xxm2 vdd vdd Dummy1_PMOS_n12_X1_Y1
xxm9 net012 gnd Dummy1_NMOS_n12_X1_Y1
xxm8 net7 gnd Dummy1_NMOS_n12_X1_Y1
xxm7 net7 vbias net012 gnd Switch_NMOS_n12_X1_Y1
xxm62 net012 vdd gnd gnd Switch_NMOS_n12_X1_Y1
xxm5_xm0 net8 vdd vout vdd SCM_PMOS_n12_X1_Y1
xxm4_xm1 vout vref_in net7 net8 vmir gnd DP_NMOS_n12_X1_Y1
.ends Reference_OTA

.subckt SCM_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends SCM_PMOS_n12_X1_Y1

.subckt DP_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends DP_NMOS_n12_X1_Y1
