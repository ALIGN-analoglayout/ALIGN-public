
.subckt ADC_CORE gnd q<9> q<8> qb<7> qb<6> qb<5> qb<4> qb<3> qb<2> qb<1> vcm vdd vrefn vrefp qb<9> qb<8> q<7> q<6> q<5> q<4> q<3> q<2> q<1> clkc clksb q<0> qb<0> est_delay clks inp inn
xi1 gnd q<9> q<8> qb<7> qb<6> qb<5> qb<4> qb<3> qb<2> qb<1> vcm vdd vrefn vrefp SAMPLE_NETWORK
xi0 gnd qb<9> qb<8> q<7> q<6> q<5> q<4> q<3> q<2> q<1> vcm vdd vrefn vrefp SAMPLE_NETWORK
xi2 clkc net3 net4 gnd net1 net2 coutn coutp vdd cpinp cpinn COMPARATOR
xi3 clkc clksb gnd coutn coutp q<9> q<8> q<7> q<6> q<5> q<4> q<3> q<2> q<1> qb<9> qb<8> qb<7> qb<6> qb<5> qb<4> qb<3> qb<2> qb<1> vdd q<0> qb<0> est_delay est SAR_LOGIC
xi11 clks net05 inp cpinp SAMPLER
xi12 clks net06 inn cpinn SAMPLER
xi13 clksb est_delay estimator<1> estimator<0> gnd coutp vdd COUNTER
.ends ADC_CORE

.subckt SAMPLE_NETWORK in<9> in<8> in<7> in<6> in<5> in<4> in<3> in<2> in<1> vcm vrefn vrefp
xi2 dac<9> dac<8> dac<7> dac<6> dac<5> dac<4> dac<3> dac<2> dac<1> gnd in<9> in<8> in<7> in<6> in<5> in<4> in<3> in<2> in<1> vcm vdd vrefn vrefp DAC_SWITCHES
.ends SAMPLE_NETWORK

.subckt DAC_SWITCHES dac<9> dac<8> dac<7> dac<6> dac<5> dac<4> dac<3> dac<2> dac<1> in<9> in<8> in<7> in<6> in<5> in<4> in<3> in<2> in<1> vcm vrefn vrefp
xi5 in<5> dac<5> vrefp vrefn INV0_LVT
xi3 in<7> dac<7> vrefp vrefn INV0_LVT
xi4 in<6> dac<6> vrefp vrefn INV0_LVT
xi6 in<2> dac<2> vrefp vrefn INV0_LVT
xi7 in<3> dac<3> vrefp vrefn INV0_LVT
xi10 in<8> net07 vdd gnd INV0_LVT
xi9 in<1> dac<1> vrefp vcm INV0_LVT
xi8 in<4> dac<4> vrefp vrefn INV0_LVT
xi0 in<9> net91 vdd gnd INV0_LVT
xi1 net91 dac<9> vrefp vrefn INV0_LVT
xi2 net07 dac<8> vrefp vrefn INV0_LVT
.ends DAC_SWITCHES

.subckt INV0_LVT i zn VDD vss
xxm0 zn i vss vss Switch_NMOS_n12_X1_Y1
xxm1 zn i VDD VDD Switch_PMOS_n12_X1_Y1
.ends INV0_LVT

.subckt Switch_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Switch_NMOS_n12_X1_Y1

.subckt Switch_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Switch_PMOS_n12_X1_Y1

.subckt CCP_PMOS_S_n12_X1_Y1 B DA DB S
xM0 DA DB S B Switch_PMOS_n12_X1_Y1
xM1 DB DA S B Switch_PMOS_n12_X1_Y1
.ends CCP_PMOS_S_n12_X1_Y1

.subckt CMC_PMOS_S_n12_X1_Y1 B DA G S DB
xM0 DA G S B Switch_PMOS_n12_X1_Y1
xM1 DB G S B Switch_PMOS_n12_X1_Y1
.ends CMC_PMOS_S_n12_X1_Y1

.subckt CCP_NMOS_n12_X1_Y1 B DA DB SA SB
xM0 DA DB SA B Switch_NMOS_n12_X1_Y1
xM1 DB DA SB B Switch_NMOS_n12_X1_Y1
.ends CCP_NMOS_n12_X1_Y1

.subckt INV_LVT zn i SN SP
xxm0 zn i SN SN Switch_NMOS_n12_X1_Y1
xxm1 zn i SP SP Switch_PMOS_n12_X1_Y1
.ends INV_LVT

.subckt DP_NMOS_n12_X1_Y1 B DA GA S DB GB
xM0 DA GA S B Switch_NMOS_n12_X1_Y1
xM1 DB GB S B Switch_NMOS_n12_X1_Y1
.ends DP_NMOS_n12_X1_Y1

.subckt COMPARATOR clk crossn crossp intern interp outm outp _net1 _net0
xxm1 gnd interp gnd Dcap_NMOS_n12_X1_Y1
xxm0 gnd intern gnd Dcap_NMOS_n12_X1_Y1
xxm26 net050 clk gnd gnd Switch_NMOS_n12_X1_Y1
xxm13_xm14 crossp crossn vdd vdd CCP_PMOS_S_n12_X1_Y1
xxm12_xm10 crossp clk vdd crossn vdd CMC_PMOS_S_n12_X1_Y1
xxm19_xm18 interp clk vdd intern vdd CMC_PMOS_S_n12_X1_Y1
xxm3_xm4 crossp crossn interp intern gnd CCP_NMOS_n12_X1_Y1
xm17_xm15 crossn gnd vdd outp INV_LVT
xm16_xm8 crossp gnd vdd outm INV_LVT
xxm24_xm25 intern _net1 net050 interp _net0 gnd DP_NMOS_n12_X1_Y1
.ends COMPARATOR

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

.subckt SAR_LOGIC clk clksb outn outp q<9> q<8> q<7> q<6> q<5> q<4> q<3> q<2> q<1> qb<9> qb<8> qb<7> qb<6> qb<5> qb<4> qb<3> qb<2> qb<1> q<0> qb<0> s<0> sb<1>
xi1 outp outn gnd q<9> q<8> q<7> q<6> q<5> q<4> q<3> q<2> q<1> qb<9> qb<8> qb<7> qb<6> qb<5> qb<4> qb<3> qb<2> qb<1> s<10> s<9> s<8> s<7> s<6> s<5> s<4> s<3> s<2> s<1> vdd q<0> qb<0> SAR_LOGIC_2ND_STAGE
xi0 clk clksb gnd s<10> s<9> s<8> s<7> s<6> s<5> s<4> s<3> s<2> s<1> s<0> vdd sb<1> SAR_LOGIC_1ST_STAGE_CLKGATING
.ends SAR_LOGIC

.subckt SAR_LOGIC_2ND_STAGE comp compb q<9> q<8> q<7> q<6> q<5> q<4> q<3> q<2> q<1> qb<9> qb<8> qb<7> qb<6> qb<5> qb<4> qb<3> qb<2> qb<1> s<10> s<9> s<8> s<7> s<6> s<5> s<4> s<3> s<2> s<1> q<0> qb<0>
xi1<9> s<9> gnd compb comp net03<0> net04<0> vdd LATCH
xi1<8> s<8> gnd compb comp net03<1> net04<1> vdd LATCH
xi1<7> s<7> gnd compb comp net03<2> net04<2> vdd LATCH
xi1<6> s<6> gnd compb comp net03<3> net04<3> vdd LATCH
xi1<5> s<5> gnd compb comp net03<4> net04<4> vdd LATCH
xi1<4> s<4> gnd compb comp net03<5> net04<5> vdd LATCH
xi1<3> s<3> gnd compb comp net03<6> net04<6> vdd LATCH
xi1<2> s<2> gnd compb comp net03<7> net04<7> vdd LATCH
xi1<1> s<1> gnd compb comp net03<8> net04<8> vdd LATCH
xi0 s<10> gnd compb comp qb<9> q<9> vdd LATCH
xi2<9> net04<0> qb<8> vdd gnd INVD0BWP
xi2<8> net04<1> qb<7> vdd gnd INVD0BWP
xi2<7> net04<2> qb<6> vdd gnd INVD0BWP
xi2<6> net04<3> qb<5> vdd gnd INVD0BWP
xi2<5> net04<4> qb<4> vdd gnd INVD0BWP
xi2<4> net04<5> qb<3> vdd gnd INVD0BWP
xi2<3> net04<6> qb<2> vdd gnd INVD0BWP
xi2<2> net04<7> qb<1> vdd gnd INVD0BWP
xi2<1> net04<8> qb<0> vdd gnd INVD0BWP
xi3<9> net03<0> q<8> vdd gnd INVD0BWP
xi3<8> net03<1> q<7> vdd gnd INVD0BWP
xi3<7> net03<2> q<6> vdd gnd INVD0BWP
xi3<6> net03<3> q<5> vdd gnd INVD0BWP
xi3<5> net03<4> q<4> vdd gnd INVD0BWP
xi3<4> net03<5> q<3> vdd gnd INVD0BWP
xi3<3> net03<6> q<2> vdd gnd INVD0BWP
xi3<2> net03<7> q<1> vdd gnd INVD0BWP
xi3<1> net03<8> q<0> vdd gnd INVD0BWP
.ends SAR_LOGIC_2ND_STAGE

.subckt LATCH clk inm inp outm outp vcc
xi1 net67 outp vcc gnd INVD0BWP
xi0 net64 outm vcc gnd INVD0BWP
xxm10 net64 clk vcc vcc Switch_PMOS_n12_X1_Y1
xxm9 net67 clk vcc vcc Switch_PMOS_n12_X1_Y1
xxm13 net67 net64 vcc vcc Switch_PMOS_n12_X1_Y1
xxm4 net64 net67 vcc vcc Switch_PMOS_n12_X1_Y1
xxm8 net65 clk vcc vcc Switch_PMOS_n12_X1_Y1
xxm12 net012 clk vcc vcc Switch_PMOS_n12_X1_Y1
xxm11 net60 clk gnd gnd Switch_NMOS_n12_X1_Y1
xxm0 net65 inp net60 gnd Switch_NMOS_n12_X1_Y1
xxm2 net67 net64 net65 gnd Switch_NMOS_n12_X1_Y1
xxm3 net64 net67 net012 gnd Switch_NMOS_n12_X1_Y1
xxm1 net012 inm net60 gnd Switch_NMOS_n12_X1_Y1
.ends LATCH

.subckt INVD0BWP i zn vss
xm0 zn i vss vss Switch_NMOS_n12_X1_Y1
xm1 zn i vdd vdd Switch_PMOS_n12_X1_Y1
.ends INVD0BWP

.subckt SAR_LOGIC_1ST_STAGE_CLKGATING clk clksb s<10> s<9> s<8> s<7> s<6> s<5> s<4> s<3> s<2> s<1> s<0> sb<1>
xi4 net2 net3 net6 net1 net5 net4 DFSNQD1BWP
xi16<10> clkb s<10> sb<9> clkff<9> vdd gnd AN3D0BWP
xi16<9> clkb s<9> sb<8> clkff<8> vdd gnd AN3D0BWP
xi16<8> clkb s<8> sb<7> clkff<7> vdd gnd AN3D0BWP
xi16<7> clkb s<7> sb<6> clkff<6> vdd gnd AN3D0BWP
xi16<6> clkb s<6> sb<5> clkff<5> vdd gnd AN3D0BWP
xi16<5> clkb s<5> sb<4> clkff<4> vdd gnd AN3D0BWP
xi16<4> clkb s<4> sb<3> clkff<3> vdd gnd AN3D0BWP
xi16<3> clkb s<3> sb<2> clkff<2> vdd gnd AN3D0BWP
xi16<2> clkb s<2> sb<1> clkff<1> vdd gnd AN3D0BWP
xi16<1> clkb s<1> sb<0> clkff<0> vdd gnd AN3D0BWP
xi19 clk clkb vdd gnd INVD0BWP
xi13 clkb sb<10> clkff<10> vdd gnd AN2D0BWP
xi18<10> s<10> clkff<9> clksb s<9> sb<9> vdd gnd DFNCND1BWP
xi18<9> s<9> clkff<8> clksb s<8> sb<8> vdd gnd DFNCND1BWP
xi18<8> s<8> clkff<7> clksb s<7> sb<7> vdd gnd DFNCND1BWP
xi18<7> s<7> clkff<6> clksb s<6> sb<6> vdd gnd DFNCND1BWP
xi18<6> s<6> clkff<5> clksb s<5> sb<5> vdd gnd DFNCND1BWP
xi18<5> s<5> clkff<4> clksb s<4> sb<4> vdd gnd DFNCND1BWP
xi18<4> s<4> clkff<3> clksb s<3> sb<3> vdd gnd DFNCND1BWP
xi18<3> s<3> clkff<2> clksb s<2> sb<2> vdd gnd DFNCND1BWP
xi18<2> s<2> clkff<1> clksb s<1> sb<1> vdd gnd DFNCND1BWP
xi18<1> s<1> clkff<0> clksb s<0> sb<0> vdd gnd DFNCND1BWP
xi17 vdd clkff<10> clksb s<10> sb<10> vdd gnd DFNCND1BWP
.ends SAR_LOGIC_1ST_STAGE_CLKGATING

.subckt DFSNQD1BWP d cp sdn q vss
xm0 net44 net25 vss vss Switch_NMOS_n12_X1_Y1
xm1 net11 cp vss vss Switch_NMOS_n12_X1_Y1
xm2 q net13 vss vss Switch_NMOS_n12_X1_Y1
xm3 net7 sdn net44 vss Switch_NMOS_n12_X1_Y1
xm4 net37 net13 vss vss Switch_NMOS_n12_X1_Y1
xm5 net33 sdn net37 vss Switch_NMOS_n12_X1_Y1
xmi20 net7 net83 net63 vss Switch_NMOS_n12_X1_Y1
xmi23 net25 net83 net5 vss Switch_NMOS_n12_X1_Y1
xmi22 net33 net11 net63 vss Switch_NMOS_n12_X1_Y1
xmi21 net25 d net20 vss Switch_NMOS_n12_X1_Y1
xm6 net13 net63 vss vss Switch_NMOS_n12_X1_Y1
xmi19 net20 net11 vss vss Switch_NMOS_n12_X1_Y1
xmi24 net5 net7 vss vss Switch_NMOS_n12_X1_Y1
xm7 net83 net11 vss vss Switch_NMOS_n12_X1_Y1
xm8 net11 cp vdd vdd Switch_PMOS_n12_X1_Y1
xmi33 net33 net83 net63 vdd Switch_PMOS_n12_X1_Y1
xm9 net7 sdn vdd vdd Switch_PMOS_n12_X1_Y1
xm10 q net13 vdd vdd Switch_PMOS_n12_X1_Y1
xmi34 net25 net11 net96 vdd Switch_PMOS_n12_X1_Y1
xmi30 net7 net11 net63 vdd Switch_PMOS_n12_X1_Y1
xm11 net7 net25 vdd vdd Switch_PMOS_n12_X1_Y1
xmi28 net81 net83 vdd vdd Switch_PMOS_n12_X1_Y1
xm12 net83 net11 vdd vdd Switch_PMOS_n12_X1_Y1
xm13 net33 net13 vdd vdd Switch_PMOS_n12_X1_Y1
xmi35 net96 net7 vdd vdd Switch_PMOS_n12_X1_Y1
xm14 net33 sdn vdd vdd Switch_PMOS_n12_X1_Y1
xm15 net13 net63 vdd vdd Switch_PMOS_n12_X1_Y1
xmi26 net25 d net81 vdd Switch_PMOS_n12_X1_Y1
.ends DFSNQD1BWP

.subckt AN3D0BWP a1 a2 a3 z vss
xm0 net13 a3 vss vss Switch_NMOS_n12_X1_Y1
xm1 z net11 vss vss Switch_NMOS_n12_X1_Y1
xm2 net5 a2 net13 vss Switch_NMOS_n12_X1_Y1
xm3 net11 a1 net5 vss Switch_NMOS_n12_X1_Y1
xm4 z net11 vdd vdd Switch_PMOS_n12_X1_Y1
xm5 net11 a3 vdd vdd Switch_PMOS_n12_X1_Y1
xm6 net11 a1 vdd vdd Switch_PMOS_n12_X1_Y1
xm7 net11 a2 vdd vdd Switch_PMOS_n12_X1_Y1
.ends AN3D0BWP

.subckt AN2D0BWP a1 a2 z vss
xm0 z net5 vdd vdd Switch_PMOS_n12_X1_Y1
xm1 net5 a1 vdd vdd Switch_PMOS_n12_X1_Y1
xm2 net5 a2 vdd vdd Switch_PMOS_n12_X1_Y1
xm3 z net5 vss vss Switch_NMOS_n12_X1_Y1
xm4 net17 a2 vss vss Switch_NMOS_n12_X1_Y1
xm5 net5 a1 net17 vss Switch_NMOS_n12_X1_Y1
.ends AN2D0BWP

.subckt DFNCND1BWP d cpn cdn q qn vss
xm0 net49 cdn vdd vdd Switch_PMOS_n12_X1_Y1
xmi43 net53 net9 vdd vdd Switch_PMOS_n12_X1_Y1
xm1 net49 net20 vdd vdd Switch_PMOS_n12_X1_Y1
xmi6 net5 d net1 vdd Switch_PMOS_n12_X1_Y1
xm2 net11 net67 vdd vdd Switch_PMOS_n12_X1_Y1
xm3 net37 net49 vdd vdd Switch_PMOS_n12_X1_Y1
xm4 qn net37 vdd vdd Switch_PMOS_n12_X1_Y1
xm5 net67 cpn vdd vdd Switch_PMOS_n12_X1_Y1
xm6 q net49 vdd vdd Switch_PMOS_n12_X1_Y1
xmi44 net53 cdn vdd vdd Switch_PMOS_n12_X1_Y1
xmi17 net37 net67 net20 vdd Switch_PMOS_n12_X1_Y1
xm7 net9 net5 vdd vdd Switch_PMOS_n12_X1_Y1
xmi16 net9 net11 net20 vdd Switch_PMOS_n12_X1_Y1
xmi45 net5 net11 net53 vdd Switch_PMOS_n12_X1_Y1
xmi7 net1 net67 vdd vdd Switch_PMOS_n12_X1_Y1
xm8 qn net37 vss vss Switch_NMOS_n12_X1_Y1
xm9 net37 net49 vss vss Switch_NMOS_n12_X1_Y1
xmi4 net109 net11 vss vss Switch_NMOS_n12_X1_Y1
xmi18 net37 net11 net20 vss Switch_NMOS_n12_X1_Y1
xm10 net49 net20 net104 vss Switch_NMOS_n12_X1_Y1
xm11 net104 cdn vss vss Switch_NMOS_n12_X1_Y1
xm12 net9 net5 vss vss Switch_NMOS_n12_X1_Y1
xmi15 net9 net67 net20 vss Switch_NMOS_n12_X1_Y1
xmi5 net5 d net109 vss Switch_NMOS_n12_X1_Y1
xm13 net67 cpn vss vss Switch_NMOS_n12_X1_Y1
xmi49 net77 cdn vss vss Switch_NMOS_n12_X1_Y1
xmi48 net64 net9 net77 vss Switch_NMOS_n12_X1_Y1
xm14 q net49 vss vss Switch_NMOS_n12_X1_Y1
xm15 net11 net67 vss vss Switch_NMOS_n12_X1_Y1
xmi47 net5 net67 net64 vss Switch_NMOS_n12_X1_Y1
.ends DFNCND1BWP

.subckt SAMPLER clks_boost vin vout
xxm0 vout clks_boost vin gnd Switch_NMOS_n12_X1_Y1
.ends SAMPLER

.subckt COUNTER clksb ctrl d<1> d<0> in
xi1 net9 d<0> clksb d<1> net9 vdd gnd DFCND1BWP
xi0 net6 net12 clksb d<0> net6 vdd gnd DFCND1BWP
xi2 in ctrl net12 vdd gnd NR2D0BWP
.ends COUNTER

.subckt DFCND1BWP d cp cdn q qn vss
xm0 qn net33 vss vss Switch_NMOS_n12_X1_Y1
xmi4 net53 net5 vss vss Switch_NMOS_n12_X1_Y1
xmi18 net33 net5 net79 vss Switch_NMOS_n12_X1_Y1
xm1 net95 net79 net9 vss Switch_NMOS_n12_X1_Y1
xm2 net81 net25 vss vss Switch_NMOS_n12_X1_Y1
xmi15 net81 net67 net79 vss Switch_NMOS_n12_X1_Y1
xm3 net33 net95 vss vss Switch_NMOS_n12_X1_Y1
xm4 net67 net5 vss vss Switch_NMOS_n12_X1_Y1
xmi5 net25 d net53 vss Switch_NMOS_n12_X1_Y1
xmi49 net20 cdn vss vss Switch_NMOS_n12_X1_Y1
xmi48 net17 net81 net20 vss Switch_NMOS_n12_X1_Y1
xm5 q net95 vss vss Switch_NMOS_n12_X1_Y1
xm6 net9 cdn vss vss Switch_NMOS_n12_X1_Y1
xm7 net5 cp vss vss Switch_NMOS_n12_X1_Y1
xmi47 net25 net67 net17 vss Switch_NMOS_n12_X1_Y1
xm8 net33 net95 vdd vdd Switch_PMOS_n12_X1_Y1
xm9 net5 cp vdd vdd Switch_PMOS_n12_X1_Y1
xm10 net67 net5 vdd vdd Switch_PMOS_n12_X1_Y1
xmi43 net72 net81 vdd vdd Switch_PMOS_n12_X1_Y1
xmi6 net25 d net104 vdd Switch_PMOS_n12_X1_Y1
xm11 qn net33 vdd vdd Switch_PMOS_n12_X1_Y1
xm12 q net95 vdd vdd Switch_PMOS_n12_X1_Y1
xmi44 net72 cdn vdd vdd Switch_PMOS_n12_X1_Y1
xmi17 net33 net67 net79 vdd Switch_PMOS_n12_X1_Y1
xm13 net81 net25 vdd vdd Switch_PMOS_n12_X1_Y1
xm14 net95 net79 vdd vdd Switch_PMOS_n12_X1_Y1
xmi16 net81 net5 net79 vdd Switch_PMOS_n12_X1_Y1
xmi45 net25 net5 net72 vdd Switch_PMOS_n12_X1_Y1
xmi7 net104 net67 vdd vdd Switch_PMOS_n12_X1_Y1
xm15 net95 cdn vdd vdd Switch_PMOS_n12_X1_Y1
.ends DFCND1BWP

.subckt NR2D0BWP a1 a2 zn vss
xm0 zn a2 vss vss Switch_NMOS_n12_X1_Y1
xm1 zn a1 vss vss Switch_NMOS_n12_X1_Y1
xm2 net13 a2 vdd vdd Switch_PMOS_n12_X1_Y1
xm3 zn a1 net13 vdd Switch_PMOS_n12_X1_Y1
.ends NR2D0BWP
