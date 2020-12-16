
.subckt CCP_PMOS_S_n12_X1_Y1 B DA DB S
xM0 DA DB S B Switch_PMOS_n12_X1_Y1
xM1 DB DA S B Switch_PMOS_n12_X1_Y1
.ends CCP_PMOS_S_n12_X1_Y1

.subckt Switch_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Switch_PMOS_n12_X1_Y1

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

.subckt DP_PMOS_n12_X1_Y1 B DA GA S DB GB
xM0 DA GA S B Switch_PMOS_n12_X1_Y1
xM1 DB GB S B Switch_PMOS_n12_X1_Y1
.ends DP_PMOS_n12_X1_Y1

.subckt CMC_PMOS_n12_X1_Y1 B DA G SA DB SB
xM0 DA G SA B Switch_PMOS_n12_X1_Y1
xM1 DB G SB B Switch_PMOS_n12_X1_Y1
.ends CMC_PMOS_n12_X1_Y1

.subckt CMC_NMOS_n12_X1_Y1 B DA G SA DB SB
xM0 DA G SA B Switch_NMOS_n12_X1_Y1
xM1 DB G SB B Switch_NMOS_n12_X1_Y1
.ends CMC_NMOS_n12_X1_Y1

.subckt COMPARATOR_2LEVEL_BIDIRECTIONAL_MAC_SKEW gnd fine_boost fine vdd clk vxn vxp flipb flip outm intern clkn _net0 vxn2 _net1 vmidb interp vxp2 vmid outp
xi3 gnd fine_boost fine gnd vdd CLK_BOOST_COMP
xi4 gnd net073 vdd gnd INVD0BWP
xi0 clk clkb vdd gnd INVD0BWP
xxm0 gnd net066 gnd Dcap_NMOS_n12_X1_Y1
xxm1 gnd net065 gnd Dcap_NMOS_n12_X1_Y1
xxm56 gnd gnd Dummy1_NMOS_n12_X1_Y1
xxm51 gnd gnd Dummy1_NMOS_n12_X1_Y1
xxm31 flipb flip gnd gnd Switch_NMOS_n12_X1_Y1
xxm21 flip clkb gnd gnd Switch_NMOS_n12_X1_Y1
xxm15 net05 clkn gnd gnd Switch_NMOS_n12_X1_Y1
xxm32 clkn flip gnd gnd Switch_NMOS_n12_X1_Y1
xxm38 vmidb vxn2 gnd gnd Switch_NMOS_n12_X1_Y1
xxm39 vmid vxp2 gnd gnd Switch_NMOS_n12_X1_Y1
xxm33 clk flipb clkn gnd Switch_NMOS_n12_X1_Y1
xxm62 vdd clk vxp vdd Switch_PMOS_n12_X1_Y1
xxm61 vdd clk vxn vdd Switch_PMOS_n12_X1_Y1
xxm58 gnd vdd Dummy1_PMOS_n12_X1_Y1
xxm57 gnd vdd Dummy1_PMOS_n12_X1_Y1
xxm54 gnd vdd Dummy1_PMOS_n12_X1_Y1
xxm30 flipb clk vdd vdd Switch_PMOS_n12_X1_Y1
xxm28 flip vxn net027 vdd Switch_PMOS_n12_X1_Y1
xxm20 net027 clkb vdd vdd Switch_PMOS_n12_X1_Y1
xxm29 flip vxp net027 vdd Switch_PMOS_n12_X1_Y1
xxm19 net04 flipb vdd vdd Switch_PMOS_n12_X1_Y1
xxm34 clk flip clkn vdd Switch_PMOS_n12_X1_Y1
xxm49_xm48 interp intern vdd vdd CCP_PMOS_S_n12_X1_Y1
xxm41_xm37 vxp2 flipb gnd vxn2 gnd CMC_NMOS_S_n12_X1_Y1
xxm45_xm47 vmidb vxn2 vdd intern vdd CMC_PMOS_S_n12_X1_Y1
xxm44_xm46 vmid vxp2 vdd interp vdd CMC_PMOS_S_n12_X1_Y1
xxm42_xm43 interp intern vmid vmidb gnd CCP_NMOS_n12_X1_Y1
xm16_xm2 intern gnd vdd outm INV_LVT
xm6_xm9 interp gnd vdd outp INV_LVT
xxm13_xm14 vxp _net1 net05 vxn _net0 gnd DP_NMOS_n12_X1_Y1
xxm17_xm18 vxp _net1 net04 vxn _net0 vdd DP_PMOS_n12_X1_Y1
xxm40_xm36 vxp2 flipb vxp vxn2 vxn vdd CMC_PMOS_n12_X1_Y1
xxm10_xm12 vxp fine_boost net066 vxn net065 gnd CMC_NMOS_n12_X1_Y1
.ends COMPARATOR_2LEVEL_BIDIRECTIONAL_MAC_SKEW

.subckt Dcap_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Dcap_NMOS_n12_X1_Y1

.subckt Dummy1_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08 m=2
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08 m=2
.ends Dummy1_NMOS_n12_X1_Y1

.subckt Dummy1_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08 m=2
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08 m=2
.ends Dummy1_PMOS_n12_X1_Y1

.subckt CCP_PMOS_S_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends CCP_PMOS_S_n12_X1_Y1

.subckt CMC_NMOS_S_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends CMC_NMOS_S_n12_X1_Y1

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

.subckt DP_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends DP_PMOS_n12_X1_Y1

.subckt CMC_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends CMC_PMOS_n12_X1_Y1

.subckt CMC_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends CMC_NMOS_n12_X1_Y1

.subckt CLK_BOOST_COMP bypass clk_boost clk_in
xxm5 net8 net5 vdd vdd Switch_PMOS_n12_X1_Y1
xxm4 clk_boost net6 net8 vdd Switch_PMOS_n12_X1_Y1
xxm1 net5 net6 net8 vdd Switch_PMOS_n12_X1_Y1
xxm6 clk_boost net6 clk_in gnd Switch_NMOS_n12_X1_Y1
xxm2 net5 net6 net013 gnd Switch_NMOS_n12_X1_Y1
xi1 net6 bypass net013 vdd gnd NR2D2BWP
xi2 clk_in net6 vdd gnd INVD0BWP
c2 net8 net013 Cap_2f
.ends CLK_BOOST_COMP

.subckt NR2D2BWP a1 a2 zn vss
xm0 zn a2 vss vss Switch_NMOS_n12_X1_Y1
xm1 zn a1 vss vss Switch_NMOS_n12_X1_Y1
xm4 zn a1 net17 vdd Switch_PMOS_n12_X1_Y1
xm6 zn a1 net25 vdd Switch_PMOS_n12_X1_Y1
xm7_m5 net17 a2 vdd net25 vdd CMC_PMOS_S_n12_X1_Y1
.ends NR2D2BWP

.subckt INVD0BWP i zn vss
xm0 zn i vss vss Switch_NMOS_n12_X1_Y1
xm1 zn i vdd vdd Switch_PMOS_n12_X1_Y1
.ends INVD0BWP
