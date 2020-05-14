
.subckt CCP_NMOS_S_n12_X1_Y1 B DA DB S
xM0 DA DB S B Switch_NMOS_n12_X1_Y1
xM1 DB DA S B Switch_NMOS_n12_X1_Y1
.ends CCP_NMOS_S_n12_X1_Y1

.subckt Switch_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Switch_NMOS_n12_X1_Y1

.subckt CMC_NMOS_S_n12_X1_Y1 B DA G S DB
xM0 DA G S B Switch_NMOS_n12_X1_Y1
xM1 DB G S B Switch_NMOS_n12_X1_Y1
.ends CMC_NMOS_S_n12_X1_Y1

.subckt CMC_PMOS_S_n12_X1_Y1 B DA G S DB
xM0 DA G S B Switch_PMOS_n12_X1_Y1
xM1 DB G S B Switch_PMOS_n12_X1_Y1
.ends CMC_PMOS_S_n12_X1_Y1

.subckt Switch_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Switch_PMOS_n12_X1_Y1

.subckt CCP_PMOS_n12_X1_Y1 B DA DB SA SB
xM0 DA DB SA B Switch_PMOS_n12_X1_Y1
xM1 DB DA SB B Switch_PMOS_n12_X1_Y1
.ends CCP_PMOS_n12_X1_Y1

.subckt tgate D GA S GB
xM0 D GA S BN Switch_NMOS_n12_X1_Y1
xM1 D GB S BP Switch_PMOS_n12_X1_Y1
.ends tgate

.subckt DP_PMOS_n12_X1_Y1 B DA GA S DB GB
xM0 DA GA S B Switch_PMOS_n12_X1_Y1
xM1 DB GB S B Switch_PMOS_n12_X1_Y1
.ends DP_PMOS_n12_X1_Y1

.subckt CMC_PMOS_n12_X1_Y1 B DA G SA DB SB
xM0 DA G SA B Switch_PMOS_n12_X1_Y1
xM1 DB G SB B Switch_PMOS_n12_X1_Y1
.ends CMC_PMOS_n12_X1_Y1

.subckt COMP_GM_STAGE_0415 vcc_gm cco_icalm cco_icalp ictrp vbp ictrm vcc_comp outm calm inp inm outp calp pre_charge gnd valid_vco clk vbn vcm
xxm7 net78 valid_vco_b vbp vcc_gm Switch_PMOS_n12_X1_Y1
xxm4 net78 valid_vco_d vcc_gm vcc_gm Switch_PMOS_n12_X1_Y1
xxm45 net070 net070 Dummy1_PMOS_n12_X1_Y1
xxm86 vcc_comp vcc_comp Dummy1_PMOS_n12_X1_Y1
xxm81 net054 calm net054 Dcap_PMOS_n12_X1_Y1
xxm13 net030 calp net030 Dcap_PMOS_n12_X1_Y1
xxm83 outm net054 gnd gnd Switch_NMOS_n12_X1_Y1
xxm21 outp net030 gnd gnd Switch_NMOS_n12_X1_Y1
xxm57 vcc_gm vbp vcc_gm Dcap_PMOS_n12_X1_Y1
xxm56 vcc_gm vbp vcc_gm Dcap_PMOS_n12_X1_Y1
xxm52 net070 clkb net036 net036 Switch_PMOS_n12_X1_Y1
xxm51 net036 vbp vcc_comp vcc_gm Switch_PMOS_n12_X1_Y1
xxm0 net070 net78 vcc_gm vcc_gm Switch_PMOS_n12_X1_Y1
xi4<1> valid_vco valid_vco_b vcc_comp gnd INVD1BWP
xi4<0> valid_vco valid_vco_b vcc_comp gnd INVD1BWP
xi5<1> valid_vco_b valid_vco_d vcc_comp gnd INVD1BWP
xi5<0> valid_vco_b valid_vco_d vcc_comp gnd INVD1BWP
xi6<1> clk clkb vcc_comp gnd INVD1BWP
xi6<0> clk clkb vcc_comp gnd INVD1BWP
xxm38 ictrm net089 gnd gnd Switch_NMOS_n12_X1_Y1
xxm33 ictrp net059 gnd gnd Switch_NMOS_n12_X1_Y1
xxm12 gnd vbn gnd Dcap_NMOS_n12_X1_Y1
xxm3 gnd vbn gnd Dcap_NMOS_n12_X1_Y1
xxm1 gnd vbn gnd Dcap_NMOS_n12_X1_Y1
xi0 gnd vbn vbp vcm vcc_gm COMP_GM_STAGE_BIAS_0415
xxm79_xm18 net054 net030 gnd gnd CCP_NMOS_S_n12_X1_Y1
xxm80_xm23 net054 clkb gnd net030 gnd CMC_NMOS_S_n12_X1_Y1
xxm75_xm26 net90 clkb gnd net83 gnd CMC_NMOS_S_n12_X1_Y1
xxm10_xm5 net089 valid_vco_b gnd net059 gnd CMC_NMOS_S_n12_X1_Y1
xxm44_xm43 ictrp valid_vco_b pre_charge ictrm gnd CMC_NMOS_S_n12_X1_Y1
xxm9_xm8 net089 valid_vco_d vbn net059 gnd CMC_NMOS_S_n12_X1_Y1
xxm91_xm90 net89 valid_vco_d vcc_gm net073 vcc_gm CMC_PMOS_S_n12_X1_Y1
xxm78_xm2 net054 net030 net90 net83 vcc_comp CCP_PMOS_n12_X1_Y1
xm63_xm64 valid_vco_d net019 valid_vco_b ictrm tgate
xm77_xm76 valid_vco_d net042 valid_vco_b ictrp tgate
xm19_xm17 valid_vco_b net019 valid_vco_d net83 tgate
xm74_xm73 valid_vco_b net042 valid_vco_d net90 tgate
xxm87_xm88 ictrp net89 vcc_gm ictrm net073 vcc_gm DP_PMOS_n12_X1_Y1
xxm11_xm55 net019 inp net070 net042 inm net070 DP_PMOS_n12_X1_Y1
xxm82_xm6 outm net054 vcc_comp outp net030 vcc_comp DP_PMOS_n12_X1_Y1
xxm92_xm89 net89 valid_vco_b cco_icalp net073 cco_icalm vcc_gm CMC_PMOS_n12_X1_Y1
.ends COMP_GM_STAGE_0415

.subckt Dummy1_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Dummy1_PMOS_n12_X1_Y1

.subckt Dcap_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Dcap_PMOS_n12_X1_Y1

.subckt Dcap_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends Dcap_NMOS_n12_X1_Y1

.subckt CCP_NMOS_S_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends CCP_NMOS_S_n12_X1_Y1

.subckt CMC_NMOS_S_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends CMC_NMOS_S_n12_X1_Y1

.subckt CMC_PMOS_S_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends CMC_PMOS_S_n12_X1_Y1

.subckt CCP_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends CCP_PMOS_n12_X1_Y1

.subckt DP_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends DP_PMOS_n12_X1_Y1

.subckt CMC_PMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends CMC_PMOS_n12_X1_Y1

.subckt INVD1BWP i zn vss
xm0 zn i vss vss Switch_NMOS_n12_X1_Y1
xm1 zn i vdd vdd Switch_PMOS_n12_X1_Y1
.ends INVD1BWP

.subckt COMP_GM_STAGE_BIAS_0415 vbn vbp vcm vdd_a
xxm4 gnd vbn gnd Dcap_NMOS_n12_X1_Y1
xxm0 vbn vbn gnd gnd DCL_NMOS_n12_X1_Y1
xxm1 vbp vcm net5 net5 Switch_PMOS_n12_X1_Y1
xxm5 vbp net5 Dummy1_PMOS_n12_X1_Y1
xxm8 net5 vbp vdd_a vdd_a Switch_PMOS_n12_X1_Y1
xxm3 vdd_a vbp vdd_a Dcap_PMOS_n12_X1_Y1
.ends COMP_GM_STAGE_BIAS_0415

.subckt DCL_NMOS_n12_X1_Y1 D G S B
m0 D G S1 B nmos_rvt  w=1e-08 l=1e-08
m1 S1 G S B nmos_rvt  w=1e-08 l=1e-08
.ends DCL_NMOS_n12_X1_Y1
