* label = Comparator
.subckt INVD1BWP i zn vdd vss
m0 zn i vss vss nfet w=w0 l=l0
m1 zn i vdd vdd pfet w=w1 l=l0
.ends INVD1BWP

.subckt COMP_GM_STAGE_BIAS_0415 gnd vbn vbp vcm vdd_a
xm4 gnd vbn gnd gnd lvtnfet w=w2 l=l1
xm0 vbn vbn gnd gnd lvtnfet w=w2 l=l1
xm1 vbp vcm net5 net5 pfet w=w3 l=l2
xm5 vbp vbp vbp net5 pfet w=w3 l=l2
xm8 net5 vbp vdd_a vdd_a lvtpfet w=w4 l=l3
xm3 vdd_a vbp vdd_a vdd_a lvtpfet w=w4 l=l3
.ends COMP_GM_STAGE_BIAS_0415

.subckt COMP_GM_STAGE_0415 calm calp cco_icalm cco_icalp clk gnd ictrm ictrp inm inp outm outp valid_vco vbn vbp vcc_comp vcc_gm vcm pre_charge
xm91 net89 valid_vco_d vcc_gm vcc_gm pfet w=w5 l=l0
xm89 net073 valid_vco_b cco_icalm vcc_gm pfet w=w6 l=l0
xm90 net073 valid_vco_d vcc_gm vcc_gm pfet w=w5 l=l0
xm92 net89 valid_vco_b cco_icalp vcc_gm pfet w=w6 l=l0
xm87 ictrp net89 vcc_gm vcc_gm pfet w=w7 l=l4
xm7 net78 valid_vco_b vbp vcc_gm pfet w=w6 l=l0
xm4 net78 valid_vco_d vcc_gm vcc_gm pfet w=w5 l=l0
xm88 ictrm net073 vcc_gm vcc_gm pfet w=w7 l=l4
xm45 net070 net070 net070 net070 pfet w=w3 l=l2
xm86 vcc_comp vcc_comp vcc_comp vcc_comp pfet w=w8 l=l2
xm64 ictrm valid_vco_b net019 vcc_comp pfet w=w6 l=l0
xm82 outm net054 vcc_comp vcc_comp pfet w=w6 l=l0
xm17 net83 valid_vco_d net019 vcc_comp pfet w=w6 l=l0
xm81 net054 calm net054 net054 pfet w=w9 l=l5
xm11 net019 inp net070 net070 pfet w=w10 l=l2
xm55 net042 inm net070 net070 pfet w=w10 l=l2
xm2 net030 net054 net83 vcc_comp pfet w=w11 l=l6
xm6 outp net030 vcc_comp vcc_comp pfet w=w6 l=l0
xm76 ictrp valid_vco_b net042 vcc_comp pfet w=w6 l=l0
xm78 net054 net030 net90 vcc_comp pfet w=w11 l=l6
xm73 net90 valid_vco_d net042 vcc_comp pfet w=w6 l=l0
xm13 net030 calp net030 net030 pfet w=w9 l=l5
xm44 ictrp valid_vco_b pre_charge gnd nfet w=w5 l=l0
xm43 ictrm valid_vco_b pre_charge gnd nfet w=w5 l=l0
xm63 ictrm valid_vco_d net019 gnd nfet w=w5 l=l0
xm83 outm net054 gnd gnd nfet w=w5 l=l0
xm19 net83 valid_vco_b net019 gnd nfet w=w5 l=l0
xm80 net054 clkb gnd gnd nfet w=w12 l=l0
xm74 net90 valid_vco_b net042 gnd nfet w=w5 l=l0
xm26 net83 clkb gnd gnd nfet w=w12 l=l0
xm75 net90 clkb gnd gnd nfet w=w12 l=l0
xm77 ictrp valid_vco_d net042 gnd nfet w=w5 l=l0
xm21 outp net030 gnd gnd nfet w=w5 l=l0
xm79 net054 net030 gnd gnd nfet w=w13 l=l6
xm23 net030 clkb gnd gnd nfet w=w12 l=l0
xm18 net030 net054 gnd gnd nfet w=w13 l=l6
xm57 vcc_gm vbp vcc_gm vcc_gm lvtpfet w=w14 l=l7
xm56 vcc_gm vbp vcc_gm vcc_gm lvtpfet w=w14 l=l8
xm52 net070 clkb net036 net036 lvtpfet w=w2 l=l0
xm51 net036 vbp vcc_comp vcc_gm lvtpfet w=w4 l=l3
xm0 net070 net78 vcc_gm vcc_gm lvtpfet w=w4 l=l3
xi4<1> valid_vco valid_vco_b vcc_comp gnd INVD1BWP
xi4<0> valid_vco valid_vco_b vcc_comp gnd INVD1BWP
xi5<1> valid_vco_b valid_vco_d vcc_comp gnd INVD1BWP
xi5<0> valid_vco_b valid_vco_d vcc_comp gnd INVD1BWP
xi6<1> clk clkb vcc_comp gnd INVD1BWP
xi6<0> clk clkb vcc_comp gnd INVD1BWP
xm38 ictrm net089 gnd gnd lvtnfet w=w2 l=l1
xm33 ictrp net059 gnd gnd lvtnfet w=w2 l=l1
d2 gnd vcc_gm diode
d0 gnd vcc_gm diode
xm9 net089 valid_vco_d vbn gnd nfet w=w5 l=l0
xm8 net059 valid_vco_d vbn gnd nfet w=w5 l=l0
xm5 net059 valid_vco_b gnd gnd nfet w=w5 l=l0
xm10 net089 valid_vco_b gnd gnd nfet w=w5 l=l0
xm12 gnd vbn gnd gnd lvtnfet w=w7 l=l1
xm3 gnd vbn gnd gnd lvtnfet w=w2 l=l4
xm1 gnd vbn gnd gnd lvtnfet w=w7 l=l4
xi0 gnd vbn vbp vcm vcc_gm COMP_GM_STAGE_BIAS_0415
.ends COMP_GM_STAGE_0415

