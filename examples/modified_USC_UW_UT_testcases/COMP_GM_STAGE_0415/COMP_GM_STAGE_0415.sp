* label = Comparator
.subckt INVD1BWP i zn vdd vss
m0 zn i vss vss nfet w=w0 l=l0
m1 zn i vdd vdd pfet w=w1 l=l0
.ends INVD1BWP

.subckt COMP_GM_STAGE_BIAS_0415 gnd vbn vbp vcm vdd_a
m4 gnd vbn gnd gnd lvtnfet w=w2 l=l1
m0 vbn vbn gnd gnd lvtnfet w=w2 l=l1
m1 vbp vcm net5 net5 pfet w=w3 l=l2
m5 vbp vbp vbp net5 pfet w=w3 l=l2
m8 net5 vbp vdd_a vdd_a lvtpfet w=w4 l=l3
m3 vdd_a vbp vdd_a vdd_a lvtpfet w=w4 l=l3
.ends COMP_GM_STAGE_BIAS_0415

.subckt COMP_GM_STAGE_0415 calm calp cco_icalm cco_icalp clk gnd ictrm ictrp inm inp outm outp valid_vco vbn vbp vcc_comp vcc_gm vcm pre_charge
m91 net89 valid_vco_d vcc_gm vcc_gm pfet w=w5 l=l0
m89 net073 valid_vco_b cco_icalm vcc_gm pfet w=w6 l=l0
m90 net073 valid_vco_d vcc_gm vcc_gm pfet w=w5 l=l0
m92 net89 valid_vco_b cco_icalp vcc_gm pfet w=w6 l=l0
m87 ictrp net89 vcc_gm vcc_gm pfet w=w7 l=l4
m7 net78 valid_vco_b vbp vcc_gm pfet w=w6 l=l0
m4 net78 valid_vco_d vcc_gm vcc_gm pfet w=w5 l=l0
m88 ictrm net073 vcc_gm vcc_gm pfet w=w7 l=l4
m45 net070 net070 net070 net070 pfet w=w3 l=l2
m86 vcc_comp vcc_comp vcc_comp vcc_comp pfet w=w8 l=l2
m64 ictrm valid_vco_b net019 vcc_comp pfet w=w6 l=l0
m82 outm net054 vcc_comp vcc_comp pfet w=w6 l=l0
m17 net83 valid_vco_d net019 vcc_comp pfet w=w6 l=l0
m81 net054 calm net054 net054 pfet w=w9 l=l5
m11 net019 inp net070 net070 pfet w=w10 l=l2
m55 net042 inm net070 net070 pfet w=w10 l=l2
m2 net030 net054 net83 vcc_comp pfet w=w11 l=l6
m6 outp net030 vcc_comp vcc_comp pfet w=w6 l=l0
m76 ictrp valid_vco_b net042 vcc_comp pfet w=w6 l=l0
m78 net054 net030 net90 vcc_comp pfet w=w11 l=l6
m73 net90 valid_vco_d net042 vcc_comp pfet w=w6 l=l0
m13 net030 calp net030 net030 pfet w=w9 l=l5
m44 ictrp valid_vco_b pre_charge gnd nfet w=w5 l=l0
m43 ictrm valid_vco_b pre_charge gnd nfet w=w5 l=l0
m63 ictrm valid_vco_d net019 gnd nfet w=w5 l=l0
m83 outm net054 gnd gnd nfet w=w5 l=l0
m19 net83 valid_vco_b net019 gnd nfet w=w5 l=l0
m80 net054 clkb gnd gnd nfet w=w12 l=l0
m74 net90 valid_vco_b net042 gnd nfet w=w5 l=l0
m26 net83 clkb gnd gnd nfet w=w12 l=l0
m75 net90 clkb gnd gnd nfet w=w12 l=l0
m77 ictrp valid_vco_d net042 gnd nfet w=w5 l=l0
m21 outp net030 gnd gnd nfet w=w5 l=l0
m79 net054 net030 gnd gnd nfet w=w13 l=l6
m23 net030 clkb gnd gnd nfet w=w12 l=l0
m18 net030 net054 gnd gnd nfet w=w13 l=l6
m57 vcc_gm vbp vcc_gm vcc_gm lvtpfet w=w14 l=l7
m56 vcc_gm vbp vcc_gm vcc_gm lvtpfet w=w14 l=l8
m52 net070 clkb net036 net036 lvtpfet w=w2 l=l0
m51 net036 vbp vcc_comp vcc_gm lvtpfet w=w4 l=l3
m0 net070 net78 vcc_gm vcc_gm lvtpfet w=w4 l=l3
xi4<1> valid_vco valid_vco_b vcc_comp gnd INVD1BWP
xi4<0> valid_vco valid_vco_b vcc_comp gnd INVD1BWP
xi5<1> valid_vco_b valid_vco_d vcc_comp gnd INVD1BWP
xi5<0> valid_vco_b valid_vco_d vcc_comp gnd INVD1BWP
xi6<1> clk clkb vcc_comp gnd INVD1BWP
xi6<0> clk clkb vcc_comp gnd INVD1BWP
m38 ictrm net089 gnd gnd lvtnfet w=w2 l=l1
m33 ictrp net059 gnd gnd lvtnfet w=w2 l=l1
d2 gnd vcc_gm diode
d0 gnd vcc_gm diode
m9 net089 valid_vco_d vbn gnd nfet w=w5 l=l0
m8 net059 valid_vco_d vbn gnd nfet w=w5 l=l0
m5 net059 valid_vco_b gnd gnd nfet w=w5 l=l0
m10 net089 valid_vco_b gnd gnd nfet w=w5 l=l0
m12 gnd vbn gnd gnd lvtnfet w=w7 l=l1
m3 gnd vbn gnd gnd lvtnfet w=w2 l=l4
m1 gnd vbn gnd gnd lvtnfet w=w7 l=l4
xi0 gnd vbn vbp vcm vcc_gm COMP_GM_STAGE_BIAS_0415
.ends COMP_GM_STAGE_0415

