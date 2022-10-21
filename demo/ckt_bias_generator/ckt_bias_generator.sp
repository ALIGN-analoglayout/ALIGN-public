.subckt dig22nand a b o1 vccd vssx
.ends
.subckt dig22inv a o1 vccd vssx
.ends
.subckt folded_cascode_n ina inb incsa incsl outb vcca vssx
qn1 diffa ina incsa vssx npv drain=sig m=2 nf=6 source=sig nfin=4
qn2 diffb inb incsa vssx npv drain=sig m=2 nf=6 source=sig nfin=4
qp6<0> incsl incsl casp vcca ppv stack=2 drain=sig m=4 source=sig nfin=4
qp6<1> incsl incsl casp vcca ppv stack=2 drain=sig m=4 source=sig nfin=4
qp2 casn incsl diffa vcca ppv stack=2 drain=sig m=8 source=sig nfin=4
qp5<0> casp casp vcca vcca ppv stack=2 drain=sig m=4 source=pwr nfin=4
qp5<1> casp casp vcca vcca ppv stack=2 drain=sig m=4 source=pwr nfin=4
qp4 diffa casp vcca vcca ppv stack=2 drain=sig m=8 source=pwr nfin=4
qp1 outb incsl diffb vcca ppv stack=2 drain=sig m=8 source=sig nfin=4
qp3 diffb casp vcca vcca ppv stack=2 drain=sig m=8 source=pwr nfin=4
qn6 net1 casn vssx vssx npv stack=2 drain=sig m=8 source=gnd nfin=4
qn3 outb casn net2 vssx npv stack=2 drain=sig m=8 source=sig nfin=4
qn5 net2 casn vssx vssx npv stack=2 drain=sig m=8 source=gnd nfin=4
qn4 casn casn net1 vssx npv stack=2 drain=sig m=8 source=sig nfin=4
.ends
.subckt folded_cascode_p ina inb incsa incsl outb vcca vssx
qn2 diffb inb incsa vcca ppv drain=sig m=2 nf=6 source=sig nfin=4
qn1 diffa ina incsa vcca ppv drain=sig m=2 nf=6 source=sig nfin=4
qp4 net1 casp vcca vcca ppv stack=2 drain=sig m=8 source=pwr nfin=4
qp2 casp casp net1 vcca ppv stack=2 drain=sig m=8 source=sig nfin=4
qp1 outb casp net2 vcca ppv stack=2 drain=sig m=8 source=sig nfin=4
qp3 net2 casp vcca vcca ppv stack=2 drain=sig m=8 source=pwr nfin=4
qn5 diffb casn vssx vssx npv stack=2 drain=sig m=16 source=gnd nfin=4
qn3 outb incsl diffb vssx npv stack=2 drain=sig m=8 source=sig nfin=4
qp6<0> casn casn vssx vssx npv stack=2 drain=sig m=4 source=gnd nfin=4
qp6<1> casn casn vssx vssx npv stack=2 drain=sig m=4 source=gnd nfin=4
qp5<0> incsl incsl casn vssx npv stack=2 drain=sig m=4 source=sig nfin=4
qp5<1> incsl incsl casn vssx npv stack=2 drain=sig m=4 source=sig nfin=4
qn4 casp incsl diffa vssx npv stack=2 drain=sig m=8 source=sig nfin=4
qn6 diffa casn vssx vssx npv stack=2 drain=sig m=16 source=gnd nfin=4
.ends
.subckt nbias_gen iout en vcca vssx
i6 vssx net1 vssx vssx npv stack=4 drain=sig m=2 source=gnd nfin=4
mn0 net1 net2 net15 vssx npv stack=4 drain=sig m=8 source=sig nfin=4
qn1 net2 net2 vssx vssx npv stack=4 drain=sig m=2 source=gnd nfin=4
qp1 net2 net1 vcca vcca ppv stack=4 drain=sig m=2 source=pwr nfin=4
mp1 iout net1 vcca vcca ppv stack=4 drain=sig m=2 source=pwr nfin=4
mp0 net1 net1 vcca vcca ppv stack=4 drain=sig m=2 source=pwr nfin=4
i9 net15 en net5 vssx npv drain=sig m=1 nf=2 source=sig nfin=4
i0 net1 vssx vssx vssx npv drain=sig m=1 nf=4 source=gnd nfin=4
r0 net5 vssx tfr_prim w=1 l=1
.ends
.subckt pbias_gen iout en vcca vssx
mn0 net4 net4 vssx vssx npv stack=4 drain=sig m=2 source=gnd nfin=4
qn1 net3 net4 vssx vssx npv stack=4 drain=sig m=2 source=gnd nfin=4
mn1 iout net4 vssx vssx npv stack=4 drain=sig m=2 source=gnd nfin=4
qp1 net3 net3 vcca vcca ppv drain=sig m=2 nf=2 source=pwr nfin=4
mp0 net4 net3 net16 vcca ppv drain=sig m=8 nf=2 source=sig nfin=4
i9 net16 en net5 vcca ppv drain=sig m=1 nf=2 source=sig nfin=4
i6 vcca net4 vcca vcca ppv drain=sig m=1 nf=2 source=pwr nfin=4
i0 net4 vcca vcca vcca ppv drain=sig m=1 nf=4 source=pwr nfin=4
r0 vcca net5 tfr_prim w=1 l=1
.ends
.subckt ckt_bias_generator v1n v1p v2n v2p ctrl n p vccd vcca vref_n vref_p vssx
i20 v1p v1p vssx vssx npv stack=2 drain=sig m=1 source=gnd nfin=4
qn3 v2p v2p vssx vssx npv stack=2 drain=sig m=1 source=gnd nfin=4
i21 v1p gate_p vcca vcca ppv drain=sig m=1 nf=2 source=pwr nfin=4
i12 fb_ota_n gate_p vcca vcca ppv drain=sig m=1 nf=2 source=pwr nfin=4
i13 v2p gate_p vcca vcca ppv drain=sig m=1 nf=2 source=pwr nfin=4
nand1 ctrl n net19 vccd vssx dig22nand
nand0 p ctrl net6 vccd vssx dig22nand
i0 fb_ota_n vref_n i_incsa_n i_incsl_n gate_p vcca vssx folded_cascode_n
i15 fb_ota_p gate_n vssx vssx npv drain=sig m=1 nf=2 source=gnd nfin=4
i16 v2n gate_n vssx vssx npv drain=sig m=1 nf=2 source=gnd nfin=4
i22 v1n gate_n vssx vssx npv drain=sig m=1 nf=2 source=gnd nfin=4
i14 fb_ota_p vref_p i_incsa_p i_incsl_p gate_n vcca vssx folded_cascode_p
i35 v1n v1n vcca vcca ppv stack=2 drain=sig m=1 source=pwr nfin=4
i36 v2n v2n vcca vcca ppv stack=2 drain=sig m=1 source=pwr nfin=4
r6 vcca fb_ota_p tfr_prim w=1 l=1
r0 fb_ota_n vssx tfr_prim w=1 l=1
inv09 net19 net21 vccd vssx dig22inv
i24 i_incsa_p net21 vcca vssx nbias_gen
i27 i_incsl_p net21 vcca vssx nbias_gen
i25 i_incsa_n net6 vcca vssx pbias_gen
i32 i_incsl_n net6 vcca vssx pbias_gen
.ends ckt_bias_generator
.END
