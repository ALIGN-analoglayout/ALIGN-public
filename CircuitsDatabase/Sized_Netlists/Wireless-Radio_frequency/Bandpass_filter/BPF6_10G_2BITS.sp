** Generated for: hspiceD
** Generated on: Jan  5 20:45:56 2020
** Design library name: PhasedArray_WB_copy
** Design cell name: BPF6_10G_2BITS
** Design view name: schematic


.TEMP 25.0
.OPTION
+    ARTIST=2
+    INGOLD=2
+    PARHIER=LOCAL
+    PSF=2


** Library name: PhasedArray_WB_copy
** Cell name: res_24K
** View name: schematic
.subckt res_24K t1 t2 vss
xr4 t2 net05 vss resistor l=8e-6 w=500e-9 m=1 
xr2 net06 net05 vss resistor l=8e-6 w=500e-9 m=1 
xr1 net06 net6 vss resistor l=8e-6 w=500e-9 m=1 
xr0 t1 net6 vss resistor l=8e-6 w=500e-9 m=1 
.ends res_24K
** End of subcircuit definition.

** Library name: PhasedArray_WB_copy
** Cell name: capbank_gp_lowC_noLSB_9u_2BITS
** View name: schematic
.subckt capbank_gp_lowC_noLSB_9u_2BITS b<3> b<2> b<1> b<0> left right vdd vss
xc3 right net3 vss mimcap lt=9e-6 wt=9e-6 lay=7 m=2 
xc2 left net1 vss mimcap lt=9e-6 wt=9e-6 lay=7 m=2 
xc1 right net4 vss mimcap lt=9e-6 wt=9e-6 lay=7 m=1 
xc0 left net2 vss mimcap lt=9e-6 wt=9e-6 lay=7 m=1 
xm1 net1 b1_buf net3 vss nmos lr=60e-9 wr=2e-6 nr=20 sigma=1 m=2 
xm0 net2 b0_buf net4 vss nmos lr=60e-9 wr=2e-6 nr=20 sigma=1 m=1 
m44 net0155 net0120 vss vss nmos l=60e-9 w=1e-6 m=1 nf=1 
m40 net0120 b<3> vss vss nmos l=60e-9 w=1e-6 m=1 nf=1 
m37 net0159 net0104 vss vss nmos l=60e-9 w=1e-6 m=1 nf=1 
m36 net0158 net0105 vss vss nmos l=60e-9 w=1e-6 m=1 nf=1 
m35 net0157 net0106 vss vss nmos l=60e-9 w=1e-6 m=1 nf=1 
m31 net0104 b<2> vss vss nmos l=60e-9 w=1e-6 m=1 nf=1 
m30 net0105 b<1> vss vss nmos l=60e-9 w=1e-6 m=1 nf=1 
m29 net0106 b<0> vss vss nmos l=60e-9 w=1e-6 m=1 nf=1 
m18 b3_buf b3_inv vss vss nmos l=60e-9 w=1e-6 m=1 nf=1 
m16 b3_inv b<3> vss vss nmos l=60e-9 w=1e-6 m=1 nf=1 
m15 b2_inv b<2> vss vss nmos l=60e-9 w=1e-6 m=1 nf=1 
m13 b2_buf b2_inv vss vss nmos l=60e-9 w=1e-6 m=1 nf=1 
m11 b1_buf b1_inv vss vss nmos l=60e-9 w=1e-6 m=1 nf=1 
m9 b1_inv b<1> vss vss nmos l=60e-9 w=1e-6 m=1 nf=1 
m7 b0_buf b0_inv vss vss nmos l=60e-9 w=1e-6 m=1 nf=1 
m4 b0_inv b<0> vss vss nmos l=60e-9 w=1e-6 m=1 nf=1 
m42 net0155 net0120 vdd vdd pmos l=60e-9 w=1e-6 m=1 nf=1 
m38 net0120 b<3> vdd vdd pmos l=60e-9 w=1e-6 m=1 nf=1 
m34 net0159 net0104 vdd vdd pmos l=60e-9 w=1e-6 m=1 nf=1 
m33 net0158 net0105 vdd vdd pmos l=60e-9 w=1e-6 m=1 nf=1 
m32 net0157 net0106 vdd vdd pmos l=60e-9 w=1e-6 m=1 nf=1 
m28 net0104 b<2> vdd vdd pmos l=60e-9 w=1e-6 m=1 nf=1 
m27 net0105 b<1> vdd vdd pmos l=60e-9 w=1e-6 m=1 nf=1 
m26 net0106 b<0> vdd vdd pmos l=60e-9 w=1e-6 m=1 nf=1 
m19 b3_inv b<3> vdd vdd pmos l=60e-9 w=1e-6 m=1 nf=1 
m17 b3_buf b3_inv vdd vdd pmos l=60e-9 w=1e-6 m=1 nf=1 
m14 b2_buf b2_inv vdd vdd pmos l=60e-9 w=1e-6 m=1 nf=1 
m12 b2_inv b<2> vdd vdd pmos l=60e-9 w=1e-6 m=1 nf=1 
m10 b1_buf b1_inv vdd vdd pmos l=60e-9 w=1e-6 m=1 nf=1 
m8 b1_inv b<1> vdd vdd pmos l=60e-9 w=1e-6 m=1 nf=1 
m6 b0_buf b0_inv vdd vdd pmos l=60e-9 w=1e-6 m=1 nf=1 
m5 b0_inv b<0> vdd vdd pmos l=60e-9 w=1e-6 m=1 nf=1 
xi16 b1_inv net3 vss res_24K
xi17 b1_inv net1 vss res_24K
xi18 b0_inv net2 vss res_24K
xi19 b0_inv net4 vss res_24K
.ends capbank_gp_lowC_noLSB_9u_2BITS
** End of subcircuit definition.

** Library name: PhasedArray_WB_copy
** Cell name: BPF6_10G_2BITS
** View name: schematic
xc4 outm vtune vss moscap wr=2e-6 lr=500e-9 br=4 gr=4 m=1
xc0 outp vtune vss moscap wr=2e-6 lr=500e-9 br=4 gr=4 m=1
xm20 outp outm vss vss nmos lr=120e-9 wr=2.5e-6 nr=10 sigma=1 m=1 
xm19 outm outp vss vss nmos lr=120e-9 wr=2.5e-6 nr=10 sigma=1 m=1 
xm2 outp inm vss vss nmos lr=120e-9 wr=2.5e-6 nr=8 sigma=1 m=1 
xm8 outm inp vss vss nmos lr=120e-9 wr=2.5e-6 nr=8 sigma=1 m=1 
xi5 dig_bpf<3> dig_bpf<2> dig_bpf<1> dig_bpf<0> outm outp vddsw vss capbank_gp_lowC_noLSB_9u_2BITS
xl4 outm outp vss vdd_bpf0p5 spiral_sym_ct_mu_z w=9e-6 nr=2 rad=35.5e-6 
.END
