** Generated for: hspiceD
** Generated on: Jan  5 21:00:24 2020
** Design library name: PhasedArray_WB_copy
** Design cell name: ILO_10G_2BITS
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
xc3 right net3 vss mimcap lt=9e-6 wt=9e-6 
xc2 left net1 vss mimcap lt=9e-6 wt=9e-6 
xc1 right net4 vss mimcap lt=9e-6 wt=9e-6 
xc0 left net2 vss mimcap lt=9e-6 wt=9e-6 
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
** Cell name: VCO_10G_2BITS
** View name: schematic
.subckt VCO_10G_2BITS dig_vco<3> dig_vco<2> dig_vco<1> dig_vco<0> outm outp vddsw vdd_vco0p5 vss vtune
xc4 outm vtune vss moscap_rf_nw wr=2e-6 lr=500e-9 br=4 gr=4 m=1
xc0 outp vtune vss moscap_rf_nw wr=2e-6 lr=500e-9 br=4 gr=4 m=1
xm0 outp outm vss vss nmos lr=60e-9 wr=1e-6 nr=25 sigma=1 m=2 
xm1 outm outp vss vss nmos lr=60e-9 wr=1e-6 nr=25 sigma=1 m=2 
xi10 dig_vco<3> dig_vco<2> dig_vco<1> dig_vco<0> outm outp vddsw vss capbank_gp_lowC_noLSB_9u_2BITS
xl0 outp outm vss vdd_vco0p5 ind w=9e-6 nr=2 rad=35.5e-6 
.ends VCO_10G_2BITS
** End of subcircuit definition.

** Library name: PhasedArray_WB_copy
** Cell name: ILO_IN_V5_CROSS
** View name: schematic
.subckt ILO_IN_V5_CROSS in out out_aux vddsw vss
xc2 in net3 vss mimcap lt=20e-6 wt=20e-6 
xr4 vss net08 vss resistor l=6e-6 w=1e-6 m=1 
xr3 vss net3 vss resistor l=12e-6 w=1e-6 m=1 
xr2 net3 vddsw vss resistor l=12e-6 w=1e-6 m=1 
xm0 out_aux net3 net08 net08 nmos lr=60e-9 wr=2e-6 nr=18 sigma=1 m=1 
xm3 out net3 vss vss nmos lr=60e-9 wr=2e-6 nr=20 sigma=1 m=1 
.ends ILO_IN_V5_CROSS
** End of subcircuit definition.

** Library name: PhasedArray_WB_copy
** Cell name: ILO_10G_2BITS
** View name: schematic
xi11 dig_vco<3> dig_vco<2> dig_vco<1> dig_vco<0> outm outp vddsw vdd_vco0p5 vss vtune VCO_10G_2BITS
xi12 inp outm outp vddsw vss ILO_IN_V5_CROSS
xi13 inm outp outm vddsw vss ILO_IN_V5_CROSS
.END
