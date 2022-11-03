** Generated for: hspiceD
** Generated on: Jun 19 10:29:58 2019
** Design library name: ALIGN_circuits_ASAP7nm
** Design cell name: switched_capacitor_filter_spice
** Design view name: schematic


.TEMP 25.0
.OPTION INGOLD=2 ARTIST=2 PSF=2 MEASOUT=1 PARHIER=LOCAL PROBE=0 MARCH=2 ACCURACY=1 POST
** Library name: ALIGN_circuits_ASAP7nm
** Cell name: telescopic_ota
** View name: schematic
.subckt telescopic_ota g_cm vdd vss vbiasn1 vbiasn2 vinn vinp dp_l dp_r
m13 net_l vbiasn1 vss vss nmos_rvt w=270e-9 l=20e-9 nfin=4 nf=8
m12 net_r vbiasn1 vss vss nmos_rvt w=270e-9 l=20e-9 nfin=4 nf=8
m11 dp_l vbiasn2 net_l vss nmos_rvt w=270e-9 l=20e-9 nfin=4 nf=8
m10 dp_r vbiasn2 net_r vss nmos_rvt w=270e-9 l=20e-9 nfin=4 nf=8
m9_cs cs_l dp_l vss vss nmos_rvt w=270e-9 l=20e-9 nfin=4 nf=16
m8_cs cs_r dp_r vss vss nmos_rvt w=270e-9 l=20e-9 nfin=4 nf=16
m7_dp dp_l vinn dp_s vdd pmos_rvt w=270e-9 l=20e-9 nfin=4 nf=24
m6_dp dp_r vinp dp_s vdd pmos_rvt w=270e-9 l=20e-9 nfin=4 nf=24
m5_cm cs_l g_cm vdd vdd pmos_rvt w=270e-9 l=20e-9 nfin=4 nf=2
m4_cm dp_s g_cm vdd vdd pmos_rvt w=270e-9 l=20e-9 nfin=8 nf=4
m3_cm vbiasn2 g_cm vdd vdd pmos_rvt w=270e-9 l=20e-9 nfin=4 nf=2
m2_cm cs_r g_cm vdd vdd pmos_rvt w=270e-9 l=20e-9 nfin=4 nf=2
m1_cm g_cm g_cm vdd vdd pmos_rvt w=270e-9 l=20e-9 nfin=4 nf=4
.ends telescopic_ota
** End of subcircuit definition.

** Library name: ALIGN_circuits_ASAP7nm
** Cell name: switched_capacitor_filter_spice
** View name: schematic
* .subckt CMF vbiasn1 vbiasn2 vo1 vo2 phi1 phi2 vss

* .ends CMF

.subckt sh_circuit phi1 phi2 vinn vinp vo1 vo2 vss vdd ibias
xi0 ibias vdd vss vbiasn1 vbiasn2 vinn vinp dp_l dp_r telescopic_ota
* xi1 vbiasn1 vbiasn2 vo1 vo2 phi1 phi2 vss CMF
C3 netr_l vo1 40e-15
C4 netr_r vo2 40e-15
R1 dp_l netr_r 1500
R0 dp_r netr_l 1500
m6 netl phi1 vbiasn2 vss nmos_rvt w=270e-9 l=20e-9 nfin=6 nf=2
m5 netr phi1 vbiasn2 vss nmos_rvt w=270e-9 l=20e-9 nfin=6 nf=2
m4 netc phi2 vbiasn1 vss nmos_rvt w=270e-9 l=20e-9 nfin=6 nf=2
m3 netc phi1 vbiasn2 vss nmos_rvt w=270e-9 l=20e-9 nfin=6 nf=2
m2 netl phi2 vo1 vss nmos_rvt w=270e-9 l=20e-9 nfin=6 nf=2
m1 netr phi2 vo2 vss nmos_rvt w=270e-9 l=20e-9 nfin=6 nf=2
c1 netc netl 20e-15
c0 netc netr 20e-15
m8 netvr vbiasn2 vss vss nmos_rvt w=270e-9 l=20e-9 nfin=6 nf=2
m7 vbiasn2 vbiasn2 netvr vss nmos_rvt w=270e-9 l=20e-9 nfin=6 nf=2
.ends sh_circuit
