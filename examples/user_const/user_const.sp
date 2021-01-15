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
.subckt telescopic_ota d1 vdd vinn vinp vss vbiasn vbiasp1 vbiasp2 voutn voutp
m9 voutn vbiasn net8 vss nmos_rvt w=270e-9 l=20e-9 nfin=36
m8 voutp vbiasn net014 vss nmos_rvt w=270e-9 l=20e-9 nfin=36
m5 d1 d1 vss vss nmos_rvt w=270e-9 l=20e-9 nfin=24
m4 net10 d1 vss vss nmos_rvt w=270e-9 l=20e-9 nfin=36
m3 net014 vinn net10 vss nmos_rvt w=270e-9 l=20e-9 nfin=72
m0 net8 vinp net10 vss nmos_rvt w=270e-9 l=20e-9 nfin=72
m7 voutp vbiasp2 net012 net012 pmos_rvt w=270e-9 l=20e-9 nfin=24
m6 voutn vbiasp2 net06 net06 pmos_rvt w=270e-9 l=20e-9 nfin=24
m2 net012 vbiasp1 vdd vdd pmos_rvt w=270e-9 l=20e-9 nfin=12
m1 net06 vbiasp1 vdd vdd pmos_rvt w=270e-9 l=20e-9 nfin=12
.ends telescopic_ota
** End of subcircuit definition.

** Library name: ALIGN_circuits_ASAP7nm
.subckt user_const D G S D1 G1 
xi0 S vdd D G vss D1 G1 vbiasp voutn voutp telescopic_ota
m0 D G S vss nmos_rvt w=270e-9 l=20e-9 nfin=12
m1 D1 G1 S vss nmos_rvt w=270e-9 l=20e-9 nfin=12
c1 voutp vbiasp 30e-15
c0 G voutn 60e-15
.ends user_const
