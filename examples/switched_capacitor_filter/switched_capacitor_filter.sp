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
.subckt telescopic_ota d1 vdd vinn vinp vss vbiasn vbiasnd vbiasp1 vbiasp2 voutn voutp
m9 voutn vbiasn net8 vss nmos_rvt w=270e-9 l=20e-9 nfin=25
m8 voutp vbiasn net014 vss nmos_rvt w=270e-9 l=20e-9 nfin=25
m5 D1 D1 vss vss nmos_rvt w=270e-9 l=20e-9 nfin=10
m4 net10 vbiasnd vss vss nmos_rvt w=270e-9 l=20e-9 nfin=50
m3 net014 vinn net10 vss nmos_rvt w=270e-9 l=20e-9 nfin=70
m0 net8 vinp net10 vss nmos_rvt w=270e-9 l=20e-9 nfin=70
m7 voutp vbiasp2 net012 net012 pmos_rvt w=270e-9 l=20e-9 nfin=15
m6 voutn vbiasp2 net06 net06 pmos_rvt w=270e-9 l=20e-9 nfin=15
m2 net012 vbiasp1 vdd vdd pmos_rvt w=270e-9 l=20e-9 nfin=10
m1 net06 vbiasp1 vdd vdd pmos_rvt w=270e-9 l=20e-9 nfin=10
.ends telescopic_ota
** End of subcircuit definition.

** Library name: ALIGN_circuits_ASAP7nm
** Cell name: switched_capacitor_filter_spice
** View name: schematic
m0 voutn phi1 net67 vss nmos_rvt w=270e-9 l=20e-9 nfin=5
m7 net66 phi1 net63 vss nmos_rvt w=270e-9 l=20e-9 nfin=5
m6 net72 phi1 vinn vss nmos_rvt w=270e-9 l=20e-9 nfin=5
m3 agnd phi2 net67 vss nmos_rvt w=270e-9 l=20e-9 nfin=5
m5 agnd phi2 net63 vss nmos_rvt w=270e-9 l=20e-9 nfin=5
m4 net72 phi2 agnd vss nmos_rvt w=270e-9 l=20e-9 nfin=5
m8 net60 phi2 agnd vss nmos_rvt w=270e-9 l=20e-9 nfin=5
m11 agnd phi2 net68 vss nmos_rvt w=270e-9 l=20e-9 nfin=5
m9 agnd phi2 net62 vss nmos_rvt w=270e-9 l=20e-9 nfin=5
m10 net64 phi1 net62 vss nmos_rvt w=270e-9 l=20e-9 nfin=5
m12 net60 phi1 vinp vss nmos_rvt w=270e-9 l=20e-9 nfin=5
m14 voutp phi1 net68 vss nmos_rvt w=270e-9 l=20e-9 nfin=5
xi0 id vdd net64 net66 vss vbiasn vbiasnd vbiasp1 vbiasp2 voutn voutp telescopic_ota
c9 voutp vss 60e-15
c8 voutn vss 60e-15
c7 net62 net68 30e-15
c6 net64 voutp 60e-15
c5 vinn net64 30e-15
c4 net60 net62 60e-15
c3 net66 voutn 60e-15
c2 vinp net66 30e-15
c1 net63 net67 30e-15
c0 net72 net63 60e-15
.END
