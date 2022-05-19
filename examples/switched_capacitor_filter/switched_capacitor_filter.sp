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
m9 voutn vbiasn net8 vss nmos_rvt w=270e-9 l=20e-9 nfin=9 nf=4
m8 voutp vbiasn net014 vss nmos_rvt w=270e-9 l=20e-9 nfin=9 nf=4
m5 d1 d1 vss vss nmos_rvt w=270e-9 l=20e-9 nfin=6 nf=4
m4 net10 d1 vss vss nmos_rvt w=270e-9 l=20e-9 nfin=6 nf=6
m3 net014 vinn net10 vss nmos_rvt w=270e-9 l=20e-9 nfin=12 nf=6
m0 net8 vinp net10 vss nmos_rvt w=270e-9 l=20e-9 nfin=12 nf=6
m7 voutp vbiasp2 net012 net012 pmos_rvt w=270e-9 l=20e-9 nfin=12 nf=2
m6 voutn vbiasp2 net06 net06 pmos_rvt w=270e-9 l=20e-9 nfin=12 nf=2
m2 net012 vbiasp1 vdd vdd pmos_rvt w=270e-9 l=20e-9 nfin=6 nf=2
m1 net06 vbiasp1 vdd vdd pmos_rvt w=270e-9 l=20e-9 nfin=6 nf=2
.ends telescopic_ota
** End of subcircuit definition.

** Library name: ALIGN_circuits_ASAP7nm
** Cell name: switched_capacitor_filter_spice
** View name: schematic

.subckt switched_capacitor_filter voutn voutp vinp vinn id agnd vss vdd
m0 voutn phi1 net67 vss nmos_rvt w=270e-9 l=20e-9 nfin=6 nf=2
m7 net66 phi1 net63 vss nmos_rvt w=270e-9 l=20e-9 nfin=6 nf=2
m6 net72 phi1 vinn vss nmos_rvt w=270e-9 l=20e-9 nfin=6 nf=2
m3 agnd phi2 net67 vss nmos_rvt w=270e-9 l=20e-9 nfin=6 nf=2
m5 agnd phi2 net63 vss nmos_rvt w=270e-9 l=20e-9 nfin=6 nf=2
m4 net72 phi2 agnd vss nmos_rvt w=270e-9 l=20e-9 nfin=6 nf=2
m8 net60 phi2 agnd vss nmos_rvt w=270e-9 l=20e-9 nfin=6 nf=2
m11 agnd phi2 net68 vss nmos_rvt w=270e-9 l=20e-9 nfin=6 nf=2
m9 agnd phi2 net62 vss nmos_rvt w=270e-9 l=20e-9 nfin=6 nf=2
m10 net64 phi1 net62 vss nmos_rvt w=270e-9 l=20e-9 nfin=6 nf=2
m12 net60 phi1 vinp vss nmos_rvt w=270e-9 l=20e-9 nfin=6 nf=2
m14 voutp phi1 net68 vss nmos_rvt w=270e-9 l=20e-9 nfin=6 nf=2
xi0 id vdd net64 net66 vss vbiasn vbiasp1 vbiasp2 voutn voutp telescopic_ota
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
.ends switched_capacitor_filter
