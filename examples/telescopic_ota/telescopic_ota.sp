.subckt telescopic_ota d1 vdd vinn vinp vss vbiasn vbiasnd vbiasp1 vbiasp2 voutn voutp
m9 voutn vbiasn net8 vss nmos_rvt w=270e-9 l=20e-9 nfin=36
m8 voutp vbiasn net014 vss nmos_rvt w=270e-9 l=20e-9 nfin=36
m5 d1 d1 vss vss nmos_rvt w=270e-9 l=20e-9 nfin=24
m4 net10 vbiasnd vss vss nmos_rvt w=270e-9 l=20e-9 nfin=36
m3 net014 vinn net10 vss nmos_rvt w=270e-9 l=20e-9 nfin=108
m0 net8 vinp net10 vss nmos_rvt w=270e-9 l=20e-9 nfin=108
m7 voutp vbiasp2 net012 net012 pmos_rvt w=270e-9 l=20e-9 nfin=24
m6 voutn vbiasp2 net06 net06 pmos_rvt w=270e-9 l=20e-9 nfin=24
m2 net012 vbiasp1 vdd vdd pmos_rvt w=270e-9 l=20e-9 nfin=12
m1 net06 vbiasp1 vdd vdd pmos_rvt w=270e-9 l=20e-9 nfin=12
.ends telescopic_ota
