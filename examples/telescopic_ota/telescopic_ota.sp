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
