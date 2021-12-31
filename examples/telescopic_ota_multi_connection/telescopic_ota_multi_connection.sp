.subckt telescopic_ota_multi_connection d1 vdd vinn vinp vss vbiasn vbiasp1 vbiasp2 voutn voutp
m9 voutn vbiasn net8 vss nmos_rvt w=270e-9 l=20e-9 nfin=18 nf=2
m8 voutp vbiasn net014 vss nmos_rvt w=270e-9 l=20e-9 nfin=18 nf=2
m5 d1 d1 vss vss nmos_rvt w=270e-9 l=20e-9 nfin=12 nf=2
m4 net10 d1 vss vss nmos_rvt w=270e-9 l=20e-9 nfin=18 nf=2
m3 net014 vinn net10 vss nmos_rvt w=270e-9 l=20e-9 nfin=54 nf=2
m0 net8 vinp net10 vss nmos_rvt w=270e-9 l=20e-9 nfin=54 nf=2
m7 voutp vbiasp2 net06 vdd pmos_rvt w=270e-9 l=20e-9 nfin=12 nf=2
m6 voutn vbiasp2 net06 vdd pmos_rvt w=270e-9 l=20e-9 nfin=12 nf=2
m2 net06 vbiasp1 vdd vdd pmos_rvt w=270e-9 l=20e-9 nfin=6 nf=2
m1 net06 vbiasp1 vdd vdd pmos_rvt w=270e-9 l=20e-9 nfin=6 nf=2
.ends telescopic_ota_multi_connection
