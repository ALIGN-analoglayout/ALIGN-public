.subckt ota_bias_asap7 d1 vdd vinn vinp vss vout
m9 vpgate vbiasn net8 vss nmos_rvt w=270e-9 l=20e-9 nfin=50
m8 vout vbiasn net014 vss nmos_rvt w=270e-9 l=20e-9 nfin=50
m5 d1 d1 vss vss nmos_rvt w=270e-9 l=20e-9 nfin=20
m4 net10 d1 vss vss nmos_rvt w=270e-9 l=20e-9 nfin=100
m3 net014 vinn net10 vss nmos_rvt w=270e-9 l=20e-9 nfin=140
m0 net8 vinp net10 vss nmos_rvt w=270e-9 l=20e-9 nfin=140
m7 vout vbiasp net012 vdd pmos_rvt w=270e-9 l=20e-9 nfin=80
m6 vpgate vbiasp net06 vdd pmos_rvt w=270e-9 l=20e-9 nfin=80
m2 net012 vpgate vdd vdd pmos_rvt w=270e-9 l=20e-9 nfin=40
m1 net06 vpgate vdd vdd pmos_rvt w=270e-9 l=20e-9 nfin=40
m10 vbiasn vbiasn net5 vss nmos_rvt w=270e-9 l=20e-9 nfin=7
m11 net5 vbiasn netm10 vss nmos_rvt w=270e-9 l=20e-9 nfin=10
m15 net9 d1 vss vss nmos_rvt w=270e-9 l=20e-9 nfin=10
m16 net9 net9 vdd vdd pmos_rvt w=270e-9 l=20e-9 nfin=10
m17 vbiasn net9 vdd vdd pmos_rvt w=270e-9 l=20e-9 nfin=10
m12 vbiasp d1 vss vss nmos_rvt w=270e-9 l=20e-9 nfin=10
m13 vbiasp vbiasp net7 vdd pmos_rvt w=270e-9 l=20e-9 nfin=5
m14 net7 vbiasp vdd vdd pmos_rvt w=270e-9 l=20e-9 nfin=10
.ends ota_bias_asap7



