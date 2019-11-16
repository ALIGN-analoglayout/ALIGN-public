.subckt ota_bias_asap7 d1 vdd vinn vinp vss vout
m9 vpgate vbiasn net8s vss nmos_rvt w=270e-9 l=20e-9 nfin=50
m9s net8s vbiasn net8 vss nmos_rvt w=270e-9 l=20e-9 nfin=50
m8 vout vbiasn net014s vss nmos_rvt w=270e-9 l=20e-9 nfin=50
m8s net014s vbiasn net014 vss nmos_rvt w=270e-9 l=20e-9 nfin=50
m5 d1 d1 netm5s vss nmos_rvt w=270e-9 l=20e-9 nfin=20
m5s netm5s d1 vss vss nmos_rvt w=270e-9 l=20e-9 nfin=20
m4 net10 d1 netm4s vss nmos_rvt w=270e-9 l=20e-9 nfin=100
m4s netm4s d1 vss vss nmos_rvt w=270e-9 l=20e-9 nfin=100
m3 net014 vinn netm3s vss nmos_rvt w=270e-9 l=20e-9 nfin=140
m3s netm3s vinn net10 vss nmos_rvt w=270e-9 l=20e-9 nfin=140
m0 net8 vinp netm0s vss nmos_rvt w=270e-9 l=20e-9 nfin=140
m0s netm0s vinp net10 vss nmos_rvt w=270e-9 l=20e-9 nfin=140
m7 vout vbiasp net012s vdd pmos_rvt w=270e-9 l=20e-9 nfin=80
m7s net012s vbiasp net012 vdd pmos_rvt w=270e-9 l=20e-9 nfin=80
m6 vpgate vbiasp net06s vdd pmos_rvt w=270e-9 l=20e-9 nfin=80
m6s net06s vbiasp net06 vdd pmos_rvt w=270e-9 l=20e-9 nfin=80
m2 net012 vpgate netm2s vdd pmos_rvt w=270e-9 l=20e-9 nfin=40
m2s netm2s vpgate vdd vdd pmos_rvt w=270e-9 l=20e-9 nfin=40
m1 net06 vpgate netm1s vdd pmos_rvt w=270e-9 l=20e-9 nfin=40
m1s netm1s vpgate vdd vdd pmos_rvt w=270e-9 l=20e-9 nfin=40
m10 vbiasn vbiasn net5s vss nmos_rvt w=270e-9 l=20e-9 nfin=7
m10s net5s vbiasn net5 vss nmos_rvt w=270e-9 l=20e-9 nfin=7
m11 net5 vbiasn netm11s vss nmos_rvt w=270e-9 l=20e-9 nfin=10
m11s netm11s vbiasn net10 vss nmos_rvt w=270e-9 l=20e-9 nfin=10
m15 net9 d1 netm15s vss nmos_rvt w=270e-9 l=20e-9 nfin=10
m15s netm15s d1 vss vss nmos_rvt w=270e-9 l=20e-9 nfin=10
m16 net9 net9 netm16s vdd pmos_rvt w=270e-9 l=20e-9 nfin=10
m16s netm16s net9 vdd vdd pmos_rvt w=270e-9 l=20e-9 nfin=10
m17 vbiasn net9 netm17s vdd pmos_rvt w=270e-9 l=20e-9 nfin=10
m17s netm17s net9 vdd vdd pmos_rvt w=270e-9 l=20e-9 nfin=10
m12 vbiasp d1 netm12s vss nmos_rvt w=270e-9 l=20e-9 nfin=10
m12s netm12s d1 vss vss nmos_rvt w=270e-9 l=20e-9 nfin=10
m13 vbiasp vbiasp netm13s vdd pmos_rvt w=270e-9 l=20e-9 nfin=5
m13s netm13s vbiasp net7 vdd pmos_rvt w=270e-9 l=20e-9 nfin=5
m14 net7 vbiasp netm14s vdd pmos_rvt w=270e-9 l=20e-9 nfin=10
m14s netm14s vbiasp vdd vdd pmos_rvt w=270e-9 l=20e-9 nfin=10
.ends ota_bias_asap7



