.subckt five_transistor_ota id vss vdd vout vinn vinp
m5 id id vss vss nmos_rvt w=270e-9 l=20e-9 nfin=5
m4 net10 id vss vss nmos_rvt w=270e-9 l=20e-9 nfin=5
m3 vout vinn net10 vss nmos_rvt w=270e-9 l=20e-9 nfin=5
m0 net8 vinp net10 vss nmos_rvt w=270e-9 l=20e-9 nfin=5
m2 vout net8 vdd vdd pmos_rvt w=270e-9 l=20e-9 nfin=5
m1 net8 net8 vdd vdd pmos_rvt w=270e-9 l=20e-9 nfin=5
.ends five_transistor_ota
