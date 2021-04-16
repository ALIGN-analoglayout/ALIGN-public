.subckt sc_dc_dc_converter phi1 phi2 vout vin vss 
m8 vout phi1 net7 vss nmos_rvt w=270e-6 l=20e-9 nfin=10e3
m7 net7 phi2 vss vss nmos_rvt w=270e-6 l=20e-9 nfin=10e3
m6 vout phi2 net8 vss nmos_rvt w=270e-6 l=20e-9 nfin=10e3
m5 net9 phi1 net8 vss nmos_rvt w=270e-6 l=20e-9 nfin=10e3
m4 net9 phi2 vss vss nmos_rvt w=270e-6 l=20e-9 nfin=10e3
m3 vout phi2 net10 vss nmos_rvt w=270e-6 l=20e-9 nfin=10e3
m0 net10 phi1 vin vss nmos_rvt w=270e-6 l=20e-9 nfin=10e3
c1 net8 net7 1e-12
c0 net10 net9 1e-12
.ends sc_dc_dc_converter
