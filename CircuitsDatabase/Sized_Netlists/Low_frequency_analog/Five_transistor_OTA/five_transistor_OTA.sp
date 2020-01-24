.subckt five_transistor_OTA vinn_ota vinp_ota vout_ota id_ota vdd_ota vss_ota
xp1 vout_ota net19 vdd_ota vdd_ota pmos m=5 l=14e-9 nfin=4 nf=1 
xp0 net19 net19 vdd_ota vdd_ota pmos m=5 l=14e-9 nfin=4 nf=1
xn3 id_ota id_ota vss_ota vss_ota nmos m=1 l=14e-9 nfin=8 nf=1
xn2 net017 id_ota vss_ota vss_ota nmos m=5 l=14e-9 nfin=8 nf=1
xn1 vout_ota vinn_ota net017 vss_ota nmos m=5 l=14e-9 nfin=18 nf=1
xn0 net19 vinp_ota net017 vss_ota nmos m=5 l=14e-9 nfin=18 nf=1
.ends
