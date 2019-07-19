.subckt cascode_current_mirror_ota id vbiasn vbiasnd vbiasp vinn vinp voutp vss vdd
m25 voutp vbiasn net034 vss nmos_rvt w=27e-9 l=20e-9 nfin=24
m24 vbiasnd vbiasn net033 vss nmos_rvt w=27e-9 l=20e-9 nfin=24
m17 net16 vinn net24 vss nmos_rvt w=27e-9 l=20e-9 nfin=30
m16 net24 id vss vss nmos_rvt w=27e-9 l=20e-9 nfin=15
m15 net27 vinp net24 vss nmos_rvt w=27e-9 l=20e-9 nfin=30
m14 id id vss vss nmos_rvt w=27e-9 l=20e-9 nfin=15
m11 net033 vbiasnd vss vss nmos_rvt w=27e-9 l=20e-9 nfin=30
m10 net034 vbiasnd vss vss nmos_rvt w=27e-9 l=20e-9 nfin=30

m1nup vbiasn vbiasn net9b vss nmos_rvt w=270e-9 l=20e-9 nfin=3
m1ndown net9b net9b vss vss nmos_rvt w=270e-9 l=20e-9 nfin=5

m1pup net8b net8b vdd vdd pmos_rvt w=270e-9 l=20e-9 nfin=5
m1pdown vbiasp vbiasp net8b vdd pmos_rvt w=270e-9 l=20e-9 nfin=5
m27 net27 vbiasp net021 vdd pmos_rvt w=27e-9 l=20e-9 nfin=60
m26 net16 vbiasp net015 vdd pmos_rvt w=27e-9 l=20e-9 nfin=60
m23 voutp vbiasp net024 vdd pmos_rvt w=27e-9 l=20e-9 nfin=120
m22 vbiasnd vbiasp net06 vdd pmos_rvt w=27e-9 l=20e-9 nfin=120
m21 net015 net16 vdd vdd pmos_rvt w=27e-9 l=20e-9 nfin=5
m20 net06 net16 vdd vdd pmos_rvt w=27e-9 l=20e-9 nfin=10
m19 net021 net27 vdd vdd pmos_rvt w=27e-9 l=20e-9 nfin=5
m18 net024 net27 vdd vdd pmos_rvt w=27e-9 l=20e-9 nfin=10
.ends cascode_current_mirror_ota
