
.subckt two_stage_ota id vdd vinn vinp vout vss
mn6 net3 id vss vss nfet nf=4 m=1 l=14e-9 nfin=2 stack=2
mn3 id id vss vss nfet nf=2 m=1 l=14e-9 nfin=2 stack=2
mn7 vout id vss vss nfet nf=6 m=1 l=14e-9 nfin=2 stack=2
mn1 net33 vinp net3 vss nfet nf=8 m=1 l=14e-9 nfin=4 stack=2
mn0 net1 vinn net3 vss nfet nf=8 m=1 l=14e-9 nfin=4 stack=2
mp2 vout net33 vdd vdd pfet nf=10 m=1 l=14e-9 nfin=6 stack=2
mp1 net33 net1 vdd vdd pfet nf=2 m=1 l=14e-9 nfin=4 stack=2
mp0 net1 net1 vdd vdd pfet nf=2 m=1 l=14e-9 nfin=4 stack=2
c0 net2 vout 1e-12
r0 net33 net2 1.5e3
.ends two_stage_ota
