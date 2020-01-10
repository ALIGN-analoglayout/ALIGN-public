.subckt sc_dc_dc_converter phi1 phi2 phi2_bar vout vin vss vdd
xp5 net2 phi2 vout vdd pmos m=1 l=14e-9 nfin=40 nf=10
xp3 net4 phi2 vout vdd pmos m=1 l=14e-9 nfin=40 nf=10
xp2 net1 phi1 vout vdd pmos m=1 l=14e-9 nfin=40 nf=10
xp1 net2 phi1 net03 vdd pmos m=1 l=14e-9 nfin=40 nf=10
xp0 vin phi1 net4 vdd pmos m=1 l=14e-9 nfin=40 nf=10
c1 net2 net1 200e-12
c0 net4 net03 200e-12
xn0 net1 phi2_bar 0 vss nmos m=1 l=14e-9 nfin=40 nf=10
xp4 net03 phi2_bar 0 vss nmos m=1 l=14e-9 nfin=40 nf=10
.ends
