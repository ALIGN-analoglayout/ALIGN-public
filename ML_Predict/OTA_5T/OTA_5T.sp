.subckt OTA_5T n0 vss vdd n3 n9 n10
m3 n3 n9 n1 n1 nfet m=1 l=14n nfin=40 nf=2
m2 n2 n10 n1 n1 nfet m=1 l=14n nfin=40 nf=2
m0 n0 n0 vss vss nfet m=1 l=14n nfin=6 nf=2
m1 n1 n0 vss vss nfet m=1 l=14n nfin=6 nf=6
m5 n3 n2 vdd vdd pfet m=1 l=14n nfin=16 nf=2
m4 n2 n2 vdd vdd pfet m=1 l=14n nfin=16 nf=2
.ends OTA_5T
