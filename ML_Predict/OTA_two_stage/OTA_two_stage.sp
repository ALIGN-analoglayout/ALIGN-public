
.subckt OTA_two_stage n0 n1 n9 n10 VOUT vdd vss
M6 VOUT n0 vss vss nfet m=1 l=14n nfin=5 nf=18 
M3 n3 n10 n1 n1 nfet m=1 l=14n nfin=40 nf=2 
M2 n2 n9 n1 n1 nfet m=1 l=14n nfin=40 nf=2 
M0 n0 n0 vss vss nfet m=1 l=14n nfin=5 nf=2 
M1 n1 n0 vss vss nfet m=1 l=14n nfin=5 nf=6 
M5 n3 n2 vdd vdd pfet m=1 l=14n nfin=15 nf=2 
M4 n2 n2 vdd vdd pfet m=1 l=14n nfin=15 nf=2 
M7 VOUT n3 vdd vdd pfet m=1 l=14n nfin=15 nf=12 
c0 VOUT n3 capacitor c=135.0f
.ends OTA_two_stage
