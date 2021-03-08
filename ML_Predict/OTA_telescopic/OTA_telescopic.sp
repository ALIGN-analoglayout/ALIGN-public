
.subckt OTA_telescopic vdd vss n9 n10 vbiasn vbiasp n1 n6
M05 n6 vbiasn n3 n3 nfet m=1 l=14e-9 nfin=25 nf=2 par=1 par_nf=2
M06 n5 vbiasn n4 n4 nfet m=1 l=14e-9 nfin=25 nf=2 par=1 par_nf=2
M01 n1 n1 vss vss nfet m=1 l=14e-9 nfin=5 nf=2 par=1 par_nf=2
M02 n2 n1 vss vss nfet m=1 l=14e-9 nfin=40 nf=2 par=1 par_nf=2
M03 n3 n9 n2 n2 nfet m=1 l=14e-9 nfin=40 nf=2 par=1 par_nf=2
M04 n4 n10 n2 n2 nfet m=1 l=14e-9 nfin=40 nf=2 par=1 par_nf=2
M10 n8 n5 vdd vdd pfet m=1 l=14e-9 nfin=15 nf=2 par=1 par_nf=2
M09 n7 n5 vdd vdd pfet m=1 l=14e-9 nfin=15 nf=2 par=1 par_nf=2
M08 n6 vbiasp n8 n8 pfet m=1 l=14e-9 nfin=10 nf=2 par=1 par_nf=2
M07 n5 vbiasp n7 n7 pfet m=1 l=14e-9 nfin=10 nf=2 par=1 par_nf=2
.ends OTA_telescopic
