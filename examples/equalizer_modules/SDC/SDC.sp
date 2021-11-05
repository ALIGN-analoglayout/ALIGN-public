
.subckt SDC vbias vd vgnd vin vps vs
    R2 vbias vin 20000
    R1 vs vgnd 5000
    R0 vps vd 5000
    M01 net11 vin vs vgnd n m=1 l=14n nfin=8 nf=1
    M00 vd vin net11 vgnd n m=1 l=14n nfin=8 nf=1
.ends SDC
