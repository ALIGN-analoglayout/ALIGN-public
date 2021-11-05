

.subckt CTLE vmirror_ctle vgnd vin1_ctle vin2_ctle vout1_ctle vout2_ctle vps
    C3 net5 net022 400f
    M13 net19 vmirror_ctle vgnd vgnd n m=1 l=14n nfin=10 nf=4
    M12 vmirror_ctle vmirror_ctle net19 vgnd n m=1 l=14n nfin=10 nf=4
    M11 net18 vmirror_ctle vgnd vgnd n m=1 l=14n nfin=10 nf=4
    M10 net022 vmirror_ctle net18 vgnd n m=1 l=14n nfin=10 nf=4
    M9 net15 vmirror_ctle vgnd vgnd n m=1 l=14n nfin=10 nf=4
    M8 net5 vmirror_ctle net15 vgnd n m=1 l=14n nfin=10 nf=4
    M7 net14 vin2_ctle net022 vgnd n m=1 l=14n nfin=12 nf=2
    M6 vout2_ctle vin2_ctle net14 vgnd n m=1 l=14n nfin=12 nf=2
    M1 net17 vin1_ctle net5 vgnd n m=1 l=14n nfin=12 nf=2
    M0 vout1_ctle vin1_ctle net17 vgnd n m=1 l=14n nfin=12 nf=2
    R1 vps vout2_ctle 800
    R0 vps vout1_ctle 800
    R4 net5 net022 3K
.ends CTLE
