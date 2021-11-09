

.subckt CTLE vmirror_ctle vgnd vin1_ctle vin2_ctle vout1_ctle vout2_ctle vps
    MDP00 vout2_ctle vin2_ctle n1 vgnd n nfin=12 nf=2
    MDP01 n1 vin2_ctle n2 vgnd n nfin=12 nf=2

    MDP10 vout1_ctle vin1_ctle n3 vgnd n nfin=12 nf=2
    MDP11 n3 vin1_ctle n4 vgnd n nfin=12 nf=2

    MCM00 vmirror_ctle vmirror_ctle n5 vgnd n nfin=10 nf=4
    MCM01 n5 vmirror_ctle vgnd vgnd n nfin=10 nf=4

    MCM10 n2 vmirror_ctle n6 vgnd n nfin=10 nf=4
	MCM11 n6 vmirror_ctle vgnd vgnd n nfin=10 nf=4
    MCM20 n4 vmirror_ctle n8 vgnd n nfin=10 nf=4
    MCM21 n8 vmirror_ctle vgnd vgnd n nfin=10 nf=4

	R1 vps vout2_ctle 800
    R0 vps vout1_ctle 800
    R4 n2 n4 3K

.ends CTLE
