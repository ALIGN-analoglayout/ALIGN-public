.subckt pcell_tfr_0 a b
xi0 a b tfr_prim w=1e-6 l=1e-6
.ends pcell_tfr_0

.subckt tia vin vop vcc vss
mp0 vop vin vcc vcc p nfin=4 nf=4 m=4
mn0 vop vin vss vss n nfin=4 nf=4 m=4
xi0 vin vop pcell_tfr_0
.ends tia
