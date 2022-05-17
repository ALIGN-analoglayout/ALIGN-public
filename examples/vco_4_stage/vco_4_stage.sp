.subckt inv_unit_latch bot vss in out top vdd
mn0 out in bot vss nfet w=1680e-9 l=14n nfin=8 nf=6
mp1 out in top vdd pfet w=2100e-9 l=14n nfin=10 nf=6
.ends inv_unit_latch

.subckt inv_unit bot vss in out top vdd
mn0 out in bot vss nfet w=1680e-9 l=14n nfin=8 nf=12
mp1 out in top vdd pfet w=2100e-9 l=14n nfin=10 nf=12
.ends inv_unit

.subckt vco_unit bot vss inn inp outn outnp outp outpn top vdd
xi3 bot vss outp outpn top vdd inv_unit_latch
xi2 bot vss outn outnp top vdd inv_unit_latch
xi1 bot vss inn outp top vdd inv_unit
xi0 bot vss inp outn top vdd inv_unit
.ends vco_unit

.subckt vco_4_stage vss phin3 phin2 phin1 phin0 phip3 phip2 phip1 phip0 vctrl vdd
mp0 top vctrl vdd vdd pfet w=420e-9 l=14n nfin=2 nf=2 stack=14
xi3 vss vss phip2 phin2 phip3 phin3 phin3 phip3 top vdd vco_unit
xi2 vss vss phin1 phip1 phin2 phip2 phip2 phin2 top vdd vco_unit
xi1 vss vss phip0 phin0 phip1 phin1 phin1 phip1 top vdd vco_unit
xi0 vss vss phip3 phin3 phin0 phip0 phip0 phin0 top vdd vco_unit
.ends vco_4_stage
