.subckt VCM4 gnd ibias vcm vdd vfb
m0 vfb net84 gnd gnd nfet w=w0 l=l0 nfin=4 nf=2
m2 net84 net80 gnd gnd nfet w=w1 l=l0 nfin=4 nf=2
m3 net80 net80 gnd gnd nfet w=w1 l=l0 nfin=4 nf=2
m1 vfb ibias vdd vdd pfet w=w2 l=l0 nfin=4 nf=2
m17 net022 ibias vdd vdd pfet w=w3 l=l0 nfin=4 nf=2
m19 net84 vcm net022 vdd pfet w=w4 l=l0 nfin=4 nf=2
m21 net80 vfb net022 vdd pfet w=w4 l=l0 nfin=4 nf=2
m29 ibias ibias vdd vdd pfet w=w5 l=l0 nfin=4 nf=2
m4 vfb net84 vfb vfb pfet w=w6 l=l1 nfin=4 nf=2
.ends VCM4

