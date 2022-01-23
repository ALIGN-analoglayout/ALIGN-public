.subckt VCM5 gnd ibias vcm vdd vout
m22 net80 net80 gnd gnd nfet w=w0 l=l0 nfin=4 nf=2
m23 net84 net84 gnd gnd nfet w=w0 l=l0 nfin=4 nf=2
m24 net92 net84 gnd gnd nfet w=w1 l=l0 nfin=4 nf=2
m25 net91 net80 gnd gnd nfet w=w1 l=l0 nfin=4 nf=2
m26 vout net039 net92 gnd nfet w=w2 l=l0 nfin=4 nf=2
m27 net77 net039 net91 gnd nfet w=w2 l=l0 nfin=4 nf=2
m31 net039 net039 gnd gnd nfet w=w0 l=l1 nfin=4 nf=2
m17 net022 ibias vdd vdd pfet w=w3 l=l0 nfin=4 nf=2
m18 net77 vcm net022 vdd pfet w=w4 l=l0 nfin=4 nf=2
m19 net84 vcm net022 vdd pfet w=w4 l=l0 nfin=4 nf=2
m20 vout vout net022 vdd pfet w=w4 l=l0 nfin=4 nf=2
m21 net80 vout net022 vdd pfet w=w4 l=l0 nfin=4 nf=2
m29 ibias ibias vdd vdd pfet w=w5 l=l0 nfin=4 nf=2
m30 net039 ibias vdd vdd pfet w=w6 l=l0 nfin=4 nf=2
m32 vout net77 vdd vdd pfet w=w7 l=l0 nfin=4 nf=2
m33 net77 net77 vdd vdd pfet w=w7 l=l0 nfin=4 nf=2
.ends VCM5

