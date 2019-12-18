.subckt VCM4 gnd ibias vcm vdd vfb
xm0 vfb net84 gnd gnd nfet w=w0 l=l0
xm2 net84 net80 gnd gnd nfet w=w1 l=l0
xm3 net80 net80 gnd gnd nfet w=w1 l=l0
xm1 vfb ibias vdd vdd pfet w=w2 l=l0
xm17 net022 ibias vdd vdd pfet w=w3 l=l0
xm19 net84 vcm net022 vdd pfet w=w4 l=l0
xm21 net80 vfb net022 vdd pfet w=w4 l=l0
xm29 ibias ibias vdd vdd pfet w=w5 l=l0
xm4 vfb net84 vfb vfb pfet w=w6 l=l1
.ends VCM4

