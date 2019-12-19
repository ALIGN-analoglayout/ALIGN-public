.subckt BUFFER_VREFP_ZHU gnd ibias vdd vin_vrefp vrefp
xm30 net26 ibias gnd gnd nfet w=w0 l=l0
xm5 ibias ibias gnd gnd nfet w=w1 l=l0
xm4 net16 ibias gnd gnd nfet w=w0 l=l0
xm21 net030 ibias gnd gnd nfet w=w1 l=l0
xm1 net037 vin_vrefp net16 gnd nfet w=w2 l=l0
xm0 net14 net026 net16 gnd nfet w=w2 l=l0
xm3 net14 net14 vdd vdd pfet w=w3 l=l0
xm2 net037 net14 vdd vdd pfet w=w3 l=l0
xm8 vdd net030 vdd vdd pfet_lvt w=w4 l=l1
xm28 vrefp net26 vdd vdd pfet_lvt w=w5 l=l0
xm29 net26 net030 vrefp vdd pfet_lvt w=w6 l=l0
xm27 net030 net030 net026 vdd pfet_lvt w=w7 l=l0
xm15 net026 net037 vdd vdd pfet_lvt w=w8 l=l0
xm9 vdd net037 vdd vdd pfet_lvt w=w9 l=l2
.ends BUFFER_VREFP_ZHU

