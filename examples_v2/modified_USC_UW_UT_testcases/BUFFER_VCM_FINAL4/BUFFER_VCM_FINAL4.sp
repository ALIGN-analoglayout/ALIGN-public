.subckt BUFFER_VCM_FINAL4 gnd ibias vcm_in vdd vout
m17 net023 net023 net023 gnd nfet w=w0 l=l0
m18 gnd gnd gnd gnd nfet w=w0 l=l0
m19 net049 net049 net049 gnd nfet w=w0 l=l0
m20 gnd gnd gnd gnd nfet w=w0 l=l0
m16 vout net049 gnd gnd nfet w=w1 l=l0
m21 gnd gnd gnd gnd nfet w=w2 l=l0
m15 net049 net023 gnd gnd nfet w=w3 l=l0
m14 net023 net023 gnd gnd nfet w=w3 l=l0
m39 vdd vdd vdd vdd pfet w=w4 l=l0
m40 vdd vdd vdd vdd pfet w=w5 l=l0
m41 net048 net048 net048 vdd pfet w=w6 l=l0
m42 net048 net048 net048 vdd pfet w=w6 l=l0
m43 vdd vdd vdd vdd pfet w=w4 l=l0
m36 net049 vcm_in net048 vdd pfet w=w7 l=l0
m28 vout net049 vout vout pfet w=w8 l=l1
m38 ibias ibias vdd vdd pfet w=w9 l=l0
m37 net023 vout net048 vdd pfet w=w7 l=l0
m35 net048 ibias vdd vdd pfet w=w10 l=l0
m34 vout ibias vdd vdd pfet w=w4 l=l0
.ends BUFFER_VCM_FINAL4

