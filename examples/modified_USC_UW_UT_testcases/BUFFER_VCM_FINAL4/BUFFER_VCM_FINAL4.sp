.subckt BUFFER_VCM_FINAL4 gnd ibias vcm_in vdd vout
xm17 net023 net023 net023 gnd nfet w=w0 l=l0
xm18 gnd gnd gnd gnd nfet w=w0 l=l0
xm19 net049 net049 net049 gnd nfet w=w0 l=l0
xm20 gnd gnd gnd gnd nfet w=w0 l=l0
xm16 vout net049 gnd gnd nfet w=w1 l=l0
xm21 gnd gnd gnd gnd nfet w=w2 l=l0
xm15 net049 net023 gnd gnd nfet w=w3 l=l0
xm14 net023 net023 gnd gnd nfet w=w3 l=l0
xm39 vdd vdd vdd vdd pfet w=w4 l=l0
xm40 vdd vdd vdd vdd pfet w=w5 l=l0
xm41 net048 net048 net048 vdd pfet w=w6 l=l0
xm42 net048 net048 net048 vdd pfet w=w6 l=l0
xm43 vdd vdd vdd vdd pfet w=w4 l=l0
xm36 net049 vcm_in net048 vdd pfet w=w7 l=l0
xm28 vout net049 vout vout pfet w=w8 l=l1
xm38 ibias ibias vdd vdd pfet w=w9 l=l0
xm37 net023 vout net048 vdd pfet w=w7 l=l0
xm35 net048 ibias vdd vdd pfet w=w10 l=l0
xm34 vout ibias vdd vdd pfet w=w4 l=l0
.ends BUFFER_VCM_FINAL4

