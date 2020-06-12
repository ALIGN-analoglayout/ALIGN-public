.subckt BUFFER_VREFP_ZHU gnd ibias vdd vin_vrefp vrefp
m30 net26 ibias gnd gnd nfet w=w0 l=l0
m5 ibias ibias gnd gnd nfet w=w1 l=l0
m4 net16 ibias gnd gnd nfet w=w0 l=l0
m21 net030 ibias gnd gnd nfet w=w1 l=l0
m1 net037 vin_vrefp net16 gnd nfet w=w2 l=l0
m0 net14 net026 net16 gnd nfet w=w2 l=l0
m3 net14 net14 vdd vdd pfet w=w3 l=l0
m2 net037 net14 vdd vdd pfet w=w3 l=l0
m8 vdd net030 vdd vdd lvtpfet w=w4 l=l1
m28 vrefp net26 vdd vdd lvtpfet w=w5 l=l0
m29 net26 net030 vrefp vdd lvtpfet w=w6 l=l0
m27 net030 net030 net026 vdd lvtpfet w=w7 l=l0
m15 net026 net037 vdd vdd lvtpfet w=w8 l=l0
m9 vdd net037 vdd vdd lvtpfet w=w9 l=l2
.ends BUFFER_VREFP_ZHU

