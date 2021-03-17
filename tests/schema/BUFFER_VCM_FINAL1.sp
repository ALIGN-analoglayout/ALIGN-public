.subckt BUFFER_VCM_FINAL1 gnd ibias vcm_in vdd vout
m2 net123 net123 gnd gnd nfet w=w0 l=l0
m0 vout net132 gnd gnd nfet w=w1 l=l0
m24 net065 net132 gnd gnd nfet w=w1 l=l0
m25 net125 net132 gnd gnd nfet w=w1 l=l0
m26 net138 net123 net065 gnd nfet w=w2 l=l0
m27 net128 net123 net125 gnd nfet w=w2 l=l0
m31 net132 net132 gnd gnd nfet w=w3 l=l0
m6 net122 net132 gnd gnd nfet w=w3 l=l0
m10 vout net065 vout vout pfet w=w4 l=l1
m4 net138 net122 net051 vdd pfet w=w5 l=l0
m5 net128 net122 net052 vdd pfet w=w5 l=l0
m3 net123 ibias vdd vdd pfet w=w4 l=l0
m1 vout net138 vdd vdd pfet w=w6 l=l0
m17 net028 ibias vdd vdd pfet w=w4 l=l0
m19 net065 vcm_in net028 vdd pfet w=w7 l=l0
m21 net125 vout net028 vdd pfet w=w7 l=l0
m29 ibias ibias vdd vdd pfet w=w4 l=l0
m30 net132 ibias vdd vdd pfet w=w4 l=l0
m32 net051 net128 vdd vdd pfet w=w8 l=l0
m33 net052 net128 vdd vdd pfet w=w8 l=l0
m7 net122 net122 vdd vdd pfet w=w9 l=l0
.ends BUFFER_VCM_FINAL1

