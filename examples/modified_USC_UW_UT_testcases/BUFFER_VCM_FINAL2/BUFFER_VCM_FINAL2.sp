.subckt BUFFER_VCM_FINAL2 gnd ibias vcm_in vdd vout
xm2 net123 net123 gnd gnd nfet w=w0 l=l0
xm0 vout net132 gnd gnd nfet w=w1 l=l1
xm24 net065 net132 gnd gnd nfet w=w1 l=l1
xm25 net125 net132 gnd gnd nfet w=w1 l=l1
xm26 net138 net123 net065 gnd nfet w=w2 l=l1
xm27 net128 net123 net125 gnd nfet w=w2 l=l1
xm31 net132 net132 gnd gnd nfet w=w0 l=l1
xm6 net122 net132 gnd gnd nfet w=w0 l=l1
xm10 vout net065 vout vout pfet w=w3 l=l2
xm4 net138 net122 net051 vdd pfet w=w4 l=l1
xm5 net128 net122 net052 vdd pfet w=w4 l=l1
xm3 net123 ibias vdd vdd pfet w=w5 l=l1
xm1 vout net138 vdd vdd pfet w=w6 l=l1
xm17 net028 ibias vdd vdd pfet w=w7 l=l1
xm19 net065 vcm_in net028 vdd pfet w=w7 l=l1
xm21 net125 vout net028 vdd pfet w=w7 l=l1
xm29 ibias ibias vdd vdd pfet w=w8 l=l1
xm30 net132 ibias vdd vdd pfet w=w5 l=l1
xm32 net051 net128 vdd vdd pfet w=w9 l=l1
xm33 net052 net128 vdd vdd pfet w=w9 l=l1
xm7 net122 net122 vdd vdd pfet w=w10 l=l3
.ends BUFFER_VCM_FINAL2

