.subckt BUFFER_VCM_FINAL gnd ibias vcm_in vdd vout
xm2 net123 net123 gnd gnd nfet w=w0 l=l0
xm0 vout net132 gnd gnd nfet w=w1 l=l0
xm24 net065 net132 gnd gnd nfet w=w1 l=l0
xm25 net125 net132 gnd gnd nfet w=w1 l=l0
xm26 net138 net123 net065 gnd nfet w=w2 l=l0
xm27 net128 net123 net125 gnd nfet w=w2 l=l0
xm31 net132 net132 gnd gnd nfet w=w3 l=l0
xm6 net122 net132 gnd gnd nfet w=w3 l=l0
xm10 vout net065 vout vout pfet w=w4 l=l1
xm4 net138 net122 net137 net137 pfet w=w5 l=l0
xm5 net128 net122 net127 net127 pfet w=w5 l=l0
xm3 net123 ibias vdd vdd pfet w=w4 l=l0
xm1 vout net138 vdd vdd pfet w=w6 l=l0
xm17 net133 ibias vdd vdd pfet w=w4 l=l0
xm19 net065 vcm_in net133 net133 pfet w=w7 l=l0
xm21 net125 vout net133 net133 pfet w=w7 l=l0
xm29 ibias ibias vdd vdd pfet w=w4 l=l0
xm30 net132 ibias vdd vdd pfet w=w4 l=l0
xm32 net137 net128 vdd vdd pfet w=w8 l=l0
xm33 net127 net128 vdd vdd pfet w=w8 l=l0
xm7 net122 net122 vdd vdd pfet w=w9 l=l0
.ends BUFFER_VCM_FINAL

