.subckt BUFFER_VCM1 gnd vcm_in vdd vout vbias
xm6 net017 net95 gnd gnd nfet w=w0 l=l0
xm31 net95 net95 gnd gnd nfet w=w0 l=l0
xm27 net92 net106 net89 gnd nfet w=w1 l=l0
xm26 net105 net106 net101 gnd nfet w=w1 l=l0
xm25 net89 net95 gnd gnd nfet w=w2 l=l0
xm24 net101 net95 gnd gnd nfet w=w2 l=l0
xm0 vout net95 gnd gnd nfet w=w2 l=l0
xm2 net106 net106 gnd gnd nfet w=w3 l=l0
xm7 net017 net017 vdd vdd pfet w=w4 l=l0
xm33 net91 net92 vdd vdd pfet w=w5 l=l0
xm32 net99 net92 vdd vdd pfet w=w5 l=l0
xm30 net95 vbias vdd vdd pfet w=w6 l=l0
xm29 vbias vbias vdd vdd pfet w=w6 l=l0
xm21 net89 vout net96 net96 pfet w=w7 l=l0
xm19 net101 vcm_in net96 net96 pfet w=w7 l=l0
xm17 net96 vbias vdd vdd pfet w=w6 l=l0
xm1 vout net105 vdd vdd pfet w=w8 l=l0
xm3 net106 vbias vdd vdd pfet w=w6 l=l0
xm5 net92 net017 net91 net91 pfet w=w9 l=l0
xm4 net105 net017 net99 net99 pfet w=w9 l=l0
.ends BUFFER_VCM1

