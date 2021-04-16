.subckt BUFFER_VCM1 gnd vcm_in vdd vout vbias
m6 net017 net95 gnd gnd nfet w=w0 l=l0
m31 net95 net95 gnd gnd nfet w=w0 l=l0
m27 net92 net106 net89 gnd nfet w=w1 l=l0
m26 net105 net106 net101 gnd nfet w=w1 l=l0
m25 net89 net95 gnd gnd nfet w=w2 l=l0
m24 net101 net95 gnd gnd nfet w=w2 l=l0
m0 vout net95 gnd gnd nfet w=w2 l=l0
m2 net106 net106 gnd gnd nfet w=w3 l=l0
m7 net017 net017 vdd vdd pfet w=w4 l=l0
m33 net91 net92 vdd vdd pfet w=w5 l=l0
m32 net99 net92 vdd vdd pfet w=w5 l=l0
m30 net95 vbias vdd vdd pfet w=w6 l=l0
m29 vbias vbias vdd vdd pfet w=w6 l=l0
m21 net89 vout net96 net96 pfet w=w7 l=l0
m19 net101 vcm_in net96 net96 pfet w=w7 l=l0
m17 net96 vbias vdd vdd pfet w=w6 l=l0
m1 vout net105 vdd vdd pfet w=w8 l=l0
m3 net106 vbias vdd vdd pfet w=w6 l=l0
m5 net92 net017 net91 net91 pfet w=w9 l=l0
m4 net105 net017 net99 net99 pfet w=w9 l=l0
.ends BUFFER_VCM1

