.subckt BUFFER_VCM gnd vbias vdd vout vref
m0 vout net93 gnd gnd nfet w=w0 l=l0
m2 net019 net019 gnd gnd nfet w=w1 l=l0
m22 net99 net99 gnd gnd nfet w=w2 l=l0
m23 net103 net103 gnd gnd nfet w=w2 l=l0
m24 net107 net103 gnd gnd nfet w=w3 l=l0
m25 net114 net99 gnd gnd nfet w=w3 l=l0
m26 net111 net019 net107 gnd nfet w=w4 l=l0
m27 net96 net019 net114 gnd nfet w=w4 l=l0
m31 net93 net93 gnd gnd nfet w=w5 l=l0
m3 net019 vbias vdd vdd pfet w=w6 l=l0
m17 net102 vbias vdd vdd pfet w=w7 l=l0
m18 net96 vout net102 net102 pfet w=w8 l=l0
m19 net103 vout net102 net102 pfet w=w8 l=l0
m20 net111 vref net102 net102 pfet w=w8 l=l0
m21 net99 vref net102 net102 pfet w=w8 l=l0
m29 vbias vbias vdd vdd pfet w=w6 l=l0
m30 net93 vbias vdd vdd pfet w=w6 l=l0
m32 net111 net96 vdd vdd pfet w=w9 l=l0
m33 net96 net96 vdd vdd pfet w=w9 l=l0
m1 vout net111 vdd vdd pfet w=w10 l=l0
c1 net107 vout 5e-14
c0 vout gnd 1e-14
.ends BUFFER_VCM

