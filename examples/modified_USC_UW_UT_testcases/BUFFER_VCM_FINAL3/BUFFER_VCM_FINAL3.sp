.subckt BUFFER_VCM_FINAL3 gnd ibias vcm_in vdd vout
m22 net050 net050 gnd gnd nfet w=w0 l=l0
m23 net053 net053 gnd gnd nfet w=w0 l=l0
m24 net060 net053 gnd gnd nfet w=w1 l=l0
m25 net061 net050 gnd gnd nfet w=w1 l=l0
m26 vout net044 net060 gnd nfet w=w2 l=l0
m27 net047 net044 net061 gnd nfet w=w2 l=l0
m31 net044 net044 gnd gnd nfet w=w0 l=l1
m3 net050 net050 net050 gnd nfet w=w3 l=l0
m11 net044 net044 net044 gnd nfet w=w3 l=l1
m4 net053 net053 net053 gnd nfet w=w3 l=l0
m5 gnd gnd gnd gnd nfet w=w3 l=l0
m7 vout vout vout gnd nfet w=w4 l=l0
m9 net061 net061 net061 gnd nfet w=w5 l=l0
m8 net047 net047 net047 gnd nfet w=w4 l=l0
m12 gnd gnd gnd gnd nfet w=w3 l=l1
m6 gnd gnd gnd gnd nfet w=w3 l=l0
m10 net060 net060 net060 gnd nfet w=w5 l=l0
m1 net052 net052 net052 vdd pfet w=w6 l=l0
m2 net052 net052 net052 vdd pfet w=w6 l=l0
m17 net052 ibias vdd vdd pfet w=w7 l=l0
m18 net047 vcm_in net052 vdd pfet w=w8 l=l0
m19 net053 vcm_in net052 vdd pfet w=w8 l=l0
m20 vout vout net052 vdd pfet w=w8 l=l0
m21 net050 vout net052 vdd pfet w=w8 l=l0
m29 ibias ibias vdd vdd pfet w=w9 l=l0
m30 net044 ibias vdd vdd pfet w=w10 l=l0
m32 vout net047 vdd vdd pfet w=w5 l=l0
m33 net047 net047 vdd vdd pfet w=w5 l=l0
m0 vdd vdd vdd vdd pfet w=w11 l=l0
m13 vdd vdd vdd vdd pfet w=w12 l=l0
.ends BUFFER_VCM_FINAL3

