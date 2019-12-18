.subckt BUFFER_VCM_FINAL3 gnd ibias vcm_in vdd vout
xm22 net050 net050 gnd gnd nfet w=w0 l=l0
xm23 net053 net053 gnd gnd nfet w=w0 l=l0
xm24 net060 net053 gnd gnd nfet w=w1 l=l0
xm25 net061 net050 gnd gnd nfet w=w1 l=l0
xm26 vout net044 net060 gnd nfet w=w2 l=l0
xm27 net047 net044 net061 gnd nfet w=w2 l=l0
xm31 net044 net044 gnd gnd nfet w=w0 l=l1
xm3 net050 net050 net050 gnd nfet w=w3 l=l0
xm11 net044 net044 net044 gnd nfet w=w3 l=l1
xm4 net053 net053 net053 gnd nfet w=w3 l=l0
xm5 gnd gnd gnd gnd nfet w=w3 l=l0
xm7 vout vout vout gnd nfet w=w4 l=l0
xm9 net061 net061 net061 gnd nfet w=w5 l=l0
xm8 net047 net047 net047 gnd nfet w=w4 l=l0
xm12 gnd gnd gnd gnd nfet w=w3 l=l1
xm6 gnd gnd gnd gnd nfet w=w3 l=l0
xm10 net060 net060 net060 gnd nfet w=w5 l=l0
xm1 net052 net052 net052 vdd pfet w=w6 l=l0
xm2 net052 net052 net052 vdd pfet w=w6 l=l0
xm17 net052 ibias vdd vdd pfet w=w7 l=l0
xm18 net047 vcm_in net052 vdd pfet w=w8 l=l0
xm19 net053 vcm_in net052 vdd pfet w=w8 l=l0
xm20 vout vout net052 vdd pfet w=w8 l=l0
xm21 net050 vout net052 vdd pfet w=w8 l=l0
xm29 ibias ibias vdd vdd pfet w=w9 l=l0
xm30 net044 ibias vdd vdd pfet w=w10 l=l0
xm32 vout net047 vdd vdd pfet w=w5 l=l0
xm33 net047 net047 vdd vdd pfet w=w5 l=l0
xm0 vdd vdd vdd vdd pfet w=w11 l=l0
xm13 vdd vdd vdd vdd pfet w=w12 l=l0
.ends BUFFER_VCM_FINAL3

