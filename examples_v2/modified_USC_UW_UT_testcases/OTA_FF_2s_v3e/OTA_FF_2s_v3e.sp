* label = OTA
.subckt OTA_FF_2s_v3e avdd avss ibin in ip on op vcas vcmi
m35 net057 ibin avdd avdd lvtpfet w=w0 l=l0
m34 cmfb vcmo net057 net057 lvtpfet w=w1 l=l0
m33 net044 vcmi net057 net057 lvtpfet w=w1 l=l0
m62 avdd ibin avdd avdd lvtpfet w=w2 l=l0
m54 net59 net59 net59 net59 lvtpfet w=w3 l=l0
m43 net5 net5 net5 net5 lvtpfet w=w4 l=l0
m53 avdd ibin avdd avdd lvtpfet w=w4 l=l0
m57 avdd ibin avdd avdd lvtpfet w=w0 l=l0
m37 op in net59 net59 lvtpfet w=w5 l=l0
m23 on ip net59 net59 lvtpfet w=w5 l=l0
m63 net75 vcas net75 net75 lvtpfet w=w6 l=l0
m58 net057 vcmo net057 net057 lvtpfet w=w1 l=l0
m36 net59 ibin avdd avdd lvtpfet w=w7 l=l0
m41 avdd ibin avdd avdd lvtpfet w=w8 l=l0
m16 ibin vcas net75 net75 lvtpfet w=w0 l=l0
m50 on1 ip net5 net5 lvtpfet w=w1 l=l0
m48 net057 vcmi net057 net057 lvtpfet w=w4 l=l0
m6 net75 ibin avdd avdd lvtpfet w=w0 l=l0
m4 net5 ibin avdd avdd lvtpfet w=w0 l=l0
m20 op1 in net5 net5 lvtpfet w=w1 l=l0
m7 avss op1 avss avss lvtnfet w=w9 l=l1
m2 avss on1 avss avss lvtnfet w=w9 l=l1
m0 avss cmfb avss avss lvtnfet w=w0 l=l0
m66 avss on1 avss avss lvtnfet w=w10 l=l0
m64 avss op1 avss avss lvtnfet w=w10 l=l0
m55 avss avss avss avss lvtnfet w=w10 l=l0
m21 on op1 avss avss lvtnfet w=w11 l=l0
m19 op on1 avss avss lvtnfet w=w11 l=l0
m29 cmfb cmfb avss avss lvtnfet w=w12 l=l0
m14 op1 cmfb avss avss lvtnfet w=w12 l=l0
m13 on1 cmfb avss avss lvtnfet w=w12 l=l0
m59 avss net044 avss avss lvtnfet w=w10 l=l0
m30 net044 net044 avss avss lvtnfet w=w12 l=l0
m56 avss cmfb avss avss lvtnfet w=w10 l=l0
c4 on vcmo cap cap=10f
c5 op vcmo cap cap=10f
r12_1__dmy0 vcmo xr12_1__dmy0 res res=100
r12_2__dmy0 xr12_1__dmy0 xr12_2__dmy0 res res=100
r12_3__dmy0 xr12_2__dmy0 xr12_3__dmy0 res res=100
r12_4__dmy0 xr12_3__dmy0 op res res=100
r13_1__dmy0 on xr13_1__dmy0 res res=100
r13_2__dmy0 xr13_1__dmy0 xr13_2__dmy0 res res=100
r13_3__dmy0 xr13_2__dmy0 xr13_3__dmy0 res res=100
r13_4__dmy0 xr13_3__dmy0 vcmo res res=100
.ends OTA_FF_2s_v3e

