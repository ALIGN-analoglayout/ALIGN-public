* label = OTA
.subckt Gm1_v5_Practice ibias vdd vim vip vom vop vss
m8 net074 ntail1 vss vss hvtnfet w=w0 l=l0
m2 vdd ibias vdd vdd lvtpfet w=w1 l=l1
m4 vdd ibias vdd vdd lvtpfet w=w1 l=l1
m12 ibias ibias vdd vdd lvtpfet w=w2 l=l0
m11 vom ibias vdd vdd lvtpfet w=w3 l=l0
m15 ibias ibias vdd vdd lvtpfet w=w2 l=l0
m14 vop ibias vdd vdd lvtpfet w=w3 l=l0
m26 vop vim net074 net074 lvtnfet w=w4 l=l0
m27 vom vip net074 net074 lvtnfet w=w4 l=l0
c21 ntail1 vom cap c=12f
c22 vop ntail1 cap c=12f
r12 ntail1 vop res r=100
r11 vom ntail1 res r=100
m3 vss ntail1 vss vss lvtnfet w=w5 l=l2
m0 vss ntail1 vss vss lvtnfet w=w5 l=l2
*d0 net074 vdd diode
*d1 vss vdd diode
.ends Gm1_v5_Practice
