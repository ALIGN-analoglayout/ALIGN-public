*label = Comparator
.subckt Comparator_1to7_0p7_lvt caln calp clke d db inm<0> inm<1> inp<0> inp<1> vb vdd vss
xm29 vout1p clk vdd vdd lvtpfet w=w0 l=l0
xm32 vout1m clk vdd vdd lvtpfet w=w0 l=l0
xm18 clk net043 vdd vdd lvtpfet w=w1 l=l0
xm19 net043 clke vdd vdd lvtpfet w=w2 l=l0
xm7 db vout2p vdd vdd lvtpfet w=w3 l=l0
xm28 vout2p vout2m vdd vdd lvtpfet w=w4 l=l1
xm38 vdd vss vdd vdd lvtpfet w=w2 l=l0
xm39 vdd vss vdd vdd lvtpfet w=w1 l=l0
xm34 vout2m vout2p vdd vdd lvtpfet w=w4 l=l1
xm25 vout2p clk vdd vdd lvtpfet w=w2 l=l0
xm8 d vout2m vdd vdd lvtpfet w=w3 l=l0
xm33 vout2m clk vdd vdd lvtpfet w=w2 l=l0
xm35 net058 clk net040 vss lvtnfet w=w5 l=l0
xm10 vout1m inp<0> net058 vss lvtnfet w=w6 l=l2
xm36 net040 vb vss vss lvtnfet w=w5 l=l0
xm9 d vout2m vss vss lvtnfet w=w7 l=l0
xm48 vss vdd vss vss lvtnfet w=w8 l=l3
xm41 vss vdd vss vss lvtnfet w=w7 l=l0
xm43 vss vdd vss vss lvtnfet w=w9 l=l0
xm42 vss vdd vss vss lvtnfet w=w2 l=l0
xm11 vout1p inm<0> net058 vss lvtnfet w=w6 l=l2
xm26 clk net043 vss vss lvtnfet w=w2 l=l0
xm14 vout2p vout2m vout1p vss lvtnfet w=w10 l=l1
xm12 vout1p inm<1> net057 vss lvtnfet w=w6 l=l2
xm37 net041 vb vss vss lvtnfet w=w5 l=l0
xm40 net057 clk net041 vss lvtnfet w=w5 l=l0
xm6 db vout2p vss vss lvtnfet w=w7 l=l0
xm27 net043 clke vss vss lvtnfet w=w7 l=l0
xm13 vout1m inp<1> net057 vss lvtnfet w=w6 l=l2
xm21 vout2m vout2p vout1m vss lvtnfet w=w10 l=l1
m1 vout2m calp vout2m vout2m lvtpfet w=w11 l=l4
m2 vout2p vss vout2p vout2p lvtpfet w=w12 l=l4
m3 vout2p caln vout2p vout2p lvtpfet w=w11 l=l4
m0 vout2m vss vout2m vout2m lvtpfet w=w12 l=l4
.ends Comparator_1to7_0p7_lvt

