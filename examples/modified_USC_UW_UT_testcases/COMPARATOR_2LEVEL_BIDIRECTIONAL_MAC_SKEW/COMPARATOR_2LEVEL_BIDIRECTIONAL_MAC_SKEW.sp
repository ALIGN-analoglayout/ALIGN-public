* label = Comparator
.subckt NR2D2BWP a1 a2 zn vdd vss
m0 zn a2 vss vss nfet w=w0 l=l0
m1 zn a1 vss vss nfet w=w0 l=l0
m2 zn a1 vss vss nfet w=w0 l=l0
m3 zn a2 vss vss nfet w=w0 l=l0
m4 zn a1 net17 vdd pfet w=w1 l=l0
m5 net25 a2 vdd vdd pfet w=w1 l=l0
m6 zn a1 net25 vdd pfet w=w1 l=l0
m7 net17 a2 vdd vdd pfet w=w1 l=l0
.ends NR2D2BWP

.subckt INVD0BWP i zn vdd vss
m0 zn i vss vss nfet w=w2 l=l0
m1 zn i vdd vdd pfet w=w3 l=l0
.ends INVD0BWP

.subckt CLK_BOOST_COMP bypass clk_boost clk_in gnd vdd
xm5 net8 net5 vdd vdd pfet w=w4 l=l0
xm4 clk_boost net6 net8 vdd pfet w=w4 l=l0
xm1 net5 net6 net8 vdd pfet w=w5 l=l0
xm6 clk_boost net6 clk_in gnd nfet w=w6 l=l0
xm2 net5 net6 net013 gnd nfet w=w5 l=l0
xi1 net6 bypass net013 vdd gnd NR2D2BWP
xi2 clk_in net6 vdd gnd INVD0BWP
xc2 net013 net8 vdd cap
xc3 net013 net8 vdd cap
.ends CLK_BOOST_COMP

.subckt COMPARATOR_2LEVEL_BIDIRECTIONAL_MAC_SKEW clk clkn fine fine_boost flip flipb gnd intern interp outm outp vdd _net0 _net1 vmid vmidb vxn vxn2 vxp vxp2
xi3 gnd fine_boost fine gnd vdd CLK_BOOST_COMP
xi4 gnd net073 vdd gnd INVD0BWP
xi0 clk clkb vdd gnd INVD0BWP
xm0 gnd net066 gnd gnd nfet w=w7 l=l1
xm1 gnd net065 gnd gnd nfet w=w7 l=l1
xm56 gnd gnd gnd gnd lvtnfet w=w5 l=l0
xm52 gnd gnd gnd gnd lvtnfet w=w5 l=l0
xm51 gnd gnd gnd gnd lvtnfet w=w5 l=l0
xm50 gnd gnd gnd gnd lvtnfet w=w5 l=l0
xm12 vxn fine_boost net065 gnd lvtnfet w=w6 l=l0
xm10 vxp fine_boost net066 gnd lvtnfet w=w6 l=l0
xm31 flipb flip gnd gnd lvtnfet w=w5 l=l0
xm16 outm intern gnd gnd lvtnfet w=w4 l=l0
xm21 flip clkb gnd gnd lvtnfet w=w5 l=l0
xm15 net05 clkn gnd gnd lvtnfet w=w6 l=l0
xm14 vxn _net0 net05 gnd lvtnfet w=w8 l=l0
xm32 clkn flip gnd gnd lvtnfet w=w5 l=l0
xm37 vxn2 flipb gnd gnd lvtnfet w=w5 l=l0
xm13 vxp _net1 net05 gnd lvtnfet w=w8 l=l0
xm38 vmidb vxn2 gnd gnd lvtnfet w=w9 l=l0
xm43 intern interp vmidb gnd lvtnfet w=w6 l=l0
xm41 vxp2 flipb gnd gnd lvtnfet w=w5 l=l0
xm42 interp intern vmid gnd lvtnfet w=w6 l=l0
xm39 vmid vxp2 gnd gnd lvtnfet w=w9 l=l0
xm33 clk flipb clkn gnd lvtnfet w=w5 l=l0
xm6 outp interp gnd gnd lvtnfet w=w4 l=l0
xm62 vdd clk vxp vdd lvtpfet w=w5 l=l0
xm61 vdd clk vxn vdd lvtpfet w=w5 l=l0
xm58 gnd gnd gnd vdd lvtpfet w=w5 l=l0
xm57 gnd gnd gnd vdd lvtpfet w=w9 l=l0
xm55 gnd gnd gnd vdd lvtpfet w=w5 l=l0
xm54 gnd gnd gnd vdd lvtpfet w=w6 l=l0
xm53 gnd gnd gnd vdd lvtpfet w=w6 l=l0
xm17 vxp _net1 net04 vdd lvtpfet w=w8 l=l0
xm30 flipb clk vdd vdd lvtpfet w=w5 l=l0
xm28 flip vxn net027 vdd lvtpfet w=w6 l=l0
xm20 net027 clkb vdd vdd lvtpfet w=w9 l=l0
xm2 outm intern vdd vdd lvtpfet w=w6 l=l0
xm29 flip vxp net027 vdd lvtpfet w=w6 l=l0
xm36 vxn2 flipb vxn vdd lvtpfet w=w9 l=l0
xm19 net04 flipb vdd vdd lvtpfet w=w4 l=l0
xm18 vxn _net0 net04 vdd lvtpfet w=w8 l=l0
xm34 clk flip clkn vdd lvtpfet w=w5 l=l0
xm40 vxp2 flipb vxp vdd lvtpfet w=w9 l=l0
xm47 intern vxn2 vdd vdd lvtpfet w=w5 l=l0
xm48 intern interp vdd vdd lvtpfet w=w9 l=l0
xm45 vmidb vxn2 vdd vdd lvtpfet w=w5 l=l0
xm49 interp intern vdd vdd lvtpfet w=w9 l=l0
xm44 vmid vxp2 vdd vdd lvtpfet w=w5 l=l0
xm9 outp interp vdd vdd lvtpfet w=w6 l=l0
xm46 interp vxp2 vdd vdd lvtpfet w=w5 l=l0
.ends COMPARATOR_2LEVEL_BIDIRECTIONAL_MAC_SKEW

