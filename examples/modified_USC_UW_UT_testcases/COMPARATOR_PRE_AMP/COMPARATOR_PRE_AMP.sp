* label = Comparator
.subckt COMPARATOR_PRE_AMP clk crossn crossp gnd intern interp outm outp vdd _net0 _net1
xm0 gnd intern gnd gnd lvtnfet w=w0 l=l0
xm22 gnd interp gnd gnd lvtnfet w=w0 l=l0
xm16 outm crossp gnd gnd lvtnfet w=w1 l=l1
xm17 outp crossn gnd gnd lvtnfet w=w1 l=l1
xm4 crossn crossp intern gnd lvtnfet w=w2 l=l1
xm3 crossp crossn interp gnd lvtnfet w=w2 l=l1
xm7 net050 clk gnd gnd lvtnfet w=w3 l=l1
xm5 intern _net0 net050 gnd lvtnfet w=w4 l=l1
xm6 interp _net1 net050 gnd lvtnfet w=w4 l=l1
xm8 outm crossp vdd vdd lvtpfet w=w5 l=l1
xm18 intern clk vdd vdd lvtpfet w=w2 l=l1
xm15 outp crossn vdd vdd lvtpfet w=w5 l=l1
xm19 interp clk vdd vdd lvtpfet w=w2 l=l1
xm10 crossn clk vdd vdd lvtpfet w=w2 l=l1
xm12 crossp clk vdd vdd lvtpfet w=w2 l=l1
xm14 crossn crossp vdd vdd lvtpfet w=w6 l=l1
xm13 crossp crossn vdd vdd lvtpfet w=w6 l=l1
.ends COMPARATOR_PRE_AMP

