
.subckt common_centroid_n d1 d2 s
MN1 d1 d2 s s nmos l=14e-9 nfin=12
MN0 d2 d1 s s nmos l=14e-9 nfin=12
.ends common_centroid_n

.subckt common_centroid_p d1 d2 s
MP1 d1 d2 s s pmos l=14e-9 nfin=12
MP0 d2 d1 s s pmos l=14e-9 nfin=12
.ends common_centroid_p

.subckt common_centroid_np d1 d2 vps vgnd
xI0 d1 d2 vgnd common_centroid_n
xI1 d1 d2 vps common_centroid_p
.ends

.subckt double_tail_sense_amplifier clk clkb in1 in2 out1 out2 vps vgnd

MN1 out1 n1 vgnd vgnd nmos l=14e-9 nfin=12
MN2 out2 n2 vgnd vgnd nmos l=14e-9 nfin=12
MP1 net8 clkb vps vps pmos l=14e-9 nfin=12
xI2 out1 out2 net8 vgnd common_centroid_np

MN3 n1 in1 net6 net6 nmos l=14e-9 nfin=12
MN4 n2 in2 net6 net6 nmos l=14e-9 nfin=12
MN5 net6 clk vgnd vgnd nmos l=14e-9 nfin=12
MP2 n1 clk vps vps pmos l=14e-9 nfin=12
MP3 n2 clk vps vps pmos l=14e-9 nfin=12
.ends


