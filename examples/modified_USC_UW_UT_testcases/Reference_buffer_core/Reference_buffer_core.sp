.subckt Reference_OTA gnd vbias vdd vmir vout vref_in
xm2 vdd vdd vdd vdd pfet_lvt w=w0 l=l0
xm0 vout net8 vdd vdd pfet_lvt w=w1 l=l0
xm5 net8 net8 vdd vdd pfet_lvt w=w1 l=l0
xm9 net012 net012 net012 gnd nfet_lvt w=w2 l=l1
xm8 net7 net7 net7 gnd nfet_lvt w=w0 l=l1
xm7 net7 vbias net012 gnd nfet_lvt w=w1 l=l1
xm62 net012 vdd gnd gnd nfet_lvt w=w3 l=l2
xm1 net8 vmir net7 gnd nfet_lvt w=w2 l=l1
xm4 vout vref_in net7 gnd nfet_lvt w=w2 l=l1
.ends Reference_OTA

.subckt Reference_buffer_core gnd vbias vbiasp vbiasp2 vdd vref vref_in
xm97 net017 net017 net017 gnd nfet_lvt w=w3 l=l2
xm104 net034 gnd vbiasp gnd nfet_lvt w=w4 l=l1
xm103 gnd gnd gnd gnd nfet_lvt w=w5 l=l2
xm102 net036 net036 net036 gnd nfet_lvt w=w2 l=l1
xm100 net017 net017 net017 gnd nfet_lvt w=w1 l=l1
xm62 net034 vdd gnd gnd nfet_lvt w=w6 l=l2
xm98 net034 net034 net034 gnd nfet_lvt w=w1 l=l1
xm19 net017 vdd gnd gnd nfet_lvt w=w7 l=l2
xm17 net036 vdd gnd gnd nfet_lvt w=w6 l=l2
xm64 vbiasp2 vbias net036 gnd nfet_lvt w=w2 l=l1
xm66 vbias vbias net034 gnd nfet_lvt w=w2 l=l1
xm7 vbiasp vbias net017 gnd nfet_lvt w=w4 l=l1
xm115 net022 vdd vdd vdd pfet_lvt w=w8 l=l2
xm114 net029 net029 net029 vdd pfet_lvt w=w9 l=l3
xm113 vref vref vref vdd pfet_lvt w=w10 l=l2
xm117 vdd vdd net061 vdd pfet_lvt w=w11 l=l3
xm112 net061 net061 net061 vdd pfet_lvt w=w12 l=l2
xm108 vdd vdd vdd vdd pfet_lvt w=w13 l=l3
xm110 net022 vdd vdd vdd pfet_lvt w=w11 l=l3
xm111 vdd vdd vdd vdd pfet_lvt w=w14 l=l2
xm107 vdd vdd vdd vdd pfet_lvt w=w15 l=l2
xm18 net022 gnd vdd vdd pfet_lvt w=w8 l=l2
xm16 net029 gnd vdd vdd pfet_lvt w=w15 l=l2
xm118 vdd vbiasp vdd vdd pfet_lvt w=w9 l=l4
xm99 net061 net018 net022 vdd pfet_lvt w=w11 l=l3
xm77 vbiasp vbiasp net061 vdd pfet_lvt w=w15 l=l2
xm105 vdd net061 vdd vdd pfet_lvt w=w9 l=l4
xm9 vref vbiasp2 net029 vdd pfet_lvt w=w9 l=l3
xm0 vbiasp2 vbiasp vref vdd pfet_lvt w=w10 l=l2
xm116 vdd vdd vbiasp vdd pfet_lvt w=w15 l=l2
xi12 gnd vbias vdd net061 net018 vref_in Reference_OTA
.ends Reference_buffer_core

