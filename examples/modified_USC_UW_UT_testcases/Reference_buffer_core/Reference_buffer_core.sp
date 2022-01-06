.subckt Reference_OTA gnd vbias vdd vmir vout vref_in
m2 vdd vdd vdd vdd lvtpfet w=w0 l=l0 nf=2
m0 vout net8 vdd vdd lvtpfet w=w1 l=l0 nf=2
m5 net8 net8 vdd vdd lvtpfet w=w1 l=l0 nf=2
m9 net012 net012 net012 gnd lvtnfet w=w2 l=l1 nf=2
m8 net7 net7 net7 gnd lvtnfet w=w0 l=l1 nf=2
m7 net7 vbias net012 gnd lvtnfet w=w1 l=l1 nf=2
m62 net012 vdd gnd gnd lvtnfet w=w3 l=l2 nf=2
m1 net8 vmir net7 gnd lvtnfet w=w2 l=l1 nf=2
m4 vout vref_in net7 gnd lvtnfet w=w2 l=l1 nf=2
.ends Reference_OTA

.subckt Reference_buffer_core gnd vbias vbiasp vbiasp2 vdd vref vref_in
m97 net017 net017 net017 gnd lvtnfet w=w3 l=l2 nf=2
m104 net034 gnd vbiasp gnd lvtnfet w=w4 l=l1 nf=2
m103 gnd gnd gnd gnd lvtnfet w=w5 l=l2 nf=2
m102 net036 net036 net036 gnd lvtnfet w=w2 l=l1 nf=2
m100 net017 net017 net017 gnd lvtnfet w=w1 l=l1 nf=2
m62 net034 vdd gnd gnd lvtnfet w=w6 l=l2 nf=2
m98 net034 net034 net034 gnd lvtnfet w=w1 l=l1 nf=2
m19 net017 vdd gnd gnd lvtnfet w=w7 l=l2 nf=2
m17 net036 vdd gnd gnd lvtnfet w=w6 l=l2 nf=2
m64 vbiasp2 vbias net036 gnd lvtnfet w=w2 l=l1 nf=2
m66 vbias vbias net034 gnd lvtnfet w=w2 l=l1 nf=2
m7 vbiasp vbias net017 gnd lvtnfet w=w4 l=l1 nf=2
m115 net022 vdd vdd vdd lvtpfet w=w8 l=l2 nf=2
m114 net029 net029 net029 vdd lvtpfet w=w9 l=l3 nf=2
m113 vref vref vref vdd lvtpfet w=w10 l=l2 nf=2
m117 vdd vdd net061 vdd lvtpfet w=w11 l=l3 nf=2
m112 net061 net061 net061 vdd lvtpfet w=w12 l=l2 nf=2
m108 vdd vdd vdd vdd lvtpfet w=w13 l=l3 nf=2
m110 net022 vdd vdd vdd lvtpfet w=w11 l=l3 nf=2
m111 vdd vdd vdd vdd lvtpfet w=w14 l=l2 nf=2
m107 vdd vdd vdd vdd lvtpfet w=w15 l=l2 nf=2
m18 net022 gnd vdd vdd lvtpfet w=w8 l=l2 nf=2
m16 net029 gnd vdd vdd lvtpfet w=w15 l=l2 nf=2
m118 vdd vbiasp vdd vdd lvtpfet w=w9 l=l4 nf=2
m99 net061 net018 net022 vdd lvtpfet w=w11 l=l3 nf=2
m77 vbiasp vbiasp net061 vdd lvtpfet w=w15 l=l2 nf=2
m105 vdd net061 vdd vdd lvtpfet w=w9 l=l4 nf=2
m9 vref vbiasp2 net029 vdd lvtpfet w=w9 l=l3 nf=2
m0 vbiasp2 vbiasp vref vdd lvtpfet w=w10 l=l2 nf=2
m116 vdd vdd vbiasp vdd lvtpfet w=w15 l=l2 nf=2
xi12 gnd vbias vdd net061 net018 vref_in Reference_OTA
.ends Reference_buffer_core

