* sky130 buffer transient testbench
.title sky130_buffer_tb

* models
.model sky130_fd_pr__pfet_01v8 pmos w=1 l=1
.model sky130_fd_pr__nfet_01v8 nmos w=1 l=1
.model nmos_rvt nmos l=1 w=1 nfin=1 nf=1 m=1 stack=1 parallel=1
.model pmos_rvt pmos l=1 w=1 nfin=1 nf=1 m=1 stack=1 parallel=1
.model nmos_lvt nmos l=1 w=1 nfin=1 nf=1 m=1 stack=1 parallel=1
.model pmos_lvt pmos l=1 w=1 nfin=1 nf=1 m=1 stack=1 parallel=1
.model nmos_hvt nmos l=1 w=1 nfin=1 nf=1 m=1 stack=1 parallel=1
.model pmos_hvt pmos l=1 w=1 nfin=1 nf=1 m=1 stack=1 parallel=1

.include extracted.spice

* supplies
Vdd vdd 0 1.8
Vss vss 0 0

* input pulse
Vin in vss PULSE(0 1.8 0.5n 0.05n 0.05n 1n 2n)

* DUT
Xbuf vss vdd in out buffer

* load
Cload out 0 10f

.tran 10p 4n

.measure tran tphl_ns TRIG v(in) VAL=0.9 RISE=1 TARG v(out) VAL=0.9 FALL=1
.measure tran tplh_ns TRIG v(in) VAL=0.9 FALL=1 TARG v(out) VAL=0.9 RISE=1

.end
