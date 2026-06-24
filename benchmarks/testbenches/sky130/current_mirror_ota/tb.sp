* sky130 current_mirror_ota AC testbench
.title sky130_current_mirror_ota_tb

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

* bias
Vbias id vss 0.6

* inputs
Vinn vinn vss 0.9
Vinp vinp vss AC 1 0.9

* DUT
Xota vss vdd vout vinn vinp id current_mirror_ota

.op
.ac dec 20 1k 10g

.measure ac gain_lin MAX vm(vout)
.measure ac bandwidth_mhz WHEN vm(vout)='gain_lin*0.7071' CROSS=1

.end
