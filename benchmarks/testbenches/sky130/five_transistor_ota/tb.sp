* sky130 five_transistor_ota AC testbench
.title sky130_five_transistor_ota_tb

* models
.model sky130_fd_pr__pfet_01v8 pmos w=1 l=1 vt0=-0.1
.model sky130_fd_pr__nfet_01v8 nmos w=1 l=1 vt0=0.1
.model nmos_rvt nmos l=1 w=1 nfin=1 nf=1 m=1 stack=1 parallel=1 vt0=0.1
.model pmos_rvt pmos l=1 w=1 nfin=1 nf=1 m=1 stack=1 parallel=1 vt0=-0.1
.model nmos_lvt nmos l=1 w=1 nfin=1 nf=1 m=1 stack=1 parallel=1 vt0=0.1
.model pmos_lvt pmos l=1 w=1 nfin=1 nf=1 m=1 stack=1 parallel=1 vt0=-0.1
.model nmos_hvt nmos l=1 w=1 nfin=1 nf=1 m=1 stack=1 parallel=1 vt0=0.1
.model pmos_hvt pmos l=1 w=1 nfin=1 nf=1 m=1 stack=1 parallel=1 vt0=-0.1

.include extracted.spice

* supplies
Vdd vdd 0 1.8
Vss vss 0 0

* bias: current source reference
Vbias id vss 0.6

* DC operating point: vinn = 0.9V, vinp = 0.9V + AC
Vinn vinn vss 0.9
Vinp vinp vss 0.9 AC 1

* DUT
Xota vss vdd vout vinn vinp id five_transistor_ota

.ac dec 20 1k 10g
.print ac v(vout)

.measure ac gain_lin MAX v(vout)
.measure ac ugbw_mhz WHEN v(vout)=1 CROSS=1

.end
