* sky130 telescopic_ota AC testbench
.title sky130_telescopic_ota_tb

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

* bias voltages
Vbiasn vbiasn 0 0.4
Vbiasp1 vbiasp1 0 1.4
Vbiasp2 vbiasp2 0 1.6

* inputs (single-ended AC drive, measure single-ended output voutn)
Vinn vinn 0 0.9
Vinp vinp 0 AC 1 0.9

* DUT: .subckt telescopic_ota vbiasn vbiasp1 vbiasp2 vinn vinp voutn voutp vdd 0
Xota vbiasn vbiasp1 vbiasp2 vinn vinp voutn voutp vdd 0 telescopic_ota

.op
.ac dec 20 1k 10g

.measure ac gain_db MAX vdb(voutn)
.measure ac ugbw_mhz WHEN vdb(voutn)=0 CROSS=1

.end
