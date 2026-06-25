* Current mirror OTA post-layout testbench
* Measures: gain_db, bandwidth_mhz
.option TNOM=27 GMIN=1e-12

* PDK models (inlined from FinFET14nm_Mock_PDK/models.sp)
.model nmos_rvt nmos l=1 w=1 nfin=1 nf=1 m=1  stack=1 parallel=1
.model pmos_rvt pmos l=1 w=1 nfin=1 nf=1 m=1  stack=1 parallel=1
.model n nmos nfin=1 w=1 nf=1 l=1 m=1  stack=1 parallel=1
.model p pmos nfin=1 w=1 nf=1 l=1 m=1  stack=1 parallel=1
.model nfet nmos nfin=1 nf=1 l=1 m=1  stack=1 parallel=1
.model pfet pmos nfin=1 nf=1 l=1 m=1  stack=1 parallel=1
.model resistor res r=1
.model capacitor cap l=1 w=1 m=1
.model inductor ind ind=1
.model nmos_vtl nmos l=1 w=1 nfin=1 nf=1 m=1  stack=1 parallel=1
.model pmos_vtl pmos l=1 w=1 nfin=1 nf=1 m=1  stack=1 parallel=1
.model lvtnfet nmos l=1 w=1 nfin=1 nf=1 m=1  stack=1 parallel=1
.model lvtpfet pmos l=1 w=1 nfin=1 nf=1 m=1  stack=1 parallel=1
.model hvtnfet nmos l=1 w=1 nfin=1 nf=1 m=1  stack=1 parallel=1
.model hvtpfet pmos l=1 w=1 nfin=1 nf=1 m=1  stack=1 parallel=1
.model slvtnfet nmos l=1 w=1 nfin=1 nf=1 m=1  stack=1 parallel=1
.model slvtpfet pmos l=1 w=1 nfin=1 nf=1 m=1  stack=1 parallel=1
.model NFET_DNW nmos l=1 w=1 nf=1 m=1  stack=1 parallel=1
.model LVTNFET_DNW nmos l=1 w=1 nf=1 m=1  stack=1 parallel=1
.model NCH_DNW nmos l=1 w=1 nf=1 m=1  stack=1 parallel=1
.model PCH pmos l=1 w=1 nf=1 m=1  stack=1 parallel=1
.model NCH pmos l=1 w=1 nf=1 m=1  stack=1 parallel=1
.model PCH_HVT pmos l=1 w=1 nf=1 m=1  stack=1 parallel=1
.model NCH_HVT nmos l=1 w=1 nf=1 m=1  stack=1 parallel=1
.model phvt pmos l=1 w=1 nf=1 m=1 stack=1 parallel=1
.model nhvt nmos l=1 w=1 nf=1 m=1 stack=1 parallel=1
.model psvt pmos l=1 w=1 nf=1 m=1 stack=1 parallel=1
.model nsvt nmos l=1 w=1 nf=1 m=1 stack=1 parallel=1
.model plvt pmos l=1 w=1 nf=1 m=1 stack=1 parallel=1
.model nlvt nmos l=1 w=1 nf=1 m=1 stack=1 parallel=1

.include extracted.spice

xdut id vinn vinp vss vdd voutp vbiasnd current_mirror_ota
vdd vdd 0 dc 1.0
vss vss 0 dc 0
vid id 0 dc 0.4
vbiasnd vbiasnd 0 dc 0.3
vinn vinn 0 dc 0.5 ac -0.5
vinp vinp 0 dc 0.5 ac  0.5

.ac dec 100 1k 1g

.measure ac gain_lin max v(voutp)
.measure ac bandwidth_mhz when v(voutp)=gain_lin*0.7071 fall=last

.end
