* Variable gain amplifier post-layout testbench
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

xdut vmirror_vga s0 s1 s2 s3 vin1 vin2 vout_vga1 vout_vga2 vps vgnd variable_gain_amplifier
vps  vps  0 dc 1.0
vgnd vgnd 0 dc 0
vmirror vmirror_vga 0 dc 0.4
vs0  s0  0 dc 1.0
vs1  s1  0 dc 0
vs2  s2  0 dc 0
vs3  s3  0 dc 0
vin1 vin1 0 dc 0.5 ac  0.5
vin2 vin2 0 dc 0.5 ac -0.5

.ac dec 100 1k 1g

.measure ac gain_db max vdb(vout_vga1)
.measure ac bandwidth_mhz when vdb(vout_vga1)=gain_db-3 fall=last

.end
