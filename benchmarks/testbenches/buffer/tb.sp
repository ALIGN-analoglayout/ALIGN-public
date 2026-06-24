* Buffer post-layout testbench
* Measures: tphl_ns, tplh_ns
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

xdut vin vout vdd vss buffer
vdd vdd 0 dc 1.0
vss vss 0 dc 0
vin vin 0 pulse(0 1.0 0 10p 10p 500p 1n)

.tran 1p 2n

.measure tran tphl_ns
+ trig v(vin)  val=0.5 fall=1
+ targ v(vout) val=0.5 fall=1

.measure tran tplh_ns
+ trig v(vin)  val=0.5 rise=1
+ targ v(vout) val=0.5 rise=1

.end
