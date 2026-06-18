* High-speed comparator post-layout testbench
* Measures: static_power_uw, regen_time_ns
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

xdut clk vcc vin vip von vop vss high_speed_comparator
vcc vcc 0 dc 1.0
vss vss 0 dc 0
vclk clk 0 pulse(1.0 0 0 10p 10p 500p 1n)
vin vin  0 dc 0.45
vip vip  0 dc 0.55

.tran 1p 2n

.measure tran iavg_a avg i(vcc) from=0.2n to=0.4n
.measure tran static_power_uw param='abs(iavg_a) * 1.0 * 1e6'

.measure tran regen_time_ns
+ trig v(vop) val=0.1 rise=1
+ targ v(vop) val=0.9 rise=1

.end
