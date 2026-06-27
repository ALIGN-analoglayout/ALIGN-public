* sky130 telescopic_ota AC testbench
.title sky130_telescopic_ota_tb

* MODELS_BEGIN - sky130_fd_pr__* stubs; run_simulation.sh replaces with real PDK .lib when available
.model sky130_fd_pr__pfet_01v8 pmos w=1 l=1 vt0=-0.1
.model sky130_fd_pr__nfet_01v8 nmos w=1 l=1 vt0=0.1
* MODELS_END
* ALIGN convenience aliases - level-1 stubs; mapped to sky130_fd_pr__ names in circuit when real PDK is used
.model nmos_rvt nmos l=1 w=1 nfin=1 nf=1 m=1 stack=1 parallel=1 vt0=0.1
.model pmos_rvt pmos l=1 w=1 nfin=1 nf=1 m=1 stack=1 parallel=1 vt0=-0.1
.model nmos_lvt nmos l=1 w=1 nfin=1 nf=1 m=1 stack=1 parallel=1 vt0=0.1
.model pmos_lvt pmos l=1 w=1 nfin=1 nf=1 m=1 stack=1 parallel=1 vt0=-0.1
.model nmos_hvt nmos l=1 w=1 nfin=1 nf=1 m=1 stack=1 parallel=1 vt0=0.1
.model pmos_hvt pmos l=1 w=1 nfin=1 nf=1 m=1 stack=1 parallel=1 vt0=-0.1

.include extracted.spice

* supplies
Vdd vdd 0 1.8

* bias voltages — tuned for real sky130 BSIM4 models:
*   nfet_01v8_lvt Vt≈0.40V, pfet_01v8 Vtp≈-0.58V (stub models had Vt=0.1V)
* Vbias_id: tail current mirror reference (diode-connected m1 gate/drain).
*   Needed regardless of model type; sets tail current via Vgs of mirror NFET.
*   0.55V gives Vov≈0.15V for LVT NFET, yielding ~10µA tail current.
Vbias_id xota.id 0 dc 0.658
Vbiasn vbiasn 0 1.0
Vbiasp1 vbiasp1 0 0.8
Vbiasp2 vbiasp2 0 1.0

* inputs (single-ended AC drive, measure single-ended output voutn)
Vinn vinn 0 0.9
Vinp vinp 0 0.9 AC 1

* DUT: .subckt telescopic_ota vbiasn vbiasp1 vbiasp2 vinn vinp voutn voutp vdd 0
Xota vbiasn vbiasp1 vbiasp2 vinn vinp voutn voutp vdd 0 telescopic_ota

.ac dec 20 1k 10g
.print ac v(voutn)

.measure ac gain_lin MAX v(voutn)
.measure ac ugbw_mhz WHEN v(voutn)=1 CROSS=1

.end
