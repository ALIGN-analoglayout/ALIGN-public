
.param cload=10f ccoup=50f nfpf=30 ngf=1 rbias=20k rload=900 \
	vbias=600m vps=0.85

.subckt nfet2x d g s b
.param p1=30
    MN0 d g n1 b    nfet l=0.014u nfin=p1 nf=2
    MN1 n1 g s b    nfet l=0.014u nfin=p1 nf=2
.ends nfet2x

.subckt single_to_differential_converter vb vin vout_sdc1 vout_sdc2 vps vgnd
.param fin_count=12 rb=20k rl=900 cc=48f cl=12f

	xI0 vd net1 vs vgnd nfet2x p1=fin_count
	R2 vb net1 resistor r=rb
	R1 vs vgnd resistor r=rl
	R0 vps vd resistor r=rl
	C2 vs vout_sdc2 capacitor W=120 L=120
	C1 vd vout_sdc1 capacitor W=120 L=120
	C0 vin net1 capacitor W=400n L=100n
.ends single_to_differential_converter
