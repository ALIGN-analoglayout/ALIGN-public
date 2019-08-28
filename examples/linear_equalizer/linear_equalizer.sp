
.param vs3=850m vs4=850m vs5=850m vs2=0.85 vs1=0 nfpf_ctle_sw0=40 \
    ngf_ctle_sw0=1 vs0=0 Cs=25f Rs=100 cload=10f ib_ctle=180u \
    nfpf_ctle_cm=80 nfpf_ctle_dp=50 ngf_ctle_cm=1 ngf_ctle_dp=1 \
    rload_ctle=800 vbias=594m ps=0.85

.subckt nfet2x d g s b
.param p1=30
    MN0 d g n1 b    nfet l=0.014u nfin=p1
    MN1 n1 g s b    nfet l=0.014u nfin=p1
.ends nfet2x

.subckt linear_equalizer vmirror_ctle s0_ctle s1_ctle s2_ctle s3_ctle s4_ctle s5_ctle vin1 vin2 vout_ctle1 vout_ctle2 vps vgnd
.param nfpf_cm=72 nfpf_dp=48 nfpf_sw=48 nfpf_sw_2=96 nfpf_sw_4=192 Rsw=100 Rsw_2=200 Rsw_4=400 Csw=24f Csw_2=48f Csw_4=96f rl=800

	xI0 vout_ctle2 vin2 net8 vgnd nfet2x p1=nfpf_dp
	xI1 vout_ctle1 vin1 net5 vgnd nfet2x p1=nfpf_dp
	xI4 vmirror_ctle vmirror_ctle vgnd vgnd nfet2x p1=nfpf_cm
	xI3 net5 vmirror_ctle vgnd vgnd nfet2x p1=nfpf_cm
	xI2 net8 vmirror_ctle vgnd vgnd nfet2x p1=nfpf_cm
	R1 vps vout_ctle2 resistor r=rl
	R0 vps vout_ctle1 resistor r=rl
	C8 net5 net049 capacitor c=Csw_4
	C7 net051 net8 capacitor c=Csw_4
	C6 net5 net050 capacitor c=Csw_2
	C5 net020 net8 capacitor c=Csw_2
	C4 net021 net8 capacitor c=Csw
	C3 net5 net022 capacitor c=Csw
	R8 net5 net017 resistor r=Rsw_4
	R7 net040 net8 resistor r=Rsw_4
	R6 net019 net8 resistor r=Rsw_2
	R5 net5 net018 resistor r=Rsw_2
	R4 net5 net016 resistor r=Rsw
	R3 net015 net8 resistor r=Rsw
	MN15 net051 s5_ctle net049 vgnd nfet l=0.014u nfin=nfpf_sw_4 
	MN14 net020 s4_ctle net050 vgnd nfet l=0.014u nfin=nfpf_sw_2 
	MN9 net021 s3_ctle net022 vgnd nfet l=0.014u nfin=nfpf_sw 
	MN8 net040 s2_ctle net017 vgnd nfet l=0.014u nfin=nfpf_sw_4 
	MN7 net019 s1_ctle net018 vgnd nfet l=0.014u nfin=nfpf_sw_2 
	MN6 net015 s0_ctle net016 vgnd nfet l=0.014u nfin=nfpf_sw 
.ends linear_equalizer
