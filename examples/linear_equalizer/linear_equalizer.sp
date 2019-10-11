
.subckt nfet2x d g s b
.param p1=30
    MN0 d g n1 b    nfet l=0.014u nfin=p1
    MN1 n1 g s b    nfet l=0.014u nfin=p1
.ends nfet2x

.subckt linear_equalizer vmirror_ctle s0_ctle s3_ctle vin1 vin2 vout_ctle1 vout_ctle2 vps vgnd
.param nfpf_cm=72 nfpf_dp=48 nfpf_sw=48 Rsw=100 Csw=24f rl=800

	xI0 vout_ctle2 vin2 net8 vgnd nfet2x p1=nfpf_dp
	xI1 vout_ctle1 vin1 net5 vgnd nfet2x p1=nfpf_dp
	xI4 vmirror_ctle vmirror_ctle vgnd vgnd nfet2x p1=nfpf_cm
	xI3 net5 vmirror_ctle vgnd vgnd nfet2x p1=nfpf_cm
	xI2 net8 vmirror_ctle vgnd vgnd nfet2x p1=nfpf_cm
	R1 vps vout_ctle2 resistor r=rl
	R0 vps vout_ctle1 resistor r=rl
	C4 net021 net8 capacitor c=Csw
	C3 net5 net022 capacitor c=Csw
	R4 net5 net016 resistor r=Rsw
	R3 net015 net8 resistor r=Rsw
	MN9 net021 s3_ctle net022 vgnd nfet l=0.014u nfin=nfpf_sw
	MN6 net015 s0_ctle net016 vgnd nfet l=0.014u nfin=nfpf_sw 
.ends linear_equalizer
