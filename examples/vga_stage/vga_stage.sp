.subckt vga_stage vmirror_vga s0 vin1 vin2 vout_vga1 vout_vga2 vgnd
.param nfpf_sw=12 nfpf_cm=12 nfpf_dp=12 rl=400
	M02 net3p vmirror_vga vgnd vgnd nfet nfin=nfpf_cm m=1  nf=6
	M01 vout_vga2 vin2 net3 vgnd nfet nfin=nfpf_dp m=1 nf=4
	M00 vout_vga1 vin1 net3 vgnd nfet nfin=nfpf_dp nf=4
	Msw0 net3 s0 net3p vgnd nfet l=0.014u nfin=nfpf_sw nf=6
.ends vga_stage

