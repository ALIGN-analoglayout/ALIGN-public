.subckt variable_gain_amplifier vmirror_vga s0 s1 s2 s3 vin1 vin2 vout_vga1 vout_vga2 vps vgnd
.param nfpf_sw=72 nfpf_cm=72 nfpf_dp=48 rl=400

        M03 vmirror_vga vmirror_vga vgnd vgnd nfet nfin=nfpf_cm m=1 nf=1
		M02 net3p vmirror_vga vgnd vgnd nfet nfin=nfpf_cm m=1  nf=1
		M01 vout_vga2 vin2 net3 vgnd nfet nfin=nfpf_dp m=1 nf=1
		M00 vout_vga1 vin1 net3 vgnd nfet nfin=nfpf_dp
		Msw0 net3 s0 net3p vgnd nfet l=0.014u nfin=nfpf_sw
		Msw1 net5 s1 net5p vgnd nfet l=0.014u nfin=nfpf_sw
		M12 net5p vmirror_vga vgnd vgnd nfet nfin=nfpf_cm
		M11 vout_vga2 vin2 net5 vgnd nfet nfin=nfpf_dp
		M10 vout_vga1 vin1 net5 vgnd nfet nfin=nfpf_dp
		Msw2 net4 s2 net4p vgnd nfet l=0.014u nfin=nfpf_sw
		M22 net4p vmirror_vga vgnd vgnd nfet nfin=nfpf_cm
		M21 vout_vga2 vin2 net4 vgnd nfet nfin=nfpf_dp
		M20 vout_vga1 vin1 net4 vgnd nfet nfin=nfpf_dp
		Msw3 net6 s3 net6p vgnd nfet l=0.014u nfin=nfpf_sw
		M32 net6p vmirror_vga vgnd vgnd nfet nfin=nfpf_cm
		M31 vout_vga2 vin2 net6 vgnd nfet nfin=nfpf_dp
		M30 vout_vga1 vin1 net6 vgnd nfet nfin=nfpf_dp
		R5 vps vout_vga2 rl
		R6 vps vout_vga1 rl
.ends variable_gain_amplifier
