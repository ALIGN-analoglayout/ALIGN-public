.subckt variable_gain_amplifier vmirror_vga s0 s1 s2 vin1 vin2 vout_vga1 vout_vga2 vps vgnd
.param nfpf_sw=72 nfpf_sw_2=144 nfpf_sw_4=288 cload=12f nfpf_cm=72 nfpf_cm_2=144 nfpf_cm_4=288 nfpf_dp=48 nfpf_dp_2=96 nfpf_dp_4=192 rl=400

        MI03 vmirror_vga vmirror_vga vgnd vgnd nfet nfin=nfpf_cm m=1 nf=1
		MI02 net3 vmirror_vga vgnd vgnd nfet nfin=nfpf_cm m=1  nf=1
		MI01 vout_vga2 vin2 net3 vgnd nfet nfin=nfpf_dp m=1 nf=1
		MI00 vout_vga1 vin1 net3 vgnd nfet nfin=nfpf_dp
		Msw0 net5 s0 net5p vgnd nfet l=0.014u nfin=nfpf_sw
		MI12 net5p vmirror_vga vgnd vgnd nfet nfin=nfpf_cm
		MI11 vout_vga2 vin2 net5 vgnd nfet nfin=nfpf_dp
		MI10 vout_vga1 vin1 net5 vgnd nfet nfin=nfpf_dp
		Msw1 net4 s1 net4p vgnd nfet l=0.014u nfin=nfpf_sw_2
		MI22 net4p vmirror_vga vgnd vgnd nfet nfin=nfpf_cm_2
		MI21 vout_vga2 vin2 net4 vgnd nfet nfin=nfpf_dp_2
		MI20 vout_vga1 vin1 net4 vgnd nfet nfin=nfpf_dp_2
		Msw2 net6 s2 net6p vgnd nfet l=0.014u nfin=nfpf_sw_4
		MI32 net6p vmirror_vga vgnd vgnd nfet nfin=nfpf_cm_4
		MI31 vout_vga2 vin2 net6 vgnd nfet nfin=nfpf_dp_4
		MI30 vout_vga1 vin1 net6 vgnd nfet nfin=nfpf_dp_4
		R5 vps vout_vga2 rl
		R6 vps vout_vga1 rl
.ends variable_gain_amplifier
