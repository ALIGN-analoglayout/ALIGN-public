// Generated for: spectre
// Generated on: Jun  3 13:08:52 2019
// Design library name: EQ_12nm
// Design cell name: VGA_top
// Design view name: schematic
simulator lang=spectre
global VDD! VSS!


// Library name: EQ_12nm
// Cell name: VGA_top
// View name: schematic
.subckt nfet2x d g s b 
.param p1=2
    MN0 d g n1 b    nfet l=0.014u nfin=p1
    MN1 n1 g s b    nfet l=0.014u nfin=p1
.ends nfet2x

// current mirror
.subckt vga vmirror_vga s0 s1 s2 vin1 vin2 vout_vga1 vout_vga2 vps vgnd 
.param nfpf_sw=72 nfpf_sw_2=144 nfpf_sw_4=288 cload=12f nfpf_cm=72 nfpf_cm_2=144 nfpf_cm_4=288 nfpf_dp=48 nfpf_dp_2=96 nfpf_dp_4=192 rl=400

        xI03 vmirror_vga vmirror_vga vgnd vgnd nfet2x p1=nfpf_cm
		xI02 net3 vmirror_vga vgnd vgnd nfet2x p1=nfpf_cm
		xI01 vout_vga2 vin2 net3 vgnd nfet2x p1=nfpf_dp
		xI00 vout_vga1 vin1 net3 vgnd nfet2x p1=nfpf_dp
		Msw0 net5 s0 net5p vgnd nfet l=0.014u nfin=nfpf_sw
		xI12 net5p vmirror_vga vgnd vgnd nfet2x p1=nfpf_cm
		xI11 vout_vga2 vin2 net5 vgnd nfet2x p1=nfpf_dp
		xI10 vout_vga1 vin1 net5 vgnd nfet2x p1=nfpf_dp
		Msw1 net4 s1 net4p vgnd nfet l=0.014u nfin=nfpf_sw_2
		xI22 net4p vmirror_vga vgnd vgnd nfet2x p1=nfpf_cm_2
		xI21 vout_vga2 vin2 net4 vgnd nfet2x p1=nfpf_dp_2
		xI20 vout_vga1 vin1 net4 vgnd nfet2x p1=nfpf_dp_2
		Msw2 net6 s2 net6p vgnd nfet l=0.014u nfin=nfpf_sw_4
		xI32 net6p vmirror_vga vgnd vgnd nfet2x p1=nfpf_cm_4
		xI31 vout_vga2 vin2 net6 vgnd nfet2x p1=nfpf_dp_4
		xI30 vout_vga1 vin1 net6 vgnd nfet2x p1=nfpf_dp_4
		R5 vps vout_vga2 resistor r=rl
		R6 vps vout_vga1 resistor r=rl
.ends vga