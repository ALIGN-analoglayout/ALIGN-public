

.subckt gain_control_block s0 s1 s2 s3 n1 n2 vgnd
	R2 n1 n3 resistor r=1000
	R3 n4 n2 resistor r=1000
	R4 n1 n5 resistor r=1000
	R5 n6 n2 resistor r=1000
	R6 n1 n7 resistor r=1000
	R7 n8 n2 resistor r=1000
	R8 n1 n9 resistor r=1000
	R9 n10 n2 resistor r=1000
	MN5 n3 s0 n4 vgnd nmos l=14e-9 nfin=48
	MN6 n5 s1 n6 vgnd nmos l=14e-9 nfin=48
	MN7 n7 s2 n8 vgnd nmos l=14e-9 nfin=48
	MN8 n9 s3 n10 vgnd nmos l=14e-9 nfin=48
.ends gain_control_block

.subckt CMB2_ctle_align d1 d2 s b
	MN0 d1 d1 s b nmos l=14e-9 nfin=84
	MN1 d2 d1 s b nmos l=14e-9 nfin=84
.ends CMB2_ctle_align

.subckt CMB3_ctle_align d1 d2 d3 s b
	xI0 d1 d2 s b CMB2_ctle_align
	MN2 d3 d1 s b nmos l=14e-9 nfin=84
.ends CMB3_ctle_align

.subckt linear_equalizer_4_level vmirror s0 s1 s2 s3 vin1 vin2 vout1 vout2 vps vgnd
	MN0 vout2 vin2 n1 vgnd nmos l=14e-9 nfin=48
	MN1 vout1 vin1 n2 vgnd nmos l=14e-9 nfin=48
	R0 vps vout1 resistor r=2000
	R1 vps vout2 resistor r=2000
	xI0 s0 s1 s2 s3 n1 n2 vgnd gain_control_block
	xI1 vmirror n1 n2 vgnd vgnd CMB3_ctle_align
.ends linear_equalizer_4_level
