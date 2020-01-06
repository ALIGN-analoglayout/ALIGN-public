
.subckt vga_align s0 s1 vmirror vin1 vin2 vout1 vout2 vps vgnd 
        MN3 vmirror vmirror vgnd vgnd nfet l=14e-9 nfin=84
	MN2 net3 vmirror vgnd vgnd nfet l=14e-9 nfin=84
	MN1 vout2 vin2 net3 vgnd nfet l=14e-9 nfin=48
	MN0 vout1 vin1 net3 vgnd nfet l=14e-9 nfin=48
	MN4 net4p vmirror vgnd vgnd nfet l=14e-9 nfin=84
	MN5 vout2 vin2 net4 vgnd nfet l=14e-9 nfin=48
	MN6 vout1 vin1 net4 vgnd nfet l=14e-9 nfin=48
	MN7 net4 s0 net4p vgnd nfet l=14e-9 nfin=48 
	MN8 net5p vmirror vgnd vgnd nfet l=14e-9 nfin=84
	MN9 vout2 vin2 net5 vgnd nfet l=14e-9 nfin=48
	MN10 vout1 vin1 net5 vgnd nfet l=14e-9 nfin=48
	MN11 net5 s1 net5p vgnd nfet l=14e-9 nfin=48 
	R5 vps vout2 resistor r=400
	R6 vps vout1 resistor r=400
.ends vga_align
