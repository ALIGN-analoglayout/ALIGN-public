
.subckt variable_gain_amplifier s0 vmirror vin1 vin2 vout1 vout2 vps vgnd 
        MN3 vmirror vmirror vgnd vgnd nfet l=14e-9 nfin=96
	MN2 net3 vmirror vgnd vgnd nfet l=14e-9 nfin=96
	MN1 vout2 vin2 net3 vgnd nfet l=14e-9 nfin=36
	MN0 vout1 vin1 net3 vgnd nfet l=14e-9 nfin=36
	MN4 net4p vmirror vgnd vgnd nfet l=14e-9 nfin=96
	MN5 vout2 vin2 net4 vgnd nfet l=14e-9 nfin=36
	MN6 vout1 vin1 net4 vgnd nfet l=14e-9 nfin=36
	MN7 net4 s0 net4p vgnd nfet l=14e-9 nfin=36 
	R5 vps vout2 resistor r=400
	R6 vps vout1 resistor r=400
.ends variable_gain_amplifier
