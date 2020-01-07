
.subckt transimpedance_amplifier vgnd vin vout vps
	MN0 vout vin vgnd vgnd nfet l=14e-9 nfin=15 
	MP0 vout vin vps vps pfet l=14e-9 nfin=15
	R0 vin vout resistor r=100
.ends transimpedance_amplifier
