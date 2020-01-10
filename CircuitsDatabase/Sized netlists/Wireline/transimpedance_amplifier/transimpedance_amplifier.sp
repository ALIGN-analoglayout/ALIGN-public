
.subckt transimpedance_amplifier vgnd vin vout vps
	MN0 vout vin vgnd vgnd nmos l=14e-9 nfin=15 
	MP0 vout vin vps vps pmos l=14e-9 nfin=15
	R0 vin vout resistor r=100
.ends transimpedance_amplifier
