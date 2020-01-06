
.subckt linear_equalizer_or vmirror vin1 vin2 vout1 vout2 vps vgnd 
MN0 vmirror vmirror vgnd vgnd nfet l=14e-9 nfin=12
MN1 n1 vmirror vgnd vgnd nfet l=14e-9 nfin=12
MN2 n2 vmirror vgnd vgnd nfet l=14e-9 nfin=12
MN3 vout1 vin1 n1 vgnd nfet l=14e-9 nfin=12
MN4 vout2 vin2 n2 vgnd nfet l=14e-9 nfin=12
R0 vps vout1 resistor r=100
R1 vps vout2 resistor r=100
R2 n1 n2 resistor r=100
R3 n1 n2 resistor r=2000
.ends linear_equalizer_or

