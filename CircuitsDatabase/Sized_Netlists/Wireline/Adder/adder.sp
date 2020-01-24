
subckt adder vin vout vbn vbp vps vgnd
MN0 vout n1 n2 vgnd nmos l=0.014u nfin=12 nf=3
MN1 n2 n1 vgnd vgnd nmos l=0.014u nfin=12 nf=3
MP0 vout n3 n4 vps pmos l=0.014u nfin=12 nf=3
MP1 n4 n3 vps vps pmos l=0.014u nfin=12 nf=3
R0 vbn n1 resistor r=20000
C0 vin n1 capacitor c=48f
R1 vbp n3 resistor r=20000
C1 vin n3 capacitor c=48f
R2 vps vout resistor r=500
ends adder
