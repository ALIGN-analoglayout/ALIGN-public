
subckt single_to_differential_converter vin vb vd vs vps vgnd
MN0 vd n1 n2 vgnd nmos l=0.014u nfin=12 nf=3
MN1 n2 n1 vs vgnd nmos l=0.014u nfin=12 nf=3
R0 vb n1 resistor r=20000
R1 vps vd resistor r=900
R2 vs vgnd resistor r=900
C0 vin n1 capacitor c=50f
ends single_to_differential_converter


