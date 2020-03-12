
subckt linear_equalizer_2_switches vmirror s0 s1 vin1 vin2 vout1 vout2 vps vgnd
MN00 vout1 vin1 n1 vgnd nmos l=0.014u nfin=12 nf=2
MN01 n1 vin1 n2 vgnd nmos l=0.014u nfin=12 nf=2
MN02 vout2 vin2 n3 vgnd nmos l=0.014u nfin=12 nf=2
MN03 n3 vin2 n4 vgnd nmos l=0.014u nfin=12 nf=2
MN04 n2 vmirror n5 vgnd nmos l=0.014u nfin=12 nf=8
MN05 n5 vmirror vgnd vgnd nmos l=0.014u nfin=12 nf=8
MN06 n3 vmirror n6 vgnd nmos l=0.014u nfin=12 nf=8
MN07 n6 vmirror vgnd vgnd nmos l=0.014u nfin=12 nf=8
MN08 vmirror vmirror n7 vgnd nmos l=0.014u nfin=12 nf=8
MN09 n7 vmirror vgnd vgnd nmos l=0.014u nfin=12 nf=8
MN10 n21 s0 n31 vgnd nmos l=0.014u nfin=12 nf=2
MN11 n22 s1 n32 vgnd nmos l=0.014u nfin=12 nf=2
Rs1 n2 n21 resistor r=600
Rs2 n31 n3 resistor r=600
Cs1 n2 n22 capacitor c=1p
Cs2 n32 n3 capacitor c=1p
R1 vps vout1 resistor r=1200
R0 vps vout2 resistor r=1200
ends linear_equalizer_2_switches

