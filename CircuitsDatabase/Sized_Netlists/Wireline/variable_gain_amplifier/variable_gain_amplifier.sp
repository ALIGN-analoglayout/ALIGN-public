
subckt variable_gain_amplifier vmirror s0 vin1 vin2 vout1 vout2 vps vgnd
MN00 vout1 vin1 n1 vgnd nmos l=0.014u nfin=12 nf=3
MN01 n1 vin1 vcm vgnd nmos l=0.014u nfin=12 nf=3
MN02 vout2 vin2 n2 vgnd nmos l=0.014u nfin=12 nf=3
MN03 n2 vin2 vcm vgnd nmos l=0.014u nfin=12 nf=3
MN04 vcm vmirror n3 vgnd nmos l=0.014u nfin=12 nf=8
MN05 n3 vmirror vgnd vgnd nmos l=0.014u nfin=12 nf=8
MN06 vmirror vmirror n4 vgnd nmos l=0.014u nfin=12 nf=8
MN07 n4 vmirror vgnd vgnd nmos l=0.014u nfin=12 nf=8
MN08 vout1 vin1 n5 vgnd nmos l=0.014u nfin=12 nf=3
MN09 n5 vin1 n7 vgnd nmos l=0.014u nfin=12 nf=3
MN10 vout2 vin2 n6 vgnd nmos l=0.014u nfin=12 nf=3
MN11 n6 vin2 n7 vgnd nmos l=0.014u nfin=12 nf=3
MN12 n7 s0 n8 vgnd nmos l=0.014u nfin=12 nf=3
MN13 n8 s0 n9 vgnd nmos l=0.014u nfin=12 nf=3
MN14 n9 vmirror n10 vgnd nmos l=0.014u nfin=12 nf=8
MN15 n10 vmirror vgnd vgnd nmos l=0.014u nfin=12 nf=8
R1 vps vout1 resistor r=318
R0 vps vout2 resistor r=318
ends variable_gain_amplifier
