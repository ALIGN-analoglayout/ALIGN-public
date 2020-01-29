
subckt transimpedance_amplifier vin vout vps vgnd
N1 n1 vin vgnd vgnd nmos m=1 l=14n nfin=12 nf=1 
N0 vout vin n1 vgnd nmos m=1 l=14n nfin=12 nf=1 
P1 n2 vin vps vps pmos m=1 l=14n nfin=12 nf=1 
P0 vout vin n2 vps pmos m=1 l=14n nfin=12 nf=1
R0 vin vout resistor r=100
ends transimpedance_amplifier

