.subckt inverter_generic vin vout vdd vss
mp1 vout vin vdd vdd pgen w=270e-9 l=20e-9 nfin=12 m=1 nf=2
mn1 vout vin vss vss ngen w=270e-9 l=20e-9 nfin=12 m=1 nf=2
.ends inverter_generic
