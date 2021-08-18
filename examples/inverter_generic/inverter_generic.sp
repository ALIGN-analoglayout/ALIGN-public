.model ngen nmos l=1 w=1 nfin=1 nf=1 m=1  stack=1 parallel=1
.model pgen pmos l=1 w=1 nfin=1 nf=1 m=1  stack=1 parallel=1
.subckt inverter_generic vin vout vdd vss
mp1 vout vin vdd vdd pgen w=270e-9 l=20e-9 nfin=12 m=1 nf=2
mn1 vout vin vss vss ngen w=270e-9 l=20e-9 nfin=12 m=1 nf=2
.ends inverter_generic
