.subckt inverter_v2 vin vout vdd vss
mp1 vdd  vin vout vdd p w=270e-9 l=20e-9 nfin=12 nf=2
mn1 vout vin vss  vss n w=270e-9 l=20e-9 nfin=12 nf=2
.ends inverter_v2