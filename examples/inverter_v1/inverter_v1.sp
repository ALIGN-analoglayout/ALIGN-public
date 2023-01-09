.subckt inverter_v1 vin vout vdd vss
mp1 vout vin vdd vdd p w=270e-9 l=20e-9 nfin=6 nf=2
mn1 vout vin vss vss n w=270e-9 l=20e-9 nfin=6 nf=2
.ends inverter_v1
