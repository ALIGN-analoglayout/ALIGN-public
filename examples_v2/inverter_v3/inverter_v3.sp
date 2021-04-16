.subckt inverter_v3 vin vout vdd vss
mp1 vout vin vdd vdd p w=270e-9 l=20e-9 nfin=12
mn1 vout vin vss vss n w=270e-9 l=20e-9 nfin=12
mn2 vout vss vss vss n w=270e-9 l=20e-9 nfin=12
.ends inverter_v3
