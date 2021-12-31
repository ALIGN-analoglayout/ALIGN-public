.subckt buffer vin vout vdd vss
mp1 vdd  vin vxx vdd p w=270e-9 l=20e-9 nfin=12 nf=2
mn1 vxx  vin vss vss n w=270e-9 l=20e-9 nfin=12 nf=2
mp2 vout vxx vdd vdd p w=270e-9 l=20e-9 nfin=24 nf=2
mn2 vout vxx vss vss n w=270e-9 l=20e-9 nfin=48 nf=2
.ends buffer
