.subckt five_transistor_ota vbias vss vdd von vop vin vip
mn1 tail vbias vss vss n w=270e-9 l=20e-9 nfin=4 nf=2 m=8
mn2 von vin tail vss n w=270e-9 l=20e-9 nfin=4 nf=2 m=16
mn3 vop vip tail vss n w=270e-9 l=20e-9 nfin=4 nf=2 m=16
mp4 von vop vdd vdd p w=270e-9 l=20e-9 nfin=4 nf=2 m=4
mp5 vop vop vdd vdd p w=270e-9 l=20e-9 nfin=4 nf=2 m=4
.ends five_transistor_ota
