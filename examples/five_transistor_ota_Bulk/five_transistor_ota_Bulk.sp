.subckt five_transistor_ota_Bulk vbias vss vdd von vin vip
mn1 tail vbias vss vss n w=400e-9 nfin=4 l=60e-9 nf=2 m=24
mn2 von vin tail vss n w=400e-9 nfin=4 l=60e-9 nf=2 m=16
mn3 vop vip tail vss n w=400e-9 nfin=4 l=60e-9 nf=2 m=16
mp4 von vop vdd vdd p w=400e-9 nfin=4 l=60e-9 nf=2 m=4
mp5 vop vop vdd vdd p w=400e-9 nfin=4 l=60e-9 nf=2 m=4
.ends five_transistor_ota
