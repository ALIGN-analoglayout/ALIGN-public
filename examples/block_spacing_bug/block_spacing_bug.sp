.subckt block_spacing_bug vss vin vip vin1 tail
mn1 von vin tail vss n w=270e-9 l=20e-9 nfin=4 nf=2 m=16
mn2 vop vip tail vss n w=270e-9 l=20e-9 nfin=4 nf=2 m=16
mn3 tail vin1 vss vss n w=270e-9 l=20e-9 nfin=4 nf=2 m=16
.ends block_spacing_bug
