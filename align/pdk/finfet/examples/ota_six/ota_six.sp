.subckt ota_six ibias vccx vssx von vin vip
//mn1 ibias ibias vssx vssx n w=360e-9 nf=2 m=1
mn1 ibias ibias vssx vssx n w=360e-9 nf=2 m=8
mn2 tail  ibias vssx vssx n w=360e-9 nf=2 m=8
mn3 vop vip tail vssx n w=360e-9 nf=2 m=16
mn4 von vin tail vssx n w=360e-9 nf=2 m=16
mp5 vop vop vccx vccx p w=360e-9 nf=2 m=4
mp6 von vop vccx vccx p w=360e-9 nf=2 m=4
.ends ota_six