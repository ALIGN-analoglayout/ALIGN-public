.subckt ota_six ibias vcc vss von vin vip
    //mn1 ibias ibias vss vss n w=360e-9 nf=2 m=1
    mn1 ibias ibias vss vss n w=360e-9 nf=2 m=8
    mn2 tail  ibias vss vss n w=360e-9 nf=2 m=8
    mn3 vop vip tail vss n w=360e-9 nf=2 m=16
    mn4 von vin tail vss n w=360e-9 nf=2 m=16
    mp5 vop vop vcc vcc p w=360e-9 nf=2 m=4
    mp6 von vop vcc vcc p w=360e-9 nf=2 m=4
.ends ota_six