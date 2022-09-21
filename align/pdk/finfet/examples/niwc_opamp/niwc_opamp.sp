.subckt niwc_opamp vtail vbn vbp1 vbp2 vin vip out vccx vssx
m1 cas1 vin tail vssx n w=360e-9 m=8 nf=1 stack=4
m2 cas2 vip tail vssx n w=360e-9 m=8 nf=1 stack=4
mtail tail vtail vssx vssx n w=360e-9 m=32 nf=1 stack=8
m7 y x vssx vssx n w=360e-9 m=16 nf=1 stack=8
m8 z x vssx vssx n w=360e-9 m=16 nf=1 stack=8
m5 x   vbn y vssx n w=360e-9 m=8 nf=1 stack=4
m6 out vbn z vssx n w=360e-9 m=8 nf=1 stack=4
m3 x vbp1 cas1 vccx p w=360e-9 m=8 nf=1 stack=4
m4 x vbp1 cas2 vccx p w=360e-9 m=8 nf=1 stack=4
m11 cas1 vbp2 vccx vccx p w=360e-9 m=32 nf=1 stack=8
m12 cas2 vbp2 vccx vccx p w=360e-9 m=32 nf=1 stack=8
.ends niwc_opamp
.END
