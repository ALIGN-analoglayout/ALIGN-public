.subckt niwc_opamp_split vtail vbn vbp1 vbp2 vin vip out vccx vssx
m1 cas1 vin tail vssx n w=360e-9 m=8 nf=1 stack=4
m2 cas2 vip tail vssx n w=360e-9 m=8 nf=1 stack=4
mtail tail vtail vssx vssx n w=360e-9 m=32 nf=1 stack=8
m7a y x vssx vssx n w=360e-9 m=8 nf=1 stack=8
m7b y x vssx vssx n w=360e-9 m=8 nf=1 stack=8
m8a z x vssx vssx n w=360e-9 m=8 nf=1 stack=8
m8b z x vssx vssx n w=360e-9 m=8 nf=1 stack=8
m5a x   vbn y vssx n w=360e-9 m=4 nf=1 stack=4
m5b x   vbn y vssx n w=360e-9 m=4 nf=1 stack=4
m6a out vbn z vssx n w=360e-9 m=4 nf=1 stack=4
m6b out vbn z vssx n w=360e-9 m=4 nf=1 stack=4
m3a x vbp1 cas1 vccx p w=360e-9 m=4 nf=1 stack=4
m3b x vbp1 cas1 vccx p w=360e-9 m=4 nf=1 stack=4
m4a x vbp1 cas2 vccx p w=360e-9 m=4 nf=1 stack=4
m4b x vbp1 cas2 vccx p w=360e-9 m=4 nf=1 stack=4
m11 cas1 vbp2 vccx vccx p w=360e-9 m=32 nf=1 stack=8
m12 cas2 vbp2 vccx vccx p w=360e-9 m=32 nf=1 stack=8
.ends niwc_opamp
.END
