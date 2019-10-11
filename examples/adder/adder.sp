
.subckt nfet2x d g s b 
.param p1=2
    MN0 d g n1 b    nfet l=0.014u nfin=p1
    MN1 n1 g s b    nfet l=0.014u nfin=p1
.ends nfet2x

.subckt pfet2x d g s b 
.param p1=2
    MP0 d g n1 b    pfet l=0.014u nfin=p1
    MP1 n1 g s b    pfet l=0.014u nfin=p1
.ends pfet2x

.subckt adder n1 n2 vin vout vps vgnd 
.param cc=48f nfpf=48 rb=20K rl=500

    xI0 vout vbn1 vgnd vgnd nfet2x p1=nfpf
    xI1 vout vbp1 vps vps pfet2x p1=nfpf 
    R0 vbn1 n1 resistor r=rb
    C0 vin vbn1 capacitor c=cc
    R1 vbp1 n2 resistor r=rb
    C1 vin vbp1 capacitor c=cc
    R2 vps vout resistor r=rl    
.ends adder
