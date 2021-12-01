

.subckt CTLE vmirror_ctle vgnd vin1_ctle vin2_ctle vout1_ctle vout2_ctle vps
    MDP00 vout2_ctle vin2_ctle n1 vgnd n nfin=12 nf=2
    MDP01 n1 vin2_ctle n2 vgnd n nfin=12 nf=2

    MDP10 vout1_ctle vin1_ctle n3 vgnd n nfin=12 nf=2
    MDP11 n3 vin1_ctle n4 vgnd n nfin=12 nf=2

    MCM00 vmirror_ctle vmirror_ctle n5 vgnd n nfin=10 nf=4
    MCM01 n5 vmirror_ctle vgnd vgnd n nfin=10 nf=4

    MCM10 n2 vmirror_ctle n6 vgnd n nfin=10 nf=4
    MCM11 n6 vmirror_ctle vgnd vgnd n nfin=10 nf=4
    MCM20 n4 vmirror_ctle n8 vgnd n nfin=10 nf=4
    MCM21 n8 vmirror_ctle vgnd vgnd n nfin=10 nf=4

    R1 vps vout2_ctle 800
    R0 vps vout1_ctle 800
    R4 n2 n4 3K
    C00 n2 n4 200f
    C01 n2 n4 200f
.ends CTLE

.subckt Adder vbiasn vbiasp vps vgnd vin1 vin2 vout
    RB0 vbiasp vin1 5000
    RB1 vbiasn vin2 5000
    R0 vps vout 5000

    M00 n1 vin1 vps vps p nfin=12 nf=4
    M01 vout vin1 n1 vps p nfin=12 nf=4

    M10 vout vin2 n2 vgnd n nfin=12 nf=4
    M11 n2 vin2 vgnd vgnd n nfin=12 nf=4
.ends Adder

.subckt AdderWithCC vbiasn vbiasp vps vgnd vin vout
    X00 vbiasn vbiasp vps vgnd vin1 vin2 vout Adder
    C0 vin vin1 200f
    C1 vin vin2 200f
.ends AdderWithCC

.subckt Adder2x vbiasn vbiasp vps vgnd vin1 vin2 vout1 vout2
    X00 vbiasn vbiasp vps vgnd vin1 vout1 AdderWithCC
    X01 vbiasn vbiasp vps vgnd vin2 vout2 AdderWithCC
.ends Adder2x

.subckt VGA vmirror_vga vin1 vin2 s0 s1 vout_vga1 vout_vga2 vps vgnd

    MCM00 vmirror_vga vmirror_vga n1 vgnd n nfin=12 nf=4
    MCM01 n1 vmirror_vga vgnd vgnd n nfin=12 nf=4

    MCM10 n2 vmirror_vga vgnd vgnd n nfin=12 nf=4
    MCM11 n3 vmirror_vga n2 vgnd n nfin=12 nf=4

    MSW0 vcm0 vps n3 vgnd n nfin=12 nf=4

    MDP00 vout_vga2 vin2 n4 vgnd n nfin=12 nf=4
    MDP01 n4 vin2 vcm0 vgnd n nfin=12 nf=4
    MDP10 vout_vga1 vin1 n5 vgnd n nfin=12 nf=4
    MDP11 n5 vin1 vcm0 vgnd n nfin=12 nf=4


    MCM20 n6 vmirror_vga vgnd vgnd n nfin=12 nf=4
    MCM21 n7 vmirror_vga n6 vgnd n nfin=12 nf=4

    MSW1 vcm1 s0 n7 vgnd n nfin=12 nf=4

    MDP20 vout_vga2 vin2 n8 vgnd n nfin=12 nf=4
    MDP21 n8 vin2 vcm1 vgnd n nfin=12 nf=4
    MDP30 vout_vga1 vin1 n9 vgnd n nfin=12 nf=4
    MDP31 n9 vin1 vcm1 vgnd n nfin=12 nf=4

    MCM30 n10 vmirror_vga vgnd vgnd n nfin=12 nf=4
    MCM31 n11 vmirror_vga n10 vgnd n nfin=12 nf=4

    MSW2 vcm2 s1 n11 vgnd n nfin=12 nf=4

    MDP40 vout_vga2 vin2 n12 vgnd n nfin=12 nf=4
    MDP41 n12 vin2 vcm2 vgnd n nfin=12 nf=4
    MDP50 vout_vga1 vin1 n13 vgnd n nfin=12 nf=4
    MDP51 n13 vin1 vcm2 vgnd n nfin=12 nf=4

    R5 vps vout_vga2 5000
    R6 vps vout_vga1 5000
.ends VGA

.subckt SDC vbias vd vgnd vin vps vs
    R2 vbias n1 20000
    R1 vs vgnd 5000
    R0 vps vd 5000
    C0 vin n1 200f
    C1 vin n1 200f
    M00 vd n1 net11 vgnd n m=1 l=14n nfin=8 nf=1
    M01 net11 n1 vs vgnd n m=1 l=14n nfin=8 nf=1
.ends SDC

.subckt RCCircuit in1 in2 out1 out2
    C0 in1 n1 200f
    C1 in2 n2 200f
    R0 n1 out1 5000
    R1 n2 out2 5000
    C2 out1 out2 100f
.ends RCCircuit

.subckt CompMod in1 in2 out1 out2
    R0 out1 out2 2400
    C0 in1 n1 200f
    C1 in2 n2 200f
    C2 n1 out1 100f
    C3 n2 out2 100f
.ends CompMod

.subckt VGAdder vin1 vin2 vout1 vout2 vps vgnd vbn_adder vbp_adder vm_vga s0 s1
    X00 vbn_adder vbp_adder vps vgnd vout_vga1 vout_vga2 vout1 vout2 Adder2x
    X01 vm_vga vin1 vin2 s0 s1 vout_vga1 vout_vga2 vps vgnd VGA
.ends VGAdder

.subckt VGAdderWithRC1 vin1 vin2 vout1 vout2 vps vgnd vbn_adder vbp_adder vm_vga s0 s1
    X00 vin1 vin2 vout1_RC vout2_RC RCCircuit
    X01 vout1_RC vout2_RC vout1 vout2 vps vgnd vbn_adder vbp_adder vm_vga s0 s1 VGAdder
.ends VGAdderWithRC1

.subckt VGAdderWithRC2 vin1 vin2 vout1 vout2 vps vgnd vbn_adder vbp_adder vm_vga s0 s1
    X00 vin1 vin2 vout1_RC vout2_RC CompMod
    X01 vout1_RC vout2_RC vout1 vout2 vps vgnd vbn_adder vbp_adder vm_vga s0 s1 VGAdder
.ends VGAdderWithRC2

.subckt EQStrip3x vin vin3 vin4 vin5 vin6 vout1 vout2 vps vgnd vbn_adder vbp_adder vm_vga s0 s1 vm_ctle vb_sdc
    X00 vout1_sdc vout2_sdc vout11 vout21 vps vgnd vbn_adder vbp_adder vm_vga s0 s1 VGAdderWithRC1
    X01 vin3 vin4 vout11 vout21 vps vgnd vbn_adder vbp_adder vm_vga s0 s1 VGAdderWithRC2
    X02 vin5 vin6 vout11 vout21 vps vgnd vbn_adder vbp_adder vm_vga s0 s1 VGAdderWithRC2
    X03 vm_ctle vgnd vout11 vout21 vout1 vout2 vps CTLE
    X04 vb_sdc vout1_sdc vgnd vin vps vout2_sdc SDC
.ends EQStrip3x
