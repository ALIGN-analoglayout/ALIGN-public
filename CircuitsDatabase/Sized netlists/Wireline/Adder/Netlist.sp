// Generated for: spectre
// Generated on: Jun  4 11:15:16 2019
// Design library name: EQ_12nm
// Design cell name: Adder_top
// Design view name: schematic
simulator lang=spectre
global VDD! VSS!

.param cload_adder=10f vps=0.85 ccoup_adder=50f nfpf_adder=50 \
    ngf_adder=1 rbias_adder=20K rload_adder=500 vbias_nfet_adder=600m \
    vbias_pfet_adder=450m

// Library name: EQ_12nm
// Cell name: Adder_top
// View name: schematic

.subckt nfet2x d g s b 
.param p1=2
    MN0 d g n1 b    nmos l=0.014u nfin=p1
    MN1 n1 g s b    nmos l=0.014u nfin=p1
.ends nfet2x

.subckt pfet2x d g s b 
.param p1=2
    MP0 d g n1 b    pmos l=0.014u nfin=p1
    MP1 n1 g s b    pmos l=0.014u nfin=p1
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
