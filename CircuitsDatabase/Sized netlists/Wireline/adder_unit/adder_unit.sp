
.subckt adder_align vb1 vb2 vin vout vps vgnd 
    MN0 vout n1 vgnd vgnd nfet l=0.014u nfin=36
    MP0 vout n2 vps vps pfet l=0.014u nfin=36
    R0 n1 vb1 resistor r=15000
    Rph0 n1 vin resistor r=15000
    R1 n2 vb2 resistor r=15000
    Rph1 n2 vin resistor r=15000
    R2 vps vout resistor r=500    
.ends adder_align
