//
// Library name: CAD_modules
// Cell name: diff2sing_v1
// View name: schematic
subckt diff2sing_v1 B VDD VSS in1 in2 o
    P2 (net3 B net1 VDD) lvtpfet m=1 l=14n nfin=12 nf=15
    P5 (net1 B VDD VDD) lvtpfet m=1 l=14n nfin=12 nf=15
    P1 (o in2 net2 VDD) lvtpfet m=1 l=14n nfin=12 nf=15
    P4 (net2 in2 net3 VDD) lvtpfet m=1 l=14n nfin=12 nf=15
    P0 (net8 in1 net4 VDD) lvtpfet m=1 l=14n nfin=12 nf=15
    P3 (net4 in1 net3 VDD) lvtpfet m=1 l=14n nfin=12 nf=15
    N1 (net8 net8 net5 VSS) lvtnfet m=1 l=14n nfin=12 nf=10
    N3 (net5 net8 VSS VSS) lvtnfet m=1 l=14n nfin=12 nf=10
    N0 (o net8 net6 VSS) lvtnfet m=1 l=14n nfin=12 nf=10
    N2 (net6 net8 VSS VSS) lvtnfet m=1 l=14n nfin=12 nf=10
ends diff2sing_v1

subckt three_terminal_inv VDD VSS VBIAS VIN VOUT
    N34 (VOUT VIN net1 VSS) lvtnfet m=1 l=14n nfin=12 nf=36
    N33 (net1 VIN VSS VSS) lvtnfet m=1 l=14n nfin=12 nf=36
    P34 (VOUT VBIAS net2 VDD) lvtpfet m=1 l=14n nfin=12 nf=8
    P33 (net2 VBIAS VDD VDD) lvtpfet m=1 l=14n nfin=12 nf=8
ends three_terminal_inv
// End of subcircuit definition.

subckt bias_constraint_test VDD VSS VINN VINP VOUTINV VOUTAMP
    I0 (VSS VDD VSS VINN VINP VOUTAMP) diff2sing_v1
    I1 (VDD VSS VSS VOUTAMP VOUTINV) three_terminal_inv
ends bias_constraint_test
