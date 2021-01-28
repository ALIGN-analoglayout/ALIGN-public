// Generated for: spectre
// Generated on: May 20 02:30:12 2020
// Design cell name: 5T_OTA_AC1_testbench
// Design view name: schematic
simulator lang=spectre
global 0

parameters vcm_r=0.675 wireopt=5 vdd_r=1

// Library name: GF12nm_OTA_schematic
// Cell name: beta_multiplier_bias
// View name: schematic
subckt beta_multiplier_bias IBIASN VDD VSS
    P2 (IBIASN net10 VDD VDD) pmos m=1 l=14n nfin=12 nf=1
    P1 (net6 net10 VDD VDD) pmos m=1 l=14n nfin=12 nf=1
    P0 (net10 net10 VDD VDD) pmos m=1 l=14n nfin=12 nf=1
    N1 (net6 net6 VSS VSS) nmos m=1 l=14n nfin=12 nf=1
    N0 (net10 net6 net19 net19) nmos m=1 l=14n nfin=40 nf=1
    R0 (VSS net19 VSS) rmres m=1 w=1u l=2u r=968.205
ends beta_multiplier_bias

P2 (n0 n11 VDD VDD) pmos m=1 l=14n nfin=12 nf=1
P1 (n12 n11 VDD VDD) pmos m=1 l=14n nfin=12 nf=1
P0 (n11 n11 VDD VDD) pmos m=1 l=14n nfin=12 nf=1
N1 (n12 n12 0 0) nmos m=1 l=14n nfin=12 nf=1
N0 (n11 n12 n13 n13) nmos m=1 l=14n nfin=40 nf=1
R0 (0 n13 0) rmres m=1 w=1u l=2u r=968.205

// End of subcircuit definition.

//subckt M4_M5 n2 n3 VDD
//M5 (n3 n2 VDD VDD) pmos m=1 l=14n nfin=15 nf=2
//M4 (n2 n2 VDD VDD) pmos m=1 l=14n nfin=15 nf=2
//ends M4_M5

M3 (n3 n9 n1 n1) nmos m=1 l=14n nfin=40 nf=2
M2 (n2 n10 n1 n1) nmos m=1 l=14n nfin=40 nf=2
M0 (n0 n0 0 0) nmos m=1 l=14n nfin=6 nf=2
M1 (n1 n0 0 0) nmos m=1 l=14n nfin=6 nf=6
M5 (n3 n2 VDD VDD) pmos m=1 l=14n nfin=16 nf=2
M4 (n2 n2 VDD VDD) pmos m=1 l=14n nfin=16 nf=2

// Library name: GF12nm_OTA_schematic
// Cell name: 5T_OTA_AC1_testbench
// View name: schematic
//I0 (net3 net5 net6 VOUT 0) GF12nm_OTA_schematic_5T_OTA_schematic
v4 VDD 0 vsource dc=vdd_r type=dc
v6 n9 0 vsource dc=vcm_r mag=-0.5 type=dc
v7 n10 0 vsource dc=vcm_r mag=0.5 type=dc
C0 n3 0 capacitor c=100.0f
simulatorOptions options reltol=1e-3 vabstol=1e-6 iabstol=1e-12 temp=27 \
    tnom=27 scalem=1.0 scale=1.0 gmin=1e-12 rforce=1 maxnotes=5 maxwarns=5 \
    digits=5 cols=80 pivrel=1e-3 sensfile="../psf/sens.output" \
    checklimitdest=psf
dcOp dc write="spectre.dc" maxiters=150 maxsteps=10000 annotate=status
dcOpInfo info what=oppoint where=rawfile
ac ac start=1000 stop=100G dec=10 annotate=status
tran tran start=0 stop=15e-9 step=1e-12
modelParameter info what=models where=rawfile
element info what=inst where=rawfile
outputParameter info what=output where=rawfile
designParamVals info what=parameters where=rawfile
primitives info what=primitives where=rawfile
subckts info what=subckts where=rawfile
saveOptions options save=allpub
