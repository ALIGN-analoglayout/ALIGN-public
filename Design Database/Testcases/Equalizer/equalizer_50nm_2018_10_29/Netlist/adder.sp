// Generated for: spectre
// Generated on: Oct 22 18:15:01 2018
// Design library name: ALIGN_project
// Design cell name: adder
simulator lang=spectre
global 0 vdd!

parameters rload=4.5k wn=590n wp=150n vbn=0.5
include "./model_file_50nm.inc"

// only one side of adder is shown here in the netlist
//unit 1
M0 (vout vbn1 0 0) N_50n w=wn l=100n
M1 (vout vbp1 vdd! vdd!) P_50n w=wp l=100n

// two biasing circuits for each adder to bias PMOS and NMOS separately
Vb01 (n1 0) vsource dc=vbn mag=0 type=dc
R0 (vbn1 n1) resistor r = 66.3e6
C0 (vin1 vbn1) capacitor c = 2.4e-12

Vb02 (n2 0) vsource dc=vbn mag=0 type=dc
R1 (vbp1 n2) resistor r = 66.3e6
C1 (vin1 vbp1) capacitor c = 2.4e-12

//unit 2
M2 (vout vbn2 0 0) N_50n w=wn l=100n
M3 (vout vbp2 vdd! vdd!) P_50n w=wp l=100n

Vb03 (n3 0) vsource dc=vbn mag=0 type=dc
R2 (vbn2 n3) resistor r = 66.3e6
C2 (vin2 vbn2) capacitor c = 2.4e-12

Vb04 (n4 0) vsource dc=vbn mag=0 type=dc
R3 (vbp2 n4) resistor r = 66.3e6
C3 (vin2 vbp2) capacitor c = 2.4e-12

//unit 3
M4 (vout vbn3 0 0) N_50n w=wn l=100n
M5 (vout vbp3 vdd! vdd!) P_50n w=wp l=100n

Vb05 (n5 0) vsource dc=vbn mag=0 type=dc
R4 (vbn3 n5) resistor r = 66.3e6
C4 (vin3 vbn3) capacitor c = 2.4e-12

Vb06 (n6 0) vsource dc=vbn mag=0 type=dc
R5 (vbp3 n6) resistor r = 66.3e6
C5 (vin3 vbp3) capacitor c = 2.4e-12


V1 (vdd! 0) vsource dc=1 type=dc

Vac1 (vin1 0) vsource dc=0 mag=100m type=sine sinedc=0 ampl=100m freq=1G
Vac2 (vin2 0) vsource dc=0 mag=100m*0 type=sine sinedc=0 ampl=100m*0 freq=1G
Vac3 (vin3 0) vsource dc=0 mag=100m*0 type=sine sinedc=0 ampl=100m*0 freq=1G

Rload (vdd! vout) resistor r=rload
Cload (vout 0) capacitor c=1.44f
simulatorOptions options reltol=1e-3 vabstol=1e-6 iabstol=1e-12 temp=27 \
    tnom=27 scalem=1.0 scale=1.0 gmin=1e-12 rforce=1 maxnotes=5 maxwarns=5 \
    digits=5 cols=80 pivrel=1e-3 sensfile="../psf/sens.output" \
    checklimitdest=psf 
tran1 tran stop=5n errpreset=moderate write="spectre.ic" \
    writefinal="spectre.fc" annotate=status maxiters=5 
//finalTimeOP info what=oppoint where=rawfile
dcOp dc write="spectre.dc" maxiters=150 maxsteps=10000 annotate=status
//dcOpInfo info what=oppoint where=rawfile
dc dc param=vbn start=0 stop=1 step=100 oppoint=rawfile maxiters=150 \
//    maxsteps=10000 annotate=status
ac1 ac start=1 stop=20G dec=10 annotate=status 
modelParameter info what=models where=rawfile
element info what=inst where=rawfile
outputParameter info what=output where=rawfile
designParamVals info what=parameters where=rawfile
primitives info what=primitives where=rawfile
subckts info what=subckts  where=rawfile
saveOptions options save=allpub
