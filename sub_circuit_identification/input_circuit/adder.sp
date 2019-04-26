// Generated for: spectre
// Design library name: ALIGN_project
// Design cell name: adder
simulator lang=spectre
global 0 vdd!

parameters rload=398 vbn=0.46 vbp = 0.45 fin_count=29 vdd = 0.8 cload=10f rcoup=2400 ccoup = 50e-15

// directory of the library files removed.

subckt nfet2x (d g s b) 
	parameters p1=2
	MN0 d g n1 b	nfet l=0.014u nfin=p1
	MN1 n1 g s b	nfet l=0.014u nfin=p1
ends nfet2x

subckt pfet2x (d g s b) 
	parameters p1=2
	MP0 d g n1 b	pfet l=0.014u nfin=p1
	MP1 n1 g s b	pfet l=0.014u nfin=p1
ends pfet2x

// only one side of adder is shown here in the netlist
//unit 1
xM0 (vout vbn1 0 0) nfet2x p1=fin_count 
xM1 (vout vbp1 vdd! vdd!) pfet2x p1=fin_count 

// two biasing circuits for each adder to bias PMOS and NMOS separately
Vb01 (n1 0) vsource dc=vbn mag=0 type=dc
R0 (vbn1 n1) resistor r = rcoup
C0 (vin1 vbn1) capacitor c = ccoup

Vb02 (n2 0) vsource dc=vbp mag=0 type=dc
R1 (vbp1 n2) resistor r = rcoup
C1 (vin1 vbp1) capacitor c = ccoup

//unit 2
xM2 (vout vbn2 0 0) nfet2x p1=fin_count 
xM3 (vout vbp2 vdd! vdd!) pfet2x p1=fin_count 

Vb03 (n3 0) vsource dc=vbn mag=0 type=dc
R2 (vbn2 n3) resistor r = rcoup
C2 (vin2 vbn2) capacitor c = ccoup

Vb04 (n4 0) vsource dc=vbp mag=0 type=dc
R3 (vbp2 n4) resistor r = rcoup
C3 (vin2 vbp2) capacitor c = ccoup

//unit 3
xM4 (vout vbn3 0 0) nfet2x p1=fin_count 
xM5 (vout vbp3 vdd! vdd!) pfet2x p1=fin_count 

Vb05 (n5 0) vsource dc=vbn mag=0 type=dc
R4 (vbn3 n5) resistor r = rcoup
C4 (vin3 vbn3) capacitor c = ccoup

Vb06 (n6 0) vsource dc=vbp mag=0 type=dc
R5 (vbp3 n6) resistor r = rcoup
C5 (vin3 vbp3) capacitor c = ccoup


V1 (vdd! 0) vsource dc=vdd type=dc

Vac1 (vin1 0) vsource dc=0 mag=1 type=sine sinedc=0 ampl=100m freq=1G
Vac2 (vin2 0) vsource dc=0 mag=1 type=sine sinedc=0 ampl=100m freq=500M
Vac3 (vin3 0) vsource dc=0 mag=1 type=sine sinedc=0 ampl=100m freq=2G

Rload (vdd! vout) resistor r=rload
Cload (vout 0) capacitor c=cload
simulatorOptions options reltol=1e-3 vabstol=1e-6 iabstol=1e-12 temp=27 \
    tnom=27 scalem=1.0 scale=1.0 gmin=1e-12 rforce=1 maxnotes=5 maxwarns=5 \
    digits=5 cols=80 pivrel=1e-3 sensfile="../psf/sens.output" \
    checklimitdest=psf 
tran1 tran stop=5n step=0.001*10n write="spectre.ic" \
    writefinal="spectre.fc" annotate=status maxiters=5 errpreset=conservative
//finalTimeOP info what=oppoint where=rawfile
dcOp dc write="spectre.dc" maxiters=150 maxsteps=10000 annotate=status
//dcOpInfo info what=oppoint where=rawfile
//dc dc param=vbn start=0 stop=1 step=100 oppoint=rawfile maxiters=150 \
//    maxsteps=10000 annotate=status
//dc dc param=fin_count start=1 stop=100 step=1 oppoint=rawfile maxiters=150 \
//    maxsteps=10000 annotate=status

ac1 ac start=100K stop=1000G dec=10 annotate=status 
modelParameter info what=models where=rawfile
element info what=inst where=rawfile
outputParameter info what=output where=rawfile
designParamVals info what=parameters where=rawfile
primitives info what=primitives where=rawfile
subckts info what=subckts  where=rawfile
saveOptions options save=allpub

save xM0.MN0:all xM0.MN1:all
save xM1.MP0:all xM1.MP1:all
