// Generated for: spectre
// Design library name: ALIGN_project
// Design cell name: sdc
simulator lang=spectre
global 0 vdd!

parameters rbias=10k vbias=0.49 cload=10f rload=55 fin_count=140 vdd=0.8

// directory of the library files removed.

// Library name: ALIGN_project_test
// Cell name: sdc
// View name: schematic
subckt nfet2x (d g s b) 
	parameters p1=2
	MN0 d g n1 b	nfet l=0.014u nfin=p1
	MN1 n1 g s b	nfet l=0.014u nfin=p1
ends nfet2x

xM0 (vd vbias vs 0) nfet2x p1=fin_count
R3 (vbias net010) resistor r=rbias
R2 (vchannel 0) resistor r=50
R1 (vdd! vd) resistor r=rload
R0 (vs 0) resistor r=rload
V2 (net010 0) vsource dc=vbias mag=0 type=dc   // bias voltage
V1 (vdd! 0) vsource dc=vdd type=dc             // power supply
C0 (vchannel vbias) capacitor c=60e-15
CL1 (vd 0) capacitor c=cload
CL2 (vs 0) capacitor c=cload

V3 (vchannel 0) vsource dc=0 mag=1 type=sine sinedc=0 ampl=200m freq=1G
simulatorOptions options reltol=1e-3 vabstol=1e-6 iabstol=1e-12 temp=27 \
    tnom=27 scalem=1.0 scale=1.0 gmin=1e-12 rforce=1 maxnotes=5 maxwarns=5 \
    digits=5 cols=80 pivrel=1e-3 sensfile="../psf/sens.output" \
    checklimitdest=psf 
dcOp dc write="spectre.dc" maxiters=150 maxsteps=10000 annotate=status
dcOpInfo info what=oppoint where=rawfile
//dc dc param=fin_count start=3 stop=300 step=2 oppoint=rawfile maxiters=150 \
//    maxsteps=10000 annotate=status
ac1 ac start=1K stop=10000G dec=10 annotate=status 
tran tran stop=5n step=0.001*10n write="spectre.ic" writefinal="spectre.fc" \
    annotate=status maxiters=5 errpreset=conservative
// use step size here, conservative mode
finalTimeOP info what=oppoint where=rawfile
modelParameter info what=models where=rawfile
element info what=inst where=rawfile
outputParameter info what=output where=rawfile
designParamVals info what=parameters where=rawfile
primitives info what=primitives where=rawfile
saveOptions options save=allpub

save xM0.MN0:all xM0.MN1:all
