// Generated for: spectre
// Generated on: Oct 28 04:00:58 2018
// Design library name: ALIGN_project
// Design cell name: sdc
simulator lang=spectre
global 0 vdd!
parameters rbias=60k vbias=1 W=50u cload=10f
include "./model_file_50nm.inc"

M0 (vd vbias vs 0) N_50n w=W l=100n
R6 (vbias net010) resistor r=rbias
R2 (vchannel 0) resistor r=50
R1 (vdd! vd) resistor r=55
R0 (vs 0) resistor r=55
V2 (net010 0) vsource dc=vbias mag=0 type=dc
V1 (vdd! 0) vsource dc=1 type=dc
C0 (vchannel vbias) capacitor c=2.4p
CL1 (vd 0) capacitor c=cload
CL2 (vs 0) capacitor c=cload

V3 (vchannel 0) vsource dc=0 mag=250m type=sine sinedc=0 ampl=300m freq=1G
simulatorOptions options reltol=1e-3 vabstol=1e-6 iabstol=1e-12 temp=27 \
    tnom=27 scalem=1.0 scale=1.0 gmin=1e-12 rforce=1 maxnotes=5 maxwarns=5 \
    digits=5 cols=80 pivrel=1e-3 sensfile="../psf/sens.output" \
    checklimitdest=psf 
dcOp dc write="spectre.dc" maxiters=150 maxsteps=10000 annotate=status
dcOpInfo info what=oppoint where=rawfile
dc dc param=W start=10u stop=500u step=1000 oppoint=rawfile maxiters=150 \
    maxsteps=10000 annotate=status
ac ac start=1K stop=100G dec=10 annotate=status 
tran tran stop=5n write="spectre.ic" writefinal="spectre.fc" \
    annotate=status maxiters=5 
finalTimeOP info what=oppoint where=rawfile
modelParameter info what=models where=rawfile
element info what=inst where=rawfile
outputParameter info what=output where=rawfile
designParamVals info what=parameters where=rawfile
primitives info what=primitives where=rawfile
subckts info what=subckts  where=rawfile
save M0:d 
saveOptions options save=allpub
