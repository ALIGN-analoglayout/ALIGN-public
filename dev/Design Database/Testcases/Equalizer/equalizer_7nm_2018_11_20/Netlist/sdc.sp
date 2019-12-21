// Generated for: spectre
// Design library name: ALIGN_project
// Design cell name: sdc
simulator lang=spectre
global 0 vdd!

parameters rbias=10k vbias=460m cload=10f no_of_fin=512 vdd=0.7 Lmin=7n
include "/home/grads/dharx027/All_research/model_files/nmosedu_50nm/model_file_50nm.inc"
include "./save_param.scs"
include "./7nm_TT_160803.pm"

// Library name: ALIGN_project_test
// Cell name: sdc
// View name: schematic
M0 (vd vbias vs 0) nmos_lvt w=no_of_fin*27n l=2*Lmin nfin=no_of_fin 
R3 (vbias net010) resistor r=rbias
R2 (vchannel 0) resistor r=50
R1 (vdd! vd) resistor r=55
R0 (vs 0) resistor r=55
V2 (net010 0) vsource dc=vbias mag=0 type=dc   // bias voltage
V1 (vdd! 0) vsource dc=vdd type=dc             // power supply
C0 (vchannel vbias) capacitor c=60e-15
CL1 (vd 0) capacitor c=cload
CL2 (vs 0) capacitor c=cload

V3 (vchannel 0) vsource dc=0 mag=200m type=sine sinedc=0 ampl=200m freq=1G
simulatorOptions options reltol=1e-3 vabstol=1e-6 iabstol=1e-12 temp=27 \
    tnom=27 scalem=1.0 scale=1.0 gmin=1e-12 rforce=1 maxnotes=5 maxwarns=5 \
    digits=5 cols=80 pivrel=1e-3 sensfile="../psf/sens.output" \
    checklimitdest=psf 
dcOp dc write="spectre.dc" maxiters=150 maxsteps=10000 annotate=status
dcOpInfo info what=oppoint where=rawfile
dc dc param=no_of_fin start=3 stop=300 step=2 oppoint=rawfile maxiters=150 \
    maxsteps=10000 annotate=status
ac1 ac start=1K stop=10000G dec=10 annotate=status 
tran tran stop=5n write="spectre.ic" writefinal="spectre.fc" \
    annotate=status maxiters=5 
finalTimeOP info what=oppoint where=rawfile
modelParameter info what=models where=rawfile
element info what=inst where=rawfile
outputParameter info what=output where=rawfile
designParamVals info what=parameters where=rawfile
primitives info what=primitives where=rawfile
subckts info what=subckts  where=rawfile
saveOptions options save=allpub
