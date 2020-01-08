simulator lang=spectre
global 0 vdd!

// Library name: EQ_01012020
// Cell name: SDC_top
// View name: schematic
N0 (vd net1 net11 0) nfet m=1 l=14n nfin=24 nf=1 
N1 (net11 net1 vs 0) nfet m=1 l=14n nfin=24 nf=1 
R2 (net1 vb) resistor r=15000
R1 (0 vs) resistor r=1080
R0 (vd vdd!) resistor r=1080 
C2 (vs 0) capacitor c=10e-15
C1 (vd 0) capacitor c=10e-15
V1 (vdd! 0) vsource dc=vps type=dc
V0 (vb 0) vsource dc=vbias type=dc
V2 (vin 0) vsource dc=0 mag=1 type=sine ampl=200m freq=1G
C0 (vin net1) capacitor c=79.5e-15
simulatorOptions options reltol=1e-3 vabstol=1e-6 iabstol=1e-12 temp=27 \
    tnom=27 scalem=1.0 scale=1.0 gmin=1e-12 rforce=1 maxnotes=5 maxwarns=5 \
    digits=5 cols=80 pivrel=1e-3 sensfile="../psf/sens.output" \
    checklimitdest=psf 
dcOp dc write="spectre.dc" maxiters=150 maxsteps=10000 annotate=status
dcOpInfo info what=oppoint where=rawfile
ac ac start=1000 stop=1000G dec=10 annotate=status 
tran tran stop=10n errpreset=conservative write="spectre.ic" \
    writefinal="spectre.fc" annotate=status maxiters=5 
finalTimeOP info what=oppoint where=rawfile
modelParameter info what=models where=rawfile
element info what=inst where=rawfile
outputParameter info what=output where=rawfile
designParamVals info what=parameters where=rawfile
primitives info what=primitives where=rawfile
subckts info what=subckts where=rawfile
saveOptions options save=allpub
