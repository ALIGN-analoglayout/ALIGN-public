simulator lang=spectre
global 0 vdd!

R2 (vout vdd!) resistor r=500
R1 (vb1 net2) resistor r=15000
R0 (net3 vb2) resistor r=500
N0 (vout net2 net010 0) nfet m=1 l=14n nfin=12 nf=3 
N2 (net010 net2 0 0) nfet m=1 l=14n nfin=12 nf=3 
C2 (vout 0) capacitor c=10f
C1 (vin net2) capacitor c=40f
C0 (vin net3) capacitor c=40f
V3 (vdd! 0) vsource dc=vps type=dc
V1 (vb2 0) vsource dc=450m type=dc
V0 (vb1 0) vsource dc=600m type=dc
V2 (vin 0) vsource mag=1 type=sine ampl=100m freq=1G
P0 (vout net3 net011 vdd!) pfet m=1 l=14n nfin=12 nf=3 
P1 (net011 net3 vdd! vdd!) pfet m=1 l=14n nfin=12 nf=3 
simulatorOptions options reltol=1e-3 vabstol=1e-6 iabstol=1e-12 temp=27 \
    tnom=27 scalem=1.0 scale=1.0 gmin=1e-12 rforce=1 maxnotes=5 maxwarns=5 \
    digits=5 cols=80 pivrel=1e-3 sensfile="../psf/sens.output" \
    checklimitdest=psf 
dcOp dc write="spectre.dc" maxiters=150 maxsteps=10000 annotate=status
dcOpInfo info what=oppoint where=rawfile
ac ac start=10000 stop=100G dec=10 annotate=status 
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

