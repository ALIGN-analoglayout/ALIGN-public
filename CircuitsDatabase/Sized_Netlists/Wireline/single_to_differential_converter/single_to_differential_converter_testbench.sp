global 0 vdd!

parameters vbias=0.6 cload=10f vdd=0.85

subckt single_to_differential_converter vin vb vd vs vps vgnd
MN0 vd n1 n2 vgnd nmos l=0.014u nfin=12 nf=3
MN1 n2 n1 vs vgnd nmos l=0.014u nfin=12 nf=3
R0 vb n1 resistor r=20000
R1 vps vd resistor r=900
R2 vs vgnd resistor r=900
C0 vin n1 capacitor c=50f
ends single_to_differential_converter


xI0 vchannel vbias vd vs vdd! 0 single_to_differential_converter
R2 (vchannel 0) resistor r=50
V2 (vbias 0) vsource dc=vbias mag=0 type=dc   // bias voltage
V1 (vdd! 0) vsource dc=vdd type=dc             // power supply
CL1 (vd 0) capacitor c=cload
CL2 (vs 0) capacitor c=cload
V3 (vchannel 0) vsource dc=0 mag=1 type=sine sinedc=0 ampl=200m freq=1G
simulatorOptions options reltol=1e-3 vabstol=1e-6 iabstol=1e-12 temp=27 \
    tnom=27 scalem=1.0 scale=1.0 gmin=1e-12 rforce=1 maxnotes=5 maxwarns=5 \
    digits=5 cols=80 pivrel=1e-3 sensfile="../psf/sens.output" \
    checklimitdest=psf 
dcOp dc write="spectre.dc" maxiters=150 maxsteps=10000 annotate=status
dcOpInfo info what=oppoint where=rawfile
ac1 ac start=1K stop=10000G dec=10 annotate=status 
tran tran stop=5n step=0.001*10n write="spectre.ic" writefinal="spectre.fc" \
    annotate=status maxiters=5 errpreset=conservative
finalTimeOP info what=oppoint where=rawfile
modelParameter info what=models where=rawfile
element info what=inst where=rawfile
outputParameter info what=output where=rawfile
designParamVals info what=parameters where=rawfile
primitives info what=primitives where=rawfile
subckts info what=subckts  where=rawfile
saveOptions options save=allpub

