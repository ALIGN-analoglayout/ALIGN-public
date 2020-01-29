simulator lang=spectre
global 0 vdd!

parameters vbn=0.6 vbp = 0.45 vdd = 0.85 cload=10f

subckt adder vin vout vbn vbp vps vgnd
MN0 vout n1 n2 vgnd nmos l=0.014u nfin=12 nf=3
MN1 n2 n1 vgnd vgnd nmos l=0.014u nfin=12 nf=3
MP0 vout n3 n4 vps pmos l=0.014u nfin=12 nf=3
MP1 n4 n3 vps vps pmos l=0.014u nfin=12 nf=3
R0 vbn n1 resistor r=20000
C0 vin n1 capacitor c=48f
R1 vbp n3 resistor r=20000
C1 vin n3 capacitor c=48f
R2 vps vout resistor r=500
ends adder

xI0 vin1 vout1 n1 n2 vdd! 0 adder

// two biasing circuits for each adder to bias PMOS and NMOS separately
Vb01 (n1 0) vsource dc=vbn mag=0 type=dc
Vb02 (n2 0) vsource dc=vbp mag=0 type=dc
V1 (vdd! 0) vsource dc=vdd type=dc
Vac1 (vin1 0) vsource dc=0 mag=1 type=sine sinedc=0 ampl=100m freq=5G
Cload1 (vout1 0) capacitor c=cload

simulatorOptions options reltol=1e-3 vabstol=1e-6 iabstol=1e-12 temp=27 \
    tnom=27 scalem=1.0 scale=1.0 gmin=1e-12 rforce=1 maxnotes=5 maxwarns=5 \
    digits=5 cols=80 pivrel=1e-3 sensfile="../psf/sens.output" \
    checklimitdest=psf 
tran1 tran stop=5n step=0.001*10n write="spectre.ic" \
    writefinal="spectre.fc" annotate=status maxiters=5 errpreset=conservative
dcOpInfo info what=oppoint where=rawfile
ac1 ac start=100K stop=1000G dec=10 annotate=status 
modelParameter info what=models where=rawfile
element info what=inst where=rawfile
outputParameter info what=output where=rawfile
designParamVals info what=parameters where=rawfile
primitives info what=primitives where=rawfile
subckts info what=subckts  where=rawfile
saveOptions options save=allpub
