simulator lang=spectre
global 0 vdd!
parameters ibias=100u vps=0.85

subckt transimpedance_amplifier vin vout vps vgnd
N1 n1 vin vgnd vgnd nmos m=1 l=14n nfin=12 nf=1 
N0 vout vin n1 vgnd nmos m=1 l=14n nfin=12 nf=1 
P1 n2 vin vps vps pmos m=1 l=14n nfin=12 nf=1 
P0 vout vin n2 vps pmos m=1 l=14n nfin=12 nf=1
R0 vin vout resistor r=100
ends transimpedance_amplifier

xI0 nin nout vdd! 0 transimpedance_amplifier
C0 (nout 0) capacitor c=10f
I2 (nin 0) isource dc=0 mag=1 type=sine ampl=ibias freq=1G
V0 (vdd! 0) vsource dc=vps type=dc
simulatorOptions options reltol=1e-3 vabstol=1e-6 iabstol=1e-12 temp=27 \
    tnom=27 scalem=1.0 scale=1.0 gmin=1e-12 rforce=1 maxnotes=5 maxwarns=5 \
    digits=5 cols=80 pivrel=1e-3 sensfile="../psf/sens.output" \
    checklimitdest=psf 
ac ac start=1000 stop=1000G dec=10 annotate=status 
tran tran stop=20n errpreset=moderate write="spectre.ic" \
    writefinal="spectre.fc" annotate=status maxiters=5 
finalTimeOP info what=oppoint where=rawfile
modelParameter info what=models where=rawfile
element info what=inst where=rawfile
outputParameter info what=output where=rawfile
designParamVals info what=parameters where=rawfile
primitives info what=primitives where=rawfile
subckts info what=subckts where=rawfile
saveOptions options save=allpub
