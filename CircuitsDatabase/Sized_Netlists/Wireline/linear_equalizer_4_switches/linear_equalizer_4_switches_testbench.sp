simulator lang=spectre
global 0 vdd!

parameters cload=10f ibias=240u vbias=650m vdd=0.85

subckt linear_equalizer vmirror s0 s1 s2 s3 vin1 vin2 vout1 vout2 vps vgnd
MN00 vout1 vin1 n1 vgnd nmos l=0.014u nfin=12 nf=2
MN01 n1 vin1 n2 vgnd nmos l=0.014u nfin=12 nf=2
MN02 vout2 vin2 n3 vgnd nmos l=0.014u nfin=12 nf=2
MN03 n3 vin2 n4 vgnd nmos l=0.014u nfin=12 nf=2
MN04 n2 vmirror n5 vgnd nmos l=0.014u nfin=12 nf=8
MN05 n5 vmirror vgnd vgnd nmos l=0.014u nfin=12 nf=8
MN06 n3 vmirror n6 vgnd nmos l=0.014u nfin=12 nf=8
MN07 n6 vmirror vgnd vgnd nmos l=0.014u nfin=12 nf=8
MN08 vmirror vmirror n7 vgnd nmos l=0.014u nfin=12 nf=8
MN09 n7 vmirror vgnd vgnd nmos l=0.014u nfin=12 nf=8

MN10 n21 s0 n31 vgnd nmos l=0.014u nfin=12 nf=2
MN11 n22 s1 n32 vgnd nmos l=0.014u nfin=12 nf=2
MN12 n23 s2 n33 vgnd nmos l=0.014u nfin=12 nf=2
MN13 n24 s3 n34 vgnd nmos l=0.014u nfin=12 nf=2

Rs1 n2 n21 resistor r=600
Rs2 n31 n3 resistor r=600
Cs1 n2 n22 capacitor c=1p
Cs2 n32 n3 capacitor c=1p

Rs3 n2 n23 resistor r=600
Rs4 n33 n3 resistor r=600
Cs3 n2 n24 capacitor c=1p
Cs4 n34 n3 capacitor c=1p

R1 vps vout1 resistor r=1200
R0 vps vout2 resistor r=1200
ends linear_equalizer

xI0 vmirror s0 s1 s2 s3 vin1 vin2 vout1 vout2 vdd! 0 linear_equalizer
C0 (vout2 0) capacitor c=cload
C1 (vout1 0) capacitor c=cload

I5 (vdd! vmirror) isource dc=ibias type=dc
V0 (vdd! 0) vsource dc=vdd mag=0 type=dc
V1 (vcm 0) vsource dc=vbias mag=0 type=dc
V2 (vdm 0) vsource dc=0 mag=1 type=sine sinedc=0 ampl=100m freq=1G
V3 (s0 0) vsource dc=vdd mag=0 type=dc
V4 (s1 0) vsource dc=vdd mag=0 type=dc
V5 (s2 0) vsource dc=0 mag=0 type=dc
V6 (s3 0) vsource dc=vdd mag=0 type=dc
E2 (vin2 vcm vdm 0) vcvs gain=-1 type=vcvs
E0 (vin1 vcm vdm 0) vcvs gain=1 type=vcvs
simulatorOptions options reltol=1e-3 vabstol=1e-6 iabstol=1e-12 temp=27 \
    tnom=27 scalem=1.0 scale=1.0 gmin=1e-12 rforce=1 maxnotes=5 maxwarns=5 \
    digits=5 cols=80 pivrel=1e-3 sensfile="../psf/sens.output" \
    checklimitdest=psf 
dcOp dc write="spectre.dc" maxiters=150 maxsteps=10000 annotate=status
dcOpInfo info what=oppoint where=rawfile
ac_analysis ac start=100k stop=1000G dec=10 annotate=status
tran_analysis tran start=0 stop=10n step=0.001*10n errpreset=conservative
modelParameter info what=models where=rawfile
element info what=inst where=rawfile
outputParameter info what=output where=rawfile
designParamVals info what=parameters where=rawfile
primitives info what=primitives where=rawfile
subckts info what=subckts  where=rawfile
saveOptions options save=allpub

save R0:all R1:all
