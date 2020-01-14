simulator lang=spectre
global 0 vdd!
parameters ibias=135u vbias= 0.53 rload=318 vdd=0.85 b0=vdd b5=0 b6=vdd cload=10f

subckt variable_gain_amplifier vmirror s0 s1 vin1 vin2 vout1 vout2 vps vgnd
MN00 vout1 vin1 n1 vgnd nmos l=0.014u nfin=12 nf=3
MN01 n1 vin1 vcm vgnd nmos l=0.014u nfin=12 nf=3
MN02 vout2 vin2 n2 vgnd nmos l=0.014u nfin=12 nf=3
MN03 n2 vin2 vcm vgnd nmos l=0.014u nfin=12 nf=3
MN04 vcm vmirror n3 vgnd nmos l=0.014u nfin=12 nf=8
MN05 n3 vmirror vgnd vgnd nmos l=0.014u nfin=12 nf=8
MN06 vmirror vmirror n4 vgnd nmos l=0.014u nfin=12 nf=8
MN07 n4 vmirror vgnd vgnd nmos l=0.014u nfin=12 nf=8

MN08 vout1 vin1 n5 vgnd nmos l=0.014u nfin=12 nf=3
MN09 n5 vin1 n7 vgnd nmos l=0.014u nfin=12 nf=3
MN10 vout2 vin2 n6 vgnd nmos l=0.014u nfin=12 nf=3
MN11 n6 vin2 n7 vgnd nmos l=0.014u nfin=12 nf=3
MN12 n7 s0 n8 vgnd nmos l=0.014u nfin=12 nf=3
MN13 n8 s0 n9 vgnd nmos l=0.014u nfin=12 nf=3
MN14 n9 vmirror n10 vgnd nmos l=0.014u nfin=12 nf=8
MN15 n10 vmirror vgnd vgnd nmos l=0.014u nfin=12 nf=8

MN16 vout1 vin1 n11 vgnd nmos l=0.014u nfin=12 nf=3
MN17 n11 vin1 n12 vgnd nmos l=0.014u nfin=12 nf=3
MN18 vout2 vin2 n13 vgnd nmos l=0.014u nfin=12 nf=3
MN19 n13 vin2 n12 vgnd nmos l=0.014u nfin=12 nf=3
MN20 n12 s1 n14 vgnd nmos l=0.014u nfin=12 nf=3
MN21 n14 s1 n15 vgnd nmos l=0.014u nfin=12 nf=3
MN22 n15 vmirror n16 vgnd nmos l=0.014u nfin=12 nf=8
MN23 n16 vmirror vgnd vgnd nmos l=0.014u nfin=12 nf=8
R1 vps vout1 resistor r=318
R0 vps vout2 resistor r=318
ends variable_gain_amplifier

xI0 vmirror b_0 b_1 vin1 vin2 vout1 vout2 vdd! 0 variable_gain_amplifier
Cload1 (vout1 0) capacitor c=cload
Cload2 (vout2 0) capacitor c=cload

V3 (b_0 0) vsource dc=vdd mag=0 type=dc
V4 (b_1 0) vsource dc=vdd mag=0 type=dc
I5 (vdd! vmirror) isource dc=ibias type=dc
V0 (vdd! 0) vsource dc=vdd mag=0 type=dc
V1 (vcm 0) vsource dc=vbias mag=0 type=dc
V2 (vdm 0) vsource dc=0 mag=1 type=sine sinedc=0 ampl=100m freq=1G
E2 (vin2 vcm vdm 0) vcvs gain=-1 type=vcvs
E0 (vin1 vcm vdm 0) vcvs gain=1 type=vcvs
simulatorOptions options reltol=1e-3 vabstol=1e-6 iabstol=1e-12 temp=27 \
    tnom=27 scalem=1.0 scale=1.0 gmin=1e-12 rforce=1 maxnotes=5 maxwarns=5 \
    digits=5 cols=80 pivrel=1e-3 sensfile="../psf/sens.output" \
    checklimitdest=psf 
dcOp dc write="spectre.dc" maxiters=150 maxsteps=10000 annotate=status
dcOpInfo info what=oppoint where=rawfile
ac1 ac start=1k stop=1000G dec=10 annotate=status 
tran1 tran start=0 stop=5n step = 0.001*5n errpreset=conservative
modelParameter info what=models where=rawfile
element info what=inst where=rawfile
outputParameter info what=output where=rawfile
designParamVals info what=parameters where=rawfile
primitives info what=primitives where=rawfile
subckts info what=subckts  where=rawfile
saveOptions options save=allpub
