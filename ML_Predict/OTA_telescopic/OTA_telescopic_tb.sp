

simulator lang=spectre
global 0
include "xyz.lib"
include "./OTA_telescopic.sp"
parameters wireopt=3 cload=100f ibias_r=40u vcm_r=0.5 vdd_r=1

subckt bias_circuits vdd! 0 vbiasn vbiasp n1
xn10 net020 n1 0 0 nfet m=1 l=14e-9 nfin=6 nf=2 par=1 par_nf=2
xn9 vbiasn vbiasn net018 0 nfet m=1 l=14e-9 nfin=25 nf=2 par=1 par_nf=2
xn8 net018 vbiasn 0 0 nfet m=1 l=14e-9 nfin=2 nf=1 par=1 par_nf=1
xn6 vbiasp n1 0 0 nfet m=1 l=14e-9 nfin=12 nf=2 par=1 par_nf=2
xp9 net020 net020 vdd! vdd! pfet m=1 l=14e-9 nfin=8 nf=2 par=1 par_nf=2
xp7 net010 net020 vdd! vdd! pfet m=1 l=14e-9 nfin=15 nf=2 par=1 par_nf=2
xp8 vbiasn vbiasp net010 vdd! pfet m=1 l=14e-9 nfin=10 nf=2 par=1 par_nf=2
xp5 net015 vbiasp vdd! vdd! pfet m=1 l=14e-9 nfin=2 nf=2 par=1 par_nf=2
xp4 vbiasp vbiasp net015 vdd! pfet m=1 l=14e-9 nfin=5 nf=2 par=1 par_nf=2
ends bias_circuits

I0 VDD 0 vbiasn vbiasp n1 bias_circuits
I1 VDD 0 n9 n10 vbiasn vbiasp n1 n6 OTA_telescopic
v4 VDD 0 vsource dc=vdd_r type=dc
v6 n9 0 vsource dc=vcm_r mag=-1 type=dc
v7 n10 0 vsource dc=vcm_r mag=1 type=dc
c0 n6 0 capacitor c=cload
i5 VDD n1 isource dc=ibias_r type=dc

simulatorOptions options reltol=1e-3 vabstol=1e-6 iabstol=1e-12 temp=27 \
    tnom=27 scalem=1.0 scale=1.0 gmin=1e-12 rforce=1 maxnotes=5 maxwarns=5 \
    digits=5 cols=80 pivrel=1e-3 sensfile="../psf/sens.output" \
    checklimitdest=psf
dcOp dc write="spectre.dc" maxiters=150 maxsteps=10000 annotate=status
dcOpInfo info what=oppoint where=rawfile
ac ac start=10000 stop=1000G annotate=status
tran tran start=0 stop=15e-9 step=1e-12
modelParameter info what=models where=rawfile
element info what=inst where=rawfile
outputParameter info what=output where=rawfile
designParamVals info what=parameters where=rawfile
primitives info what=primitives where=rawfile
subckts info what=subckts where=rawfile
saveOptions options save=allpub

//save M01:all M02:all M03:all M04:all M05:all M06:all M07:all M08:all M09:all M10:all
