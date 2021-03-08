
simulator lang=spectre
global 0
include "xyz.lib"
include "./OTA_two_stage.sp"
parameters vcm_r=0.55 vdd_r=1 wireopt=5

I1 n0 n1 n9 n10 VOUT VDD 0 OTA_two_stage
C1 (VOUT 0) capacitor c=100.0f

v4 VDD 0 vsource dc=vdd_r type=dc
v6 n9 0 vsource dc=vcm_r mag=-0.5 type=dc
v7 n10 0 vsource dc=vcm_r mag=0.5 type=dc

I2 (VDD n0) isource dc=100u type=dc
simulatorOptions options reltol=1e-3 vabstol=1e-6 iabstol=1e-12 temp=27 \
    tnom=27 scalem=1.0 scale=1.0 gmin=1e-12 rforce=1 maxnotes=5 maxwarns=5 \
    digits=5 cols=80 pivrel=1e-3 sensfile="../psf/sens.output" \
    checklimitdest=psf
dcOp dc write="spectre.dc" maxiters=150 maxsteps=10000 annotate=status
dcOpInfo info what=oppoint where=rawfile
ac ac start=1000 stop=100G annotate=status
tran tran start=0 stop=15e-9 step=1e-12
modelParameter info what=models where=rawfile
element info what=inst where=rawfile
outputParameter info what=output where=rawfile
designParamVals info what=parameters where=rawfile
primitives info what=primitives where=rawfile
subckts info what=subckts where=rawfile
saveOptions options save=allpub
