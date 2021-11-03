
simulator lang=spectre
global 0
include "<ADD PDK LIBRARY>" section=xx
include "./HIGH_SPEED_COMPARATOR.sp"
parameters tper=0.5n vdd_r=0.9 vn=vdd_r/2-vdd_r/10 vp=vdd_r/2+vdd_r/10 tstop=tper*2

simulator lang=spectre
//.subckt high_speed_comparator clk vcc vin vip von vop vss
I1 clk VDD vn vp von vop 0 high_speed_comparator
c0 von 0 capacitor c=10f
c1 vop 0 capacitor c=10f
v4 VDD 0 vsource dc=vdd_r type=dc
V1 (clk 0) vsource type=pulse val0=0 val1=vdd_r period=tper rise=tper/20 fall=tper/20 width=9*tper/20
V2 (vp 0) vsource dc=0 type=pwl wave=[ 0 vn (3*tper/4) vn (3*tper/4+10p) vp (7*tper/4) vp (7*tper/4+10p) vn ]
V3 (vn 0) vsource dc=0 type=pwl wave=[ 0 vp (3*tper/4) vp (3*tper/4+10p) vn (7*tper/4) vn (7*tper/4+10p) vp ]
//V2 (vp 0) vsource dc=0 type=dc
//V3 (vn 0) vsource dc=0 type=dc
simulatorOptions options reltol=1e-3 vabstol=1e-6 iabstol=1e-12 temp=27 \
    tnom=27 scalem=1.0 scale=1.0 gmin=1e-12 rforce=1 maxnotes=5 maxwarns=5 \
    digits=5 cols=80 pivrel=1e-3 sensfile="../psf/sens.output" \
    checklimitdest=psf
dcOp dc write="spectre.dc" maxiters=150 maxsteps=10000 annotate=status
dcOpInfo info what=oppoint where=rawfile
ac ac start=1000 stop=100G dec=10 annotate=status
tran tran start=0 stop=1e-9 step=1e-11 errpreset = conservative
//tran tran start=0 stop=1e-9 step=1e-13
modelParameter info what=models where=rawfile
element info what=inst where=rawfile
outputParameter info what=output where=rawfile
designParamVals info what=parameters where=rawfile
primitives info what=primitives where=rawfile
subckts info what=subckts where=rawfile
saveOptions options save=allpub
