
simulator lang=spectre
global 0
include "<Add proper library file for devices here>" section=tt
//include "./OTA_5T.sp"
include "./OTA_5T.sp"
parameters vcm_r=0.675 wireopt=5 vdd_r=1


P2 (n0 n11 VDD VDD) pfet m=1 l=14n nfin=12 nf=1
P1 (n12 n11 VDD VDD) pfet m=1 l=14n nfin=12 nf=1
P0 (n11 n11 VDD VDD) pfet m=1 l=14n nfin=12 nf=1
N1 (n12 n12 0 0) nfet m=1 l=14n nfin=12 nf=1
N0 (n11 n12 n13 n13) nfet m=1 l=14n nfin=40 nf=1
R0 (0 n13 0) rmres m=1 w=1u l=2u r=968.205

I0 n0 0 VDD n3 n9 n10 OTA_5T

v4 VDD 0 vsource dc=vdd_r type=dc
v6 n9 0 vsource dc=vcm_r mag=-0.5 type=dc
v7 n10 0 vsource dc=vcm_r mag=0.5 type=dc
C0 n3 0 capacitor c=100.0f

simulatorOptions options reltol=1e-3 vabstol=1e-6 iabstol=1e-12 temp=27 \
    tnom=27 scalem=1.0 scale=1.0 gmin=1e-12 rforce=1 maxnotes=5 maxwarns=5 \
    digits=5 cols=80 pivrel=1e-3 sensfile="../psf/sens.output" \
    checklimitdest=psf
dcOp dc write="spectre.dc" maxiters=150 maxsteps=10000 annotate=status
dcOpInfo info what=oppoint where=rawfile
ac ac start=1000 stop=100G dec=10 annotate=status
tran tran start=0 stop=15e-9 step=1e-12
modelParameter info what=models where=rawfile
element info what=inst where=rawfile
outputParameter info what=output where=rawfile
designParamVals info what=parameters where=rawfile
primitives info what=primitives where=rawfile
subckts info what=subckts where=rawfile
saveOptions options save=allpub
