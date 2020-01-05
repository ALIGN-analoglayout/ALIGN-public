// Generated for: spectre
// Design library name: ALIGN_project
// Design cell name: ctle
simulator lang=spectre
global 0 vdd!

// here, Rs and Cs are variable resistance and capacitance respectively. 
//parameters Lmin=7n W=27n nfin_ncm=16*6 nfin_dp=24*6 cs=600f rs=1200 cload=10f ibias=296u*6 vbias=550m rload=0.2k vdd=0.7
parameters Lmin=7n W=27n nfin_ncm=120 nfin_dp=144 cs=140f rs=2000 cload=10f ibias=296u*6 vbias=550m rload=0.2k vdd=0.7

simulator lang=spice
.include "7nm_TT_160803.pm"
.include "save.scs"
simulator lang=spectre

//current mirror
M4 (vmirror vmirror 0 0) nmos_lvt w=W*nfin_ncm l=2*Lmin nfin= nfin_ncm
M3 (net3 vmirror 0 0) nmos_lvt w=W*nfin_ncm l=2*Lmin nfin= nfin_ncm
M2 (net5 vmirror 0 0) nmos_lvt w=W*nfin_ncm l=2*Lmin nfin= nfin_ncm

//differential pair
M1 (vout1 vin2 net3 0) nmos_lvt w=W*nfin_dp l=2*Lmin nfin= nfin_dp
M0 (vout2 vin1 net5 0) nmos_lvt w=W*nfin_dp l=2*Lmin nfin= nfin_dp

//variable resistance
Rs (net3 net5) resistor r=rs

// load resistance and capacitance
R1 (vdd! vout1) resistor r=rload
R0 (vdd! vout2) resistor r=rload
C0 (vout2 0) capacitor c=cload
C1 (vout1 0) capacitor c=cload
Cs (net3 net5) capacitor c=cs

I5 (vdd! vmirror) isource dc=ibias type=dc
V0 (vdd! 0) vsource dc=vdd mag=0 type=dc
V1 (vcm 0) vsource dc=vbias mag=0 type=dc
V2 (vdm 0) vsource dc=0 mag=125m type=sine sinedc=0 ampl=125m freq=1G
E2 (vin2 vcm vdm 0) vcvs gain=-.5 type=vcvs
E0 (vin1 vcm vdm 0) vcvs gain=.5 type=vcvs
simulatorOptions options reltol=1e-3 vabstol=1e-6 iabstol=1e-12 temp=27 \
    tnom=27 scalem=1.0 scale=1.0 gmin=1e-12 rforce=1 maxnotes=5 maxwarns=5 \
    digits=5 cols=80 pivrel=1e-3 sensfile="../psf/sens.output" \
    checklimitdest=psf 
dcOp dc write="spectre.dc" maxiters=150 maxsteps=10000 annotate=status
dcOpInfo info what=oppoint where=rawfile
ac_analysis ac start=100k stop=1000G dec=10 annotate=status 
tran_analysis tran start=0 stop=5n step=0.0001*5n
modelParameter info what=models where=rawfile
element info what=inst where=rawfile
outputParameter info what=output where=rawfile
designParamVals info what=parameters where=rawfile
primitives info what=primitives where=rawfile
subckts info what=subckts  where=rawfile
saveOptions options save=allpub
