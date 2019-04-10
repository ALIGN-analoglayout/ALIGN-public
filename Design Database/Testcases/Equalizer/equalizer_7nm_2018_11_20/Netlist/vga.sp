// Generated for: spectre
// Design library name: ALIGN_project
// Design cell name: vga
simulator lang=spectre
global 0 vdd!
parameters ibias=296u vbias= 0.45 rload=400 nfin_ncm=30 nfin_dp=24 vdd=0.7 b0=vdd b1=vdd b2=vdd Lmin=7n cload=10f W=27n

simulator lang=spice
.include "7nm_TT_160803.pm"
.include "save.scs"
simulator lang=spectre

// current mirror
M03 (vmirror vmirror 0 0) nmos_lvt w=W*nfin_ncm l=2*Lmin nfin= nfin_ncm
M02 (net3 vmirror 0 0) nmos_lvt w=W*nfin_ncm l=2*Lmin nfin= nfin_ncm
// differential pair
M01 (vout1 vin2 net3 0) nmos_lvt w=W*nfin_dp l=2*Lmin nfin= nfin_dp
M00 (vout2 vin1 net3 0) nmos_lvt w=W*nfin_dp l=2*Lmin nfin= nfin_dp

R1 (vdd! vout1) resistor r=rload
R0 (vdd! vout2) resistor r=rload
Cload1 (vout1 0) capacitor c=cload
Cload2 (vout2 0) capacitor c=cload

// switch
M13 (net4 b_0 net4p 0) nmos_lvt w=W*nfin_ncm l=2*Lmin nfin= nfin_ncm
// current mirror
M12 (net4p vmirror 0 0) nmos_lvt w=W*nfin_ncm l=2*Lmin nfin= nfin_ncm
// differential pair
M11 (vout1 vin2 net4 0) nmos_lvt w=W*nfin_dp l=2*Lmin nfin= nfin_dp
M10 (vout2 vin1 net4 0) nmos_lvt w=W*nfin_dp l=2*Lmin nfin= nfin_dp

// switch
M23 (net5 b_1 net5p 0) nmos_lvt w=W*nfin_ncm l=2*Lmin nfin= nfin_ncm
// current mirror
M22 (net5p vmirror 0 0) nmos_lvt w=W*nfin_ncm*2 l=2*Lmin nfin= nfin_ncm*2
// differential pair
M21 (vout1 vin2 net5 0) nmos_lvt w=W*nfin_dp*2 l=2*Lmin nfin= nfin_dp*2
M20 (vout2 vin1 net5 0) nmos_lvt w=W*nfin_dp*2 l=2*Lmin nfin= nfin_dp*2

// switch
M33 (net6 b_2 net6p 0)nmos_lvt w=W*nfin_ncm l=2*Lmin nfin= nfin_ncm
// current mirror
M32 (net6p vmirror 0 0) nmos_lvt w=W*nfin_ncm*4 l=2*Lmin nfin= nfin_ncm*4
// differential pair
M31 (vout1 vin2 net6 0) nmos_lvt w=W*nfin_dp*4 l=2*Lmin nfin= nfin_dp*4
M30 (vout2 vin1 net6 0) nmos_lvt w=W*nfin_dp*4 l=2*Lmin nfin= nfin_dp*4

V3 (b_0 0) vsource dc=b0 mag=0 type=dc
V4 (b_1 0) vsource dc=b1 mag=0 type=dc
V5 (b_2 0) vsource dc=b2 mag=0 type=dc


I5 (vdd! vmirror) isource dc=ibias type=dc
V0 (vdd! 0) vsource dc=vdd mag=0 type=dc
V1 (vcm 0) vsource dc=vbias mag=0 type=dc
V2 (vdm 0) vsource dc=0 mag=1m type=sine sinedc=0 ampl=250m freq=1G
E2 (vin2 vcm vdm 0) vcvs gain=-.5 type=vcvs
E0 (vin1 vcm vdm 0) vcvs gain=.5 type=vcvs
simulatorOptions options reltol=1e-3 vabstol=1e-6 iabstol=1e-12 temp=27 \
    tnom=27 scalem=1.0 scale=1.0 gmin=1e-12 rforce=1 maxnotes=5 maxwarns=5 \
    digits=5 cols=80 pivrel=1e-3 sensfile="../psf/sens.output" \
    checklimitdest=psf 
dcOp dc write="spectre.dc" maxiters=150 maxsteps=10000 annotate=status
dcOpInfo info what=oppoint where=rawfile
ac1 ac start=1k stop=100G dec=10 annotate=status 
tran1 tran start=0 stop=5n step = 0.0001*5n
modelParameter info what=models where=rawfile
element info what=inst where=rawfile
outputParameter info what=output where=rawfile
designParamVals info what=parameters where=rawfile
primitives info what=primitives where=rawfile
subckts info what=subckts  where=rawfile
saveOptions options save=allpub
