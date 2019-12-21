// Generated for: spectre
// Generated on: Oct 21 12:33:02 2018
// Design library name: ALIGN_project
// Design cell name: ctle
simulator lang=spectre
global 0 vdd!

parameters ibias=71u/2 rload=5.8k wcm=912n wdp=880n cs=1.4p rs=1k
include "./model_file_50nm.inc"

//current mirror
M4 (vmirror vmirror 0 0) N_50n w=wcm l=50n
M3 (net3 vmirror 0 0) N_50n w=wcm l=50n
M2 (net5 vmirror 0 0) N_50n w=wcm l=50n

//differential pair
M1 (vout1 vin2 net3 0) N_50n w=wdp l=50n
M0 (vout2 vin1 net5 0) N_50n w=wdp l=50n
//variable resistance
Rs (net3 net5) resistor r=rs

// load resistance and capacitance
R1 (vdd! vout1) resistor r=rload
R0 (vdd! vout2) resistor r=rload
C0 (vout2 0) capacitor c=1.44f
C1 (vout1 0) capacitor c=1.44f

//variable capacitance
Cs (net3 net5) capacitor c=cs
I5 (vdd! vmirror) isource dc=ibias type=dc
V0 (vdd! 0) vsource dc=1 mag=0 type=dc
V1 (vcm 0) vsource dc=500m mag=0 type=dc
V2 (vdm 0) vsource dc=0 mag=250m type=sine sinedc=0 ampl=10m freq=100K
E2 (vin2 vcm vdm 0) vcvs gain=-.5 type=vcvs
E0 (vin1 vcm vdm 0) vcvs gain=.5 type=vcvs
simulatorOptions options reltol=1e-3 vabstol=1e-6 iabstol=1e-12 temp=27 \
    tnom=27 scalem=1.0 scale=1.0 gmin=1e-12 rforce=1 maxnotes=5 maxwarns=5 \
    digits=5 cols=80 pivrel=1e-3 sensfile="../psf/sens.output" \
    checklimitdest=psf 
dcOp dc write="spectre.dc" maxiters=150 maxsteps=10000 annotate=status
dcOpInfo info what=oppoint where=rawfile
ac_analysis ac start=1k stop=10000G dec=10 annotate=status 
modelParameter info what=models where=rawfile
element info what=inst where=rawfile
outputParameter info what=output where=rawfile
designParamVals info what=parameters where=rawfile
primitives info what=primitives where=rawfile
subckts info what=subckts  where=rawfile
saveOptions options save=allpub
