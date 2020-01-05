// Generated for: spectre
// Generated on: Oct 21 15:41:50 2018
// Design library name: ALIGN_project
// Design cell name: vga

simulator lang=spectre
global 0 vdd!
parameters ibias=56.6u rload=1.2k wcm=727n wdp=703n vps=1 b0=1 b1=0 b2=0
include "./model_file_50nm.inc"

//current mirror
MCM00 (vmirror vmirror 0 0) N_50n w=wcm l=50n
MCM01 (net3 vmirror 0 0) N_50n w=wcm l=50n

//differential pair
MDP01 (vout1 vin2 net3 0) N_50n w=wdp l=50n
MDP00 (vout2 vin1 net3 0) N_50n w=wdp l=50n


R1 (vdd! vout1) resistor r=rload
R0 (vdd! vout2) resistor r=rload
Cload1 (vout1 0) capacitor c=2.7f
Cload2 (vout2 0) capacitor c=2.7f
//switch
MSW01 (net4 b_0 net4p 0) N_50n w=wcm l=50n
//current mirror
MCM02 (net4p vmirror 0 0) N_50n w=wcm l=50n
//differential pair
MDP03 (vout1 vin2 net4 0) N_50n w=wdp l=50n
MDP02 (vout2 vin1 net4 0) N_50n w=wdp l=50n

//switch
MSW02 (net5 b_1 net5p 0) N_50n w=wcm l=50n
//current mirror
MCM03 (net5p vmirror 0 0) N_50n w=wcm*2 l=50n
//differential pair
MDP05 (vout1 vin2 net5 0) N_50n w=wdp*2 l=50n
MDP04 (vout2 vin1 net5 0) N_50n w=wdp*2 l=50n

//switch
MSW03 (net6 b_2 net6p 0) N_50n w=wcm l=50n
//current mirror
MCM04 (net6p vmirror 0 0) N_50n w=wcm*4 l=50n
//differential pair
MDP07 (vout1 vin2 net6 0) N_50n w=wdp*4 l=50n
MDP06 (vout2 vin1 net6 0) N_50n w=wdp*4 l=50n

V3 (b_0 0) vsource dc=b0 mag=0 type=dc
V4 (b_1 0) vsource dc=b1 mag=0 type=dc
V5 (b_2 0) vsource dc=b2 mag=0 type=dc


I5 (vdd! vmirror) isource dc=ibias type=dc
V0 (vdd! 0) vsource dc=vps mag=0 type=dc
V1 (vcm 0) vsource dc=550m mag=0 type=dc
V2 (vdm 0) vsource dc=0 mag=1m type=sine sinedc=0 ampl=10m freq=100K
E2 (vin2 vcm vdm 0) vcvs gain=-.5 type=vcvs
E0 (vin1 vcm vdm 0) vcvs gain=.5 type=vcvs
simulatorOptions options reltol=1e-3 vabstol=1e-6 iabstol=1e-12 temp=27 \
    tnom=27 scalem=1.0 scale=1.0 gmin=1e-12 rforce=1 maxnotes=5 maxwarns=5 \
    digits=5 cols=80 pivrel=1e-3 sensfile="../psf/sens.output" \
    checklimitdest=psf 
dcOp dc write="spectre.dc" maxiters=150 maxsteps=10000 annotate=status
dcOpInfo info what=oppoint where=rawfile
ac1 ac start=1k stop=100G dec=10 annotate=status 
modelParameter info what=models where=rawfile
element info what=inst where=rawfile
outputParameter info what=output where=rawfile
designParamVals info what=parameters where=rawfile
primitives info what=primitives where=rawfile
subckts info what=subckts  where=rawfile
saveOptions options save=allpub
