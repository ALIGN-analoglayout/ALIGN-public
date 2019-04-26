// Generated for: spectre
// Design library name: ALIGN_project
// Design cell name: vga
simulator lang=spectre
global 0 vdd!

parameters ibias=201u vbias= 0.66 rload=318 fin_count_cm=22 fin_count_dp=29 vdd=0.8 b0=vdd b5=vdd b6=vdd cload=10f fin_count_cm_2=44 fin_count_cm_4=88 fin_count_dp_2=58 fin_count_dp_4=116

// directory of the library files removed.

subckt nfet2x (d g s b) 
	parameters p1=2
	MN0 d g n1 b	nfet l=0.014u nfin=p1
	MN1 n1 g s b	nfet l=0.014u nfin=p1
ends nfet2x

// current mirror
xM03 (vmirror vmirror 0 0) nfet2x p1=fin_count_cm
xM02 (net3 vmirror 0 0) nfet2x p1=fin_count_cm
// differential pair
xM01 (vout2 vin2 net3 0) nfet2x p1=fin_count_dp
xM00 (vout1 vin1 net3 0) nfet2x p1=fin_count_dp

R1 (vdd! vout1) resistor r=rload
R0 (vdd! vout2) resistor r=rload
Cload1 (vout1 0) capacitor c=cload
Cload2 (vout2 0) capacitor c=cload

// switch
xM13 (net5 b_0 net5p 0) nfet2x p1=fin_count_cm
// current mirror
xM12 (net5p vmirror 0 0) nfet2x p1=fin_count_cm
// differential pair
xM11 (vout2 vin2 net5 0) nfet2x p1=fin_count_dp
xM10 (vout1 vin1 net5 0) nfet2x p1=fin_count_dp

// switch
xM23 (net4 b_1 net4p 0) nfet2x p1=fin_count_cm
// current mirror
xM22 (net4p vmirror 0 0) nfet2x p1=fin_count_cm_2
// differential pair
xM21 (vout2 vin2 net4 0) nfet2x p1=fin_count_dp_2
xM20 (vout1 vin1 net4 0) nfet2x p1=fin_count_dp_2


// switch
xM33 (net6 b_2 net6p 0) nfet2x p1=fin_count_cm
// current mirror
xM32 (net6p vmirror 0 0) nfet2x p1=fin_count_cm_4
// differential pair
xM31 (vout2 vin2 net6 0) nfet2x p1=fin_count_dp_4
xM30 (vout1 vin1 net6 0) nfet2x p1=fin_count_dp_4


V3 (b_0 0) vsource dc=b0 mag=0 type=dc
V4 (b_1 0) vsource dc=b5 mag=0 type=dc
V5 (b_2 0) vsource dc=b6 mag=0 type=dc


I5 (vdd! vmirror) isource dc=ibias type=dc
V0 (vdd! 0) vsource dc=vdd mag=0 type=dc
V1 (vcm 0) vsource dc=vbias mag=0 type=dc
V2 (vdm 0) vsource dc=0 mag=1 type=sine sinedc=0 ampl=100m freq=1G
E2 (vin2 vcm vdm 0) vcvs gain=-.5 type=vcvs
E0 (vin1 vcm vdm 0) vcvs gain=.5 type=vcvs
simulatorOptions options reltol=1e-3 vabstol=1e-6 iabstol=1e-12 temp=27 \
    tnom=27 scalem=1.0 scale=1.0 gmin=1e-12 rforce=1 maxnotes=5 maxwarns=5 \
    digits=5 cols=80 pivrel=1e-3 sensfile="../psf/sens.output" \
    checklimitdest=psf 
dcOp dc write="spectre.dc" maxiters=150 maxsteps=10000 annotate=status
dcOpInfo info what=oppoint where=rawfile
ac1 ac start=1k stop=100G dec=10 annotate=status 
tran1 tran start=0 stop=5n step = 0.001*5n errpreset=conservative
modelParameter info what=models where=rawfile
element info what=inst where=rawfile
outputParameter info what=output where=rawfile
designParamVals info what=parameters where=rawfile
primitives info what=primitives where=rawfile
subckts info what=subckts  where=rawfile
saveOptions options save=allpub

save xM00.MN0:all xM00.MN1:all
save xM01.MN0:all xM01.MN1:all 
save xM02.MN0:all xM02.MN1:all 
save xM03.MN0:all xM03.MN1:all
