// Generated for: spectre
// Design library name: ALIGN_project
// Design cell name: ctle
simulator lang=spectre
global 0 vdd!

// here, Rs and Cs are variable resistance and capacitance respectively. 
parameters fin_count_cm=56 fin_count_dp=74 cs=140f rs=100 cload=10f ibias=502u vbias=700m rload=637 vdd=0.8

// directory of the library files removed.

subckt nfet2x (d g s b) 
	parameters p1=2
	MN0 d g n1 b	nfet l=0.014u nfin=p1
	MN1 n1 g s b	nfet l=0.014u nfin=p1
ends nfet2x

//current mirror

xM4 (vmirror vmirror 0 0) nfet2x p1=fin_count_cm
xM3 (net3 vmirror 0 0) nfet2x p1=fin_count_cm
xM2 (net5 vmirror 0 0) nfet2x p1=fin_count_cm

//differential pair
xM1 (vout2 vin2 net3 0) nfet2x p1=fin_count_dp
xM0 (vout1 vin1 net5 0) nfet2x p1=fin_count_dp

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
V2 (vdm 0) vsource dc=0 mag=1 type=sine sinedc=0 ampl=100m freq=1G
E2 (vin2 vcm vdm 0) vcvs gain=-.5 type=vcvs
E0 (vin1 vcm vdm 0) vcvs gain=.5 type=vcvs
simulatorOptions options reltol=1e-3 vabstol=1e-6 iabstol=1e-12 temp=27 \
    tnom=27 scalem=1.0 scale=1.0 gmin=1e-12 rforce=1 maxnotes=5 maxwarns=5 \
    digits=5 cols=80 pivrel=1e-3 sensfile="../psf/sens.output" \
    checklimitdest=psf 
dcOp dc write="spectre.dc" maxiters=150 maxsteps=10000 annotate=status
dcOpInfo info what=oppoint where=rawfile
ac_analysis ac start=100k stop=1000G dec=10 annotate=status
tran_analysis tran start=0 stop=10n step=0.001*10n errpreset=conservative
modelParameter info what=models where=rawfile
element info what=inst where=rawfile
outputParameter info what=output where=rawfile
designParamVals info what=parameters where=rawfile
primitives info what=primitives where=rawfile
subckts info what=subckts  where=rawfile
saveOptions options save=allpub

save xM0.MN0:all xM0.MN1:all
save xM1.MN0:all xM1.MN1:all 
save xM2.MN0:all xM2.MN1:all 
save xM3.MN0:all xM3.MN1:all
save xM4.MN0:all xM4.MN1:all
