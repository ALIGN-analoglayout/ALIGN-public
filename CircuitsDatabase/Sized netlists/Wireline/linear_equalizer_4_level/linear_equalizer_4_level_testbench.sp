simulator lang=spectre
global 0 vdd!
parameters vs3=0.85 vs4=0 vs5=0 vs2=0.85 vs1=0.85 nfpf_ctle_sw0=40 ngf_ctle_sw0=1 \
    vs0=0.85 Cs=25f Rs=100 cload=10f ib_ctle=180u nfpf_ctle_cm=80 \
    nfpf_ctle_dp=50 ngf_ctle_cm=1 ngf_ctle_dp=1 rload_ctle=800 vbias=594m \
    vps=0.85 wireopt=9

// Library name: EQ_01032020
// Cell name: CTLE_top
// View name: schematic
V6 (s3_ctle 0) vsource dc=vs3 type=dc
V5 (s2_ctle 0) vsource dc=vs2 type=dc
V4 (s1_ctle 0) vsource dc=vs1 type=dc
V3 (s0_ctle 0) vsource dc=vs0 type=dc
V1 (vdd! 0) vsource dc=vps type=dc
V0 (vcm_ctle 0) vsource dc=vbias type=dc
C2 (vout2_ctle 0) capacitor c=10f
C1 (vout1_ctle 0) capacitor c=10f
V2 (vac 0) vsource dc=0 mag=2 type=sine ampl=200m freq=1G
I25 (vdd! net048) isource dc=ib_ctle type=dc
E2 (vin2 vcm_ctle vac 0) vcvs gain=-0.5
E0 (vin1 vcm_ctle vac 0) vcvs gain=0.5
N33 (net066 vin2 net055 0) nfet m=1 l=14n nfin=12 nf=4         
N32 (vout2_ctle vin2 net066 0) nfet m=1 l=14n nfin=12 nf=4         
N31 (net055 net048 net065 0) nfet m=1 l=14n nfin=12 nf=7 
N30 (net065 net048 0 0) nfet m=1 l=14n nfin=12 nf=7 
N29 (net074 s2_ctle net068 0) nfet m=1 l=14n nfin=12 nf=4 
N28 (net073 s1_ctle net067 0) nfet m=1 l=14n nfin=12 nf=4   
N27 (net072 s3_ctle net070 0) nfet m=1 l=14n nfin=12 nf=4         
N26 (net071 s0_ctle net069 0) nfet m=1 l=14n nfin=12 nf=4         
N25 (net075 s0_ctle net071 0) nfet m=1 l=14n nfin=12 nf=4         
N24 (net076 s3_ctle net072 0) nfet m=1 l=14n nfin=12 nf=4         
N23 (net077 s1_ctle net073 0) nfet m=1 l=14n nfin=12 nf=4         
N20 (net078 s2_ctle net074 0) nfet m=1 l=14n nfin=12 nf=4        
N19 (net079 vin1 net052 0) nfet m=1 l=14n nfin=12 nf=4         
N18 (net080 net048 0 0) nfet m=1 l=14n nfin=12 nf=7 
N17 (net052 net048 net080 0) nfet m=1 l=14n nfin=12 nf=7 
N16 (vout1_ctle vin1 net079 0) nfet m=1 l=14n nfin=12 nf=4        
N22 (net081 net048 0 0) nfet m=1 l=14n nfin=12 nf=7 
N21 (net048 net048 net081 0) nfet m=1 l=14n nfin=12 nf=7 
R13 (net069 net055) resistor r=1200
R12 (net070 net055) resistor r=1200
R11 (vout2_ctle vdd!) resistor r=2000
R10 (net052 net075) resistor r=1200
R9 (net052 net076) resistor r=1200
R2 (vout1_ctle vdd!) resistor r=2000
C11 (net055 net068) capacitor c=43.6f
C10 (net055 net067) capacitor c=43.6f
C9 (net052 net077) capacitor c=43.6f
C0 (net052 net078) capacitor c=43.6f
simulatorOptions options reltol=1e-3 vabstol=1e-6 iabstol=1e-12 temp=27 \
    tnom=27 scalem=1.0 scale=1.0 gmin=1e-12 rforce=1 maxnotes=5 maxwarns=5 \
    digits=5 cols=80 pivrel=1e-3 sensfile="../psf/sens.output" \
    checklimitdest=psf 
dcOp dc write="spectre.dc" maxiters=150 maxsteps=10000 annotate=status
dcOpInfo info what=oppoint where=rawfile
tran tran stop=10n errpreset=conservative write="spectre.ic" \
    writefinal="spectre.fc" annotate=status maxiters=5 
finalTimeOP info what=oppoint where=rawfile
ac ac start=10000 stop=100G dec=10 annotate=status 
modelParameter info what=models where=rawfile
element info what=inst where=rawfile
outputParameter info what=output where=rawfile
designParamVals info what=parameters where=rawfile
primitives info what=primitives where=rawfile
subckts info what=subckts where=rawfile
saveOptions options save=allpub
