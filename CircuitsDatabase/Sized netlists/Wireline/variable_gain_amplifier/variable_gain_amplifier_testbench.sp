// Generated for: spectre
// Generated on: Jan  2 11:59:36 2020
// Design library name: Optical_receiver
// Design cell name: VGA_top
// Design view name: schematic
simulator lang=spectre
global 0 vdd!


parameters vs2=0 nfpf_vga_sw=80 vs0=850m cload=10f ib_vga=250u \
    rload_vga=400 vbias=600m vps=0.85 wireopt=9

// Library name: Optical_receiver
// Cell name: VGA_top
// View name: schematic
R3 (vout2 vdd!) resistor r=477
R2 (vout1 vdd!) resistor r=477
N230 (vout1 vin1 net0308 0) nfet m=1 l=14n nfin=12 nf=1 
N229 (vout1 vin1 net0310 0) nfet m=1 l=14n nfin=12 nf=1 
N228 (vout2 vin2 net0307 0) nfet m=1 l=14n nfin=12 nf=1 
N227 (vout2 vin2 net0305 0) nfet m=1 l=14n nfin=12 nf=1 
N226 (vout2 vin2 net0306 0) nfet m=1 l=14n nfin=12 nf=1 ß
N225 (vout1 vin1 net0309 0) nfet m=1 l=14n nfin=12 nf=1 
N224 (vout2 vin2 net0300 0) nfet m=1 l=14n nfin=12 nf=1 
N223 (vout2 vin2 net0299 0) nfet m=1 l=14n nfin=12 nf=1 
N222 (vout2 vin2 net0301 0) nfet m=1 l=14n nfin=12 nf=1 
N221 (vout1 vin1 net0302 0) nfet m=1 l=14n nfin=12 nf=1 
N220 (vout1 vin1 net0304 0) nfet m=1 l=14n nfin=12 nf=1 
N219 (vout1 vin1 net0303 0) nfet m=1 l=14n nfin=12 nf=1 
N218 (net0309 vin1 net0273 0) nfet m=1 l=14n nfin=12 nf=1 
N217 (net0310 vin1 net0273 0) nfet m=1 l=14n nfin=12 nf=1 
N216 (net0308 vin1 net0273 0) nfet m=1 l=14n nfin=12 nf=1 
N215 (net0307 vin2 net0273 0) nfet m=1 l=14n nfin=12 nf=1 
N214 (net0306 vin2 net0273 0) nfet m=1 l=14n nfin=12 nf=1 
N213 (net0305 vin2 net0273 0) nfet m=1 l=14n nfin=12 nf=1 
N212 (net0302 vin1 net0295 0) nfet m=1 l=14n nfin=12 nf=1 
N211 (net0303 vin1 net0295 0) nfet m=1 l=14n nfin=12 nf=1 
N210 (net0304 vin1 net0295 0) nfet m=1 l=14n nfin=12 nf=1 
N209 (net0299 vin2 net0295 0) nfet m=1 l=14n nfin=12 nf=1 
N208 (net0300 vin2 net0295 0) nfet m=1 l=14n nfin=12 nf=1 
N207 (net0301 vin2 net0295 0) nfet m=1 l=14n nfin=12 nf=1 
N206 (net0295 s0 net0311 0) nfet m=1 l=14n nfin=12 nf=1 
N205 (net0295 s0 net0312 0) nfet m=1 l=14n nfin=12 nf=1 
N204 (net0295 s0 net0313 0) nfet m=1 l=14n nfin=12 nf=1 
N203 (net0311 s0 net0288 0) nfet m=1 l=14n nfin=12 nf=1 
N202 (net0312 s0 net0288 0) nfet m=1 l=14n nfin=12 nf=1 
N201 (net0313 s0 net0288 0) nfet m=1 l=14n nfin=12 nf=1 
N200 (net0273 net0252 net0323 0) nfet m=1 l=14n nfin=12 nf=1 
N199 (net0273 net0252 net0324 0) nfet m=1 l=14n nfin=12 nf=1 
N198 (net0273 net0252 net0325 0) nfet m=1 l=14n nfin=12 nf=1 
N197 (net0273 net0252 net0326 0) nfet m=1 l=14n nfin=12 nf=1 
N196 (net0273 net0252 net0327 0) nfet m=1 l=14n nfin=12 nf=1 
N195 (net0273 net0252 net0328 0) nfet m=1 l=14n nfin=12 nf=1 
N194 (net0273 net0252 net0329 0) nfet m=1 l=14n nfin=12 nf=1 
N193 (net0273 net0252 net0330 0) nfet m=1 l=14n nfin=12 nf=1 
N192 (net0288 net0252 net0316 0) nfet m=1 l=14n nfin=12 nf=1 
N191 (net0288 net0252 net0317 0) nfet m=1 l=14n nfin=12 nf=1 
N190 (net0288 net0252 net0318 0) nfet m=1 l=14n nfin=12 nf=1 
N189 (net0288 net0252 net0319 0) nfet m=1 l=14n nfin=12 nf=1 
N188 (net0288 net0252 net0320 0) nfet m=1 l=14n nfin=12 nf=1 
N187 (net0288 net0252 net0321 0) nfet m=1 l=14n nfin=12 nf=1 
N186 (net0288 net0252 net0322 0) nfet m=1 l=14n nfin=12 nf=1 
N185 (net0288 net0252 net0315 0) nfet m=1 l=14n nfin=12 nf=1 
N184 (net0252 net0252 net0338 0) nfet m=1 l=14n nfin=12 nf=1 
N183 (net0252 net0252 net0336 0) nfet m=1 l=14n nfin=12 nf=1 
N182 (net0252 net0252 net0337 0) nfet m=1 l=14n nfin=12 nf=1 
N181 (net0252 net0252 net0331 0) nfet m=1 l=14n nfin=12 nf=1 
N180 (net0252 net0252 net0332 0) nfet m=1 l=14n nfin=12 nf=1 
N179 (net0252 net0252 net0333 0) nfet m=1 l=14n nfin=12 nf=1 
N178 (net0252 net0252 net0334 0) nfet m=1 l=14n nfin=12 nf=1 
N177 (net0252 net0252 net0335 0) nfet m=1 l=14n nfin=12 nf=1 
N176 (net0323 net0252 0 0) nfet m=1 l=14n nfin=12 nf=1 
N175 (net0324 net0252 0 0) nfet m=1 l=14n nfin=12 nf=1 
N174 (net0325 net0252 0 0) nfet m=1 l=14n nfin=12 nf=1 
N173 (net0326 net0252 0 0) nfet m=1 l=14n nfin=12 nf=1 
N172 (net0327 net0252 0 0) nfet m=1 l=14n nfin=12 nf=1 
N171 (net0328 net0252 0 0) nfet m=1 l=14n nfin=12 nf=1 
N170 (net0329 net0252 0 0) nfet m=1 l=14n nfin=12 nf=1 
N169 (net0330 net0252 0 0) nfet m=1 l=14n nfin=12 nf=1 
N168 (net0315 net0252 0 0) nfet m=1 l=14n nfin=12 nf=1 
N167 (net0316 net0252 0 0) nfet m=1 l=14n nfin=12 nf=1 
N166 (net0317 net0252 0 0) nfet m=1 l=14n nfin=12 nf=1 
N165 (net0318 net0252 0 0) nfet m=1 l=14n nfin=12 nf=1 
N164 (net0319 net0252 0 0) nfet m=1 l=14n nfin=12 nf=1 
N163 (net0320 net0252 0 0) nfet m=1 l=14n nfin=12 nf=1 
N162 (net0321 net0252 0 0) nfet m=1 l=14n nfin=12 nf=1 
N161 (net0322 net0252 0 0) nfet m=1 l=14n nfin=12 nf=1 
N160 (net0331 net0252 0 0) nfet m=1 l=14n nfin=12 nf=1 
N159 (net0332 net0252 0 0) nfet m=1 l=14n nfin=12 nf=1 
N158 (net0333 net0252 0 0) nfet m=1 l=14n nfin=12 nf=1 
N157 (net0334 net0252 0 0) nfet m=1 l=14n nfin=12 nf=1 
N156 (net0335 net0252 0 0) nfet m=1 l=14n nfin=12 nf=1 
N155 (net0338 net0252 0 0) nfet m=1 l=14n nfin=12 nf=1 
N154 (net0337 net0252 0 0) nfet m=1 l=14n nfin=12 nf=1 
N153 (net0336 net0252 0 0) nfet m=1 l=14n nfin=12 nf=1 
V1 (vdd! 0) vsource dc=vps type=dc
V0 (vb_vga 0) vsource dc=vbias type=dc
V3 (s0 0) vsource dc=vs0 type=dc
C2 (vout2 0) capacitor c=10f
C1 (vout1 0) capacitor c=10f
V2 (vac 0) vsource dc=0 mag=1 type=sine ampl=100m freq=1G
E2 (vin2 vb_vga vac 0) vcvs gain=-1
E0 (vin1 vb_vga vac 0) vcvs gain=1
I11 (vdd! net0252) isource dc=ib_vga type=dc
simulatorOptions options reltol=1e-3 vabstol=1e-6 iabstol=1e-12 temp=27 \
    tnom=27 scalem=1.0 scale=1.0 gmin=1e-12 rforce=1 maxnotes=5 maxwarns=5 \
    digits=5 cols=80 pivrel=1e-3 sensfile="../psf/sens.output" \
    checklimitdest=psf 
dcOp dc write="spectre.dc" maxiters=150 maxsteps=10000 annotate=status
dcOpInfo info what=oppoint where=rawfile
ac ac start=100k stop=100G dec=10 annotate=status 
tran tran stop=10n errpreset=conservative write="spectre.ic" \
    writefinal="spectre.fc" annotate=status maxiters=5 
finalTimeOP info what=oppoint where=rawfile
modelParameter info what=models where=rawfile
element info what=inst where=rawfile
outputParameter info what=output where=rawfile
designParamVals info what=parameters where=rawfile
primitives info what=primitives where=rawfile
subckts info what=subckts where=rawfile
saveOptions options save=allpub
