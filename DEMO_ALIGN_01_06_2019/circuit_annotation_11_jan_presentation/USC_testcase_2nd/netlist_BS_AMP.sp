************************************************************************
* auCdl Netlist:
* 
* Library Name:  UM_GF14
* Top Cell Name: TB_IBS_norm
* View Name:     schematic
* Netlisted on:  Jan  4 14:34:06 2019
************************************************************************

*.BIPOLAR
*.RESI = 2000 
*.RESVAL
*.CAPVAL
*.DIOPERI
*.DIOAREA
*.EQUATION
*.SCALE METER
*.MEGA
.PARAM wireopt=9

*.GLOBAL gnd!

*.PIN gnd!

************************************************************************
* Library Name: UM_GF14
* Cell Name:    IBS_norm_rvt
* View Name:    schematic
************************************************************************

.SUBCKT IBS_norm_rvt IBS_IN IBSn_OUT IBSp_OUT VDD VSS
*.PININFO IBS_IN:B IBSn_OUT:B IBSp_OUT:B VDD:B VSS:B
MN2 IBSn_OUT net7 VSS VSS nfet m=4 l=14n nf=4 nfin=3 fpitch=48n cpp=78n 
+ ngcon=1 p_la=0 plorient=0
MN1 net7 net7 VSS VSS nfet m=1 l=14n nf=4 nfin=3 fpitch=48n cpp=78n ngcon=1 
+ p_la=0 plorient=0
MP2 IBSp_OUT IBS_IN VDD VDD pfet m=4 l=16n nf=4 nfin=3 fpitch=48n cpp=78n 
+ ngcon=1 p_la=0 plorient=0
MP1 IBS_IN IBS_IN VDD VDD pfet m=1 l=14n nf=4 nfin=3 fpitch=48n cpp=78n 
+ ngcon=1 p_la=0 plorient=0
MP0 net7 IBS_IN VDD VDD pfet m=1 l=14n nf=4 nfin=3 fpitch=48n cpp=78n ngcon=1 
+ p_la=0 plorient=0
.ENDS

************************************************************************
* Library Name: UM_GF14
* Cell Name:    IBS_norm_lvt
* View Name:    schematic
************************************************************************

.SUBCKT IBS_norm_lvt IBS_IN IBSn_OUT IBSp_OUT VDD VSS
*.PININFO IBS_IN:B IBSn_OUT:B IBSp_OUT:B VDD:B VSS:B
MN1 net7 net7 VSS VSS lvtnfet m=1 l=14n nf=3 nfin=3 fpitch=48n cpp=78n ngcon=1 
+ p_la=0 plorient=0
MN0 IBSn_OUT net7 VSS VSS lvtnfet m=4 l=14n nf=3 nfin=3 fpitch=48n cpp=78n 
+ ngcon=1 p_la=0 plorient=0
MP2 IBSp_OUT IBS_IN VDD VDD lvtpfet m=4 l=14n nf=3 nfin=3 fpitch=48n cpp=78n 
+ ngcon=1 p_la=0 plorient=0
MP1 IBS_IN IBS_IN VDD VDD lvtpfet m=1 l=14n nf=3 nfin=3 fpitch=48n cpp=78n 
+ ngcon=1 p_la=0 plorient=0
MP0 net7 IBS_IN VDD VDD lvtpfet m=1 l=14n nf=3 nfin=3 fpitch=48n cpp=78n 
+ ngcon=1 p_la=0 plorient=0
.ENDS

************************************************************************
* Library Name: UM_GF14
* Cell Name:    IBS_norm_hvt
* View Name:    schematic
************************************************************************

.SUBCKT IBS_norm_hvt IBS_IN IBSn_OUT IBSp_OUT VDD VSS
*.PININFO IBS_IN:B IBSn_OUT:B IBSp_OUT:B VDD:B VSS:B
MN1 net7 net7 VSS VSS hvtnfet m=1 l=14n nf=4 nfin=3 fpitch=48n cpp=78n ngcon=1 
+ p_la=0 plorient=0
MN0 IBSn_OUT net7 VSS VSS hvtnfet m=4 l=14n nf=4 nfin=3 fpitch=48n cpp=78n 
+ ngcon=1 p_la=0 plorient=0
MP2 IBSp_OUT IBS_IN VDD VDD hvtpfet m=4 l=16n nf=4 nfin=3 fpitch=48n cpp=78n 
+ ngcon=1 p_la=0 plorient=0
MP1 IBS_IN IBS_IN VDD VDD hvtpfet m=1 l=14n nf=4 nfin=3 fpitch=48n cpp=78n 
+ ngcon=1 p_la=0 plorient=0
MP0 net7 IBS_IN VDD VDD hvtpfet m=1 l=16n nf=4 nfin=3 fpitch=48n cpp=78n 
+ ngcon=1 p_la=0 plorient=0
.ENDS

************************************************************************
* Library Name: UM_GF14
* Cell Name:    IBS_norm_slvt
* View Name:    schematic
************************************************************************

.SUBCKT IBS_norm_slvt IBS_IN IBSn_OUT IBSp_OUT VDD VSS
*.PININFO IBS_IN:B IBSn_OUT:B IBSp_OUT:B VDD:B VSS:B
MN1 net7 net7 VSS VSS slvtnfet m=1 l=14n nf=3 nfin=3 fpitch=48n cpp=78n 
+ ngcon=1 p_la=0 plorient=0
MN0 IBSn_OUT net7 VSS VSS slvtnfet m=4 l=14n nf=3 nfin=3 fpitch=48n cpp=78n 
+ ngcon=1 p_la=0 plorient=0
MP2 IBSp_OUT IBS_IN VDD VDD slvtpfet m=4 l=14n nf=3 nfin=3 fpitch=48n cpp=78n 
+ ngcon=1 p_la=0 plorient=0
MP1 IBS_IN IBS_IN VDD VDD slvtpfet m=1 l=14n nf=3 nfin=3 fpitch=48n cpp=78n 
+ ngcon=1 p_la=0 plorient=0
MP0 net7 IBS_IN VDD VDD slvtpfet m=1 l=14n nf=3 nfin=3 fpitch=48n cpp=78n 
+ ngcon=1 p_la=0 plorient=0
.ENDS

************************************************************************
* Library Name: UM_GF14
* Cell Name:    Amp_diff_norm_rvt
* View Name:    schematic
************************************************************************

.SUBCKT Amp_diff_norm_rvt IBSn IN IP ON OP VDD VSS
*.PININFO IBSn:B IN:B IP:B ON:B OP:B VDD:B VSS:B
RR9 OP VDD $SUB=VDD $[rmres] m=1 l=1u w=280n r=3.83529K sbar=2 pbar=1 
+ orientation=1 r_cut=0
RR0 ON VDD $SUB=VDD $[rmres] m=1 l=1u w=280n r=3.83529K sbar=2 pbar=1 
+ orientation=1 r_cut=0
MN3 IBSn IBSn VSS VSS nfet m=4 l=14n nf=4 nfin=3 fpitch=48n cpp=78n ngcon=1 
+ p_la=0 plorient=0
MN2 OP IN net39 VSS nfet m=2 l=14n nf=4 nfin=3 fpitch=48n cpp=78n ngcon=1 
+ p_la=0 plorient=0
MN1 ON IP net39 VSS nfet m=2 l=14n nf=4 nfin=3 fpitch=48n cpp=78n ngcon=1 
+ p_la=0 plorient=0
MN0 net39 IBSn VSS VSS nfet m=4 l=14n nf=4 nfin=3 fpitch=48n cpp=78n ngcon=1 
+ p_la=0 plorient=0
.ENDS

************************************************************************
* Library Name: UM_GF14
* Cell Name:    Amp_diff_norm_lvt
* View Name:    schematic
************************************************************************

.SUBCKT Amp_diff_norm_lvt IBSn IN IP ON OP VDD VSS
*.PININFO IBSn:B IN:B IP:B ON:B OP:B VDD:B VSS:B
RR9 OP VDD $SUB=VDD $[rmres] m=1 l=1u w=280n r=3.83529K sbar=2 pbar=1 
+ orientation=1 r_cut=0
RR0 ON VDD $SUB=VDD $[rmres] m=1 l=1u w=280n r=3.83529K sbar=2 pbar=1 
+ orientation=1 r_cut=0
MN3 IBSn IBSn VSS VSS lvtnfet m=4 l=14n nf=2 nfin=3 fpitch=48n cpp=78n ngcon=1 
+ p_la=0 plorient=0
MN2 OP IN net39 VSS lvtnfet m=2 l=14n nf=2 nfin=3 fpitch=48n cpp=78n ngcon=1 
+ p_la=0 plorient=0
MN1 ON IP net39 VSS lvtnfet m=2 l=14n nf=2 nfin=3 fpitch=48n cpp=78n ngcon=1 
+ p_la=0 plorient=0
MN0 net39 IBSn VSS VSS lvtnfet m=4 l=14n nf=2 nfin=3 fpitch=48n cpp=78n 
+ ngcon=1 p_la=0 plorient=0
.ENDS

************************************************************************
* Library Name: UM_GF14
* Cell Name:    Amp_diff_norm_hvt
* View Name:    schematic
************************************************************************

.SUBCKT Amp_diff_norm_hvt IBSn IN IP ON OP VDD VSS
*.PININFO IBSn:B IN:B IP:B ON:B OP:B VDD:B VSS:B
MN3 IBSn IBSn VSS VSS hvtnfet m=4 l=14n nf=4 nfin=3 fpitch=48n cpp=78n ngcon=1 
+ p_la=0 plorient=0
MN2 OP IN net39 VSS hvtnfet m=2 l=14n nf=4 nfin=3 fpitch=48n cpp=78n ngcon=1 
+ p_la=0 plorient=0
MN1 ON IP net39 VSS hvtnfet m=2 l=14n nf=4 nfin=3 fpitch=48n cpp=78n ngcon=1 
+ p_la=0 plorient=0
MN0 net39 IBSn VSS VSS hvtnfet m=4 l=14n nf=4 nfin=3 fpitch=48n cpp=78n 
+ ngcon=1 p_la=0 plorient=0
RR9 OP VDD $SUB=VDD $[rmres] m=1 l=1u w=280n r=3.83529K sbar=2 pbar=1 
+ orientation=1 r_cut=0
RR0 ON VDD $SUB=VDD $[rmres] m=1 l=1u w=280n r=3.83529K sbar=2 pbar=1 
+ orientation=1 r_cut=0
.ENDS

************************************************************************
* Library Name: UM_GF14
* Cell Name:    Amp_diff_norm_slvt
* View Name:    schematic
************************************************************************

.SUBCKT Amp_diff_norm_slvt IBSn IN IP ON OP VDD VSS
*.PININFO IBSn:B IN:B IP:B ON:B OP:B VDD:B VSS:B
RR9 OP VDD $SUB=VDD $[rmres] m=1 l=1u w=280n r=3.83529K sbar=2 pbar=1 
+ orientation=1 r_cut=0
RR0 ON VDD $SUB=VDD $[rmres] m=1 l=1u w=280n r=3.83529K sbar=2 pbar=1 
+ orientation=1 r_cut=0
MN3 IBSn IBSn VSS VSS slvtnfet m=4 l=14n nf=2 nfin=3 fpitch=48n cpp=78n 
+ ngcon=1 p_la=0 plorient=0
MN2 OP IN net39 VSS slvtnfet m=2 l=14n nf=2 nfin=3 fpitch=48n cpp=78n ngcon=1 
+ p_la=0 plorient=0
MN1 ON IP net39 VSS slvtnfet m=2 l=14n nf=2 nfin=3 fpitch=48n cpp=78n ngcon=1 
+ p_la=0 plorient=0
MN0 net39 IBSn VSS VSS slvtnfet m=4 l=14n nf=2 nfin=3 fpitch=48n cpp=78n 
+ ngcon=1 p_la=0 plorient=0
.ENDS

************************************************************************
* Library Name: UM_GF14
* Cell Name:    TB_IBS_norm
* View Name:    schematic
************************************************************************

.SUBCKT TB_IBS_norm VDD
*.PININFO VDD:B
XI34 net021 net038 net022 VDD gnd! / IBS_norm_rvt
XI6 net013 net06 net032 VDD gnd! / IBS_norm_rvt
XI44 net065 net059 net035 VDD gnd! / IBS_norm_lvt
XI9 net011 net07 net012 VDD gnd! / IBS_norm_lvt
RR8 net014 gnd! 3K $[RP]
RR7 net012 gnd! 3K $[RP]
RR6 net032 gnd! 3K $[RP]
RR5 net031 gnd! 3K $[RP]
RR1 VDD net05 3K $[RP]
RR4 VDD net08 3K $[RP]
RR2 VDD net06 3K $[RP]
RR3 VDD net07 3K $[RP]
XI22 net046 net042 net018 VDD gnd! / IBS_norm_hvt
XI3 net015 net05 net031 VDD gnd! / IBS_norm_hvt
XI47 net033 net061 net034 VDD gnd! / IBS_norm_slvt
XI13 net010 net08 net014 VDD gnd! / IBS_norm_slvt
XI37 net022 net019 net020 rON rOP VDD gnd! / Amp_diff_norm_rvt
XI51 net035 net066 net029 lON lOP VDD gnd! / Amp_diff_norm_lvt
XI30 net018 net030 net028 hON hOP VDD gnd! / Amp_diff_norm_hvt
XI43 net034 net062 net063 sON sOP VDD gnd! / Amp_diff_norm_slvt
.ENDS

