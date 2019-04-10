************************************************************************
* auCdl Netlist:
* 
* Library Name:  UM_GF14
* Top Cell Name: TH
* View Name:     schematic
* Netlisted on:  Jan  4 14:33:35 2019
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



************************************************************************
* Library Name: UM_GF14
* Cell Name:    TH
* View Name:    schematic
************************************************************************

.SUBCKT TH CN CP IN IP ON OP VCM VDD VSS
*.PININFO CN:B CP:B IN:B IP:B ON:B OP:B VCM:B VDD:B VSS:B
MP0 IN CN ON VDD slvtpfet m=4 l=14n nf=16 nfin=8 fpitch=48n cpp=78n ngcon=1 
+ p_la=0 plorient=0
MN1 IP CN OP VDD slvtpfet m=4 l=14n nf=16 nfin=8 fpitch=48n cpp=78n ngcon=1 
+ p_la=0 plorient=0
MN2 ON CP IN VSS slvtnfet m=4 l=14n nf=16 nfin=8 fpitch=48n cpp=78n ngcon=1 
+ p_la=0 plorient=0
MN0 OP CP IP VSS slvtnfet m=4 l=14n nf=16 nfin=8 fpitch=48n cpp=78n ngcon=1 
+ p_la=0 plorient=0
CC7 ON VCM $[vncap] $SUB=VSS m=1 w=3.555u l=7.165u botlev=15 toplev=17 volt=2.5
CC6 ON VCM $[vncap] $SUB=VSS m=1 w=3.555u l=7.165u botlev=15 toplev=17 volt=2.5
CC5 ON VCM $[vncap] $SUB=VSS m=1 w=3.555u l=7.165u botlev=15 toplev=17 volt=2.5
CC4 ON VCM $[vncap] $SUB=VSS m=1 w=3.555u l=7.165u botlev=15 toplev=17 volt=2.5
CC3 OP VCM $[vncap] $SUB=VSS m=1 w=3.555u l=7.165u botlev=15 toplev=17 volt=2.5
CC2 OP VCM $[vncap] $SUB=VSS m=1 w=3.555u l=7.165u botlev=15 toplev=17 volt=2.5
CC1 OP VCM $[vncap] $SUB=VSS m=1 w=3.555u l=7.165u botlev=15 toplev=17 volt=2.5
CC0 OP VCM $[vncap] $SUB=VSS m=1 w=3.555u l=7.165u botlev=15 toplev=17 volt=2.5
.ENDS

