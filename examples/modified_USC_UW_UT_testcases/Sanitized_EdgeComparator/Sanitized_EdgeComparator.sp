************************************************************************
* auCdl Netlist:
*
* Library Name:  TempSensorLayout
* Top Cell Name: EdgeComparator
* View Name:     schematic
* Netlisted on:  May 17 01:22:45 2019
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
.PARAM



************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    NR2D2LVT
* View Name:    schematic
************************************************************************

.SUBCKT NR2D2LVT A1 A2 VDD VSS ZN
*.PININFO A1:I A2:I ZN:O VDD:B VSS:B
MMI1_1-M_u3 ZN A2 VSS VSS lvtnfet l=LA w=WD m=1
MMI1_1-M_u4 ZN A1 VSS VSS lvtnfet l=LA w=WD m=1
MMI1_0-M_u4 ZN A1 VSS VSS lvtnfet l=LA w=WD m=1
MMI1_0-M_u3 ZN A2 VSS VSS lvtnfet l=LA w=WD m=1
MMI1_1-M_u2 ZN A1 net17 VDD lvtpfet l=LA w=WE m=1
MMI1_0-M_u1 net25 A2 VDD VDD lvtpfet l=LA w=WE m=1
MMI1_0-M_u2 ZN A1 net25 VDD lvtpfet l=LA w=WE m=1
MMI1_1-M_u1 net17 A2 VDD VDD lvtpfet l=LA w=WE m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    INVD1LVT
* View Name:    schematic
************************************************************************

.SUBCKT INVD1LVT I VDD VSS ZN
*.PININFO I:I ZN:O VDD:B VSS:B
MMU1-M_u2 ZN I VSS VSS lvtnfet l=LA w=WD m=1
MMU1-M_u3 ZN I VDD VDD lvtpfet l=LA w=WF m=1
.ENDS

************************************************************************
* Library Name: TempSensorLayout
* Cell Name:    EdgeComparator
* View Name:    schematic
************************************************************************

.SUBCKT Sanitized_EdgeComparator COMPEN PRESET VDD VIN VIP VONL VOPL VSS
*.PININFO COMPEN:I PRESET:I VIN:I VIP:I VONL:O VOPL:O VDD:B VSS:B
MM7 net028 net029 VDD VDD lvtpfet l=LB w=WA m=1
MM6 net25 net033 VDD VDD lvtpfet l=LB w=WA m=1
MM2 net25 VIN VDD VDD lvtpfet l=LB w=WA m=1
MM0 net028 VIP VDD VDD lvtpfet l=LB w=WA m=1
MM45 net25 net028 VDD VDD lvtpfet l=LB w=WA m=4
MM3 net028 net25 VDD VDD lvtpfet l=LB w=WA m=4
XI95 VOP VOPL VDD VSS VONL NR2D2LVT
XI96 VON VONL VDD VSS VOPL NR2D2LVT
MM5 net032 net028 net015 VSS lvtnfet l=LC w=WB m=2
MM4 net24 net25 net015 VSS lvtnfet l=LC w=WB m=2
MM28 net25 VIN net032 VSS lvtnfet l=LC w=WC m=2
MM1 net028 VIP net24 VSS lvtnfet l=LC w=WC m=2
MM22 net015 COMPEN VSS VSS lvtnfet l=LC w=WB m=2
XI5 PRESET VDD VSS net029 INVD1LVT
XI4 PRESET VDD VSS net033 INVD1LVT
XI3 net028 VDD VSS VOP INVD1LVT
XI1 net25 VDD VSS VON INVD1LVT
.ENDS

