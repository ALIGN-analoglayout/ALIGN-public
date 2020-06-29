************************************************************************
* auCdl Netlist:
* 
* Library Name:  TempSensorLayout
* Top Cell Name: CrossingDetector
* View Name:     schematic
* Netlisted on:  May 17 01:23:47 2019
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
* Cell Name:    MUX2D2LVT
* View Name:    schematic
************************************************************************

.SUBCKT MUX2D2LVT I0 I1 S VDD VSS Z
*.PININFO I0:I I1:I S:I Z:O VDD:B VSS:B
MMU18-M_u3 net25 net17 net7 VSS lvtnfet l=LA w=WB m=1
MMI16-M_u2 net25 I0 VSS VSS lvtnfet l=LA w=WB m=1
MMI17-M_u2 net17 S VSS VSS lvtnfet l=LA w=WI m=1
MMI13-M_u3 net9 S net7 VSS lvtnfet l=LA w=WC m=1
MMI14-M_u2 net9 I1 VSS VSS lvtnfet l=LA w=WG m=1
MMU29_0-M_u2 Z net7 VSS VSS lvtnfet l=LA w=WG m=1
MMU29_1-M_u2 Z net7 VSS VSS lvtnfet l=LA w=WG m=1
MMI17-M_u3 net17 S VDD VDD lvtpfet l=LA w=WD m=1
MMI14-M_u3 net9 I1 VDD VDD lvtpfet l=LA w=WA m=1
MMU29_1-M_u3 Z net7 VDD VDD lvtpfet l=LA w=WA m=1
MMI16-M_u3 net25 I0 VDD VDD lvtpfet l=LA w=WE m=1
MMU29_0-M_u3 Z net7 VDD VDD lvtpfet l=LA w=WA m=1
MMI13-M_u2 net9 net17 net7 VDD lvtpfet l=LA w=WF m=1
MMU18-M_u2 net25 S net7 VDD lvtpfet l=LA w=WH m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    CKBD1LVT
* View Name:    schematic
************************************************************************

.SUBCKT CKBD1LVT I VDD VSS Z
*.PININFO I:I Z:O VDD:B VSS:B
MM_u15 net5 I VSS VSS lvtnfet l=LA w=WJ m=1
MMU23 Z net5 VSS VSS lvtnfet l=LA w=WJ m=1
MM_u3 net5 I VDD VDD lvtpfet l=LA w=WA m=1
MMU21 Z net5 VDD VDD lvtpfet l=LA w=WA m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    CKND1LVT
* View Name:    schematic
************************************************************************

.SUBCKT CKND1LVT I VDD VSS ZN
*.PININFO I:I ZN:O VDD:B VSS:B
MM_u2 ZN I VSS VSS lvtnfet l=LA w=WJ m=1
MM_u1 ZN I VDD VDD lvtpfet l=LA w=WA m=1
.ENDS

************************************************************************
* Library Name: TempSensorLayout
* Cell Name:    CrossingDetector_Mux
* View Name:    schematic
************************************************************************

.SUBCKT CrossingDetector_Mux IN SS VDD VO VSS
*.PININFO IN:I SS:I VO:O VDD:B VSS:B
XI18 net012 net032 SS VDD VSS VO / MUX2D2LVT
XI16 net033 VDD VSS net012 / CKBD1LVT
XI10 net012 VDD VSS net032 / CKBD1LVT
XI9 net015 VDD VSS net033 / CKBD1LVT
MM2 net06 IN VDD VDD lvtpfet l=LA w=WK m=2
MM1 net06 IN VSS VSS lvtnfet l=LA w=WJ m=2
XI15 net06 VDD VSS net015 / CKND1LVT
.ENDS

************************************************************************
* Library Name: TempSensorLayout
* Cell Name:    CrossingDetector
* View Name:    schematic
************************************************************************

.SUBCKT Sanitized_LevelCrossingDetector QD QPHASE SQ SS VCP VCPS VDD VSS
*.PININFO QPHASE:I SQ:I SS:I VCP:I QD:O VCPS:O VDD:B VSS:B
XI2 QPHASE SQ VDD QD VSS / CrossingDetector_Mux
XI0 VCP SS VDD VCPS VSS / CrossingDetector_Mux
.ENDS

