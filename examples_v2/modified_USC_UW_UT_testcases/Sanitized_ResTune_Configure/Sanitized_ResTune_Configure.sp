************************************************************************
* auCdl Netlist:
* 
* Library Name:  TempSensorLayout
* Top Cell Name: ResTune_CFG
* View Name:     schematic
* Netlisted on:  May 17 01:29:50 2019
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
* Cell Name:    DCAP8LVT
* View Name:    schematic
************************************************************************

.SUBCKT DCAP8LVT VDD VSS
*.PININFO VDD:B VSS:B
MMI4 VSS net9 VSS VSS lvtnfet l=LB w=WC m=1
MM_u2 net11 net9 VSS VSS lvtnfet l=LA w=WC m=1
MMI3 VDD net11 VDD VDD lvtpfet l=LB w=WA m=1
MM_u1 net9 net11 VDD VDD lvtpfet l=LA w=WB m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    DCAP16LVT
* View Name:    schematic
************************************************************************

.SUBCKT DCAP16LVT VDD VSS
*.PININFO VDD:B VSS:B
MMI4 VSS net11 VSS VSS lvtnfet l=LB w=WC m=1
MMI8 VSS net11 VSS VSS lvtnfet l=LB w=WC m=1
MM_u2 net5 net11 VSS VSS lvtnfet l=LA w=WC m=1
MMI7 VSS net11 VSS VSS lvtnfet l=LB w=WC m=1
MMI3 VDD net5 VDD VDD lvtpfet l=LB w=WA m=1
MMI6 VDD net5 VDD VDD lvtpfet l=LB w=WA m=1
MM_u1 net11 net5 VDD VDD lvtpfet l=LA w=WB m=1
MMI5 VDD net5 VDD VDD lvtpfet l=LB w=WA m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    DCAP32LVT
* View Name:    schematic
************************************************************************

.SUBCKT DCAP32LVT VDD VSS
*.PININFO VDD:B VSS:B
MMI38 VSS net11 VSS VSS lvtnfet l=LC w=WC m=1
MMI6 VSS net11 VSS VSS lvtnfet l=LC w=WC m=1
MMI39 VSS net11 VSS VSS lvtnfet l=LC w=WC m=1
MMI37 VSS net11 VSS VSS lvtnfet l=LC w=WC m=1
MM_u2 net5 net11 VSS VSS lvtnfet l=LA w=WC m=1
MMI36 VSS net11 VSS VSS lvtnfet l=LC w=WC m=1
MMI33 VDD net5 VDD VDD lvtpfet l=LC w=WA m=1
MM_u1 net11 net5 VDD VDD lvtpfet l=LA w=WB m=1
MMI34 VDD net5 VDD VDD lvtpfet l=LC w=WA m=1
MMI35 VDD net5 VDD VDD lvtpfet l=LC w=WA m=1
MMI32 VDD net5 VDD VDD lvtpfet l=LC w=WA m=1
MMI26 VDD net5 VDD VDD lvtpfet l=LC w=WA m=1
.ENDS

************************************************************************
* Library Name: TempSensorLayout
* Cell Name:    BUFTD16LVT
* View Name:    schematic
************************************************************************

.SUBCKT BUFTD16LVT I OE VDD VSS Z
*.PININFO I:I OE:I Z:O VDD:B VSS:B
MMI6-M_u4 net37 I VSS VSS lvtnfet l=LA w=WB m=1
MMI5_1-M_u4 net25 net5 VSS VSS lvtnfet l=LA w=WB m=1
MMI5_0-M_u3 net25 I VSS VSS lvtnfet l=LA w=WB m=1
MMI5_0-M_u4 net25 net5 VSS VSS lvtnfet l=LA w=WB m=1
MMI7-M_u3 net13 OE net9 VSS lvtnfet l=LA w=WD m=1
MM_u7 Z net25 VSS VSS lvtnfet l=LA w=WG m=1
MMI6-M_u3 net13 OE net37 VSS lvtnfet l=LA w=WD m=1
MMI7-M_u4 net9 I VSS VSS lvtnfet l=LA w=WB m=1
MM_u17-M_u2 net5 OE VSS VSS lvtnfet l=LA w=WB m=1
MMI5_1-M_u3 net25 I VSS VSS lvtnfet l=LA w=WB m=1
MM_u17-M_u3 net5 OE VDD VDD lvtpfet l=LA w=WE m=1
MMI5_0-M_u1 net72 I VDD VDD lvtpfet l=LA w=WF m=1
MMI5_0-M_u2 net25 net5 net72 VDD lvtpfet l=LA w=WF m=1
MMI6-M_u2 net13 I VDD VDD lvtpfet l=LA w=WE m=1
MMI7-M_u1 net13 OE VDD VDD lvtpfet l=LA w=WE m=1
MM_u6 Z net13 VDD VDD lvtpfet l=LA w=WH m=1
MMI5_1-M_u1 net53 I VDD VDD lvtpfet l=LA w=WF m=1
MMI7-M_u2 net13 I VDD VDD lvtpfet l=LA w=WE m=1
MMI5_1-M_u2 net25 net5 net53 VDD lvtpfet l=LA w=WF m=1
MMI6-M_u1 net13 OE VDD VDD lvtpfet l=LA w=WE m=1
.ENDS

************************************************************************
* Library Name: TempSensorLayout
* Cell Name:    ResTune_CFG
* View Name:    schematic
************************************************************************

.SUBCKT Sanitized_ResTune_Configure INPH INPHASE<7> INPHASE<6> INPHASE<5> INPHASE<4> 
+ INPHASE<3> INPHASE<2> INPHASE<1> INPHASE<0> OUTPH OUTPHASE<7> OUTPHASE<6> 
+ OUTPHASE<5> OUTPHASE<4> OUTPHASE<3> OUTPHASE<2> OUTPHASE<1> OUTPHASE<0> 
+ RESEN<7> RESEN<6> RESEN<5> RESEN<4> RESEN<3> RESEN<2> RESEN<1> RESEN<0> VDD 
+ VSS
*.PININFO INPH:I OUTPH:I RESEN<7>:I RESEN<6>:I RESEN<5>:I RESEN<4>:I 
*.PININFO RESEN<3>:I RESEN<2>:I RESEN<1>:I RESEN<0>:I INPHASE<7>:O 
*.PININFO INPHASE<6>:O INPHASE<5>:O INPHASE<4>:O INPHASE<3>:O INPHASE<2>:O 
*.PININFO INPHASE<1>:O INPHASE<0>:O OUTPHASE<7>:O OUTPHASE<6>:O OUTPHASE<5>:O 
*.PININFO OUTPHASE<4>:O OUTPHASE<3>:O OUTPHASE<2>:O OUTPHASE<1>:O 
*.PININFO OUTPHASE<0>:O VDD:B VSS:B
XI3<1> VDD VSS / DCAP8LVT
XI3<0> VDD VSS / DCAP8LVT
XI2<7> VDD VSS / DCAP16LVT
XI2<6> VDD VSS / DCAP16LVT
XI2<5> VDD VSS / DCAP16LVT
XI2<4> VDD VSS / DCAP16LVT
XI2<3> VDD VSS / DCAP16LVT
XI2<2> VDD VSS / DCAP16LVT
XI2<1> VDD VSS / DCAP16LVT
XI2<0> VDD VSS / DCAP16LVT
XI4<3> VDD VSS / DCAP32LVT
XI4<2> VDD VSS / DCAP32LVT
XI4<1> VDD VSS / DCAP32LVT
XI4<0> VDD VSS / DCAP32LVT
XI1<7> INPH RESEN<7> VDD VSS INPHASE<7> / BUFTD16LVT
XI1<6> INPH RESEN<6> VDD VSS INPHASE<6> / BUFTD16LVT
XI1<5> INPH RESEN<5> VDD VSS INPHASE<5> / BUFTD16LVT
XI1<4> INPH RESEN<4> VDD VSS INPHASE<4> / BUFTD16LVT
XI1<3> INPH RESEN<3> VDD VSS INPHASE<3> / BUFTD16LVT
XI1<2> INPH RESEN<2> VDD VSS INPHASE<2> / BUFTD16LVT
XI1<1> INPH RESEN<1> VDD VSS INPHASE<1> / BUFTD16LVT
XI1<0> INPH RESEN<0> VDD VSS INPHASE<0> / BUFTD16LVT
XI0<7> OUTPH RESEN<7> VDD VSS OUTPHASE<7> / BUFTD16LVT
XI0<6> OUTPH RESEN<6> VDD VSS OUTPHASE<6> / BUFTD16LVT
XI0<5> OUTPH RESEN<5> VDD VSS OUTPHASE<5> / BUFTD16LVT
XI0<4> OUTPH RESEN<4> VDD VSS OUTPHASE<4> / BUFTD16LVT
XI0<3> OUTPH RESEN<3> VDD VSS OUTPHASE<3> / BUFTD16LVT
XI0<2> OUTPH RESEN<2> VDD VSS OUTPHASE<2> / BUFTD16LVT
XI0<1> OUTPH RESEN<1> VDD VSS OUTPHASE<1> / BUFTD16LVT
XI0<0> OUTPH RESEN<0> VDD VSS OUTPHASE<0> / BUFTD16LVT
.ENDS

