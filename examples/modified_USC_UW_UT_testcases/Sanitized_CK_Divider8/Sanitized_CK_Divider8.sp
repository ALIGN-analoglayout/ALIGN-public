************************************************************************
* auCdl Netlist:
* 
* Library Name:  TempSensorLayout
* Top Cell Name: CK_DividerBy8
* View Name:     schematic
* Netlisted on:  May 17 01:21:37 2019
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
* Cell Name:    INVD2LVT
* View Name:    schematic
************************************************************************

.SUBCKT INVD2LVT I VDD VSS ZN
*.PININFO I:I ZN:O VDD:B VSS:B
MMU1_0-M_u2 ZN I VSS VSS lvtnfet l=LA w=WA m=1
MMU1_1-M_u2 ZN I VSS VSS lvtnfet l=LA w=WA m=1
MMU1_0-M_u3 ZN I VDD VDD lvtpfet l=LA w=WB m=1
MMU1_1-M_u3 ZN I VDD VDD lvtpfet l=LA w=WB m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    DCAP8LVT
* View Name:    schematic
************************************************************************

.SUBCKT DCAP8LVT VDD VSS
*.PININFO VDD:B VSS:B
MMI4 VSS net9 VSS VSS lvtnfet l=LB w=WC m=1
MM_u2 net11 net9 VSS VSS lvtnfet l=LA w=WC m=1
MMI3 VDD net11 VDD VDD lvtpfet l=LB w=WD m=1
MM_u1 net9 net11 VDD VDD lvtpfet l=LA w=WA m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    INVD1LVT
* View Name:    schematic
************************************************************************

.SUBCKT INVD1LVT I VDD VSS ZN
*.PININFO I:I ZN:O VDD:B VSS:B
MMU1-M_u2 ZN I VSS VSS lvtnfet l=LA w=WA m=1
MMU1-M_u3 ZN I VDD VDD lvtpfet l=LA w=WB m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    CKBD1LVT
* View Name:    schematic
************************************************************************

.SUBCKT CKBD1LVT I VDD VSS Z
*.PININFO I:I Z:O VDD:B VSS:B
MM_u15 net5 I VSS VSS lvtnfet l=LA w=WE m=1
MMU23 Z net5 VSS VSS lvtnfet l=LA w=WE m=1
MM_u3 net5 I VDD VDD lvtpfet l=LA w=WB m=1
MMU21 Z net5 VDD VDD lvtpfet l=LA w=WB m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    AN2D1LVT
* View Name:    schematic
************************************************************************

.SUBCKT AN2D1LVT A1 A2 VDD VSS Z
*.PININFO A1:I A2:I Z:O VDD:B VSS:B
MM_u3-M_u3 Z net5 VDD VDD lvtpfet l=LA w=WB m=1
MM_u2-M_u1 net5 A1 VDD VDD lvtpfet l=LA w=WF m=1
MM_u2-M_u2 net5 A2 VDD VDD lvtpfet l=LA w=WF m=1
MM_u3-M_u2 Z net5 VSS VSS lvtnfet l=LA w=WA m=1
MM_u2-M_u4 net17 A2 VSS VSS lvtnfet l=LA w=WG m=1
MM_u2-M_u3 net5 A1 net17 VSS lvtnfet l=LA w=WG m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    CKND1LVT
* View Name:    schematic
************************************************************************

.SUBCKT CKND1LVT I VDD VSS ZN
*.PININFO I:I ZN:O VDD:B VSS:B
MM_u2 ZN I VSS VSS lvtnfet l=LA w=WE m=1
MM_u1 ZN I VDD VDD lvtpfet l=LA w=WB m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    DFCND1LVT
* View Name:    schematic
************************************************************************

.SUBCKT DFCND1LVT CDN CP D Q QN VDD VSS
*.PININFO CDN:I CP:I D:I Q:O QN:O VDD:B VSS:B
MMI29-M_u2 QN net33 VSS VSS lvtnfet l=LA w=WA m=1
MMI4 net53 net5 VSS VSS lvtnfet l=LA w=WH m=1
MMI18 net33 net5 net79 VSS lvtnfet l=LA w=WI m=1
MMI21-M_u3 net95 net79 net9 VSS lvtnfet l=LA w=WA m=1
MMI13-M_u2 net81 net25 VSS VSS lvtnfet l=LA w=WJ m=1
MMI15 net81 net67 net79 VSS lvtnfet l=LA w=WJ m=1
MMI14-M_u2 net33 net95 VSS VSS lvtnfet l=LA w=WG m=1
MMI32-M_u2 net67 net5 VSS VSS lvtnfet l=LA w=WG m=1
MMI5 net25 D net53 VSS lvtnfet l=LA w=WH m=1
MMI49 net20 CDN VSS VSS lvtnfet l=LA w=WI m=1
MMI48 net17 net81 net20 VSS lvtnfet l=LA w=WI m=1
MMI27-M_u2 Q net95 VSS VSS lvtnfet l=LA w=WA m=1
MMI21-M_u4 net9 CDN VSS VSS lvtnfet l=LA w=WA m=1
MMI22-M_u2 net5 CP VSS VSS lvtnfet l=LA w=WG m=1
MMI47 net25 net67 net17 VSS lvtnfet l=LA w=WI m=1
MMI14-M_u3 net33 net95 VDD VDD lvtpfet l=LA w=WF m=1
MMI22-M_u3 net5 CP VDD VDD lvtpfet l=LA w=WF m=1
MMI32-M_u3 net67 net5 VDD VDD lvtpfet l=LA w=WF m=1
MMI43 net72 net81 VDD VDD lvtpfet l=LA w=WI m=1
MMI6 net25 D net104 VDD lvtpfet l=LA w=WL m=1
MMI29-M_u3 QN net33 VDD VDD lvtpfet l=LA w=WB m=1
MMI27-M_u3 Q net95 VDD VDD lvtpfet l=LA w=WB m=1
MMI44 net72 CDN VDD VDD lvtpfet l=LA w=WI m=1
MMI17 net33 net67 net79 VDD lvtpfet l=LA w=WI m=1
MMI13-M_u3 net81 net25 VDD VDD lvtpfet l=LA w=WK m=1
MMI21-M_u1 net95 net79 VDD VDD lvtpfet l=LA w=WM m=1
MMI16 net81 net5 net79 VDD lvtpfet l=LA w=WN m=1
MMI45 net25 net5 net72 VDD lvtpfet l=LA w=WI m=1
MMI7 net104 net67 VDD VDD lvtpfet l=LA w=WL m=1
MMI21-M_u2 net95 CDN VDD VDD lvtpfet l=LA w=WM m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    CKND3LVT
* View Name:    schematic
************************************************************************

.SUBCKT CKND3LVT I VDD VSS ZN
*.PININFO I:I ZN:O VDD:B VSS:B
MM_u1_0 ZN I VDD VDD lvtpfet l=LA w=WB m=1
MM_u1_2 ZN I VDD VDD lvtpfet l=LA w=WB m=1
MM_u1_1 ZN I VDD VDD lvtpfet l=LA w=WB m=1
MM_u2_1 ZN I VSS VSS lvtnfet l=LA w=WE m=1
MM_u2_0 ZN I VSS VSS lvtnfet l=LA w=WE m=1
MM_u2_2 ZN I VSS VSS lvtnfet l=LA w=WE m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    CKND8LVT
* View Name:    schematic
************************************************************************

.SUBCKT CKND8LVT I VDD VSS ZN
*.PININFO I:I ZN:O VDD:B VSS:B
MM_u1_7 ZN I VDD VDD lvtpfet l=LA w=WB m=1
MM_u1_0 ZN I VDD VDD lvtpfet l=LA w=WB m=1
MM_u1_3 ZN I VDD VDD lvtpfet l=LA w=WB m=1
MM_u1_2 ZN I VDD VDD lvtpfet l=LA w=WB m=1
MM_u1_4 ZN I VDD VDD lvtpfet l=LA w=WB m=1
MM_u1_6 ZN I VDD VDD lvtpfet l=LA w=WB m=1
MM_u1_1 ZN I VDD VDD lvtpfet l=LA w=WB m=1
MM_u1_5 ZN I VDD VDD lvtpfet l=LA w=WB m=1
**DDI3 VSS I ndio_lvt area=6.6e-14 pj=1.18e-06 m=1
MM_u2_1 ZN I VSS VSS lvtnfet l=LA w=WE m=1
MM_u2_6 ZN I VSS VSS lvtnfet l=LA w=WE m=1
MM_u2_3 ZN I VSS VSS lvtnfet l=LA w=WE m=1
MM_u2_4 ZN I VSS VSS lvtnfet l=LA w=WE m=1
MM_u2_7 ZN I VSS VSS lvtnfet l=LA w=WE m=1
MM_u2_0 ZN I VSS VSS lvtnfet l=LA w=WE m=1
MM_u2_2 ZN I VSS VSS lvtnfet l=LA w=WE m=1
MM_u2_5 ZN I VSS VSS lvtnfet l=LA w=WE m=1
.ENDS

************************************************************************
* Library Name: TempSensorLayout
* Cell Name:    DFCND1LVT_schematic
* View Name:    schematic
************************************************************************

.SUBCKT DFCND1LVT_schematic CDN CP D QN VDD VSS
*.PININFO CDN:I CP:I D:I QN:O VDD:B VSS:B
MMI29-M_u2 QN net33 VSS VSS lvtnfet l=LA w=WA m=1
MMI4 net53 net5 VSS VSS lvtnfet l=LA w=WH m=1
MMI18 net33 net5 net79 VSS lvtnfet l=LA w=WI m=1
MMI21-M_u3 net95 net79 net9 VSS lvtnfet l=LA w=WA m=1
MMI13-M_u2 net81 net25 VSS VSS lvtnfet l=LA w=WJ m=1
MMI15 net81 net67 net79 VSS lvtnfet l=LA w=WJ m=1
MMI14-M_u2 net33 net95 VSS VSS lvtnfet l=LA w=WG m=1
MMI32-M_u2 net67 net5 VSS VSS lvtnfet l=LA w=WG m=1
MMI5 net25 D net53 VSS lvtnfet l=LA w=WH m=1
MMI49 net20 CDN VSS VSS lvtnfet l=LA w=WI m=1
MMI48 net17 net81 net20 VSS lvtnfet l=LA w=WI m=1
MMI27-M_u2 net036 net95 VSS VSS lvtnfet l=LA w=WA m=1
MMI21-M_u4 net9 CDN VSS VSS lvtnfet l=LA w=WA m=1
MMI22-M_u2 net5 CP VSS VSS lvtnfet l=LA w=WG m=1
MMI47 net25 net67 net17 VSS lvtnfet l=LA w=WI m=1
MMI14-M_u3 net33 net95 VDD VDD lvtpfet l=LA w=WF m=1
MMI22-M_u3 net5 CP VDD VDD lvtpfet l=LA w=WF m=1
MMI32-M_u3 net67 net5 VDD VDD lvtpfet l=LA w=WF m=1
MMI43 net72 net81 VDD VDD lvtpfet l=LA w=WI m=1
MMI6 net25 D net104 VDD lvtpfet l=LA w=WL m=1
MMI29-M_u3 QN net33 VDD VDD lvtpfet l=LA w=WB m=1
MMI27-M_u3 net036 net95 VDD VDD lvtpfet l=LA w=WB m=1
MMI44 net72 CDN VDD VDD lvtpfet l=LA w=WI m=1
MMI17 net33 net67 net79 VDD lvtpfet l=LA w=WI m=1
MMI13-M_u3 net81 net25 VDD VDD lvtpfet l=LA w=WK m=1
MMI21-M_u1 net95 net79 VDD VDD lvtpfet l=LA w=WM m=1
MMI16 net81 net5 net79 VDD lvtpfet l=LA w=WN m=1
MMI45 net25 net5 net72 VDD lvtpfet l=LA w=WI m=1
MMI7 net104 net67 VDD VDD lvtpfet l=LA w=WL m=1
MMI21-M_u2 net95 CDN VDD VDD lvtpfet l=LA w=WM m=1
.ENDS

************************************************************************
* Library Name: TempSensorLayout
* Cell Name:    CK_DividerBy8
* View Name:    schematic
************************************************************************

.SUBCKT Sanitized_CK_Divider8 CKIN COMPEN INPHASE OUTPHASE PRESET QPHASE VDD VSS
*.PININFO CKIN:I PRESET:I COMPEN:O INPHASE:O OUTPHASE:O QPHASE:O VDD:B VSS:B
XI14 PRESET VDD VSS net039 / INVD2LVT
XI51<18> VDD VSS / DCAP8LVT
XI51<17> VDD VSS / DCAP8LVT
XI51<16> VDD VSS / DCAP8LVT
XI51<15> VDD VSS / DCAP8LVT
XI51<14> VDD VSS / DCAP8LVT
XI51<13> VDD VSS / DCAP8LVT
XI51<12> VDD VSS / DCAP8LVT
XI51<11> VDD VSS / DCAP8LVT
XI51<10> VDD VSS / DCAP8LVT
XI51<9> VDD VSS / DCAP8LVT
XI51<8> VDD VSS / DCAP8LVT
XI51<7> VDD VSS / DCAP8LVT
XI51<6> VDD VSS / DCAP8LVT
XI51<5> VDD VSS / DCAP8LVT
XI51<4> VDD VSS / DCAP8LVT
XI51<3> VDD VSS / DCAP8LVT
XI51<2> VDD VSS / DCAP8LVT
XI51<1> VDD VSS / DCAP8LVT
XI51<0> VDD VSS / DCAP8LVT
XI50 PRESET VDD VSS net048 / INVD1LVT
XI6 CKIN VDD VSS net45 / CKBD1LVT
XI139 net048 net015 VDD VSS COMPEN / AN2D1LVT
XI5 net45 VDD VSS net49 / CKND1LVT
XI8 net039 net011 net48 net015 net48 VDD VSS / DFCND1LVT
XI7 net039 net018 net50 net076 net50 VDD VSS / DFCND1LVT
XI43 net076 VDD VSS net059 / CKND3LVT
XI39 net48 VDD VSS net063 / CKND3LVT
XI37 net015 VDD VSS net064 / CKND3LVT
XI42 net059 VDD VSS QPHASE / CKND8LVT
XI38 net063 VDD VSS OUTPHASE / CKND8LVT
XI20 net064 VDD VSS INPHASE / CKND8LVT
XI29 net039 net49 net016 net016 VDD VSS / DFCND1LVT_schematic
XI28 net039 net016 net018 net018 VDD VSS / DFCND1LVT_schematic
XI27 net039 net45 net040 net040 VDD VSS / DFCND1LVT_schematic
XI26 net039 net040 net011 net011 VDD VSS / DFCND1LVT_schematic
.ENDS

