************************************************************************
* auCdl Netlist:
*
* Library Name:  TempSensorLayout_PostLayout
* Top Cell Name: TempSensorCore_Post_Decap
* View Name:     schematic
* Netlisted on:  May 17 01:08:24 2019
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
MMU1_0-M_u2 ZN I VSS VSS lvtnfet l=LA w=WV m=1
MMU1_1-M_u2 ZN I VSS VSS lvtnfet l=LA w=WV m=1
MMU1_0-M_u3 ZN I VDD VDD lvtpfet l=LA w=WAL m=1
MMU1_1-M_u3 ZN I VDD VDD lvtpfet l=LA w=WAL m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    DCAP8LVT
* View Name:    schematic
************************************************************************

.SUBCKT DCAP8LVT VDD VSS
*.PININFO VDD:B VSS:B
MMI4 VSS net9 VSS VSS lvtnfet l=LG w=WT m=1
MM_u2 net11 net9 VSS VSS lvtnfet l=LA w=WT m=1
MMI3 VDD net11 VDD VDD lvtpfet l=LG w=WAI m=1
MM_u1 net9 net11 VDD VDD lvtpfet l=LA w=WV m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    INVD1LVT
* View Name:    schematic
************************************************************************

.SUBCKT INVD1LVT I VDD VSS ZN
*.PININFO I:I ZN:O VDD:B VSS:B
MMU1-M_u2 ZN I VSS VSS lvtnfet l=LA w=WV m=1
MMU1-M_u3 ZN I VDD VDD lvtpfet l=LA w=WAL m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    CKBD1LVT
* View Name:    schematic
************************************************************************

.SUBCKT CKBD1LVT I VDD VSS Z
*.PININFO I:I Z:O VDD:B VSS:B
MM_u15 net5 I VSS VSS lvtnfet l=LA w=WU m=1
MMU23 Z net5 VSS VSS lvtnfet l=LA w=WU m=1
MM_u3 net5 I VDD VDD lvtpfet l=LA w=WAL m=1
MMU21 Z net5 VDD VDD lvtpfet l=LA w=WAL m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    AN2D1LVT
* View Name:    schematic
************************************************************************

.SUBCKT AN2D1LVT A1 A2 VDD VSS Z
*.PININFO A1:I A2:I Z:O VDD:B VSS:B
MM_u3-M_u3 Z net5 VDD VDD lvtpfet l=LA w=WAL m=1
MM_u2-M_u1 net5 A1 VDD VDD lvtpfet l=LA w=WI m=1
MM_u2-M_u2 net5 A2 VDD VDD lvtpfet l=LA w=WI m=1
MM_u3-M_u2 Z net5 VSS VSS lvtnfet l=LA w=WV m=1
MM_u2-M_u4 net17 A2 VSS VSS lvtnfet l=LA w=WB m=1
MM_u2-M_u3 net5 A1 net17 VSS lvtnfet l=LA w=WB m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    CKND1LVT
* View Name:    schematic
************************************************************************

.SUBCKT CKND1LVT I VDD VSS ZN
*.PININFO I:I ZN:O VDD:B VSS:B
MM_u2 ZN I VSS VSS lvtnfet l=LA w=WU m=1
MM_u1 ZN I VDD VDD lvtpfet l=LA w=WAL m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    DFCND1LVT
* View Name:    schematic
************************************************************************

.SUBCKT DFCND1LVT CDN CP D Q QN VDD VSS
*.PININFO CDN:I CP:I D:I Q:O QN:O VDD:B VSS:B
MMI29-M_u2 QN net33 VSS VSS lvtnfet l=LA w=WV m=1
MMI4 net53 net5 VSS VSS lvtnfet l=LA w=WW m=1
MMI18 net33 net5 net79 VSS lvtnfet l=LA w=WA m=1
MMI21-M_u3 net95 net79 net9 VSS lvtnfet l=LA w=WV m=1
MMI13-M_u2 net81 net25 VSS VSS lvtnfet l=LA w=WC m=1
MMI15 net81 net67 net79 VSS lvtnfet l=LA w=WC m=1
MMI14-M_u2 net33 net95 VSS VSS lvtnfet l=LA w=WB m=1
MMI32-M_u2 net67 net5 VSS VSS lvtnfet l=LA w=WB m=1
MMI5 net25 D net53 VSS lvtnfet l=LA w=WW m=1
MMI49 net20 CDN VSS VSS lvtnfet l=LA w=WA m=1
MMI48 net17 net81 net20 VSS lvtnfet l=LA w=WA m=1
MMI27-M_u2 Q net95 VSS VSS lvtnfet l=LA w=WV m=1
MMI21-M_u4 net9 CDN VSS VSS lvtnfet l=LA w=WV m=1
MMI22-M_u2 net5 CP VSS VSS lvtnfet l=LA w=WB m=1
MMI47 net25 net67 net17 VSS lvtnfet l=LA w=WA m=1
MMI14-M_u3 net33 net95 VDD VDD lvtpfet l=LA w=WI m=1
MMI22-M_u3 net5 CP VDD VDD lvtpfet l=LA w=WI m=1
MMI32-M_u3 net67 net5 VDD VDD lvtpfet l=LA w=WI m=1
MMI43 net72 net81 VDD VDD lvtpfet l=LA w=WA m=1
MMI6 net25 D net104 VDD lvtpfet l=LA w=WAH m=1
MMI29-M_u3 QN net33 VDD VDD lvtpfet l=LA w=WAL m=1
MMI27-M_u3 Q net95 VDD VDD lvtpfet l=LA w=WAL m=1
MMI44 net72 CDN VDD VDD lvtpfet l=LA w=WA m=1
MMI17 net33 net67 net79 VDD lvtpfet l=LA w=WA m=1
MMI13-M_u3 net81 net25 VDD VDD lvtpfet l=LA w=WJ m=1
MMI21-M_u1 net95 net79 VDD VDD lvtpfet l=LA w=WX m=1
MMI16 net81 net5 net79 VDD lvtpfet l=LA w=WK m=1
MMI45 net25 net5 net72 VDD lvtpfet l=LA w=WA m=1
MMI7 net104 net67 VDD VDD lvtpfet l=LA w=WAH m=1
MMI21-M_u2 net95 CDN VDD VDD lvtpfet l=LA w=WX m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    CKND3LVT
* View Name:    schematic
************************************************************************

.SUBCKT CKND3LVT I VDD VSS ZN
*.PININFO I:I ZN:O VDD:B VSS:B
MM_u1_0 ZN I VDD VDD lvtpfet l=LA w=WAL m=1
MM_u1_2 ZN I VDD VDD lvtpfet l=LA w=WAL m=1
MM_u1_1 ZN I VDD VDD lvtpfet l=LA w=WAL m=1
MM_u2_1 ZN I VSS VSS lvtnfet l=LA w=WU m=1
MM_u2_0 ZN I VSS VSS lvtnfet l=LA w=WU m=1
MM_u2_2 ZN I VSS VSS lvtnfet l=LA w=WU m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    CKND8LVT
* View Name:    schematic
************************************************************************

.SUBCKT CKND8LVT I VDD VSS ZN
*.PININFO I:I ZN:O VDD:B VSS:B
MM_u1_7 ZN I VDD VDD lvtpfet l=LA w=WAL m=1
MM_u1_0 ZN I VDD VDD lvtpfet l=LA w=WAL m=1
MM_u1_3 ZN I VDD VDD lvtpfet l=LA w=WAL m=1
MM_u1_2 ZN I VDD VDD lvtpfet l=LA w=WAL m=1
MM_u1_4 ZN I VDD VDD lvtpfet l=LA w=WAL m=1
MM_u1_6 ZN I VDD VDD lvtpfet l=LA w=WAL m=1
MM_u1_1 ZN I VDD VDD lvtpfet l=LA w=WAL m=1
MM_u1_5 ZN I VDD VDD lvtpfet l=LA w=WAL m=1
MM_u2_1 ZN I VSS VSS lvtnfet l=LA w=WU m=1
MM_u2_6 ZN I VSS VSS lvtnfet l=LA w=WU m=1
MM_u2_3 ZN I VSS VSS lvtnfet l=LA w=WU m=1
MM_u2_4 ZN I VSS VSS lvtnfet l=LA w=WU m=1
MM_u2_7 ZN I VSS VSS lvtnfet l=LA w=WU m=1
MM_u2_0 ZN I VSS VSS lvtnfet l=LA w=WU m=1
MM_u2_2 ZN I VSS VSS lvtnfet l=LA w=WU m=1
MM_u2_5 ZN I VSS VSS lvtnfet l=LA w=WU m=1
.ENDS

************************************************************************
* Library Name: TempSensorLayout
* Cell Name:    DFCND1LVT_schematic
* View Name:    schematic
************************************************************************

.SUBCKT DFCND1LVT_schematic CDN CP D QN VDD VSS
*.PININFO CDN:I CP:I D:I QN:O VDD:B VSS:B
MMI29-M_u2 QN net33 VSS VSS lvtnfet l=LA w=WV m=1
MMI4 net53 net5 VSS VSS lvtnfet l=LA w=WW m=1
MMI18 net33 net5 net79 VSS lvtnfet l=LA w=WA m=1
MMI21-M_u3 net95 net79 net9 VSS lvtnfet l=LA w=WV m=1
MMI13-M_u2 net81 net25 VSS VSS lvtnfet l=LA w=WC m=1
MMI15 net81 net67 net79 VSS lvtnfet l=LA w=WC m=1
MMI14-M_u2 net33 net95 VSS VSS lvtnfet l=LA w=WB m=1
MMI32-M_u2 net67 net5 VSS VSS lvtnfet l=LA w=WB m=1
MMI5 net25 D net53 VSS lvtnfet l=LA w=WW m=1
MMI49 net20 CDN VSS VSS lvtnfet l=LA w=WA m=1
MMI48 net17 net81 net20 VSS lvtnfet l=LA w=WA m=1
MMI27-M_u2 net036 net95 VSS VSS lvtnfet l=LA w=WV m=1
MMI21-M_u4 net9 CDN VSS VSS lvtnfet l=LA w=WV m=1
MMI22-M_u2 net5 CP VSS VSS lvtnfet l=LA w=WB m=1
MMI47 net25 net67 net17 VSS lvtnfet l=LA w=WA m=1
MMI14-M_u3 net33 net95 VDD VDD lvtpfet l=LA w=WI m=1
MMI22-M_u3 net5 CP VDD VDD lvtpfet l=LA w=WI m=1
MMI32-M_u3 net67 net5 VDD VDD lvtpfet l=LA w=WI m=1
MMI43 net72 net81 VDD VDD lvtpfet l=LA w=WA m=1
MMI6 net25 D net104 VDD lvtpfet l=LA w=WAH m=1
MMI29-M_u3 QN net33 VDD VDD lvtpfet l=LA w=WAL m=1
MMI27-M_u3 net036 net95 VDD VDD lvtpfet l=LA w=WAL m=1
MMI44 net72 CDN VDD VDD lvtpfet l=LA w=WA m=1
MMI17 net33 net67 net79 VDD lvtpfet l=LA w=WA m=1
MMI13-M_u3 net81 net25 VDD VDD lvtpfet l=LA w=WJ m=1
MMI21-M_u1 net95 net79 VDD VDD lvtpfet l=LA w=WX m=1
MMI16 net81 net5 net79 VDD lvtpfet l=LA w=WK m=1
MMI45 net25 net5 net72 VDD lvtpfet l=LA w=WA m=1
MMI7 net104 net67 VDD VDD lvtpfet l=LA w=WAH m=1
MMI21-M_u2 net95 CDN VDD VDD lvtpfet l=LA w=WX m=1
.ENDS

************************************************************************
* Library Name: TempSensorLayout
* Cell Name:    CK_DividerBy8
* View Name:    schematic
************************************************************************

.SUBCKT CK_DividerBy8 CKIN COMPEN INPHASE OUTPHASE PRESET QPHASE VDD VSS
*.PININFO CKIN:I PRESET:I COMPEN:O INPHASE:O OUTPHASE:O QPHASE:O VDD:B VSS:B
XI14 PRESET VDD VSS net039 INVD2LVT
XI51<18> VDD VSS DCAP8LVT
XI51<17> VDD VSS DCAP8LVT
XI51<16> VDD VSS DCAP8LVT
XI51<15> VDD VSS DCAP8LVT
XI51<14> VDD VSS DCAP8LVT
XI51<13> VDD VSS DCAP8LVT
XI51<12> VDD VSS DCAP8LVT
XI51<11> VDD VSS DCAP8LVT
XI51<10> VDD VSS DCAP8LVT
XI51<9> VDD VSS DCAP8LVT
XI51<8> VDD VSS DCAP8LVT
XI51<7> VDD VSS DCAP8LVT
XI51<6> VDD VSS DCAP8LVT
XI51<5> VDD VSS DCAP8LVT
XI51<4> VDD VSS DCAP8LVT
XI51<3> VDD VSS DCAP8LVT
XI51<2> VDD VSS DCAP8LVT
XI51<1> VDD VSS DCAP8LVT
XI51<0> VDD VSS DCAP8LVT
XI50 PRESET VDD VSS net048 INVD1LVT
XI6 CKIN VDD VSS net45 CKBD1LVT
XI139 net048 net015 VDD VSS COMPEN AN2D1LVT
XI5 net45 VDD VSS net49 CKND1LVT
XI8 net039 net011 net48 net015 net48 VDD VSS DFCND1LVT
XI7 net039 net018 net50 net076 net50 VDD VSS DFCND1LVT
XI43 net076 VDD VSS net059 CKND3LVT
XI39 net48 VDD VSS net063 CKND3LVT
XI37 net015 VDD VSS net064 CKND3LVT
XI42 net059 VDD VSS QPHASE CKND8LVT
XI38 net063 VDD VSS OUTPHASE CKND8LVT
XI20 net064 VDD VSS INPHASE CKND8LVT
XI29 net039 net49 net016 net016 VDD VSS DFCND1LVT_schematic
XI28 net039 net016 net018 net018 VDD VSS DFCND1LVT_schematic
XI27 net039 net45 net040 net040 VDD VSS DFCND1LVT_schematic
XI26 net039 net040 net011 net011 VDD VSS DFCND1LVT_schematic
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    DFNCND1LVT
* View Name:    schematic
************************************************************************

.SUBCKT DFNCND1LVT CDN CPN D Q QN VDD VSS
*.PININFO CDN:I CPN:I D:I Q:O QN:O VDD:B VSS:B
MMI60-M_u2 net49 CDN VDD VDD lvtpfet l=LA w=WY m=1
MMI43 net53 net9 VDD VDD lvtpfet l=LA w=WA m=1
MMI60-M_u1 net49 net20 VDD VDD lvtpfet l=LA w=WY m=1
MMI6 net5 D net1 VDD lvtpfet l=LA w=WAJ m=1
MMI62-M_u3 net11 net67 VDD VDD lvtpfet l=LA w=WI m=1
MMI63-M_u3 net37 net49 VDD VDD lvtpfet l=LA w=WI m=1
MMI29-M_u3 QN net37 VDD VDD lvtpfet l=LA w=WAL m=1
MMI31-M_u3 net67 CPN VDD VDD lvtpfet l=LA w=WI m=1
MMI27-M_u3 Q net49 VDD VDD lvtpfet l=LA w=WAL m=1
MMI44 net53 CDN VDD VDD lvtpfet l=LA w=WA m=1
MMI17 net37 net67 net20 VDD lvtpfet l=LA w=WA m=1
MMI13-M_u3 net9 net5 VDD VDD lvtpfet l=LA w=WZ m=1
MMI16 net9 net11 net20 VDD lvtpfet l=LA w=WL m=1
MMI45 net5 net11 net53 VDD lvtpfet l=LA w=WA m=1
MMI7 net1 net67 VDD VDD lvtpfet l=LA w=WAJ m=1
MMI29-M_u2 QN net37 VSS VSS lvtnfet l=LA w=WV m=1
MMI63-M_u2 net37 net49 VSS VSS lvtnfet l=LA w=WB m=1
MMI4 net109 net11 VSS VSS lvtnfet l=LA w=WD m=1
MMI18 net37 net11 net20 VSS lvtnfet l=LA w=WA m=1
MMI60-M_u3 net49 net20 net104 VSS lvtnfet l=LA w=WV m=1
MMI60-M_u4 net104 CDN VSS VSS lvtnfet l=LA w=WV m=1
MMI13-M_u2 net9 net5 VSS VSS lvtnfet l=LA w=WC m=1
MMI15 net9 net67 net20 VSS lvtnfet l=LA w=WE m=1
MMI5 net5 D net109 VSS lvtnfet l=LA w=WD m=1
MMI31-M_u2 net67 CPN VSS VSS lvtnfet l=LA w=WB m=1
MMI49 net77 CDN VSS VSS lvtnfet l=LA w=WA m=1
MMI48 net64 net9 net77 VSS lvtnfet l=LA w=WA m=1
MMI27-M_u2 Q net49 VSS VSS lvtnfet l=LA w=WV m=1
MMI62-M_u2 net11 net67 VSS VSS lvtnfet l=LA w=WB m=1
MMI47 net5 net67 net64 VSS lvtnfet l=LA w=WA m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    TIEHLVT
* View Name:    schematic
************************************************************************

.SUBCKT TIEHLVT VDD VSS Z
*.PININFO Z:O VDD:B VSS:B
MM_u2 net7 net7 VSS VSS lvtnfet l=LA w=WAK m=1
MM_u1 Z net7 VDD VDD lvtpfet l=LA w=WAM m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    DFCNQD1LVT
* View Name:    schematic
************************************************************************

.SUBCKT DFCNQD1LVT CDN CP D Q VDD VSS
*.PININFO CDN:I CP:I D:I Q:O VDD:B VSS:B
MMI4 net53 net5 VSS VSS lvtnfet l=LA w=WW m=1
MMI21-M_u3 net81 net51 net9 VSS lvtnfet l=LA w=WV m=1
MMI13-M_u2 net37 net97 VSS VSS lvtnfet l=LA w=WD m=1
MMI29 net51 net5 net44 VSS lvtnfet l=LA w=WA m=1
MMI15 net37 net63 net51 VSS lvtnfet l=LA w=WD m=1
MMI32-M_u2 net63 net5 VSS VSS lvtnfet l=LA w=WB m=1
MMI5 net97 D net53 VSS lvtnfet l=LA w=WW m=1
MMI49 net20 CDN VSS VSS lvtnfet l=LA w=WA m=1
MMI26 net44 net81 VSS VSS lvtnfet l=LA w=WA m=1
MMI48 net17 net37 net20 VSS lvtnfet l=LA w=WA m=1
MMI27-M_u2 Q net81 VSS VSS lvtnfet l=LA w=WV m=1
MMI21-M_u4 net9 CDN VSS VSS lvtnfet l=LA w=WV m=1
MMI22-M_u2 net5 CP VSS VSS lvtnfet l=LA w=WB m=1
MMI47 net97 net63 net17 VSS lvtnfet l=LA w=WA m=1
MMI22-M_u3 net5 CP VDD VDD lvtpfet l=LA w=WI m=1
MMI32-M_u3 net63 net5 VDD VDD lvtpfet l=LA w=WI m=1
MMI43 net101 net37 VDD VDD lvtpfet l=LA w=WA m=1
MMI6 net97 D net100 VDD lvtpfet l=LA w=WAH m=1
MMI27-M_u3 Q net81 VDD VDD lvtpfet l=LA w=WAL m=1
MMI44 net101 CDN VDD VDD lvtpfet l=LA w=WA m=1
MMI13-M_u3 net37 net97 VDD VDD lvtpfet l=LA w=WJ m=1
MMI21-M_u1 net81 net51 VDD VDD lvtpfet l=LA w=WAE m=1
MMI16 net37 net5 net51 VDD lvtpfet l=LA w=WK m=1
MMI24 net72 net81 VDD VDD lvtpfet l=LA w=WA m=1
MMI28 net51 net63 net72 VDD lvtpfet l=LA w=WA m=1
MMI45 net97 net5 net101 VDD lvtpfet l=LA w=WA m=1
MMI7 net100 net63 VDD VDD lvtpfet l=LA w=WAH m=1
MMI21-M_u2 net81 CDN VDD VDD lvtpfet l=LA w=WAE m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    CKND4LVT
* View Name:    schematic
************************************************************************

.SUBCKT CKND4LVT I VDD VSS ZN
*.PININFO I:I ZN:O VDD:B VSS:B
MM_u1_0 ZN I VDD VDD lvtpfet l=LA w=WAL m=1
MM_u1_3 ZN I VDD VDD lvtpfet l=LA w=WAL m=1
MM_u1_2 ZN I VDD VDD lvtpfet l=LA w=WAL m=1
MM_u1_1 ZN I VDD VDD lvtpfet l=LA w=WAL m=1
MM_u2_1 ZN I VSS VSS lvtnfet l=LA w=WU m=1
MM_u2_3 ZN I VSS VSS lvtnfet l=LA w=WU m=1
MM_u2_0 ZN I VSS VSS lvtnfet l=LA w=WU m=1
MM_u2_2 ZN I VSS VSS lvtnfet l=LA w=WU m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    NR2D1LVT
* View Name:    schematic
************************************************************************

.SUBCKT NR2D1LVT A1 A2 VDD VSS ZN
*.PININFO A1:I A2:I ZN:O VDD:B VSS:B
MMI1-M_u3 ZN A2 VSS VSS lvtnfet l=LA w=WV m=1
MMI1-M_u4 ZN A1 VSS VSS lvtnfet l=LA w=WV m=1
MMI1-M_u1 net13 A2 VDD VDD lvtpfet l=LA w=WAL m=1
MMI1-M_u2 ZN A1 net13 VDD lvtpfet l=LA w=WAL m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    OR2D1LVT
* View Name:    schematic
************************************************************************

.SUBCKT OR2D1LVT A1 A2 VDD VSS Z
*.PININFO A1:I A2:I Z:O VDD:B VSS:B
MMU1-M_u2 Z net5 VSS VSS lvtnfet l=LA w=WV m=1
MM_u7-M_u4 net5 A1 VSS VSS lvtnfet l=LA w=WB m=1
MM_u7-M_u3 net5 A2 VSS VSS lvtnfet l=LA w=WB m=1
MMU1-M_u3 Z net5 VDD VDD lvtpfet l=LA w=WAL m=1
MM_u7-M_u1 net17 A2 VDD VDD lvtpfet l=LA w=WAL m=1
MM_u7-M_u2 net5 A1 net17 VDD lvtpfet l=LA w=WAL m=1
.ENDS

************************************************************************
* Library Name: TempSensorLayout
* Cell Name:    DFNCND1LVT_schematic
* View Name:    schematic
************************************************************************

.SUBCKT DFNCND1LVT_schematic CDN CPN D Q VDD VSS
*.PININFO CDN:I CPN:I D:I Q:O VDD:B VSS:B
MMI60-M_u2 net49 CDN VDD VDD lvtpfet l=LA w=WY m=1
MMI43 net53 net9 VDD VDD lvtpfet l=LA w=WA m=1
MMI60-M_u1 net49 net20 VDD VDD lvtpfet l=LA w=WY m=1
MMI6 net5 D net1 VDD lvtpfet l=LA w=WAJ m=1
MMI62-M_u3 net11 net67 VDD VDD lvtpfet l=LA w=WI m=1
MMI63-M_u3 net37 net49 VDD VDD lvtpfet l=LA w=WI m=1
MMI29-M_u3 net040 net37 VDD VDD lvtpfet l=LA w=WAL m=1
MMI31-M_u3 net67 CPN VDD VDD lvtpfet l=LA w=WI m=1
MMI27-M_u3 Q net49 VDD VDD lvtpfet l=LA w=WAL m=1
MMI44 net53 CDN VDD VDD lvtpfet l=LA w=WA m=1
MMI17 net37 net67 net20 VDD lvtpfet l=LA w=WA m=1
MMI13-M_u3 net9 net5 VDD VDD lvtpfet l=LA w=WZ m=1
MMI16 net9 net11 net20 VDD lvtpfet l=LA w=WL m=1
MMI45 net5 net11 net53 VDD lvtpfet l=LA w=WA m=1
MMI7 net1 net67 VDD VDD lvtpfet l=LA w=WAJ m=1
MMI29-M_u2 net040 net37 VSS VSS lvtnfet l=LA w=WV m=1
MMI63-M_u2 net37 net49 VSS VSS lvtnfet l=LA w=WB m=1
MMI4 net109 net11 VSS VSS lvtnfet l=LA w=WD m=1
MMI18 net37 net11 net20 VSS lvtnfet l=LA w=WA m=1
MMI60-M_u3 net49 net20 net104 VSS lvtnfet l=LA w=WV m=1
MMI60-M_u4 net104 CDN VSS VSS lvtnfet l=LA w=WV m=1
MMI13-M_u2 net9 net5 VSS VSS lvtnfet l=LA w=WC m=1
MMI15 net9 net67 net20 VSS lvtnfet l=LA w=WE m=1
MMI5 net5 D net109 VSS lvtnfet l=LA w=WD m=1
MMI31-M_u2 net67 CPN VSS VSS lvtnfet l=LA w=WB m=1
MMI49 net77 CDN VSS VSS lvtnfet l=LA w=WA m=1
MMI48 net64 net9 net77 VSS lvtnfet l=LA w=WA m=1
MMI27-M_u2 Q net49 VSS VSS lvtnfet l=LA w=WV m=1
MMI62-M_u2 net11 net67 VSS VSS lvtnfet l=LA w=WB m=1
MMI47 net5 net67 net64 VSS lvtnfet l=LA w=WA m=1
.ENDS

************************************************************************
* Library Name: TempSensorLayout
* Cell Name:    DFSND1LVT
* View Name:    schematic
************************************************************************

.SUBCKT DFSND1LVT CP D QN SDN VDD VSS
*.PININFO CP:I D:I SDN:I QN:O VDD:B VSS:B
MMI32-M_u4 net57 net61 VSS VSS lvtnfet l=LA w=WV m=1
MMI55-M_u2 net11 CP VSS VSS lvtnfet l=LA w=WB m=1
MMI60-M_u2 net032 net79 VSS VSS lvtnfet l=LA w=WV m=1
MMI32-M_u3 net97 SDN net57 VSS lvtnfet l=LA w=WV m=1
MMI31-M_u4 net40 net79 VSS VSS lvtnfet l=LA w=WB m=1
MMI31-M_u3 net25 SDN net40 VSS lvtnfet l=LA w=WB m=1
MMI20 net97 net81 net67 VSS lvtnfet l=LA w=WM m=1
MMI23 net61 net81 net5 VSS lvtnfet l=LA w=WA m=1
MMI22 net25 net11 net67 VSS lvtnfet l=LA w=WA m=1
MMI21 net61 D net9 VSS lvtnfet l=LA w=WV m=1
MMI25-M_u2 net79 net67 VSS VSS lvtnfet l=LA w=WV m=1
MMI57-M_u2 QN net25 VSS VSS lvtnfet l=LA w=WV m=1
MMI19 net9 net11 VSS VSS lvtnfet l=LA w=WU m=1
MMI24 net5 net97 VSS VSS lvtnfet l=LA w=WA m=1
MMI40-M_u2 net81 net11 VSS VSS lvtnfet l=LA w=WB m=1
MMI55-M_u3 net11 CP VDD VDD lvtpfet l=LA w=WI m=1
MMI33 net25 net81 net67 VDD lvtpfet l=LA w=WA m=1
MMI32-M_u1 net97 SDN VDD VDD lvtpfet l=LA w=WAL m=1
MMI60-M_u3 net032 net79 VDD VDD lvtpfet l=LA w=WAL m=1
MMI34 net61 net11 net104 VDD lvtpfet l=LA w=WA m=1
MMI30 net97 net11 net67 VDD lvtpfet l=LA w=WAA m=1
MMI57-M_u3 QN net25 VDD VDD lvtpfet l=LA w=WAL m=1
MMI32-M_u2 net97 net61 VDD VDD lvtpfet l=LA w=WAL m=1
MMI28 net85 net81 VDD VDD lvtpfet l=LA w=WAL m=1
MMI40-M_u3 net81 net11 VDD VDD lvtpfet l=LA w=WI m=1
MMI31-M_u2 net25 net79 VDD VDD lvtpfet l=LA w=WI m=1
MMI35 net104 net97 VDD VDD lvtpfet l=LA w=WA m=1
MMI31-M_u1 net25 SDN VDD VDD lvtpfet l=LA w=WI m=1
MMI25-M_u3 net79 net67 VDD VDD lvtpfet l=LA w=WAL m=1
MMI26 net61 D net85 VDD lvtpfet l=LA w=WAL m=1
.ENDS

************************************************************************
* Library Name: TempSensorLayout
* Cell Name:    SARLogic
* View Name:    schematic
************************************************************************

.SUBCKT SARLogic COMPEN D<8> D<7> D<6> D<5> D<4> D<3> D<2> D<1> D<0> DONE
+ PRESET VCTL0<8> VCTL0<7> VCTL0<6> VCTL0<5> VCTL0<4> VCTL0<3> VCTL0<2>
+ VCTL0<1> VCTL0<0> VCTLIN<8> VCTLIN<7> VCTLIN<6> VCTLIN<5> VCTLIN<4>
+ VCTLIN<3> VCTLIN<2> VCTLIN<1> VCTLIN<0> VDD VONLATCH VOPLATCH VSS
*.PININFO COMPEN:I PRESET:I VONLATCH:I VOPLATCH:I D<8>:O D<7>:O D<6>:O D<5>:O
*.PININFO D<4>:O D<3>:O D<2>:O D<1>:O D<0>:O DONE:O VCTL0<8>:O VCTL0<7>:O
*.PININFO VCTL0<6>:O VCTL0<5>:O VCTL0<4>:O VCTL0<3>:O VCTL0<2>:O VCTL0<1>:O
*.PININFO VCTL0<0>:O VCTLIN<8>:O VCTLIN<7>:O VCTLIN<6>:O VCTLIN<5>:O
*.PININFO VCTLIN<4>:O VCTLIN<3>:O VCTLIN<2>:O VCTLIN<1>:O VCTLIN<0>:O VDD:B
*.PININFO VSS:B
XI3<27> VDD VSS DCAP8LVT
XI3<26> VDD VSS DCAP8LVT
XI3<25> VDD VSS DCAP8LVT
XI3<24> VDD VSS DCAP8LVT
XI3<23> VDD VSS DCAP8LVT
XI3<22> VDD VSS DCAP8LVT
XI3<21> VDD VSS DCAP8LVT
XI3<20> VDD VSS DCAP8LVT
XI3<19> VDD VSS DCAP8LVT
XI3<18> VDD VSS DCAP8LVT
XI3<17> VDD VSS DCAP8LVT
XI3<16> VDD VSS DCAP8LVT
XI3<15> VDD VSS DCAP8LVT
XI3<14> VDD VSS DCAP8LVT
XI3<13> VDD VSS DCAP8LVT
XI3<12> VDD VSS DCAP8LVT
XI3<11> VDD VSS DCAP8LVT
XI3<10> VDD VSS DCAP8LVT
XI3<9> VDD VSS DCAP8LVT
XI3<8> VDD VSS DCAP8LVT
XI3<7> VDD VSS DCAP8LVT
XI3<6> VDD VSS DCAP8LVT
XI3<5> VDD VSS DCAP8LVT
XI3<4> VDD VSS DCAP8LVT
XI3<3> VDD VSS DCAP8LVT
XI3<2> VDD VSS DCAP8LVT
XI3<1> VDD VSS DCAP8LVT
XI3<0> VDD VSS DCAP8LVT
XI59 n1 COMPEN CK<1> CK<0> CKB<0> VDD VSS DFNCND1LVT
XI58 n1 COMPEN CK<2> CK<1> CKB<1> VDD VSS DFNCND1LVT
XI57 n1 COMPEN CK<3> CK<2> CKB<2> VDD VSS DFNCND1LVT
XI55 n1 COMPEN CK<4> CK<3> CKB<3> VDD VSS DFNCND1LVT
XI56 n1 COMPEN CK<5> CK<4> CKB<4> VDD VSS DFNCND1LVT
XI54 n1 COMPEN CK<6> CK<5> CKB<5> VDD VSS DFNCND1LVT
XI51 n1 COMPEN CK<7> CK<6> CKB<6> VDD VSS DFNCND1LVT
XI65 n1 COMPEN CK<8> CK<7> CKB<7> VDD VSS DFNCND1LVT
XI67 n1 COMPEN net163 CK<8> CKB<8> VDD VSS DFNCND1LVT
XI0 VDD VSS net034 TIEHLVT
XI42 n1 COMPEN CK<0> DONE VDD VSS DFCNQD1LVT
XI60 n1 CK<5> VOPLATCH D<5> VDD VSS DFCNQD1LVT
XI53 n1 CK<6> VOPLATCH D<6> VDD VSS DFCNQD1LVT
XI52 n1 CK<7> VOPLATCH D<7> VDD VSS DFCNQD1LVT
XI66 n1 CK<8> VOPLATCH D<8> VDD VSS DFCNQD1LVT
XI69 PRESET VDD VSS n1 CKND4LVT
XI73<7> D<7> net164<0> VDD VSS VCTL0<7> NR2D1LVT
XI73<6> D<6> net164<1> VDD VSS VCTL0<6> NR2D1LVT
XI73<5> D<5> net164<2> VDD VSS VCTL0<5> NR2D1LVT
XI73<4> D<4> net164<3> VDD VSS VCTL0<4> NR2D1LVT
XI73<3> D<3> net164<4> VDD VSS VCTL0<3> NR2D1LVT
XI73<2> D<2> net164<5> VDD VSS VCTL0<2> NR2D1LVT
XI73<1> D<1> net164<6> VDD VSS VCTL0<1> NR2D1LVT
XI73<0> D<0> net164<7> VDD VSS VCTL0<0> NR2D1LVT
XI84 D<8> CKB<8> VDD VSS net162 NR2D1LVT
XI72<7> CK<8> CKB<7> VDD VSS net164<0> AN2D1LVT
XI72<6> CK<7> CKB<6> VDD VSS net164<1> AN2D1LVT
XI72<5> CK<6> CKB<5> VDD VSS net164<2> AN2D1LVT
XI72<4> CK<5> CKB<4> VDD VSS net164<3> AN2D1LVT
XI72<3> CK<4> CKB<3> VDD VSS net164<4> AN2D1LVT
XI72<2> CK<3> CKB<2> VDD VSS net164<5> AN2D1LVT
XI72<1> CK<2> CKB<1> VDD VSS net164<6> AN2D1LVT
XI72<0> CK<1> CKB<0> VDD VSS net164<7> AN2D1LVT
XI106 PRESET net162 VDD VSS VCTL0<8> OR2D1LVT
XI71<7> VCTL0<7> VDD VSS VCTLIN<7> CKND1LVT
XI71<6> VCTL0<6> VDD VSS VCTLIN<6> CKND1LVT
XI71<5> VCTL0<5> VDD VSS VCTLIN<5> CKND1LVT
XI71<4> VCTL0<4> VDD VSS VCTLIN<4> CKND1LVT
XI71<3> VCTL0<3> VDD VSS VCTLIN<3> CKND1LVT
XI71<2> VCTL0<2> VDD VSS VCTLIN<2> CKND1LVT
XI71<1> VCTL0<1> VDD VSS VCTLIN<1> CKND1LVT
XI71<0> VCTL0<0> VDD VSS VCTLIN<0> CKND1LVT
XI86 VCTL0<8> VDD VSS VCTLIN<8> CKND1LVT
XI50 n1 COMPEN net034 net163 VDD VSS DFNCND1LVT_schematic
XI81 CK<0> VONLATCH D<0> n1 VDD VSS DFSND1LVT
XI80 CK<1> VONLATCH D<1> n1 VDD VSS DFSND1LVT
XI79 CK<2> VONLATCH D<2> n1 VDD VSS DFSND1LVT
XI62 CK<3> VONLATCH D<3> n1 VDD VSS DFSND1LVT
XI61 CK<4> VONLATCH D<4> n1 VDD VSS DFSND1LVT
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    DCAP16LVT
* View Name:    schematic
************************************************************************

.SUBCKT DCAP16LVT VDD VSS
*.PININFO VDD:B VSS:B
MMI4 VSS net11 VSS VSS lvtnfet l=LE w=WT m=1
MMI8 VSS net11 VSS VSS lvtnfet l=LE w=WT m=1
MM_u2 net5 net11 VSS VSS lvtnfet l=LA w=WT m=1
MMI7 VSS net11 VSS VSS lvtnfet l=LE w=WT m=1
MMI3 VDD net5 VDD VDD lvtpfet l=LE w=WAI m=1
MMI6 VDD net5 VDD VDD lvtpfet l=LE w=WAI m=1
MM_u1 net11 net5 VDD VDD lvtpfet l=LA w=WV m=1
MMI5 VDD net5 VDD VDD lvtpfet l=LE w=WAI m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    DCAP32LVT
* View Name:    schematic
************************************************************************

.SUBCKT DCAP32LVT VDD VSS
*.PININFO VDD:B VSS:B
MMI38 VSS net11 VSS VSS lvtnfet l=LH w=WT m=1
MMI6 VSS net11 VSS VSS lvtnfet l=LH w=WT m=1
MMI39 VSS net11 VSS VSS lvtnfet l=LH w=WT m=1
MMI37 VSS net11 VSS VSS lvtnfet l=LH w=WT m=1
MM_u2 net5 net11 VSS VSS lvtnfet l=LA w=WT m=1
MMI36 VSS net11 VSS VSS lvtnfet l=LH w=WT m=1
MMI33 VDD net5 VDD VDD lvtpfet l=LH w=WAI m=1
MM_u1 net11 net5 VDD VDD lvtpfet l=LA w=WV m=1
MMI34 VDD net5 VDD VDD lvtpfet l=LH w=WAI m=1
MMI35 VDD net5 VDD VDD lvtpfet l=LH w=WAI m=1
MMI32 VDD net5 VDD VDD lvtpfet l=LH w=WAI m=1
MMI26 VDD net5 VDD VDD lvtpfet l=LH w=WAI m=1
.ENDS

************************************************************************
* Library Name: TempSensorLayout
* Cell Name:    BUFTD16LVT
* View Name:    schematic
************************************************************************

.SUBCKT BUFTD16LVT I OE VDD VSS Z
*.PININFO I:I OE:I Z:O VDD:B VSS:B
MMI6-M_u4 net37 I VSS VSS lvtnfet l=LA w=WV m=1
MMI5_1-M_u4 net25 net5 VSS VSS lvtnfet l=LA w=WV m=1
MMI5_0-M_u3 net25 I VSS VSS lvtnfet l=LA w=WV m=1
MMI5_0-M_u4 net25 net5 VSS VSS lvtnfet l=LA w=WV m=1
MMI7-M_u3 net13 OE net9 VSS lvtnfet l=LA w=WN m=1
MM_u7 Z net25 VSS VSS lvtnfet l=LA w=WAB m=1
MMI6-M_u3 net13 OE net37 VSS lvtnfet l=LA w=WN m=1
MMI7-M_u4 net9 I VSS VSS lvtnfet l=LA w=WV m=1
MM_u17-M_u2 net5 OE VSS VSS lvtnfet l=LA w=WV m=1
MMI5_1-M_u3 net25 I VSS VSS lvtnfet l=LA w=WV m=1
MM_u17-M_u3 net5 OE VDD VDD lvtpfet l=LA w=WAL m=1
MMI5_0-M_u1 net72 I VDD VDD lvtpfet l=LA w=WAC m=1
MMI5_0-M_u2 net25 net5 net72 VDD lvtpfet l=LA w=WAC m=1
MMI6-M_u2 net13 I VDD VDD lvtpfet l=LA w=WAL m=1
MMI7-M_u1 net13 OE VDD VDD lvtpfet l=LA w=WAL m=1
MM_u6 Z net13 VDD VDD lvtpfet l=LA w=WAS m=1
MMI5_1-M_u1 net53 I VDD VDD lvtpfet l=LA w=WAC m=1
MMI7-M_u2 net13 I VDD VDD lvtpfet l=LA w=WAL m=1
MMI5_1-M_u2 net25 net5 net53 VDD lvtpfet l=LA w=WAC m=1
MMI6-M_u1 net13 OE VDD VDD lvtpfet l=LA w=WAL m=1
.ENDS

************************************************************************
* Library Name: TempSensorLayout
* Cell Name:    ResTune_CFG
* View Name:    schematic
************************************************************************

.SUBCKT ResTune_CFG INPH INPHASE<7> INPHASE<6> INPHASE<5> INPHASE<4>
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
XI3<1> VDD VSS DCAP8LVT
XI3<0> VDD VSS DCAP8LVT
XI2<7> VDD VSS DCAP16LVT
XI2<6> VDD VSS DCAP16LVT
XI2<5> VDD VSS DCAP16LVT
XI2<4> VDD VSS DCAP16LVT
XI2<3> VDD VSS DCAP16LVT
XI2<2> VDD VSS DCAP16LVT
XI2<1> VDD VSS DCAP16LVT
XI2<0> VDD VSS DCAP16LVT
XI4<3> VDD VSS DCAP32LVT
XI4<2> VDD VSS DCAP32LVT
XI4<1> VDD VSS DCAP32LVT
XI4<0> VDD VSS DCAP32LVT
XI1<7> INPH RESEN<7> VDD VSS INPHASE<7> BUFTD16LVT
XI1<6> INPH RESEN<6> VDD VSS INPHASE<6> BUFTD16LVT
XI1<5> INPH RESEN<5> VDD VSS INPHASE<5> BUFTD16LVT
XI1<4> INPH RESEN<4> VDD VSS INPHASE<4> BUFTD16LVT
XI1<3> INPH RESEN<3> VDD VSS INPHASE<3> BUFTD16LVT
XI1<2> INPH RESEN<2> VDD VSS INPHASE<2> BUFTD16LVT
XI1<1> INPH RESEN<1> VDD VSS INPHASE<1> BUFTD16LVT
XI1<0> INPH RESEN<0> VDD VSS INPHASE<0> BUFTD16LVT
XI0<7> OUTPH RESEN<7> VDD VSS OUTPHASE<7> BUFTD16LVT
XI0<6> OUTPH RESEN<6> VDD VSS OUTPHASE<6> BUFTD16LVT
XI0<5> OUTPH RESEN<5> VDD VSS OUTPHASE<5> BUFTD16LVT
XI0<4> OUTPH RESEN<4> VDD VSS OUTPHASE<4> BUFTD16LVT
XI0<3> OUTPH RESEN<3> VDD VSS OUTPHASE<3> BUFTD16LVT
XI0<2> OUTPH RESEN<2> VDD VSS OUTPHASE<2> BUFTD16LVT
XI0<1> OUTPH RESEN<1> VDD VSS OUTPHASE<1> BUFTD16LVT
XI0<0> OUTPH RESEN<0> VDD VSS OUTPHASE<0> BUFTD16LVT
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    MUX2D2LVT
* View Name:    schematic
************************************************************************

.SUBCKT MUX2D2LVT I0 I1 S VDD VSS Z
*.PININFO I0:I I1:I S:I Z:O VDD:B VSS:B
MMU18-M_u3 net25 net17 net7 VSS lvtnfet l=LA w=WO m=1
MMI16-M_u2 net25 I0 VSS VSS lvtnfet l=LA w=WO m=1
MMI17-M_u2 net17 S VSS VSS lvtnfet l=LA w=WB m=1
MMI13-M_u3 net9 S net7 VSS lvtnfet l=LA w=WP m=1
MMI14-M_u2 net9 I1 VSS VSS lvtnfet l=LA w=WV m=1
MMU29_0-M_u2 Z net7 VSS VSS lvtnfet l=LA w=WV m=1
MMU29_1-M_u2 Z net7 VSS VSS lvtnfet l=LA w=WV m=1
MMI17-M_u3 net17 S VDD VDD lvtpfet l=LA w=WI m=1
MMI14-M_u3 net9 I1 VDD VDD lvtpfet l=LA w=WAL m=1
MMU29_1-M_u3 Z net7 VDD VDD lvtpfet l=LA w=WAL m=1
MMI16-M_u3 net25 I0 VDD VDD lvtpfet l=LA w=WAC m=1
MMU29_0-M_u3 Z net7 VDD VDD lvtpfet l=LA w=WAL m=1
MMI13-M_u2 net9 net17 net7 VDD lvtpfet l=LA w=WW m=1
MMU18-M_u2 net25 S net7 VDD lvtpfet l=LA w=WAK m=1
.ENDS

************************************************************************
* Library Name: TempSensorLayout
* Cell Name:    CrossingDetector_Mux
* View Name:    schematic
************************************************************************

.SUBCKT CrossingDetector_Mux IN SS VDD VO VSS
*.PININFO IN:I SS:I VO:O VDD:B VSS:B
XI18 net012 net032 SS VDD VSS VO MUX2D2LVT
XI16 net033 VDD VSS net012 CKBD1LVT
XI10 net012 VDD VSS net032 CKBD1LVT
XI9 net015 VDD VSS net033 CKBD1LVT
MM2 net06 IN VDD VDD lvtpfet l=LA w=WAN m=2
MM1 net06 IN VSS VSS lvtnfet l=LA w=WU m=2
XI15 net06 VDD VSS net015 CKND1LVT
.ENDS

************************************************************************
* Library Name: TempSensorLayout
* Cell Name:    CrossingDetector
* View Name:    schematic
************************************************************************

.SUBCKT CrossingDetector QD QPHASE SQ SS VCP VCPS VDD VSS
*.PININFO QPHASE:I SQ:I SS:I VCP:I QD:O VCPS:O VDD:B VSS:B
XI2 QPHASE SQ VDD QD VSS CrossingDetector_Mux
XI0 VCP SS VDD VCPS VSS CrossingDetector_Mux
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    NR2D2LVT
* View Name:    schematic
************************************************************************

.SUBCKT NR2D2LVT A1 A2 VDD VSS ZN
*.PININFO A1:I A2:I ZN:O VDD:B VSS:B
MMI1_1-M_u3 ZN A2 VSS VSS lvtnfet l=LA w=WV m=1
MMI1_1-M_u4 ZN A1 VSS VSS lvtnfet l=LA w=WV m=1
MMI1_0-M_u4 ZN A1 VSS VSS lvtnfet l=LA w=WV m=1
MMI1_0-M_u3 ZN A2 VSS VSS lvtnfet l=LA w=WV m=1
MMI1_1-M_u2 ZN A1 net17 VDD lvtpfet l=LA w=WAO m=1
MMI1_0-M_u1 net25 A2 VDD VDD lvtpfet l=LA w=WAO m=1
MMI1_0-M_u2 ZN A1 net25 VDD lvtpfet l=LA w=WAO m=1
MMI1_1-M_u1 net17 A2 VDD VDD lvtpfet l=LA w=WAO m=1
.ENDS

************************************************************************
* Library Name: TempSensorLayout
* Cell Name:    EdgeComparator
* View Name:    schematic
************************************************************************

.SUBCKT EdgeComparator COMPEN PRESET VDD VIN VIP VONL VOPL VSS
*.PININFO COMPEN:I PRESET:I VIN:I VIP:I VONL:O VOPL:O VDD:B VSS:B
MM7 net028 net029 VDD VDD lvtpfet l=LF w=WT m=1
MM6 net25 net033 VDD VDD lvtpfet l=LF w=WT m=1
MM2 net25 VIN VDD VDD lvtpfet l=LF w=WT m=1
MM0 net028 VIP VDD VDD lvtpfet l=LF w=WT m=1
MM45 net25 net028 VDD VDD lvtpfet l=LF w=WT m=4
MM3 net028 net25 VDD VDD lvtpfet l=LF w=WT m=4
XI95 VOP VOPL VDD VSS VONL NR2D2LVT
XI96 VON VONL VDD VSS VOPL NR2D2LVT
MM5 net032 net028 net015 VSS lvtnfet l=LB w=WAP m=2
MM4 net24 net25 net015 VSS lvtnfet l=LB w=WAP m=2
MM28 net25 VIN net032 VSS lvtnfet l=LB w=WAR m=2
MM1 net028 VIP net24 VSS lvtnfet l=LB w=WAR m=2
MM22 net015 COMPEN VSS VSS lvtnfet l=LB w=WAP m=2
XI5 PRESET VDD VSS net029 INVD1LVT
XI4 PRESET VDD VSS net033 INVD1LVT
XI3 net028 VDD VSS VOP INVD1LVT
XI1 net25 VDD VSS VON INVD1LVT
.ENDS

************************************************************************
* Library Name: TempSensorLayout
* Cell Name:    SwitchCap_256X
* View Name:    schematic
************************************************************************

.SUBCKT SwitchCap_256X VDD VSS Vctl0 Vctlin Von Vop
*.PININFO Vctl0:I Vctlin:I VDD:B VSS:B Von:B Vop:B
MM5 Von Vctlin net3 VSS lvtnfet l=LA w=WAD m=1
MM0 net4 Vctl0 VSS VSS lvtnfet l=LA w=WAD m=1
MM4 net3 Vctl0 VSS VSS lvtnfet l=LA w=WAD m=1
MM3 Vop Vctlin net4 VSS lvtnfet l=LA w=WAD m=1
MM2 net4 Vctl0 Vop VDD lvtpfet l=LA w=WAL m=1
MM1 net3 Vctl0 Von VDD lvtpfet l=LA w=WAL m=1
.ENDS

************************************************************************
* Library Name: TempSensorLayout
* Cell Name:    SwitchCap_128X
* View Name:    schematic
************************************************************************

.SUBCKT SwitchCap_128X VDD VSS Vctl0 Vctlin Von Vop
*.PININFO Vctl0:I Vctlin:I VDD:B VSS:B Von:B Vop:B
MM5 Von Vctlin net3 VSS lvtnfet l=LA w=WAE m=1
MM0 net4 Vctl0 VSS VSS lvtnfet l=LA w=WAE m=1
MM4 net3 Vctl0 VSS VSS lvtnfet l=LA w=WAE m=1
MM3 Vop Vctlin net4 VSS lvtnfet l=LA w=WAE m=1
MM2 net4 Vctl0 Vop VDD lvtpfet l=LA w=WAM m=1
MM1 net3 Vctl0 Von VDD lvtpfet l=LA w=WAM m=1
.ENDS

************************************************************************
* Library Name: TempSensorLayout
* Cell Name:    SwitchCap_64X
* View Name:    schematic
************************************************************************

.SUBCKT SwitchCap_64X VDD VSS Vctl0 Vctlin Von Vop
*.PININFO Vctl0:I Vctlin:I VDD:B VSS:B Von:B Vop:B
MM5 Von Vctlin net3 VSS lvtnfet l=LA w=WAF m=1
MM0 net4 Vctl0 VSS VSS lvtnfet l=LA w=WAF m=1
MM4 net3 Vctl0 VSS VSS lvtnfet l=LA w=WAF m=1
MM3 Vop Vctlin net4 VSS lvtnfet l=LA w=WAF m=1
MM2 net4 Vctl0 Vop VDD lvtpfet l=LA w=WAQ m=1
MM1 net3 Vctl0 Von VDD lvtpfet l=LA w=WAQ m=1
.ENDS

************************************************************************
* Library Name: TempSensorLayout
* Cell Name:    SwitchCap_32X
* View Name:    schematic
************************************************************************

.SUBCKT SwitchCap_32X VDD VSS Vctl0 Vctlin Von Vop
*.PININFO Vctl0:I Vctlin:I VDD:B VSS:B Von:B Vop:B
MM5 Von Vctlin net3 VSS lvtnfet l=LA w=WAG m=1
MM0 net4 Vctl0 VSS VSS lvtnfet l=LA w=WAG m=1
MM4 net3 Vctl0 VSS VSS lvtnfet l=LA w=WAG m=1
MM3 Vop Vctlin net4 VSS lvtnfet l=LA w=WAG m=1
MM2 net4 Vctl0 Vop VDD lvtpfet l=LA w=WAN m=1
MM1 net3 Vctl0 Von VDD lvtpfet l=LA w=WAN m=1
.ENDS

************************************************************************
* Library Name: TempSensorLayout
* Cell Name:    SwitchCap_16X
* View Name:    schematic
************************************************************************

.SUBCKT SwitchCap_16X VDD VSS Vctl0 Vctlin Von Vop
*.PININFO Vctl0:I Vctlin:I VDD:B VSS:B Von:B Vop:B
MM5 Von Vctlin net3 VSS lvtnfet l=LA w=WAH m=1
MM0 net4 Vctl0 VSS VSS lvtnfet l=LA w=WAH m=1
MM4 net3 Vctl0 VSS VSS lvtnfet l=LA w=WAH m=1
MM3 Vop Vctlin net4 VSS lvtnfet l=LA w=WAH m=1
MM2 net4 Vctl0 Vop VDD lvtpfet l=LA w=WAR m=1
MM1 net3 Vctl0 Von VDD lvtpfet l=LA w=WAR m=1
.ENDS

************************************************************************
* Library Name: TempSensorLayout
* Cell Name:    SwitchCap_8X
* View Name:    schematic
************************************************************************

.SUBCKT SwitchCap_8X VDD VSS Vctl0 Vctlin Von Vop
*.PININFO Vctl0:I Vctlin:I VDD:B VSS:B Von:B Vop:B
MM5 Von Vctlin net3 VSS lvtnfet l=LA w=WP m=1
MM0 net4 Vctl0 VSS VSS lvtnfet l=LA w=WP m=1
MM4 net3 Vctl0 VSS VSS lvtnfet l=LA w=WP m=1
MM3 Vop Vctlin net4 VSS lvtnfet l=LA w=WP m=1
MM2 net4 Vctl0 Vop VDD lvtpfet l=LA w=WT m=1
MM1 net3 Vctl0 Von VDD lvtpfet l=LA w=WT m=1
.ENDS

************************************************************************
* Library Name: TempSensorLayout
* Cell Name:    SwitchCap_4X
* View Name:    schematic
************************************************************************

.SUBCKT SwitchCap_4X VDD VSS Vctl0 Vctlin Von Vop
*.PININFO Vctl0:I Vctlin:I VDD:B VSS:B Von:B Vop:B
MM5 Von Vctlin net3 VSS lvtnfet l=LA w=WQ m=1
MM0 net4 Vctl0 VSS VSS lvtnfet l=LA w=WQ m=1
MM4 net3 Vctl0 VSS VSS lvtnfet l=LA w=WQ m=1
MM3 Vop Vctlin net4 VSS lvtnfet l=LA w=WQ m=1
MM2 net4 Vctl0 Vop VDD lvtpfet l=LA w=WI m=1
MM1 net3 Vctl0 Von VDD lvtpfet l=LA w=WI m=1
.ENDS

************************************************************************
* Library Name: TempSensorLayout
* Cell Name:    SwitchCap_2X
* View Name:    schematic
************************************************************************

.SUBCKT SwitchCap_2X VDD VSS Vctl0 Vctlin Von Vop
*.PININFO Vctl0:I Vctlin:I VDD:B VSS:B Von:B Vop:B
MM5 Von Vctlin net3 VSS lvtnfet l=LA w=WQ m=1
MM0 net4 Vctl0 VSS VSS lvtnfet l=LA w=WQ m=1
MM4 net3 Vctl0 VSS VSS lvtnfet l=LA w=WQ m=1
MM3 Vop Vctlin net4 VSS lvtnfet l=LA w=WQ m=1
MM2 net4 Vctl0 Vop VDD lvtpfet l=LA w=WI m=1
MM1 net3 Vctl0 Von VDD lvtpfet l=LA w=WI m=1
.ENDS

************************************************************************
* Library Name: TempSensorLayout
* Cell Name:    SwitchCap_1X
* View Name:    schematic
************************************************************************

.SUBCKT SwitchCap_1X VDD VSS Vctl0 Vctlin Von Vop
*.PININFO Vctl0:I Vctlin:I VDD:B VSS:B Von:B Vop:B
MM5 Von Vctlin net3 VSS lvtnfet l=LA w=WQ m=1
MM0 net4 Vctl0 VSS VSS lvtnfet l=LA w=WQ m=1
MM4 net3 Vctl0 VSS VSS lvtnfet l=LA w=WQ m=1
MM3 Vop Vctlin net4 VSS lvtnfet l=LA w=WQ m=1
MM2 net4 Vctl0 Vop VDD lvtpfet l=LA w=WI m=1
MM1 net3 Vctl0 Von VDD lvtpfet l=LA w=WI m=1
.ENDS

************************************************************************
* Library Name: TempSensorLayout_PostLayout
* Cell Name:    SwitchCapArray_V2
* View Name:    schematic
************************************************************************

.SUBCKT SwitchCapArray_V2 VCN VCP VCTL0<8> VCTL0<7> VCTL0<6> VCTL0<5> VCTL0<4>
+ VCTL0<3> VCTL0<2> VCTL0<1> VCTL0<0> VCTLIN<8> VCTLIN<7> VCTLIN<6> VCTLIN<5>
+ VCTLIN<4> VCTLIN<3> VCTLIN<2> VCTLIN<1> VCTLIN<0> VDD VSS
*.PININFO VCTL0<8>:I VCTL0<7>:I VCTL0<6>:I VCTL0<5>:I VCTL0<4>:I VCTL0<3>:I
*.PININFO VCTL0<2>:I VCTL0<1>:I VCTL0<0>:I VCTLIN<8>:I VCTLIN<7>:I VCTLIN<6>:I
*.PININFO VCTLIN<5>:I VCTLIN<4>:I VCTLIN<3>:I VCTLIN<2>:I VCTLIN<1>:I
*.PININFO VCTLIN<0>:I VCN:B VCP:B VDD:B VSS:B
XI14<0> VDD VSS VCTL0<8> VCTLIN<8> VCN VCP SwitchCap_256X
XI14<1> VDD VSS VCTL0<8> VCTLIN<8> VCN VCP SwitchCap_256X
XI14<2> VDD VSS VCTL0<8> VCTLIN<8> VCN VCP SwitchCap_256X
XI14<3> VDD VSS VCTL0<8> VCTLIN<8> VCN VCP SwitchCap_256X
XI9<0> VDD VSS VCTL0<8> VCTLIN<8> VCN VCP SwitchCap_256X
XI9<1> VDD VSS VCTL0<8> VCTLIN<8> VCN VCP SwitchCap_256X
XI9<2> VDD VSS VCTL0<8> VCTLIN<8> VCN VCP SwitchCap_256X
XI9<3> VDD VSS VCTL0<8> VCTLIN<8> VCN VCP SwitchCap_256X
XI6<0> VDD VSS VCTL0<8> VCTLIN<8> VCN VCP SwitchCap_256X
XI6<1> VDD VSS VCTL0<8> VCTLIN<8> VCN VCP SwitchCap_256X
XI6<2> VDD VSS VCTL0<8> VCTLIN<8> VCN VCP SwitchCap_256X
XI6<3> VDD VSS VCTL0<8> VCTLIN<8> VCN VCP SwitchCap_256X
XI0<0> VDD VSS VCTL0<8> VCTLIN<8> VCN VCP SwitchCap_256X
XI0<1> VDD VSS VCTL0<8> VCTLIN<8> VCN VCP SwitchCap_256X
XI0<2> VDD VSS VCTL0<8> VCTLIN<8> VCN VCP SwitchCap_256X
XI0<3> VDD VSS VCTL0<8> VCTLIN<8> VCN VCP SwitchCap_256X
XI13<0> VDD VSS VCTL0<7> VCTLIN<7> VCN VCP SwitchCap_128X
XI13<1> VDD VSS VCTL0<7> VCTLIN<7> VCN VCP SwitchCap_128X
XI10<0> VDD VSS VCTL0<7> VCTLIN<7> VCN VCP SwitchCap_128X
XI10<1> VDD VSS VCTL0<7> VCTLIN<7> VCN VCP SwitchCap_128X
XI5<0> VDD VSS VCTL0<7> VCTLIN<7> VCN VCP SwitchCap_128X
XI5<1> VDD VSS VCTL0<7> VCTLIN<7> VCN VCP SwitchCap_128X
XI1<0> VDD VSS VCTL0<7> VCTLIN<7> VCN VCP SwitchCap_128X
XI1<1> VDD VSS VCTL0<7> VCTLIN<7> VCN VCP SwitchCap_128X
XI12 VDD VSS VCTL0<6> VCTLIN<6> VCN VCP SwitchCap_64X
XI8 VDD VSS VCTL0<6> VCTLIN<6> VCN VCP SwitchCap_64X
XI4 VDD VSS VCTL0<6> VCTLIN<6> VCN VCP SwitchCap_64X
XI2 VDD VSS VCTL0<6> VCTLIN<6> VCN VCP SwitchCap_64X
XI11 VDD VSS VCTL0<5> VCTLIN<5> VCN VCP SwitchCap_32X
XI3 VDD VSS VCTL0<5> VCTLIN<5> VCN VCP SwitchCap_32X
XI7 VDD VSS VCTL0<4> VCTLIN<4> VCN VCP SwitchCap_16X
XI15 VDD VSS VCTL0<3> VCTLIN<3> VCN VCP SwitchCap_8X
XI16 VDD VSS VCTL0<2> VCTLIN<2> VCN VCP SwitchCap_4X
XI17 VDD VSS VCTL0<1> VCTLIN<1> VCN VCP SwitchCap_2X
XI18 VDD VSS VCTL0<0> VCTLIN<0> VCN VCP SwitchCap_1X
.ENDS

************************************************************************
* Library Name: TempSensorLayout
* Cell Name:    TunableRes_nonUniform_Layout_Final
* View Name:    schematic
************************************************************************

.SUBCKT TunableRes_nonUniform_Layout_Final R2CAP RTUNE<7> RTUNE<6> RTUNE<5>
+ RTUNE<4> RTUNE<3> RTUNE<2> RTUNE<1> RTUNE<0> VSS
*.PININFO R2CAP:I RTUNE<7>:I RTUNE<6>:I RTUNE<5>:I RTUNE<4>:I RTUNE<3>:I
*.PININFO RTUNE<2>:I RTUNE<1>:I RTUNE<0>:I VSS:B
R7 RTUNE<7> RTUNE<6> rppolys l=LL w=WG m=1
R6 RTUNE<6> RTUNE<5> rppolys l=LK w=WG m=1
R5 RTUNE<5> RTUNE<4> rppolys l=LJ w=WF m=1
R4 RTUNE<4> RTUNE<3> rppolys l=LI w=WF m=1
R3 RTUNE<3> RTUNE<2> rppolys l=LJ w=WF m=1
R2 RTUNE<2> RTUNE<1> rppolys l=LK w=WG m=1
R1 RTUNE<1> RTUNE<0> rppolys l=LL w=WG m=1
R0 RTUNE<0> R2CAP rppolys l=LN w=WH m=1
.ENDS

************************************************************************
* Library Name: TempSensorLayout
* Cell Name:    TunableRes_nonUniform_Layout_Final_1dummy
* View Name:    schematic
************************************************************************

.SUBCKT TunableRes_nonUniform_Layout_Final_1dummy R2CAP RTUNE<7> RTUNE<6>
+ RTUNE<5> RTUNE<4> RTUNE<3> RTUNE<2> RTUNE<1> RTUNE<0> VSS
*.PININFO R2CAP:I RTUNE<7>:I RTUNE<6>:I RTUNE<5>:I RTUNE<4>:I RTUNE<3>:I
*.PININFO RTUNE<2>:I RTUNE<1>:I RTUNE<0>:I VSS:B
R7 RTUNE<7> RTUNE<6> rppolys l=LL w=WG m=1
R6 RTUNE<6> RTUNE<5> rppolys l=LK w=WG m=1
R5 RTUNE<5> RTUNE<4> rppolys l=LJ w=WF m=1
R4 RTUNE<4> RTUNE<3> rppolys l=LI w=WF m=1
R3 RTUNE<3> RTUNE<2> rppolys l=LJ w=WF m=1
R2 RTUNE<2> RTUNE<1> rppolys l=LK w=WG m=1
R1 RTUNE<1> RTUNE<0> rppolys l=LL w=WG m=1
R0 RTUNE<0> R2CAP rppolys l=LN w=WH m=1
.ENDS

************************************************************************
* Library Name: TempSensorLayout_PostLayout
* Cell Name:    PP_RCFilter
* View Name:    schematic
************************************************************************

.SUBCKT PP_RCFilter INPHASE<7> INPHASE<6> INPHASE<5> INPHASE<4> INPHASE<3>
+ INPHASE<2> INPHASE<1> INPHASE<0> OUTPHASE<7> OUTPHASE<6> OUTPHASE<5>
+ OUTPHASE<4> OUTPHASE<3> OUTPHASE<2> OUTPHASE<1> OUTPHASE<0> VCTL0<8>
+ VCTL0<7> VCTL0<6> VCTL0<5> VCTL0<4> VCTL0<3> VCTL0<2> VCTL0<1> VCTL0<0>
+ VCTLIN<8> VCTLIN<7> VCTLIN<6> VCTLIN<5> VCTLIN<4> VCTLIN<3> VCTLIN<2>
+ VCTLIN<1> VCTLIN<0> VDD VDLPF_P VSS
*.PININFO INPHASE<7>:I INPHASE<6>:I INPHASE<5>:I INPHASE<4>:I INPHASE<3>:I
*.PININFO INPHASE<2>:I INPHASE<1>:I INPHASE<0>:I OUTPHASE<7>:I OUTPHASE<6>:I
*.PININFO OUTPHASE<5>:I OUTPHASE<4>:I OUTPHASE<3>:I OUTPHASE<2>:I
*.PININFO OUTPHASE<1>:I OUTPHASE<0>:I VCTL0<8>:I VCTL0<7>:I VCTL0<6>:I
*.PININFO VCTL0<5>:I VCTL0<4>:I VCTL0<3>:I VCTL0<2>:I VCTL0<1>:I VCTL0<0>:I
*.PININFO VCTLIN<8>:I VCTLIN<7>:I VCTLIN<6>:I VCTLIN<5>:I VCTLIN<4>:I
*.PININFO VCTLIN<3>:I VCTLIN<2>:I VCTLIN<1>:I VCTLIN<0>:I VDLPF_P:O VDD:B VSS:B
XI2 VDLPF_N VDLPF_P VCTL0<8> VCTL0<7> VCTL0<6> VCTL0<5> VCTL0<4> VCTL0<3>
+ VCTL0<2> VCTL0<1> VCTL0<0> VCTLIN<8> VCTLIN<7> VCTLIN<6> VCTLIN<5> VCTLIN<4>
+ VCTLIN<3> VCTLIN<2> VCTLIN<1> VCTLIN<0> VDD VSS SwitchCapArray_V2
C0 VDLPF_P VDLPF_N cap_mom nv=20 nh=42 w=100n s=100n stm=2 spm=7 m=8
XI0 VDLPF_P INPHASE<7> INPHASE<6> INPHASE<5> INPHASE<4> INPHASE<3> INPHASE<2>
+ INPHASE<1> INPHASE<0> VSS TunableRes_nonUniform_Layout_Final
XI3 VDLPF_N OUTPHASE<7> OUTPHASE<6> OUTPHASE<5> OUTPHASE<4> OUTPHASE<3>
+ OUTPHASE<2> OUTPHASE<1> OUTPHASE<0> VSS
+ TunableRes_nonUniform_Layout_Final_1dummy
.ENDS

************************************************************************
* Library Name: TempSensorLayout_PostLayout
* Cell Name:    TempSensorCore_Post_Copy
* View Name:    schematic
************************************************************************

.SUBCKT TempSensorCore_Post_Copy CFG<7> CFG<6> CFG<5> CFG<4> CFG<3> CFG<2>
+ CFG<1> CFG<0> CFG<15> CFG<14> CKIN D<8> D<7> D<6> D<5> D<4> D<3> D<2> D<1>
+ D<0> DONE PRESET VDD VSS
*.PININFO CFG<7>:I CFG<6>:I CFG<5>:I CFG<4>:I CFG<3>:I CFG<2>:I CFG<1>:I
*.PININFO CFG<0>:I CFG<15>:I CFG<14>:I CKIN:I PRESET:I D<8>:O D<7>:O D<6>:O
*.PININFO D<5>:O D<4>:O D<3>:O D<2>:O D<1>:O D<0>:O DONE:O VDD:B VSS:B
XI0 CKIN COMPEN net014 net013 PRESET QPHASE VDD VSS CK_DividerBy8
XI6 COMPEN D<8> D<7> D<6> D<5> D<4> D<3> D<2> D<1> D<0> DONE PRESET net024<0>
+ net024<1> net024<2> net024<3> net024<4> net024<5> net024<6> net024<7>
+ net024<8> net025<0> net025<1> net025<2> net025<3> net025<4> net025<5>
+ net025<6> net025<7> net025<8> VDD VONL VOPL VSS SARLogic
XI8 net014 net023<0> net023<1> net023<2> net023<3> net023<4> net023<5>
+ net023<6> net023<7> net013 net022<0> net022<1> net022<2> net022<3> net022<4>
+ net022<5> net022<6> net022<7> CFG<7> CFG<6> CFG<5> CFG<4> CFG<3> CFG<2>
+ CFG<1> CFG<0> VDD VSS ResTune_CFG
XI7 net019 QPHASE CFG<14> CFG<15> net010 net020 VDD VSS CrossingDetector
XI5 COMPEN PRESET VDD net019 net020 VONL VOPL VSS EdgeComparator
XI2 net023<0> net023<1> net023<2> net023<3> net023<4> net023<5> net023<6>
+ net023<7> net022<0> net022<1> net022<2> net022<3> net022<4> net022<5>
+ net022<6> net022<7> net024<0> net024<1> net024<2> net024<3> net024<4>
+ net024<5> net024<6> net024<7> net024<8> net025<0> net025<1> net025<2>
+ net025<3> net025<4> net025<5> net025<6> net025<7> net025<8> VDD net010 VSS
+ PP_RCFilter
.ENDS

************************************************************************
* Library Name: TempSensorLayout_PostLayout
* Cell Name:    TempSensorCore_Post_Decap
* View Name:    schematic
************************************************************************

.SUBCKT Sanitized_TempSensor AVDD AVSS CFG<7> CFG<6> CFG<5> CFG<4> CFG<3>
+ CFG<2> CFG<1> CFG<0> CFG<15> CFG<14> CKIN D<8> D<7> D<6> D<5> D<4> D<3> D<2>
+ D<1> D<0> DONE PRESET
*.PININFO CFG<7>:I CFG<6>:I CFG<5>:I CFG<4>:I CFG<3>:I CFG<2>:I CFG<1>:I
*.PININFO CFG<0>:I CFG<15>:I CFG<14>:I CKIN:I PRESET:I D<8>:O D<7>:O D<6>:O
*.PININFO D<5>:O D<4>:O D<3>:O D<2>:O D<1>:O D<0>:O DONE:O AVDD:B AVSS:B
XI0 CFG<7> CFG<6> CFG<5> CFG<4> CFG<3> CFG<2> CFG<1> CFG<0> CFG<15> CFG<14>
+ CKIN D<8> D<7> D<6> D<5> D<4> D<3> D<2> D<1> D<0> DONE PRESET AVDD AVSS
+ TempSensorCore_Post_Copy
MM1 AVSS AVDD AVSS AVSS nch l=LD w=WS m=12
MM0 AVSS AVDD AVSS AVSS nch l=LC w=WR m=38
.ENDS

