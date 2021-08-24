************************************************************************
* auCdl Netlist:
*
* Library Name:  ADC_Layout
* Top Cell Name: Coarse_Comp_CK
* View Name:     schematic
* Netlisted on:  Jun 11 11:27:47 2019
************************************************************************

*.BIPOLAR
*.RESI = 2000
*.RESVAL
*.CAPVAL
*.DIOPERI
*.DIOAREA
*.EQUATION
*.LDD
*.SCALE METER
.PARAM



************************************************************************
* Library Name: monkey2
* Cell Name:    PINVD0YVT
* View Name:    schematic
************************************************************************

.SUBCKT PINVD0YVT I P VDD VSS ZN
*.PININFO I:I P:I ZN:O VDD:B VSS:B
MM4 ZN I net11 VSS nch_hvt l=LA w=WD m=1
MM1 net11 P VSS VSS nch_hvt l=LA w=WD m=1
MM3 net09 VSS VDD VDD pch_hvt l=LA w=WC m=1
MM0 ZN I net09 VDD pch_hvt l=LA w=WC m=1
.ENDS

************************************************************************
* Library Name: monkey2
* Cell Name:    INVD0HVT
* View Name:    schematic
************************************************************************

.SUBCKT INVD0HVT I ZN VDD VSS
*.PININFO I:I ZN:O VDD:B VSS:B
MMU1-M_u2 ZN I VSS VSS nch_hvt l=LA w=WD m=1
MMU1-M_u3 ZN I VDD VDD pch_hvt l=LA w=WC m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    ND2D3LVT
* View Name:    schematic
************************************************************************

.SUBCKT ND2D3LVT A1 A2 ZN VDD VSS
*.PININFO A1:I A2:I ZN:O VDD:B VSS:B
MMU3_0-M_u4 net21 A2 VSS VSS lvtnfet l=LA w=WB m=1
MMU3_1-M_u3 ZN A1 net20 VSS lvtnfet l=LA w=WB m=1
MMU3_2-M_u4 net13 A2 VSS VSS lvtnfet l=LA w=WB m=1
MMU3_1-M_u4 net20 A2 VSS VSS lvtnfet l=LA w=WB m=1
MMU3_0-M_u3 ZN A1 net21 VSS lvtnfet l=LA w=WB m=1
MMU3_2-M_u3 ZN A1 net13 VSS lvtnfet l=LA w=WB m=1
MMU3_2-M_u1 ZN A1 VDD VDD lvtpfet l=LA w=WA m=1
MMU3_1-M_u1 ZN A1 VDD VDD lvtpfet l=LA w=WA m=1
MMU3_1-M_u2 ZN A2 VDD VDD lvtpfet l=LA w=WA m=1
MMU3_2-M_u2 ZN A2 VDD VDD lvtpfet l=LA w=WA m=1
MMU3_0-M_u2 ZN A2 VDD VDD lvtpfet l=LA w=WA m=1
MMU3_0-M_u1 ZN A1 VDD VDD lvtpfet l=LA w=WA m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    NR3D1LVT
* View Name:    schematic
************************************************************************

.SUBCKT NR3D1LVT A1 A2 A3 ZN VDD VSS
*.PININFO A1:I A2:I A3:I ZN:O VDD:B VSS:B
MMI1_1 ZN A1 net5 VDD lvtpfet l=LA w=WA m=1
MM_u1_0 net17 A3 VDD VDD lvtpfet l=LA w=WA m=1
MMI1_0 ZN A1 net9 VDD lvtpfet l=LA w=WA m=1
MMI0_0 net9 A2 net17 VDD lvtpfet l=LA w=WA m=1
MMI0_1 net5 A2 net1 VDD lvtpfet l=LA w=WA m=1
MM_u1_1 net1 A3 VDD VDD lvtpfet l=LA w=WA m=1
MMI3 ZN A1 VSS VSS lvtnfet l=LA w=WB m=1
MMI2 ZN A2 VSS VSS lvtnfet l=LA w=WB m=1
MM_u4 ZN A3 VSS VSS lvtnfet l=LA w=WB m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    INVD2LVT
* View Name:    schematic
************************************************************************

.SUBCKT INVD2LVT I ZN VDD VSS
*.PININFO I:I ZN:O VDD:B VSS:B
MMU1_0-M_u2 ZN I VSS VSS lvtnfet l=LA w=WB m=1
MMU1_1-M_u2 ZN I VSS VSS lvtnfet l=LA w=WB m=1
MMU1_0-M_u3 ZN I VDD VDD lvtpfet l=LA w=WA m=1
MMU1_1-M_u3 ZN I VDD VDD lvtpfet l=LA w=WA m=1
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    Coarse_Comp_CK
* View Name:    schematic
************************************************************************

.SUBCKT Sanitized_Coarse_Comp_CK CKC CKSBT DVDD DVSS OUTNC OUTPC ST_FINE VALIDC VCTIN
*.PININFO VCTIN:I CKC:B CKSBT:B DVDD:B DVSS:B OUTNC:B OUTPC:B ST_FINE:B
*.PININFO VALIDC:B
XI67 net07 VCTIN DVDD DVSS net09 PINVD0YVT
XI46 net30 VCTIN DVDD DVSS net29 PINVD0YVT
XI21 net33 VCTIN DVDD DVSS net32 PINVD0YVT
XI12 net34 VCTIN DVDD DVSS net33 PINVD0YVT
XI47 net31 VCTIN DVDD DVSS net30 PINVD0YVT
XI0 net29 net07 DVDD DVSS INVD0HVT
XI22 net32 net31 DVDD DVSS INVD0HVT
XI3 OUTNC OUTPC VALIDC DVDD DVSS ND2D3LVT
XI218 VALIDC ST_FINE CKSBT net34 DVDD DVSS NR3D1LVT
XI65 net09 CKC DVDD DVSS INVD2LVT
.ENDS

