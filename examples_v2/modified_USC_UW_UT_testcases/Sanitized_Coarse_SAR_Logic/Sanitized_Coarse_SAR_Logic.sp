************************************************************************
* auCdl Netlist:
* 
* Library Name:  ADC_Layout
* Top Cell Name: Coarse_SAR_Logic
* View Name:     schematic
* Netlisted on:  Jun 11 11:21:45 2019
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
* Library Name: ADC_Layout
* Cell Name:    DFF_HVT_Coarse
* View Name:    schematic
************************************************************************

.SUBCKT DFF_HVT_Coarse CK D DGND DVDD Q QN
*.PININFO CK:I D:I Q:O QN:O DGND:B DVDD:B
MM2 QN CK NET4 DGND nch_hvt l=LA w=WC m=1
MM7 Q QN DGND DGND nch_hvt l=LA w=WC m=1
MM14 NET3 CK DGND DGND nch_hvt l=LA w=WB m=1
MM4 NET2 N1 NET3 DGND nch_hvt l=LA w=WB m=1
MM13 N1 D DGND DGND nch_hvt l=LA w=WB m=1
MM3 NET4 NET2 DGND DGND nch_hvt l=LA w=WC m=1
MM12 Q QN DVDD DVDD pch_hvt l=LA w=WD m=1
MM11 QN NET2 DVDD DVDD pch_hvt l=LA w=WD m=1
MM9 NET2 CK DVDD DVDD pch_hvt l=LA w=WB m=1
MM8 NET1 D DVDD DVDD pch_hvt l=LA w=WB m=1
MM15 N1 CK NET1 DVDD pch_hvt l=LA w=WB m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    INVD1LVT
* View Name:    schematic
************************************************************************

.SUBCKT INVD1LVT I ZN VDD VSS
*.PININFO I:I ZN:O VDD:B VSS:B
MMU1-M_u2 ZN I VSS VSS lvtnfet l=LA w=WC m=1
MMU1-M_u3 ZN I VDD VDD lvtpfet l=LA w=WD m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    TIEHLVT
* View Name:    schematic
************************************************************************

.SUBCKT TIEHLVT Z VDD VSS
*.PININFO Z:O VDD:B VSS:B
MM_u2 net7 net7 VSS VSS lvtnfet l=LA w=WF m=1
MM_u1 Z net7 VDD VDD lvtpfet l=LA w=WE m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    NR2D1LVT
* View Name:    schematic
************************************************************************

.SUBCKT NR2D1LVT A1 A2 ZN VDD VSS
*.PININFO A1:I A2:I ZN:O VDD:B VSS:B
MMI1-M_u3 ZN A2 VSS VSS lvtnfet l=LA w=WC m=1
MMI1-M_u4 ZN A1 VSS VSS lvtnfet l=LA w=WC m=1
MMI1-M_u1 net13 A2 VDD VDD lvtpfet l=LA w=WD m=1
MMI1-M_u2 ZN A1 net13 VDD lvtpfet l=LA w=WD m=1
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    DFFRB_B_V6_HVT
* View Name:    schematic
************************************************************************

.SUBCKT DFFRB_B_V6_HVT CK D DVDD DVSS Q RST
*.PININFO CK:I D:I RST:I Q:O DVDD:B DVSS:B
MM8 NET1 D DVDD DVDD pch_hvt l=LA w=WB m=1
MM10 NET2 CK net58 DVDD pch_hvt l=LA w=WB m=1
MM19 net58 RSTB DVDD DVDD pch_hvt l=LA w=WB m=1
MM15 net06 RST DVDD DVDD pch_hvt l=LA w=WG m=1
MM9 M1 CK NET1 DVDD pch_hvt l=LA w=WB m=1
MM14 Q net06 DVDD DVDD pch_hvt l=LA w=WD m=1
MM12 net06 NET2 DVDD DVDD pch_hvt l=LA w=WD m=1
MM0 RSTB RST DVDD DVDD pch_hvt l=LA w=WH m=1
MM16 NET3 CK DVSS DVSS nch_hvt l=LA w=WB m=1
MM13 NET4 NET2 DVSS DVSS nch_hvt l=LA w=WC m=1
MM7 Q net06 DVSS DVSS nch_hvt l=LA w=WC m=1
MM6 net06 CK NET4 DVSS nch_hvt l=LA w=WC m=1
MM17 M1 D DVSS DVSS nch_hvt l=LA w=WB m=1
MM5 NET2 RSTB DVSS DVSS nch_hvt l=LA w=WB m=1
MM4 NET2 M1 NET3 DVSS nch_hvt l=LA w=WB m=1
MM18 RSTB RST DVSS DVSS nch_hvt l=LA w=WA m=1
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    Coarse_SAR_Logic
* View Name:    schematic
************************************************************************

.SUBCKT Sanitized_Coarse_SAR_Logic CK<11> CK<10> CK<9> CK<8> CKSBT CKSBTB CPY D<11> 
+ D<10> D<9> D<8> DB<11> DB<10> DB<9> DB<8> DF<11> DF<10> DF<9> DF<8> DF<7> 
+ DFB<11> DFB<10> DFB<9> DFB<8> DFB<7> DVDD DVSS OUTNC OUTPC ST_FINE SWC<11> 
+ SWC<10> SWC<9> SWC<8> SWCB<11> SWCB<10> SWCB<9> SWCB<8> TGC<11> TGC<10> 
+ TGC<9> TGC<8> TGCB<11> TGCB<10> TGCB<9> TGCB<8> VALIDC
*.PININFO CPY:O ST_FINE:O CK<11>:B CK<10>:B CK<9>:B CK<8>:B CKSBT:B CKSBTB:B 
*.PININFO D<11>:B D<10>:B D<9>:B D<8>:B DB<11>:B DB<10>:B DB<9>:B DB<8>:B 
*.PININFO DF<11>:B DF<10>:B DF<9>:B DF<8>:B DF<7>:B DFB<11>:B DFB<10>:B 
*.PININFO DFB<9>:B DFB<8>:B DFB<7>:B DVDD:B DVSS:B OUTNC:B OUTPC:B SWC<11>:B 
*.PININFO SWC<10>:B SWC<9>:B SWC<8>:B SWCB<11>:B SWCB<10>:B SWCB<9>:B 
*.PININFO SWCB<8>:B TGC<11>:B TGC<10>:B TGC<9>:B TGC<8>:B TGCB<11>:B 
*.PININFO TGCB<10>:B TGCB<9>:B TGCB<8>:B VALIDC:B
XI228 CPY OUTNC DVSS DVDD net057 net018 / DFF_HVT_Coarse
XI227 CK<8> OUTNC DVSS DVDD DB<8> D<8> / DFF_HVT_Coarse
XI229 CK<11> OUTPC DVSS DVDD D<11> DB<11> / DFF_HVT_Coarse
XI230 CK<10> OUTPC DVSS DVDD D<10> DB<10> / DFF_HVT_Coarse
XI231 CK<9> OUTNC DVSS DVDD DB<9> D<9> / DFF_HVT_Coarse
XI18 net018 DFB<7> DVDD DVSS / INVD1LVT
XI17 net057 DF<7> DVDD DVSS / INVD1LVT
XI16 DB<8> DF<8> DVDD DVSS / INVD1LVT
XI15 D<8> DFB<8> DVDD DVSS / INVD1LVT
XI14 D<9> DFB<9> DVDD DVSS / INVD1LVT
XI13 DB<9> DF<9> DVDD DVSS / INVD1LVT
XI12 DB<10> DF<10> DVDD DVSS / INVD1LVT
XI11 D<10> DFB<10> DVDD DVSS / INVD1LVT
XI173 TGC<11> TGCB<11> DVDD DVSS / INVD1LVT
XI31 SWC<11> SWCB<11> DVDD DVSS / INVD1LVT
XI104 SWC<10> SWCB<10> DVDD DVSS / INVD1LVT
XI170 TGC<10> TGCB<10> DVDD DVSS / INVD1LVT
XI158 TGC<9> TGCB<9> DVDD DVSS / INVD1LVT
XI102 SWC<9> SWCB<9> DVDD DVSS / INVD1LVT
XI100 SWC<8> SWCB<8> DVDD DVSS / INVD1LVT
XI155 TGC<8> TGCB<8> DVDD DVSS / INVD1LVT
XI9 D<11> DFB<11> DVDD DVSS / INVD1LVT
XI10 DB<11> DF<11> DVDD DVSS / INVD1LVT
XI8 net054 DVDD DVSS / TIEHLVT
XI175 CK<11> CKSBT TGC<11> DVDD DVSS / NR2D1LVT
XI107 TGC<11> CKSBT SWC<11> DVDD DVSS / NR2D1LVT
XI171 CK<10> CKSBT TGC<10> DVDD DVSS / NR2D1LVT
XI105 TGC<10> CKSBT SWC<10> DVDD DVSS / NR2D1LVT
XI39 TGC<9> CKSBT SWC<9> DVDD DVSS / NR2D1LVT
XI159 CK<9> CKSBT TGC<9> DVDD DVSS / NR2D1LVT
XI101 TGC<8> CKSBT SWC<8> DVDD DVSS / NR2D1LVT
XI156 CK<8> CKSBT TGC<8> DVDD DVSS / NR2D1LVT
XI53 VALIDC net133 DVDD DVSS ST_FINE CKSBTB / DFFRB_B_V6_HVT
XI54 VALIDC CPY DVDD DVSS net133 CKSBTB / DFFRB_B_V6_HVT
XI213 VALIDC CK<11> DVDD DVSS CK<10> CKSBTB / DFFRB_B_V6_HVT
XI212 VALIDC net054 DVDD DVSS CK<11> CKSBTB / DFFRB_B_V6_HVT
XI214 VALIDC CK<10> DVDD DVSS CK<9> CKSBTB / DFFRB_B_V6_HVT
XI215 VALIDC CK<9> DVDD DVSS CK<8> CKSBTB / DFFRB_B_V6_HVT
XI216 VALIDC CK<8> DVDD DVSS CPY CKSBTB / DFFRB_B_V6_HVT
.ENDS

