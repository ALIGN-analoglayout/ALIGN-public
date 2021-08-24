************************************************************************
* auCdl Netlist:
*
* Library Name:  ADC_Layout
* Top Cell Name: 12b_ADC_TOP
* View Name:     schematic
* Netlisted on:  Mar 12 12:01:10 2019
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
* Cell Name:    SW1_Dummy_V2
* View Name:    schematic
************************************************************************

.SUBCKT SW1_Dummy_V2 CKS CKSB DVDD DVSS VBTSW VCM VIN VO
*.PININFO CKS:I CKSB:I VCM:I VIN:I VO:O DVDD:B DVSS:B VBTSW:B
MM6 VO VBTSW VIN DVSS nch_dnw l=LA w=WB m=1
MM5 VO CKSB VCM DVSS nch_dnw l=LA w=WB m=1
MM2 VO CKS VCM DVDD pch l=LA w=WB m=1
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    SW1_V2
* View Name:    schematic
************************************************************************

.SUBCKT SW1_V2 D DVDD DVSS SW SWB TG TGB VBTSW VCM VIN VO VREFN VREFP
*.PININFO D:I SW:I SWB:I TG:I TGB:I VCM:I VIN:I VREFN:I VREFP:I VO:O DVDD:B
*.PININFO DVSS:B VBTSW:B
MM6 VO VBTSW VIN DVSS nch_dnw l=LA w=WB m=1
MM5 VO TG VCM DVSS nch_dnw l=LA w=WB m=1
MM4 net22 D VREFN DVSS nch_dnw l=LA w=WC m=1
MM3 VO SW net22 DVSS nch_dnw l=LA w=WC m=1
MM2 VO TGB VCM DVDD pch l=LA w=WB m=1
MM1 VO SWB net23 DVDD pch l=LA w=WI m=1
MM0 net23 D VREFP DVDD pch l=LA w=WI m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    ND2D1LVT
* View Name:    schematic
************************************************************************

.SUBCKT ND2D1LVT A1 A2 ZN VDD VSS
*.PININFO A1:I A2:I ZN:O VDD:B VSS:B
MMI1-M_u3 ZN A1 net1 VSS lvtnfet l=LA w=WP m=1
MMI1-M_u4 net1 A2 VSS VSS lvtnfet l=LA w=WP m=1
MMI1-M_u1 ZN A1 VDD VDD lvtpfet l=LA w=WV m=1
MMI1-M_u2 ZN A2 VDD VDD lvtpfet l=LA w=WV m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    INVD0LVT
* View Name:    schematic
************************************************************************

.SUBCKT INVD0LVT I ZN VDD VSS
*.PININFO I:I ZN:O VDD:B VSS:B
MMU1-M_u2 ZN I VSS VSS lvtnfet l=LA w=WC m=1
MMU1-M_u3 ZN I VDD VDD lvtpfet l=LA w=WI m=1
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    SW_Cres_v3_6
* View Name:    schematic
************************************************************************

.SUBCKT SW_Cres_v3_6 CK DVDD DVSS VRCTL VRN VRNX VRP VRPX
*.PININFO VRCTL:I CK:B DVDD:B DVSS:B VRN:B VRNX:B VRP:B VRPX:B
MM3 VRN CLK VRN DVSS nch l=LA w=WB m=1
MM2 VRN net010 VRNX DVSS nch l=LA w=WK m=1
MM4 VRP net018 VRP DVDD pch l=LA w=WB m=1
MM1 VRP CLK VRPX DVDD pch l=LA w=WK m=1
XI11 CK VRCTL net010 DVDD DVSS ND2D1LVT
XI5 CLK net018 DVDD DVSS INVD0LVT
XI6 net010 CLK DVDD DVSS INVD0LVT
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    SW_Cres_v3_5
* View Name:    schematic
************************************************************************

.SUBCKT SW_Cres_v3_5 CK DVDD DVSS VRCTL VRN VRNX VRP VRPX
*.PININFO VRCTL:I CK:B DVDD:B DVSS:B VRN:B VRNX:B VRP:B VRPX:B
MM3 VRN CLK VRN DVSS nch l=LA w=WB m=1
MM2 VRN net010 VRNX DVSS nch l=LA w=WK m=1
MM4 VRP net018 VRP DVDD pch l=LA w=WB m=1
MM1 VRP CLK VRPX DVDD pch l=LA w=WK m=1
XI11 CK VRCTL net010 DVDD DVSS ND2D1LVT
XI5 CLK net018 DVDD DVSS INVD0LVT
XI6 net010 CLK DVDD DVSS INVD0LVT
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    SW2_V2
* View Name:    schematic
************************************************************************

.SUBCKT SW2_V2 D DVDD DVSS SW SWB TG TGB VBTSW VCM VIN VO VREFN VREFP
*.PININFO D:I SW:I SWB:I TG:I TGB:I VCM:I VIN:I VREFN:I VREFP:I VO:O DVDD:B
*.PININFO DVSS:B VBTSW:B
MM6 VO VBTSW VIN DVSS nch_dnw l=LA w=WB m=1
MM5 VO TG VCM DVSS nch_dnw l=LA w=WB m=1
MM4 net22 D VREFN DVSS nch_dnw l=LA w=WP m=1
MM3 VO SW net22 DVSS nch_dnw l=LA w=WP m=1
MM2 VO TGB VCM DVDD pch l=LA w=WB m=1
MM1 VO SWB net23 DVDD pch l=LA w=WV m=1
MM0 net23 D VREFP DVDD pch l=LA w=WV m=1
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    SW3_V2
* View Name:    schematic
************************************************************************

.SUBCKT SW3_V2 D DVDD DVSS SW SWB TG TGB VBTSW VCM VIN VO VREFN VREFP
*.PININFO D:I SW:I SWB:I TG:I TGB:I VCM:I VIN:I VREFN:I VREFP:I VO:O DVDD:B
*.PININFO DVSS:B VBTSW:B
MM6 VO VBTSW VIN DVSS nch_dnw l=LA w=WB m=1
MM5 VO TG VCM DVSS nch_dnw l=LA w=WB m=1
MM4 net22 D VREFN DVSS nch_dnw l=LA w=WP m=2
MM3 VO SW net22 DVSS nch_dnw l=LA w=WP m=2
MM2 VO TGB VCM DVDD pch l=LA w=WB m=1
MM1 VO SWB net23 DVDD pch l=LA w=WV m=2
MM0 net23 D VREFP DVDD pch l=LA w=WV m=2
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    SW4_V2
* View Name:    schematic
************************************************************************

.SUBCKT SW4_V2 D DVDD DVSS SW SWB TG TGB VBTSW VCM VIN VO VREFN VREFP
*.PININFO D:I SW:I SWB:I TG:I TGB:I VCM:I VIN:I VREFN:I VREFP:I VO:O DVDD:B
*.PININFO DVSS:B VBTSW:B
MM6 VO VBTSW VIN DVSS nch_dnw l=LA w=WB m=1
MM5 VO TG VCM DVSS nch_dnw l=LA w=WH m=1
MM4 net22 D VREFN DVSS nch_dnw l=LA w=WP m=4
MM3 VO SW net22 DVSS nch_dnw l=LA w=WP m=4
MM2 VO TGB VCM DVDD pch l=LA w=WH m=1
MM1 VO SWB net23 DVDD pch l=LA w=WV m=4
MM0 net23 D VREFP DVDD pch l=LA w=WV m=4
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    TG_Top_Coarse
* View Name:    schematic
************************************************************************

.SUBCKT TG_Top_Coarse CKS CKSB DVDD DVSS VCM VO
*.PININFO CKS:I CKSB:I VCM:I VO:O DVDD:B DVSS:B
MM5 VO CKS VCM DVSS lvtnfet_dnw l=LA w=WU m=2
MM2 VO CKSB VCM DVDD lvtpfet l=LA w=WU m=2
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    CDAC_SW_Coarse
* View Name:    schematic
************************************************************************

.SUBCKT CDAC_SW_Coarse C<11> C<10> C<9> C<8> C<7> CK<11> CK<10> CK<9> CK<8>
+ CKS CKSB CKSBT CKSBTB D<11> D<10> D<9> D<8> DVDD DVSS SWC<11> SWC<10> SWC<9>
+ SWC<8> SWCB<11> SWCB<10> SWCB<9> SWCB<8> TGC<11> TGC<10> TGC<9> TGC<8>
+ TGCB<11> TGCB<10> TGCB<9> TGCB<8> VBTN VCM VCP VIN VRCTL VRN<11> VRN<10>
+ VRN<9> VRN<8> VRNX VRP<11> VRP<10> VRP<9> VRP<8> VRPX
*.PININFO CKS:I CKSB:I VRCTL:I VRNX:I VRPX:I C<11>:B C<10>:B C<9>:B C<8>:B
*.PININFO C<7>:B CK<11>:B CK<10>:B CK<9>:B CK<8>:B CKSBT:B CKSBTB:B D<11>:B
*.PININFO D<10>:B D<9>:B D<8>:B DVDD:B DVSS:B SWC<11>:B SWC<10>:B SWC<9>:B
*.PININFO SWC<8>:B SWCB<11>:B SWCB<10>:B SWCB<9>:B SWCB<8>:B TGC<11>:B
*.PININFO TGC<10>:B TGC<9>:B TGC<8>:B TGCB<11>:B TGCB<10>:B TGCB<9>:B
*.PININFO TGCB<8>:B VBTN:B VCM:B VCP:B VIN:B VRN<11>:B VRN<10>:B VRN<9>:B
*.PININFO VRN<8>:B VRP<11>:B VRP<10>:B VRP<9>:B VRP<8>:B
XCres10<0> VRP<10> VRN<10> nmoscap lr=3u wr=3u m=1
XCres10<1> VRP<10> VRN<10> nmoscap lr=3u wr=3u m=1
XCres10<2> VRP<10> VRN<10> nmoscap lr=3u wr=3u m=1
XCres10<3> VRP<10> VRN<10> nmoscap lr=3u wr=3u m=1
XCres10<4> VRP<10> VRN<10> nmoscap lr=3u wr=3u m=1
XCres10<5> VRP<10> VRN<10> nmoscap lr=3u wr=3u m=1
XCres10<6> VRP<10> VRN<10> nmoscap lr=3u wr=3u m=1
XCres10<7> VRP<10> VRN<10> nmoscap lr=3u wr=3u m=1
XCres10<8> VRP<10> VRN<10> nmoscap lr=3u wr=3u m=1
XCres10<9> VRP<10> VRN<10> nmoscap lr=3u wr=3u m=1
XCres10<10> VRP<10> VRN<10> nmoscap lr=3u wr=3u m=1
XCres10<11> VRP<10> VRN<10> nmoscap lr=3u wr=3u m=1
XCres11<0> VRP<11> VRN<11> nmoscap lr=3u wr=3u m=1
XCres11<1> VRP<11> VRN<11> nmoscap lr=3u wr=3u m=1
XCres11<2> VRP<11> VRN<11> nmoscap lr=3u wr=3u m=1
XCres11<3> VRP<11> VRN<11> nmoscap lr=3u wr=3u m=1
XCres11<4> VRP<11> VRN<11> nmoscap lr=3u wr=3u m=1
XCres11<5> VRP<11> VRN<11> nmoscap lr=3u wr=3u m=1
XCres11<6> VRP<11> VRN<11> nmoscap lr=3u wr=3u m=1
XCres11<7> VRP<11> VRN<11> nmoscap lr=3u wr=3u m=1
XCres11<8> VRP<11> VRN<11> nmoscap lr=3u wr=3u m=1
XCres11<9> VRP<11> VRN<11> nmoscap lr=3u wr=3u m=1
XCres11<10> VRP<11> VRN<11> nmoscap lr=3u wr=3u m=1
XCres11<11> VRP<11> VRN<11> nmoscap lr=3u wr=3u m=1
XCres11<12> VRP<11> VRN<11> nmoscap lr=3u wr=3u m=1
XCres11<13> VRP<11> VRN<11> nmoscap lr=3u wr=3u m=1
XCres11<14> VRP<11> VRN<11> nmoscap lr=3u wr=3u m=1
XCres11<15> VRP<11> VRN<11> nmoscap lr=3u wr=3u m=1
XCres11<16> VRP<11> VRN<11> nmoscap lr=3u wr=3u m=1
XCres11<17> VRP<11> VRN<11> nmoscap lr=3u wr=3u m=1
XCres11<18> VRP<11> VRN<11> nmoscap lr=3u wr=3u m=1
XCres11<19> VRP<11> VRN<11> nmoscap lr=3u wr=3u m=1
XCres11<20> VRP<11> VRN<11> nmoscap lr=3u wr=3u m=1
XCres11<21> VRP<11> VRN<11> nmoscap lr=3u wr=3u m=1
XCres11<22> VRP<11> VRN<11> nmoscap lr=3u wr=3u m=1
XCres11<23> VRP<11> VRN<11> nmoscap lr=3u wr=3u m=1
XCres11<24> VRP<11> VRN<11> nmoscap lr=3u wr=3u m=1
XCres11<25> VRP<11> VRN<11> nmoscap lr=3u wr=3u m=1
XCres11<26> VRP<11> VRN<11> nmoscap lr=3u wr=3u m=1
XCres11<27> VRP<11> VRN<11> nmoscap lr=3u wr=3u m=1
XCres11<28> VRP<11> VRN<11> nmoscap lr=3u wr=3u m=1
XCres11<29> VRP<11> VRN<11> nmoscap lr=3u wr=3u m=1
XC0<0> VRP<9> VRN<9> nmoscap lr=3u wr=3u m=1
XC0<1> VRP<9> VRN<9> nmoscap lr=3u wr=3u m=1
XC0<2> VRP<9> VRN<9> nmoscap lr=3u wr=3u m=1
XC0<3> VRP<9> VRN<9> nmoscap lr=3u wr=3u m=1
XC0<4> VRP<9> VRN<9> nmoscap lr=3u wr=3u m=1
XC0<5> VRP<9> VRN<9> nmoscap lr=3u wr=3u m=1
XCres8<0> VRP<8> VRN<8> nmoscap lr=3u wr=3u m=1
XCres8<1> VRP<8> VRN<8> nmoscap lr=3u wr=3u m=1
XCres8<2> VRP<8> VRN<8> nmoscap lr=3u wr=3u m=1
XCres8<3> VRP<8> VRN<8> nmoscap lr=3u wr=3u m=1
XCres8<4> VRP<8> VRN<8> nmoscap lr=3u wr=3u m=1
XCres8<5> VRP<8> VRN<8> nmoscap lr=3u wr=3u m=1
XCres8<6> VRP<8> VRN<8> nmoscap lr=3u wr=3u m=1
XCres8<7> VRP<8> VRN<8> nmoscap lr=3u wr=3u m=1
XCres8<8> VRP<8> VRN<8> nmoscap lr=3u wr=3u m=1
XCres8<9> VRP<8> VRN<8> nmoscap lr=3u wr=3u m=1
XCres8<10> VRP<8> VRN<8> nmoscap lr=3u wr=3u m=1
XCres8<11> VRP<8> VRN<8> nmoscap lr=3u wr=3u m=1
XI2 CKSBT CKSBTB DVDD DVSS VBTN VCM VIN C<7> SW1_Dummy_V2
XI3 D<8> DVDD DVSS SWC<8> SWCB<8> TGC<8> TGCB<8> VBTN VCM VIN C<8> VRN<8>
+ VRP<8> SW1_V2
XI0 CK<11> DVDD DVSS VRCTL VRN<11> VRNX VRP<11> VRPX SW_Cres_v3_6
XI4 CK<10> DVDD DVSS VRCTL VRN<10> VRNX VRP<10> VRPX SW_Cres_v3_6
XCr11<0> CK<11> DVDD DVSS VRCTL VRN<11> VRNX VRP<11> VRPX SW_Cres_v3_5
XCr11<1> CK<11> DVDD DVSS VRCTL VRN<11> VRNX VRP<11> VRPX SW_Cres_v3_5
XCr11<2> CK<11> DVDD DVSS VRCTL VRN<11> VRNX VRP<11> VRPX SW_Cres_v3_5
XCr11<3> CK<11> DVDD DVSS VRCTL VRN<11> VRNX VRP<11> VRPX SW_Cres_v3_5
XI1 CK<10> DVDD DVSS VRCTL VRN<10> VRNX VRP<10> VRPX SW_Cres_v3_5
XI6 CK<9> DVDD DVSS VRCTL VRN<9> VRNX VRP<9> VRPX SW_Cres_v3_5
XSW<0> CK<8> DVDD DVSS VRCTL VRN<8> VRNX VRP<8> VRPX SW_Cres_v3_5
XSW<1> CK<8> DVDD DVSS VRCTL VRN<8> VRNX VRP<8> VRPX SW_Cres_v3_5
XI8 D<9> DVDD DVSS SWC<9> SWCB<9> TGC<9> TGCB<9> VBTN VCM VIN C<9> VRN<9>
+ VRP<9> SW2_V2
XI9 D<10> DVDD DVSS SWC<10> SWCB<10> TGC<10> TGCB<10> VBTN VCM VIN C<10>
+ VRN<10> VRP<10> SW3_V2
XI10 D<11> DVDD DVSS SWC<11> SWCB<11> TGC<11> TGCB<11> VBTN VCM VIN C<11>
+ VRN<11> VRP<11> SW4_V2
XI5 CKS CKSB DVDD DVSS VCM VCP TG_Top_Coarse
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    DFF_HVT_Coarse
* View Name:    schematic
************************************************************************

.SUBCKT DFF_HVT_Coarse CK D DGND DVDD Q QN
*.PININFO CK:I D:I Q:O QN:O DGND:B DVDD:B
MM2 QN CK NET4 DGND nch_hvt l=LA w=WP m=1
MM7 Q QN DGND DGND nch_hvt l=LA w=WP m=1
MM14 NET3 CK DGND DGND nch_hvt l=LA w=WB m=1
MM4 NET2 N1 NET3 DGND nch_hvt l=LA w=WB m=1
MM13 N1 D DGND DGND nch_hvt l=LA w=WB m=1
MM3 NET4 NET2 DGND DGND nch_hvt l=LA w=WP m=1
MM12 Q QN DVDD DVDD pch_hvt l=LA w=WV m=1
MM11 QN NET2 DVDD DVDD pch_hvt l=LA w=WV m=1
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
MMU1-M_u2 ZN I VSS VSS lvtnfet l=LA w=WP m=1
MMU1-M_u3 ZN I VDD VDD lvtpfet l=LA w=WV m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    TIEHLVT
* View Name:    schematic
************************************************************************

.SUBCKT TIEHLVT Z VDD VSS
*.PININFO Z:O VDD:B VSS:B
MM_u2 net7 net7 VSS VSS lvtnfet l=LA w=WR m=1
MM_u1 Z net7 VDD VDD lvtpfet l=LA w=WX m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    NR2D1LVT
* View Name:    schematic
************************************************************************

.SUBCKT NR2D1LVT A1 A2 ZN VDD VSS
*.PININFO A1:I A2:I ZN:O VDD:B VSS:B
MMI1-M_u3 ZN A2 VSS VSS lvtnfet l=LA w=WP m=1
MMI1-M_u4 ZN A1 VSS VSS lvtnfet l=LA w=WP m=1
MMI1-M_u1 net13 A2 VDD VDD lvtpfet l=LA w=WV m=1
MMI1-M_u2 ZN A1 net13 VDD lvtpfet l=LA w=WV m=1
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
MM15 net06 RST DVDD DVDD pch_hvt l=LA w=WU m=1
MM9 M1 CK NET1 DVDD pch_hvt l=LA w=WB m=1
MM14 Q net06 DVDD DVDD pch_hvt l=LA w=WV m=1
MM12 net06 NET2 DVDD DVDD pch_hvt l=LA w=WV m=1
MM0 RSTB RST DVDD DVDD pch_hvt l=LA w=WI m=1
MM16 NET3 CK DVSS DVSS nch_hvt l=LA w=WB m=1
MM13 NET4 NET2 DVSS DVSS nch_hvt l=LA w=WP m=1
MM7 Q net06 DVSS DVSS nch_hvt l=LA w=WP m=1
MM6 net06 CK NET4 DVSS nch_hvt l=LA w=WP m=1
MM17 M1 D DVSS DVSS nch_hvt l=LA w=WB m=1
MM5 NET2 RSTB DVSS DVSS nch_hvt l=LA w=WB m=1
MM4 NET2 M1 NET3 DVSS nch_hvt l=LA w=WB m=1
MM18 RSTB RST DVSS DVSS nch_hvt l=LA w=WC m=1
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    Coarse_SAR_Logic
* View Name:    schematic
************************************************************************

.SUBCKT Coarse_SAR_Logic CK<11> CK<10> CK<9> CK<8> CKSBT CKSBTB CPY D<11>
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
XI228 CPY OUTNC DVSS DVDD net057 net018 DFF_HVT_Coarse
XI227 CK<8> OUTNC DVSS DVDD DB<8> D<8> DFF_HVT_Coarse
XI229 CK<11> OUTPC DVSS DVDD D<11> DB<11> DFF_HVT_Coarse
XI230 CK<10> OUTPC DVSS DVDD D<10> DB<10> DFF_HVT_Coarse
XI231 CK<9> OUTNC DVSS DVDD DB<9> D<9> DFF_HVT_Coarse
XI18 net018 DFB<7> DVDD DVSS INVD1LVT
XI17 net057 DF<7> DVDD DVSS INVD1LVT
XI16 DB<8> DF<8> DVDD DVSS INVD1LVT
XI15 D<8> DFB<8> DVDD DVSS INVD1LVT
XI14 D<9> DFB<9> DVDD DVSS INVD1LVT
XI13 DB<9> DF<9> DVDD DVSS INVD1LVT
XI12 DB<10> DF<10> DVDD DVSS INVD1LVT
XI11 D<10> DFB<10> DVDD DVSS INVD1LVT
XI173 TGC<11> TGCB<11> DVDD DVSS INVD1LVT
XI31 SWC<11> SWCB<11> DVDD DVSS INVD1LVT
XI104 SWC<10> SWCB<10> DVDD DVSS INVD1LVT
XI170 TGC<10> TGCB<10> DVDD DVSS INVD1LVT
XI158 TGC<9> TGCB<9> DVDD DVSS INVD1LVT
XI102 SWC<9> SWCB<9> DVDD DVSS INVD1LVT
XI100 SWC<8> SWCB<8> DVDD DVSS INVD1LVT
XI155 TGC<8> TGCB<8> DVDD DVSS INVD1LVT
XI9 D<11> DFB<11> DVDD DVSS INVD1LVT
XI10 DB<11> DF<11> DVDD DVSS INVD1LVT
XI8 net054 DVDD DVSS TIEHLVT
XI175 CK<11> CKSBT TGC<11> DVDD DVSS NR2D1LVT
XI107 TGC<11> CKSBT SWC<11> DVDD DVSS NR2D1LVT
XI171 CK<10> CKSBT TGC<10> DVDD DVSS NR2D1LVT
XI105 TGC<10> CKSBT SWC<10> DVDD DVSS NR2D1LVT
XI39 TGC<9> CKSBT SWC<9> DVDD DVSS NR2D1LVT
XI159 CK<9> CKSBT TGC<9> DVDD DVSS NR2D1LVT
XI101 TGC<8> CKSBT SWC<8> DVDD DVSS NR2D1LVT
XI156 CK<8> CKSBT TGC<8> DVDD DVSS NR2D1LVT
XI53 VALIDC net133 DVDD DVSS ST_FINE CKSBTB DFFRB_B_V6_HVT
XI54 VALIDC CPY DVDD DVSS net133 CKSBTB DFFRB_B_V6_HVT
XI213 VALIDC CK<11> DVDD DVSS CK<10> CKSBTB DFFRB_B_V6_HVT
XI212 VALIDC net054 DVDD DVSS CK<11> CKSBTB DFFRB_B_V6_HVT
XI214 VALIDC CK<10> DVDD DVSS CK<9> CKSBTB DFFRB_B_V6_HVT
XI215 VALIDC CK<9> DVDD DVSS CK<8> CKSBTB DFFRB_B_V6_HVT
XI216 VALIDC CK<8> DVDD DVSS CPY CKSBTB DFFRB_B_V6_HVT
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    INVD2LVT
* View Name:    schematic
************************************************************************

.SUBCKT INVD2LVT I ZN VDD VSS
*.PININFO I:I ZN:O VDD:B VSS:B
MMU1_0-M_u3 ZN I VDD VDD lvtpfet l=LA w=WV m=1
MMU1_1-M_u3 ZN I VDD VDD lvtpfet l=LA w=WV m=1
MMU1_0-M_u2 ZN I VSS VSS lvtnfet_dnw l=LA w=WP m=1
MMU1_1-M_u2 ZN I VSS VSS lvtnfet_dnw l=LA w=WP m=1
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    INVD1LVT_schematic
* View Name:    schematic
************************************************************************

.SUBCKT INVD1LVT_schematic I ZN VDD VSS
*.PININFO I:I ZN:O VDD:B VSS:B
MMU1-M_u3 ZN I VDD VDD lvtpfet l=LA w=WV m=1
MMU1-M_u2 ZN I VSS VSS lvtnfet_dnw l=LA w=WP m=1
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    INVD0HVT
* View Name:    schematic
************************************************************************

.SUBCKT INVD0HVT I ZN VDD VSS
*.PININFO I:I ZN:O VDD:B VSS:B
MMU1-M_u3 ZN I VDD VDD pch_hvt l=LA w=WI m=1
MMU1-M_u2 ZN I VSS VSS nch_hvt_dnw l=LA w=WC m=1
.ENDS

************************************************************************
* Library Name: AW_12b_SARADC
* Cell Name:    Comp_Coarse_V3_Cali
* View Name:    schematic
************************************************************************

.SUBCKT Comp_Coarse_V3_Cali AVDD AVSS CKC N<1> N<2> N<3> N<4> OUTNC OUTPC P<1>
+ P<2> P<3> P<4> VCN VCP
*.PININFO CKC:I N<1>:I N<2>:I N<3>:I N<4>:I P<1>:I P<2>:I P<3>:I P<4>:I VCN:I
*.PININFO VCP:I OUTNC:O OUTPC:O AVDD:B AVSS:B
MM17 net29 net041 net29 AVSS nch_hvt_dnw l=LD w=WK m=2
MM16 net29 net040 net29 AVSS nch_hvt_dnw l=LD w=WQ m=3
MM15 net29 net043 net29 AVSS nch_hvt_dnw l=LD w=WK m=1
MM14 net29 net042 net29 AVSS nch_hvt_dnw l=LD w=WB m=1
MM13 net017 net036 net017 AVSS nch_hvt_dnw l=LD w=WB m=1
MM12 net017 net037 net017 AVSS nch_hvt_dnw l=LD w=WK m=1
MM11 net017 net038 net017 AVSS nch_hvt_dnw l=LD w=WK m=2
MM10 net017 net027 net017 AVSS nch_hvt_dnw l=LD w=WQ m=3
MM9 net15 CKC AVDD AVDD lvtpfet l=LD w=WI m=2
MM8 net19 CKC AVDD AVDD lvtpfet l=LD w=WI m=2
MM7 net15 net19 AVDD AVDD lvtpfet l=LD w=WI m=2
MM6 net19 net15 AVDD AVDD lvtpfet l=LD w=WI m=2
XI3 net026 OUTNC AVDD AVSS INVD2LVT
XI2 net025 OUTPC AVDD AVSS INVD2LVT
XI1 net15 net025 AVDD AVSS INVD1LVT_schematic
XI0 net19 net026 AVDD AVSS INVD1LVT_schematic
MM5 net15 CKC net27 AVSS lvtnfet_dnw l=LB w=WQ m=2
MM4 net19 CKC net28 AVSS lvtnfet_dnw l=LB w=WQ m=2
MM3 net27 net19 net29 AVSS lvtnfet_dnw l=LC w=WQ m=1
MM2 net28 net15 net017 AVSS lvtnfet_dnw l=LC w=WQ m=1
MM1 net29 VCN AVSS AVSS lvtnfet_dnw l=LD w=WQ m=2
MM0 net017 VCP AVSS AVSS lvtnfet_dnw l=LD w=WQ m=2
XI11 N<1> net042 AVDD AVSS INVD0HVT
XI10 N<2> net043 AVDD AVSS INVD0HVT
XI9 N<3> net041 AVDD AVSS INVD0HVT
XI8 N<4> net040 AVDD AVSS INVD0HVT
XI7 P<1> net036 AVDD AVSS INVD0HVT
XI6 P<2> net037 AVDD AVSS INVD0HVT
XI4 P<4> net027 AVDD AVSS INVD0HVT
XI5 P<3> net038 AVDD AVSS INVD0HVT
.ENDS

************************************************************************
* Library Name: monkey2
* Cell Name:    PINVD0YVT
* View Name:    schematic
************************************************************************

.SUBCKT PINVD0YVT I P VDD VSS ZN
*.PININFO I:I P:I ZN:O VDD:B VSS:B
MM4 ZN I net11 VSS nch_hvt l=LA w=WC m=1
MM1 net11 P VSS VSS nch_hvt l=LA w=WC m=1
MM3 net09 VSS VDD VDD pch_hvt l=LA w=WI m=1
MM0 ZN I net09 VDD pch_hvt l=LA w=WI m=1
.ENDS

************************************************************************
* Library Name: monkey2
* Cell Name:    INVD0HVT_schematic
* View Name:    schematic
************************************************************************

.SUBCKT INVD0HVT_schematic I ZN VDD VSS
*.PININFO I:I ZN:O VDD:B VSS:B
MMU1-M_u2 ZN I VSS VSS nch_hvt l=LA w=WC m=1
MMU1-M_u3 ZN I VDD VDD pch_hvt l=LA w=WI m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    ND2D3LVT
* View Name:    schematic
************************************************************************

.SUBCKT ND2D3LVT A1 A2 ZN VDD VSS
*.PININFO A1:I A2:I ZN:O VDD:B VSS:B
MMU3_0-M_u4 net21 A2 VSS VSS lvtnfet l=LA w=WP m=1
MMU3_1-M_u3 ZN A1 net20 VSS lvtnfet l=LA w=WP m=1
MMU3_2-M_u4 net13 A2 VSS VSS lvtnfet l=LA w=WP m=1
MMU3_1-M_u4 net20 A2 VSS VSS lvtnfet l=LA w=WP m=1
MMU3_0-M_u3 ZN A1 net21 VSS lvtnfet l=LA w=WP m=1
MMU3_2-M_u3 ZN A1 net13 VSS lvtnfet l=LA w=WP m=1
MMU3_2-M_u1 ZN A1 VDD VDD lvtpfet l=LA w=WV m=1
MMU3_1-M_u1 ZN A1 VDD VDD lvtpfet l=LA w=WV m=1
MMU3_1-M_u2 ZN A2 VDD VDD lvtpfet l=LA w=WV m=1
MMU3_2-M_u2 ZN A2 VDD VDD lvtpfet l=LA w=WV m=1
MMU3_0-M_u2 ZN A2 VDD VDD lvtpfet l=LA w=WV m=1
MMU3_0-M_u1 ZN A1 VDD VDD lvtpfet l=LA w=WV m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    NR3D1LVT
* View Name:    schematic
************************************************************************

.SUBCKT NR3D1LVT A1 A2 A3 ZN VDD VSS
*.PININFO A1:I A2:I A3:I ZN:O VDD:B VSS:B
MMI1_1 ZN A1 net5 VDD lvtpfet l=LA w=WV m=1
MM_u1_0 net17 A3 VDD VDD lvtpfet l=LA w=WV m=1
MMI1_0 ZN A1 net9 VDD lvtpfet l=LA w=WV m=1
MMI0_0 net9 A2 net17 VDD lvtpfet l=LA w=WV m=1
MMI0_1 net5 A2 net1 VDD lvtpfet l=LA w=WV m=1
MM_u1_1 net1 A3 VDD VDD lvtpfet l=LA w=WV m=1
MMI3 ZN A1 VSS VSS lvtnfet l=LA w=WP m=1
MMI2 ZN A2 VSS VSS lvtnfet l=LA w=WP m=1
MM_u4 ZN A3 VSS VSS lvtnfet l=LA w=WP m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    INVD2LVT_schematic
* View Name:    schematic
************************************************************************

.SUBCKT INVD2LVT_schematic I ZN VDD VSS
*.PININFO I:I ZN:O VDD:B VSS:B
MMU1_0-M_u2 ZN I VSS VSS lvtnfet l=LA w=WP m=1
MMU1_1-M_u2 ZN I VSS VSS lvtnfet l=LA w=WP m=1
MMU1_0-M_u3 ZN I VDD VDD lvtpfet l=LA w=WV m=1
MMU1_1-M_u3 ZN I VDD VDD lvtpfet l=LA w=WV m=1
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    Coarse_Comp_CK
* View Name:    schematic
************************************************************************

.SUBCKT Coarse_Comp_CK CKC CKSBT DVDD DVSS OUTNC OUTPC ST_FINE VALIDC VCTIN
*.PININFO VCTIN:I CKC:B CKSBT:B DVDD:B DVSS:B OUTNC:B OUTPC:B ST_FINE:B
*.PININFO VALIDC:B
XI67 net07 VCTIN DVDD DVSS net09 PINVD0YVT
XI46 net30 VCTIN DVDD DVSS net29 PINVD0YVT
XI21 net33 VCTIN DVDD DVSS net32 PINVD0YVT
XI12 net34 VCTIN DVDD DVSS net33 PINVD0YVT
XI47 net31 VCTIN DVDD DVSS net30 PINVD0YVT
XI0 net29 net07 DVDD DVSS INVD0HVT_schematic
XI22 net32 net31 DVDD DVSS INVD0HVT_schematic
XI3 OUTNC OUTPC VALIDC DVDD DVSS ND2D3LVT
XI218 VALIDC ST_FINE CKSBT net34 DVDD DVSS NR3D1LVT
XI65 net09 CKC DVDD DVSS INVD2LVT_schematic
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    INVD3LVT
* View Name:    schematic
************************************************************************

.SUBCKT INVD3LVT I ZN VDD VSS
*.PININFO I:I ZN:O VDD:B VSS:B
MMU1_0-M_u2 ZN I VSS VSS lvtnfet l=LA w=WP m=1
MMU1_1-M_u2 ZN I VSS VSS lvtnfet l=LA w=WP m=1
MMU1_2-M_u2 ZN I VSS VSS lvtnfet l=LA w=WP m=1
MMU1_0-M_u3 ZN I VDD VDD lvtpfet l=LA w=WV m=1
MMU1_1-M_u3 ZN I VDD VDD lvtpfet l=LA w=WV m=1
MMU1_2-M_u3 ZN I VDD VDD lvtpfet l=LA w=WV m=1
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    BTSW
* View Name:    schematic
************************************************************************

.SUBCKT BTSW AVDD AVSS CKSBT CKSBTB VBTSW VIN
*.PININFO CKSBT:I CKSBTB:I VIN:I AVDD:B AVSS:B VBTSW:B
MM9 VBTSW net7 net12 net12 pch l=LA w=WQ m=1
MM8 AVDD VBTSW net12 net12 pch l=LA w=WQ m=1
MM7 net7 CKSBT AVDD AVDD pch l=LA w=WQ m=1
MM10 net013 net12 net013 AVSS nch l=LE w=WAB m=4
MM6 net27 CKSBTB AVSS AVSS nch l=LA w=WK m=1
MM5 VBTSW AVDD net27 AVSS nch l=LA w=WK m=1
MM3 VIN VBTSW net013 AVSS nch l=LA w=WK m=1
MM2 net7 VBTSW net013 AVSS nch l=LA w=WK m=1
MM1 net013 CKSBTB AVSS AVSS nch l=LA w=WK m=1
MM0 net7 CKSBT net013 AVSS nch l=LA w=WK m=1
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    5b_ADC
* View Name:    schematic
************************************************************************

.SUBCKT 5b_ADC AVDD AVSS CKS CKSB CKSBT CKSBTB CPY DF<11> DF<10> DF<9> DF<8>
+ DF<7> DFB<11> DFB<10> DFB<9> DFB<8> DFB<7> DVDD DVSS N<1> N<2> N<3> N<4>
+ P<1> P<2> P<3> P<4> ST_FINE VCM VCTIN VIN VIP VRCTL VRNX VRPX
*.PININFO CKS:I CKSB:I CKSBT:I CKSBTB:I N<1>:I N<2>:I N<3>:I N<4>:I P<1>:I
*.PININFO P<2>:I P<3>:I P<4>:I VCTIN:I VIN:I VIP:I VRCTL:I DF<11>:O DF<10>:O
*.PININFO DF<9>:O DF<8>:O DF<7>:O DFB<11>:O DFB<10>:O DFB<9>:O DFB<8>:O
*.PININFO DFB<7>:O AVDD:B AVSS:B CPY:B DVDD:B DVSS:B ST_FINE:B VCM:B VRNX:B
*.PININFO VRPX:B
XI4 net013<0> net013<1> net013<2> net013<3> net013<4> CK<11> CK<10> CK<9>
+ CK<8> CKS CKSB CKSBTI CKSBTIB DB<11> DB<10> DB<9> DB<8> DVDD DVSS SWC<11>
+ SWC<10> SWC<9> SWC<8> SWCB<11> SWCB<10> SWCB<9> SWCB<8> TGC<11> TGC<10>
+ TGC<9> TGC<8> TGCB<11> TGCB<10> TGCB<9> TGCB<8> VBTP VCM VCN VIP VRCTL
+ VRN<11> VRN<10> VRN<9> VRN<8> VRNX VRP<11> VRP<10> VRP<9> VRP<8> VRPX
+ CDAC_SW_Coarse
XI0 net014<0> net014<1> net014<2> net014<3> net014<4> CK<11> CK<10> CK<9>
+ CK<8> CKS CKSB CKSBTI CKSBTIB D<11> D<10> D<9> D<8> DVDD DVSS SWC<11>
+ SWC<10> SWC<9> SWC<8> SWCB<11> SWCB<10> SWCB<9> SWCB<8> TGC<11> TGC<10>
+ TGC<9> TGC<8> TGCB<11> TGCB<10> TGCB<9> TGCB<8> VBTN VCM VCP VIN VRCTL
+ VRN<11> VRN<10> VRN<9> VRN<8> VRNX VRP<11> VRP<10> VRP<9> VRP<8> VRPX
+ CDAC_SW_Coarse
XI1 CK<11> CK<10> CK<9> CK<8> CKSBTI CKSBTIB CPY D<11> D<10> D<9> D<8> DB<11>
+ DB<10> DB<9> DB<8> DF<11> DF<10> DF<9> DF<8> DF<7> DFB<11> DFB<10> DFB<9>
+ DFB<8> DFB<7> DVDD DVSS OUTNC OUTPC ST_FINE SWC<11> SWC<10> SWC<9> SWC<8>
+ SWCB<11> SWCB<10> SWCB<9> SWCB<8> TGC<11> TGC<10> TGC<9> TGC<8> TGCB<11>
+ TGCB<10> TGCB<9> TGCB<8> VALIDC Coarse_SAR_Logic
XI2 AVDD AVSS CKC N<1> N<2> N<3> N<4> OUTNC OUTPC P<1> P<2> P<3> P<4> VCN VCP
+ Comp_Coarse_V3_Cali
XI5 CKC CKSBTI DVDD DVSS OUTNC OUTPC ST_FINE VALIDC VCTIN Coarse_Comp_CK
XI16 CKSBTB net68 DVDD DVSS INVD1LVT
XI17 CKSBT net69 DVDD DVSS INVD1LVT
XI15 net68 CKSBTIB DVDD DVSS INVD3LVT
XI18 net69 CKSBTI DVDD DVSS INVD3LVT
XI6 AVDD AVSS CKSBT CKSBTB VBTN VIN BTSW
XI12 AVDD AVSS CKSBT CKSBTB VBTP VIP BTSW
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    SW_Cres_v3_1_np_v2
* View Name:    schematic
************************************************************************

.SUBCKT SW_Cres_v3_1_np_v2 CK DVDD DVSS VRCTL VRN VRNX VRP VRPX
*.PININFO VRCTL:I CK:B DVDD:B DVSS:B VRN:B VRNX:B VRP:B VRPX:B
MM7 VRN CLK VRN DVSS nch l=LA w=WJ m=1
MM2 VRN net05 VRNX DVSS nch l=LA w=WQ m=3
MM1 VRP CLK VRPX DVDD pch l=LA w=WQ m=3
MM8 VRP net013 VRP DVDD pch l=LA w=WJ m=1
XI5 CLK net013 DVDD DVSS INVD1LVT
XI6 net05 CLK DVDD DVSS INVD1LVT
XI11 CK VRCTL net05 DVDD DVSS ND2D1LVT
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    INVD8LVT
* View Name:    schematic
************************************************************************

.SUBCKT INVD8LVT I ZN VDD VSS
*.PININFO I:I ZN:O VDD:B VSS:B
MMU1_5-M_u2 ZN I VSS VSS lvtnfet l=LA w=WP m=1
MMU1_0-M_u2 ZN I VSS VSS lvtnfet l=LA w=WP m=1
MMU1_3-M_u2 ZN I VSS VSS lvtnfet l=LA w=WP m=1
MMU1_7-M_u2 ZN I VSS VSS lvtnfet l=LA w=WP m=1
MMU1_4-M_u2 ZN I VSS VSS lvtnfet l=LA w=WP m=1
MMU1_1-M_u2 ZN I VSS VSS lvtnfet l=LA w=WP m=1
MMU1_6-M_u2 ZN I VSS VSS lvtnfet l=LA w=WP m=1
MMU1_2-M_u2 ZN I VSS VSS lvtnfet l=LA w=WP m=1
MMU1_0-M_u3 ZN I VDD VDD lvtpfet l=LA w=WV m=1
MMU1_4-M_u3 ZN I VDD VDD lvtpfet l=LA w=WV m=1
MMU1_5-M_u3 ZN I VDD VDD lvtpfet l=LA w=WV m=1
MMU1_1-M_u3 ZN I VDD VDD lvtpfet l=LA w=WV m=1
MMU1_3-M_u3 ZN I VDD VDD lvtpfet l=LA w=WV m=1
MMU1_7-M_u3 ZN I VDD VDD lvtpfet l=LA w=WV m=1
MMU1_6-M_u3 ZN I VDD VDD lvtpfet l=LA w=WV m=1
MMU1_2-M_u3 ZN I VDD VDD lvtpfet l=LA w=WV m=1
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    SW5_V2
* View Name:    schematic
************************************************************************

.SUBCKT SW5_V2 D DVDD DVSS SW SWB TG TGB VBTSW VCM VIN VO VREFN VREFP
*.PININFO D:I SW:I SWB:I TG:I TGB:I VCM:I VIN:I VREFN:I VREFP:I VO:O DVDD:B
*.PININFO DVSS:B VBTSW:B
MM6 VO VBTSW VIN DVSS nch_dnw l=LA w=WB m=1
MM5 VO TG VCM DVSS nch_dnw l=LA w=WU m=1
MM4 net22 D VREFN DVSS nch_dnw l=LA w=WP m=8
MM3 VO SW net22 DVSS nch_dnw l=LA w=WP m=8
MM2 VO TGB VCM DVDD pch l=LA w=WU m=1
MM1 VO SWB net23 DVDD pch l=LA w=WV m=8
MM0 net23 D VREFP DVDD pch l=LA w=WV m=8
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    SW6_V3
* View Name:    schematic
************************************************************************

.SUBCKT SW6_V3 D DVDD DVSS SW SWB TG TGB VCM VO VREFN VREFP
*.PININFO D:I SW:I SWB:I TG:I TGB:I VCM:I VREFN:I VREFP:I VO:O DVDD:B DVSS:B
MM5 VO TG VCM DVSS nch_dnw l=LA w=WU m=2
MM4 net22 D VREFN DVSS nch_dnw l=LA w=WY m=8
MM3 VO SW net22 DVSS nch_dnw l=LA w=WY m=8
MM2 VO TGB VCM DVDD pch l=LA w=WU m=2
MM1 VO SWB net23 DVDD pch l=LA w=WAA m=8
MM0 net23 D VREFP DVDD pch l=LA w=WAA m=8
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    BTSW_256
* View Name:    schematic
************************************************************************

.SUBCKT BTSW_256 DVSS VBTSW VIN VO
*.PININFO VIN:I VO:O DVSS:B VBTSW:B
MM0 VO VBTSW VIN DVSS nch_dnw l=LA w=WK m=2
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    SW_Cres_v3_1_np_v3
* View Name:    schematic
************************************************************************

.SUBCKT SW_Cres_v3_1_np_v3 CK DVDD DVSS VRCTL VRN VRNX VRP VRPX
*.PININFO VRCTL:I CK:B DVDD:B DVSS:B VRN:B VRNX:B VRP:B VRPX:B
MM7 VRN CLK VRN DVSS nch l=LA w=WJ m=1
MM2 VRN net05 VRNX DVSS nch l=LA w=WQ m=3
MM1 VRP CLK VRPX DVDD pch l=LA w=WQ m=3
MM8 VRP net013 VRP DVDD pch l=LA w=WJ m=1
XI5 CLK net013 DVDD DVSS INVD1LVT
XI6 net05 CLK DVDD DVSS INVD1LVT
XI11 CK VRCTL net05 DVDD DVSS ND2D1LVT
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    BTSW_MSB
* View Name:    schematic
************************************************************************

.SUBCKT BTSW_MSB DVSS VBTSW VIN VO
*.PININFO VIN:I VO:O DVSS:B VBTSW:B
MM0 VO VBTSW VIN DVSS nch_dnw l=LA w=WK m=3
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    BTSW_128
* View Name:    schematic
************************************************************************

.SUBCKT BTSW_128 DVSS VBTSW VIN VO
*.PININFO VIN:I VO:O DVSS:B VBTSW:B
MM0 VO VBTSW VIN DVSS nch_dnw l=LA w=WK m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    INVD4LVT
* View Name:    schematic
************************************************************************

.SUBCKT INVD4LVT I ZN VDD VSS
*.PININFO I:I ZN:O VDD:B VSS:B
MMU1_0-M_u2 ZN I VSS VSS lvtnfet l=LA w=WP m=1
MMU1_3-M_u2 ZN I VSS VSS lvtnfet l=LA w=WP m=1
MMU1_1-M_u2 ZN I VSS VSS lvtnfet l=LA w=WP m=1
MMU1_2-M_u2 ZN I VSS VSS lvtnfet l=LA w=WP m=1
MMU1_0-M_u3 ZN I VDD VDD lvtpfet l=LA w=WV m=1
MMU1_1-M_u3 ZN I VDD VDD lvtpfet l=LA w=WV m=1
MMU1_3-M_u3 ZN I VDD VDD lvtpfet l=LA w=WV m=1
MMU1_2-M_u3 ZN I VDD VDD lvtpfet l=LA w=WV m=1
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    TG_Top_Fine_v3
* View Name:    schematic
************************************************************************

.SUBCKT TG_Top_Fine_v3 CKS CKSB DVDD DVSS VCM VO
*.PININFO CKS:I CKSB:I VCM:I VO:O DVDD:B DVSS:B
MM2 VO CKSB VCM DVDD lvtpfet l=LA w=WZ m=16
MM5 VO CKS VCM DVSS lvtnfet_dnw l=LA w=WZ m=16
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    CDAC_SW_Fine_P
* View Name:    schematic
************************************************************************

.SUBCKT CDAC_SW_Fine_P C6R C<6> C<5> C<4> C<3> C<2> C<1> C<0> CK<7> CK<6>
+ CK<5> CK<4> CK<3> CK<2> CKS CKSB CL<10> CL<9> CL<8> CL<7> CPYB CR<10> CR<9>
+ CR<8> CR<7> D<7> D<6> D<5> D<4> D<3> D<2> D<1> DVDD DVSS D_F<11> D_F<10>
+ D_F<9> D_F<8> D_F<7> SW<12> SW<11> SW<10> SW<9> SW<8> SW<7> SW<6> SW<5>
+ SW<4> SW<3> SW<2> SW<1> SWB<12> SWB<11> SWB<10> SWB<9> SWB<8> SWB<7> SWB<6>
+ SWB<5> SWB<4> SWB<3> SWB<2> SWB<1> TG<12> TG<11> TG<10> TG<9> TG<8> TG<7>
+ TG<6> TG<5> TG<4> TG<3> TG<2> TG<1> TGB<12> TGB<11> TGB<10> TGB<9> TGB<8>
+ TGB<7> TGB<6> TGB<5> TGB<4> TGB<3> TGB<2> TGB<1> VBTFN VCM VFP VIN VRCTL
+ VRN<7> VRN<6> VRN<5> VRN<4> VRN<3> VRN<2> VRNCPY VRNX VRP<7> VRP<6> VRP<5>
+ VRP<4> VRP<3> VRP<2> VRPCPY VRPX
*.PININFO CKS:I CKSB:I CPYB:I VRCTL:I VRNX:I VRPX:I C6R:B C<6>:B C<5>:B C<4>:B
*.PININFO C<3>:B C<2>:B C<1>:B C<0>:B CK<7>:B CK<6>:B CK<5>:B CK<4>:B CK<3>:B
*.PININFO CK<2>:B CL<10>:B CL<9>:B CL<8>:B CL<7>:B CR<10>:B CR<9>:B CR<8>:B
*.PININFO CR<7>:B D<7>:B D<6>:B D<5>:B D<4>:B D<3>:B D<2>:B D<1>:B DVDD:B
*.PININFO DVSS:B D_F<11>:B D_F<10>:B D_F<9>:B D_F<8>:B D_F<7>:B SW<12>:B
*.PININFO SW<11>:B SW<10>:B SW<9>:B SW<8>:B SW<7>:B SW<6>:B SW<5>:B SW<4>:B
*.PININFO SW<3>:B SW<2>:B SW<1>:B SWB<12>:B SWB<11>:B SWB<10>:B SWB<9>:B
*.PININFO SWB<8>:B SWB<7>:B SWB<6>:B SWB<5>:B SWB<4>:B SWB<3>:B SWB<2>:B
*.PININFO SWB<1>:B TG<12>:B TG<11>:B TG<10>:B TG<9>:B TG<8>:B TG<7>:B TG<6>:B
*.PININFO TG<5>:B TG<4>:B TG<3>:B TG<2>:B TG<1>:B TGB<12>:B TGB<11>:B
*.PININFO TGB<10>:B TGB<9>:B TGB<8>:B TGB<7>:B TGB<6>:B TGB<5>:B TGB<4>:B
*.PININFO TGB<3>:B TGB<2>:B TGB<1>:B VBTFN:B VCM:B VFP:B VIN:B VRN<7>:B
*.PININFO VRN<6>:B VRN<5>:B VRN<4>:B VRN<3>:B VRN<2>:B VRNCPY:B VRP<7>:B
*.PININFO VRP<6>:B VRP<5>:B VRP<4>:B VRP<3>:B VRP<2>:B VRPCPY:B
XI114 D_F<9> net0215 DVDD DVSS INVD3LVT
XI63 D_F<9> net0222 DVDD DVSS INVD3LVT
XI62 SW<11> net0234 DVDD DVSS INVD3LVT
XI60 SWB<11> net0233 DVDD DVSS INVD3LVT
XI44 TG<12> net0178 DVDD DVSS INVD3LVT
XI43 TGB<12> net0177 DVDD DVSS INVD3LVT
XI42 SWB<12> net0223 DVDD DVSS INVD3LVT
XI39 SW<12> net0224 DVDD DVSS INVD3LVT
XI38 D_F<10> net0225 DVDD DVSS INVD3LVT
XI36 CPYD net52 DVDD DVSS INVD3LVT
XI32 CPYD net53 DVDD DVSS INVD3LVT
XI104 SW<11> net0217 DVDD DVSS INVD3LVT
XI94 SWB<12> net0228 DVDD DVSS INVD3LVT
XI101 SW<12> net0227 DVDD DVSS INVD3LVT
XI97 SWB<11> net0226 DVDD DVSS INVD3LVT
XI87 TGB<12> net0172 DVDD DVSS INVD3LVT
XI84 TG<12> net0173 DVDD DVSS INVD3LVT
XI107 D_F<10> net0212 DVDD DVSS INVD3LVT
XCrM<0> net43 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v2
XCrM<1> net43 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v2
XCrM<2> net43 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v2
XCrM<3> net43 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v2
XCrM<4> net43 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v2
XCrM<5> net43 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v2
XCrM<6> net43 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v2
XCrM<7> net43 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v2
XCrM<8> net43 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v2
XCrM<9> net43 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v2
XCrM<10> net43 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v2
XCrM<11> net43 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v2
XCrM<12> net43 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v2
XCrM<13> net43 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v2
XCrM<14> net43 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v2
XCrM<15> net43 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v2
XCrM<16> net43 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v2
XCrM<17> net43 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v2
XCrM<18> net43 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v2
XCrM<19> net43 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v2
XCrM<20> net43 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v2
XCrM<21> net43 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v2
XCrM<22> net43 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v2
XCrM<23> net43 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v2
XCrM<24> net43 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v2
XCrM<25> net43 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v2
XCrM<26> net43 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v2
XCrM<27> net43 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v2
XCrM<28> net43 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v2
XCrM<29> net43 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v2
XCrM<30> net43 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v2
XCrM<31> net43 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v2
XCrM<32> net43 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v2
XCrM<33> net43 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v2
XI25 CK<7> DVDD DVSS VRCTL VRN<7> VRNX VRP<7> VRPX SW_Cres_v3_1_np_v2
XI137 CK<6> DVDD DVSS VRCTL VRN<6> VRNX VRP<6> VRPX SW_Cres_v3_1_np_v2
XI139 CK<5> DVDD DVSS VRCTL VRN<5> VRNX VRP<5> VRPX SW_Cres_v3_1_np_v2
XI140 CK<4> DVDD DVSS VRCTL VRN<4> VRNX VRP<4> VRPX SW_Cres_v3_1_np_v2
XI141 CK<3> DVDD DVSS VRCTL VRN<3> VRNX VRP<3> VRPX SW_Cres_v3_1_np_v2
XI142 CK<2> DVDD DVSS VRCTL VRN<2> VRNX VRP<2> VRPX SW_Cres_v3_1_np_v2
XI123 CPYB CPYD DVDD DVSS INVD2LVT_schematic
XI122 net0191 net0156 DVDD DVSS INVD2LVT_schematic
XI120 SWB<7> net0157 DVDD DVSS INVD2LVT_schematic
XI119 SW<7> net0155 DVDD DVSS INVD2LVT_schematic
XI78 net0229 net0206 DVDD DVSS INVD2LVT_schematic
XI77 SW<9> net0205 DVDD DVSS INVD2LVT_schematic
XI76 SWB<9> net0211 DVDD DVSS INVD2LVT_schematic
XI58 TGB<11> net0189 DVDD DVSS INVD2LVT_schematic
XI57 TG<11> net0190 DVDD DVSS INVD2LVT_schematic
XI106 SWB<9> net0209 DVDD DVSS INVD2LVT_schematic
XI99 SW<9> net0203 DVDD DVSS INVD2LVT_schematic
XI109 net0216 net0204 DVDD DVSS INVD2LVT_schematic
XI86 TG<11> net0185 DVDD DVSS INVD2LVT_schematic
XI83 SW<8> net0207 DVDD DVSS INVD2LVT_schematic
XI82 SWB<8> net0210 DVDD DVSS INVD2LVT_schematic
XI80 net0218 net0208 DVDD DVSS INVD2LVT_schematic
XI89 TGB<11> net0184 DVDD DVSS INVD2LVT_schematic
XI9 D<5> DVDD DVSS SW<5> SWB<5> TG<5> TGB<5> VBTFN VCM VIN C<4> VRN<5> VRP<5>
+ SW3_V2
XI10 D<6> DVDD DVSS SW<6> SWB<6> TG<6> TGB<6> VBTFN VCM VIN C<5> VRN<6> VRP<6>
+ SW4_V2
XI1 D<2> DVDD DVSS SW<2> SWB<2> TG<2> TGB<2> VBTFN VCM VIN C<1> VRN<2> VRP<2>
+ SW1_V2
XI2 D<1> DVDD DVSS SW<1> SWB<1> TG<1> TGB<1> VBTFN VCM VIN C<0> VRNX VRPX
+ SW1_V2
XI7 D<3> DVDD DVSS SW<3> SWB<3> TG<3> TGB<3> VBTFN VCM VIN C<2> VRN<3> VRP<3>
+ SW1_V2
XI113 net0215 net0182 DVDD DVSS INVD8LVT
XI64 net0222 net0187 DVDD DVSS INVD8LVT
XI61 net0234 net0186 DVDD DVSS INVD8LVT
XI59 net0233 net0188 DVDD DVSS INVD8LVT
XI41 net0223 net0176 DVDD DVSS INVD8LVT
XI40 net0224 net0174 DVDD DVSS INVD8LVT
XI37 net0225 net0175 DVDD DVSS INVD8LVT
XI34 net52 net42 DVDD DVSS INVD8LVT
XI31 net53 net43 DVDD DVSS INVD8LVT
XI108 net0212 net0170 DVDD DVSS INVD8LVT
XI105 net0217 net0181 DVDD DVSS INVD8LVT
XI98 net0226 net0183 DVDD DVSS INVD8LVT
XI100 net0227 net0169 DVDD DVSS INVD8LVT
XI93 net0228 net0171 DVDD DVSS INVD8LVT
XI118 net0204 DVDD DVSS net0209 net0203 TG<9> TGB<9> VBTFN VCM VIN CR<7>
+ VRNCPY VRPCPY SW5_V2
XI75 net0206 DVDD DVSS net0211 net0205 TG<9> TGB<9> VBTFN VCM VIN CL<7> VRNCPY
+ VRPCPY SW5_V2
XI30 net0208 DVDD DVSS net0210 net0207 TG<8> TGB<8> VBTFN VCM VIN C<6> VRNCPY
+ VRPCPY SW5_V2
XI3 net0156 DVDD DVSS net0157 net0155 TG<7> TGB<7> VBTFN VCM VIN C6R VRN<7>
+ VRP<7> SW5_V2
XCrC<0> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<2> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<3> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<4> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<5> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<6> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<7> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<8> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<9> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<10> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<11> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<12> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<13> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<14> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<15> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<16> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<17> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<18> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<19> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<20> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<21> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<22> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<23> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<24> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<25> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<26> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<27> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<28> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<29> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<30> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<31> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<32> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<33> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<34> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<35> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<36> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<37> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<38> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<39> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<40> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<41> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<42> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<43> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<44> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<45> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<46> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<47> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<48> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<49> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<50> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<51> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<52> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<53> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<54> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<55> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<56> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<57> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<58> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<59> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<60> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<61> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<62> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<63> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<64> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<65> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<66> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<67> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<68> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<69> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<70> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<71> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<72> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<73> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<74> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<75> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<76> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<77> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<78> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<79> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<80> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<81> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<82> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<83> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<84> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<85> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<86> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<87> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<88> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<89> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<90> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<91> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<92> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<93> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<94> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<95> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<96> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<97> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<98> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<99> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<100> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<101> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<102> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<103> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<104> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<105> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<106> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<107> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<108> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<109> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<110> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<111> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<112> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<113> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<114> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<115> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<116> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<117> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<118> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<119> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<120> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<121> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<122> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<123> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<124> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<125> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<126> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<127> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<128> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<129> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<130> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<131> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<132> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<133> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<134> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<135> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<136> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<137> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<138> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<139> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<140> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<141> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<142> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<143> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<144> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<145> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<146> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<147> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<148> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<149> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<150> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<151> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<152> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<153> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<154> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<155> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<156> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<157> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<158> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<159> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<160> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<161> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<162> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<163> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<164> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<165> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<166> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<167> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<168> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<169> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<170> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<171> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<172> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<173> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<174> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<175> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<176> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<177> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<178> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<179> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<180> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<181> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<182> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<183> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<184> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<185> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<186> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<187> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<188> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<189> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<190> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<191> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<192> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<193> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<194> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<195> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<196> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<197> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<198> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<199> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<200> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<201> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<202> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<203> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<204> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<205> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<206> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<207> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<208> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<209> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<210> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<211> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<212> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<213> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<214> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<215> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<216> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<217> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<218> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<219> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<220> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<221> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<222> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<223> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<224> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<225> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<226> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<227> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<228> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<229> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<230> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<231> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<232> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<233> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<234> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<235> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<236> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<237> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<238> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<239> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<240> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<241> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<242> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<243> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<244> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<245> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<246> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<247> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<248> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<249> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<250> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<251> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<252> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<253> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<254> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<255> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<256> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<257> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<258> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<259> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<260> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<261> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<262> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<263> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<264> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<265> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<266> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<267> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<268> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<269> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<270> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<271> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<272> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<273> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<274> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<275> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<276> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<277> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<278> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<279> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<280> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<281> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<282> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<283> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<284> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<285> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<286> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<287> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<288> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<289> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<290> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<291> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<292> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<293> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<294> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<295> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<296> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<297> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<298> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<299> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<300> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<301> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<302> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<303> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<304> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<305> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<306> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<307> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<308> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<309> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<310> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<311> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<312> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<313> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<314> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<315> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<316> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<317> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<318> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<319> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<320> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<321> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<322> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<323> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<324> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<325> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<326> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<327> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<328> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<329> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<330> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<331> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<332> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<333> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<334> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<335> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<336> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<337> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<338> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<339> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<340> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<341> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<342> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<343> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<344> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<345> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<346> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<347> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<348> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<349> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<350> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<351> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<352> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<353> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<354> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<355> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<356> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<357> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<358> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<359> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<360> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<361> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<362> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<363> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<364> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<365> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<366> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<367> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<368> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<369> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<370> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<371> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<372> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<373> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<374> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<375> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<376> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<377> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<378> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<379> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<380> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<381> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<382> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<383> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<384> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<385> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<386> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<387> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<388> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<389> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<390> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<391> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<392> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<393> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<394> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<395> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<396> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<397> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<398> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<399> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<400> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<401> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<402> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<403> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<404> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<405> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<406> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<407> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<408> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<409> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<410> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<411> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<412> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<413> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<414> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<415> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<416> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<417> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<418> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<419> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<420> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<421> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<422> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<423> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<424> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<425> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<426> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<427> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<428> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<429> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<430> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<431> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<432> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<433> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<434> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<435> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<436> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<437> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<438> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<439> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<440> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<441> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<442> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<443> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<444> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<445> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<446> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<447> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<448> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<449> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<450> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<451> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<452> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<453> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<454> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<455> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<456> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<457> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<458> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<459> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<460> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<461> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<462> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<463> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<464> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<465> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<466> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<467> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<468> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<469> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<470> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<471> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<472> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<473> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<474> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<475> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<476> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<477> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<478> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<479> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<480> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<481> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<482> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<483> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<484> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<485> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<486> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<487> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<488> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<489> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<490> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<491> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<492> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<493> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<494> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<495> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<496> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<497> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<498> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<499> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<500> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<501> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<502> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<503> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<504> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<505> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<506> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<507> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<508> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<509> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<510> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<511> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<512> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<513> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<514> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<515> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<516> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<517> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<518> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<519> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<520> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<521> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<522> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<523> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<524> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<525> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<526> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<527> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<528> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<529> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<530> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<531> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<532> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<533> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<534> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<535> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<536> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<537> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<538> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<539> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<540> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<541> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<542> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<543> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<544> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<545> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<546> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<547> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<548> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<549> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<550> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<551> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<552> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<553> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<554> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<555> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<556> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<557> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<558> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<559> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<560> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<561> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<562> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<563> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<564> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<565> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<566> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<567> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<568> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<569> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<570> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<571> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<572> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<573> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<574> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<575> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<576> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<577> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<578> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<579> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<580> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<581> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<582> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<583> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<584> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<585> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<586> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<587> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<588> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<589> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<590> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<591> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<592> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<593> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<594> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<595> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<596> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<597> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<598> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<599> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<600> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<601> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<602> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<603> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<604> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<605> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<606> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<607> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<608> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<609> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<610> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<611> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<612> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<613> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<614> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<615> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<616> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<617> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<618> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<619> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<620> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<621> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<622> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<623> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<624> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<625> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<626> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<627> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<628> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<629> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<630> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<631> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<632> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<633> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<634> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<635> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<636> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<637> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<638> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<639> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<640> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<641> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<642> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<643> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<644> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<645> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<646> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<647> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<648> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<649> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<650> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<651> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<652> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<653> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<654> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<655> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<656> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<657> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<658> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<659> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<660> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<661> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<662> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<663> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<664> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<665> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<666> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<667> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<668> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<669> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<670> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<671> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<672> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<673> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<674> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<675> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<676> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<677> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<678> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<679> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<680> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<681> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<682> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<683> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<684> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<685> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<686> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<687> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<688> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<689> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<690> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<691> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<692> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<693> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<694> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<695> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<696> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<697> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<698> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<699> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<700> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<701> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<702> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<703> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<704> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<705> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<706> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<707> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<708> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<709> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<710> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<711> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<712> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<713> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<714> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<715> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<716> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<717> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<718> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<719> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<720> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<721> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<722> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<723> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<724> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<725> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<726> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<727> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<728> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<729> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<730> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<731> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<732> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<733> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<734> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<735> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<736> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<737> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<738> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<739> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<740> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<741> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<742> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<743> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<744> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<745> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<746> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<747> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<748> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<749> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<750> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<751> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<752> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<753> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<754> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<755> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<756> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<757> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<758> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<759> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<760> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<761> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<762> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<763> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<764> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<765> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<766> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<767> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<768> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<769> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<770> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<771> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<772> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<773> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<774> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<775> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<776> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<777> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<778> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<779> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<780> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<781> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<782> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<783> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<784> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<785> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<786> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<787> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<788> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<789> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<790> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<791> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<792> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<793> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<794> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<795> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<796> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<797> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<798> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<799> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<800> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<801> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<802> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<803> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<804> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<805> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<806> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<807> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<808> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<809> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<810> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<811> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<812> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<813> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<814> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<815> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<816> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<817> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<818> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<819> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<820> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<821> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<822> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<823> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<824> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<825> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<826> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<827> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<828> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<829> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<830> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<831> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<832> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<833> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<834> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<835> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<836> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<837> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<838> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<839> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<840> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<841> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<842> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<843> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<844> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<845> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<846> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<847> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<848> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<849> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<850> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<851> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<852> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<853> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<854> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<855> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<856> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<857> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<858> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<859> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<860> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<861> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<862> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<863> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<864> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<865> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<866> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<867> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<868> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<869> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<870> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<871> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<872> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<873> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<874> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<875> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<876> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<877> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<878> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<879> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<880> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<881> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<882> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<883> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<884> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<885> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<886> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<887> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<888> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<889> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<890> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<891> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<892> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<893> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<894> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<895> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<896> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<897> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<898> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<899> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<900> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<901> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<902> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<903> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<904> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<905> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<906> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<907> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<908> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<909> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<910> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<911> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<912> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<913> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<914> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<915> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<916> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<917> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<918> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<919> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<920> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<921> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<922> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<923> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<924> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<925> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<926> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<927> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<928> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<929> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<930> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<931> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<932> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<933> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<934> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<935> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<936> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<937> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<938> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<939> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<940> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<941> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<942> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<943> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<944> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<945> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<946> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<947> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<948> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<949> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<950> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<951> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<952> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<953> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<954> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<955> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<956> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<957> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<958> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<959> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<960> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<961> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<962> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<963> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<964> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<965> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<966> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<967> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<968> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<969> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<970> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<971> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<972> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<973> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<974> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<975> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<976> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<977> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<978> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<979> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<980> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<981> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<982> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<983> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<984> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<985> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<986> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<987> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<988> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<989> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<990> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<991> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<992> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<993> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<994> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<995> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<996> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<997> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<998> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<999> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1000> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1001> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1002> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1003> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1004> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1005> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1006> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1007> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1008> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1009> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1010> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1011> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1012> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1013> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1014> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1015> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1016> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1017> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1018> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1019> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1020> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1021> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1022> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1023> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1024> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1025> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1026> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1027> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1028> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1029> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1030> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1031> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1032> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1033> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1034> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1035> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1036> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1037> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1038> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1039> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1040> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1041> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1042> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1043> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1044> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1045> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1046> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1047> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1048> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1049> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1050> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1051> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1052> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1053> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1054> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1055> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1056> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1057> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1058> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1059> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1060> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1061> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1062> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1063> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1064> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1065> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1066> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1067> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1068> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1069> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1070> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1071> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1072> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1073> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1074> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1075> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1076> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1077> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1078> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1079> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1080> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1081> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1082> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1083> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1084> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1085> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1086> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1087> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1088> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1089> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1090> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1091> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1092> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1093> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1094> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1095> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1096> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1097> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1098> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1099> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1100> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1101> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1102> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1103> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1104> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1105> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1106> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1107> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1108> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1109> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1110> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1111> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1112> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1113> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1114> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1115> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1116> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1117> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1118> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1119> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1120> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1121> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1122> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1123> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1124> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1125> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1126> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1127> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1128> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1129> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1130> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1131> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1132> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1133> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1134> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1135> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1136> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1137> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1138> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1139> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1140> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1141> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1142> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1143> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1144> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1145> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1146> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1147> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1148> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1149> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1150> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1151> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1152> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1153> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1154> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1155> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1156> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1157> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1158> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1159> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1160> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1161> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1162> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1163> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1164> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1165> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1166> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1167> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1168> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCrC<1169> VRPCPY VRNCPY nmoscap lr=3u wr=3u m=1
XCr7<0> VRP<7> VRN<7> nmoscap lr=3u wr=3u m=1
XCr7<1> VRP<7> VRN<7> nmoscap lr=3u wr=3u m=1
XCr7<2> VRP<7> VRN<7> nmoscap lr=3u wr=3u m=1
XCr7<3> VRP<7> VRN<7> nmoscap lr=3u wr=3u m=1
XCr7<4> VRP<7> VRN<7> nmoscap lr=3u wr=3u m=1
XCr7<5> VRP<7> VRN<7> nmoscap lr=3u wr=3u m=1
XCr7<6> VRP<7> VRN<7> nmoscap lr=3u wr=3u m=1
XCr7<7> VRP<7> VRN<7> nmoscap lr=3u wr=3u m=1
XCr7<8> VRP<7> VRN<7> nmoscap lr=3u wr=3u m=1
XCr7<9> VRP<7> VRN<7> nmoscap lr=3u wr=3u m=1
XCr7<10> VRP<7> VRN<7> nmoscap lr=3u wr=3u m=1
XCr7<11> VRP<7> VRN<7> nmoscap lr=3u wr=3u m=1
XCr7<12> VRP<7> VRN<7> nmoscap lr=3u wr=3u m=1
XCr7<13> VRP<7> VRN<7> nmoscap lr=3u wr=3u m=1
XCr7<14> VRP<7> VRN<7> nmoscap lr=3u wr=3u m=1
XCr7<15> VRP<7> VRN<7> nmoscap lr=3u wr=3u m=1
XCr7<16> VRP<7> VRN<7> nmoscap lr=3u wr=3u m=1
XCr7<17> VRP<7> VRN<7> nmoscap lr=3u wr=3u m=1
XCr7<18> VRP<7> VRN<7> nmoscap lr=3u wr=3u m=1
XCr7<19> VRP<7> VRN<7> nmoscap lr=3u wr=3u m=1
XCr7<20> VRP<7> VRN<7> nmoscap lr=3u wr=3u m=1
XCr7<21> VRP<7> VRN<7> nmoscap lr=3u wr=3u m=1
XCr7<22> VRP<7> VRN<7> nmoscap lr=3u wr=3u m=1
XCr7<23> VRP<7> VRN<7> nmoscap lr=3u wr=3u m=1
XCr7<24> VRP<7> VRN<7> nmoscap lr=3u wr=3u m=1
XCr7<25> VRP<7> VRN<7> nmoscap lr=3u wr=3u m=1
XCr7<26> VRP<7> VRN<7> nmoscap lr=3u wr=3u m=1
XCr7<27> VRP<7> VRN<7> nmoscap lr=3u wr=3u m=1
XCr7<28> VRP<7> VRN<7> nmoscap lr=3u wr=3u m=1
XCr7<29> VRP<7> VRN<7> nmoscap lr=3u wr=3u m=1
XCr7<30> VRP<7> VRN<7> nmoscap lr=3u wr=3u m=1
XCr7<31> VRP<7> VRN<7> nmoscap lr=3u wr=3u m=1
XCr7<32> VRP<7> VRN<7> nmoscap lr=3u wr=3u m=1
XCr7<33> VRP<7> VRN<7> nmoscap lr=3u wr=3u m=1
XCr7<34> VRP<7> VRN<7> nmoscap lr=3u wr=3u m=1
XCr7<35> VRP<7> VRN<7> nmoscap lr=3u wr=3u m=1
XCr6<0> VRP<6> VRN<6> nmoscap lr=3u wr=3u m=1
XCr6<1> VRP<6> VRN<6> nmoscap lr=3u wr=3u m=1
XCr6<2> VRP<6> VRN<6> nmoscap lr=3u wr=3u m=1
XCr6<3> VRP<6> VRN<6> nmoscap lr=3u wr=3u m=1
XCr6<4> VRP<6> VRN<6> nmoscap lr=3u wr=3u m=1
XCr6<5> VRP<6> VRN<6> nmoscap lr=3u wr=3u m=1
XCr6<6> VRP<6> VRN<6> nmoscap lr=3u wr=3u m=1
XCr6<7> VRP<6> VRN<6> nmoscap lr=3u wr=3u m=1
XCr6<8> VRP<6> VRN<6> nmoscap lr=3u wr=3u m=1
XCr6<9> VRP<6> VRN<6> nmoscap lr=3u wr=3u m=1
XCr6<10> VRP<6> VRN<6> nmoscap lr=3u wr=3u m=1
XCr6<11> VRP<6> VRN<6> nmoscap lr=3u wr=3u m=1
XCr6<12> VRP<6> VRN<6> nmoscap lr=3u wr=3u m=1
XCr6<13> VRP<6> VRN<6> nmoscap lr=3u wr=3u m=1
XCr6<14> VRP<6> VRN<6> nmoscap lr=3u wr=3u m=1
XCr6<15> VRP<6> VRN<6> nmoscap lr=3u wr=3u m=1
XCr6<16> VRP<6> VRN<6> nmoscap lr=3u wr=3u m=1
XCr6<17> VRP<6> VRN<6> nmoscap lr=3u wr=3u m=1
XCr5<0> VRP<5> VRN<5> nmoscap lr=3u wr=3u m=1
XCr5<1> VRP<5> VRN<5> nmoscap lr=3u wr=3u m=1
XCr5<2> VRP<5> VRN<5> nmoscap lr=3u wr=3u m=1
XCr5<3> VRP<5> VRN<5> nmoscap lr=3u wr=3u m=1
XCr5<4> VRP<5> VRN<5> nmoscap lr=3u wr=3u m=1
XCr5<5> VRP<5> VRN<5> nmoscap lr=3u wr=3u m=1
XCr5<6> VRP<5> VRN<5> nmoscap lr=3u wr=3u m=1
XCr5<7> VRP<5> VRN<5> nmoscap lr=3u wr=3u m=1
XCr5<8> VRP<5> VRN<5> nmoscap lr=3u wr=3u m=1
XCr5<9> VRP<5> VRN<5> nmoscap lr=3u wr=3u m=1
XCr5<10> VRP<5> VRN<5> nmoscap lr=3u wr=3u m=1
XCr5<11> VRP<5> VRN<5> nmoscap lr=3u wr=3u m=1
XCr5<12> VRP<5> VRN<5> nmoscap lr=3u wr=3u m=1
XCr5<13> VRP<5> VRN<5> nmoscap lr=3u wr=3u m=1
XCr5<14> VRP<5> VRN<5> nmoscap lr=3u wr=3u m=1
XCr5<15> VRP<5> VRN<5> nmoscap lr=3u wr=3u m=1
XCr5<16> VRP<5> VRN<5> nmoscap lr=3u wr=3u m=1
XCr5<17> VRP<5> VRN<5> nmoscap lr=3u wr=3u m=1
XCr4<0> VRP<4> VRN<4> nmoscap lr=3u wr=3u m=1
XCr4<1> VRP<4> VRN<4> nmoscap lr=3u wr=3u m=1
XCr4<2> VRP<4> VRN<4> nmoscap lr=3u wr=3u m=1
XCr4<3> VRP<4> VRN<4> nmoscap lr=3u wr=3u m=1
XCr4<4> VRP<4> VRN<4> nmoscap lr=3u wr=3u m=1
XCr4<5> VRP<4> VRN<4> nmoscap lr=3u wr=3u m=1
XCr4<6> VRP<4> VRN<4> nmoscap lr=3u wr=3u m=1
XCr4<7> VRP<4> VRN<4> nmoscap lr=3u wr=3u m=1
XCr4<8> VRP<4> VRN<4> nmoscap lr=3u wr=3u m=1
XCr4<9> VRP<4> VRN<4> nmoscap lr=3u wr=3u m=1
XCr4<10> VRP<4> VRN<4> nmoscap lr=3u wr=3u m=1
XCr4<11> VRP<4> VRN<4> nmoscap lr=3u wr=3u m=1
XCr4<12> VRP<4> VRN<4> nmoscap lr=3u wr=3u m=1
XCr4<13> VRP<4> VRN<4> nmoscap lr=3u wr=3u m=1
XCr4<14> VRP<4> VRN<4> nmoscap lr=3u wr=3u m=1
XCr4<15> VRP<4> VRN<4> nmoscap lr=3u wr=3u m=1
XCr4<16> VRP<4> VRN<4> nmoscap lr=3u wr=3u m=1
XCr4<17> VRP<4> VRN<4> nmoscap lr=3u wr=3u m=1
XCr3<0> VRP<3> VRN<3> nmoscap lr=3u wr=3u m=1
XCr3<1> VRP<3> VRN<3> nmoscap lr=3u wr=3u m=1
XCr3<2> VRP<3> VRN<3> nmoscap lr=3u wr=3u m=1
XCr3<3> VRP<3> VRN<3> nmoscap lr=3u wr=3u m=1
XCr3<4> VRP<3> VRN<3> nmoscap lr=3u wr=3u m=1
XCr3<5> VRP<3> VRN<3> nmoscap lr=3u wr=3u m=1
XCr3<6> VRP<3> VRN<3> nmoscap lr=3u wr=3u m=1
XCr3<7> VRP<3> VRN<3> nmoscap lr=3u wr=3u m=1
XCr3<8> VRP<3> VRN<3> nmoscap lr=3u wr=3u m=1
XCr3<9> VRP<3> VRN<3> nmoscap lr=3u wr=3u m=1
XCr3<10> VRP<3> VRN<3> nmoscap lr=3u wr=3u m=1
XCr3<11> VRP<3> VRN<3> nmoscap lr=3u wr=3u m=1
XCr3<12> VRP<3> VRN<3> nmoscap lr=3u wr=3u m=1
XCr3<13> VRP<3> VRN<3> nmoscap lr=3u wr=3u m=1
XCr3<14> VRP<3> VRN<3> nmoscap lr=3u wr=3u m=1
XCr3<15> VRP<3> VRN<3> nmoscap lr=3u wr=3u m=1
XCr3<16> VRP<3> VRN<3> nmoscap lr=3u wr=3u m=1
XCr3<17> VRP<3> VRN<3> nmoscap lr=3u wr=3u m=1
XCr2<0> VRP<2> VRN<2> nmoscap lr=3u wr=3u m=1
XCr2<1> VRP<2> VRN<2> nmoscap lr=3u wr=3u m=1
XCr2<2> VRP<2> VRN<2> nmoscap lr=3u wr=3u m=1
XCr2<3> VRP<2> VRN<2> nmoscap lr=3u wr=3u m=1
XCr2<4> VRP<2> VRN<2> nmoscap lr=3u wr=3u m=1
XCr2<5> VRP<2> VRN<2> nmoscap lr=3u wr=3u m=1
XCr2<6> VRP<2> VRN<2> nmoscap lr=3u wr=3u m=1
XCr2<7> VRP<2> VRN<2> nmoscap lr=3u wr=3u m=1
XCr2<8> VRP<2> VRN<2> nmoscap lr=3u wr=3u m=1
XCr2<9> VRP<2> VRN<2> nmoscap lr=3u wr=3u m=1
XCr2<10> VRP<2> VRN<2> nmoscap lr=3u wr=3u m=1
XCr2<11> VRP<2> VRN<2> nmoscap lr=3u wr=3u m=1
XCr2<12> VRP<2> VRN<2> nmoscap lr=3u wr=3u m=1
XCr2<13> VRP<2> VRN<2> nmoscap lr=3u wr=3u m=1
XCr2<14> VRP<2> VRN<2> nmoscap lr=3u wr=3u m=1
XCr2<15> VRP<2> VRN<2> nmoscap lr=3u wr=3u m=1
XCr2<16> VRP<2> VRN<2> nmoscap lr=3u wr=3u m=1
XCr2<17> VRP<2> VRN<2> nmoscap lr=3u wr=3u m=1
XI117<0> net0182 DVDD DVSS net0181 net0183 net0184 net0185 VCM CR<9> VRNCPY
+ VRPCPY SW6_V3
XI117<1> net0182 DVDD DVSS net0181 net0183 net0184 net0185 VCM CR<9> VRNCPY
+ VRPCPY SW6_V3
XI116 net0194 DVDD DVSS net0193 net0195 net0196 net0197 VCM CR<8> VRNCPY
+ VRPCPY SW6_V3
XI115<0> net0170 DVDD DVSS net0169 net0171 net0172 net0173 VCM CR<10> VRNCPY
+ VRPCPY SW6_V3
XI115<1> net0170 DVDD DVSS net0169 net0171 net0172 net0173 VCM CR<10> VRNCPY
+ VRPCPY SW6_V3
XI115<2> net0170 DVDD DVSS net0169 net0171 net0172 net0173 VCM CR<10> VRNCPY
+ VRPCPY SW6_V3
XI65 net0199 DVDD DVSS net0198 net0200 net0201 net0202 VCM CL<8> VRNCPY VRPCPY
+ SW6_V3
XSW10L<0> net0187 DVDD DVSS net0186 net0188 net0189 net0190 VCM CL<9> VRNCPY
+ VRPCPY SW6_V3
XSW10L<1> net0187 DVDD DVSS net0186 net0188 net0189 net0190 VCM CL<9> VRNCPY
+ VRPCPY SW6_V3
XSW11L<0> net0175 DVDD DVSS net0174 net0176 net0177 net0178 VCM CL<10> VRNCPY
+ VRPCPY SW6_V3
XSW11L<1> net0175 DVDD DVSS net0174 net0176 net0177 net0178 VCM CL<10> VRNCPY
+ VRPCPY SW6_V3
XSW11L<2> net0175 DVDD DVSS net0174 net0176 net0177 net0178 VCM CL<10> VRNCPY
+ VRPCPY SW6_V3
XI56 DVSS VBTFN VIN CL<9> BTSW_256
XI91 DVSS VBTFN VIN CR<9> BTSW_256
XCrP<0> net42 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v3
XCrP<1> net42 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v3
XCrP<2> net42 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v3
XCrP<3> net42 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v3
XCrP<4> net42 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v3
XCrP<5> net42 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v3
XCrP<6> net42 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v3
XCrP<7> net42 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v3
XCrP<8> net42 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v3
XCrP<9> net42 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v3
XCrP<10> net42 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v3
XCrP<11> net42 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v3
XCrP<12> net42 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v3
XCrP<13> net42 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v3
XCrP<14> net42 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v3
XCrP<15> net42 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v3
XCrP<16> net42 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v3
XCrP<17> net42 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v3
XCrP<18> net42 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v3
XCrP<19> net42 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v3
XCrP<20> net42 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v3
XCrP<21> net42 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v3
XCrP<22> net42 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v3
XCrP<23> net42 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v3
XCrP<24> net42 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v3
XCrP<25> net42 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v3
XCrP<26> net42 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v3
XCrP<27> net42 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v3
XCrP<28> net42 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v3
XCrP<29> net42 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v3
XCrP<30> net42 DVDD DVSS VRCTL VRNCPY VRNX VRPCPY VRPX SW_Cres_v3_1_np_v3
XI26 CK<7> DVDD DVSS VRCTL VRN<7> VRNX VRP<7> VRPX SW_Cres_v3_1_np_v3
XI90 DVSS VBTFN VIN CR<10> BTSW_MSB
XI45 DVSS VBTFN VIN CL<10> BTSW_MSB
XI8 D<4> DVDD DVSS SW<4> SWB<4> TG<4> TGB<4> VBTFN VCM VIN C<3> VRN<4> VRP<4>
+ SW2_V2
XI66 DVSS VBTFN VIN CL<8> BTSW_128
XI92 DVSS VBTFN VIN CR<8> BTSW_128
XI121 D<7> net0191 DVDD DVSS INVD1LVT
XI112 D_F<8> net0214 DVDD DVSS INVD1LVT
XI110 D_F<7> net0216 DVDD DVSS INVD1LVT
XI79 D_F<7> net0229 DVDD DVSS INVD1LVT
XI73 SWB<10> net0232 DVDD DVSS INVD1LVT
XI71 SW<10> net0230 DVDD DVSS INVD1LVT
XI70 D_F<8> net0231 DVDD DVSS INVD1LVT
XI68 TG<10> net0202 DVDD DVSS INVD1LVT
XI67 TGB<10> net0201 DVDD DVSS INVD1LVT
XI88 TGB<10> net0196 DVDD DVSS INVD1LVT
XI103 SW<10> net0219 DVDD DVSS INVD1LVT
XI85 TG<10> net0197 DVDD DVSS INVD1LVT
XI96 SWB<10> net0213 DVDD DVSS INVD1LVT
XI81 D_F<11> net0218 DVDD DVSS INVD1LVT
XI111 net0214 net0194 DVDD DVSS INVD4LVT
XI74 net0232 net0200 DVDD DVSS INVD4LVT
XI72 net0230 net0198 DVDD DVSS INVD4LVT
XI69 net0231 net0199 DVDD DVSS INVD4LVT
XI102 net0219 net0193 DVDD DVSS INVD4LVT
XI95 net0213 net0195 DVDD DVSS INVD4LVT
XI158 CKS CKSB DVDD DVSS VCM VFP TG_Top_Fine_v3
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    ND2D2LVT
* View Name:    schematic
************************************************************************

.SUBCKT ND2D2LVT A1 A2 ZN VDD VSS
*.PININFO A1:I A2:I ZN:O VDD:B VSS:B
MMU3_1-M_u1 ZN A1 VDD VDD lvtpfet l=LA w=WV m=1
MMU3_1-M_u2 ZN A2 VDD VDD lvtpfet l=LA w=WV m=1
MMU3_0-M_u2 ZN A2 VDD VDD lvtpfet l=LA w=WV m=1
MMU3_0-M_u1 ZN A1 VDD VDD lvtpfet l=LA w=WV m=1
MMU3_0-M_u4 net20 A2 VSS VSS lvtnfet l=LA w=WP m=1
MMU3_1-M_u3 ZN A1 net28 VSS lvtnfet l=LA w=WP m=1
MMU3_1-M_u4 net28 A2 VSS VSS lvtnfet l=LA w=WP m=1
MMU3_0-M_u3 ZN A1 net20 VSS lvtnfet l=LA w=WP m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    XNR2D0LVT
* View Name:    schematic
************************************************************************

.SUBCKT XNR2D0LVT A1 A2 ZN VDD VSS
*.PININFO A1:I A2:I ZN:O VDD:B VSS:B
MM_u4-M_u3 ZN net28 VDD VDD lvtpfet l=LA w=WI m=1
MM_u5-M_u3 net25 net5 VDD VDD lvtpfet l=LA w=WF m=1
MM_u8-M_u3 net11 A1 VDD VDD lvtpfet l=LA w=WI m=1
MMI0-M_u2 net5 net11 net28 VDD lvtpfet l=LA w=WI m=1
MM_u2-M_u3 net5 A2 VDD VDD lvtpfet l=LA w=WI m=1
MM_u7-M_u2 net25 A1 net28 VDD lvtpfet l=LA w=WI m=1
MMI0-M_u3 net5 A1 net28 VSS lvtnfet l=LA w=WC m=1
MM_u8-M_u2 net11 A1 VSS VSS lvtnfet l=LA w=WE m=1
MM_u4-M_u2 ZN net28 VSS VSS lvtnfet l=LA w=WC m=1
MM_u2-M_u2 net5 A2 VSS VSS lvtnfet l=LA w=WC m=1
MM_u5-M_u2 net25 net5 VSS VSS lvtnfet l=LA w=WD m=1
MM_u7-M_u3 net25 net11 net28 VSS lvtnfet l=LA w=WD m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    NR2D2LVT
* View Name:    schematic
************************************************************************

.SUBCKT NR2D2LVT A1 A2 ZN VDD VSS
*.PININFO A1:I A2:I ZN:O VDD:B VSS:B
MMI1_1-M_u3 ZN A2 VSS VSS lvtnfet l=LA w=WP m=1
MMI1_1-M_u4 ZN A1 VSS VSS lvtnfet l=LA w=WP m=1
MMI1_0-M_u4 ZN A1 VSS VSS lvtnfet l=LA w=WP m=1
MMI1_0-M_u3 ZN A2 VSS VSS lvtnfet l=LA w=WP m=1
MMI1_1-M_u2 ZN A1 net17 VDD lvtpfet l=LA w=WW m=1
MMI1_0-M_u1 net25 A2 VDD VDD lvtpfet l=LA w=WW m=1
MMI1_0-M_u2 ZN A1 net25 VDD lvtpfet l=LA w=WW m=1
MMI1_1-M_u1 net17 A2 VDD VDD lvtpfet l=LA w=WW m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    TIELLVT
* View Name:    schematic
************************************************************************

.SUBCKT TIELLVT ZN VDD VSS
*.PININFO ZN:O VDD:B VSS:B
MM_u2 ZN net5 VSS VSS lvtnfet l=LA w=WR m=1
MM_u1 net5 net5 VDD VDD lvtpfet l=LA w=WX m=1
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    ckt_CpSkp_LOG_V3
* View Name:    schematic
************************************************************************

.SUBCKT ckt_CpSkp_LOG_V3 CPY D<11> D<10> D<9> D<8> D<7> DVDD DVSS SW<12>
+ SW<11> SW<10> SW<9> SW<8> SWB<12> SWB<11> SWB<10> SWB<9> SWB<8> TG<12>
+ TG<11> TG<10> TG<9> TG<8> TGB<12> TGB<11> TGB<10> TGB<9> TGB<8>
*.PININFO CPY:I D<11>:I D<10>:I D<9>:I D<8>:I D<7>:I SW<12>:O SW<11>:O
*.PININFO SW<10>:O SW<9>:O SW<8>:O SWB<12>:O SWB<11>:O SWB<10>:O SWB<9>:O
*.PININFO SWB<8>:O TG<12>:O TG<11>:O TG<10>:O TG<9>:O TG<8>:O TGB<12>:O
*.PININFO TGB<11>:O TGB<10>:O TGB<9>:O TGB<8>:O DVDD:B DVSS:B
XI51 TGB<10> CP SWB<10> DVDD DVSS ND2D2LVT
XI52 TGB<9> CP SWB<9> DVDD DVSS ND2D2LVT
XI22 CPB net054 net053 DVDD DVSS NR2D1LVT
XI24 CPB net087 net086 DVDD DVSS NR2D1LVT
XI15 D<7> D<11> net084 DVDD DVSS XNR2D0LVT
XI11 D<8> D<11> net085 DVDD DVSS XNR2D0LVT
XI7 D<9> D<11> net087 DVDD DVSS XNR2D0LVT
XI2 D<10> D<11> net054 DVDD DVSS XNR2D0LVT
XI45 net027 SWB<11> DVDD DVSS INVD3LVT
XI44 net010 SW<11> DVDD DVSS INVD3LVT
XI48 net026 SWB<12> DVDD DVSS INVD3LVT
XI47 net018 SW<12> DVDD DVSS INVD3LVT
XI28 net014 CP DVDD DVSS INVD3LVT
XI6 net011 TG<12> DVDD DVSS INVD3LVT
XI5 net053 TGB<12> DVDD DVSS INVD3LVT
XI25 CPB net085 TG<10> DVDD DVSS NR2D2LVT
XI26 CPB net084 TG<9> DVDD DVSS NR2D2LVT
XI64 TGB<11> TG<11> DVDD DVSS INVD2LVT_schematic
XI42 SWB<8> SW<8> DVDD DVSS INVD2LVT_schematic
XI54 SWB<9> SW<9> DVDD DVSS INVD2LVT_schematic
XI41 CP SWB<8> DVDD DVSS INVD2LVT_schematic
XI49 SWB<10> SW<10> DVDD DVSS INVD2LVT_schematic
XI18 TG<8> TGB<8> DVDD DVSS INVD2LVT_schematic
XI16 TG<9> TGB<9> DVDD DVSS INVD2LVT_schematic
XI12 TG<10> TGB<10> DVDD DVSS INVD2LVT_schematic
XI8 net086 TGB<11> DVDD DVSS INVD2LVT_schematic
XI23 CPY CPB DVDD DVSS INVD2LVT_schematic
XI46 TGB<12> CP net018 DVDD DVSS ND2D1LVT
XI43 TGB<11> CP net010 DVDD DVSS ND2D1LVT
XI56 net010 net027 DVDD DVSS INVD1LVT
XI55 net018 net026 DVDD DVSS INVD1LVT
XI65 CPY net014 DVDD DVSS INVD1LVT
XI63 net053 net011 DVDD DVSS INVD1LVT
XI37 TG<8> DVDD DVSS TIELLVT
.ENDS

************************************************************************
* Library Name: AW_12b_SARADC
* Cell Name:    Comp_Fine
* View Name:    schematic
************************************************************************

.SUBCKT Comp_Fine AVDD AVSS CKF VIN VIP VON VOP
*.PININFO CKF:I VIN:I VIP:I VON:O VOP:O AVDD:B AVSS:B
XI5 net02 VOP AVDD AVSS INVD2LVT
XI3 net027 VON AVDD AVSS INVD2LVT
MM18 net029 net03 AVDD AVDD lvtpfet l=LD w=WS m=2
MM13 net03 fn net025 AVDD lvtpfet l=LD w=WS m=2
MM17 net013 fp net029 AVDD lvtpfet l=LD w=WS m=2
MM9 net025 net013 AVDD AVDD lvtpfet l=LD w=WS m=2
MM4 fp CKF AVDD AVDD lvtpfet l=LD w=WH m=2
MM3 fn CKF AVDD AVDD lvtpfet l=LD w=WH m=2
XI7 net013 net027 AVDD AVSS INVD1LVT_schematic
XI6 net03 net02 AVDD AVSS INVD1LVT_schematic
MM10 net013 fp AVSS AVSS lvtnfet_dnw l=LD w=WK m=2
MM6 net013 net03 AVSS AVSS lvtnfet_dnw l=LD w=WK m=2
MM7 net03 fn AVSS AVSS lvtnfet_dnw l=LD w=WK m=2
MM5 net03 net013 AVSS AVSS lvtnfet_dnw l=LD w=WK m=2
MM2 fp VIN net15 AVSS lvtnfet_dnw l=LC w=WQ m=4
MM1 fn VIP net15 AVSS lvtnfet_dnw l=LC w=WQ m=4
MM0 net15 CKF AVSS AVSS lvtnfet_dnw l=LD w=WQ m=2
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    FINE_SAR_Logic_V4
* View Name:    schematic
************************************************************************

.SUBCKT FINE_SAR_Logic_V4 CK0 CK<7> CK<6> CK<5> CK<4> CK<3> CK<2> CKSBT CKSBTB
+ D<7> D<6> D<5> D<4> D<3> D<2> D<1> DB<7> DB<6> DB<5> DB<4> DB<3> DB<2> DB<1>
+ DVDD DVSS FD<7> FD<6> FD<5> FD<4> FD<3> FD<2> FD<1> FD<0> FIN_RDY OUTNF
+ OUTPF ST_FINE SW<7> SW<6> SW<5> SW<4> SW<3> SW<2> SW<1> SWB<7> SWB<6> SWB<5>
+ SWB<4> SWB<3> SWB<2> SWB<1> TG<7> TG<6> TG<5> TG<4> TG<3> TG<2> TG<1> TGB<7>
+ TGB<6> TGB<5> TGB<4> TGB<3> TGB<2> TGB<1> VALIDF
*.PININFO FIN_RDY:O CK0:B CK<7>:B CK<6>:B CK<5>:B CK<4>:B CK<3>:B CK<2>:B
*.PININFO CKSBT:B CKSBTB:B D<7>:B D<6>:B D<5>:B D<4>:B D<3>:B D<2>:B D<1>:B
*.PININFO DB<7>:B DB<6>:B DB<5>:B DB<4>:B DB<3>:B DB<2>:B DB<1>:B DVDD:B
*.PININFO DVSS:B FD<7>:B FD<6>:B FD<5>:B FD<4>:B FD<3>:B FD<2>:B FD<1>:B
*.PININFO FD<0>:B OUTNF:B OUTPF:B ST_FINE:B SW<7>:B SW<6>:B SW<5>:B SW<4>:B
*.PININFO SW<3>:B SW<2>:B SW<1>:B SWB<7>:B SWB<6>:B SWB<5>:B SWB<4>:B SWB<3>:B
*.PININFO SWB<2>:B SWB<1>:B TG<7>:B TG<6>:B TG<5>:B TG<4>:B TG<3>:B TG<2>:B
*.PININFO TG<1>:B TGB<7>:B TGB<6>:B TGB<5>:B TGB<4>:B TGB<3>:B TGB<2>:B
*.PININFO TGB<1>:B VALIDF:B
XI11 VALIDF CK<1> DVDD DVSS CK0 CKSBTB DFFRB_B_V6_HVT
XI53 VALIDF CK<2> DVDD DVSS CK<1> CKSBTB DFFRB_B_V6_HVT
XI54 VALIDF CK<3> DVDD DVSS CK<2> CKSBTB DFFRB_B_V6_HVT
XI213 VALIDF CK<7> DVDD DVSS CK<6> CKSBTB DFFRB_B_V6_HVT
XI212 VALIDF ST_FINE DVDD DVSS CK<7> CKSBTB DFFRB_B_V6_HVT
XI214 VALIDF CK<6> DVDD DVSS CK<5> CKSBTB DFFRB_B_V6_HVT
XI215 VALIDF CK<5> DVDD DVSS CK<4> CKSBTB DFFRB_B_V6_HVT
XI216 VALIDF CK<4> DVDD DVSS CK<3> CKSBTB DFFRB_B_V6_HVT
XI30 CK0 net079 DVDD DVSS INVD0HVT_schematic
XI40 net083 FD<0> DVDD DVSS INVD1LVT
XI38 DB<1> FD<1> DVDD DVSS INVD1LVT
XI37 DB<2> FD<2> DVDD DVSS INVD1LVT
XI36 DB<3> FD<3> DVDD DVSS INVD1LVT
XI35 DB<4> FD<4> DVDD DVSS INVD1LVT
XI34 DB<5> FD<5> DVDD DVSS INVD1LVT
XI33 DB<6> FD<6> DVDD DVSS INVD1LVT
XI29 SW<1> SWB<1> DVDD DVSS INVD1LVT
XI28 TG<1> TGB<1> DVDD DVSS INVD1LVT
XI25 TG<2> TGB<2> DVDD DVSS INVD1LVT
XI24 SW<2> SWB<2> DVDD DVSS INVD1LVT
XI21 SW<3> SWB<3> DVDD DVSS INVD1LVT
XI20 TG<3> TGB<3> DVDD DVSS INVD1LVT
XI32 DB<7> FD<7> DVDD DVSS INVD1LVT
XI108 net079 FIN_RDY DVDD DVSS INVD1LVT
XI173 TG<7> TGB<7> DVDD DVSS INVD1LVT
XI31 SW<7> SWB<7> DVDD DVSS INVD1LVT
XI104 SW<6> SWB<6> DVDD DVSS INVD1LVT
XI170 TG<6> TGB<6> DVDD DVSS INVD1LVT
XI158 TG<5> TGB<5> DVDD DVSS INVD1LVT
XI102 SW<5> SWB<5> DVDD DVSS INVD1LVT
XI100 SW<4> SWB<4> DVDD DVSS INVD1LVT
XI155 TG<4> TGB<4> DVDD DVSS INVD1LVT
XI27 CK<1> CKSBT TG<1> DVDD DVSS NR2D1LVT
XI26 TG<1> CKSBT SW<1> DVDD DVSS NR2D1LVT
XI23 TG<2> CKSBT SW<2> DVDD DVSS NR2D1LVT
XI22 CK<2> CKSBT TG<2> DVDD DVSS NR2D1LVT
XI19 TG<3> CKSBT SW<3> DVDD DVSS NR2D1LVT
XI18 CK<3> CKSBT TG<3> DVDD DVSS NR2D1LVT
XI175 CK<7> CKSBT TG<7> DVDD DVSS NR2D1LVT
XI107 TG<7> CKSBT SW<7> DVDD DVSS NR2D1LVT
XI171 CK<6> CKSBT TG<6> DVDD DVSS NR2D1LVT
XI105 TG<6> CKSBT SW<6> DVDD DVSS NR2D1LVT
XI39 TG<5> CKSBT SW<5> DVDD DVSS NR2D1LVT
XI159 CK<5> CKSBT TG<5> DVDD DVSS NR2D1LVT
XI101 TG<4> CKSBT SW<4> DVDD DVSS NR2D1LVT
XI156 CK<4> CKSBT TG<4> DVDD DVSS NR2D1LVT
XI9 CK<2> OUTNF DVSS DVDD DB<2> D<2> DFF_HVT_Coarse
XI10 CK<1> OUTNF DVSS DVDD DB<1> D<1> DFF_HVT_Coarse
XI12 CK0 OUTNF DVSS DVDD net083 net081 DFF_HVT_Coarse
XI228 CK<3> OUTNF DVSS DVDD DB<3> D<3> DFF_HVT_Coarse
XI227 CK<4> OUTPF DVSS DVDD D<4> DB<4> DFF_HVT_Coarse
XI229 CK<7> OUTPF DVSS DVDD D<7> DB<7> DFF_HVT_Coarse
XI230 CK<6> OUTPF DVSS DVDD D<6> DB<6> DFF_HVT_Coarse
XI231 CK<5> OUTPF DVSS DVDD D<5> DB<5> DFF_HVT_Coarse
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    Fine_Comp_CK_V3
* View Name:    schematic
************************************************************************

.SUBCKT Fine_Comp_CK_V3 CK0 CKF DVDD DVSS OUTNF OUTPF ST_FINEB VALIDF VCTIN
*.PININFO VCTIN:I CK0:B CKF:B DVDD:B DVSS:B OUTNF:B OUTPF:B ST_FINEB:B VALIDF:B
XI4 net012 VCTIN DVDD DVSS net08 PINVD0YVT
XI2 net021 VCTIN DVDD DVSS net012 PINVD0YVT
XI46 net30 VCTIN DVDD DVSS net29 PINVD0YVT
XI21 net33 VCTIN DVDD DVSS net32 PINVD0YVT
XI12 net34 VCTIN DVDD DVSS net33 PINVD0YVT
XI47 net31 VCTIN DVDD DVSS net30 PINVD0YVT
XI0 net29 net021 DVDD DVSS INVD0HVT_schematic
XI22 net32 net31 DVDD DVSS INVD0HVT_schematic
XI1 net014 VALIDF DVDD DVSS INVD3LVT
XI218 VALIDF ST_FINEB CK0 net34 DVDD DVSS NR3D1LVT
XI24 OUTNF OUTPF net014 DVDD DVSS NR2D1LVT
XI3 net019 CKF DVDD DVSS INVD2LVT_schematic
XI5 net08 net019 DVDD DVSS INVD1LVT
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    BTSW_MOM
* View Name:    schematic
************************************************************************

.SUBCKT BTSW_MOM AVDD AVSS CKSBT CKSBTB VBTSW VIN
*.PININFO CKSBT:I CKSBTB:I VIN:I AVDD:B AVSS:B VBTSW:B
XC0 net12 net20 cap nv=64 nh=28 w=WA s=100n stm=1 spm=7 m=1
MM9 VBTSW net7 net12 net12 pch l=LA w=WQ m=1
MM8 AVDD VBTSW net12 net12 pch l=LA w=WQ m=1
MM7 net7 CKSBT AVDD AVDD pch l=LA w=WQ m=1
MM6 net27 CKSBTB AVSS AVSS nch l=LA w=WK m=1
MM5 VBTSW AVDD net27 AVSS nch l=LA w=WK m=1
MM3 VIN VBTSW net20 AVSS nch l=LA w=WK m=1
MM2 net7 VBTSW net20 AVSS nch l=LA w=WK m=1
MM1 net20 CKSBTB AVSS AVSS nch l=LA w=WK m=2
MM0 net7 CKSBT net20 AVSS nch l=LA w=WK m=1
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    8b_ADC
* View Name:    schematic
************************************************************************

.SUBCKT 8b_ADC AVDD AVSS CKS CKSB CKSBT CKSBTB CPY D<11> D<10> D<9> D<8> D<7>
+ DB<11> DB<10> DB<9> DB<8> DB<7> DO<11> DO<10> DO<9> DO<8> DO<7> DVDD DVSS
+ FD<7> FD<6> FD<5> FD<4> FD<3> FD<2> FD<1> FD<0> FIN_RDY ST_FINE VCM VCTINF
+ VIN VIP VRCTL VRNX VRPX
*.PININFO CKS:I CKSB:I CKSBT:I CKSBTB:I CPY:I ST_FINE:I VCTINF:I VIN:I VIP:I
*.PININFO VRCTL:I DO<11>:O DO<10>:O DO<9>:O DO<8>:O DO<7>:O FD<7>:O FD<6>:O
*.PININFO FD<5>:O FD<4>:O FD<3>:O FD<2>:O FD<1>:O FD<0>:O FIN_RDY:O AVDD:B
*.PININFO AVSS:B D<11>:B D<10>:B D<9>:B D<8>:B D<7>:B DB<11>:B DB<10>:B
*.PININFO DB<9>:B DB<8>:B DB<7>:B DVDD:B DVSS:B VCM:B VRNX:B VRPX:B
XI137 net029 net031<0> net031<1> net031<2> net031<3> net031<4> net031<5>
+ net031<6> CK<7> CK<6> CK<5> CK<4> CK<3> CK<2> CKS CKSB net032<0> net032<1>
+ net032<2> net032<3> CPYB net030<0> net030<1> net030<2> net030<3> DFB<7>
+ DFB<6> DFB<5> DFB<4> DFB<3> DFB<2> DFB<1> DVDD DVSS DB<11> DB_F<10> DB_F<9>
+ DB<8> DB<7> SW<12> SW<11> SW<10> SW<9> SW<8> SW<7> SW<6> SW<5> SW<4> SW<3>
+ SW<2> L SWB<12> SWB<11> SWB<10> SWB<9> SWB<8> SWB<7> SWB<6> SWB<5> SWB<4>
+ SWB<3> SWB<2> H TG<12> TG<11> TG<10> TG<9> TG<8> TG<7> TG<6> TG<5> TG<4>
+ TG<3> TG<2> CKSBTB TGB<12> TGB<11> TGB<10> TGB<9> TGB<8> TGB<7> TGB<6>
+ TGB<5> TGB<4> TGB<3> TGB<2> CKSBT VBTFP VCM VFN VIP VRCTL net96<0> net96<1>
+ net96<2> net96<3> net96<4> net96<5> net92 VRNX net95<0> net95<1> net95<2>
+ net95<3> net95<4> net95<5> net94 VRPX CDAC_SW_Fine_P
XI136 net033 net035<0> net035<1> net035<2> net035<3> net035<4> net035<5>
+ net035<6> CK<7> CK<6> CK<5> CK<4> CK<3> CK<2> CKS CKSB net036<0> net036<1>
+ net036<2> net036<3> CPYB net034<0> net034<1> net034<2> net034<3> DF<7> DF<6>
+ DF<5> DF<4> DF<3> DF<2> DF<1> DVDD DVSS D<11> D_F<10> D_F<9> D<8> D<7>
+ SW<12> SW<11> SW<10> SW<9> SW<8> SW<7> SW<6> SW<5> SW<4> SW<3> SW<2> SW<1>
+ SWB<12> SWB<11> SWB<10> SWB<9> SWB<8> SWB<7> SWB<6> SWB<5> SWB<4> SWB<3>
+ SWB<2> SWB<1> TG<12> TG<11> TG<10> TG<9> TG<8> TG<7> TG<6> TG<5> TG<4> TG<3>
+ TG<2> TG<1> TGB<12> TGB<11> TGB<10> TGB<9> TGB<8> TGB<7> TGB<6> TGB<5>
+ TGB<4> TGB<3> TGB<2> TGB<1> VBTFN VCM VFP VIN VRCTL net96<0> net96<1>
+ net96<2> net96<3> net96<4> net96<5> net92 VRNX net95<0> net95<1> net95<2>
+ net95<3> net95<4> net95<5> net94 VRPX CDAC_SW_Fine_P
XI0 CPY D_F<11> D_F<10> D_F<9> D<8> D<7> DVDD DVSS SW<12> SW<11> SW<10> SW<9>
+ SW<8> SWB<12> SWB<11> SWB<10> SWB<9> SWB<8> TG<12> TG<11> TG<10> TG<9> TG<8>
+ TGB<12> TGB<11> TGB<10> TGB<9> TGB<8> ckt_CpSkp_LOG_V3
XI138 AVDD AVSS CKF VFN VFP OUTNF OUTPF Comp_Fine
XI160 H DVDD DVSS TIEHLVT
XI161 L DVDD DVSS TIELLVT
XI2 CK0 CK<7> CK<6> CK<5> CK<4> CK<3> CK<2> CKSBTI CKSBTIB DF<7> DF<6> DF<5>
+ DF<4> DF<3> DF<2> DF<1> DFB<7> DFB<6> DFB<5> DFB<4> DFB<3> DFB<2> DFB<1>
+ DVDD DVSS FD<7> FD<6> FD<5> FD<4> FD<3> FD<2> FD<1> FD<0> FIN_RDY OUTNF
+ OUTPF ST_FIN SW<7> SW<6> SW<5> SW<4> SW<3> SW<2> SW<1> SWB<7> SWB<6> SWB<5>
+ SWB<4> SWB<3> SWB<2> SWB<1> TG<7> TG<6> TG<5> TG<4> TG<3> TG<2> TG<1> TGB<7>
+ TGB<6> TGB<5> TGB<4> TGB<3> TGB<2> TGB<1> VALIDF FINE_SAR_Logic_V4
XI15 net90 CKSBTIB DVDD DVSS INVD3LVT
XI140 net89 CKSBTI DVDD DVSS INVD3LVT
XI8 CK0 CKF DVDD DVSS OUTNF OUTPF ST_FINB VALIDF VCTINF Fine_Comp_CK_V3
XINV<1> DB<11> DO<11> DVDD DVSS INVD1LVT
XINV<2> DB<10> DO<10> DVDD DVSS INVD1LVT
XINV<3> DB<9> DO<9> DVDD DVSS INVD1LVT
XINV<4> DB<8> DO<8> DVDD DVSS INVD1LVT
XINV<5> DB<7> DO<7> DVDD DVSS INVD1LVT
XI11 ST_FINE ST_FINB DVDD DVSS INVD1LVT
XI10 ST_FINB ST_FIN DVDD DVSS INVD1LVT
XI16 CKSBTB net90 DVDD DVSS INVD1LVT
XI9 CPY CPYB DVDD DVSS INVD1LVT
XI7 DB<9> D_F<9> DVDD DVSS INVD1LVT
XI6 DB<10> D_F<10> DVDD DVSS INVD1LVT
XI5 D<9> DB_F<9> DVDD DVSS INVD1LVT
XI3 D<10> DB_F<10> DVDD DVSS INVD1LVT
XI1 DB<11> D_F<11> DVDD DVSS INVD1LVT
XI17 CKSBT net89 DVDD DVSS INVD1LVT
XI12 AVDD AVSS CKSBT CKSBTB VBTFP VIP BTSW_MOM
XI139 AVDD AVSS CKSBT CKSBTB VBTFN VIN BTSW_MOM
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    12b_ADC
* View Name:    schematic
************************************************************************

.SUBCKT 12b_ADC AVDD AVSS CKS CKSB CKSBT CKSBTB DO<11> DO<10> DO<9> DO<8>
+ DO<7> DVDD DVSS FD<7> FD<6> FD<5> FD<4> FD<3> FD<2> FD<1> FD<0> FIN_RDY N<1>
+ N<2> N<3> N<4> P<1> P<2> P<3> P<4> VCM VCT_DLY VCT_DLYF VIN VIP VRCTL VRN VRP
*.PININFO CKS:I CKSB:I CKSBT:I CKSBTB:I N<1>:I N<2>:I N<3>:I N<4>:I P<1>:I
*.PININFO P<2>:I P<3>:I P<4>:I VCM:I VCT_DLY:I VCT_DLYF:I VIN:I VIP:I VRCTL:I
*.PININFO VRN:I VRP:I DO<11>:O DO<10>:O DO<9>:O DO<8>:O DO<7>:O FD<7>:O
*.PININFO FD<6>:O FD<5>:O FD<4>:O FD<3>:O FD<2>:O FD<1>:O FD<0>:O FIN_RDY:O
*.PININFO AVDD:B AVSS:B DVDD:B DVSS:B
XI0 AVDD AVSS CKS CKSB CKSBT CKSBTB net64 DF<11> DF<10> DF<9> DF<8> DF<7>
+ DFB<11> DFB<10> DFB<9> DFB<8> DFB<7> DVDD DVSS N<1> N<2> N<3> N<4> P<1> P<2>
+ P<3> P<4> net012 VCM VCT_DLY VIN VIP VRCTL VRN VRP 5b_ADC
XI8 AVDD AVSS CKS CKSB CKSBT CKSBTB net64 DF<11> DF<10> DF<9> DF<8> DF<7>
+ DFB<11> DFB<10> DFB<9> DFB<8> DFB<7> DO<11> DO<10> DO<9> DO<8> DO<7> DVDD
+ DVSS FD<7> FD<6> FD<5> FD<4> FD<3> FD<2> FD<1> FD<0> FIN_RDY net012 VCM
+ VCT_DLYF VIN VIP VRCTL VRN VRP 8b_ADC
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    DEL01LVT
* View Name:    schematic
************************************************************************

.SUBCKT DEL01LVT I Z VDD VSS
*.PININFO I:I Z:O VDD:B VSS:B
MMI2-M_u3 Z net5 VDD VDD lvtpfet l=LA w=WV m=1
MMI3 net17 net13 VDD VDD lvtpfet l=LA w=WV m=1
MMI6 net13 net9 net1 VDD lvtpfet l=LA w=WV m=1
MMI1-M_u3 net9 I VDD VDD lvtpfet l=LA w=WV m=1
MMI10 net5 net13 net17 VDD lvtpfet l=LA w=WV m=1
MMI7 net1 net9 VDD VDD lvtpfet l=LA w=WV m=1
MMI13 net17 net13 VSS VSS lvtnfet l=LA w=WP m=1
MMI4 net1 net9 VSS VSS lvtnfet l=LA w=WP m=1
MMI2-M_u2 Z net5 VSS VSS lvtnfet l=LA w=WP m=1
MMI12 net5 net13 net17 VSS lvtnfet l=LA w=WP m=1
MMI5 net13 net9 net1 VSS lvtnfet l=LA w=WP m=1
MMI1-M_u2 net9 I VSS VSS lvtnfet l=LA w=WP m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    CKND4LVT
* View Name:    schematic
************************************************************************

.SUBCKT CKND4LVT I ZN VDD VSS
*.PININFO I:I ZN:O VDD:B VSS:B
MM_u1_0 ZN I VDD VDD lvtpfet l=LA w=WV m=1
MM_u1_3 ZN I VDD VDD lvtpfet l=LA w=WV m=1
MM_u1_2 ZN I VDD VDD lvtpfet l=LA w=WV m=1
MM_u1_1 ZN I VDD VDD lvtpfet l=LA w=WV m=1
MM_u2_1 ZN I VSS VSS lvtnfet l=LA w=WL m=1
MM_u2_3 ZN I VSS VSS lvtnfet l=LA w=WL m=1
MM_u2_0 ZN I VSS VSS lvtnfet l=LA w=WL m=1
MM_u2_2 ZN I VSS VSS lvtnfet l=LA w=WL m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    CKBD1LVT
* View Name:    schematic
************************************************************************

.SUBCKT CKBD1LVT I Z VDD VSS
*.PININFO I:I Z:O VDD:B VSS:B
MM_u15 net5 I VSS VSS lvtnfet l=LA w=WL m=1
MMU23 Z net5 VSS VSS lvtnfet l=LA w=WL m=1
MM_u3 net5 I VDD VDD lvtpfet l=LA w=WV m=1
MMU21 Z net5 VDD VDD lvtpfet l=LA w=WV m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    CKND1LVT
* View Name:    schematic
************************************************************************

.SUBCKT CKND1LVT I ZN VDD VSS
*.PININFO I:I ZN:O VDD:B VSS:B
MM_u2 ZN I VSS VSS lvtnfet l=LA w=WL m=1
MM_u1 ZN I VDD VDD lvtpfet l=LA w=WV m=1
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    ckt_CKGEN
* View Name:    schematic
************************************************************************

.SUBCKT ckt_CKGEN CKIN CKS CKSB CKSBT CKSBTB DVDD DVSS
*.PININFO CKIN:I CKS:O CKSB:O CKSBT:O CKSBTB:O DVDD:B DVSS:B
XI370 CKS CKSD DVDD DVSS DEL01LVT
XI364 net59 CKSB DVDD DVSS CKND4LVT
XI290 net60 CKS DVDD DVSS CKND4LVT
XI189 CKSB CKSD pulse DVDD DVSS NR2D1LVT
XI188 pulse CKSD CKSBTB DVDD DVSS NR2D1LVT
XI373 CKIN net59 DVDD DVSS CKBD1LVT
XI187 CKSBTB CKSBT DVDD DVSS CKND1LVT
XI291 CKIN net60 DVDD DVSS CKND1LVT
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    DFQD1LVT
* View Name:    schematic
************************************************************************

.SUBCKT DFQD1LVT D CP Q VDD VSS
*.PININFO CP:I D:I Q:O VDD:B VSS:B
MMI53-M_u2 net7 net13 VSS VSS lvtnfet l=LA w=WP m=1
MMI4 net24 net63 VSS VSS lvtnfet l=LA w=WO m=1
MMI56 net37 net7 VSS VSS lvtnfet l=LA w=WB m=1
MMI13-M_u2 net11 net67 VSS VSS lvtnfet l=LA w=WP m=1
MMI50 net11 net25 net13 VSS lvtnfet l=LA w=WD m=1
MMI32-M_u2 net25 net63 VSS VSS lvtnfet l=LA w=WC m=1
MMI5 net67 D net24 VSS lvtnfet l=LA w=WO m=1
MMI31-M_u2 net63 CP VSS VSS lvtnfet l=LA w=WC m=1
MMI49 net13 net63 net37 VSS lvtnfet l=LA w=WB m=1
MMI48 net9 net11 VSS VSS lvtnfet l=LA w=WB m=1
MMI27-M_u2 Q net7 VSS VSS lvtnfet l=LA w=WP m=1
MMI47 net67 net25 net9 VSS lvtnfet l=LA w=WB m=1
MMI53-M_u3 net7 net13 VDD VDD lvtpfet l=LA w=WV m=1
MMI32-M_u3 net25 net63 VDD VDD lvtpfet l=LA w=WI m=1
MMI43 net56 net11 VDD VDD lvtpfet l=LA w=WB m=1
MMI6 net67 D net49 VDD lvtpfet l=LA w=WT m=1
MMI31-M_u3 net63 CP VDD VDD lvtpfet l=LA w=WI m=1
MMI27-M_u3 Q net7 VDD VDD lvtpfet l=LA w=WV m=1
MMI57 net13 net25 net72 VDD lvtpfet l=LA w=WB m=1
MMI13-M_u3 net11 net67 VDD VDD lvtpfet l=LA w=WV m=1
MMI52 net11 net63 net13 VDD lvtpfet l=LA w=WI m=1
MMI51 net72 net7 VDD VDD lvtpfet l=LA w=WB m=1
MMI45 net67 net63 net56 VDD lvtpfet l=LA w=WB m=1
MMI7 net49 net25 VDD VDD lvtpfet l=LA w=WT m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    MUX2ND1LVT
* View Name:    schematic
************************************************************************

.SUBCKT MUX2ND1LVT I0 I1 S ZN VDD VSS
*.PININFO I0:I I1:I S:I ZN:O VDD:B VSS:B
MMI15-M_u2 net25 S VSS VSS lvtnfet l=LA w=WC m=1
MMI18-M_u3 net13 net25 net24 VSS lvtnfet l=LA w=WG m=1
MMI16-M_u2 net17 net24 VSS VSS lvtnfet l=LA w=WP m=1
MMI17-M_u2 net13 I0 VSS VSS lvtnfet l=LA w=WG m=1
MMI13-M_u3 net5 S net24 VSS lvtnfet l=LA w=WH m=1
MMI14-M_u2 net5 I1 VSS VSS lvtnfet l=LA w=WP m=1
MMU29-M_u2 ZN net17 VSS VSS lvtnfet l=LA w=WP m=1
MMI17-M_u3 net13 I0 VDD VDD lvtpfet l=LA w=WM m=1
MMI14-M_u3 net5 I1 VDD VDD lvtpfet l=LA w=WV m=1
MMI16-M_u3 net17 net24 VDD VDD lvtpfet l=LA w=WV m=1
MMU29-M_u3 ZN net17 VDD VDD lvtpfet l=LA w=WV m=1
MMI15-M_u3 net25 S VDD VDD lvtpfet l=LA w=WI m=1
MMI13-M_u2 net5 net25 net24 VDD lvtpfet l=LA w=WN m=1
MMI18-M_u2 net13 S net24 VDD lvtpfet l=LA w=WR m=1
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    Data_Collector
* View Name:    schematic
************************************************************************

.SUBCKT Data_Collector CKO CKS D<11> D<10> D<9> D<8> D<7> FD<7> FD<6> FD<5>
+ FD<4> FD<3> FD<2> FD<1> FD<0> DOUT<12> DOUT<11> DOUT<10> DOUT<9> DOUT<8>
+ DOUT<7> DOUT<6> DOUT<5> DOUT<4> DOUT<3> DOUT<2> DOUT<1> DOUT<0> DVDD DVSS
+ FIN_RDY SPI_CHX_CKO
*.PININFO CKS:I D<11>:I D<10>:I D<9>:I D<8>:I D<7>:I FD<7>:I FD<6>:I FD<5>:I
*.PININFO FD<4>:I FD<3>:I FD<2>:I FD<1>:I FD<0>:I FIN_RDY:I SPI_CHX_CKO:I
*.PININFO CKO:O DOUT<12>:O DOUT<11>:O DOUT<10>:O DOUT<9>:O DOUT<8>:O DOUT<7>:O
*.PININFO DOUT<6>:O DOUT<5>:O DOUT<4>:O DOUT<3>:O DOUT<2>:O DOUT<1>:O
*.PININFO DOUT<0>:O DVDD:B DVSS:B
XI11<12> D<11> FINE_RDY DOUT<12> DVDD DVSS DFQD1LVT
XI11<11> D<10> FINE_RDY DOUT<11> DVDD DVSS DFQD1LVT
XI11<10> D<9> FINE_RDY DOUT<10> DVDD DVSS DFQD1LVT
XI11<9> D<8> FINE_RDY DOUT<9> DVDD DVSS DFQD1LVT
XI11<8> D<7> FINE_RDY DOUT<8> DVDD DVSS DFQD1LVT
XI11<7> FD<7> FINE_RDY DOUT<7> DVDD DVSS DFQD1LVT
XI11<6> FD<6> FINE_RDY DOUT<6> DVDD DVSS DFQD1LVT
XI11<5> FD<5> FINE_RDY DOUT<5> DVDD DVSS DFQD1LVT
XI11<4> FD<4> FINE_RDY DOUT<4> DVDD DVSS DFQD1LVT
XI11<3> FD<3> FINE_RDY DOUT<3> DVDD DVSS DFQD1LVT
XI11<2> FD<2> FINE_RDY DOUT<2> DVDD DVSS DFQD1LVT
XI11<1> FD<1> FINE_RDY DOUT<1> DVDD DVSS DFQD1LVT
XI11<0> FD<0> FINE_RDY DOUT<0> DVDD DVSS DFQD1LVT
XI4 net38 net37 DVDD DVSS INVD1LVT
XI0 net07 CKO DVDD DVSS INVD3LVT
XI5 net37 net36 DVDD DVSS INVD3LVT
XI6 net36 FINE_RDY DVDD DVSS INVD8LVT
XI14 FIN_RDY net38 DVDD DVSS INVD0HVT_schematic
XI1 CKS FINE_RDY SPI_CHX_CKO net07 DVDD DVSS MUX2ND1LVT
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    12b_ADC_TOP
* View Name:    schematic
************************************************************************

.SUBCKT Santized_12b_ADC_TOP AVDD AVSS CKO CK_IN DOUT<12> DOUT<11> DOUT<10> DOUT<9>
+ DOUT<8> DOUT<7> DOUT<6> DOUT<5> DOUT<4> DOUT<3> DOUT<2> DOUT<1> DOUT<0> DVDD
+ DVSS N<1> N<2> N<3> N<4> P<1> P<2> P<3> P<4> SPI_CHX_CKO VCM VCT_DLY
+ VCT_DLYF VIN VIP VRCTL VRN VRP
*.PININFO CK_IN:I N<1>:I N<2>:I N<3>:I N<4>:I P<1>:I P<2>:I P<3>:I P<4>:I
*.PININFO SPI_CHX_CKO:I VCM:I VCT_DLY:I VCT_DLYF:I VIN:I VIP:I VRCTL:I VRN:I
*.PININFO VRP:I CKO:O DOUT<12>:O DOUT<11>:O DOUT<10>:O DOUT<9>:O DOUT<8>:O
*.PININFO DOUT<7>:O DOUT<6>:O DOUT<5>:O DOUT<4>:O DOUT<3>:O DOUT<2>:O
*.PININFO DOUT<1>:O DOUT<0>:O AVDD:B AVSS:B DVDD:B DVSS:B
XI0 AVDD AVSS CKS net39 net38 net37 D<11> D<10> D<9> D<8> D<7> DVDD DVSS FD<7>
+ FD<6> FD<5> FD<4> FD<3> FD<2> FD<1> FD<0> net36 N<1> N<2> N<3> N<4> P<1>
+ P<2> P<3> P<4> VCM VCT_DLY VCT_DLYF VIN VIP VRCTL VRN VRP 12b_ADC
XI1 CK_IN CKS net39 net38 net37 DVDD DVSS ckt_CKGEN
XI4 CKO CKS D<11> D<10> D<9> D<8> D<7> FD<7> FD<6> FD<5> FD<4> FD<3> FD<2>
+ FD<1> FD<0> DOUT<12> DOUT<11> DOUT<10> DOUT<9> DOUT<8> DOUT<7> DOUT<6>
+ DOUT<5> DOUT<4> DOUT<3> DOUT<2> DOUT<1> DOUT<0> DVDD DVSS net36 SPI_CHX_CKO
+ Data_Collector
.ENDS


.SUBCKT crtmom PLUS MINUS BULK
*.PININFO  PLUS:B MINUS:B BULK:B
.ENDS

.SUBCKT nmoscap PLUS MINUS
*.PININFO  PLUS:B MINUS:B
.ENDS
