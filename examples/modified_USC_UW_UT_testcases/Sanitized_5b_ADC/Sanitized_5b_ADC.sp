************************************************************************
* auCdl Netlist:
*
* Library Name:  ADC_Layout
* Top Cell Name: 5b_ADC
* View Name:     schematic
* Netlisted on:  Jul 19 10:12:56 2019
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
MM6 VO VBTSW VIN DVSS nch_dnw l=LA w=WG m=1
MM5 VO CKSB VCM DVSS nch_dnw l=LA w=WG m=1
MM2 VO CKS VCM DVDD pch l=LA w=WG m=1
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    SW1_V2
* View Name:    schematic
************************************************************************

.SUBCKT SW1_V2 D DVDD DVSS SW SWB TG TGB VBTSW VCM VIN VO VREFN VREFP
*.PININFO D:I SW:I SWB:I TG:I TGB:I VCM:I VIN:I VREFN:I VREFP:I VO:O DVDD:B
*.PININFO DVSS:B VBTSW:B
MM6 VO VBTSW VIN DVSS nch_dnw l=LA w=WG m=1
MM5 VO TG VCM DVSS nch_dnw l=LA w=WG m=1
MM4 net22 D VREFN DVSS nch_dnw l=LA w=WF m=1
MM3 VO SW net22 DVSS nch_dnw l=LA w=WF m=1
MM2 VO TGB VCM DVDD pch l=LA w=WG m=1
MM1 VO SWB net23 DVDD pch l=LA w=WE m=1
MM0 net23 D VREFP DVDD pch l=LA w=WE m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    ND2D1LVT
* View Name:    schematic
************************************************************************

.SUBCKT ND2D1LVT A1 A2 ZN VDD VSS
*.PININFO A1:I A2:I ZN:O VDD:B VSS:B
MMI1_M_u3 ZN A1 net1 VSS lvtnfet l=LA w=WC m=1
MMI1_M_u4 net1 A2 VSS VSS lvtnfet l=LA w=WC m=1
MMI1_M_u1 ZN A1 VDD VDD lvtpfet l=LA w=WD m=1
MMI1_M_u2 ZN A2 VDD VDD lvtpfet l=LA w=WD m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    INVD0LVT
* View Name:    schematic
************************************************************************

.SUBCKT INVD0LVT I ZN VDD VSS
*.PININFO I:I ZN:O VDD:B VSS:B
MMU1_M_u2 ZN I VSS VSS lvtnfet l=LA w=WF m=1
MMU1_M_u3 ZN I VDD VDD lvtpfet l=LA w=WE m=1
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    SW_Cres_v3_6
* View Name:    schematic
************************************************************************

.SUBCKT SW_Cres_v3_6 CK DVDD DVSS VRCTL VRN VRNX VRP VRPX
*.PININFO VRCTL:I CK:B DVDD:B DVSS:B VRN:B VRNX:B VRP:B VRPX:B
MM3 VRN CLK VRN DVSS nch l=LA w=WG m=1
MM2 VRN net010 VRNX DVSS nch l=LA w=WA m=1
MM4 VRP net018 VRP DVDD pch l=LA w=WG m=1
MM1 VRP CLK VRPX DVDD pch l=LA w=WA m=1
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
MM3 VRN CLK VRN DVSS nch l=LA w=WG m=1
MM2 VRN net010 VRNX DVSS nch l=LA w=WA m=1
MM4 VRP net018 VRP DVDD pch l=LA w=WG m=1
MM1 VRP CLK VRPX DVDD pch l=LA w=WA m=1
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
MM6 VO VBTSW VIN DVSS nch_dnw l=LA w=WG m=1
MM5 VO TG VCM DVSS nch_dnw l=LA w=WG m=1
MM4 net22 D VREFN DVSS nch_dnw l=LA w=WC m=1
MM3 VO SW net22 DVSS nch_dnw l=LA w=WC m=1
MM2 VO TGB VCM DVDD pch l=LA w=WG m=1
MM1 VO SWB net23 DVDD pch l=LA w=WD m=1
MM0 net23 D VREFP DVDD pch l=LA w=WD m=1
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    SW3_V2
* View Name:    schematic
************************************************************************

.SUBCKT SW3_V2 D DVDD DVSS SW SWB TG TGB VBTSW VCM VIN VO VREFN VREFP
*.PININFO D:I SW:I SWB:I TG:I TGB:I VCM:I VIN:I VREFN:I VREFP:I VO:O DVDD:B
*.PININFO DVSS:B VBTSW:B
MM6 VO VBTSW VIN DVSS nch_dnw l=LA w=WG m=1
MM5 VO TG VCM DVSS nch_dnw l=LA w=WG m=1
MM4 net22 D VREFN DVSS nch_dnw l=LA w=WC m=2
MM3 VO SW net22 DVSS nch_dnw l=LA w=WC m=2
MM2 VO TGB VCM DVDD pch l=LA w=WG m=1
MM1 VO SWB net23 DVDD pch l=LA w=WD m=2
MM0 net23 D VREFP DVDD pch l=LA w=WD m=2
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    SW4_V2
* View Name:    schematic
************************************************************************

.SUBCKT SW4_V2 D DVDD DVSS SW SWB TG TGB VBTSW VCM VIN VO VREFN VREFP
*.PININFO D:I SW:I SWB:I TG:I TGB:I VCM:I VIN:I VREFN:I VREFP:I VO:O DVDD:B
*.PININFO DVSS:B VBTSW:B
MM6 VO VBTSW VIN DVSS nch_dnw l=LA w=WG m=1
MM5 VO TG VCM DVSS nch_dnw l=LA w=WJ m=1
MM4 net22 D VREFN DVSS nch_dnw l=LA w=WC m=4
MM3 VO SW net22 DVSS nch_dnw l=LA w=WC m=4
MM2 VO TGB VCM DVDD pch l=LA w=WJ m=1
MM1 VO SWB net23 DVDD pch l=LA w=WD m=4
MM0 net23 D VREFP DVDD pch l=LA w=WD m=4
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    TG_Top_Coarse
* View Name:    schematic
************************************************************************

.SUBCKT TG_Top_Coarse CKS CKSB DVDD DVSS VCM VO
*.PININFO CKS:I CKSB:I VCM:I VO:O DVDD:B DVSS:B
MM5 VO CKS VCM DVSS lvtnfet_dnw l=LA w=WF m=2
MM2 VO CKSB VCM DVDD lvtpfet l=LA w=WF m=2
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
MM2 QN CK NET4 DGND nch_hvt l=LA w=WC m=1
MM7 Q QN DGND DGND nch_hvt l=LA w=WC m=1
MM14 NET3 CK DGND DGND nch_hvt l=LA w=WG m=1
MM4 NET2 N1 NET3 DGND nch_hvt l=LA w=WG m=1
MM13 N1 D DGND DGND nch_hvt l=LA w=WG m=1
MM3 NET4 NET2 DGND DGND nch_hvt l=LA w=WC m=1
MM12 Q QN DVDD DVDD pch_hvt l=LA w=WD m=1
MM11 QN NET2 DVDD DVDD pch_hvt l=LA w=WD m=1
MM9 NET2 CK DVDD DVDD pch_hvt l=LA w=WG m=1
MM8 NET1 D DVDD DVDD pch_hvt l=LA w=WG m=1
MM15 N1 CK NET1 DVDD pch_hvt l=LA w=WG m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    INVD1LVT
* View Name:    schematic
************************************************************************

.SUBCKT INVD1LVT I ZN VDD VSS
*.PININFO I:I ZN:O VDD:B VSS:B
MMU1_M_u2 ZN I VSS VSS lvtnfet l=LA w=WC m=1
MMU1_M_u3 ZN I VDD VDD lvtpfet l=LA w=WD m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    TIEHLVT
* View Name:    schematic
************************************************************************

.SUBCKT TIEHLVT Z VDD VSS
*.PININFO Z:O VDD:B VSS:B
MM_u2 net7 net7 VSS VSS lvtnfet l=LA w=WH m=1
MM_u1 Z net7 VDD VDD lvtpfet l=LA w=WI m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    NR2D1LVT
* View Name:    schematic
************************************************************************

.SUBCKT NR2D1LVT A1 A2 ZN VDD VSS
*.PININFO A1:I A2:I ZN:O VDD:B VSS:B
MMI1_M_u3 ZN A2 VSS VSS lvtnfet l=LA w=WC m=1
MMI1_M_u4 ZN A1 VSS VSS lvtnfet l=LA w=WC m=1
MMI1_M_u1 net13 A2 VDD VDD lvtpfet l=LA w=WD m=1
MMI1_M_u2 ZN A1 net13 VDD lvtpfet l=LA w=WD m=1
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    DFFRB_B_V6_HVT
* View Name:    schematic
************************************************************************

.SUBCKT DFFRB_B_V6_HVT CK D DVDD DVSS Q RST
*.PININFO CK:I D:I RST:I Q:O DVDD:B DVSS:B
MM8 NET1 D DVDD DVDD pch_hvt l=LA w=WG m=1
MM10 NET2 CK net58 DVDD pch_hvt l=LA w=WG m=1
MM19 net58 RSTB DVDD DVDD pch_hvt l=LA w=WG m=1
MM15 net06 RST DVDD DVDD pch_hvt l=LA w=WF m=1
MM9 M1 CK NET1 DVDD pch_hvt l=LA w=WG m=1
MM14 Q net06 DVDD DVDD pch_hvt l=LA w=WD m=1
MM12 net06 NET2 DVDD DVDD pch_hvt l=LA w=WD m=1
MM0 RSTB RST DVDD DVDD pch_hvt l=LA w=WE m=1
MM16 NET3 CK DVSS DVSS nch_hvt l=LA w=WG m=1
MM13 NET4 NET2 DVSS DVSS nch_hvt l=LA w=WC m=1
MM7 Q net06 DVSS DVSS nch_hvt l=LA w=WC m=1
MM6 net06 CK NET4 DVSS nch_hvt l=LA w=WC m=1
MM17 M1 D DVSS DVSS nch_hvt l=LA w=WG m=1
MM5 NET2 RSTB DVSS DVSS nch_hvt l=LA w=WG m=1
MM4 NET2 M1 NET3 DVSS nch_hvt l=LA w=WG m=1
MM18 RSTB RST DVSS DVSS nch_hvt l=LA w=WF m=1
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
MMU1_0_M_u3 ZN I VDD VDD lvtpfet l=LA w=WD m=1
MMU1_1_M_u3 ZN I VDD VDD lvtpfet l=LA w=WD m=1
MMU1_0_M_u2 ZN I VSS VSS lvtnfet_dnw l=LA w=WC m=1
MMU1_1_M_u2 ZN I VSS VSS lvtnfet_dnw l=LA w=WC m=1
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    INVD1LVT_schematic
* View Name:    schematic
************************************************************************

.SUBCKT INVD1LVT_schematic I ZN VDD VSS
*.PININFO I:I ZN:O VDD:B VSS:B
MMU1_M_u3 ZN I VDD VDD lvtpfet l=LA w=WD m=1
MMU1_M_u2 ZN I VSS VSS lvtnfet_dnw l=LA w=WC m=1
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    INVD0HVT
* View Name:    schematic
************************************************************************

.SUBCKT INVD0HVT I ZN VDD VSS
*.PININFO I:I ZN:O VDD:B VSS:B
MMU1_M_u3 ZN I VDD VDD pch_hvt l=LA w=WE m=1
MMU1_M_u2 ZN I VSS VSS nch_hvt_dnw l=LA w=WF m=1
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
MM17 net29 net041 net29 AVSS nch_hvt_dnw l=LB w=WA m=2
MM16 net29 net040 net29 AVSS nch_hvt_dnw l=LB w=WB m=3
MM15 net29 net043 net29 AVSS nch_hvt_dnw l=LB w=WA m=1
MM14 net29 net042 net29 AVSS nch_hvt_dnw l=LB w=WG m=1
MM13 net017 net036 net017 AVSS nch_hvt_dnw l=LB w=WG m=1
MM12 net017 net037 net017 AVSS nch_hvt_dnw l=LB w=WA m=1
MM11 net017 net038 net017 AVSS nch_hvt_dnw l=LB w=WA m=2
MM10 net017 net027 net017 AVSS nch_hvt_dnw l=LB w=WB m=3
MM9 net15 CKC AVDD AVDD lvtpfet l=LB w=WE m=2
MM8 net19 CKC AVDD AVDD lvtpfet l=LB w=WE m=2
MM7 net15 net19 AVDD AVDD lvtpfet l=LB w=WE m=2
MM6 net19 net15 AVDD AVDD lvtpfet l=LB w=WE m=2
XI3 net026 OUTNC AVDD AVSS INVD2LVT
XI2 net025 OUTPC AVDD AVSS INVD2LVT
XI1 net15 net025 AVDD AVSS INVD1LVT_schematic
XI0 net19 net026 AVDD AVSS INVD1LVT_schematic
MM5 net15 CKC net27 AVSS lvtnfet_dnw l=LC w=WB m=2
MM4 net19 CKC net28 AVSS lvtnfet_dnw l=LC w=WB m=2
MM3 net27 net19 net29 AVSS lvtnfet_dnw l=LD w=WB m=1
MM2 net28 net15 net017 AVSS lvtnfet_dnw l=LD w=WB m=1
MM1 net29 VCN AVSS AVSS lvtnfet_dnw l=LB w=WB m=2
MM0 net017 VCP AVSS AVSS lvtnfet_dnw l=LB w=WB m=2
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
MM4 ZN I net11 VSS nch_hvt l=LA w=WF m=1
MM1 net11 P VSS VSS nch_hvt l=LA w=WF m=1
MM3 net09 VSS VDD VDD pch_hvt l=LA w=WE m=1
MM0 ZN I net09 VDD pch_hvt l=LA w=WE m=1
.ENDS

************************************************************************
* Library Name: monkey2
* Cell Name:    INVD0HVT_schematic
* View Name:    schematic
************************************************************************

.SUBCKT INVD0HVT_schematic I ZN VDD VSS
*.PININFO I:I ZN:O VDD:B VSS:B
MMU1_M_u2 ZN I VSS VSS nch_hvt l=LA w=WF m=1
MMU1_M_u3 ZN I VDD VDD pch_hvt l=LA w=WE m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    ND2D3LVT
* View Name:    schematic
************************************************************************

.SUBCKT ND2D3LVT A1 A2 ZN VDD VSS
*.PININFO A1:I A2:I ZN:O VDD:B VSS:B
MMU3_0_M_u4 net21 A2 VSS VSS lvtnfet l=LA w=WC m=1
MMU3_1_M_u3 ZN A1 net20 VSS lvtnfet l=LA w=WC m=1
MMU3_2_M_u4 net13 A2 VSS VSS lvtnfet l=LA w=WC m=1
MMU3_1_M_u4 net20 A2 VSS VSS lvtnfet l=LA w=WC m=1
MMU3_0_M_u3 ZN A1 net21 VSS lvtnfet l=LA w=WC m=1
MMU3_2_M_u3 ZN A1 net13 VSS lvtnfet l=LA w=WC m=1
MMU3_2_M_u1 ZN A1 VDD VDD lvtpfet l=LA w=WD m=1
MMU3_1_M_u1 ZN A1 VDD VDD lvtpfet l=LA w=WD m=1
MMU3_1_M_u2 ZN A2 VDD VDD lvtpfet l=LA w=WD m=1
MMU3_2_M_u2 ZN A2 VDD VDD lvtpfet l=LA w=WD m=1
MMU3_0_M_u2 ZN A2 VDD VDD lvtpfet l=LA w=WD m=1
MMU3_0_M_u1 ZN A1 VDD VDD lvtpfet l=LA w=WD m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    NR3D1LVT
* View Name:    schematic
************************************************************************

.SUBCKT NR3D1LVT A1 A2 A3 ZN VDD VSS
*.PININFO A1:I A2:I A3:I ZN:O VDD:B VSS:B
MMI1_1 ZN A1 net5 VDD lvtpfet l=LA w=WD m=1
MM_u1_0 net17 A3 VDD VDD lvtpfet l=LA w=WD m=1
MMI1_0 ZN A1 net9 VDD lvtpfet l=LA w=WD m=1
MMI0_0 net9 A2 net17 VDD lvtpfet l=LA w=WD m=1
MMI0_1 net5 A2 net1 VDD lvtpfet l=LA w=WD m=1
MM_u1_1 net1 A3 VDD VDD lvtpfet l=LA w=WD m=1
MMI3 ZN A1 VSS VSS lvtnfet l=LA w=WC m=1
MMI2 ZN A2 VSS VSS lvtnfet l=LA w=WC m=1
MM_u4 ZN A3 VSS VSS lvtnfet l=LA w=WC m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    INVD2LVT_schematic
* View Name:    schematic
************************************************************************

.SUBCKT INVD2LVT_schematic I ZN VDD VSS
*.PININFO I:I ZN:O VDD:B VSS:B
MMU1_0_M_u2 ZN I VSS VSS lvtnfet l=LA w=WC m=1
MMU1_1_M_u2 ZN I VSS VSS lvtnfet l=LA w=WC m=1
MMU1_0_M_u3 ZN I VDD VDD lvtpfet l=LA w=WD m=1
MMU1_1_M_u3 ZN I VDD VDD lvtpfet l=LA w=WD m=1
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
MMU1_0_M_u2 ZN I VSS VSS lvtnfet l=LA w=WC m=1
MMU1_1_M_u2 ZN I VSS VSS lvtnfet l=LA w=WC m=1
MMU1_2_M_u2 ZN I VSS VSS lvtnfet l=LA w=WC m=1
MMU1_0_M_u3 ZN I VDD VDD lvtpfet l=LA w=WD m=1
MMU1_1_M_u3 ZN I VDD VDD lvtpfet l=LA w=WD m=1
MMU1_2_M_u3 ZN I VDD VDD lvtpfet l=LA w=WD m=1
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    BTSW
* View Name:    schematic
************************************************************************

.SUBCKT BTSW AVDD AVSS CKSBT CKSBTB VBTSW VIN
*.PININFO CKSBT:I CKSBTB:I VIN:I AVDD:B AVSS:B VBTSW:B
MM9 VBTSW net7 net12 net12 pch l=LA w=WB m=1
MM8 AVDD VBTSW net12 net12 pch l=LA w=WB m=1
MM7 net7 CKSBT AVDD AVDD pch l=LA w=WB m=1
MM10 net013 net12 net013 AVSS nch l=1u w=2u m=4
MM6 net27 CKSBTB AVSS AVSS nch l=LA w=WA m=1
MM5 VBTSW AVDD net27 AVSS nch l=LA w=WA m=1
MM3 VIN VBTSW net013 AVSS nch l=LA w=WA m=1
MM2 net7 VBTSW net013 AVSS nch l=LA w=WA m=1
MM1 net013 CKSBTB AVSS AVSS nch l=LA w=WA m=1
MM0 net7 CKSBT net013 AVSS nch l=LA w=WA m=1
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    5b_ADC
* View Name:    schematic
************************************************************************

.SUBCKT Sanitized_5b_ADC AVDD AVSS CKS CKSB CKSBT CKSBTB CPY DF<11> DF<10> DF<9> DF<8>
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


.SUBCKT nmoscap PLUS MINUS
*.PININFO  PLUS:B MINUS:B
.ENDS
