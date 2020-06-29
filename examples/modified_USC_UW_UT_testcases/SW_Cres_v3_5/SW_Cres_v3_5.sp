************************************************************************
* auCdl Netlist:
* 
* Library Name:  ADC_Layout
* Top Cell Name: CDAC_SW_Coarse
* View Name:     schematic
* Netlisted on:  Jun 11 11:23:20 2019
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
MM6 VO VBTSW VIN DVSS nfet_dnw l=LA w=WA m=1
MM5 VO CKSB VCM DVSS nfet_dnw l=LA w=WA m=1
MM2 VO CKS VCM DVDD pfet l=LA w=WA m=1
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    SW1_V2
* View Name:    schematic
************************************************************************

.SUBCKT SW1_V2 D DVDD DVSS SW SWB TG TGB VBTSW VCM VIN VO VREFN VREFP
*.PININFO D:I SW:I SWB:I TG:I TGB:I VCM:I VIN:I VREFN:I VREFP:I VO:O DVDD:B 
*.PININFO DVSS:B VBTSW:B
MM6 VO VBTSW VIN DVSS nfet_dnw l=LA w=WA m=1
MM5 VO TG VCM DVSS nfet_dnw l=LA w=WA m=1
MM4 net22 D VREFN DVSS nfet_dnw l=LA w=WB m=1
MM3 VO SW net22 DVSS nfet_dnw l=LA w=WB m=1
MM2 VO TGB VCM DVDD pfet l=LA w=WA m=1
MM1 VO SWB net23 DVDD pfet l=LA w=WC m=1
MM0 net23 D VREFP DVDD pfet l=LA w=WC m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    ND2D1LVT
* View Name:    schematic
************************************************************************

.SUBCKT ND2D1LVT A1 A2 ZN VDD VSS
*.PININFO A1:I A2:I ZN:O VDD:B VSS:B
MMI1-M_u3 ZN A1 net1 VSS lvtnfet l=LA w=WD m=1
MMI1-M_u4 net1 A2 VSS VSS lvtnfet l=LA w=WD m=1
MMI1-M_u1 ZN A1 VDD VDD lvtpfet l=LA w=WE m=1
MMI1-M_u2 ZN A2 VDD VDD lvtpfet l=LA w=WE m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    INVD0LVT
* View Name:    schematic
************************************************************************

.SUBCKT INVD0LVT I ZN VDD VSS
*.PININFO I:I ZN:O VDD:B VSS:B
MMU1-M_u2 ZN I VSS VSS lvtnfet l=LA w=WB m=1
MMU1-M_u3 ZN I VDD VDD lvtpfet l=LA w=WC m=1
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    SW_Cres_v3_6
* View Name:    schematic
************************************************************************

.SUBCKT SW_Cres_v3_6 CK DVDD DVSS VRCTL VRN VRNX VRP VRPX
*.PININFO VRCTL:I CK:B DVDD:B DVSS:B VRN:B VRNX:B VRP:B VRPX:B
MM3 VRN CLK VRN DVSS nfet l=LA w=WA m=1
MM2 VRN net010 VRNX DVSS nfet l=LA w=WF m=1
MM4 VRP net018 VRP DVDD pfet l=LA w=WA m=1
MM1 VRP CLK VRPX DVDD pfet l=LA w=WF m=1
XI11 CK VRCTL net010 DVDD DVSS / ND2D1LVT
XI5 CLK net018 DVDD DVSS / INVD0LVT
XI6 net010 CLK DVDD DVSS / INVD0LVT
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    SW_Cres_v3_5
* View Name:    schematic
************************************************************************

.SUBCKT SW_Cres_v3_5 CK DVDD DVSS VRCTL VRN VRNX VRP VRPX
*.PININFO VRCTL:I CK:B DVDD:B DVSS:B VRN:B VRNX:B VRP:B VRPX:B
MM3 VRN CLK VRN DVSS nfet l=LA w=WA m=1
MM2 VRN net010 VRNX DVSS nfet l=LA w=WF m=1
MM4 VRP net018 VRP DVDD pfet l=LA w=WA m=1
MM1 VRP CLK VRPX DVDD pfet l=LA w=WF m=1
XI11 CK VRCTL net010 DVDD DVSS / ND2D1LVT
XI5 CLK net018 DVDD DVSS / INVD0LVT
XI6 net010 CLK DVDD DVSS / INVD0LVT
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    SW2_V2
* View Name:    schematic
************************************************************************

.SUBCKT SW2_V2 D DVDD DVSS SW SWB TG TGB VBTSW VCM VIN VO VREFN VREFP
*.PININFO D:I SW:I SWB:I TG:I TGB:I VCM:I VIN:I VREFN:I VREFP:I VO:O DVDD:B 
*.PININFO DVSS:B VBTSW:B
MM6 VO VBTSW VIN DVSS nfet_dnw l=LA w=WA m=1
MM5 VO TG VCM DVSS nfet_dnw l=LA w=WA m=1
MM4 net22 D VREFN DVSS nfet_dnw l=LA w=WD m=1
MM3 VO SW net22 DVSS nfet_dnw l=LA w=WD m=1
MM2 VO TGB VCM DVDD pfet l=LA w=WA m=1
MM1 VO SWB net23 DVDD pfet l=LA w=WE m=1
MM0 net23 D VREFP DVDD pfet l=LA w=WE m=1
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    SW3_V2
* View Name:    schematic
************************************************************************

.SUBCKT SW3_V2 D DVDD DVSS SW SWB TG TGB VBTSW VCM VIN VO VREFN VREFP
*.PININFO D:I SW:I SWB:I TG:I TGB:I VCM:I VIN:I VREFN:I VREFP:I VO:O DVDD:B 
*.PININFO DVSS:B VBTSW:B
MM6 VO VBTSW VIN DVSS nfet_dnw l=LA w=WA m=1
MM5 VO TG VCM DVSS nfet_dnw l=LA w=WA m=1
MM4 net22 D VREFN DVSS nfet_dnw l=LA w=WD m=2
MM3 VO SW net22 DVSS nfet_dnw l=LA w=WD m=2
MM2 VO TGB VCM DVDD pfet l=LA w=WA m=1
MM1 VO SWB net23 DVDD pfet l=LA w=WE m=2
MM0 net23 D VREFP DVDD pfet l=LA w=WE m=2
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    SW4_V2
* View Name:    schematic
************************************************************************

.SUBCKT SW4_V2 D DVDD DVSS SW SWB TG TGB VBTSW VCM VIN VO VREFN VREFP
*.PININFO D:I SW:I SWB:I TG:I TGB:I VCM:I VIN:I VREFN:I VREFP:I VO:O DVDD:B 
*.PININFO DVSS:B VBTSW:B
MM6 VO VBTSW VIN DVSS nfet_dnw l=LA w=WA m=1
MM5 VO TG VCM DVSS nfet_dnw l=LA w=WG m=1
MM4 net22 D VREFN DVSS nfet_dnw l=LA w=WD m=4
MM3 VO SW net22 DVSS nfet_dnw l=LA w=WD m=4
MM2 VO TGB VCM DVDD pfet l=LA w=WG m=1
MM1 VO SWB net23 DVDD pfet l=LA w=WE m=4
MM0 net23 D VREFP DVDD pfet l=LA w=WE m=4
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    TG_Top_Coarse
* View Name:    schematic
************************************************************************

.SUBCKT TG_Top_Coarse CKS CKSB DVDD DVSS VCM VO
*.PININFO CKS:I CKSB:I VCM:I VO:O DVDD:B DVSS:B
MM5 VO CKS VCM DVSS lvtnfet l=LA w=WH m=2
MM2 VO CKSB VCM DVDD lvtpfet l=LA w=WH m=2
.ENDS

************************************************************************
* Library Name: ADC_Layout
* Cell Name:    CDAC_SW_Coarse
* View Name:    schematic
************************************************************************

.SUBCKT Sanitized_CDAC_SW_Coarse C<11> C<10> C<9> C<8> C<7> CK<11> CK<10> CK<9> CK<8> 
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
XI2 CKSBT CKSBTB DVDD DVSS VBTN VCM VIN C<7> / SW1_Dummy_V2
XI3 D<8> DVDD DVSS SWC<8> SWCB<8> TGC<8> TGCB<8> VBTN VCM VIN C<8> VRN<8> 
+ VRP<8> / SW1_V2
XI0 CK<11> DVDD DVSS VRCTL VRN<11> VRNX VRP<11> VRPX / SW_Cres_v3_6
XI4 CK<10> DVDD DVSS VRCTL VRN<10> VRNX VRP<10> VRPX / SW_Cres_v3_6
XCr11<0> CK<11> DVDD DVSS VRCTL VRN<11> VRNX VRP<11> VRPX / SW_Cres_v3_5
XCr11<1> CK<11> DVDD DVSS VRCTL VRN<11> VRNX VRP<11> VRPX / SW_Cres_v3_5
XCr11<2> CK<11> DVDD DVSS VRCTL VRN<11> VRNX VRP<11> VRPX / SW_Cres_v3_5
XCr11<3> CK<11> DVDD DVSS VRCTL VRN<11> VRNX VRP<11> VRPX / SW_Cres_v3_5
XI1 CK<10> DVDD DVSS VRCTL VRN<10> VRNX VRP<10> VRPX / SW_Cres_v3_5
XI6 CK<9> DVDD DVSS VRCTL VRN<9> VRNX VRP<9> VRPX / SW_Cres_v3_5
XSW<0> CK<8> DVDD DVSS VRCTL VRN<8> VRNX VRP<8> VRPX / SW_Cres_v3_5
XSW<1> CK<8> DVDD DVSS VRCTL VRN<8> VRNX VRP<8> VRPX / SW_Cres_v3_5
XI8 D<9> DVDD DVSS SWC<9> SWCB<9> TGC<9> TGCB<9> VBTN VCM VIN C<9> VRN<9> 
+ VRP<9> / SW2_V2
XI9 D<10> DVDD DVSS SWC<10> SWCB<10> TGC<10> TGCB<10> VBTN VCM VIN C<10> 
+ VRN<10> VRP<10> / SW3_V2
XI10 D<11> DVDD DVSS SWC<11> SWCB<11> TGC<11> TGCB<11> VBTN VCM VIN C<11> 
+ VRN<11> VRP<11> / SW4_V2
XI5 CKS CKSB DVDD DVSS VCM VCP / TG_Top_Coarse
.ENDS


.SUBCKT nmoscap PLUS MINUS 
*.PININFO  PLUS:B MINUS:B
.ENDS
