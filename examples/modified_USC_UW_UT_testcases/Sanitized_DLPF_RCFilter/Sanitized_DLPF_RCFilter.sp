************************************************************************
* auCdl Netlist:
* 
* Library Name:  TempSensorLayout_PostLayout
* Top Cell Name: PP_RCFilter
* View Name:     schematic
* Netlisted on:  May 17 01:25:37 2019
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
* Library Name: TempSensorLayout
* Cell Name:    SwitchCap_256X
* View Name:    schematic
************************************************************************

.SUBCKT SwitchCap_256X VDD VSS Vctl0 Vctlin Von Vop
*.PININFO Vctl0:I Vctlin:I VDD:B VSS:B Von:B Vop:B
MM5 Von Vctlin net3 VSS lvtnfet l=LA w=WA m=1
MM0 net4 Vctl0 VSS VSS lvtnfet l=LA w=WA m=1
MM4 net3 Vctl0 VSS VSS lvtnfet l=LA w=WA m=1
MM3 Vop Vctlin net4 VSS lvtnfet l=LA w=WA m=1
MM2 net4 Vctl0 Vop VDD lvtpfet l=LA w=WB m=1
MM1 net3 Vctl0 Von VDD lvtpfet l=LA w=WB m=1
.ENDS

************************************************************************
* Library Name: TempSensorLayout
* Cell Name:    SwitchCap_128X
* View Name:    schematic
************************************************************************

.SUBCKT SwitchCap_128X VDD VSS Vctl0 Vctlin Von Vop
*.PININFO Vctl0:I Vctlin:I VDD:B VSS:B Von:B Vop:B
MM5 Von Vctlin net3 VSS lvtnfet l=LA w=WD m=1
MM0 net4 Vctl0 VSS VSS lvtnfet l=LA w=WD m=1
MM4 net3 Vctl0 VSS VSS lvtnfet l=LA w=WD m=1
MM3 Vop Vctlin net4 VSS lvtnfet l=LA w=WD m=1
MM2 net4 Vctl0 Vop VDD lvtpfet l=LA w=WC m=1
MM1 net3 Vctl0 Von VDD lvtpfet l=LA w=WC m=1
.ENDS

************************************************************************
* Library Name: TempSensorLayout
* Cell Name:    SwitchCap_64X
* View Name:    schematic
************************************************************************

.SUBCKT SwitchCap_64X VDD VSS Vctl0 Vctlin Von Vop
*.PININFO Vctl0:I Vctlin:I VDD:B VSS:B Von:B Vop:B
MM5 Von Vctlin net3 VSS lvtnfet l=LA w=WE m=1
MM0 net4 Vctl0 VSS VSS lvtnfet l=LA w=WE m=1
MM4 net3 Vctl0 VSS VSS lvtnfet l=LA w=WE m=1
MM3 Vop Vctlin net4 VSS lvtnfet l=LA w=WE m=1
MM2 net4 Vctl0 Vop VDD lvtpfet l=LA w=WF m=1
MM1 net3 Vctl0 Von VDD lvtpfet l=LA w=WF m=1
.ENDS

************************************************************************
* Library Name: TempSensorLayout
* Cell Name:    SwitchCap_32X
* View Name:    schematic
************************************************************************

.SUBCKT SwitchCap_32X VDD VSS Vctl0 Vctlin Von Vop
*.PININFO Vctl0:I Vctlin:I VDD:B VSS:B Von:B Vop:B
MM5 Von Vctlin net3 VSS lvtnfet l=LA w=WG m=1
MM0 net4 Vctl0 VSS VSS lvtnfet l=LA w=WG m=1
MM4 net3 Vctl0 VSS VSS lvtnfet l=LA w=WG m=1
MM3 Vop Vctlin net4 VSS lvtnfet l=LA w=WG m=1
MM2 net4 Vctl0 Vop VDD lvtpfet l=LA w=WH m=1
MM1 net3 Vctl0 Von VDD lvtpfet l=LA w=WH m=1
.ENDS

************************************************************************
* Library Name: TempSensorLayout
* Cell Name:    SwitchCap_16X
* View Name:    schematic
************************************************************************

.SUBCKT SwitchCap_16X VDD VSS Vctl0 Vctlin Von Vop
*.PININFO Vctl0:I Vctlin:I VDD:B VSS:B Von:B Vop:B
MM5 Von Vctlin net3 VSS lvtnfet l=LA w=WI m=1
MM0 net4 Vctl0 VSS VSS lvtnfet l=LA w=WI m=1
MM4 net3 Vctl0 VSS VSS lvtnfet l=LA w=WI m=1
MM3 Vop Vctlin net4 VSS lvtnfet l=LA w=WI m=1
MM2 net4 Vctl0 Vop VDD lvtpfet l=LA w=WJ m=1
MM1 net3 Vctl0 Von VDD lvtpfet l=LA w=WJ m=1
.ENDS

************************************************************************
* Library Name: TempSensorLayout
* Cell Name:    SwitchCap_8X
* View Name:    schematic
************************************************************************

.SUBCKT SwitchCap_8X VDD VSS Vctl0 Vctlin Von Vop
*.PININFO Vctl0:I Vctlin:I VDD:B VSS:B Von:B Vop:B
MM5 Von Vctlin net3 VSS lvtnfet l=LA w=WL m=1
MM0 net4 Vctl0 VSS VSS lvtnfet l=LA w=WL m=1
MM4 net3 Vctl0 VSS VSS lvtnfet l=LA w=WL m=1
MM3 Vop Vctlin net4 VSS lvtnfet l=LA w=WL m=1
MM2 net4 Vctl0 Vop VDD lvtpfet l=LA w=WK m=1
MM1 net3 Vctl0 Von VDD lvtpfet l=LA w=WK m=1
.ENDS

************************************************************************
* Library Name: TempSensorLayout
* Cell Name:    SwitchCap_4X
* View Name:    schematic
************************************************************************

.SUBCKT SwitchCap_4X VDD VSS Vctl0 Vctlin Von Vop
*.PININFO Vctl0:I Vctlin:I VDD:B VSS:B Von:B Vop:B
MM5 Von Vctlin net3 VSS lvtnfet l=LA w=WM m=1
MM0 net4 Vctl0 VSS VSS lvtnfet l=LA w=WM m=1
MM4 net3 Vctl0 VSS VSS lvtnfet l=LA w=WM m=1
MM3 Vop Vctlin net4 VSS lvtnfet l=LA w=WM m=1
MM2 net4 Vctl0 Vop VDD lvtpfet l=LA w=WN m=1
MM1 net3 Vctl0 Von VDD lvtpfet l=LA w=WN m=1
.ENDS

************************************************************************
* Library Name: TempSensorLayout
* Cell Name:    SwitchCap_2X
* View Name:    schematic
************************************************************************

.SUBCKT SwitchCap_2X VDD VSS Vctl0 Vctlin Von Vop
*.PININFO Vctl0:I Vctlin:I VDD:B VSS:B Von:B Vop:B
MM5 Von Vctlin net3 VSS lvtnfet l=LA w=WM m=1
MM0 net4 Vctl0 VSS VSS lvtnfet l=LA w=WM m=1
MM4 net3 Vctl0 VSS VSS lvtnfet l=LA w=WM m=1
MM3 Vop Vctlin net4 VSS lvtnfet l=LA w=WM m=1
MM2 net4 Vctl0 Vop VDD lvtpfet l=LA w=WN m=1
MM1 net3 Vctl0 Von VDD lvtpfet l=LA w=WN m=1
.ENDS

************************************************************************
* Library Name: TempSensorLayout
* Cell Name:    SwitchCap_1X
* View Name:    schematic
************************************************************************

.SUBCKT SwitchCap_1X VDD VSS Vctl0 Vctlin Von Vop
*.PININFO Vctl0:I Vctlin:I VDD:B VSS:B Von:B Vop:B
MM5 Von Vctlin net3 VSS lvtnfet l=LA w=WM m=1
MM0 net4 Vctl0 VSS VSS lvtnfet l=LA w=WM m=1
MM4 net3 Vctl0 VSS VSS lvtnfet l=LA w=WM m=1
MM3 Vop Vctlin net4 VSS lvtnfet l=LA w=WM m=1
MM2 net4 Vctl0 Vop VDD lvtpfet l=LA w=WN m=1
MM1 net3 Vctl0 Von VDD lvtpfet l=LA w=WN m=1
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
XI14<0> VDD VSS VCTL0<8> VCTLIN<8> VCN VCP / SwitchCap_256X
XI14<1> VDD VSS VCTL0<8> VCTLIN<8> VCN VCP / SwitchCap_256X
XI14<2> VDD VSS VCTL0<8> VCTLIN<8> VCN VCP / SwitchCap_256X
XI14<3> VDD VSS VCTL0<8> VCTLIN<8> VCN VCP / SwitchCap_256X
XI9<0> VDD VSS VCTL0<8> VCTLIN<8> VCN VCP / SwitchCap_256X
XI9<1> VDD VSS VCTL0<8> VCTLIN<8> VCN VCP / SwitchCap_256X
XI9<2> VDD VSS VCTL0<8> VCTLIN<8> VCN VCP / SwitchCap_256X
XI9<3> VDD VSS VCTL0<8> VCTLIN<8> VCN VCP / SwitchCap_256X
XI6<0> VDD VSS VCTL0<8> VCTLIN<8> VCN VCP / SwitchCap_256X
XI6<1> VDD VSS VCTL0<8> VCTLIN<8> VCN VCP / SwitchCap_256X
XI6<2> VDD VSS VCTL0<8> VCTLIN<8> VCN VCP / SwitchCap_256X
XI6<3> VDD VSS VCTL0<8> VCTLIN<8> VCN VCP / SwitchCap_256X
XI0<0> VDD VSS VCTL0<8> VCTLIN<8> VCN VCP / SwitchCap_256X
XI0<1> VDD VSS VCTL0<8> VCTLIN<8> VCN VCP / SwitchCap_256X
XI0<2> VDD VSS VCTL0<8> VCTLIN<8> VCN VCP / SwitchCap_256X
XI0<3> VDD VSS VCTL0<8> VCTLIN<8> VCN VCP / SwitchCap_256X
XI13<0> VDD VSS VCTL0<7> VCTLIN<7> VCN VCP / SwitchCap_128X
XI13<1> VDD VSS VCTL0<7> VCTLIN<7> VCN VCP / SwitchCap_128X
XI10<0> VDD VSS VCTL0<7> VCTLIN<7> VCN VCP / SwitchCap_128X
XI10<1> VDD VSS VCTL0<7> VCTLIN<7> VCN VCP / SwitchCap_128X
XI5<0> VDD VSS VCTL0<7> VCTLIN<7> VCN VCP / SwitchCap_128X
XI5<1> VDD VSS VCTL0<7> VCTLIN<7> VCN VCP / SwitchCap_128X
XI1<0> VDD VSS VCTL0<7> VCTLIN<7> VCN VCP / SwitchCap_128X
XI1<1> VDD VSS VCTL0<7> VCTLIN<7> VCN VCP / SwitchCap_128X
XI12 VDD VSS VCTL0<6> VCTLIN<6> VCN VCP / SwitchCap_64X
XI8 VDD VSS VCTL0<6> VCTLIN<6> VCN VCP / SwitchCap_64X
XI4 VDD VSS VCTL0<6> VCTLIN<6> VCN VCP / SwitchCap_64X
XI2 VDD VSS VCTL0<6> VCTLIN<6> VCN VCP / SwitchCap_64X
XI11 VDD VSS VCTL0<5> VCTLIN<5> VCN VCP / SwitchCap_32X
XI3 VDD VSS VCTL0<5> VCTLIN<5> VCN VCP / SwitchCap_32X
XI7 VDD VSS VCTL0<4> VCTLIN<4> VCN VCP / SwitchCap_16X
XI15 VDD VSS VCTL0<3> VCTLIN<3> VCN VCP / SwitchCap_8X
XI16 VDD VSS VCTL0<2> VCTLIN<2> VCN VCP / SwitchCap_4X
XI17 VDD VSS VCTL0<1> VCTLIN<1> VCN VCP / SwitchCap_2X
XI18 VDD VSS VCTL0<0> VCTLIN<0> VCN VCP / SwitchCap_1X
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
*XR12 VSS VSS rppolys l=LC w=WO m=1
XR7 RTUNE<7> RTUNE<6> rppolys l=LD w=WQ m=1
XR6 RTUNE<6> RTUNE<5> rppolys l=LE w=WQ m=1
XR5 RTUNE<5> RTUNE<4> rppolys l=LF w=WP m=1
XR4 RTUNE<4> RTUNE<3> rppolys l=LG w=WP m=1
XR3 RTUNE<3> RTUNE<2> rppolys l=LF w=WP m=1
XR2 RTUNE<2> RTUNE<1> rppolys l=LE w=WQ m=1
XR1 RTUNE<1> RTUNE<0> rppolys l=LD w=WQ m=1
XR0 RTUNE<0> R2CAP rppolys l=LH w=WO m=1
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
*XR12 VSS VSS rppolys l=LC w=WO m=1
XR7 RTUNE<7> RTUNE<6> rppolys l=LD w=WQ m=1
XR6 RTUNE<6> RTUNE<5> rppolys l=LE w=WQ m=1
XR5 RTUNE<5> RTUNE<4> rppolys l=LF w=WP m=1
XR4 RTUNE<4> RTUNE<3> rppolys l=LG w=WP m=1
XR3 RTUNE<3> RTUNE<2> rppolys l=LF w=WP m=1
XR2 RTUNE<2> RTUNE<1> rppolys l=LE w=WQ m=1
XR1 RTUNE<1> RTUNE<0> rppolys l=LD w=WQ m=1
XR0 RTUNE<0> R2CAP rppolys l=LH w=WO m=1
.ENDS

************************************************************************
* Library Name: TempSensorLayout_PostLayout
* Cell Name:    PP_RCFilter
* View Name:    schematic
************************************************************************

.SUBCKT Sanitized_DLPF_RCFilter INPHASE<7> INPHASE<6> INPHASE<5> INPHASE<4> INPHASE<3> 
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
+ VCTLIN<3> VCTLIN<2> VCTLIN<1> VCTLIN<0> VDD VSS / SwitchCapArray_V2
XC0 VDLPF_P VDLPF_N cap nv=20 nh=42 w=100n s=100n stm=2 spm=7 m=8
XI0 VDLPF_P INPHASE<7> INPHASE<6> INPHASE<5> INPHASE<4> INPHASE<3> INPHASE<2> 
+ INPHASE<1> INPHASE<0> VSS / TunableRes_nonUniform_Layout_Final
XI3 VDLPF_N OUTPHASE<7> OUTPHASE<6> OUTPHASE<5> OUTPHASE<4> OUTPHASE<3> 
+ OUTPHASE<2> OUTPHASE<1> OUTPHASE<0> VSS / 
+ TunableRes_nonUniform_Layout_Final_1dummy
.ENDS

