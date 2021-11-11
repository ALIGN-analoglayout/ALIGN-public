************************************************************************
* auCdl Netlist:
*
* Library Name:  model3x
* Top Cell Name: MDLL_TOP
* View Name:     schematic
* Netlisted on:  Mar 14 22:33:22 2019
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
* Library Name: tcbn65lp
* Cell Name:    INVD0
* View Name:    schematic
************************************************************************

.SUBCKT INVD0 I VDD VSS ZN
*.PININFO I:I ZN:O VDD:B VSS:B
MMU1-M_u2 ZN I VSS VSS nch l=LA w=WE m=1
MMU1-M_u3 ZN I VDD VDD pch l=LA w=WQ m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    AN3D2
* View Name:    schematic
************************************************************************

.SUBCKT AN3D2 A1 A2 A3 VDD VSS Z
*.PININFO A1:I A2:I A3:I Z:O VDD:B VSS:B
MM_u3_1-M_u2 Z net5 VSS VSS nch l=LA w=WAC m=1
MM_u4-M_u6 net13 A3 VSS VSS nch l=LA w=WAC m=1
MM_u4-M_u5 net9 A2 net13 VSS nch l=LA w=WAC m=1
MM_u4-M_u4 net5 A1 net9 VSS nch l=LA w=WAC m=1
MM_u3_0-M_u2 Z net5 VSS VSS nch l=LA w=WAC m=1
MM_u4-M_u3 net5 A3 VDD VDD pch l=LA w=WAJ m=1
MM_u3_1-M_u3 Z net5 VDD VDD pch l=LA w=WAJ m=1
MM_u3_0-M_u3 Z net5 VDD VDD pch l=LA w=WAJ m=1
MM_u4-M_u1 net5 A1 VDD VDD pch l=LA w=WAJ m=1
MM_u4-M_u2 net5 A2 VDD VDD pch l=LA w=WAJ m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    INVD1
* View Name:    schematic
************************************************************************

.SUBCKT INVD1 I VDD VSS ZN
*.PININFO I:I ZN:O VDD:B VSS:B
MMU1-M_u2 ZN I VSS VSS nch l=LA w=WAC m=1
MMU1-M_u3 ZN I VDD VDD pch l=LA w=WAJ m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    NR2D0
* View Name:    schematic
************************************************************************

.SUBCKT NR2D0 A1 A2 VDD VSS ZN
*.PININFO A1:I A2:I ZN:O VDD:B VSS:B
MMI1-M_u3 ZN A2 VSS VSS nch l=LA w=WE m=1
MMI1-M_u4 ZN A1 VSS VSS nch l=LA w=WE m=1
MMI1-M_u1 net13 A2 VDD VDD pch l=LA w=WQ m=1
MMI1-M_u2 ZN A1 net13 VDD pch l=LA w=WQ m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    DFND1
* View Name:    schematic
************************************************************************

.SUBCKT DFND1 CPN D Q QN VDD VSS
*.PININFO CPN:I D:I Q:O QN:O VDD:B VSS:B
MMI53-M_u2 net63 net100 VSS VSS nch l=LA w=WAC m=1
MMI29-M_u2 QN net97 VSS VSS nch l=LA w=WAC m=1
MMI4 net24 net67 VSS VSS nch l=LA w=WG m=1
MMI55 net97 net67 net100 VSS nch l=LA w=WA m=1
MMI13-M_u2 net11 net1 VSS VSS nch l=LA w=WF m=1
MMI50 net11 net95 net100 VSS nch l=LA w=WF m=1
MMI32-M_u2 net67 net95 VSS VSS nch l=LA w=WE m=1
MMI5 net1 D net24 VSS nch l=LA w=WG m=1
MMI31-M_u2 net95 CPN VSS VSS nch l=LA w=WE m=1
MMI56-M_u2 net97 net63 VSS VSS nch l=LA w=WE m=1
MMI48 net9 net11 VSS VSS nch l=LA w=WA m=1
MMI27-M_u2 Q net63 VSS VSS nch l=LA w=WAC m=1
MMI47 net1 net95 net9 VSS nch l=LA w=WA m=1
MMI53-M_u3 net63 net100 VDD VDD pch l=LA w=WAI m=1
MMI54 net97 net95 net100 VDD pch l=LA w=WA m=1
MMI32-M_u3 net67 net95 VDD VDD pch l=LA w=WQ m=1
MMI43 net60 net11 VDD VDD pch l=LA w=WA m=1
MMI6 net1 D net53 VDD pch l=LA w=WAF m=1
MMI29-M_u3 QN net97 VDD VDD pch l=LA w=WAJ m=1
MMI31-M_u3 net95 CPN VDD VDD pch l=LA w=WQ m=1
MMI27-M_u3 Q net63 VDD VDD pch l=LA w=WAJ m=1
MMI13-M_u3 net11 net1 VDD VDD pch l=LA w=WR m=1
MMI52 net11 net67 net100 VDD pch l=LA w=WR m=1
MMI56-M_u3 net97 net63 VDD VDD pch l=LA w=WQ m=1
MMI45 net1 net67 net60 VDD pch l=LA w=WA m=1
MMI7 net53 net95 VDD VDD pch l=LA w=WAF m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    INVD8
* View Name:    schematic
************************************************************************

.SUBCKT INVD8 I VDD VSS ZN
*.PININFO I:I ZN:O VDD:B VSS:B
MMU1_5-M_u2 ZN I VSS VSS nch l=LA w=WAC m=1
MMU1_0-M_u2 ZN I VSS VSS nch l=LA w=WAC m=1
MMU1_3-M_u2 ZN I VSS VSS nch l=LA w=WAC m=1
MMU1_7-M_u2 ZN I VSS VSS nch l=LA w=WAC m=1
MMU1_4-M_u2 ZN I VSS VSS nch l=LA w=WAC m=1
MMU1_1-M_u2 ZN I VSS VSS nch l=LA w=WAC m=1
MMU1_6-M_u2 ZN I VSS VSS nch l=LA w=WAC m=1
MMU1_2-M_u2 ZN I VSS VSS nch l=LA w=WAC m=1
MMU1_0-M_u3 ZN I VDD VDD pch l=LA w=WAJ m=1
MMU1_4-M_u3 ZN I VDD VDD pch l=LA w=WAJ m=1
MMU1_5-M_u3 ZN I VDD VDD pch l=LA w=WAJ m=1
MMU1_1-M_u3 ZN I VDD VDD pch l=LA w=WAJ m=1
MMU1_3-M_u3 ZN I VDD VDD pch l=LA w=WAJ m=1
MMU1_7-M_u3 ZN I VDD VDD pch l=LA w=WAJ m=1
MMU1_6-M_u3 ZN I VDD VDD pch l=LA w=WAJ m=1
MMU1_2-M_u3 ZN I VDD VDD pch l=LA w=WAJ m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    TIEL
* View Name:    schematic
************************************************************************

.SUBCKT TIEL VDD VSS ZN
*.PININFO ZN:O VDD:B VSS:B
MM_u2 ZN net5 VSS VSS nch l=LA w=WAE m=1
MM_u1 net5 net5 VDD VDD pch l=LA w=WAK m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    DFSNQD1
* View Name:    schematic
************************************************************************

.SUBCKT DFSNQD1 CP D Q SDN VDD VSS
*.PININFO CP:I D:I SDN:I Q:O VDD:B VSS:B
MMI32-M_u4 net44 net25 VSS VSS nch l=LA w=WAC m=1
MMI55-M_u2 net11 CP VSS VSS nch l=LA w=WE m=1
MMI60-M_u2 Q net13 VSS VSS nch l=LA w=WAC m=1
MMI32-M_u3 net7 SDN net44 VSS nch l=LA w=WAC m=1
MMI31-M_u4 net37 net13 VSS VSS nch l=LA w=WA m=1
MMI31-M_u3 net33 SDN net37 VSS nch l=LA w=WA m=1
MMI20 net7 net83 net63 VSS nch l=LA w=WN m=1
MMI23 net25 net83 net5 VSS nch l=LA w=WA m=1
MMI22 net33 net11 net63 VSS nch l=LA w=WA m=1
MMI21 net25 D net20 VSS nch l=LA w=WAC m=1
MMI25-M_u2 net13 net63 VSS VSS nch l=LA w=WAC m=1
MMI19 net20 net11 VSS VSS nch l=LA w=WW m=1
MMI24 net5 net7 VSS VSS nch l=LA w=WA m=1
MMI40-M_u2 net83 net11 VSS VSS nch l=LA w=WE m=1
MMI55-M_u3 net11 CP VDD VDD pch l=LA w=WQ m=1
MMI33 net33 net83 net63 VDD pch l=LA w=WA m=1
MMI32-M_u1 net7 SDN VDD VDD pch l=LA w=WAJ m=1
MMI60-M_u3 Q net13 VDD VDD pch l=LA w=WAJ m=1
MMI34 net25 net11 net96 VDD pch l=LA w=WA m=1
MMI30 net7 net11 net63 VDD pch l=LA w=WX m=1
MMI32-M_u2 net7 net25 VDD VDD pch l=LA w=WAJ m=1
MMI28 net81 net83 VDD VDD pch l=LA w=WAJ m=1
MMI40-M_u3 net83 net11 VDD VDD pch l=LA w=WQ m=1
MMI31-M_u2 net33 net13 VDD VDD pch l=LA w=WA m=1
MMI35 net96 net7 VDD VDD pch l=LA w=WA m=1
MMI31-M_u1 net33 SDN VDD VDD pch l=LA w=WA m=1
MMI25-M_u3 net13 net63 VDD VDD pch l=LA w=WAJ m=1
MMI26 net25 D net81 VDD pch l=LA w=WAJ m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    ND2D0
* View Name:    schematic
************************************************************************

.SUBCKT ND2D0 A1 A2 VDD VSS ZN
*.PININFO A1:I A2:I ZN:O VDD:B VSS:B
MMI0-M_u3 ZN A1 net1 VSS nch l=LA w=WE m=1
MMI0-M_u4 net1 A2 VSS VSS nch l=LA w=WE m=1
MMI0-M_u1 ZN A1 VDD VDD pch l=LA w=WQ m=1
MMI0-M_u2 ZN A2 VDD VDD pch l=LA w=WQ m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    DEL015
* View Name:    schematic
************************************************************************

.SUBCKT DEL015 I VDD VSS Z
*.PININFO I:I Z:O VDD:B VSS:B
MMI2-M_u2 Z net13 VSS VSS nch l=LA w=WAC m=1
MMI29 net25 net9 net28 VSS nch l=LA w=WAC m=1
MMI30 net28 net9 VSS VSS nch l=LA w=WAC m=1
MMI37 net17 net5 VSS VSS nch l=LA w=WAC m=1
MMI28 net13 net9 net25 VSS nch l=LA w=WAC m=1
MMI35 net9 net5 net44 VSS nch l=LA w=WAC m=1
MMI1-M_u2 net5 I VSS VSS nch l=LA w=WAC m=1
MMI36 net44 net5 net17 VSS nch l=LA w=WAC m=1
MMI2-M_u3 Z net13 VDD VDD pch l=LA w=WAJ m=1
MMI20 net57 net9 VDD VDD pch l=LA w=WAJ m=1
MMI23 net13 net9 net25 VDD pch l=LA w=WAJ m=1
MMI1-M_u3 net5 I VDD VDD pch l=LA w=WAJ m=1
MMI21 net25 net9 net57 VDD pch l=LA w=WAJ m=1
MMI32 net9 net5 net44 VDD pch l=LA w=WAJ m=1
MMI31 net44 net5 net33 VDD pch l=LA w=WAJ m=1
MMI7 net33 net5 VDD VDD pch l=LA w=WAJ m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    DFSND1
* View Name:    schematic
************************************************************************

.SUBCKT DFSND1 CP D Q QN SDN VDD VSS
*.PININFO CP:I D:I SDN:I Q:O QN:O VDD:B VSS:B
MMI32-M_u4 net57 net61 VSS VSS nch l=LA w=WAC m=1
MMI55-M_u2 net11 CP VSS VSS nch l=LA w=WE m=1
MMI60-M_u2 Q net79 VSS VSS nch l=LA w=WAC m=1
MMI32-M_u3 net97 SDN net57 VSS nch l=LA w=WAC m=1
MMI31-M_u4 net40 net79 VSS VSS nch l=LA w=WE m=1
MMI31-M_u3 net25 SDN net40 VSS nch l=LA w=WE m=1
MMI20 net97 net81 net67 VSS nch l=LA w=WM m=1
MMI23 net61 net81 net5 VSS nch l=LA w=WA m=1
MMI22 net25 net11 net67 VSS nch l=LA w=WA m=1
MMI21 net61 D net9 VSS nch l=LA w=WAC m=1
MMI25-M_u2 net79 net67 VSS VSS nch l=LA w=WAC m=1
MMI57-M_u2 QN net25 VSS VSS nch l=LA w=WAC m=1
MMI19 net9 net11 VSS VSS nch l=LA w=WW m=1
MMI24 net5 net97 VSS VSS nch l=LA w=WA m=1
MMI40-M_u2 net81 net11 VSS VSS nch l=LA w=WE m=1
MMI55-M_u3 net11 CP VDD VDD pch l=LA w=WQ m=1
MMI33 net25 net81 net67 VDD pch l=LA w=WA m=1
MMI32-M_u1 net97 SDN VDD VDD pch l=LA w=WAJ m=1
MMI60-M_u3 Q net79 VDD VDD pch l=LA w=WAJ m=1
MMI34 net61 net11 net104 VDD pch l=LA w=WA m=1
MMI30 net97 net11 net67 VDD pch l=LA w=WX m=1
MMI57-M_u3 QN net25 VDD VDD pch l=LA w=WAJ m=1
MMI32-M_u2 net97 net61 VDD VDD pch l=LA w=WAJ m=1
MMI28 net85 net81 VDD VDD pch l=LA w=WAJ m=1
MMI40-M_u3 net81 net11 VDD VDD pch l=LA w=WQ m=1
MMI31-M_u2 net25 net79 VDD VDD pch l=LA w=WQ m=1
MMI35 net104 net97 VDD VDD pch l=LA w=WA m=1
MMI31-M_u1 net25 SDN VDD VDD pch l=LA w=WQ m=1
MMI25-M_u3 net79 net67 VDD VDD pch l=LA w=WAJ m=1
MMI26 net61 D net85 VDD pch l=LA w=WAJ m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    AN2D0
* View Name:    schematic
************************************************************************

.SUBCKT AN2D0 A1 A2 VDD VSS Z
*.PININFO A1:I A2:I Z:O VDD:B VSS:B
MM_u3-M_u3 Z net5 VDD VDD pch l=LA w=WQ m=1
MM_u2-M_u1 net5 A1 VDD VDD pch l=LA w=WQ m=1
MM_u2-M_u2 net5 A2 VDD VDD pch l=LA w=WQ m=1
MM_u3-M_u2 Z net5 VSS VSS nch l=LA w=WE m=1
MM_u2-M_u4 net17 A2 VSS VSS nch l=LA w=WE m=1
MM_u2-M_u3 net5 A1 net17 VSS nch l=LA w=WE m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    DFCND1
* View Name:    schematic
************************************************************************

.SUBCKT DFCND1 CDN CP D Q QN VDD VSS
*.PININFO CDN:I CP:I D:I Q:O QN:O VDD:B VSS:B
MMI29-M_u2 QN net33 VSS VSS nch l=LA w=WAC m=1
MMI4 net53 net5 VSS VSS nch l=LA w=WZ m=1
MMI18 net33 net5 net79 VSS nch l=LA w=WA m=1
MMI21-M_u3 net95 net79 net9 VSS nch l=LA w=WAC m=1
MMI13-M_u2 net81 net25 VSS VSS nch l=LA w=WF m=1
MMI15 net81 net67 net79 VSS nch l=LA w=WF m=1
MMI14-M_u2 net33 net95 VSS VSS nch l=LA w=WE m=1
MMI32-M_u2 net67 net5 VSS VSS nch l=LA w=WE m=1
MMI5 net25 D net53 VSS nch l=LA w=WZ m=1
MMI49 net20 CDN VSS VSS nch l=LA w=WA m=1
MMI48 net17 net81 net20 VSS nch l=LA w=WA m=1
MMI27-M_u2 Q net95 VSS VSS nch l=LA w=WAC m=1
MMI21-M_u4 net9 CDN VSS VSS nch l=LA w=WAC m=1
MMI22-M_u2 net5 CP VSS VSS nch l=LA w=WE m=1
MMI47 net25 net67 net17 VSS nch l=LA w=WA m=1
MMI14-M_u3 net33 net95 VDD VDD pch l=LA w=WQ m=1
MMI22-M_u3 net5 CP VDD VDD pch l=LA w=WQ m=1
MMI32-M_u3 net67 net5 VDD VDD pch l=LA w=WQ m=1
MMI43 net72 net81 VDD VDD pch l=LA w=WA m=1
MMI6 net25 D net104 VDD pch l=LA w=WAH m=1
MMI29-M_u3 QN net33 VDD VDD pch l=LA w=WAJ m=1
MMI27-M_u3 Q net95 VDD VDD pch l=LA w=WAJ m=1
MMI44 net72 CDN VDD VDD pch l=LA w=WA m=1
MMI17 net33 net67 net79 VDD pch l=LA w=WA m=1
MMI13-M_u3 net81 net25 VDD VDD pch l=LA w=WJ m=1
MMI21-M_u1 net95 net79 VDD VDD pch l=LA w=WAA m=1
MMI16 net81 net5 net79 VDD pch l=LA w=WO m=1
MMI45 net25 net5 net72 VDD pch l=LA w=WA m=1
MMI7 net104 net67 VDD VDD pch l=LA w=WAH m=1
MMI21-M_u2 net95 CDN VDD VDD pch l=LA w=WAA m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    AN2D2
* View Name:    schematic
************************************************************************

.SUBCKT AN2D2 A1 A2 VDD VSS Z
*.PININFO A1:I A2:I Z:O VDD:B VSS:B
MM_u3_1-M_u3 Z net9 VDD VDD pch l=LA w=WAJ m=1
MM_u2-M_u2 net9 A2 VDD VDD pch l=LA w=WAJ m=1
MM_u3_0-M_u3 Z net9 VDD VDD pch l=LA w=WAJ m=1
MM_u2-M_u1 net9 A1 VDD VDD pch l=LA w=WAJ m=1
MM_u2-M_u4 net29 A2 VSS VSS nch l=LA w=WAC m=1
MM_u2-M_u3 net9 A1 net29 VSS nch l=LA w=WAC m=1
MM_u3_1-M_u2 Z net9 VSS VSS nch l=LA w=WAC m=1
MM_u3_0-M_u2 Z net9 VSS VSS nch l=LA w=WAC m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    CKBD4
* View Name:    schematic
************************************************************************

.SUBCKT CKBD4 I VDD VSS Z
*.PININFO I:I Z:O VDD:B VSS:B
MM_u15_1 net11 I VSS VSS nch l=LA w=WW m=1
MMU23_1 Z net11 VSS VSS nch l=LA w=WW m=1
MMU23_3 Z net11 VSS VSS nch l=LA w=WW m=1
MMU23_0 Z net11 VSS VSS nch l=LA w=WW m=1
MMU23_2 Z net11 VSS VSS nch l=LA w=WW m=1
MM_u15_0 net11 I VSS VSS nch l=LA w=WW m=1
MMU21_0 Z net11 VDD VDD pch l=LA w=WAJ m=1
MMU21_1 Z net11 VDD VDD pch l=LA w=WAJ m=1
MM_u3_0 net11 I VDD VDD pch l=LA w=WAJ m=1
MMU21_3 Z net11 VDD VDD pch l=LA w=WAJ m=1
MM_u3_1 net11 I VDD VDD pch l=LA w=WAJ m=1
MMU21_2 Z net11 VDD VDD pch l=LA w=WAJ m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    ND3D3
* View Name:    schematic
************************************************************************

.SUBCKT ND3D3 A1 A2 A3 VDD VSS ZN
*.PININFO A1:I A2:I A3:I ZN:O VDD:B VSS:B
MMI0_0-M_u3 ZN A3 VDD VDD pch l=LA w=WAJ m=1
MMI0_0-M_u1 ZN A1 VDD VDD pch l=LA w=WAJ m=1
MMI0_2-M_u3 ZN A3 VDD VDD pch l=LA w=WAJ m=1
MMI0_2-M_u2 ZN A2 VDD VDD pch l=LA w=WAJ m=1
MMI0_1-M_u2 ZN A2 VDD VDD pch l=LA w=WAJ m=1
MMI0_1-M_u3 ZN A3 VDD VDD pch l=LA w=WAJ m=1
MMI0_0-M_u2 ZN A2 VDD VDD pch l=LA w=WAJ m=1
MMI0_2-M_u1 ZN A1 VDD VDD pch l=LA w=WAJ m=1
MMI0_1-M_u1 ZN A1 VDD VDD pch l=LA w=WAJ m=1
MMI0_1-M_u5 net69 A2 net72 VSS nch l=LA w=WAC m=1
MMI0_2-M_u6 net56 A3 VSS VSS nch l=LA w=WAC m=1
MMI0_1-M_u4 ZN A1 net69 VSS nch l=LA w=WAC m=1
MMI0_2-M_u4 ZN A1 net53 VSS nch l=LA w=WAC m=1
MMI0_2-M_u5 net53 A2 net56 VSS nch l=LA w=WAC m=1
MMI0_1-M_u6 net72 A3 VSS VSS nch l=LA w=WAC m=1
MMI0_0-M_u6 net44 A3 VSS VSS nch l=LA w=WAC m=1
MMI0_0-M_u5 net40 A2 net44 VSS nch l=LA w=WAC m=1
MMI0_0-M_u4 ZN A1 net40 VSS nch l=LA w=WAC m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    AN3D1
* View Name:    schematic
************************************************************************

.SUBCKT AN3D1 A1 A2 A3 VDD VSS Z
*.PININFO A1:I A2:I A3:I Z:O VDD:B VSS:B
MM_u4-M_u6 net13 A3 VSS VSS nch l=LA w=WE m=1
MM_u3-M_u2 Z net11 VSS VSS nch l=LA w=WAC m=1
MM_u4-M_u5 net5 A2 net13 VSS nch l=LA w=WE m=1
MM_u4-M_u4 net11 A1 net5 VSS nch l=LA w=WE m=1
MM_u3-M_u3 Z net11 VDD VDD pch l=LA w=WAJ m=1
MM_u4-M_u3 net11 A3 VDD VDD pch l=LA w=WQ m=1
MM_u4-M_u1 net11 A1 VDD VDD pch l=LA w=WQ m=1
MM_u4-M_u2 net11 A2 VDD VDD pch l=LA w=WQ m=1
.ENDS

************************************************************************
* Library Name: modelx
* Cell Name:    MDLL_CKGEN_V1
* View Name:    schematic
************************************************************************

.SUBCKT MDLL_CKGEN_V1 EN_DLL FREE_RUN MD_SAR MD_TRK REF_CLK SAR_EN SCLK0
+ SEL_RST TRK_EN VDD VSS
*.PININFO EN_DLL:I MD_SAR:I MD_TRK:I SCLK0:I FREE_RUN:O REF_CLK:O SAR_EN:O
*.PININFO SEL_RST:O TRK_EN:O VDD:B VSS:B
XI9 net31 VDD VSS net17 INVD0
XI40 net042 EN_DLL MD_SAR VDD VSS SAR_EN AN3D2
XI45 SCLK net010 net25 VDD VSS net048 AN3D2
XI25 net010 VDD VSS FREE_RUN INVD1
XI5 net37 VDD VSS net25 INVD1
XI0 MD_SAR MD_TRK VDD VSS net36 NR2D0
XI43 SCLK0 EN_DLL net032 net045 VDD VSS DFND1
XI44 net048 VDD VSS SEL_RST INVD8
XI15 VDD VSS net32 TIEL
XI22 SCLK net30 net27 net14 VDD VSS DFSNQD1
XI21 SCLK net29 net30 net14 VDD VSS DFSNQD1
XI20 SCLK net27 net021 net14 VDD VSS DFSNQD1
XI19 SCLK net34 net33 net14 VDD VSS DFSNQD1
XI18 SCLK net33 net29 net14 VDD VSS DFSNQD1
XI17 SCLK net35 net34 net14 VDD VSS DFSNQD1
XI16 SCLK net32 net35 net14 VDD VSS DFSNQD1
XI24 net36 EN_DLL VDD VSS net010 ND2D0
XI8 EN_DLL VDD VSS net31 DEL015
XI4 SCLK VDD VSS net37 DEL015
XI27 SCLK net021 net042 net026 net14 VDD VSS DFSND1
XI28 net026 EN_DLL VDD VSS TRK_RST AN2D0
XI30 TRK_RST net020 net039 net027 net039 VDD VSS DFCND1
XI29 TRK_RST SCLK net015 net020 net015 VDD VSS DFCND1
XI36 net032 SCLK0 VDD VSS SCLK AN2D2
XI35 SCLK VDD VSS REF_CLK CKBD4
XI38 EN_DLL net17 MD_SAR VDD VSS net14 ND3D3
XI42 net027 net015 MD_TRK VDD VSS TRK_EN AN3D1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    MUX2D1
* View Name:    schematic
************************************************************************

.SUBCKT MUX2D1 I0 I1 S VDD VSS Z
*.PININFO I0:I I1:I S:I Z:O VDD:B VSS:B
MMI14-M_u3 net5 I1 VDD VDD pch l=LA w=WAJ m=1
MMI16-M_u3 net37 I0 VDD VDD pch l=LA w=WW m=1
MMU29-M_u3 Z net27 VDD VDD pch l=LA w=WAJ m=1
MMI15-M_u3 net9 S VDD VDD pch l=LA w=WQ m=1
MMI13-M_u2 net5 net9 net27 VDD pch l=LA w=WY m=1
MMU18-M_u2 net37 S net27 VDD pch l=LA w=WAE m=1
MMU18-M_u3 net37 net9 net27 VSS nch l=LA w=WQ m=1
MMI15-M_u2 net9 S VSS VSS nch l=LA w=WE m=1
MMI16-M_u2 net37 I0 VSS VSS nch l=LA w=WL m=1
MMI13-M_u3 net5 S net27 VSS nch l=LA w=WN m=1
MMI14-M_u2 net5 I1 VSS VSS nch l=LA w=WAC m=1
MMU29-M_u2 Z net27 VSS VSS nch l=LA w=WAC m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    DEL0
* View Name:    schematic
************************************************************************

.SUBCKT DEL0 I VDD VSS Z
*.PININFO I:I Z:O VDD:B VSS:B
MMU7-M_u2 net11 net25 VSS VSS nch l=LB w=WAC m=1
MMI2-M_u2 Z net11 VSS VSS nch l=LA w=WAC m=1
MMI1-M_u2 net5 I VSS VSS nch l=LA w=WAC m=1
MMU5-M_u2 net25 net5 VSS VSS nch l=LB w=WAC m=1
MMI2-M_u3 Z net11 VDD VDD pch l=LA w=WAJ m=1
MMU5-M_u3 net25 net5 VDD VDD pch l=LB w=WAJ m=1
MMI1-M_u3 net5 I VDD VDD pch l=LA w=WAJ m=1
MMU7-M_u3 net11 net25 VDD VDD pch l=LB w=WAJ m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    MUX2D0
* View Name:    schematic
************************************************************************

.SUBCKT MUX2D0 I0 I1 S VDD VSS Z
*.PININFO I0:I I1:I S:I Z:O VDD:B VSS:B
MMU29-M_u3 Z net5 VDD VDD pch l=LA w=WQ m=1
MMI15-M_u3 net17 S VDD VDD pch l=LA w=WP m=1
MMI111 net13 I0 VDD VDD pch l=LA w=WQ m=1
MMI24 net9 I1 VDD VDD pch l=LA w=WQ m=1
MMI5 net5 S net13 VDD pch l=LA w=WQ m=1
MMI25 net5 net17 net9 VDD pch l=LA w=WQ m=1
MMI15-M_u2 net17 S VSS VSS nch l=LA w=WE m=1
MMI20 net36 I1 VSS VSS nch l=LA w=WE m=1
MMI12 net5 net17 net25 VSS nch l=LA w=WE m=1
MMI21 net5 S net36 VSS nch l=LA w=WE m=1
MMU29-M_u2 Z net5 VSS VSS nch l=LA w=WE m=1
MMI19 net25 I0 VSS VSS nch l=LA w=WE m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    DEL005
* View Name:    schematic
************************************************************************

.SUBCKT DEL005 I VDD VSS Z
*.PININFO I:I Z:O VDD:B VSS:B
MMI2-M_u3 Z net11 VDD VDD pch l=LA w=WAJ m=1
MMI3 net5 I VDD VDD pch l=LA w=WAJ m=1
MMI10 net11 I net5 VDD pch l=LA w=WAJ m=1
MMI13 net5 I VSS VSS nch l=LA w=WAC m=1
MMI2-M_u2 Z net11 VSS VSS nch l=LA w=WAC m=1
MMI12 net11 I net5 VSS nch l=LA w=WAC m=1
.ENDS

************************************************************************
* Library Name: modelx
* Cell Name:    DEL_3x1_BIN
* View Name:    schematic
************************************************************************

.SUBCKT DEL_3x1_BIN DEL_IN DEL_OUT LSB<3> LSB<2> LSB<1> VDD VSS
*.PININFO DEL_IN:I LSB<3>:I LSB<2>:I LSB<1>:I DEL_OUT:O VDD:B VSS:B
XI9 net020 net027 net033 VDD VSS DEL_OUT MUX2D1
XI1 net010 VDD VSS net032 DEL0
XI19 LSB<3> VDD VSS net013 DEL0
XI20 LSB<2> VDD VSS net035 DEL015
XI5 net030 VDD VSS net029 DEL015
XI21 LSB<1> VDD VSS net033 DEL015
XI3 DEL_IN net032 net013 VDD VSS net019 MUX2D0
XI6 net019 net029 net035 VDD VSS net020 MUX2D0
XI8 net028 VDD VSS net027 DEL005
XI14 DEL_IN VDD VSS net05 INVD0
XI16 net019 VDD VSS net018 INVD0
XI17 net020 VDD VSS net023 INVD0
XI15 net018 LSB<2> VDD VSS net030 ND2D0
XI13 net05 LSB<3> VDD VSS net010 ND2D0
XI18 net023 LSB<1> VDD VSS net028 ND2D0
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    OR2D0
* View Name:    schematic
************************************************************************

.SUBCKT OR2D0 A1 A2 VDD VSS Z
*.PININFO A1:I A2:I Z:O VDD:B VSS:B
MMU1-M_u2 Z net5 VSS VSS nch l=LA w=WE m=1
MM_u7-M_u4 net5 A1 VSS VSS nch l=LA w=WE m=1
MM_u7-M_u3 net5 A2 VSS VSS nch l=LA w=WE m=1
MMU1-M_u3 Z net5 VDD VDD pch l=LA w=WQ m=1
MM_u7-M_u1 net17 A2 VDD VDD pch l=LA w=WQ m=1
MM_u7-M_u2 net5 A1 net17 VDD pch l=LA w=WQ m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    DEL1
* View Name:    schematic
************************************************************************

.SUBCKT DEL1 I VDD VSS Z
*.PININFO I:I Z:O VDD:B VSS:B
MMU7-M_u2 net11 net25 VSS VSS nch l=LD w=WAC m=1
MMI2-M_u2 Z net11 VSS VSS nch l=LA w=WV m=1
MMI1-M_u2 net5 I VSS VSS nch l=LA w=WAC m=1
MMU5-M_u2 net25 net5 VSS VSS nch l=LD w=WAC m=1
MMI2-M_u3 Z net11 VDD VDD pch l=LA w=WAJ m=1
MMU5-M_u3 net25 net5 VDD VDD pch l=LD w=WAJ m=1
MMI1-M_u3 net5 I VDD VDD pch l=LA w=WAJ m=1
MMU7-M_u3 net11 net25 VDD VDD pch l=LD w=WAJ m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    MUX4D0
* View Name:    schematic
************************************************************************

.SUBCKT MUX4D0 I0 I1 I2 I3 S0 S1 VDD VSS Z
*.PININFO I0:I I1:I I2:I I3:I S0:I S1:I Z:O VDD:B VSS:B
MMU18-M_u3 Z net20 VDD VDD pch l=LA w=WQ m=1
MMI53-M_u2 net97 S1 net20 VDD pch l=LA w=WQ m=1
MMI51-M_u3 net37 I3 VDD VDD pch l=LA w=WQ m=1
MMI55-M_u2 net37 net61 net104 VDD pch l=LA w=WQ m=1
MMI50-M_u3 net33 S1 VDD VDD pch l=LA w=WQ m=1
MMI48-M_u3 net61 S0 VDD VDD pch l=LA w=WQ m=1
MMI49-M_u3 net81 I2 VDD VDD pch l=LA w=WQ m=1
MMI47-M_u3 net5 I1 VDD VDD pch l=LA w=WQ m=1
MMI56-M_u2 net104 net33 net20 VDD pch l=LA w=WQ m=1
MMI54-M_u2 net81 S0 net104 VDD pch l=LA w=WQ m=1
MMI40-M_u2 net9 S0 net97 VDD pch l=LA w=WQ m=1
MMI52-M_u2 net5 net61 net97 VDD pch l=LA w=WQ m=1
MMI46-M_u3 net9 I0 VDD VDD pch l=LA w=WQ m=1
MMI55-M_u3 net37 S0 net104 VSS nch l=LA w=WE m=1
MMI53-M_u3 net97 net33 net20 VSS nch l=LA w=WE m=1
MMI47-M_u2 net5 I1 VSS VSS nch l=LA w=WE m=1
MMI51-M_u2 net37 I3 VSS VSS nch l=LA w=WE m=1
MMI52-M_u3 net5 S0 net97 VSS nch l=LA w=WE m=1
MMI54-M_u3 net81 net61 net104 VSS nch l=LA w=WD m=1
MMI56-M_u3 net104 S1 net20 VSS nch l=LA w=WE m=1
MMI40-M_u3 net9 net61 net97 VSS nch l=LA w=WC m=1
MMI49-M_u2 net81 I2 VSS VSS nch l=LA w=WD m=1
MMU18-M_u2 Z net20 VSS VSS nch l=LA w=WE m=1
MMI48-M_u2 net61 S0 VSS VSS nch l=LA w=WD m=1
MMI46-M_u2 net9 I0 VSS VSS nch l=LA w=WC m=1
MMI50-M_u2 net33 S1 VSS VSS nch l=LA w=WA m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    BUFFD0
* View Name:    schematic
************************************************************************

.SUBCKT BUFFD0 I VDD VSS Z
*.PININFO I:I Z:O VDD:B VSS:B
MMI2-M_u2 net5 I VSS VSS nch l=LA w=WE m=1
MMI1-M_u2 Z net5 VSS VSS nch l=LA w=WE m=1
MMI2-M_u3 net5 I VDD VDD pch l=LA w=WQ m=1
MMI1-M_u3 Z net5 VDD VDD pch l=LA w=WQ m=1
.ENDS

************************************************************************
* Library Name: modelx
* Cell Name:    DEL_3x1
* View Name:    schematic
************************************************************************

.SUBCKT DEL_3x1 DEL_IN DEL_OUT EN SEL0 SEL1 VDD VSS
*.PININFO DEL_IN:I EN:I SEL0:I SEL1:I DEL_OUT:O VDD:B VSS:B
XI18 SEL1 SEL0 VDD VSS S2T<3> AN2D0
XI8 net12 S2T<3> VDD VSS net18 AN2D0
XI6 net11 S2T<2> VDD VSS net19 AN2D0
XI4 net21 S2T<1> VDD VSS net20 AN2D0
XI2 DEL_IN S2T<0> VDD VSS net21 AN2D0
XI9 net18 VDD VSS net17 DEL1
XI7 net19 VDD VSS net12 DEL1
XI5 net20 VDD VSS net11 DEL1
XI11 net21 net11 net12 net17 SEL0 SEL1 VDD VSS DEL_OUT MUX4D0
XI17 SEL1 VDD VSS S2T<2> BUFFD0
XI16 EN VDD VSS S2T<0> BUFFD0
XI14 SEL1 SEL0 VDD VSS S2T<1> OR2D0
.ENDS

************************************************************************
* Library Name: modelx
* Cell Name:    DEL_4x1
* View Name:    schematic
************************************************************************

.SUBCKT DEL_4x1 DEL_IN DEL_OUT EN SEL0 SEL1 VDD VSS
*.PININFO DEL_IN:I EN:I SEL0:I SEL1:I DEL_OUT:O VDD:B VSS:B
XI18 SEL1 SEL0 VDD VSS S2T<3> AN2D0
XI8 net12 S2T<3> VDD VSS net18 AN2D0
XI6 net11 S2T<2> VDD VSS net19 AN2D0
XI4 net10 S2T<1> VDD VSS net20 AN2D0
XI2 DEL_IN S2T<0> VDD VSS net21 AN2D0
XI9 net18 VDD VSS net17 DEL1
XI7 net19 VDD VSS net12 DEL1
XI5 net20 VDD VSS net11 DEL1
XI3 net21 VDD VSS net10 DEL1
XI11 net10 net11 net12 net17 SEL0 SEL1 VDD VSS DEL_OUT MUX4D0
XI17 SEL1 VDD VSS S2T<2> BUFFD0
XI16 EN VDD VSS S2T<0> BUFFD0
XI14 SEL1 SEL0 VDD VSS S2T<1> OR2D0
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    CKBD2
* View Name:    schematic
************************************************************************

.SUBCKT CKBD2 I VDD VSS Z
*.PININFO I:I Z:O VDD:B VSS:B
MMU23_1 Z net5 VSS VSS nch l=LA w=WW m=1
MM_u15 net5 I VSS VSS nch l=LA w=WW m=1
MMU23_0 Z net5 VSS VSS nch l=LA w=WW m=1
MM_u3 net5 I VDD VDD pch l=LA w=WAJ m=1
MMU21_0 Z net5 VDD VDD pch l=LA w=WAJ m=1
MMU21_1 Z net5 VDD VDD pch l=LA w=WAJ m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    MUX4ND0
* View Name:    schematic
************************************************************************

.SUBCKT MUX4ND0 I0 I1 I2 I3 S0 S1 VDD VSS ZN
*.PININFO I0:I I1:I I2:I I3:I S0:I S1:I ZN:O VDD:B VSS:B
MMI47-M_u2 net17 I2 VSS VSS nch l=LA w=WF m=1
MMI51-M_u3 net20 S1 ZN VSS nch l=LA w=WE m=1
MMI55-M_u2 net61 I0 VSS VSS nch l=LA w=WG m=1
MMI50-M_u3 net33 net83 ZN VSS nch l=LA w=WE m=1
MMI48-M_u3 net61 net67 net33 VSS nch l=LA w=WF m=1
MMI58-M_u2 net67 S0 VSS VSS nch l=LA w=WD m=1
MMI49-M_u3 net5 S0 net33 VSS nch l=LA w=WE m=1
MMI52-M_u3 net17 net67 net20 VSS nch l=LA w=WF m=1
MMI54-M_u3 net9 S0 net20 VSS nch l=LA w=WE m=1
MMI57-M_u2 net9 I3 VSS VSS nch l=LA w=WAC m=1
MMI56-M_u2 net5 I1 VSS VSS nch l=LA w=WAC m=1
MMU18-M_u2 net83 S1 VSS VSS nch l=LA w=WE m=1
MMI55-M_u3 net61 I0 VDD VDD pch l=LA w=WY m=1
MMU18-M_u3 net83 S1 VDD VDD pch l=LA w=WQ m=1
MMI58-M_u3 net67 S0 VDD VDD pch l=LA w=WQ m=1
MMI51-M_u2 net20 net83 ZN VDD pch l=LA w=WQ m=1
MMI57-M_u3 net9 I3 VDD VDD pch l=LA w=WAJ m=1
MMI56-M_u3 net5 I1 VDD VDD pch l=LA w=WAJ m=1
MMI47-M_u3 net17 I2 VDD VDD pch l=LA w=WY m=1
MMI49-M_u2 net5 net67 net33 VDD pch l=LA w=WQ m=1
MMI48-M_u2 net61 S0 net33 VDD pch l=LA w=WQ m=1
MMI54-M_u2 net9 net67 net20 VDD pch l=LA w=WQ m=1
MMI52-M_u2 net17 S0 net20 VDD pch l=LA w=WQ m=1
MMI50-M_u2 net33 S1 ZN VDD pch l=LA w=WQ m=1
.ENDS

************************************************************************
* Library Name: modelx
* Cell Name:    DEL_7b
* View Name:    schematic
************************************************************************

.SUBCKT DEL_7b CKOUT EN LSB<3> LSB<2> LSB<1> REF_CLK SEL0 SEL1 SEL2 SEL3
+ SEL_DL VDD VSS
*.PININFO EN:I LSB<3>:I LSB<2>:I LSB<1>:I REF_CLK:I SEL0:I SEL1:I SEL2:I
*.PININFO SEL3:I SEL_DL:I CKOUT:O VDD:B VSS:B
XI29 net87 net82 LSB<3> LSB<2> LSB<1> VDD VSS DEL_3x1_BIN
XI14 SEL3 SEL2 VDD VSS S2T<1> OR2D0
XI23 SEL1 S2T<1> VDD VSS net90 OR2D0
XI27 SEL1 S2T<3> VDD VSS net88 OR2D0
XI25 SEL1 S2T<2> VDD VSS net89 OR2D0
XI24 SEL0 S2T<1> VDD VSS net83 OR2D0
XI28 SEL0 S2T<3> VDD VSS net85 OR2D0
XI26 SEL0 S2T<2> VDD VSS net84 OR2D0
XI0 REF_CLK net82 SEL_DL VDD VSS net91 MUX2D0
XI19 net91 net76 S2T<0> net83 net90 VDD VSS DEL_3x1
XI22 net80 net86 S2T<3> SEL0 SEL1 VDD VSS DEL_4x1
XI21 net78 net80 S2T<2> net85 net88 VDD VSS DEL_4x1
XI20 net76 net78 S2T<1> net84 net89 VDD VSS DEL_4x1
XI18 SEL3 SEL2 VDD VSS S2T<3> AN2D0
XI16 EN VDD VSS S2T<0> BUFFD0
XI17 SEL3 VDD VSS S2T<2> BUFFD0
XI2 net82 VDD VSS CKOUT CKBD2
XI3 net76 net78 net80 net86 SEL2 SEL3 VDD VSS net87 MUX4ND0
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    CKND0
* View Name:    schematic
************************************************************************

.SUBCKT CKND0 I VDD VSS ZN
*.PININFO I:I ZN:O VDD:B VSS:B
MM_u2 ZN I VSS VSS nch l=LA w=WA m=1
MM_u1 ZN I VDD VDD pch l=LA w=WQ m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    AO22D0
* View Name:    schematic
************************************************************************

.SUBCKT AO22D0 A1 A2 B1 B2 VDD VSS Z
*.PININFO A1:I A2:I B1:I B2:I Z:O VDD:B VSS:B
MMI23 net17 A2 VSS VSS nch l=LA w=WE m=1
MMI8-M_u2 Z net5 VSS VSS nch l=LA w=WE m=1
MMI16 net5 B1 net1 VSS nch l=LA w=WE m=1
MMI24 net5 A1 net17 VSS nch l=LA w=WE m=1
MMI22 net1 B2 VSS VSS nch l=LA w=WE m=1
MMI20 net5 A1 net33 VDD pch l=LA w=WQ m=1
MM_u2 net33 B2 VDD VDD pch l=LA w=WQ m=1
MMI19 net5 A2 net33 VDD pch l=LA w=WQ m=1
MMI8-M_u3 Z net5 VDD VDD pch l=LA w=WQ m=1
MMI21 net33 B1 VDD VDD pch l=LA w=WQ m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    MOAI22D1
* View Name:    schematic
************************************************************************

.SUBCKT MOAI22D1 A1 A2 B1 B2 VDD VSS ZN
*.PININFO A1:I A2:I B1:I B2:I ZN:O VDD:B VSS:B
MMU1 net37 B1 net20 VSS nch l=LA w=WAC m=1
MMI6 net9 net37 VSS VSS nch l=LA w=WAC m=1
MMU9 net9 A1 ZN VSS nch l=LA w=WAC m=1
MMI5 net20 B2 VSS VSS nch l=LA w=WAC m=1
MMU10 net9 A2 ZN VSS nch l=LA w=WAC m=1
MMI1 net37 B1 VDD VDD pch l=LA w=WAJ m=1
MMI3 net33 A2 VDD VDD pch l=LA w=WAJ m=1
MMI4 ZN A1 net33 VDD pch l=LA w=WAJ m=1
MMI2 ZN net37 VDD VDD pch l=LA w=WAJ m=1
MMU3 net37 B2 VDD VDD pch l=LA w=WAJ m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    CKAN2D0
* View Name:    schematic
************************************************************************

.SUBCKT CKAN2D0 A1 A2 VDD VSS Z
*.PININFO A1:I A2:I Z:O VDD:B VSS:B
MM_u2-M_u2 net5 A2 VDD VDD pch l=LA w=WE m=1
MM_u2-M_u1 net5 A1 VDD VDD pch l=LA w=WE m=1
MM_u3-M_u3 Z net5 VDD VDD pch l=LA w=WQ m=1
MM_u2-M_u4 net21 A2 VSS VSS nch l=LA w=WA m=1
MM_u3-M_u2 Z net5 VSS VSS nch l=LA w=WA m=1
MM_u2-M_u3 net5 A1 net21 VSS nch l=LA w=WA m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    AN2XD1
* View Name:    schematic
************************************************************************

.SUBCKT AN2XD1 A1 A2 VDD VSS Z
*.PININFO A1:I A2:I Z:O VDD:B VSS:B
MM_u2-M_u4 net9 A2 VSS VSS nch l=LA w=WAC m=1
MM_u2-M_u3 net5 A1 net9 VSS nch l=LA w=WAC m=1
MM_u3-M_u2 Z net5 VSS VSS nch l=LA w=WAC m=1
MM_u3-M_u3 Z net5 VDD VDD pch l=LA w=WAJ m=1
MM_u2-M_u2 net5 A2 VDD VDD pch l=LA w=WAJ m=1
MM_u2-M_u1 net5 A1 VDD VDD pch l=LA w=WAJ m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    AN3D0
* View Name:    schematic
************************************************************************

.SUBCKT AN3D0 A1 A2 A3 VDD VSS Z
*.PININFO A1:I A2:I A3:I Z:O VDD:B VSS:B
MM_u4-M_u6 net13 A3 VSS VSS nch l=LA w=WE m=1
MM_u3-M_u2 Z net11 VSS VSS nch l=LA w=WE m=1
MM_u4-M_u5 net5 A2 net13 VSS nch l=LA w=WE m=1
MM_u4-M_u4 net11 A1 net5 VSS nch l=LA w=WE m=1
MM_u3-M_u3 Z net11 VDD VDD pch l=LA w=WQ m=1
MM_u4-M_u3 net11 A3 VDD VDD pch l=LA w=WQ m=1
MM_u4-M_u1 net11 A1 VDD VDD pch l=LA w=WQ m=1
MM_u4-M_u2 net11 A2 VDD VDD pch l=LA w=WQ m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    AN3XD1
* View Name:    schematic
************************************************************************

.SUBCKT AN3XD1 A1 A2 A3 VDD VSS Z
*.PININFO A1:I A2:I A3:I Z:O VDD:B VSS:B
MM_u4-M_u6 net13 A3 VSS VSS nch l=LA w=WAC m=1
MM_u3-M_u2 Z net11 VSS VSS nch l=LA w=WAC m=1
MM_u4-M_u5 net5 A2 net13 VSS nch l=LA w=WAC m=1
MM_u4-M_u4 net11 A1 net5 VSS nch l=LA w=WAC m=1
MM_u3-M_u3 Z net11 VDD VDD pch l=LA w=WAJ m=1
MM_u4-M_u3 net11 A3 VDD VDD pch l=LA w=WAJ m=1
MM_u4-M_u1 net11 A1 VDD VDD pch l=LA w=WAJ m=1
MM_u4-M_u2 net11 A2 VDD VDD pch l=LA w=WAJ m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    ND2D1
* View Name:    schematic
************************************************************************

.SUBCKT ND2D1 A1 A2 VDD VSS ZN
*.PININFO A1:I A2:I ZN:O VDD:B VSS:B
MMI1-M_u3 ZN A1 net1 VSS nch l=LA w=WAC m=1
MMI1-M_u4 net1 A2 VSS VSS nch l=LA w=WAC m=1
MMI1-M_u1 ZN A1 VDD VDD pch l=LA w=WAJ m=1
MMI1-M_u2 ZN A2 VDD VDD pch l=LA w=WAJ m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    CKND2D2
* View Name:    schematic
************************************************************************

.SUBCKT CKND2D2 A1 A2 VDD VSS ZN
*.PININFO A1:I A2:I ZN:O VDD:B VSS:B
MMI0_0-M_u1 ZN A1 VDD VDD pch l=LA w=WAC m=1
MMI0_1-M_u2 ZN A2 VDD VDD pch l=LA w=WAC m=1
MMI0_0-M_u2 ZN A2 VDD VDD pch l=LA w=WAC m=1
MMI0_1-M_u1 ZN A1 VDD VDD pch l=LA w=WAC m=1
MMI0_1-M_u4 net24 A2 VSS VSS nch l=LA w=WAC m=1
MMI0_0-M_u3 ZN A1 net17 VSS nch l=LA w=WAC m=1
MMI0_1-M_u3 ZN A1 net24 VSS nch l=LA w=WAC m=1
MMI0_0-M_u4 net17 A2 VSS VSS nch l=LA w=WAC m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    CKND2D1
* View Name:    schematic
************************************************************************

.SUBCKT CKND2D1 A1 A2 VDD VSS ZN
*.PININFO A1:I A2:I ZN:O VDD:B VSS:B
MMI0-M_u3 ZN A1 net1 VSS nch l=LA w=WAC m=1
MMI0-M_u4 net1 A2 VSS VSS nch l=LA w=WAC m=1
MMI0-M_u1 ZN A1 VDD VDD pch l=LA w=WAC m=1
MMI0-M_u2 ZN A2 VDD VDD pch l=LA w=WAC m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    CKND1
* View Name:    schematic
************************************************************************

.SUBCKT CKND1 I VDD VSS ZN
*.PININFO I:I ZN:O VDD:B VSS:B
MM_u2 ZN I VSS VSS nch l=LA w=WW m=1
MM_u1 ZN I VDD VDD pch l=LA w=WAJ m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    CKND2D0
* View Name:    schematic
************************************************************************

.SUBCKT CKND2D0 A1 A2 VDD VSS ZN
*.PININFO A1:I A2:I ZN:O VDD:B VSS:B
MMU1-M_u3 ZN A1 net1 VSS nch l=LA w=WE m=1
MMU1-M_u4 net1 A2 VSS VSS nch l=LA w=WE m=1
MMU1-M_u2 ZN A2 VDD VDD pch l=LA w=WE m=1
MMU1-M_u1 ZN A1 VDD VDD pch l=LA w=WE m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    IND2D0
* View Name:    schematic
************************************************************************

.SUBCKT IND2D0 A1 B1 VDD VSS ZN
*.PININFO A1:I B1:I ZN:O VDD:B VSS:B
MMI2-M_u3 net9 A1 VDD VDD pch l=LA w=WP m=1
MMI11 VDD B1 ZN VDD pch l=LA w=WP m=1
MM_u16 VDD net9 ZN VDD pch l=LA w=WP m=1
MMI13 net21 net9 VSS VSS nch l=LA w=WE m=1
MMI2-M_u2 net9 A1 VSS VSS nch l=LA w=WE m=1
MMI12 ZN B1 net21 VSS nch l=LA w=WE m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    IND2D2
* View Name:    schematic
************************************************************************

.SUBCKT IND2D2 A1 B1 VDD VSS ZN
*.PININFO A1:I B1:I ZN:O VDD:B VSS:B
MMI3 VDD net11 ZN VDD pch l=LA w=WAL m=1
MM_u16 VDD B1 ZN VDD pch l=LA w=WAL m=1
MMI9-M_u3 net11 A1 VDD VDD pch l=LA w=WAJ m=1
MMI9-M_u2 net11 A1 VSS VSS nch l=LA w=WAC m=1
MMI4 net20 B1 VSS VSS nch l=LA w=WAC m=1
MMI11 net21 B1 VSS VSS nch l=LA w=WAC m=1
MMI12 ZN net11 net20 VSS nch l=LA w=WAC m=1
MMI10 ZN net11 net21 VSS nch l=LA w=WAC m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    AO21D0
* View Name:    schematic
************************************************************************

.SUBCKT AO21D0 A1 A2 B VDD VSS Z
*.PININFO A1:I A2:I B:I Z:O VDD:B VSS:B
MMI9 net5 A2 net9 VDD pch l=LA w=WQ m=1
MM_u2 net9 B VDD VDD pch l=LA w=WQ m=1
MMI10 net5 A1 net9 VDD pch l=LA w=WQ m=1
MMI8-M_u3 Z net5 VDD VDD pch l=LA w=WQ m=1
MMI11 net5 A1 net25 VSS nch l=LA w=WE m=1
MMI12 net25 A2 VSS VSS nch l=LA w=WE m=1
MMI8-M_u2 Z net5 VSS VSS nch l=LA w=WE m=1
MMI6 net5 B VSS VSS nch l=LA w=WE m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    IND2D1
* View Name:    schematic
************************************************************************

.SUBCKT IND2D1 A1 B1 VDD VSS ZN
*.PININFO A1:I B1:I ZN:O VDD:B VSS:B
MMI2-M_u3 net9 A1 VDD VDD pch l=LA w=WQ m=1
MMI11 VDD B1 ZN VDD pch l=LA w=WAJ m=1
MM_u16 VDD net9 ZN VDD pch l=LA w=WAJ m=1
MMI13 net21 net9 VSS VSS nch l=LA w=WAC m=1
MMI2-M_u2 net9 A1 VSS VSS nch l=LA w=WE m=1
MMI12 ZN B1 net21 VSS nch l=LA w=WAC m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    CKXOR2D1
* View Name:    schematic
************************************************************************

.SUBCKT CKXOR2D1 A1 A2 VDD VSS Z
*.PININFO A1:I A2:I Z:O VDD:B VSS:B
MM_u6-M_u2 net27 A1 net44 VDD pch l=LA w=WU m=1
MM_u4-M_u3 Z net44 VDD VDD pch l=LA w=WAJ m=1
MM_u5-M_u3 net5 net27 VDD VDD pch l=LA w=WU m=1
MM_u8-M_u3 net9 A1 VDD VDD pch l=LA w=WQ m=1
MMI0-M_u2 net5 net9 net44 VDD pch l=LA w=WU m=1
MM_u2-M_u3 net27 A2 VDD VDD pch l=LA w=WAJ m=1
MM_u6-M_u3 net27 net9 net44 VSS nch l=LA w=WE m=1
MMI0-M_u3 net5 A1 net44 VSS nch l=LA w=WE m=1
MM_u8-M_u2 net9 A1 VSS VSS nch l=LA w=WE m=1
MM_u4-M_u2 Z net44 VSS VSS nch l=LA w=WAC m=1
MM_u2-M_u2 net27 A2 VSS VSS nch l=LA w=WAC m=1
MM_u5-M_u2 net5 net27 VSS VSS nch l=LA w=WE m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    OAI21D1
* View Name:    schematic
************************************************************************

.SUBCKT OAI21D1 A1 A2 B VDD VSS ZN
*.PININFO A1:I A2:I B:I ZN:O VDD:B VSS:B
MMI16-MI13 net9 A2 VDD VDD pch l=LA w=WAJ m=1
MM_u9 ZN B VDD VDD pch l=LA w=WAJ m=1
MMI16-MI12 ZN A1 net9 VDD pch l=LA w=WAJ m=1
MM_u3 ZN A2 net24 VSS nch l=LA w=WAC m=1
MM_u4 net24 B VSS VSS nch l=LA w=WAC m=1
MM_u2 ZN A1 net24 VSS nch l=LA w=WAC m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    ND3D1
* View Name:    schematic
************************************************************************

.SUBCKT ND3D1 A1 A2 A3 VDD VSS ZN
*.PININFO A1:I A2:I A3:I ZN:O VDD:B VSS:B
MMI1-M_u5 net9 A2 net1 VSS nch l=LA w=WAC m=1
MMI1-M_u4 ZN A1 net9 VSS nch l=LA w=WAC m=1
MMI1-M_u6 net1 A3 VSS VSS nch l=LA w=WAC m=1
MMI1-M_u1 ZN A1 VDD VDD pch l=LA w=WAJ m=1
MMI1-M_u3 ZN A3 VDD VDD pch l=LA w=WAJ m=1
MMI1-M_u2 ZN A2 VDD VDD pch l=LA w=WAJ m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    XNR2D1
* View Name:    schematic
************************************************************************

.SUBCKT XNR2D1 A1 A2 VDD VSS ZN
*.PININFO A1:I A2:I ZN:O VDD:B VSS:B
MM_u6-M_u2 net27 net9 net44 VDD pch l=LA w=WAB m=1
MM_u4-M_u3 ZN net44 VDD VDD pch l=LA w=WAJ m=1
MM_u5-M_u3 net5 net27 VDD VDD pch l=LA w=WQ m=1
MM_u8-M_u3 net9 A1 VDD VDD pch l=LA w=WQ m=1
MMI0-M_u2 net5 A1 net44 VDD pch l=LA w=WM m=1
MM_u2-M_u3 net27 A2 VDD VDD pch l=LA w=WAJ m=1
MM_u6-M_u3 net27 A1 net44 VSS nch l=LA w=WK m=1
MMI0-M_u3 net5 net9 net44 VSS nch l=LA w=WF m=1
MM_u8-M_u2 net9 A1 VSS VSS nch l=LA w=WE m=1
MM_u4-M_u2 ZN net44 VSS VSS nch l=LA w=WAC m=1
MM_u2-M_u2 net27 A2 VSS VSS nch l=LA w=WAC m=1
MM_u5-M_u2 net5 net27 VSS VSS nch l=LA w=WF m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    AOI21D0
* View Name:    schematic
************************************************************************

.SUBCKT AOI21D0 A1 A2 B VDD VSS ZN
*.PININFO A1:I A2:I B:I ZN:O VDD:B VSS:B
MMI9 ZN A1 net5 VDD pch l=LA w=WQ m=1
MM_u2 net5 B VDD VDD pch l=LA w=WQ m=1
MMI8 ZN A2 net5 VDD pch l=LA w=WQ m=1
MMI2 ZN A1 net13 VSS nch l=LA w=WE m=1
MMI11 ZN B VSS VSS nch l=LA w=WE m=1
MMI10 net13 A2 VSS VSS nch l=LA w=WE m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    NR2XD0
* View Name:    schematic
************************************************************************

.SUBCKT NR2XD0 A1 A2 VDD VSS ZN
*.PININFO A1:I A2:I ZN:O VDD:B VSS:B
MMI1-M_u3 ZN A2 VSS VSS nch l=LA w=WE m=1
MMI1-M_u4 ZN A1 VSS VSS nch l=LA w=WE m=1
MMI1-M_u1 net13 A2 VDD VDD pch l=LA w=WAJ m=1
MMI1-M_u2 ZN A1 net13 VDD pch l=LA w=WAJ m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    NR2D1
* View Name:    schematic
************************************************************************

.SUBCKT NR2D1 A1 A2 VDD VSS ZN
*.PININFO A1:I A2:I ZN:O VDD:B VSS:B
MMI1-M_u3 ZN A2 VSS VSS nch l=LA w=WAC m=1
MMI1-M_u4 ZN A1 VSS VSS nch l=LA w=WAC m=1
MMI1-M_u1 net13 A2 VDD VDD pch l=LA w=WAJ m=1
MMI1-M_u2 ZN A1 net13 VDD pch l=LA w=WAJ m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    NR3D0
* View Name:    schematic
************************************************************************

.SUBCKT NR3D0 A1 A2 A3 VDD VSS ZN
*.PININFO A1:I A2:I A3:I ZN:O VDD:B VSS:B
MMI3 ZN A1 VSS VSS nch l=LA w=WE m=1
MMI2 ZN A2 VSS VSS nch l=LA w=WE m=1
MM_u4 ZN A3 VSS VSS nch l=LA w=WE m=1
MMI1 ZN A1 net13 VDD pch l=LA w=WAJ m=1
MM_u1 net17 A3 VDD VDD pch l=LA w=WAJ m=1
MMI0 net13 A2 net17 VDD pch l=LA w=WAJ m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    INR2D1
* View Name:    schematic
************************************************************************

.SUBCKT INR2D1 A1 B1 VDD VSS ZN
*.PININFO A1:I B1:I ZN:O VDD:B VSS:B
MMU1-M_u3 ZN net11 VSS VSS nch l=LA w=WAC m=1
MMU1-M_u4 ZN B1 VSS VSS nch l=LA w=WAC m=1
MMU6-M_u2 net11 A1 VSS VSS nch l=LA w=WE m=1
MMU6-M_u3 net11 A1 VDD VDD pch l=LA w=WQ m=1
MMU1-M_u2 ZN B1 net20 VDD pch l=LA w=WAJ m=1
MMU1-M_u1 net20 net11 VDD VDD pch l=LA w=WAJ m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    OAI22D0
* View Name:    schematic
************************************************************************

.SUBCKT OAI22D0 A1 A2 B1 B2 VDD VSS ZN
*.PININFO A1:I A2:I B1:I B2:I ZN:O VDD:B VSS:B
MM_u4 net13 B2 VSS VSS nch l=LA w=WE m=1
MMI8 ZN A2 net13 VSS nch l=LA w=WE m=1
MMI9 ZN A1 net13 VSS nch l=LA w=WE m=1
MMI7 net13 B1 VSS VSS nch l=LA w=WE m=1
MMI4 ZN B1 net32 VDD pch l=LA w=WQ m=1
MMI6 ZN A1 net17 VDD pch l=LA w=WQ m=1
MMU24 net32 B2 VDD VDD pch l=LA w=WQ m=1
MMI5 net17 A2 VDD VDD pch l=LA w=WQ m=1
.ENDS

************************************************************************
* Library Name: model3
* Cell Name:    MDLL_LOGIC_VLOG_DW01_sub_J17_0
* View Name:    schematic
************************************************************************

.SUBCKT MDLL_LOGIC_VLOG_DW01_sub_J17_0 A<6> A<5> A<4> A<3> A<2> A<1> A<0> B<6>
+ B<5> B<4> B<3> B<2> B<1> B<0> DIFF<6> DIFF<5> DIFF<4> DIFF<3> DIFF<2>
+ DIFF<1> DIFF<0> IN0 IN1 IN2 VDD VSS
*.PININFO A<6>:I A<5>:I A<4>:I A<3>:I A<2>:I A<1>:I A<0>:I B<6>:I B<5>:I
*.PININFO B<4>:I B<3>:I B<2>:I B<1>:I B<0>:I CI:I IN0:I IN1:I IN2:I CO:O
*.PININFO DIFF<6>:O DIFF<5>:O DIFF<4>:O DIFF<3>:O DIFF<2>:O DIFF<1>:O
*.PININFO DIFF<0>:O VDD:B VSS:B
XU35 N1 N16 VDD VSS N15 ND2D1
XU45 N10 N12 VDD VSS N22 ND2D1
XU34 N1 N18 VDD VSS N24 ND2D1
XU38 A<3> N41 VDD VSS N36 ND2D1
XU15 IN1 N44 VDD VSS N35 ND2D1
XU6 B<3> N42 VDD VSS N37 ND2D1
XU37 A<1> N54 VDD VSS N27 ND2D1
XU7 B<1> N55 VDD VSS N29 ND2D1
XU10 N23 N18 VDD VSS N10 ND2D1
XU32 N48 N29 VDD VSS N26 ND2D1
XU9 B<0> IN0 VDD VSS N51 IND2D2
XU55 N18 VDD VSS N17 CKND1
XU62 N35 VDD VSS N43 CKND1
XU13 N25 VDD VSS N14 CKND1
XU60 N37 VDD VSS N34 CKND1
XU54 N9 VDD VSS N11 CKND1
XU64 N51 VDD VSS N48 CKND1
XU26 B<0> A<0> N48 VDD VSS DIFF<0> AO21D0
XU8 N37 N36 VDD VSS N40 CKND2D0
XU25 N51 N52 VDD VSS N50 CKND2D0
XU24 N29 N27 VDD VSS N49 CKND2D0
XU20 B<2> A<2> VDD VSS N38 CKND2D0
XU30 N38 N35 VDD VSS N2 AN2XD1
XU28 N38 N37 VDD VSS N1 AN2XD1
XU46 IN2 B<5> VDD VSS N9 IND2D1
XU42 B<4> A<4> VDD VSS N12 IND2D1
XU40 A<4> B<4> VDD VSS N18 IND2D1
XU49 B<2> VDD VSS N44 INVD1
XU43 A<3> VDD VSS N42 INVD1
XU39 A<1> VDD VSS N55 INVD1
XU48 B<0> VDD VSS N53 CKND0
XU21 B<3> VDD VSS N41 CKND0
XU19 B<1> VDD VSS N54 CKND0
XU52 N4 N5 VDD VSS DIFF<6> CKXOR2D1
XU53 B<6> A<6> VDD VSS N5 CKXOR2D1
XU56 N19 N20 VDD VSS DIFF<5> CKXOR2D1
XU57 B<5> IN2 VDD VSS N20 CKXOR2D1
XU59 B<4> A<4> VDD VSS N32 CKXOR2D1
XU58 N31 N32 VDD VSS DIFF<4> CKXOR2D1
XU61 N39 N40 VDD VSS DIFF<3> CKXOR2D1
XU29 N33 N2 VDD VSS DIFF<2> CKXOR2D1
XU27 N34 N35 N36 VDD VSS N23 OAI21D1
XU51 IN0 B<0> VDD VSS N30 IND2D0
XU50 IN0 B<0> VDD VSS N47 IND2D0
XU12 N29 N30 VDD VSS N28 ND2D0
XU11 N29 N47 VDD VSS N46 ND2D0
XU47 N26 N27 N28 VDD VSS N25 ND3D1
XU5 N26 N27 N46 VDD VSS N33 ND3D1
XU63 N49 N50 VDD VSS DIFF<1> XNR2D1
XU17 N14 N15 VDD VSS N6 NR2D0
XU23 IN0 N53 VDD VSS N52 NR2D0
XU16 N1 N33 N23 VDD VSS N31 AOI21D0
XU18 N33 N38 N43 VDD VSS N39 AOI21D0
XU22 N21 N22 VDD VSS N19 NR2XD0
XU36 N17 N11 VDD VSS N16 NR2D1
XU33 N14 N24 VDD VSS N21 NR2D1
XU3 N6 N7 N8 VDD VSS N4 NR3D0
XU31 N9 N10 VDD VSS N8 INR2D1
XU14 N11 N12 B<5> A<5> VDD VSS N7 OAI22D0
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    OR2D1
* View Name:    schematic
************************************************************************

.SUBCKT OR2D1 A1 A2 VDD VSS Z
*.PININFO A1:I A2:I Z:O VDD:B VSS:B
MMU1-M_u2 Z net5 VSS VSS nch l=LA w=WAC m=1
MM_u7-M_u4 net5 A1 VSS VSS nch l=LA w=WE m=1
MM_u7-M_u3 net5 A2 VSS VSS nch l=LA w=WE m=1
MMU1-M_u3 Z net5 VDD VDD pch l=LA w=WAJ m=1
MM_u7-M_u1 net17 A2 VDD VDD pch l=LA w=WAJ m=1
MM_u7-M_u2 net5 A1 net17 VDD pch l=LA w=WAJ m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    AOI21D1
* View Name:    schematic
************************************************************************

.SUBCKT AOI21D1 A1 A2 B VDD VSS ZN
*.PININFO A1:I A2:I B:I ZN:O VDD:B VSS:B
MM_u3 net5 A1 ZN VDD pch l=LA w=WAJ m=1
MM_u2 net5 B VDD VDD pch l=LA w=WAJ m=1
MM_u4 net5 A2 ZN VDD pch l=LA w=WAJ m=1
MMI2 ZN A1 net13 VSS nch l=LA w=WAC m=1
MM_u7 ZN B VSS VSS nch l=LA w=WAC m=1
MMI3 net13 A2 VSS VSS nch l=LA w=WAC m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    OR2XD1
* View Name:    schematic
************************************************************************

.SUBCKT OR2XD1 A1 A2 VDD VSS Z
*.PININFO A1:I A2:I Z:O VDD:B VSS:B
MMU1-M_u2 Z net5 VSS VSS nch l=LA w=WAC m=1
MM_u7-M_u4 net5 A1 VSS VSS nch l=LA w=WAC m=1
MM_u7-M_u3 net5 A2 VSS VSS nch l=LA w=WAC m=1
MMU1-M_u3 Z net5 VDD VDD pch l=LA w=WAJ m=1
MM_u7-M_u1 net17 A2 VDD VDD pch l=LA w=WAJ m=1
MM_u7-M_u2 net5 A1 net17 VDD pch l=LA w=WAJ m=1
.ENDS

************************************************************************
* Library Name: model3
* Cell Name:    MDLL_LOGIC_VLOG_DW01_add_J16_0
* View Name:    schematic
************************************************************************

.SUBCKT MDLL_LOGIC_VLOG_DW01_add_J16_0 A<6> A<5> A<4> A<3> A<2> A<1> A<0> B<6>
+ B<5> B<4> B<3> B<2> B<1> B<0> IN0 IN1 SUM<6> SUM<5> SUM<4> SUM<3>
+ SUM<2> SUM<1> SUM<0> VDD VSS
*.PININFO A<6>:I A<5>:I A<4>:I A<3>:I A<2>:I A<1>:I A<0>:I B<6>:I B<5>:I
*.PININFO B<4>:I B<3>:I B<2>:I B<1>:I B<0>:I CI:I IN0:I IN1:I CO:O SUM<6>:O
*.PININFO SUM<5>:O SUM<4>:O SUM<3>:O SUM<2>:O SUM<1>:O SUM<0>:O VDD:B VSS:B
XU41 A<0> B<0> VDD VSS N19 CKND2D0
XU17 N30 N28 VDD VSS N32 CKND2D0
XU18 B<2> IN1 VDD VSS N34 CKND2D0
XU39 N21 N20 VDD VSS N37 CKND2D0
XU19 B<3> A<3> VDD VSS N28 CKND2D0
XU35 B<0> A<0> VDD VSS N38 CKND2D0
XU14 N11 N12 VDD VSS N10 ND2D1
XU11 N36 N20 VDD VSS N26 ND2D1
XU30 B<1> A<1> VDD VSS N20 ND2D1
XU32 B<3> A<3> VDD VSS N30 OR2D1
XU10 B<1> A<1> VDD VSS N21 OR2D1
XU3 B<2> A<2> VDD VSS N29 IND2D1
XU31 B<4> A<4> VDD VSS N15 IND2D1
XU47 N34 VDD VSS N33 CKND1
XU16 N30 VDD VSS N16 CKND1
XU45 N29 VDD VSS N17 CKND1
XU36 N24 N7 VDD VSS SUM<4> XNR2D1
XU43 B<6> A<6> VDD VSS N9 XNR2D1
XU20 N10 N5 VDD VSS SUM<5> XNR2D1
XU21 B<5> A<5> VDD VSS N5 XNR2D1
XU34 A<0> B<0> VDD VSS N39 NR2D0
XU33 N38 N39 VDD VSS SUM<0> INR2D1
XU27 B<4> IN0 VDD VSS N7 CKXOR2D1
XU42 N8 N9 VDD VSS SUM<6> CKXOR2D1
XU46 N31 N32 VDD VSS SUM<3> CKXOR2D1
XU24 N26 N6 VDD VSS SUM<2> CKXOR2D1
XU23 N37 N38 VDD VSS SUM<1> CKXOR2D1
XU6 B<4> IN0 VDD VSS N2 AN2XD1
XU5 B<5> A<5> VDD VSS N1 AN2XD1
XU8 B<0> A<0> VDD VSS N4 AN2XD1
XU25 N29 N34 VDD VSS N6 AN2XD1
XU13 N21 N4 VDD VSS N36 ND2D0
XU38 IN1 B<2> VDD VSS N27 CKND2D1
XU44 N18 N19 N20 VDD VSS N13 OAI21D1
XU26 N16 N27 N28 VDD VSS N22 OAI21D1
XU15 N26 N29 N33 VDD VSS N31 AOI21D0
XU28 N25 N26 N22 VDD VSS N24 AOI21D1
XU9 N22 N15 N2 VDD VSS N11 AOI21D1
XU29 N3 N10 N1 VDD VSS N8 AOI21D1
XU7 A<5> B<5> VDD VSS N3 OR2XD1
XU37 N21 VDD VSS N18 INVD1
XU12 N16 N17 VDD VSS N14 NR2XD0
XU22 N14 N15 N13 VDD VSS N12 ND3D1
XU40 N16 N17 VDD VSS N25 NR2D1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    IND3D1
* View Name:    schematic
************************************************************************

.SUBCKT IND3D1 A1 B1 B2 VDD VSS ZN
*.PININFO A1:I B1:I B2:I ZN:O VDD:B VSS:B
MMI4 VDD net19 ZN VDD pch l=LA w=WAJ m=1
MMI11 VDD B2 ZN VDD pch l=LA w=WAJ m=1
MM_u16 VDD B1 ZN VDD pch l=LA w=WAJ m=1
MMI5-M_u3 net19 A1 VDD VDD pch l=LA w=WQ m=1
MMI5-M_u2 net19 A1 VSS VSS nch l=LA w=WE m=1
MMI6 net25 B1 net17 VSS nch l=LA w=WAC m=1
MMI12 ZN B2 net25 VSS nch l=LA w=WAC m=1
MMI7 net17 net19 VSS VSS nch l=LA w=WAC m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    HA1D0
* View Name:    schematic
************************************************************************

.SUBCKT HA1D0 A B CO S VDD VSS
*.PININFO A:I B:I CO:O S:O VDD:B VSS:B
MMU1-M_u3 net9 A VDD VDD pch l=LA w=WAJ m=1
MMU7-M_u2 net13 net5 net72 VDD pch l=LA w=WAJ m=1
MMU9-M_u1 net25 A VDD VDD pch l=LA w=WQ m=1
MMU5-M_u3 CO net25 VDD VDD pch l=LA w=WQ m=1
MMU9-M_u2 net25 B VDD VDD pch l=LA w=WQ m=1
MMU2-M_u3 net13 net9 VDD VDD pch l=LA w=WAJ m=1
MMU8-M_u2 net9 B net72 VDD pch l=LA w=WW m=1
MMU3-M_u3 net5 B VDD VDD pch l=LA w=WT m=1
MMU4-M_u3 S net72 VDD VDD pch l=LA w=WQ m=1
MMU8-M_u3 net9 net5 net72 VSS nch l=LA w=WH m=1
MMU9-M_u4 net56 B VSS VSS nch l=LA w=WE m=1
MMU1-M_u2 net9 A VSS VSS nch l=LA w=WAC m=1
MMU4-M_u2 S net72 VSS VSS nch l=LA w=WE m=1
MMU9-M_u3 net25 A net56 VSS nch l=LA w=WE m=1
MMU7-M_u3 net13 B net72 VSS nch l=LA w=WU m=1
MMU3-M_u2 net5 B VSS VSS nch l=LA w=WAC m=1
MMU2-M_u2 net13 net9 VSS VSS nch l=LA w=WAC m=1
MMU5-M_u2 CO net25 VSS VSS nch l=LA w=WE m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    CKXOR2D0
* View Name:    schematic
************************************************************************

.SUBCKT CKXOR2D0 A1 A2 VDD VSS Z
*.PININFO A1:I A2:I Z:O VDD:B VSS:B
MM_u6-M_u3 net37 net17 net44 VSS nch l=LA w=WA m=1
MMI2-M_u2 net17 A1 VSS VSS nch l=LA w=WA m=1
MM_u4-M_u2 Z net44 VSS VSS nch l=LA w=WA m=1
MMI3-M_u3 net5 A1 net44 VSS nch l=LA w=WA m=1
MM_u5-M_u2 net5 net37 VSS VSS nch l=LA w=WA m=1
MMI1-M_u2 net37 A2 VSS VSS nch l=LA w=WA m=1
MMI2-M_u3 net17 A1 VDD VDD pch l=LA w=WQ m=1
MM_u6-M_u2 net37 A1 net44 VDD pch l=LA w=WQ m=1
MMI1-M_u3 net37 A2 VDD VDD pch l=LA w=WQ m=1
MM_u4-M_u3 Z net44 VDD VDD pch l=LA w=WQ m=1
MM_u5-M_u3 net5 net37 VDD VDD pch l=LA w=WQ m=1
MMI3-M_u2 net5 net17 net44 VDD pch l=LA w=WQ m=1
.ENDS

************************************************************************
* Library Name: model3
* Cell Name:    MDLL_LOGIC_VLOG_DW01_inc_0
* View Name:    schematic
************************************************************************

.SUBCKT MDLL_LOGIC_VLOG_DW01_inc_0 A<6> A<5> A<4> A<3> A<2> A<1> A<0> SUM<6>
+ SUM<5> SUM<4> SUM<3> SUM<2> SUM<1> VDD VSS
*.PININFO A<6>:I A<5>:I A<4>:I A<3>:I A<2>:I A<1>:I A<0>:I SUM<6>:O SUM<5>:O
*.PININFO SUM<4>:O SUM<3>:O SUM<2>:O SUM<1>:O SUM<0>:O VDD:B VSS:B
XU10103 A<3> CARRY<3> CARRY<4> SUM<3> VDD VSS HA1D0
XU10101 A<1> A<0> CARRY<2> SUM<1> VDD VSS HA1D0
XU10102 A<2> CARRY<2> CARRY<3> SUM<2> VDD VSS HA1D0
XU10104 A<4> CARRY<4> CARRY<5> SUM<4> VDD VSS HA1D0
XU10105 A<5> CARRY<5> CARRY<6> SUM<5> VDD VSS HA1D0
XU2 CARRY<6> A<6> VDD VSS SUM<6> CKXOR2D0
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    CKAN2D1
* View Name:    schematic
************************************************************************

.SUBCKT CKAN2D1 A1 A2 VDD VSS Z
*.PININFO A1:I A2:I Z:O VDD:B VSS:B
MM_u2-M_u2 net5 A2 VDD VDD pch l=LA w=WE m=1
MM_u2-M_u1 net5 A1 VDD VDD pch l=LA w=WE m=1
MM_u3-M_u3 Z net5 VDD VDD pch l=LA w=WAJ m=1
MM_u2-M_u4 net21 A2 VSS VSS nch l=LA w=WE m=1
MM_u3-M_u2 Z net5 VSS VSS nch l=LA w=WS m=1
MM_u2-M_u3 net5 A1 net21 VSS nch l=LA w=WE m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    AN2D1
* View Name:    schematic
************************************************************************

.SUBCKT AN2D1 A1 A2 VDD VSS Z
*.PININFO A1:I A2:I Z:O VDD:B VSS:B
MM_u3-M_u3 Z net5 VDD VDD pch l=LA w=WAJ m=1
MM_u2-M_u1 net5 A1 VDD VDD pch l=LA w=WQ m=1
MM_u2-M_u2 net5 A2 VDD VDD pch l=LA w=WQ m=1
MM_u3-M_u2 Z net5 VSS VSS nch l=LA w=WAC m=1
MM_u2-M_u4 net17 A2 VSS VSS nch l=LA w=WE m=1
MM_u2-M_u3 net5 A1 net17 VSS nch l=LA w=WE m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    DFCNQD1
* View Name:    schematic
************************************************************************

.SUBCKT DFCNQD1 CDN CP D Q VDD VSS
*.PININFO CDN:I CP:I D:I Q:O VDD:B VSS:B
MMI4 net53 net5 VSS VSS nch l=LA w=WZ m=1
MMI21-M_u3 net81 net51 net9 VSS nch l=LA w=WAC m=1
MMI13-M_u2 net37 net97 VSS VSS nch l=LA w=WB m=1
MMI29 net51 net5 net44 VSS nch l=LA w=WA m=1
MMI15 net37 net63 net51 VSS nch l=LA w=WB m=1
MMI32-M_u2 net63 net5 VSS VSS nch l=LA w=WE m=1
MMI5 net97 D net53 VSS nch l=LA w=WZ m=1
MMI49 net20 CDN VSS VSS nch l=LA w=WA m=1
MMI26 net44 net81 VSS VSS nch l=LA w=WA m=1
MMI48 net17 net37 net20 VSS nch l=LA w=WA m=1
MMI27-M_u2 Q net81 VSS VSS nch l=LA w=WAC m=1
MMI21-M_u4 net9 CDN VSS VSS nch l=LA w=WAC m=1
MMI22-M_u2 net5 CP VSS VSS nch l=LA w=WE m=1
MMI47 net97 net63 net17 VSS nch l=LA w=WA m=1
MMI22-M_u3 net5 CP VDD VDD pch l=LA w=WQ m=1
MMI32-M_u3 net63 net5 VDD VDD pch l=LA w=WQ m=1
MMI43 net101 net37 VDD VDD pch l=LA w=WA m=1
MMI6 net97 D net100 VDD pch l=LA w=WAH m=1
MMI27-M_u3 Q net81 VDD VDD pch l=LA w=WAJ m=1
MMI44 net101 CDN VDD VDD pch l=LA w=WA m=1
MMI13-M_u3 net37 net97 VDD VDD pch l=LA w=WJ m=1
MMI21-M_u1 net81 net51 VDD VDD pch l=LA w=WAD m=1
MMI16 net37 net5 net51 VDD pch l=LA w=WO m=1
MMI24 net72 net81 VDD VDD pch l=LA w=WA m=1
MMI28 net51 net63 net72 VDD pch l=LA w=WA m=1
MMI45 net97 net5 net101 VDD pch l=LA w=WA m=1
MMI7 net100 net63 VDD VDD pch l=LA w=WAH m=1
MMI21-M_u2 net81 CDN VDD VDD pch l=LA w=WAD m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    OAI21D0
* View Name:    schematic
************************************************************************

.SUBCKT OAI21D0 A1 A2 B VDD VSS ZN
*.PININFO A1:I A2:I B:I ZN:O VDD:B VSS:B
MMI16-MI13 net9 A2 VDD VDD pch l=LA w=WQ m=1
MM_u9 ZN B VDD VDD pch l=LA w=WQ m=1
MMI16-MI12 ZN A1 net9 VDD pch l=LA w=WQ m=1
MM_u3 ZN A2 net24 VSS nch l=LA w=WE m=1
MM_u4 net24 B VSS VSS nch l=LA w=WE m=1
MM_u2 ZN A1 net24 VSS nch l=LA w=WE m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    OA211D0
* View Name:    schematic
************************************************************************

.SUBCKT OA211D0 A1 A2 B C VDD VSS Z
*.PININFO A1:I A2:I B:I C:I Z:O VDD:B VSS:B
MMI8 net17 B net20 VSS nch l=LA w=WE m=1
MMI11-M_u2 Z net5 VSS VSS nch l=LA w=WE m=1
MMI9 net20 C VSS VSS nch l=LA w=WE m=1
MM_u2 net5 A1 net17 VSS nch l=LA w=WE m=1
MMI7 net5 A2 net17 VSS nch l=LA w=WE m=1
MMI4 net5 C VDD VDD pch l=LA w=WQ m=1
MMI6 net5 A2 net25 VDD pch l=LA w=WQ m=1
MM_u12 net5 B VDD VDD pch l=LA w=WQ m=1
MMI5 net25 A1 VDD VDD pch l=LA w=WQ m=1
MMI11-M_u3 Z net5 VDD VDD pch l=LA w=WQ m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    AO211D1
* View Name:    schematic
************************************************************************

.SUBCKT AO211D1 A1 A2 B C VDD VSS Z
*.PININFO A1:I A2:I B:I C:I Z:O VDD:B VSS:B
MM_u12 net5 C VSS VSS nch l=LA w=WAC m=1
MMI8-M_u2 Z net5 VSS VSS nch l=LA w=WAC m=1
MMI12-M_u10 net5 A1 net1 VSS nch l=LA w=WAC m=1
MM_u13 net5 B VSS VSS nch l=LA w=WAC m=1
MMI12-M_u11 net1 A2 VSS VSS nch l=LA w=WAC m=1
MMI16-MI12 net33 B net25 VDD pch l=LA w=WAJ m=1
MM_u3 net33 A1 net5 VDD pch l=LA w=WAJ m=1
MMI0 net33 A2 net5 VDD pch l=LA w=WAJ m=1
MMI16-MI13 net25 C VDD VDD pch l=LA w=WAJ m=1
MMI8-M_u3 Z net5 VDD VDD pch l=LA w=WAJ m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    MUX2ND0
* View Name:    schematic
************************************************************************

.SUBCKT MUX2ND0 I0 I1 S VDD VSS ZN
*.PININFO I0:I I1:I S:I ZN:O VDD:B VSS:B
MMI15-M_u3 net37 S VDD VDD pch l=LA w=WQ m=1
MMI111 net13 I0 VDD VDD pch l=LA w=WW m=1
MMI24 net9 I1 VDD VDD pch l=LA w=WAJ m=1
MMI5 ZN S net13 VDD pch l=LA w=WAC m=1
MMI25 ZN net37 net9 VDD pch l=LA w=WAC m=1
MMI15-M_u2 net37 S VSS VSS nch l=LA w=WI m=1
MMI20 net33 I1 VSS VSS nch l=LA w=WAC m=1
MMI12 ZN net37 net32 VSS nch l=LA w=WL m=1
MMI21 ZN S net33 VSS nch l=LA w=WL m=1
MMI19 net32 I0 VSS VSS nch l=LA w=WL m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    DFCNQD4
* View Name:    schematic
************************************************************************

.SUBCKT DFCNQD4 CDN CP D Q VDD VSS
*.PININFO CDN:I CP:I D:I Q:O VDD:B VSS:B
MMI22-M_u3 Q net123 VDD VDD pch l=LA w=WAJ m=1
MMI38 net16 net123 VDD VDD pch l=LA w=WA m=1
MMI32-M_u3 net79 net67 VDD VDD pch l=LA w=WAJ m=1
MMI43 net61 net125 VDD VDD pch l=LA w=WA m=1
MMI6 net9 D net1 VDD pch l=LA w=WAH m=1
MMI31-M_u3 net67 CP VDD VDD pch l=LA w=WAJ m=1
MMI27-M_u3 Q net123 VDD VDD pch l=LA w=WAJ m=1
MMI36-M_u2 net123 CDN VDD VDD pch l=LA w=WAG m=1
MMI44 net61 CDN VDD VDD pch l=LA w=WA m=1
MMI36-M_u1 net123 net13 VDD VDD pch l=LA w=WAG m=1
MMI13-M_u3 net125 net9 VDD VDD pch l=LA w=WJ m=1
MMI24-M_u3 Q net123 VDD VDD pch l=LA w=WAJ m=1
MMI16 net125 net67 net13 VDD pch l=LA w=WR m=1
MMI30-M_u1 net123 net13 VDD VDD pch l=LA w=WAG m=1
MMI30-M_u2 net123 CDN VDD VDD pch l=LA w=WAG m=1
MMI28 net13 net79 net16 VDD pch l=LA w=WA m=1
MMI45 net9 net67 net61 VDD pch l=LA w=WA m=1
MMI25-M_u3 Q net123 VDD VDD pch l=LA w=WAJ m=1
MMI7 net1 net79 VDD VDD pch l=LA w=WAH m=1
MMI24-M_u2 Q net123 VSS VSS nch l=LA w=WAC m=1
MMI30-M_u4 net145 CDN VSS VSS nch l=LA w=WI m=1
MMI4 net112 net67 VSS VSS nch l=LA w=WZ m=1
MMI13-M_u2 net125 net9 VSS VSS nch l=LA w=WF m=1
MMI30-M_u3 net123 net13 net145 VSS nch l=LA w=WI m=1
MMI29 net13 net67 net93 VSS nch l=LA w=WA m=1
MMI15 net125 net79 net13 VSS nch l=LA w=WF m=1
MMI25-M_u2 Q net123 VSS VSS nch l=LA w=WAC m=1
MMI36-M_u3 net123 net13 net97 VSS nch l=LA w=WI m=1
MMI32-M_u2 net79 net67 VSS VSS nch l=LA w=WAC m=1
MMI5 net9 D net112 VSS nch l=LA w=WZ m=1
MMI31-M_u2 net67 CP VSS VSS nch l=LA w=WAC m=1
MMI49 net92 CDN VSS VSS nch l=LA w=WA m=1
MMI36-M_u4 net97 CDN VSS VSS nch l=LA w=WI m=1
MMI26 net93 net123 VSS VSS nch l=LA w=WA m=1
MMI48 net80 net125 net92 VSS nch l=LA w=WA m=1
MMI27-M_u2 Q net123 VSS VSS nch l=LA w=WAC m=1
MMI22-M_u2 Q net123 VSS VSS nch l=LA w=WAC m=1
MMI47 net9 net79 net80 VSS nch l=LA w=WA m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    AO22D1
* View Name:    schematic
************************************************************************

.SUBCKT AO22D1 A1 A2 B1 B2 VDD VSS Z
*.PININFO A1:I A2:I B1:I B2:I Z:O VDD:B VSS:B
MMI20-M_u2 Z net5 VSS VSS nch l=LA w=WAC m=1
MMI29 net13 A2 VSS VSS nch l=LA w=WAC m=1
MMI22 net9 B2 VSS VSS nch l=LA w=WAC m=1
MMI28 net5 A1 net13 VSS nch l=LA w=WAC m=1
MMI21 net5 B1 net9 VSS nch l=LA w=WAC m=1
MMI17 net25 B1 VDD VDD pch l=LA w=WAJ m=1
MMI19 net5 A1 net25 VDD pch l=LA w=WAJ m=1
MMI18 net5 A2 net25 VDD pch l=LA w=WAJ m=1
MMI15 net25 B2 VDD VDD pch l=LA w=WAJ m=1
MMI20-M_u3 Z net5 VDD VDD pch l=LA w=WAJ m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    AOI22D1
* View Name:    schematic
************************************************************************

.SUBCKT AOI22D1 A1 A2 B1 B2 VDD VSS ZN
*.PININFO A1:I A2:I B1:I B2:I ZN:O VDD:B VSS:B
MMI3 ZN B1 net1 VSS nch l=LA w=WAC m=1
MMI9 ZN A1 net5 VSS nch l=LA w=WAC m=1
MMI10 net5 A2 VSS VSS nch l=LA w=WAC m=1
MMI8 net1 B2 VSS VSS nch l=LA w=WAC m=1
MM_u3 net20 A2 ZN VDD pch l=LA w=WAJ m=1
MM_u5 VDD B2 net20 VDD pch l=LA w=WAJ m=1
MM_u2 net20 A1 ZN VDD pch l=LA w=WAJ m=1
MM_u4 VDD B1 net20 VDD pch l=LA w=WAJ m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    AOI222D0
* View Name:    schematic
************************************************************************

.SUBCKT AOI222D0 A1 A2 B1 B2 C1 C2 VDD VSS ZN
*.PININFO A1:I A2:I B1:I B2:I C1:I C2:I ZN:O VDD:B VSS:B
MMI17 net17 B1 net20 VDD pch l=LA w=WQ m=1
MMI16 net17 B2 net20 VDD pch l=LA w=WQ m=1
MMI19 net20 A1 ZN VDD pch l=LA w=WQ m=1
MMU27 VDD C2 net17 VDD pch l=LA w=WQ m=1
MMI18 net20 A2 ZN VDD pch l=LA w=WQ m=1
MMI15 VDD C1 net17 VDD pch l=LA w=WQ m=1
MMI20-M_u10 ZN B1 net25 VSS nch l=LA w=WE m=1
MMI6-M_u11 net40 A2 VSS VSS nch l=LA w=WE m=1
MMI6-M_u10 ZN A1 net40 VSS nch l=LA w=WE m=1
MMI21-M_u10 ZN C1 net36 VSS nch l=LA w=WE m=1
MMI21-M_u11 net36 C2 VSS VSS nch l=LA w=WE m=1
MMI20-M_u11 net25 B2 VSS VSS nch l=LA w=WE m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    AO221D1
* View Name:    schematic
************************************************************************

.SUBCKT AO221D1 A1 A2 B1 B2 C VDD VSS Z
*.PININFO A1:I A2:I B1:I B2:I C:I Z:O VDD:B VSS:B
MMI1-M_u10 net5 A1 net9 VSS nch l=LA w=WAC m=1
MMI17-M_u10 net5 B1 net20 VSS nch l=LA w=WAC m=1
MMI8-M_u2 Z net5 VSS VSS nch l=LA w=WAC m=1
MMI1-M_u11 net9 A2 VSS VSS nch l=LA w=WAC m=1
MMU20 net5 C VSS VSS nch l=LA w=WAC m=1
MMI17-M_u11 net20 B2 VSS VSS nch l=LA w=WAC m=1
MMI5 net44 A1 net5 VDD pch l=LA w=WAJ m=1
MMI2 net33 B2 net44 VDD pch l=LA w=WAJ m=1
MMU22 VDD C net33 VDD pch l=LA w=WAJ m=1
MMI3 net33 B1 net44 VDD pch l=LA w=WAJ m=1
MMI4 net44 A2 net5 VDD pch l=LA w=WAJ m=1
MMI8-M_u3 Z net5 VDD VDD pch l=LA w=WAJ m=1
.ENDS

************************************************************************
* Library Name: model3
* Cell Name:    MDLL_LOGIC_VLOG
* View Name:    schematic
************************************************************************

.SUBCKT MDLL_LOGIC_VLOG CODE<6> CODE<5> CODE<4> CODE<3> CODE<2> CODE<1>
+ CODE<0> COMP EN0DLL FRCODE<6> FRCODE<5> FRCODE<4> FRCODE<3> FRCODE<2>
+ FRCODE<1> FRCODE<0> FREE0RUN REFCLK SAR0EN STATUS<2> STATUS<1> STATUS<0>
+ TRK0EN VDD VSS
*.PININFO COMP:I EN0DLL:I FRCODE<6>:I FRCODE<5>:I FRCODE<4>:I FRCODE<3>:I
*.PININFO FRCODE<2>:I FRCODE<1>:I FRCODE<0>:I FREE0RUN:I REFCLK:I SAR0EN:I
*.PININFO TRK0EN:I CODE<6>:O CODE<5>:O CODE<4>:O CODE<3>:O CODE<2>:O CODE<1>:O
*.PININFO CODE<0>:O STATUS<2>:O STATUS<1>:O STATUS<0>:O VDD:B VSS:B
XU85 N130 VDD VSS N131 CKND0
XU2 SAR0CODE<5> VDD VSS N2 CKND0
XU3 SAR0CODE<2> VDD VSS N3 CKND0
XU4 SAR0CODE<4> VDD VSS N4 CKND0
XU5 SAR0CODE<0> VDD VSS N5 CKND0
XU6 STATUS<0> VDD VSS N6 CKND0
XU1 FREE0RUN VDD VSS N1 CKND0
XU56 N41 N75 N27 N53 VDD VSS N89 AO22D0
XU100 N39 N75 N25 N53 VDD VSS N125 AO22D0
XU106 N1 SAR0CODE<3> FRCODE<3> FREE0RUN VDD VSS CODE<3> AO22D0
XU105 N1 SAR0CODE<2> FRCODE<2> FREE0RUN VDD VSS CODE<2> AO22D0
XU104 N1 SAR0CODE<1> FRCODE<1> FREE0RUN VDD VSS CODE<1> AO22D0
XU103 N1 SAR0CODE<0> FRCODE<0> FREE0RUN VDD VSS CODE<0> AO22D0
XU156 N136 FREE0RUN FRCODE<6> FREE0RUN VDD VSS CODE<6> MOAI22D1
XU155 FREE0RUN N2 FRCODE<5> FREE0RUN VDD VSS CODE<5> MOAI22D1
XU154 FREE0RUN N4 FRCODE<4> FREE0RUN VDD VSS CODE<4> MOAI22D1
XU75 N111 N6 VDD VSS N620 CKAN2D0
XU69 N110 N56 VDD VSS N71 CKAN2D0
XU90 N69 N110 VDD VSS N70 CKAN2D0
XU107 N64 N73 VDD VSS N76 AN2XD1
XU68 N113 N6 VDD VSS N56 AN2XD1
XU63 N640 N108 VDD VSS N55 AN2XD1
XU92 N113 STATUS<0> VDD VSS N69 AN2XD1
XU65 N55 N69 VDD VSS N68 AN2XD1
XU81 N82 N130 N81 VDD VSS N73 AN3D0
XU89 N111 N6 N110 VDD VSS N74 AN3D0
XU57 COMP N88 N118 VDD VSS N53 AN3XD1
XU91 N55 STATUS<0> N111 VDD VSS N67 AN3XD1
XU73 N29 N53 VDD VSS N610 ND2D1
XU72 SAR0CODE<4> N101 VDD VSS N600 ND2D1
XU96 N45 N75 VDD VSS N119 ND2D1
XU95 N31 N53 VDD VSS N120 ND2D1
XU101 N6 N85 VDD VSS N107 ND2D1
XU67 STATUS<1> STATUS<0> VDD VSS N590 ND2D1
XU79 N630 N590 VDD VSS N640 ND2D1
XU66 N640 N108 VDD VSS N110 ND2D1
XU80 STATUS<2> VDD VSS N630 INVD1
XU58 N590 VDD VSS N109 INVD1
XU77 N111 VDD VSS N113 INVD1
XU55 N107 N590 VDD VSS N111 CKND2D2
XU133 N97 N96 VDD VSS N46 CKND2D1
XU153 N133 N132 VDD VSS N48 CKND2D1
XU121 N129 N91 VDD VSS N84 CKND2D1
XU60 STATUS<2> N109 VDD VSS N108 CKND2D1
XU150 SAR0CODE<1> VDD VSS N127 CKND1
XU141 N115 VDD VSS N103 CKND1
XU123 N94 VDD VSS N83 CKND1
XU138 N104 VDD VSS N114 CKND1
XU125 SAR0EN VDD VSS N87 CKND1
XU139 N101 VDD VSS N102 CKND1
XU126 STATUS<1> VDD VSS N85 CKND1
XU129 SAR0CODE<3> VDD VSS N92 CKND1
XU134 N98 VDD VSS N99 CKND1
XU120 N137 VDD VSS N91 CKND1
XU119 N124 VDD VSS N129 CKND1
XU117 COMP VDD VSS N86 CKND1
XU115 N80 VDD VSS N88 CKND1
XU87 N114 N2 VDD VSS N117 CKND2D0
XU71 STATUS<2> N109 VDD VSS N58 CKND2D0
XU157 SAR0CODE<1> N5 VDD VSS N137 IND2D0
XU82 N107 N630 VDD VSS N118 IND2D0
XSUB049 SAR0CODE<6> N2 SAR0CODE<4> SAR0CODE<3> N3 SAR0CODE<1> N5 N74 N70 N71
+ N67 N72 N68 N66 N45 N44 N43 N42 N41 N40 N39 SAR0CODE<0>
+ SAR0CODE<2> SAR0CODE<5> VDD VSS MDLL_LOGIC_VLOG_DW01_sub_J17_0
XADD049 SAR0CODE<6> SAR0CODE<5> N4 SAR0CODE<3> N3 SAR0CODE<1> SAR0CODE<0> N74
+ N70 N71 N67 N72 N68 N66 SAR0CODE<4> SAR0CODE<2> N31 N30 N29
+ N28 N27 N26 N25 VDD VSS MDLL_LOGIC_VLOG_DW01_add_J16_0
XU114 N58 VDD VSS N82 INVD0
XU99 N123 N122 VDD VSS N430 IND2D1
XU118 COMP0REG N86 VDD VSS N81 IND2D1
XU116 TRK0EN N82 VDD VSS N130 IND2D1
XU93 N81 N82 N130 VDD VSS N124 IND3D1
XADD051 SAR0CODE<6> SAR0CODE<5> SAR0CODE<4> SAR0CODE<3> SAR0CODE<2>
+ SAR0CODE<1> SAR0CODE<0> N64 N63 N62 N61 N60 N59 VDD
+ VSS MDLL_LOGIC_VLOG_DW01_inc_0
XU131 N3 N92 N98 VDD VSS N95 OAI21D1
XU151 N5 N127 N137 VDD VSS N128 OAI21D1
XU140 N4 N124 N102 VDD VSS N115 OAI21D1
XU135 N99 N124 N130 VDD VSS N101 OAI21D1
XU122 N91 N124 N130 VDD VSS N94 OAI21D1
XU74 N600 N610 N104 VDD VSS N100 ND3D1
XU94 N120 N119 N118 VDD VSS N121 ND3D1
XU130 N91 N92 N3 VDD VSS N98 ND3D1
XU137 N99 N129 N4 VDD VSS N104 ND3D1
XU70 N113 N6 VDD VSS N65 CKAN2D1
XU64 N55 N65 VDD VSS N66 AN2D2
XU76 N55 N620 VDD VSS N72 AN2D1
XSAR0CODE0REG030 EN0DLL REFCLK N46 SAR0CODE<3> VDD VSS DFCNQD1
XSAR0CODE0REG040 EN0DLL REFCLK N450 SAR0CODE<4> VDD VSS DFCNQD1
XSAR0CODE0REG010 EN0DLL REFCLK N48 SAR0CODE<1> VDD VSS DFCNQD1
XSAR0CODE0REG050 EN0DLL REFCLK N440 SAR0CODE<5> VDD VSS DFCNQD1
XSAR0CODE0REG020 EN0DLL REFCLK N47 SAR0CODE<2> VDD VSS DFCNQD1
XCOMP0REG0REG EN0DLL REFCLK N54 COMP0REG VDD VSS DFCNQD1
XSTATUS0REG010 EN0DLL REFCLK N51 STATUS<1> VDD VSS DFCNQD1
XSTATUS0REG000 EN0DLL REFCLK N52 STATUS<0> VDD VSS DFCNQD1
XSTATUS0REG020 EN0DLL REFCLK N50 STATUS<2> VDD VSS DFCNQD1
XU109 N590 N80 N630 VDD VSS N50 OAI21D0
XU78 STATUS<1> N79 VDD VSS N51 CKXOR2D0
XU112 STATUS<0> N88 VDD VSS N52 CKXOR2D0
XU110 N6 N80 VDD VSS N79 NR2D0
XU113 SAR0EN N58 VDD VSS N80 ND2D0
XU83 N87 N86 N118 N58 VDD VSS N75 OA211D0
XU59 COMP VDD VSS N54 DEL005
XU144 N63 N73 N106 N105 VDD VSS N440 AO211D1
XU127 N60 N73 N90 N89 VDD VSS N47 AO211D1
XU148 N5 N73 N126 N125 VDD VSS N49 AO211D1
XU142 N104 N103 SAR0CODE<5> VDD VSS N106 MUX2ND0
XU124 N84 N83 SAR0CODE<2> VDD VSS N90 MUX2ND0
XU146 N117 N116 SAR0CODE<6> VDD VSS N123 MUX2ND0
XU147 N124 N130 SAR0CODE<0> VDD VSS N126 MUX2ND0
XSAR0CODE0REG000 EN0DLL REFCLK N49 SAR0CODE<0> VDD VSS DFCNQD4
XU88 N121 N76 VDD VSS N122 NR2XD0
XSAR0CODE0REG060 REFCLK N430 SAR0CODE<6> N136 EN0DLL VDD VSS DFSND1
XU84 N129 SAR0CODE<5> N115 VDD VSS N116 AOI21D0
XU143 N44 N75 N30 N53 VDD VSS N105 AO22D1
XU132 N42 N75 N61 N73 VDD VSS N96 AOI22D1
XU152 N59 N73 N131 SAR0CODE<1> VDD VSS N132 AOI22D1
XU98 N28 N53 N129 N95 SAR0CODE<3> N94 VDD VSS N97 AOI222D0
XU97 N40 N75 N129 N128 N26 N53 VDD VSS N133 AOI222D0
XU86 N43 N75 N62 N73 N100 VDD VSS N450 AO221D1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    DCAP8
* View Name:    schematic
************************************************************************

.SUBCKT DCAP8 VDD VSS
*.PININFO VDD:B VSS:B
MMI4 VSS net9 VSS VSS nch l=LC w=WV m=1
MM_u2 net11 net9 VSS VSS nch l=LA w=WV m=1
MMI3 VDD net11 VDD VDD pch l=LC w=WAF m=1
MM_u1 net9 net11 VDD VDD pch l=LA w=WAC m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    OA31D1
* View Name:    schematic
************************************************************************

.SUBCKT OA31D1 A1 A2 A3 B VDD VSS Z
*.PININFO A1:I A2:I A3:I B:I Z:O VDD:B VSS:B
MMU1-M_u2 Z net25 VSS VSS nch l=LA w=WAC m=1
MMI6 net5 A1 net25 VSS nch l=LA w=WAC m=1
MM_u5 VSS B net5 VSS nch l=LA w=WAC m=1
MMI8 net5 A3 net25 VSS nch l=LA w=WAC m=1
MMI7 net5 A2 net25 VSS nch l=LA w=WAC m=1
MMI3 net37 A1 VDD VDD pch l=LA w=WAJ m=1
MMI4 net33 A2 net37 VDD pch l=LA w=WAJ m=1
MMU1-M_u3 Z net25 VDD VDD pch l=LA w=WAJ m=1
MM_u11 net25 B VDD VDD pch l=LA w=WAJ m=1
MMI5 net25 A3 net33 VDD pch l=LA w=WAJ m=1
.ENDS

************************************************************************
* Library Name: model3
* Cell Name:    SEL_LOGIC_V2
* View Name:    schematic
************************************************************************

.SUBCKT SEL_LOGIC_V2 MDLCLK NDIV<5> NDIV<4> NDIV<3> NDIV<2> NDIV<1> NDIV<0>
+ SEL SRST VDD VSS
*.PININFO MDLCLK:I NDIV<5>:I NDIV<4>:I NDIV<3>:I NDIV<2>:I NDIV<1>:I NDIV<0>:I
*.PININFO SRST:I SEL:O VDD:B VSS:B
XCYLCNT0REG010 SRST MDLCLK N1 CYLCNT<1> VDD VSS DFCNQD1
XCYLCNT0REG020 SRST MDLCLK N2 CYLCNT<2> VDD VSS DFCNQD1
XCYLCNT0REG030 SRST MDLCLK N3 CYLCNT<3> VDD VSS DFCNQD1
XCYLCNT0REG040 SRST MDLCLK N4 CYLCNT<4> VDD VSS DFCNQD1
XCYLCNT0REG050 SRST MDLCLK N5 CYLCNT<5> VDD VSS DFCNQD1
XCYLCNT0REG000 SRST MDLCLK N14 CYLCNT<0> VDD VSS DFCNQD1
XU22 CYLCNT<0> VDD VSS N14 INVD1
XU5 N15 N16 N17 SEL VDD VSS N10 OA31D1
XU11 NDIV<4> CYLCNT<4> VDD VSS N20 XNR2D1
XU12 NDIV<2> CYLCNT<2> VDD VSS N19 XNR2D1
XU13 NDIV<5> CYLCNT<5> VDD VSS N18 XNR2D1
XU16 NDIV<3> CYLCNT<3> VDD VSS N21 XNR2D1
XU15 NDIV<1> CYLCNT<1> VDD VSS N22 XNR2D1
XU17 NDIV<0> N14 VDD VSS N15 XNR2D1
XSEL0REG MDLCLK N10 SEL SRST VDD VSS DFSNQD1
XU20 N21 N22 VDD VSS N16 ND2D1
XU6 CYLCNT<1> CYLCNT<0> ADD0190CARRY020 N1 VDD VSS HA1D0
XU7 CYLCNT<3> ADD0190CARRY030 ADD0190CARRY040 N3 VDD VSS HA1D0
XU8 CYLCNT<2> ADD0190CARRY020 ADD0190CARRY030 N2 VDD VSS HA1D0
XU9 CYLCNT<4> ADD0190CARRY040 ADD0190CARRY050 N4 VDD VSS HA1D0
XU18 ADD0190CARRY050 CYLCNT<5> VDD VSS N5 CKXOR2D1
XU21 N18 N19 N20 VDD VSS N17 ND3D1
.ENDS

************************************************************************
* Library Name: model3x
* Cell Name:    MDLL_TOP
* View Name:    schematic
************************************************************************

.SUBCKT Sanitized_model3x_MDLL_TOP CKOUT EN_DLL FRCODE<6> FRCODE<5> FRCODE<4> FRCODE<3>
+ FRCODE<2> FRCODE<1> FRCODE<0> MD_SAR MD_TRK NDIV<5> NDIV<4> NDIV<3> NDIV<2>
+ NDIV<1> NDIV<0> SCLK0 VDD VSS
*.PININFO EN_DLL:I FRCODE<6>:I FRCODE<5>:I FRCODE<4>:I FRCODE<3>:I FRCODE<2>:I
*.PININFO FRCODE<1>:I FRCODE<0>:I MD_SAR:I MD_TRK:I NDIV<5>:I NDIV<4>:I
*.PININFO NDIV<3>:I NDIV<2>:I NDIV<1>:I NDIV<0>:I SCLK0:I CKOUT:O VDD:B VSS:B
XI0 EN_DLL FR MD_SAR MD_TRK net15 net19 SCLK0 SEL_RST net20 VDD VSS
+ MDLL_CKGEN_V1
XI1 net17 EN_DLL CODE<2> CODE<1> CODE<0> net15 CODE<3> CODE<4> CODE<5> CODE<6>
+ net013 VDD VSS DEL_7b
XI3 CODE<6> CODE<5> CODE<4> CODE<3> CODE<2> CODE<1> CODE<0> COMP EN_DLL
+ FRCODE<6> FRCODE<5> FRCODE<4> FRCODE<3> FRCODE<2> FRCODE<1> FRCODE<0> FR
+ net15 net19 net016<0> net016<1> net016<2> net20 VDD VSS MDLL_LOGIC_VLOG
XI10<131> VDD VSS DCAP8
XI10<130> VDD VSS DCAP8
XI10<129> VDD VSS DCAP8
XI10<128> VDD VSS DCAP8
XI10<127> VDD VSS DCAP8
XI10<126> VDD VSS DCAP8
XI10<125> VDD VSS DCAP8
XI10<124> VDD VSS DCAP8
XI10<123> VDD VSS DCAP8
XI10<122> VDD VSS DCAP8
XI10<121> VDD VSS DCAP8
XI10<120> VDD VSS DCAP8
XI10<119> VDD VSS DCAP8
XI10<118> VDD VSS DCAP8
XI10<117> VDD VSS DCAP8
XI10<116> VDD VSS DCAP8
XI10<115> VDD VSS DCAP8
XI10<114> VDD VSS DCAP8
XI10<113> VDD VSS DCAP8
XI10<112> VDD VSS DCAP8
XI10<111> VDD VSS DCAP8
XI10<110> VDD VSS DCAP8
XI10<109> VDD VSS DCAP8
XI10<108> VDD VSS DCAP8
XI10<107> VDD VSS DCAP8
XI10<106> VDD VSS DCAP8
XI10<105> VDD VSS DCAP8
XI10<104> VDD VSS DCAP8
XI10<103> VDD VSS DCAP8
XI10<102> VDD VSS DCAP8
XI10<101> VDD VSS DCAP8
XI10<100> VDD VSS DCAP8
XI10<99> VDD VSS DCAP8
XI10<98> VDD VSS DCAP8
XI10<97> VDD VSS DCAP8
XI10<96> VDD VSS DCAP8
XI10<95> VDD VSS DCAP8
XI10<94> VDD VSS DCAP8
XI10<93> VDD VSS DCAP8
XI10<92> VDD VSS DCAP8
XI10<91> VDD VSS DCAP8
XI10<90> VDD VSS DCAP8
XI10<89> VDD VSS DCAP8
XI10<88> VDD VSS DCAP8
XI10<87> VDD VSS DCAP8
XI10<86> VDD VSS DCAP8
XI10<85> VDD VSS DCAP8
XI10<84> VDD VSS DCAP8
XI10<83> VDD VSS DCAP8
XI10<82> VDD VSS DCAP8
XI10<81> VDD VSS DCAP8
XI10<80> VDD VSS DCAP8
XI10<79> VDD VSS DCAP8
XI10<78> VDD VSS DCAP8
XI10<77> VDD VSS DCAP8
XI10<76> VDD VSS DCAP8
XI10<75> VDD VSS DCAP8
XI10<74> VDD VSS DCAP8
XI10<73> VDD VSS DCAP8
XI10<72> VDD VSS DCAP8
XI10<71> VDD VSS DCAP8
XI10<70> VDD VSS DCAP8
XI10<69> VDD VSS DCAP8
XI10<68> VDD VSS DCAP8
XI10<67> VDD VSS DCAP8
XI10<66> VDD VSS DCAP8
XI10<65> VDD VSS DCAP8
XI10<64> VDD VSS DCAP8
XI10<63> VDD VSS DCAP8
XI10<62> VDD VSS DCAP8
XI10<61> VDD VSS DCAP8
XI10<60> VDD VSS DCAP8
XI10<59> VDD VSS DCAP8
XI10<58> VDD VSS DCAP8
XI10<57> VDD VSS DCAP8
XI10<56> VDD VSS DCAP8
XI10<55> VDD VSS DCAP8
XI10<54> VDD VSS DCAP8
XI10<53> VDD VSS DCAP8
XI10<52> VDD VSS DCAP8
XI10<51> VDD VSS DCAP8
XI10<50> VDD VSS DCAP8
XI10<49> VDD VSS DCAP8
XI10<48> VDD VSS DCAP8
XI10<47> VDD VSS DCAP8
XI10<46> VDD VSS DCAP8
XI10<45> VDD VSS DCAP8
XI10<44> VDD VSS DCAP8
XI10<43> VDD VSS DCAP8
XI10<42> VDD VSS DCAP8
XI10<41> VDD VSS DCAP8
XI10<40> VDD VSS DCAP8
XI10<39> VDD VSS DCAP8
XI10<38> VDD VSS DCAP8
XI10<37> VDD VSS DCAP8
XI10<36> VDD VSS DCAP8
XI10<35> VDD VSS DCAP8
XI10<34> VDD VSS DCAP8
XI10<33> VDD VSS DCAP8
XI10<32> VDD VSS DCAP8
XI10<31> VDD VSS DCAP8
XI10<30> VDD VSS DCAP8
XI10<29> VDD VSS DCAP8
XI10<28> VDD VSS DCAP8
XI10<27> VDD VSS DCAP8
XI10<26> VDD VSS DCAP8
XI10<25> VDD VSS DCAP8
XI10<24> VDD VSS DCAP8
XI10<23> VDD VSS DCAP8
XI10<22> VDD VSS DCAP8
XI10<21> VDD VSS DCAP8
XI10<20> VDD VSS DCAP8
XI10<19> VDD VSS DCAP8
XI10<18> VDD VSS DCAP8
XI10<17> VDD VSS DCAP8
XI10<16> VDD VSS DCAP8
XI10<15> VDD VSS DCAP8
XI10<14> VDD VSS DCAP8
XI10<13> VDD VSS DCAP8
XI10<12> VDD VSS DCAP8
XI10<11> VDD VSS DCAP8
XI10<10> VDD VSS DCAP8
XI10<9> VDD VSS DCAP8
XI10<8> VDD VSS DCAP8
XI10<7> VDD VSS DCAP8
XI10<6> VDD VSS DCAP8
XI10<5> VDD VSS DCAP8
XI10<4> VDD VSS DCAP8
XI10<3> VDD VSS DCAP8
XI10<2> VDD VSS DCAP8
XI10<1> VDD VSS DCAP8
XI10<0> VDD VSS DCAP8
XI2 net17 NDIV<5> NDIV<4> NDIV<3> NDIV<2> NDIV<1> NDIV<0> net16 SEL_RST VDD
+ VSS SEL_LOGIC_V2
XI8 net16 VDD VSS COMP INVD0
XI7 net17 VDD VSS CKOUT CKBD2
XI16 net16 FR VDD VSS net013 OR2D1
.ENDS

