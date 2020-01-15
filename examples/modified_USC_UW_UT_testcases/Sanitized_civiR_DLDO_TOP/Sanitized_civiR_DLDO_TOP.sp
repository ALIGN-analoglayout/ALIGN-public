************************************************************************
* auCdl Netlist:
* 
* Library Name:  civicR
* Top Cell Name: DLDO_TOP
* View Name:     schematic
* Netlisted on:  Mar 22 19:27:06 2019
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
* Cell Name:    DFQD1
* View Name:    schematic
************************************************************************

.SUBCKT DFQD1 CP D Q VDD VSS
*.PININFO CP:I D:I Q:O VDD:B VSS:B
MMI53-M_u2 net7 net13 VSS VSS nch l=LA w=WAC m=1
MMI4 net24 net63 VSS VSS nch l=LA w=WAB m=1
MMI56 net37 net7 VSS VSS nch l=LA w=WA m=1
MMI13-M_u2 net11 net67 VSS VSS nch l=LA w=WAC m=1
MMI50 net11 net25 net13 VSS nch l=LA w=WD m=1
MMI32-M_u2 net25 net63 VSS VSS nch l=LA w=WE m=1
MMI5 net67 D net24 VSS nch l=LA w=WAB m=1
MMI31-M_u2 net63 CP VSS VSS nch l=LA w=WE m=1
MMI49 net13 net63 net37 VSS nch l=LA w=WA m=1
MMI48 net9 net11 VSS VSS nch l=LA w=WA m=1
MMI27-M_u2 Q net7 VSS VSS nch l=LA w=WAC m=1
MMI47 net67 net25 net9 VSS nch l=LA w=WA m=1
MMI53-M_u3 net7 net13 VDD VDD pch l=LA w=WAM m=1
MMI32-M_u3 net25 net63 VDD VDD pch l=LA w=WL m=1
MMI43 net56 net11 VDD VDD pch l=LA w=WA m=1
MMI6 net67 D net49 VDD pch l=LA w=WAI m=1
MMI31-M_u3 net63 CP VDD VDD pch l=LA w=WL m=1
MMI27-M_u3 Q net7 VDD VDD pch l=LA w=WAM m=1
MMI57 net13 net25 net72 VDD pch l=LA w=WA m=1
MMI13-M_u3 net11 net67 VDD VDD pch l=LA w=WAM m=1
MMI52 net11 net63 net13 VDD pch l=LA w=WL m=1
MMI51 net72 net7 VDD VDD pch l=LA w=WA m=1
MMI45 net67 net63 net56 VDD pch l=LA w=WA m=1
MMI7 net49 net25 VDD VDD pch l=LA w=WAI m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    INVD1
* View Name:    schematic
************************************************************************

.SUBCKT INVD1 I VDD VSS ZN
*.PININFO I:I ZN:O VDD:B VSS:B
MMU1-M_u2 ZN I VSS VSS nch l=LA w=WAC m=1
MMU1-M_u3 ZN I VDD VDD pch l=LA w=WAM m=1
.ENDS

************************************************************************
* Library Name: civic
* Cell Name:    ULDO4HVT
* View Name:    schematic
************************************************************************

.SUBCKT ULDO4HVT A D EN RS VDD VO VSS Z
*.PININFO A:I D:I EN:I RS:I Z:O VDD:B VO:B VSS:B
MM16 VSS VO VSS VSS nch_hvt l=LD w=WAO m=1
MM18 Z RS net027 VSS nch_hvt l=LA w=WAC m=1
MMI1-M_u3 net027 net020 VSS VSS nch_hvt l=LA w=WAC m=1
MM14 net021 EN VSS VSS nch_hvt l=LA w=WH m=1
MM13 net21 D net021 VSS nch_hvt l=LA w=WH m=1
MM20 net020 A VSS VSS nch_hvt l=LA w=WAC m=1
MM10 VO net21 VDD VDD pch_hvt l=LA w=WAP m=1
MMI1-M_u2 Z RS VO VDD pch_hvt l=LA w=WAM m=1
MM15 net21 EN VDD VDD pch_hvt l=LA w=WH m=1
MM12 net21 D VDD VDD pch_hvt l=LA w=WH m=1
MM19 net020 A VO VDD pch_hvt l=LA w=WAM m=1
MM17 Z net020 VO VDD pch_hvt l=LA w=WAM m=1
.ENDS

************************************************************************
* Library Name: tcbn65lphvt
* Cell Name:    DCAP16HVT
* View Name:    schematic
************************************************************************

.SUBCKT DCAP16HVT VDD VSS
*.PININFO VDD:B VSS:B
MMI4 VSS net11 VSS VSS nch_hvt l=LB w=WV m=1
MMI8 VSS net11 VSS VSS nch_hvt l=LB w=WV m=1
MM_u2 net5 net11 VSS VSS nch_hvt l=LA w=WV m=1
MMI7 VSS net11 VSS VSS nch_hvt l=LB w=WV m=1
MMI3 VDD net5 VDD VDD pch_hvt l=LB w=WAG m=1
MMI6 VDD net5 VDD VDD pch_hvt l=LB w=WAG m=1
MM_u1 net11 net5 VDD VDD pch_hvt l=LA w=WAC m=1
MMI5 VDD net5 VDD VDD pch_hvt l=LB w=WAG m=1
.ENDS

************************************************************************
* Library Name: civic
* Cell Name:    ULDO_BANK
* View Name:    schematic
************************************************************************

.SUBCKT ULDO_BANK CODE<5> CODE<4> CODE<3> CODE<2> CODE<1> CODE<0> EN RO<0> 
+ RO<64> RO<63> RO<62> RO<61> RO<60> RO<59> RO<58> RO<57> RO<56> RO<55> RO<54> 
+ RO<53> RO<52> RO<51> RO<50> RO<49> RO<48> RO<47> RO<46> RO<45> RO<44> RO<43> 
+ RO<42> RO<41> RO<40> RO<39> RO<38> RO<37> RO<36> RO<35> RO<34> RO<33> RO<32> 
+ RO<31> RO<30> RO<29> RO<28> RO<27> RO<26> RO<25> RO<24> RO<23> RO<22> RO<21> 
+ RO<20> RO<19> RO<18> RO<17> RO<16> RO<15> RO<14> RO<13> RO<12> RO<11> RO<10> 
+ RO<9> RO<8> RO<7> RO<6> RO<5> RO<4> RO<3> RO<2> RO<1> RS_RISING VDD VOUT VSS
*.PININFO CODE<5>:I CODE<4>:I CODE<3>:I CODE<2>:I CODE<1>:I CODE<0>:I EN:I 
*.PININFO RO<0>:I RS_RISING:I RO<64>:O RO<63>:O RO<62>:O RO<61>:O RO<60>:O 
*.PININFO RO<59>:O RO<58>:O RO<57>:O RO<56>:O RO<55>:O RO<54>:O RO<53>:O 
*.PININFO RO<52>:O RO<51>:O RO<50>:O RO<49>:O RO<48>:O RO<47>:O RO<46>:O 
*.PININFO RO<45>:O RO<44>:O RO<43>:O RO<42>:O RO<41>:O RO<40>:O RO<39>:O 
*.PININFO RO<38>:O RO<37>:O RO<36>:O RO<35>:O RO<34>:O RO<33>:O RO<32>:O 
*.PININFO RO<31>:O RO<30>:O RO<29>:O RO<28>:O RO<27>:O RO<26>:O RO<25>:O 
*.PININFO RO<24>:O RO<23>:O RO<22>:O RO<21>:O RO<20>:O RO<19>:O RO<18>:O 
*.PININFO RO<17>:O RO<16>:O RO<15>:O RO<14>:O RO<13>:O RO<12>:O RO<11>:O 
*.PININFO RO<10>:O RO<9>:O RO<8>:O RO<7>:O RO<6>:O RO<5>:O RO<4>:O RO<3>:O 
*.PININFO RO<2>:O RO<1>:O VDD:B VOUT:B VSS:B
XPWB14<3> RO<44> CODE<4> EN RS_RISING VDD VOUT VSS RO<45> / ULDO4HVT
XPWB14<2> RO<45> CODE<4> EN RS_RISING VDD VOUT VSS RO<46> / ULDO4HVT
XPWB14<1> RO<46> CODE<3> EN RS_RISING VDD VOUT VSS RO<47> / ULDO4HVT
XPWB14<0> RO<47> CODE<3> EN RS_RISING VDD VOUT VSS RO<48> / ULDO4HVT
XPWB7<3> RO<28> CODE<4> EN RS_RISING VDD VOUT VSS RO<29> / ULDO4HVT
XPWB7<2> RO<29> CODE<4> EN RS_RISING VDD VOUT VSS RO<30> / ULDO4HVT
XPWB7<1> RO<30> CODE<2> EN RS_RISING VDD VOUT VSS RO<31> / ULDO4HVT
XPWB7<0> RO<31> CODE<2> EN RS_RISING VDD VOUT VSS RO<32> / ULDO4HVT
XPWB6<3> RO<12> CODE<5> EN RS_RISING VDD VOUT VSS RO<13> / ULDO4HVT
XPWB6<2> RO<13> CODE<5> EN RS_RISING VDD VOUT VSS RO<14> / ULDO4HVT
XPWB6<1> RO<14> CODE<5> EN RS_RISING VDD VOUT VSS RO<15> / ULDO4HVT
XPWB6<0> RO<15> CODE<5> EN RS_RISING VDD VOUT VSS RO<16> / ULDO4HVT
XPWB15<3> RO<60> CODE<4> EN RS_RISING VDD VOUT VSS RO<61> / ULDO4HVT
XPWB15<2> RO<61> CODE<4> EN RS_RISING VDD VOUT VSS RO<62> / ULDO4HVT
XPWB15<1> RO<62> CODE<3> EN RS_RISING VDD VOUT VSS RO<63> / ULDO4HVT
XPWB15<0> RO<63> CODE<3> EN RS_RISING VDD VOUT VSS RO<64> / ULDO4HVT
XPWB13<3> RO<56> CODE<4> EN RS_RISING VDD VOUT VSS RO<57> / ULDO4HVT
XPWB13<2> RO<57> CODE<4> EN RS_RISING VDD VOUT VSS RO<58> / ULDO4HVT
XPWB13<1> RO<58> CODE<3> EN RS_RISING VDD VOUT VSS RO<59> / ULDO4HVT
XPWB13<0> RO<59> CODE<3> EN RS_RISING VDD VOUT VSS RO<60> / ULDO4HVT
XPWB12<3> RO<40> CODE<5> EN RS_RISING VDD VOUT VSS RO<41> / ULDO4HVT
XPWB12<2> RO<41> CODE<5> EN RS_RISING VDD VOUT VSS RO<42> / ULDO4HVT
XPWB12<1> RO<42> CODE<5> EN RS_RISING VDD VOUT VSS RO<43> / ULDO4HVT
XPWB12<0> RO<43> CODE<1> EN RS_RISING VDD VOUT VSS RO<44> / ULDO4HVT
XPWB5<3> RO<24> CODE<5> EN RS_RISING VDD VOUT VSS RO<25> / ULDO4HVT
XPWB5<2> RO<25> CODE<5> EN RS_RISING VDD VOUT VSS RO<26> / ULDO4HVT
XPWB5<1> RO<26> CODE<5> EN RS_RISING VDD VOUT VSS RO<27> / ULDO4HVT
XPWB5<0> RO<27> CODE<0> EN RS_RISING VDD VOUT VSS RO<28> / ULDO4HVT
XPWB4<3> RO<8> CODE<5> EN RS_RISING VDD VOUT VSS RO<9> / ULDO4HVT
XPWB4<2> RO<9> CODE<5> EN RS_RISING VDD VOUT VSS RO<10> / ULDO4HVT
XPWB4<1> RO<10> CODE<5> EN RS_RISING VDD VOUT VSS RO<11> / ULDO4HVT
XPWB4<0> RO<11> CODE<5> EN RS_RISING VDD VOUT VSS RO<12> / ULDO4HVT
XPWB11<3> RO<52> CODE<5> EN RS_RISING VDD VOUT VSS RO<53> / ULDO4HVT
XPWB11<2> RO<53> CODE<5> EN RS_RISING VDD VOUT VSS RO<54> / ULDO4HVT
XPWB11<1> RO<54> CODE<3> EN RS_RISING VDD VOUT VSS RO<55> / ULDO4HVT
XPWB11<0> RO<55> CODE<3> EN RS_RISING VDD VOUT VSS RO<56> / ULDO4HVT
XPWB10<3> RO<36> CODE<5> EN RS_RISING VDD VOUT VSS RO<37> / ULDO4HVT
XPWB10<2> RO<37> CODE<5> EN RS_RISING VDD VOUT VSS RO<38> / ULDO4HVT
XPWB10<1> RO<38> CODE<5> EN RS_RISING VDD VOUT VSS RO<39> / ULDO4HVT
XPWB10<0> RO<39> CODE<1> EN RS_RISING VDD VOUT VSS RO<40> / ULDO4HVT
XPWB3<3> RO<20> CODE<5> EN RS_RISING VDD VOUT VSS RO<21> / ULDO4HVT
XPWB3<2> RO<21> CODE<5> EN RS_RISING VDD VOUT VSS RO<22> / ULDO4HVT
XPWB3<1> RO<22> CODE<2> EN RS_RISING VDD VOUT VSS RO<23> / ULDO4HVT
XPWB3<0> RO<23> CODE<2> EN RS_RISING VDD VOUT VSS RO<24> / ULDO4HVT
XPWB2<3> RO<4> CODE<5> EN RS_RISING VDD VOUT VSS RO<5> / ULDO4HVT
XPWB2<2> RO<5> CODE<5> EN RS_RISING VDD VOUT VSS RO<6> / ULDO4HVT
XPWB2<1> RO<6> CODE<5> EN RS_RISING VDD VOUT VSS RO<7> / ULDO4HVT
XPWB2<0> RO<7> CODE<5> EN RS_RISING VDD VOUT VSS RO<8> / ULDO4HVT
XPWB9<3> RO<48> CODE<4> EN RS_RISING VDD VOUT VSS RO<49> / ULDO4HVT
XPWB9<2> RO<49> CODE<4> EN RS_RISING VDD VOUT VSS RO<50> / ULDO4HVT
XPWB9<1> RO<50> CODE<4> EN RS_RISING VDD VOUT VSS RO<51> / ULDO4HVT
XPWB9<0> RO<51> CODE<4> EN RS_RISING VDD VOUT VSS RO<52> / ULDO4HVT
XPBW8<3> RO<32> CODE<5> EN RS_RISING VDD VOUT VSS RO<33> / ULDO4HVT
XPBW8<2> RO<33> CODE<5> EN RS_RISING VDD VOUT VSS RO<34> / ULDO4HVT
XPBW8<1> RO<34> CODE<5> EN RS_RISING VDD VOUT VSS RO<35> / ULDO4HVT
XPBW8<0> RO<35> CODE<5> EN RS_RISING VDD VOUT VSS RO<36> / ULDO4HVT
XPWB1<3> RO<16> CODE<4> EN RS_RISING VDD VOUT VSS RO<17> / ULDO4HVT
XPWB1<2> RO<17> CODE<4> EN RS_RISING VDD VOUT VSS RO<18> / ULDO4HVT
XPWB1<1> RO<18> CODE<4> EN RS_RISING VDD VOUT VSS RO<19> / ULDO4HVT
XPWB1<0> RO<19> CODE<4> EN RS_RISING VDD VOUT VSS RO<20> / ULDO4HVT
XPWB0<3> RO<0> CODE<5> EN RS_RISING VDD VOUT VSS RO<1> / ULDO4HVT
XPWB0<2> RO<1> CODE<5> EN RS_RISING VDD VOUT VSS RO<2> / ULDO4HVT
XPWB0<1> RO<2> CODE<5> EN RS_RISING VDD VOUT VSS RO<3> / ULDO4HVT
XPWB0<0> RO<3> EN EN RS_RISING VDD VOUT VSS RO<4> / ULDO4HVT
XDDCP<47> VDD VSS / DCAP16HVT
XDDCP<46> VDD VSS / DCAP16HVT
XDDCP<45> VDD VSS / DCAP16HVT
XDDCP<44> VDD VSS / DCAP16HVT
XDDCP<43> VDD VSS / DCAP16HVT
XDDCP<42> VDD VSS / DCAP16HVT
XDDCP<41> VDD VSS / DCAP16HVT
XDDCP<40> VDD VSS / DCAP16HVT
XDDCP<39> VDD VSS / DCAP16HVT
XDDCP<38> VDD VSS / DCAP16HVT
XDDCP<37> VDD VSS / DCAP16HVT
XDDCP<36> VDD VSS / DCAP16HVT
XDDCP<35> VDD VSS / DCAP16HVT
XDDCP<34> VDD VSS / DCAP16HVT
XDDCP<33> VDD VSS / DCAP16HVT
XDDCP<32> VDD VSS / DCAP16HVT
XDDCP<31> VDD VSS / DCAP16HVT
XDDCP<30> VDD VSS / DCAP16HVT
XDDCP<29> VDD VSS / DCAP16HVT
XDDCP<28> VDD VSS / DCAP16HVT
XDDCP<27> VDD VSS / DCAP16HVT
XDDCP<26> VDD VSS / DCAP16HVT
XDDCP<25> VDD VSS / DCAP16HVT
XDDCP<24> VDD VSS / DCAP16HVT
XDDCP<23> VDD VSS / DCAP16HVT
XDDCP<22> VDD VSS / DCAP16HVT
XDDCP<21> VDD VSS / DCAP16HVT
XDDCP<20> VDD VSS / DCAP16HVT
XDDCP<19> VDD VSS / DCAP16HVT
XDDCP<18> VDD VSS / DCAP16HVT
XDDCP<17> VDD VSS / DCAP16HVT
XDDCP<16> VDD VSS / DCAP16HVT
XDDCP<15> VDD VSS / DCAP16HVT
XDDCP<14> VDD VSS / DCAP16HVT
XDDCP<13> VDD VSS / DCAP16HVT
XDDCP<12> VDD VSS / DCAP16HVT
XDDCP<11> VDD VSS / DCAP16HVT
XDDCP<10> VDD VSS / DCAP16HVT
XDDCP<9> VDD VSS / DCAP16HVT
XDDCP<8> VDD VSS / DCAP16HVT
XDDCP<7> VDD VSS / DCAP16HVT
XDDCP<6> VDD VSS / DCAP16HVT
XDDCP<5> VDD VSS / DCAP16HVT
XDDCP<4> VDD VSS / DCAP16HVT
XDDCP<3> VDD VSS / DCAP16HVT
XDDCP<2> VDD VSS / DCAP16HVT
XDDCP<1> VDD VSS / DCAP16HVT
XDDCP<0> VDD VSS / DCAP16HVT
.ENDS

************************************************************************
* Library Name: tcbn65lphvt
* Cell Name:    INVD0HVT
* View Name:    schematic
************************************************************************

.SUBCKT INVD0HVT I VDD VSS ZN
*.PININFO I:I ZN:O VDD:B VSS:B
MMU1-M_u2 ZN I VSS VSS nch_hvt l=LA w=WE m=1
MMU1-M_u3 ZN I VDD VDD pch_hvt l=LA w=WL m=1
.ENDS

************************************************************************
* Library Name: tcbn65lphvt
* Cell Name:    ND2D0HVT
* View Name:    schematic
************************************************************************

.SUBCKT ND2D0HVT A1 A2 VDD VSS ZN
*.PININFO A1:I A2:I ZN:O VDD:B VSS:B
MMI0-M_u3 ZN A1 net1 VSS nch_hvt l=LA w=WE m=1
MMI0-M_u4 net1 A2 VSS VSS nch_hvt l=LA w=WE m=1
MMI0-M_u1 ZN A1 VDD VDD pch_hvt l=LA w=WL m=1
MMI0-M_u2 ZN A2 VDD VDD pch_hvt l=LA w=WL m=1
.ENDS

************************************************************************
* Library Name: civic
* Cell Name:    Dlvlxft_16B
* View Name:    schematic
************************************************************************

.SUBCKT Dlvlxft_16B BUS_IN<15> BUS_IN<14> BUS_IN<13> BUS_IN<12> BUS_IN<11> 
+ BUS_IN<10> BUS_IN<9> BUS_IN<8> BUS_IN<7> BUS_IN<6> BUS_IN<5> BUS_IN<4> 
+ BUS_IN<3> BUS_IN<2> BUS_IN<1> BUS_IN<0> BUS_OUT<15> BUS_OUT<14> BUS_OUT<13> 
+ BUS_OUT<12> BUS_OUT<11> BUS_OUT<10> BUS_OUT<9> BUS_OUT<8> BUS_OUT<7> 
+ BUS_OUT<6> BUS_OUT<5> BUS_OUT<4> BUS_OUT<3> BUS_OUT<2> BUS_OUT<1> BUS_OUT<0> 
+ BUS_OUTN<15> BUS_OUTN<14> BUS_OUTN<13> BUS_OUTN<12> BUS_OUTN<11> 
+ BUS_OUTN<10> BUS_OUTN<9> BUS_OUTN<8> BUS_OUTN<7> BUS_OUTN<6> BUS_OUTN<5> 
+ BUS_OUTN<4> BUS_OUTN<3> BUS_OUTN<2> BUS_OUTN<1> BUS_OUTN<0> VDD VSS
*.PININFO BUS_IN<15>:I BUS_IN<14>:I BUS_IN<13>:I BUS_IN<12>:I BUS_IN<11>:I 
*.PININFO BUS_IN<10>:I BUS_IN<9>:I BUS_IN<8>:I BUS_IN<7>:I BUS_IN<6>:I 
*.PININFO BUS_IN<5>:I BUS_IN<4>:I BUS_IN<3>:I BUS_IN<2>:I BUS_IN<1>:I 
*.PININFO BUS_IN<0>:I BUS_OUT<15>:O BUS_OUT<14>:O BUS_OUT<13>:O BUS_OUT<12>:O 
*.PININFO BUS_OUT<11>:O BUS_OUT<10>:O BUS_OUT<9>:O BUS_OUT<8>:O BUS_OUT<7>:O 
*.PININFO BUS_OUT<6>:O BUS_OUT<5>:O BUS_OUT<4>:O BUS_OUT<3>:O BUS_OUT<2>:O 
*.PININFO BUS_OUT<1>:O BUS_OUT<0>:O BUS_OUTN<15>:O BUS_OUTN<14>:O 
*.PININFO BUS_OUTN<13>:O BUS_OUTN<12>:O BUS_OUTN<11>:O BUS_OUTN<10>:O 
*.PININFO BUS_OUTN<9>:O BUS_OUTN<8>:O BUS_OUTN<7>:O BUS_OUTN<6>:O 
*.PININFO BUS_OUTN<5>:O BUS_OUTN<4>:O BUS_OUTN<3>:O BUS_OUTN<2>:O 
*.PININFO BUS_OUTN<1>:O BUS_OUTN<0>:O VDD:B VSS:B
XI2<15> BUS_IN<15> VDD VSS N<15> / INVD0HVT
XI2<14> BUS_IN<14> VDD VSS N<14> / INVD0HVT
XI2<13> BUS_IN<13> VDD VSS N<13> / INVD0HVT
XI2<12> BUS_IN<12> VDD VSS N<12> / INVD0HVT
XI2<11> BUS_IN<11> VDD VSS N<11> / INVD0HVT
XI2<10> BUS_IN<10> VDD VSS N<10> / INVD0HVT
XI2<9> BUS_IN<9> VDD VSS N<9> / INVD0HVT
XI2<8> BUS_IN<8> VDD VSS N<8> / INVD0HVT
XI2<7> BUS_IN<7> VDD VSS N<7> / INVD0HVT
XI2<6> BUS_IN<6> VDD VSS N<6> / INVD0HVT
XI2<5> BUS_IN<5> VDD VSS N<5> / INVD0HVT
XI2<4> BUS_IN<4> VDD VSS N<4> / INVD0HVT
XI2<3> BUS_IN<3> VDD VSS N<3> / INVD0HVT
XI2<2> BUS_IN<2> VDD VSS N<2> / INVD0HVT
XI2<1> BUS_IN<1> VDD VSS N<1> / INVD0HVT
XI2<0> BUS_IN<0> VDD VSS N<0> / INVD0HVT
XI1<15> N<15> BUS_OUTN<15> VDD VSS BUS_OUT<15> / ND2D0HVT
XI1<14> N<14> BUS_OUTN<14> VDD VSS BUS_OUT<14> / ND2D0HVT
XI1<13> N<13> BUS_OUTN<13> VDD VSS BUS_OUT<13> / ND2D0HVT
XI1<12> N<12> BUS_OUTN<12> VDD VSS BUS_OUT<12> / ND2D0HVT
XI1<11> N<11> BUS_OUTN<11> VDD VSS BUS_OUT<11> / ND2D0HVT
XI1<10> N<10> BUS_OUTN<10> VDD VSS BUS_OUT<10> / ND2D0HVT
XI1<9> N<9> BUS_OUTN<9> VDD VSS BUS_OUT<9> / ND2D0HVT
XI1<8> N<8> BUS_OUTN<8> VDD VSS BUS_OUT<8> / ND2D0HVT
XI1<7> N<7> BUS_OUTN<7> VDD VSS BUS_OUT<7> / ND2D0HVT
XI1<6> N<6> BUS_OUTN<6> VDD VSS BUS_OUT<6> / ND2D0HVT
XI1<5> N<5> BUS_OUTN<5> VDD VSS BUS_OUT<5> / ND2D0HVT
XI1<4> N<4> BUS_OUTN<4> VDD VSS BUS_OUT<4> / ND2D0HVT
XI1<3> N<3> BUS_OUTN<3> VDD VSS BUS_OUT<3> / ND2D0HVT
XI1<2> N<2> BUS_OUTN<2> VDD VSS BUS_OUT<2> / ND2D0HVT
XI1<1> N<1> BUS_OUTN<1> VDD VSS BUS_OUT<1> / ND2D0HVT
XI1<0> N<0> BUS_OUTN<0> VDD VSS BUS_OUT<0> / ND2D0HVT
XI3<15> BUS_IN<15> BUS_OUT<15> VDD VSS BUS_OUTN<15> / ND2D0HVT
XI3<14> BUS_IN<14> BUS_OUT<14> VDD VSS BUS_OUTN<14> / ND2D0HVT
XI3<13> BUS_IN<13> BUS_OUT<13> VDD VSS BUS_OUTN<13> / ND2D0HVT
XI3<12> BUS_IN<12> BUS_OUT<12> VDD VSS BUS_OUTN<12> / ND2D0HVT
XI3<11> BUS_IN<11> BUS_OUT<11> VDD VSS BUS_OUTN<11> / ND2D0HVT
XI3<10> BUS_IN<10> BUS_OUT<10> VDD VSS BUS_OUTN<10> / ND2D0HVT
XI3<9> BUS_IN<9> BUS_OUT<9> VDD VSS BUS_OUTN<9> / ND2D0HVT
XI3<8> BUS_IN<8> BUS_OUT<8> VDD VSS BUS_OUTN<8> / ND2D0HVT
XI3<7> BUS_IN<7> BUS_OUT<7> VDD VSS BUS_OUTN<7> / ND2D0HVT
XI3<6> BUS_IN<6> BUS_OUT<6> VDD VSS BUS_OUTN<6> / ND2D0HVT
XI3<5> BUS_IN<5> BUS_OUT<5> VDD VSS BUS_OUTN<5> / ND2D0HVT
XI3<4> BUS_IN<4> BUS_OUT<4> VDD VSS BUS_OUTN<4> / ND2D0HVT
XI3<3> BUS_IN<3> BUS_OUT<3> VDD VSS BUS_OUTN<3> / ND2D0HVT
XI3<2> BUS_IN<2> BUS_OUT<2> VDD VSS BUS_OUTN<2> / ND2D0HVT
XI3<1> BUS_IN<1> BUS_OUT<1> VDD VSS BUS_OUTN<1> / ND2D0HVT
XI3<0> BUS_IN<0> BUS_OUT<0> VDD VSS BUS_OUTN<0> / ND2D0HVT
.ENDS

************************************************************************
* Library Name: tcbn65lphvt
* Cell Name:    CKND1HVT
* View Name:    schematic
************************************************************************

.SUBCKT CKND1HVT I VDD VSS ZN
*.PININFO I:I ZN:O VDD:B VSS:B
MM_u2 ZN I VSS VSS nch_hvt l=LA w=WW m=1
MM_u1 ZN I VDD VDD pch_hvt l=LA w=WAM m=1
.ENDS

************************************************************************
* Library Name: tcbn65lphvt
* Cell Name:    MUX3D1HVT
* View Name:    schematic
************************************************************************

.SUBCKT MUX3D1HVT I0 I1 I2 S0 S1 VDD VSS Z
*.PININFO I0:I I1:I I2:I S0:I S1:I Z:O VDD:B VSS:B
MMI22-M_u3 net37 net13 net25 VSS nch_hvt l=LA w=WH m=1
MMI4-M_u3 net33 S0 net25 VSS nch_hvt l=LA w=WI m=1
MMI12-M_u2 net37 I0 VSS VSS nch_hvt l=LA w=WH m=1
MMI5-M_u3 net25 net9 net79 VSS nch_hvt l=LA w=WF m=1
MMU95-M_u2 net5 I2 VSS VSS nch_hvt l=LA w=WAC m=1
MMI14-M_u2 net33 I1 VSS VSS nch_hvt l=LA w=WAC m=1
MMI3-M_u2 net13 S0 VSS VSS nch_hvt l=LA w=WE m=1
MMU19-M_u2 net9 S1 VSS VSS nch_hvt l=LA w=WE m=1
MMI6-M_u3 net5 S1 net79 VSS nch_hvt l=LA w=WX m=1
MMU18-M_u2 Z net79 VSS VSS nch_hvt l=LA w=WAC m=1
MMU18-M_u3 Z net79 VDD VDD pch_hvt l=LA w=WAM m=1
MMI5-M_u2 net25 S1 net79 VDD pch_hvt l=LA w=WL m=1
MMI14-M_u3 net33 I1 VDD VDD pch_hvt l=LA w=WAM m=1
MMU19-M_u3 net9 S1 VDD VDD pch_hvt l=LA w=WL m=1
MMU95-M_u3 net5 I2 VDD VDD pch_hvt l=LA w=WAM m=1
MMI4-M_u2 net33 net13 net25 VDD pch_hvt l=LA w=WZ m=1
MMI3-M_u3 net13 S0 VDD VDD pch_hvt l=LA w=WL m=1
MMI6-M_u2 net5 net9 net79 VDD pch_hvt l=LA w=WAH m=1
MMI12-M_u3 net37 I0 VDD VDD pch_hvt l=LA w=WY m=1
MMI22-M_u2 net37 S0 net25 VDD pch_hvt l=LA w=WAF m=1
.ENDS

************************************************************************
* Library Name: civic
* Cell Name:    PWR_BANK
* View Name:    schematic
************************************************************************

.SUBCKT PWR_BANK CODE<5> CODE<4> CODE<3> CODE<2> CODE<1> CODE<0> DOUT<0> 
+ DOUT<1> DOUT<2> DOUT<3> DOUT<4> DOUT<5> DOUT<6> DOUT<7> DOUT<8> DOUT<9> 
+ DOUT<10> DOUT<11> DOUT<12> DOUT<13> DOUT<14> DOUT<15> EN MCLK RS_RISING 
+ SEL<1> SEL<0> SYSCLK VDD VOUT VSS
*.PININFO CODE<5>:I CODE<4>:I CODE<3>:I CODE<2>:I CODE<1>:I CODE<0>:I EN:I 
*.PININFO RS_RISING:I SEL<1>:I SEL<0>:I SYSCLK:I DOUT<0>:O DOUT<1>:O DOUT<2>:O 
*.PININFO DOUT<3>:O DOUT<4>:O DOUT<5>:O DOUT<6>:O DOUT<7>:O DOUT<8>:O 
*.PININFO DOUT<9>:O DOUT<10>:O DOUT<11>:O DOUT<12>:O DOUT<13>:O DOUT<14>:O 
*.PININFO DOUT<15>:O MCLK:O VDD:B VOUT:B VSS:B
XI30 CODE<5> CODE<4> CODE<3> CODE<2> CODE<1> CODE<0> EN RO<0> RO<64> RO<63> 
+ RO<62> RO<61> RO<60> RO<59> RO<58> RO<57> RO<56> RO<55> RO<54> RO<53> RO<52> 
+ RO<51> RO<50> RO<49> RO<48> RO<47> RO<46> RO<45> RO<44> RO<43> RO<42> RO<41> 
+ RO<40> RO<39> RO<38> RO<37> RO<36> RO<35> RO<34> RO<33> RO<32> RO<31> RO<30> 
+ RO<29> RO<28> RO<27> RO<26> RO<25> RO<24> RO<23> RO<22> RO<21> RO<20> RO<19> 
+ RO<18> RO<17> RO<16> RO<15> RO<14> RO<13> RO<12> RO<11> RO<10> RO<9> RO<8> 
+ RO<7> RO<6> RO<5> RO<4> RO<3> RO<2> RO<1> RS_RISING VDD VOUT VSS / ULDO_BANK
XI16 RO<4> RO<8> RO<12> RO<16> RO<20> RO<24> RO<28> RO<32> RO<36> RO<40> 
+ RO<44> RO<48> RO<52> RO<56> RO<60> RO<64> DOUT<0> DOUT<1> DOUT<2> DOUT<3> 
+ DOUT<4> DOUT<5> DOUT<6> DOUT<7> DOUT<8> DOUT<9> DOUT<10> DOUT<11> DOUT<12> 
+ DOUT<13> DOUT<14> DOUT<15> DOUTN<0> DOUTN<1> DOUTN<2> DOUTN<3> DOUTN<4> 
+ DOUTN<5> DOUTN<6> DOUTN<7> DOUTN<8> DOUTN<9> DOUTN<10> DOUTN<11> DOUTN<12> 
+ DOUTN<13> DOUTN<14> DOUTN<15> VDD VSS / Dlvlxft_16B
XI28 DOUT<0> VDD VSS MCLK / CKND1HVT
XI27 SYSCLK DOUTN<7> DOUTN<15> SEL<0> SEL<1> VDD VSS RO<0> / MUX3D1HVT
.ENDS

************************************************************************
* Library Name: tcbn65lphvt
* Cell Name:    DCAP8HVT
* View Name:    schematic
************************************************************************

.SUBCKT DCAP8HVT VDD VSS
*.PININFO VDD:B VSS:B
MMI4 VSS net9 VSS VSS nch_hvt l=LC w=WV m=1
MM_u2 net11 net9 VSS VSS nch_hvt l=LA w=WV m=1
MMI3 VDD net11 VDD VDD pch_hvt l=LC w=WAG m=1
MM_u1 net9 net11 VDD VDD pch_hvt l=LA w=WAC m=1
.ENDS

************************************************************************
* Library Name: tcbn65lphvt
* Cell Name:    INVD1HVT
* View Name:    schematic
************************************************************************

.SUBCKT INVD1HVT I VDD VSS ZN
*.PININFO I:I ZN:O VDD:B VSS:B
MMU1-M_u2 ZN I VSS VSS nch_hvt l=LA w=WAC m=1
MMU1-M_u3 ZN I VDD VDD pch_hvt l=LA w=WAM m=1
.ENDS

************************************************************************
* Library Name: tcbn65lphvt
* Cell Name:    AN2D4HVT
* View Name:    schematic
************************************************************************

.SUBCKT AN2D4HVT A1 A2 VDD VSS Z
*.PININFO A1:I A2:I Z:O VDD:B VSS:B
MM_u3_2-M_u3 Z net5 VDD VDD pch_hvt l=LA w=WAM m=1
MM_u3_1-M_u3 Z net5 VDD VDD pch_hvt l=LA w=WAM m=1
MM_u3_0-M_u3 Z net5 VDD VDD pch_hvt l=LA w=WAM m=1
MM_u3_3-M_u3 Z net5 VDD VDD pch_hvt l=LA w=WAM m=1
MM_u2_0-M_u1 net5 A1 VDD VDD pch_hvt l=LA w=WAM m=1
MM_u2_1-M_u1 net5 A1 VDD VDD pch_hvt l=LA w=WAM m=1
MM_u2_0-M_u2 net5 A2 VDD VDD pch_hvt l=LA w=WAM m=1
MM_u2_1-M_u2 net5 A2 VDD VDD pch_hvt l=LA w=WAM m=1
MM_u3_1-M_u2 Z net5 VSS VSS nch_hvt l=LA w=WAC m=1
MM_u2_0-M_u4 net57 A2 VSS VSS nch_hvt l=LA w=WAC m=1
MM_u3_2-M_u2 Z net5 VSS VSS nch_hvt l=LA w=WAC m=1
MM_u2_1-M_u4 net44 A2 VSS VSS nch_hvt l=LA w=WAC m=1
MM_u3_3-M_u2 Z net5 VSS VSS nch_hvt l=LA w=WAC m=1
MM_u2_1-M_u3 net5 A1 net44 VSS nch_hvt l=LA w=WAC m=1
MM_u2_0-M_u3 net5 A1 net57 VSS nch_hvt l=LA w=WAC m=1
MM_u3_0-M_u2 Z net5 VSS VSS nch_hvt l=LA w=WAC m=1
.ENDS

************************************************************************
* Library Name: tcbn65lphvt
* Cell Name:    INVD16HVT
* View Name:    schematic
************************************************************************

.SUBCKT INVD16HVT I VDD VSS ZN
*.PININFO I:I ZN:O VDD:B VSS:B
MMI2_9-M_u3 ZN I VDD VDD pch_hvt l=LA w=WAM m=1
MMI2_6-M_u3 ZN I VDD VDD pch_hvt l=LA w=WAM m=1
MMI2_1-M_u3 ZN I VDD VDD pch_hvt l=LA w=WAM m=1
MMI2_4-M_u3 ZN I VDD VDD pch_hvt l=LA w=WAM m=1
MMI2_12-M_u3 ZN I VDD VDD pch_hvt l=LA w=WAM m=1
MMI2_13-M_u3 ZN I VDD VDD pch_hvt l=LA w=WAM m=1
MMI2_3-M_u3 ZN I VDD VDD pch_hvt l=LA w=WAM m=1
MMI2_10-M_u3 ZN I VDD VDD pch_hvt l=LA w=WAM m=1
MMI2_0-M_u3 ZN I VDD VDD pch_hvt l=LA w=WAM m=1
MMI2_11-M_u3 ZN I VDD VDD pch_hvt l=LA w=WAM m=1
MMI2_7-M_u3 ZN I VDD VDD pch_hvt l=LA w=WAM m=1
MMI2_5-M_u3 ZN I VDD VDD pch_hvt l=LA w=WAM m=1
MMI2_2-M_u3 ZN I VDD VDD pch_hvt l=LA w=WAM m=1
MMI2_8-M_u3 ZN I VDD VDD pch_hvt l=LA w=WAM m=1
MMI2_15-M_u3 ZN I VDD VDD pch_hvt l=LA w=WAM m=1
MMI2_14-M_u3 ZN I VDD VDD pch_hvt l=LA w=WAM m=1
MMI2_12-M_u2 ZN I VSS VSS nch_hvt l=LA w=WAC m=1
MMI2_15-M_u2 ZN I VSS VSS nch_hvt l=LA w=WAC m=1
MMI2_3-M_u2 ZN I VSS VSS nch_hvt l=LA w=WAC m=1
MMI2_14-M_u2 ZN I VSS VSS nch_hvt l=LA w=WAC m=1
MMI2_4-M_u2 ZN I VSS VSS nch_hvt l=LA w=WAC m=1
MMI2_1-M_u2 ZN I VSS VSS nch_hvt l=LA w=WAC m=1
MMI2_0-M_u2 ZN I VSS VSS nch_hvt l=LA w=WAC m=1
MMI2_13-M_u2 ZN I VSS VSS nch_hvt l=LA w=WAC m=1
MMI2_8-M_u2 ZN I VSS VSS nch_hvt l=LA w=WAC m=1
MMI2_5-M_u2 ZN I VSS VSS nch_hvt l=LA w=WAC m=1
MMI2_7-M_u2 ZN I VSS VSS nch_hvt l=LA w=WAC m=1
MMI2_6-M_u2 ZN I VSS VSS nch_hvt l=LA w=WAC m=1
MMI2_9-M_u2 ZN I VSS VSS nch_hvt l=LA w=WAC m=1
MMI2_2-M_u2 ZN I VSS VSS nch_hvt l=LA w=WAC m=1
MMI2_11-M_u2 ZN I VSS VSS nch_hvt l=LA w=WAC m=1
MMI2_10-M_u2 ZN I VSS VSS nch_hvt l=LA w=WAC m=1
.ENDS

************************************************************************
* Library Name: tcbn65lphvt
* Cell Name:    DEL015HVT
* View Name:    schematic
************************************************************************

.SUBCKT DEL015HVT I VDD VSS Z
*.PININFO I:I Z:O VDD:B VSS:B
MMI2-M_u2 Z net13 VSS VSS nch_hvt l=LA w=WAC m=1
MMI29 net25 net9 net28 VSS nch_hvt l=LA w=WAC m=1
MMI30 net28 net9 VSS VSS nch_hvt l=LA w=WAC m=1
MMI37 net17 net5 VSS VSS nch_hvt l=LA w=WAC m=1
MMI28 net13 net9 net25 VSS nch_hvt l=LA w=WAC m=1
MMI35 net9 net5 net44 VSS nch_hvt l=LA w=WAC m=1
MMI1-M_u2 net5 I VSS VSS nch_hvt l=LA w=WAC m=1
MMI36 net44 net5 net17 VSS nch_hvt l=LA w=WAC m=1
MMI2-M_u3 Z net13 VDD VDD pch_hvt l=LA w=WAM m=1
MMI20 net57 net9 VDD VDD pch_hvt l=LA w=WAM m=1
MMI23 net13 net9 net25 VDD pch_hvt l=LA w=WAM m=1
MMI1-M_u3 net5 I VDD VDD pch_hvt l=LA w=WAM m=1
MMI21 net25 net9 net57 VDD pch_hvt l=LA w=WAM m=1
MMI32 net9 net5 net44 VDD pch_hvt l=LA w=WAM m=1
MMI31 net44 net5 net33 VDD pch_hvt l=LA w=WAM m=1
MMI7 net33 net5 VDD VDD pch_hvt l=LA w=WAM m=1
.ENDS

************************************************************************
* Library Name: civic
* Cell Name:    LDO_CK_GEN
* View Name:    schematic
************************************************************************

.SUBCKT LDO_CK_GEN SEL_RST SYSCLK VDD VSS
*.PININFO SYSCLK:I SEL_RST:O VDD:B VSS:B
XI19 net26 VDD VSS net24 / INVD1HVT
XI0 SYSCLK net24 VDD VSS net25 / AN2D4HVT
XI44 net25 VDD VSS SEL_RST / INVD16HVT
XI4 SYSCLK VDD VSS net26 / DEL015HVT
.ENDS

************************************************************************
* Library Name: tcbn65lphvt
* Cell Name:    CKND0HVT
* View Name:    schematic
************************************************************************

.SUBCKT CKND0HVT I VDD VSS ZN
*.PININFO I:I ZN:O VDD:B VSS:B
MM_u2 ZN I VSS VSS nch_hvt l=LA w=WA m=1
MM_u1 ZN I VDD VDD pch_hvt l=LA w=WL m=1
.ENDS

************************************************************************
* Library Name: tcbn65lphvt
* Cell Name:    ND3D1HVT
* View Name:    schematic
************************************************************************

.SUBCKT ND3D1HVT A1 A2 A3 VDD VSS ZN
*.PININFO A1:I A2:I A3:I ZN:O VDD:B VSS:B
MMI1-M_u5 net9 A2 net1 VSS nch_hvt l=LA w=WAC m=1
MMI1-M_u4 ZN A1 net9 VSS nch_hvt l=LA w=WAC m=1
MMI1-M_u6 net1 A3 VSS VSS nch_hvt l=LA w=WAC m=1
MMI1-M_u1 ZN A1 VDD VDD pch_hvt l=LA w=WAM m=1
MMI1-M_u3 ZN A3 VDD VDD pch_hvt l=LA w=WAM m=1
MMI1-M_u2 ZN A2 VDD VDD pch_hvt l=LA w=WAM m=1
.ENDS

************************************************************************
* Library Name: tcbn65lphvt
* Cell Name:    OAI21D1HVT
* View Name:    schematic
************************************************************************

.SUBCKT OAI21D1HVT A1 A2 B VDD VSS ZN
*.PININFO A1:I A2:I B:I ZN:O VDD:B VSS:B
MMI16-MI13 net9 A2 VDD VDD pch_hvt l=LA w=WAM m=1
MM_u9 ZN B VDD VDD pch_hvt l=LA w=WAM m=1
MMI16-MI12 ZN A1 net9 VDD pch_hvt l=LA w=WAM m=1
MM_u3 ZN A2 net24 VSS nch_hvt l=LA w=WAC m=1
MM_u4 net24 B VSS VSS nch_hvt l=LA w=WAC m=1
MM_u2 ZN A1 net24 VSS nch_hvt l=LA w=WAC m=1
.ENDS

************************************************************************
* Library Name: tcbn65lphvt
* Cell Name:    ND2D1HVT
* View Name:    schematic
************************************************************************

.SUBCKT ND2D1HVT A1 A2 VDD VSS ZN
*.PININFO A1:I A2:I ZN:O VDD:B VSS:B
MMI1-M_u3 ZN A1 net1 VSS nch_hvt l=LA w=WAC m=1
MMI1-M_u4 net1 A2 VSS VSS nch_hvt l=LA w=WAC m=1
MMI1-M_u1 ZN A1 VDD VDD pch_hvt l=LA w=WAM m=1
MMI1-M_u2 ZN A2 VDD VDD pch_hvt l=LA w=WAM m=1
.ENDS

************************************************************************
* Library Name: tcbn65lphvt
* Cell Name:    CKXOR2D1HVT
* View Name:    schematic
************************************************************************

.SUBCKT CKXOR2D1HVT A1 A2 VDD VSS Z
*.PININFO A1:I A2:I Z:O VDD:B VSS:B
MM_u6-M_u2 net27 A1 net44 VDD pch_hvt l=LA w=WQ m=1
MM_u4-M_u3 Z net44 VDD VDD pch_hvt l=LA w=WAM m=1
MM_u5-M_u3 net5 net27 VDD VDD pch_hvt l=LA w=WQ m=1
MM_u8-M_u3 net9 A1 VDD VDD pch_hvt l=LA w=WL m=1
MMI0-M_u2 net5 net9 net44 VDD pch_hvt l=LA w=WQ m=1
MM_u2-M_u3 net27 A2 VDD VDD pch_hvt l=LA w=WAM m=1
MM_u6-M_u3 net27 net9 net44 VSS nch_hvt l=LA w=WE m=1
MMI0-M_u3 net5 A1 net44 VSS nch_hvt l=LA w=WE m=1
MM_u8-M_u2 net9 A1 VSS VSS nch_hvt l=LA w=WE m=1
MM_u4-M_u2 Z net44 VSS VSS nch_hvt l=LA w=WAC m=1
MM_u2-M_u2 net27 A2 VSS VSS nch_hvt l=LA w=WAC m=1
MM_u5-M_u2 net5 net27 VSS VSS nch_hvt l=LA w=WE m=1
.ENDS

************************************************************************
* Library Name: tcbn65lphvt
* Cell Name:    INVD3HVT
* View Name:    schematic
************************************************************************

.SUBCKT INVD3HVT I VDD VSS ZN
*.PININFO I:I ZN:O VDD:B VSS:B
MMU1_0-M_u2 ZN I VSS VSS nch_hvt l=LA w=WAC m=1
MMU1_1-M_u2 ZN I VSS VSS nch_hvt l=LA w=WAC m=1
MMU1_2-M_u2 ZN I VSS VSS nch_hvt l=LA w=WAC m=1
MMU1_0-M_u3 ZN I VDD VDD pch_hvt l=LA w=WAM m=1
MMU1_1-M_u3 ZN I VDD VDD pch_hvt l=LA w=WAM m=1
MMU1_2-M_u3 ZN I VDD VDD pch_hvt l=LA w=WAM m=1
.ENDS

************************************************************************
* Library Name: tcbn65lphvt
* Cell Name:    CKND6HVT
* View Name:    schematic
************************************************************************

.SUBCKT CKND6HVT I VDD VSS ZN
*.PININFO I:I ZN:O VDD:B VSS:B
MM_u1_0 ZN I VDD VDD pch_hvt l=LA w=WAM m=1
MM_u1_3 ZN I VDD VDD pch_hvt l=LA w=WAM m=1
MM_u1_2 ZN I VDD VDD pch_hvt l=LA w=WAM m=1
MM_u1_4 ZN I VDD VDD pch_hvt l=LA w=WAM m=1
MM_u1_1 ZN I VDD VDD pch_hvt l=LA w=WAM m=1
MM_u1_5 ZN I VDD VDD pch_hvt l=LA w=WAM m=1
DDI3 VSS I ndio_hvt area=6.6e-14 pj=1.18e-06 m=1
MM_u2_1 ZN I VSS VSS nch_hvt l=LA w=WW m=1
MM_u2_3 ZN I VSS VSS nch_hvt l=LA w=WW m=1
MM_u2_4 ZN I VSS VSS nch_hvt l=LA w=WW m=1
MM_u2_0 ZN I VSS VSS nch_hvt l=LA w=WW m=1
MM_u2_2 ZN I VSS VSS nch_hvt l=LA w=WW m=1
MM_u2_5 ZN I VSS VSS nch_hvt l=LA w=WW m=1
.ENDS

************************************************************************
* Library Name: tcbn65lphvt
* Cell Name:    DFCNQD1HVT
* View Name:    schematic
************************************************************************

.SUBCKT DFCNQD1HVT CDN CP D Q VDD VSS
*.PININFO CDN:I CP:I D:I Q:O VDD:B VSS:B
MMI4 net53 net5 VSS VSS nch_hvt l=LA w=WZ m=1
MMI21-M_u3 net81 net51 net9 VSS nch_hvt l=LA w=WAC m=1
MMI13-M_u2 net37 net97 VSS VSS nch_hvt l=LA w=WB m=1
MMI29 net51 net5 net44 VSS nch_hvt l=LA w=WA m=1
MMI15 net37 net63 net51 VSS nch_hvt l=LA w=WB m=1
MMI32-M_u2 net63 net5 VSS VSS nch_hvt l=LA w=WE m=1
MMI5 net97 D net53 VSS nch_hvt l=LA w=WZ m=1
MMI49 net20 CDN VSS VSS nch_hvt l=LA w=WA m=1
MMI26 net44 net81 VSS VSS nch_hvt l=LA w=WA m=1
MMI48 net17 net37 net20 VSS nch_hvt l=LA w=WA m=1
MMI27-M_u2 Q net81 VSS VSS nch_hvt l=LA w=WAC m=1
MMI21-M_u4 net9 CDN VSS VSS nch_hvt l=LA w=WAC m=1
MMI22-M_u2 net5 CP VSS VSS nch_hvt l=LA w=WE m=1
MMI47 net97 net63 net17 VSS nch_hvt l=LA w=WA m=1
MMI22-M_u3 net5 CP VDD VDD pch_hvt l=LA w=WL m=1
MMI32-M_u3 net63 net5 VDD VDD pch_hvt l=LA w=WL m=1
MMI43 net101 net37 VDD VDD pch_hvt l=LA w=WA m=1
MMI6 net97 D net100 VDD pch_hvt l=LA w=WAI m=1
MMI27-M_u3 Q net81 VDD VDD pch_hvt l=LA w=WAM m=1
MMI44 net101 CDN VDD VDD pch_hvt l=LA w=WA m=1
MMI13-M_u3 net37 net97 VDD VDD pch_hvt l=LA w=WG m=1
MMI21-M_u1 net81 net51 VDD VDD pch_hvt l=LA w=WAE m=1
MMI16 net37 net5 net51 VDD pch_hvt l=LA w=WJ m=1
MMI24 net72 net81 VDD VDD pch_hvt l=LA w=WA m=1
MMI28 net51 net63 net72 VDD pch_hvt l=LA w=WA m=1
MMI45 net97 net5 net101 VDD pch_hvt l=LA w=WA m=1
MMI7 net100 net63 VDD VDD pch_hvt l=LA w=WAI m=1
MMI21-M_u2 net81 CDN VDD VDD pch_hvt l=LA w=WAE m=1
.ENDS

************************************************************************
* Library Name: tcbn65lphvt
* Cell Name:    CKBD1HVT
* View Name:    schematic
************************************************************************

.SUBCKT CKBD1HVT I VDD VSS Z
*.PININFO I:I Z:O VDD:B VSS:B
MM_u15 net5 I VSS VSS nch_hvt l=LA w=WW m=1
MMU23 Z net5 VSS VSS nch_hvt l=LA w=WW m=1
MM_u3 net5 I VDD VDD pch_hvt l=LA w=WAM m=1
MMU21 Z net5 VDD VDD pch_hvt l=LA w=WAM m=1
.ENDS

************************************************************************
* Library Name: tcbn65lphvt
* Cell Name:    OAI32D1HVT
* View Name:    schematic
************************************************************************

.SUBCKT OAI32D1HVT A1 A2 A3 B1 B2 VDD VSS ZN
*.PININFO A1:I A2:I A3:I B1:I B2:I ZN:O VDD:B VSS:B
MMI16-MI13 net17 B1 VDD VDD pch_hvt l=LA w=WAM m=1
MMI15-MI15 net13 A1 VDD VDD pch_hvt l=LA w=WAM m=1
MMI16-MI12 ZN B2 net17 VDD pch_hvt l=LA w=WAM m=1
MMI15-MI12 ZN A3 net1 VDD pch_hvt l=LA w=WAM m=1
MMI15-MI13 net1 A2 net13 VDD pch_hvt l=LA w=WAM m=1
MMI1 ZN A1 net25 VSS nch_hvt l=LA w=WAC m=1
MMI3 ZN A3 net25 VSS nch_hvt l=LA w=WAC m=1
MMI2 ZN A2 net25 VSS nch_hvt l=LA w=WAC m=1
MMI0 net25 B2 VSS VSS nch_hvt l=LA w=WAC m=1
MM_u4 net25 B1 VSS VSS nch_hvt l=LA w=WAC m=1
.ENDS

************************************************************************
* Library Name: tcbn65lphvt
* Cell Name:    AOI32D1HVT
* View Name:    schematic
************************************************************************

.SUBCKT AOI32D1HVT A1 A2 A3 B1 B2 VDD VSS ZN
*.PININFO A1:I A2:I A3:I B1:I B2:I ZN:O VDD:B VSS:B
MMU18 ZN A3 net20 VDD pch_hvt l=LA w=WAM m=1
MMU19 net20 B2 VDD VDD pch_hvt l=LA w=WAM m=1
MMU16 ZN A2 net20 VDD pch_hvt l=LA w=WAM m=1
MMU20 net20 B1 VDD VDD pch_hvt l=LA w=WAM m=1
MMU17 ZN A1 net20 VDD pch_hvt l=LA w=WAM m=1
MMI20-M_u10 ZN A1 net21 VSS nch_hvt l=LA w=WAC m=1
MMI17-M_u10 ZN B1 net36 VSS nch_hvt l=LA w=WAC m=1
MMI17-M_u11 net36 B2 VSS VSS nch_hvt l=LA w=WAC m=1
MMI20-MI12 net25 A3 VSS VSS nch_hvt l=LA w=WAC m=1
MMI20-M_u11 net21 A2 net25 VSS nch_hvt l=LA w=WAC m=1
.ENDS

************************************************************************
* Library Name: tcbn65lphvt
* Cell Name:    AOI211XD0HVT
* View Name:    schematic
************************************************************************

.SUBCKT AOI211XD0HVT A1 A2 B C VDD VSS ZN
*.PININFO A1:I A2:I B:I C:I ZN:O VDD:B VSS:B
MM_u12 ZN C VSS VSS nch_hvt l=LA w=WE m=1
MMI12-M_u10 ZN A1 net1 VSS nch_hvt l=LA w=WE m=1
MM_u13 ZN B VSS VSS nch_hvt l=LA w=WE m=1
MMI12-M_u11 net1 A2 VSS VSS nch_hvt l=LA w=WE m=1
MMI16-MI12 net25 B net17 VDD pch_hvt l=LA w=WAM m=1
MM_u3 net25 A1 ZN VDD pch_hvt l=LA w=WAM m=1
MMI0 net25 A2 ZN VDD pch_hvt l=LA w=WAM m=1
MMI16-MI13 net17 C VDD VDD pch_hvt l=LA w=WAM m=1
.ENDS

************************************************************************
* Library Name: tcbn65lphvt
* Cell Name:    DFCSNQD4HVT
* View Name:    schematic
************************************************************************

.SUBCKT DFCSNQD4HVT CDN CP D Q SDN VDD VSS
*.PININFO CDN:I CP:I D:I SDN:I Q:O VDD:B VSS:B
MMI86-M_u3 net81 net83 net17 VSS nch_hvt l=LA w=WAC m=1
MMI60-M_u2 Q net81 VSS VSS nch_hvt l=LA w=WAC m=1
MMI80-M_u4 net36 CDN VSS VSS nch_hvt l=LA w=WAC m=1
MMI71-M_u4 net24 net81 VSS VSS nch_hvt l=LA w=WF m=1
MMI20 net5 net67 net83 VSS nch_hvt l=LA w=WH m=1
MMI72-M_u4 net61 net63 VSS VSS nch_hvt l=LA w=WF m=1
MMI23 net63 net67 net25 VSS nch_hvt l=LA w=WA m=1
MMI76-M_u2 Q net81 VSS VSS nch_hvt l=LA w=WAC m=1
MMI22 net49 net51 net83 VSS nch_hvt l=LA w=WA m=1
MMI21 net63 D net29 VSS nch_hvt l=LA w=WAC m=1
MMI75-M_u2 Q net81 VSS VSS nch_hvt l=LA w=WAC m=1
MMI85-M_u2 net51 CP VSS VSS nch_hvt l=LA w=WAC m=1
MMI80-M_u3 net81 net83 net36 VSS nch_hvt l=LA w=WAC m=1
MMI19 net29 net51 VSS VSS nch_hvt l=LA w=WAD m=1
MMI24 net25 net5 net1 VSS nch_hvt l=LA w=WA m=1
MMI71-M_u3 net49 SDN net24 VSS nch_hvt l=LA w=WF m=1
MMI86-M_u4 net17 CDN VSS VSS nch_hvt l=LA w=WAC m=1
MMI84-M_u2 net67 net51 VSS VSS nch_hvt l=LA w=WAC m=1
MMI73-M_u2 Q net81 VSS VSS nch_hvt l=LA w=WAC m=1
MMI72-M_u3 net5 SDN net61 VSS nch_hvt l=LA w=WF m=1
MMI25 net1 CDN VSS VSS nch_hvt l=LA w=WA m=1
MMI33 net49 net67 net83 VDD pch_hvt l=LA w=WA m=1
MMI75-M_u3 Q net81 VDD VDD pch_hvt l=LA w=WAM m=1
MMI71-M_u1 net49 SDN VDD VDD pch_hvt l=LA w=WZ m=1
MMI85-M_u3 net51 CP VDD VDD pch_hvt l=LA w=WAM m=1
MMI60-M_u3 Q net81 VDD VDD pch_hvt l=LA w=WAM m=1
MMI72-M_u1 net5 SDN VDD VDD pch_hvt l=LA w=WAJ m=1
MMI86-M_u2 net81 CDN VDD VDD pch_hvt l=LA w=WAM m=1
MMI34 net63 net51 net89 VDD pch_hvt l=LA w=WC m=1
MMI71-M_u2 net49 net81 VDD VDD pch_hvt l=LA w=WZ m=1
MMI80-M_u1 net81 net83 VDD VDD pch_hvt l=LA w=WAM m=1
MMI30 net5 net51 net83 VDD pch_hvt l=LA w=WN m=1
MMI80-M_u2 net81 CDN VDD VDD pch_hvt l=LA w=WAM m=1
MMI73-M_u3 Q net81 VDD VDD pch_hvt l=LA w=WAM m=1
MMI76-M_u3 Q net81 VDD VDD pch_hvt l=LA w=WAM m=1
MMI28 net96 net67 VDD VDD pch_hvt l=LA w=WAK m=1
MMI35 net89 net5 VDD VDD pch_hvt l=LA w=WA m=1
MMI72-M_u2 net5 net63 VDD VDD pch_hvt l=LA w=WAJ m=1
MMI84-M_u3 net67 net51 VDD VDD pch_hvt l=LA w=WAM m=1
MMI26 net63 D net96 VDD pch_hvt l=LA w=WAK m=1
MMI36 net89 CDN VDD VDD pch_hvt l=LA w=WA m=1
MMI86-M_u1 net81 net83 VDD VDD pch_hvt l=LA w=WAM m=1
.ENDS

************************************************************************
* Library Name: tcbn65lphvt
* Cell Name:    NR3D0HVT
* View Name:    schematic
************************************************************************

.SUBCKT NR3D0HVT A1 A2 A3 VDD VSS ZN
*.PININFO A1:I A2:I A3:I ZN:O VDD:B VSS:B
MMI3 ZN A1 VSS VSS nch_hvt l=LA w=WE m=1
MMI2 ZN A2 VSS VSS nch_hvt l=LA w=WE m=1
MM_u4 ZN A3 VSS VSS nch_hvt l=LA w=WE m=1
MMI1 ZN A1 net13 VDD pch_hvt l=LA w=WAM m=1
MM_u1 net17 A3 VDD VDD pch_hvt l=LA w=WAM m=1
MMI0 net13 A2 net17 VDD pch_hvt l=LA w=WAM m=1
.ENDS

************************************************************************
* Library Name: tcbn65lphvt
* Cell Name:    OR3D1HVT
* View Name:    schematic
************************************************************************

.SUBCKT OR3D1HVT A1 A2 A3 VDD VSS Z
*.PININFO A1:I A2:I A3:I Z:O VDD:B VSS:B
MMU42-M_u1 net13 A1 VDD VDD pch_hvt l=LA w=WAM m=1
MMU42-M_u3 net9 A3 net1 VDD pch_hvt l=LA w=WAM m=1
MM_u4-M_u3 Z net9 VDD VDD pch_hvt l=LA w=WAM m=1
MMU42-M_u2 net1 A2 net13 VDD pch_hvt l=LA w=WAM m=1
MMU42-M_u5 net9 A2 VSS VSS nch_hvt l=LA w=WE m=1
MMU42-M_u4 net9 A1 VSS VSS nch_hvt l=LA w=WE m=1
MM_u4-M_u2 Z net9 VSS VSS nch_hvt l=LA w=WAC m=1
MMU42-M_u6 net9 A3 VSS VSS nch_hvt l=LA w=WE m=1
.ENDS

************************************************************************
* Library Name: tcbn65lphvt
* Cell Name:    NR2D1HVT
* View Name:    schematic
************************************************************************

.SUBCKT NR2D1HVT A1 A2 VDD VSS ZN
*.PININFO A1:I A2:I ZN:O VDD:B VSS:B
MMI1-M_u3 ZN A2 VSS VSS nch_hvt l=LA w=WAC m=1
MMI1-M_u4 ZN A1 VSS VSS nch_hvt l=LA w=WAC m=1
MMI1-M_u1 net13 A2 VDD VDD pch_hvt l=LA w=WAM m=1
MMI1-M_u2 ZN A1 net13 VDD pch_hvt l=LA w=WAM m=1
.ENDS

************************************************************************
* Library Name: model3x
* Cell Name:    SEL_LOGIC_V3
* View Name:    schematic
************************************************************************

.SUBCKT SEL_LOGIC_V3 MCLK NRO<2> NRO<1> NRO<0> SEL<1> SEL<0> SRST VDD VSS
*.PININFO MCLK:I NRO<2>:I NRO<1>:I NRO<0>:I SRST:I SEL<1>:O SEL<0>:O VDD:B 
*.PININFO VSS:B
XU12 N38 VDD VSS N90 / INVD1HVT
XU15 SEL<1> VDD VSS N70 / INVD1HVT
XU9 CYLCNT<1> VDD VSS N6 / INVD1HVT
XU19 NRO<1> VDD VSS EQ_99_B_0_ / INVD1HVT
XU17 NRO<2> VDD VSS N10 / INVD1HVT
XU4 N8 VDD VSS EQ_99_B_9_ / INVD1HVT
XU7 SRST VDD VSS N2 / INVD1HVT
XU20 CYLCNT<0> VDD VSS N5 / INVD1HVT
XU3 NRO<0> VDD VSS N11 / CKND0HVT
XU6 N11 N2 EQ_99_B_9_ VDD VSS N20 / ND3D1HVT
XU18 EQ_99_B_0_ N10 N8 VDD VSS N7 / OAI21D1HVT
XU21 NRO<0> N8 N2 VDD VSS N21 / OAI21D1HVT
XU5 EQ_99_B_0_ N10 VDD VSS N8 / ND2D1HVT
XU16 NRO<1> CYLCNT<0> VDD VSS N16 / CKXOR2D1HVT
XU23 N7 CYLCNT<1> VDD VSS N30 / CKXOR2D1HVT
XU24 CYLCNT<1> CYLCNT<0> VDD VSS N3 / CKXOR2D1HVT
XU25 EQ_99_B_0_ CYLCNT<0> VDD VSS N4 / CKXOR2D1HVT
XCKND16HVT_G1B2I1 MCLK VDD VSS MCLK_G1B1I1 / INVD3HVT
XCKND2HVT_G1B1I1 MCLK_G1B1I1 VDD VSS MCLK_G1B2I1 / CKND6HVT
XCYLCNT_REG_0_ SRST MCLK_G1B2I1 N35 CYLCNT<0> VDD VSS / DFCNQD1HVT
XCYLCNT_REG_1_ SRST MCLK_G1B2I1 N3 CYLCNT<1> VDD VSS / DFCNQD1HVT
XU28 SEL<0> VDD VSS N38 / CKBD1HVT
XU27 N25 VDD VSS N37 / CKBD1HVT
XU2 N22 VDD VSS N36 / CKBD1HVT
XU1 N5 VDD VSS N35 / CKBD1HVT
XU11 N1 NRO<0> N14 N12 N90 VDD VSS N25 / OAI32D1HVT
XU8 N16 N6 N10 CYLCNT<1> N19 VDD VSS N12 / OAI32D1HVT
XU10 CYLCNT<0> N10 NRO<1> EQ_99_B_9_ N5 VDD VSS N19 / AOI32D1HVT
XU14 N9 N11 N70 N12 VDD VSS N22 / AOI211XD0HVT
XSEL_REG_0_ N21 MCLK_G1B2I1 N37 SEL<0> N20 VDD VSS / DFCSNQD4HVT
XSEL_REG_1_ N20 MCLK_G1B2I1 N36 SEL<1> N21 VDD VSS / DFCSNQD4HVT
XU26 N4 EQ_99_B_9_ N30 VDD VSS N9 / NR3D0HVT
XU22 N4 EQ_99_B_9_ N30 VDD VSS N1 / OR3D1HVT
XU13 SEL<0> SEL<1> VDD VSS N14 / NR2D1HVT
.ENDS

************************************************************************
* Library Name: tcbn65lphvt
* Cell Name:    CKBD0HVT
* View Name:    schematic
************************************************************************

.SUBCKT CKBD0HVT I VDD VSS Z
*.PININFO I:I Z:O VDD:B VSS:B
MM_u15 net5 I VSS VSS nch_hvt l=LA w=WA m=1
MMU23 Z net5 VSS VSS nch_hvt l=LA w=WA m=1
MM_u3 net5 I VDD VDD pch_hvt l=LA w=WL m=1
MMU21 Z net5 VDD VDD pch_hvt l=LA w=WL m=1
.ENDS

************************************************************************
* Library Name: civic
* Cell Name:    DLDO_LOOP
* View Name:    schematic
************************************************************************

.SUBCKT DLDO_LOOP CODE<5> CODE<4> CODE<3> CODE<2> CODE<1> CODE<0> DOUT<15> 
+ DOUT<14> DOUT<13> DOUT<12> DOUT<11> DOUT<10> DOUT<9> DOUT<8> DOUT<7> DOUT<6> 
+ DOUT<5> DOUT<4> DOUT<3> DOUT<2> DOUT<1> DOUT<0> LDO_EN NRO<2> NRO<1> NRO<0> 
+ SEL<1> SEL<0> SYS_CLK VDD VOUT VSS
*.PININFO CODE<5>:I CODE<4>:I CODE<3>:I CODE<2>:I CODE<1>:I CODE<0>:I LDO_EN:I 
*.PININFO NRO<2>:I NRO<1>:I NRO<0>:I SYS_CLK:I DOUT<15>:O DOUT<14>:O 
*.PININFO DOUT<13>:O DOUT<12>:O DOUT<11>:O DOUT<10>:O DOUT<9>:O DOUT<8>:O 
*.PININFO DOUT<7>:O DOUT<6>:O DOUT<5>:O DOUT<4>:O DOUT<3>:O DOUT<2>:O 
*.PININFO DOUT<1>:O DOUT<0>:O SEL<1>:O SEL<0>:O VDD:B VOUT:B VSS:B
Xpwbk2 CODE<5> CODE<4> CODE<3> CODE<2> CODE<1> CODE<0> DOUT<15> DOUT<14> 
+ DOUT<13> DOUT<12> DOUT<11> DOUT<10> DOUT<9> DOUT<8> DOUT<7> DOUT<6> DOUT<5> 
+ DOUT<4> DOUT<3> DOUT<2> DOUT<1> DOUT<0> LDO_EN net24 net23 SEL<1> SEL<0> 
+ SYS_CLK VDD VOUT VSS / PWR_BANK
XI0<40> VDD VSS / DCAP8HVT
XI0<39> VDD VSS / DCAP8HVT
XI0<38> VDD VSS / DCAP8HVT
XI0<37> VDD VSS / DCAP8HVT
XI0<36> VDD VSS / DCAP8HVT
XI0<35> VDD VSS / DCAP8HVT
XI0<34> VDD VSS / DCAP8HVT
XI0<33> VDD VSS / DCAP8HVT
XI0<32> VDD VSS / DCAP8HVT
XI0<31> VDD VSS / DCAP8HVT
XI0<30> VDD VSS / DCAP8HVT
XI0<29> VDD VSS / DCAP8HVT
XI0<28> VDD VSS / DCAP8HVT
XI0<27> VDD VSS / DCAP8HVT
XI0<26> VDD VSS / DCAP8HVT
XI0<25> VDD VSS / DCAP8HVT
XI0<24> VDD VSS / DCAP8HVT
XI0<23> VDD VSS / DCAP8HVT
XI0<22> VDD VSS / DCAP8HVT
XI0<21> VDD VSS / DCAP8HVT
XI0<20> VDD VSS / DCAP8HVT
XI0<19> VDD VSS / DCAP8HVT
XI0<18> VDD VSS / DCAP8HVT
XI0<17> VDD VSS / DCAP8HVT
XI0<16> VDD VSS / DCAP8HVT
XI0<15> VDD VSS / DCAP8HVT
XI0<14> VDD VSS / DCAP8HVT
XI0<13> VDD VSS / DCAP8HVT
XI0<12> VDD VSS / DCAP8HVT
XI0<11> VDD VSS / DCAP8HVT
XI0<10> VDD VSS / DCAP8HVT
XI0<9> VDD VSS / DCAP8HVT
XI0<8> VDD VSS / DCAP8HVT
XI0<7> VDD VSS / DCAP8HVT
XI0<6> VDD VSS / DCAP8HVT
XI0<5> VDD VSS / DCAP8HVT
XI0<4> VDD VSS / DCAP8HVT
XI0<3> VDD VSS / DCAP8HVT
XI0<2> VDD VSS / DCAP8HVT
XI0<1> VDD VSS / DCAP8HVT
XI0<0> VDD VSS / DCAP8HVT
Xckgen0 net23 SYS_CLK VDD VSS / LDO_CK_GEN
Xselog1 net24 NRO<2> NRO<1> N1 SEL<1> SEL<0> net23 VDD VSS / SEL_LOGIC_V3
XI1 NRO<0> VDD VSS N1 / CKBD0HVT
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    CKND3
* View Name:    schematic
************************************************************************

.SUBCKT CKND3 I VDD VSS ZN
*.PININFO I:I ZN:O VDD:B VSS:B
MM_u1_0 ZN I VDD VDD pch l=LA w=WAM m=1
MM_u1_2 ZN I VDD VDD pch l=LA w=WAM m=1
MM_u1_1 ZN I VDD VDD pch l=LA w=WAM m=1
MM_u2_1 ZN I VSS VSS nch l=LA w=WW m=1
MM_u2_0 ZN I VSS VSS nch l=LA w=WW m=1
MM_u2_2 ZN I VSS VSS nch l=LA w=WW m=1
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
MM_u1 ZN I VDD VDD pch l=LA w=WAM m=1
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
MMI1-M_u1 ZN A1 VDD VDD pch l=LA w=WAM m=1
MMI1-M_u3 ZN A3 VDD VDD pch l=LA w=WAM m=1
MMI1-M_u2 ZN A2 VDD VDD pch l=LA w=WAM m=1
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
MMI1-M_u1 net13 A2 VDD VDD pch l=LA w=WAM m=1
MMI1-M_u2 ZN A1 net13 VDD pch l=LA w=WAM m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    MUX2ND0
* View Name:    schematic
************************************************************************

.SUBCKT MUX2ND0 I0 I1 S VDD VSS ZN
*.PININFO I0:I I1:I S:I ZN:O VDD:B VSS:B
MMI15-M_u3 net37 S VDD VDD pch l=LA w=WL m=1
MMI111 net13 I0 VDD VDD pch l=LA w=WW m=1
MMI24 net9 I1 VDD VDD pch l=LA w=WAM m=1
MMI5 ZN S net13 VDD pch l=LA w=WAC m=1
MMI25 ZN net37 net9 VDD pch l=LA w=WAC m=1
MMI15-M_u2 net37 S VSS VSS nch l=LA w=WF m=1
MMI20 net33 I1 VSS VSS nch l=LA w=WAC m=1
MMI12 ZN net37 net32 VSS nch l=LA w=WH m=1
MMI21 ZN S net33 VSS nch l=LA w=WH m=1
MMI19 net32 I0 VSS VSS nch l=LA w=WH m=1
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
MMI3 net37 A1 VDD VDD pch l=LA w=WAM m=1
MMI4 net33 A2 net37 VDD pch l=LA w=WAM m=1
MMU1-M_u3 Z net25 VDD VDD pch l=LA w=WAM m=1
MM_u11 net25 B VDD VDD pch l=LA w=WAM m=1
MMI5 net25 A3 net33 VDD pch l=LA w=WAM m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    CKBD1
* View Name:    schematic
************************************************************************

.SUBCKT CKBD1 I VDD VSS Z
*.PININFO I:I Z:O VDD:B VSS:B
MM_u15 net5 I VSS VSS nch l=LA w=WW m=1
MMU23 Z net5 VSS VSS nch l=LA w=WW m=1
MM_u3 net5 I VDD VDD pch l=LA w=WAM m=1
MMU21 Z net5 VDD VDD pch l=LA w=WAM m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    NR4D0
* View Name:    schematic
************************************************************************

.SUBCKT NR4D0 A1 A2 A3 A4 VDD VSS ZN
*.PININFO A1:I A2:I A3:I A4:I ZN:O VDD:B VSS:B
MMI34 ZN A2 VSS VSS nch l=LA w=WE m=1
MMI5 ZN A1 VSS VSS nch l=LA w=WE m=1
MMI35 ZN A3 VSS VSS nch l=LA w=WE m=1
MMI36 ZN A4 VSS VSS nch l=LA w=WE m=1
MMI27 net29 A2 net32 VDD pch l=LA w=WAM m=1
MMI28 ZN A1 net29 VDD pch l=LA w=WAM m=1
MMI26 net32 A3 net24 VDD pch l=LA w=WAM m=1
MMI7 net24 A4 VDD VDD pch l=LA w=WAM m=1
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
MM_u3-M_u3 Z net11 VDD VDD pch l=LA w=WAM m=1
MM_u4-M_u3 net11 A3 VDD VDD pch l=LA w=WAM m=1
MM_u4-M_u1 net11 A1 VDD VDD pch l=LA w=WAM m=1
MM_u4-M_u2 net11 A2 VDD VDD pch l=LA w=WAM m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    OA211D1
* View Name:    schematic
************************************************************************

.SUBCKT OA211D1 A1 A2 B C VDD VSS Z
*.PININFO A1:I A2:I B:I C:I Z:O VDD:B VSS:B
MMI17 net17 C VSS VSS nch l=LA w=WAC m=1
MMI15 net25 A1 net9 VSS nch l=LA w=WAC m=1
MMI16 net9 B net17 VSS nch l=LA w=WAC m=1
MMI11-M_u2 Z net25 VSS VSS nch l=LA w=WAC m=1
MMI7 net25 A2 net9 VSS nch l=LA w=WAC m=1
MMI13 net37 A1 VDD VDD pch l=LA w=WAM m=1
MMI12 net25 C VDD VDD pch l=LA w=WAM m=1
MM_u12 net25 B VDD VDD pch l=LA w=WAM m=1
MMI14 net25 A2 net37 VDD pch l=LA w=WAM m=1
MMI11-M_u3 Z net25 VDD VDD pch l=LA w=WAM m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    DFCSNQD1
* View Name:    schematic
************************************************************************

.SUBCKT DFCSNQD1 CDN CP D Q SDN VDD VSS
*.PININFO CDN:I CP:I D:I SDN:I Q:O VDD:B VSS:B
MMI75-M_u3 net61 net100 net37 VSS nch l=LA w=WAC m=1
MMI60-M_u2 Q net61 VSS VSS nch l=LA w=WAC m=1
MMI71-M_u4 net20 net61 VSS VSS nch l=LA w=WF m=1
MMI20 net97 net81 net100 VSS nch l=LA w=WH m=1
MMI72-M_u4 net45 net47 VSS VSS nch l=LA w=WF m=1
MMI23 net47 net81 net44 VSS nch l=LA w=WA m=1
MMI75-M_u4 net37 CDN VSS VSS nch l=LA w=WAC m=1
MMI22 net125 net13 net100 VSS nch l=LA w=WA m=1
MMI21 net47 D net25 VSS nch l=LA w=WAC m=1
MMI19 net25 net13 VSS VSS nch l=LA w=WAD m=1
MMI24 net44 net97 net5 VSS nch l=LA w=WA m=1
MMI71-M_u3 net125 SDN net20 VSS nch l=LA w=WF m=1
MMI73-M_u2 net13 CP VSS VSS nch l=LA w=WE m=1
MMI72-M_u3 net97 SDN net45 VSS nch l=LA w=WF m=1
MMI25 net5 CDN VSS VSS nch l=LA w=WA m=1
MMI40-M_u2 net81 net13 VSS VSS nch l=LA w=WE m=1
MMI33 net125 net81 net100 VDD pch l=LA w=WA m=1
MMI71-M_u1 net125 SDN VDD VDD pch l=LA w=WZ m=1
MMI75-M_u1 net61 net100 VDD VDD pch l=LA w=WAM m=1
MMI60-M_u3 Q net61 VDD VDD pch l=LA w=WAM m=1
MMI72-M_u1 net97 SDN VDD VDD pch l=LA w=WAJ m=1
MMI34 net47 net13 net108 VDD pch l=LA w=WC m=1
MMI71-M_u2 net125 net61 VDD VDD pch l=LA w=WZ m=1
MMI30 net97 net13 net100 VDD pch l=LA w=WN m=1
MMI75-M_u2 net61 CDN VDD VDD pch l=LA w=WAM m=1
MMI73-M_u3 net13 CP VDD VDD pch l=LA w=WL m=1
MMI28 net72 net81 VDD VDD pch l=LA w=WAK m=1
MMI40-M_u3 net81 net13 VDD VDD pch l=LA w=WL m=1
MMI35 net108 net97 VDD VDD pch l=LA w=WA m=1
MMI72-M_u2 net97 net47 VDD VDD pch l=LA w=WAJ m=1
MMI26 net47 D net72 VDD pch l=LA w=WAK m=1
MMI36 net108 CDN VDD VDD pch l=LA w=WA m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    AOI21D1
* View Name:    schematic
************************************************************************

.SUBCKT AOI21D1 A1 A2 B VDD VSS ZN
*.PININFO A1:I A2:I B:I ZN:O VDD:B VSS:B
MM_u3 net5 A1 ZN VDD pch l=LA w=WAM m=1
MM_u2 net5 B VDD VDD pch l=LA w=WAM m=1
MM_u4 net5 A2 ZN VDD pch l=LA w=WAM m=1
MMI2 ZN A1 net13 VSS nch l=LA w=WAC m=1
MM_u7 ZN B VSS VSS nch l=LA w=WAC m=1
MMI3 net13 A2 VSS VSS nch l=LA w=WAC m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    AO221D0
* View Name:    schematic
************************************************************************

.SUBCKT AO221D0 A1 A2 B1 B2 C VDD VSS Z
*.PININFO A1:I A2:I B1:I B2:I C:I Z:O VDD:B VSS:B
MMU22 VDD C net9 VDD pch l=LA w=WL m=1
MMI9 net13 A2 net20 VDD pch l=LA w=WL m=1
MMI10 net13 A1 net20 VDD pch l=LA w=WL m=1
MMI6 net9 B2 net13 VDD pch l=LA w=WL m=1
MMI8-M_u3 Z net20 VDD VDD pch l=LA w=WL m=1
MMI7 net9 B1 net13 VDD pch l=LA w=WL m=1
MMI1-M_u10 net20 A1 net33 VSS nch l=LA w=WE m=1
MMI17-M_u10 net20 B1 net25 VSS nch l=LA w=WE m=1
MMI8-M_u2 Z net20 VSS VSS nch l=LA w=WE m=1
MMI1-M_u11 net33 A2 VSS VSS nch l=LA w=WE m=1
MMU20 net20 C VSS VSS nch l=LA w=WE m=1
MMI17-M_u11 net25 B2 VSS VSS nch l=LA w=WE m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    OAI211D1
* View Name:    schematic
************************************************************************

.SUBCKT OAI211D1 A1 A2 B C VDD VSS ZN
*.PININFO A1:I A2:I B:I C:I ZN:O VDD:B VSS:B
MMI3 net13 C VSS VSS nch l=LA w=WAC m=1
MMI2 net9 B net13 VSS nch l=LA w=WAC m=1
MM_u3 ZN A2 net9 VSS nch l=LA w=WAC m=1
MM_u2 ZN A1 net9 VSS nch l=LA w=WAC m=1
MMI1 ZN A2 net25 VDD pch l=LA w=WAM m=1
MMI0 net25 A1 VDD VDD pch l=LA w=WAM m=1
MM_u11 ZN C VDD VDD pch l=LA w=WAM m=1
MM_u12 ZN B VDD VDD pch l=LA w=WAM m=1
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
MMI1-M_u1 ZN A1 VDD VDD pch l=LA w=WAM m=1
MMI1-M_u2 ZN A2 VDD VDD pch l=LA w=WAM m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    MUX3ND0
* View Name:    schematic
************************************************************************

.SUBCKT MUX3ND0 I0 I1 I2 S0 S1 VDD VSS ZN
*.PININFO I0:I I1:I I2:I S0:I S1:I ZN:O VDD:B VSS:B
MMI5-M_u2 net25 S0 net20 VDD pch l=LA w=WAF m=1
MMI16-M_u3 net29 I2 VDD VDD pch l=LA w=WAN m=1
MMI15-M_u3 net25 I0 VDD VDD pch l=LA w=WW m=1
MMU19-M_u3 net51 S1 VDD VDD pch l=LA w=WL m=1
MMI17-M_u2 net5 net13 net20 VDD pch l=LA w=WAA m=1
MMI13-M_u3 net13 S0 VDD VDD pch l=LA w=WL m=1
MMI18-M_u2 net20 S1 ZN VDD pch l=LA w=WN m=1
MMI12-M_u3 net5 I1 VDD VDD pch l=LA w=WAM m=1
MMI19-M_u2 net29 net51 ZN VDD pch l=LA w=WN m=1
MMI17-M_u3 net5 S0 net20 VSS nch l=LA w=WI m=1
MMI15-M_u2 net25 I0 VSS VSS nch l=LA w=WH m=1
MMI12-M_u2 net5 I1 VSS VSS nch l=LA w=WAC m=1
MMI19-M_u3 net29 S1 ZN VSS nch l=LA w=WF m=1
MMI13-M_u2 net13 S0 VSS VSS nch l=LA w=WF m=1
MMI18-M_u3 net20 net51 ZN VSS nch l=LA w=WF m=1
MMI5-M_u3 net25 net13 net20 VSS nch l=LA w=WL m=1
MMI16-M_u2 net29 I2 VSS VSS nch l=LA w=WAC m=1
MMU19-M_u2 net51 S1 VSS VSS nch l=LA w=WAC m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    OAI22D1
* View Name:    schematic
************************************************************************

.SUBCKT OAI22D1 A1 A2 B1 B2 VDD VSS ZN
*.PININFO A1:I A2:I B1:I B2:I ZN:O VDD:B VSS:B
MM_u3 ZN A1 net5 VSS nch l=LA w=WAC m=1
MM_u5 net5 B1 VSS VSS nch l=LA w=WAC m=1
MM_u4 net5 B2 VSS VSS nch l=LA w=WAC m=1
MM_u2 ZN A2 net5 VSS nch l=LA w=WAC m=1
MMI1 ZN B1 net32 VDD pch l=LA w=WAM m=1
MMI3 ZN A1 net17 VDD pch l=LA w=WAM m=1
MMU24 net32 B2 VDD VDD pch l=LA w=WAM m=1
MMI2 net17 A2 VDD VDD pch l=LA w=WAM m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    HA1D0
* View Name:    schematic
************************************************************************

.SUBCKT HA1D0 A B CO S VDD VSS
*.PININFO A:I B:I CO:O S:O VDD:B VSS:B
MMU1-M_u3 net9 A VDD VDD pch l=LA w=WAM m=1
MMU7-M_u2 net13 net5 net72 VDD pch l=LA w=WAM m=1
MMU9-M_u1 net25 A VDD VDD pch l=LA w=WL m=1
MMU5-M_u3 CO net25 VDD VDD pch l=LA w=WL m=1
MMU9-M_u2 net25 B VDD VDD pch l=LA w=WL m=1
MMU2-M_u3 net13 net9 VDD VDD pch l=LA w=WAM m=1
MMU8-M_u2 net9 B net72 VDD pch l=LA w=WW m=1
MMU3-M_u3 net5 B VDD VDD pch l=LA w=WR m=1
MMU4-M_u3 S net72 VDD VDD pch l=LA w=WL m=1
MMU8-M_u3 net9 net5 net72 VSS nch l=LA w=WS m=1
MMU9-M_u4 net56 B VSS VSS nch l=LA w=WE m=1
MMU1-M_u2 net9 A VSS VSS nch l=LA w=WAC m=1
MMU4-M_u2 S net72 VSS VSS nch l=LA w=WE m=1
MMU9-M_u3 net25 A net56 VSS nch l=LA w=WE m=1
MMU7-M_u3 net13 B net72 VSS nch l=LA w=WQ m=1
MMU3-M_u2 net5 B VSS VSS nch l=LA w=WAC m=1
MMU2-M_u2 net13 net9 VSS VSS nch l=LA w=WAC m=1
MMU5-M_u2 CO net25 VSS VSS nch l=LA w=WE m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    CKXOR2D1
* View Name:    schematic
************************************************************************

.SUBCKT CKXOR2D1 A1 A2 VDD VSS Z
*.PININFO A1:I A2:I Z:O VDD:B VSS:B
MM_u6-M_u2 net27 A1 net44 VDD pch l=LA w=WQ m=1
MM_u4-M_u3 Z net44 VDD VDD pch l=LA w=WAM m=1
MM_u5-M_u3 net5 net27 VDD VDD pch l=LA w=WQ m=1
MM_u8-M_u3 net9 A1 VDD VDD pch l=LA w=WL m=1
MMI0-M_u2 net5 net9 net44 VDD pch l=LA w=WQ m=1
MM_u2-M_u3 net27 A2 VDD VDD pch l=LA w=WAM m=1
MM_u6-M_u3 net27 net9 net44 VSS nch l=LA w=WE m=1
MMI0-M_u3 net5 A1 net44 VSS nch l=LA w=WE m=1
MM_u8-M_u2 net9 A1 VSS VSS nch l=LA w=WE m=1
MM_u4-M_u2 Z net44 VSS VSS nch l=LA w=WAC m=1
MM_u2-M_u2 net27 A2 VSS VSS nch l=LA w=WAC m=1
MM_u5-M_u2 net5 net27 VSS VSS nch l=LA w=WE m=1
.ENDS

************************************************************************
* Library Name: civicR
* Cell Name:    DLDO_LOGIC_V1_DW01_inc_0
* View Name:    schematic
************************************************************************

.SUBCKT DLDO_LOGIC_V1_DW01_inc_0 A<6> A<5> A<4> A<3> A<2> A<1> A<0> SUM<6> 
+ SUM<5> SUM<4> SUM<3> SUM<2> SUM<1> SUM<0> VDD VSS
*.PININFO A<6>:I A<5>:I A<4>:I A<3>:I A<2>:I A<1>:I A<0>:I SUM<6>:O SUM<5>:O 
*.PININFO SUM<4>:O SUM<3>:O SUM<2>:O SUM<1>:O SUM<0>:O VDD:B VSS:B
XU2 A<0> VDD VSS SUM<0> / INVD1
XU1_1_5 A<5> CARRY<5> CARRY<6> SUM<5> VDD VSS / HA1D0
XU1_1_3 A<3> CARRY<3> CARRY<4> SUM<3> VDD VSS / HA1D0
XU1_1_4 A<4> CARRY<4> CARRY<5> SUM<4> VDD VSS / HA1D0
XU1_1_2 A<2> CARRY<2> CARRY<3> SUM<2> VDD VSS / HA1D0
XU1_1_1 A<1> A<0> CARRY<2> SUM<1> VDD VSS / HA1D0
XU1 CARRY<6> A<6> VDD VSS SUM<6> / CKXOR2D1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    AO21D1
* View Name:    schematic
************************************************************************

.SUBCKT AO21D1 A1 A2 B VDD VSS Z
*.PININFO A1:I A2:I B:I Z:O VDD:B VSS:B
MM_u7 net5 A1 net1 VSS nch l=LA w=WAC m=1
MMI8-M_u2 Z net5 VSS VSS nch l=LA w=WAC m=1
MMI6 net5 B VSS VSS nch l=LA w=WAC m=1
MMI7 net1 A2 VSS VSS nch l=LA w=WAC m=1
MM_u3 net25 A1 net5 VDD pch l=LA w=WAM m=1
MM_u2 net25 B VDD VDD pch l=LA w=WAM m=1
MM_u4 net25 A2 net5 VDD pch l=LA w=WAM m=1
MMI8-M_u3 Z net5 VDD VDD pch l=LA w=WAM m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    XNR2D1
* View Name:    schematic
************************************************************************

.SUBCKT XNR2D1 A1 A2 VDD VSS ZN
*.PININFO A1:I A2:I ZN:O VDD:B VSS:B
MM_u6-M_u2 net27 net9 net44 VDD pch l=LA w=WAB m=1
MM_u4-M_u3 ZN net44 VDD VDD pch l=LA w=WAM m=1
MM_u5-M_u3 net5 net27 VDD VDD pch l=LA w=WL m=1
MM_u8-M_u3 net9 A1 VDD VDD pch l=LA w=WL m=1
MMI0-M_u2 net5 A1 net44 VDD pch l=LA w=WT m=1
MM_u2-M_u3 net27 A2 VDD VDD pch l=LA w=WAM m=1
MM_u6-M_u3 net27 A1 net44 VSS nch l=LA w=WU m=1
MMI0-M_u3 net5 net9 net44 VSS nch l=LA w=WD m=1
MM_u8-M_u2 net9 A1 VSS VSS nch l=LA w=WE m=1
MM_u4-M_u2 ZN net44 VSS VSS nch l=LA w=WAC m=1
MM_u2-M_u2 net27 A2 VSS VSS nch l=LA w=WAC m=1
MM_u5-M_u2 net5 net27 VSS VSS nch l=LA w=WD m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    ND4D1
* View Name:    schematic
************************************************************************

.SUBCKT ND4D1 A1 A2 A3 A4 VDD VSS ZN
*.PININFO A1:I A2:I A3:I A4:I ZN:O VDD:B VSS:B
MMI3 net13 A2 net9 VSS nch l=LA w=WAC m=1
MMI4 net9 A3 net1 VSS nch l=LA w=WAC m=1
MMU53 ZN A1 net13 VSS nch l=LA w=WAC m=1
MMI5 net1 A4 VSS VSS nch l=LA w=WAC m=1
MMI1 ZN A3 VDD VDD pch l=LA w=WAM m=1
MMI2 ZN A4 VDD VDD pch l=LA w=WAM m=1
MMI0 ZN A2 VDD VDD pch l=LA w=WAM m=1
MMI7 ZN A1 VDD VDD pch l=LA w=WAM m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    INR3D0
* View Name:    schematic
************************************************************************

.SUBCKT INR3D0 A1 B1 B2 VDD VSS ZN
*.PININFO A1:I B1:I B2:I ZN:O VDD:B VSS:B
MMU9-M_u1 net13 net9 VDD VDD pch l=LA w=WAM m=1
MMU47-M_u3 net9 A1 VDD VDD pch l=LA w=WM m=1
MMU9-M_u3 ZN B2 net1 VDD pch l=LA w=WAM m=1
MMU9-M_u2 net1 B1 net13 VDD pch l=LA w=WAM m=1
MMU9-M_u6 ZN B2 VSS VSS nch l=LA w=WE m=1
MMU9-M_u4 ZN net9 VSS VSS nch l=LA w=WE m=1
MMU9-M_u5 ZN B1 VSS VSS nch l=LA w=WE m=1
MMU47-M_u2 net9 A1 VSS VSS nch l=LA w=WE m=1
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
MM_u3-M_u3 Z net5 VDD VDD pch l=LA w=WAM m=1
MM_u2-M_u2 net5 A2 VDD VDD pch l=LA w=WAM m=1
MM_u2-M_u1 net5 A1 VDD VDD pch l=LA w=WAM m=1
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
MMI1-M_u1 net13 A2 VDD VDD pch l=LA w=WAM m=1
MMI1-M_u2 ZN A1 net13 VDD pch l=LA w=WAM m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    MAOI222D1
* View Name:    schematic
************************************************************************

.SUBCKT MAOI222D1 A B C VDD VSS ZN
*.PININFO A:I B:I C:I ZN:O VDD:B VSS:B
MMI1 net5 B ZN VSS nch l=LA w=WF m=1
MMI4 net13 B VSS VSS nch l=LA w=WF m=1
MMU6 ZN A net13 VSS nch l=LA w=WAC m=1
MMU9 net5 A ZN VSS nch l=LA w=WAC m=1
MMI5 net5 C VSS VSS nch l=LA w=WF m=1
MMU5 net33 A ZN VDD pch l=LA w=WAL m=1
MMU4 net33 B ZN VDD pch l=LA w=WAL m=1
MMI3 net33 C VDD VDD pch l=LA w=WAL m=1
MMI2 ZN A net28 VDD pch l=LA w=WAL m=1
MMU2 net28 B VDD VDD pch l=LA w=WAL m=1
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
MMI1 net37 B1 VDD VDD pch l=LA w=WAM m=1
MMI3 net33 A2 VDD VDD pch l=LA w=WAM m=1
MMI4 ZN A1 net33 VDD pch l=LA w=WAM m=1
MMI2 ZN net37 VDD VDD pch l=LA w=WAM m=1
MMU3 net37 B2 VDD VDD pch l=LA w=WAM m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    OA32D0
* View Name:    schematic
************************************************************************

.SUBCKT OA32D0 A1 A2 A3 B1 B2 VDD VSS Z
*.PININFO A1:I A2:I A3:I B1:I B2:I Z:O VDD:B VSS:B
MMU1-M_u3 Z net5 VDD VDD pch l=LA w=WL m=1
MMI16-MI13 net17 B1 VDD VDD pch l=LA w=WL m=1
MMI15-MI15 net13 A1 VDD VDD pch l=LA w=WL m=1
MMI16-MI12 net5 B2 net17 VDD pch l=LA w=WL m=1
MMI15-MI12 net5 A3 net1 VDD pch l=LA w=WL m=1
MMI15-MI13 net1 A2 net13 VDD pch l=LA w=WL m=1
MMI3 net5 A3 net33 VSS nch l=LA w=WE m=1
MMU1-M_u2 Z net5 VSS VSS nch l=LA w=WE m=1
MMI11 net33 B2 VSS VSS nch l=LA w=WE m=1
MMI12 net33 B1 VSS VSS nch l=LA w=WE m=1
MMI8 net5 A2 net33 VSS nch l=LA w=WE m=1
MMI9 net5 A1 net33 VSS nch l=LA w=WE m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    IOA21D1
* View Name:    schematic
************************************************************************

.SUBCKT IOA21D1 A1 A2 B VDD VSS ZN
*.PININFO A1:I A2:I B:I ZN:O VDD:B VSS:B
MMU35-M_u2 net5 A2 VDD VDD pch l=LA w=WL m=1
MMU36-M_u1 ZN B VDD VDD pch l=LA w=WAM m=1
MMU35-M_u1 net5 A1 VDD VDD pch l=LA w=WL m=1
MMU36-M_u2 ZN net5 VDD VDD pch l=LA w=WAM m=1
MMU35-M_u4 net29 A2 VSS VSS nch l=LA w=WE m=1
MMU35-M_u3 net5 A1 net29 VSS nch l=LA w=WE m=1
MMU36-M_u3 ZN B net24 VSS nch l=LA w=WAC m=1
MMU36-M_u4 net24 net5 VSS VSS nch l=LA w=WAC m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    OAI32D1
* View Name:    schematic
************************************************************************

.SUBCKT OAI32D1 A1 A2 A3 B1 B2 VDD VSS ZN
*.PININFO A1:I A2:I A3:I B1:I B2:I ZN:O VDD:B VSS:B
MMI16-MI13 net17 B1 VDD VDD pch l=LA w=WAM m=1
MMI15-MI15 net13 A1 VDD VDD pch l=LA w=WAM m=1
MMI16-MI12 ZN B2 net17 VDD pch l=LA w=WAM m=1
MMI15-MI12 ZN A3 net1 VDD pch l=LA w=WAM m=1
MMI15-MI13 net1 A2 net13 VDD pch l=LA w=WAM m=1
MMI1 ZN A1 net25 VSS nch l=LA w=WAC m=1
MMI3 ZN A3 net25 VSS nch l=LA w=WAC m=1
MMI2 ZN A2 net25 VSS nch l=LA w=WAC m=1
MMI0 net25 B2 VSS VSS nch l=LA w=WAC m=1
MM_u4 net25 B1 VSS VSS nch l=LA w=WAC m=1
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
MMU1-M_u3 Z net5 VDD VDD pch l=LA w=WAM m=1
MM_u7-M_u1 net17 A2 VDD VDD pch l=LA w=WAM m=1
MM_u7-M_u2 net5 A1 net17 VDD pch l=LA w=WAM m=1
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
MMU6-M_u3 net11 A1 VDD VDD pch l=LA w=WL m=1
MMU1-M_u2 ZN B1 net20 VDD pch l=LA w=WAM m=1
MMU1-M_u1 net20 net11 VDD VDD pch l=LA w=WAM m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    AOI221D0
* View Name:    schematic
************************************************************************

.SUBCKT AOI221D0 A1 A2 B1 B2 C VDD VSS ZN
*.PININFO A1:I A2:I B1:I B2:I C:I ZN:O VDD:B VSS:B
MMU22 VDD C net20 VDD pch l=LA w=WL m=1
MMI9 net13 A1 ZN VDD pch l=LA w=WN m=1
MMI6 net20 B2 net13 VDD pch l=LA w=WL m=1
MMI7 net20 B1 net13 VDD pch l=LA w=WL m=1
MMI8 net13 A2 ZN VDD pch l=LA w=WN m=1
MMI17-M_u10 ZN B1 net29 VSS nch l=LA w=WE m=1
MMU20 ZN C VSS VSS nch l=LA w=WE m=1
MMI17-M_u11 net29 B2 VSS VSS nch l=LA w=WE m=1
MMI10-M_u10 ZN A1 net28 VSS nch l=LA w=WE m=1
MMI10-M_u11 net28 A2 VSS VSS nch l=LA w=WE m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    OA22D0
* View Name:    schematic
************************************************************************

.SUBCKT OA22D0 A1 A2 B1 B2 VDD VSS Z
*.PININFO A1:I A2:I B1:I B2:I Z:O VDD:B VSS:B
MMU1-M_u2 Z net5 VSS VSS nch l=LA w=WE m=1
MMI18 net13 B1 VSS VSS nch l=LA w=WE m=1
MMI20 net5 A1 net13 VSS nch l=LA w=WE m=1
MMI19 net5 A2 net13 VSS nch l=LA w=WE m=1
MM_u4 net13 B2 VSS VSS nch l=LA w=WE m=1
MMU1-M_u3 Z net5 VDD VDD pch l=LA w=WL m=1
MMU24 net33 B2 VDD VDD pch l=LA w=WL m=1
MMI17 net5 A1 net32 VDD pch l=LA w=WL m=1
MMI15 net5 B1 net33 VDD pch l=LA w=WL m=1
MMI16 net32 A2 VDD VDD pch l=LA w=WL m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    MUX2D0
* View Name:    schematic
************************************************************************

.SUBCKT MUX2D0 I0 I1 S VDD VSS Z
*.PININFO I0:I I1:I S:I Z:O VDD:B VSS:B
MMU29-M_u3 Z net5 VDD VDD pch l=LA w=WL m=1
MMI15-M_u3 net17 S VDD VDD pch l=LA w=WK m=1
MMI111 net13 I0 VDD VDD pch l=LA w=WL m=1
MMI24 net9 I1 VDD VDD pch l=LA w=WL m=1
MMI5 net5 S net13 VDD pch l=LA w=WL m=1
MMI25 net5 net17 net9 VDD pch l=LA w=WL m=1
MMI15-M_u2 net17 S VSS VSS nch l=LA w=WE m=1
MMI20 net36 I1 VSS VSS nch l=LA w=WE m=1
MMI12 net5 net17 net25 VSS nch l=LA w=WE m=1
MMI21 net5 S net36 VSS nch l=LA w=WE m=1
MMU29-M_u2 Z net5 VSS VSS nch l=LA w=WE m=1
MMI19 net25 I0 VSS VSS nch l=LA w=WE m=1
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
MMI22-M_u3 net5 CP VDD VDD pch l=LA w=WL m=1
MMI32-M_u3 net63 net5 VDD VDD pch l=LA w=WL m=1
MMI43 net101 net37 VDD VDD pch l=LA w=WA m=1
MMI6 net97 D net100 VDD pch l=LA w=WAI m=1
MMI27-M_u3 Q net81 VDD VDD pch l=LA w=WAM m=1
MMI44 net101 CDN VDD VDD pch l=LA w=WA m=1
MMI13-M_u3 net37 net97 VDD VDD pch l=LA w=WG m=1
MMI21-M_u1 net81 net51 VDD VDD pch l=LA w=WAE m=1
MMI16 net37 net5 net51 VDD pch l=LA w=WJ m=1
MMI24 net72 net81 VDD VDD pch l=LA w=WA m=1
MMI28 net51 net63 net72 VDD pch l=LA w=WA m=1
MMI45 net97 net5 net101 VDD pch l=LA w=WA m=1
MMI7 net100 net63 VDD VDD pch l=LA w=WAI m=1
MMI21-M_u2 net81 CDN VDD VDD pch l=LA w=WAE m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    DFD1
* View Name:    schematic
************************************************************************

.SUBCKT DFD1 CP D Q QN VDD VSS
*.PININFO CP:I D:I Q:O QN:O VDD:B VSS:B
MMI53-M_u2 net67 net100 VSS VSS nch l=LA w=WAC m=1
MMI29-M_u2 QN net97 VSS VSS nch l=LA w=WAC m=1
MMI4 net20 net13 VSS VSS nch l=LA w=WAB m=1
MMI55 net97 net13 net100 VSS nch l=LA w=WA m=1
MMI13-M_u2 net11 net17 VSS VSS nch l=LA w=WAC m=1
MMI50 net11 net99 net100 VSS nch l=LA w=WO m=1
MMI57-M_u2 net97 net67 VSS VSS nch l=LA w=WE m=1
MMI32-M_u2 net99 net13 VSS VSS nch l=LA w=WC m=1
MMI5 net17 D net20 VSS nch l=LA w=WAB m=1
MMI31-M_u2 net13 CP VSS VSS nch l=LA w=WE m=1
MMI48 net9 net11 VSS VSS nch l=LA w=WA m=1
MMI27-M_u2 Q net67 VSS VSS nch l=LA w=WAC m=1
MMI47 net17 net99 net9 VSS nch l=LA w=WA m=1
MMI53-M_u3 net67 net100 VDD VDD pch l=LA w=WAM m=1
MMI54 net97 net99 net100 VDD pch l=LA w=WA m=1
MMI32-M_u3 net99 net13 VDD VDD pch l=LA w=WL m=1
MMI43 net60 net11 VDD VDD pch l=LA w=WA m=1
MMI6 net17 D net53 VDD pch l=LA w=WAI m=1
MMI29-M_u3 QN net97 VDD VDD pch l=LA w=WAM m=1
MMI31-M_u3 net13 CP VDD VDD pch l=LA w=WL m=1
MMI27-M_u3 Q net67 VDD VDD pch l=LA w=WAM m=1
MMI13-M_u3 net11 net17 VDD VDD pch l=LA w=WAM m=1
MMI57-M_u3 net97 net67 VDD VDD pch l=LA w=WL m=1
MMI52 net11 net13 net100 VDD pch l=LA w=WP m=1
MMI45 net17 net13 net60 VDD pch l=LA w=WA m=1
MMI7 net53 net99 VDD VDD pch l=LA w=WAI m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    OA222D1
* View Name:    schematic
************************************************************************

.SUBCKT OA222D1 A1 A2 B1 B2 C1 C2 VDD VSS Z
*.PININFO A1:I A2:I B1:I B2:I C1:I C2:I Z:O VDD:B VSS:B
MMU25 net9 C1 VSS VSS nch l=LA w=WAC m=1
MMI18 net33 A2 net20 VSS nch l=LA w=WAC m=1
MMI17 net33 A1 net20 VSS nch l=LA w=WAC m=1
MMI15 net20 B1 net9 VSS nch l=LA w=WAC m=1
MMI14 net9 C2 VSS VSS nch l=LA w=WAC m=1
MMI16 net20 B2 net9 VSS nch l=LA w=WAC m=1
MMI19-M_u2 Z net33 VSS VSS nch l=LA w=WAC m=1
MMI13 net33 A1 net56 VDD pch l=LA w=WAM m=1
MMI2 net49 C1 VDD VDD pch l=LA w=WAM m=1
MMI11 net45 B1 VDD VDD pch l=LA w=WAM m=1
MMI12 net56 A2 VDD VDD pch l=LA w=WAM m=1
MMI19-M_u3 Z net33 VDD VDD pch l=LA w=WAM m=1
MMI8 net33 C2 net49 VDD pch l=LA w=WAM m=1
MMI9 net33 B2 net45 VDD pch l=LA w=WAM m=1
.ENDS

************************************************************************
* Library Name: tcbn65lp
* Cell Name:    IAO21D1
* View Name:    schematic
************************************************************************

.SUBCKT IAO21D1 A1 A2 B VDD VSS ZN
*.PININFO A1:I A2:I B:I ZN:O VDD:B VSS:B
MMU37-M_u3 net11 A2 VSS VSS nch l=LA w=WE m=1
MMU39-M_u3 ZN net11 VSS VSS nch l=LA w=WAC m=1
MMU39-M_u4 ZN B VSS VSS nch l=LA w=WAC m=1
MMU37-M_u4 net11 A1 VSS VSS nch l=LA w=WE m=1
MMU39-M_u2 ZN B net25 VDD pch l=LA w=WAM m=1
MMU39-M_u1 net25 net11 VDD VDD pch l=LA w=WAM m=1
MMU37-M_u2 net11 A1 net24 VDD pch l=LA w=WL m=1
MMU37-M_u1 net24 A2 VDD VDD pch l=LA w=WL m=1
.ENDS

************************************************************************
* Library Name: civicR
* Cell Name:    DLDO_LOGIC_V1
* View Name:    schematic
************************************************************************

.SUBCKT DLDO_LOGIC_V1 BOOST CFG_1<5> CFG_1<4> CFG_1<3> CFG_1<2> CFG_1<1> 
+ CFG_1<0> CFG_2<5> CFG_2<4> CFG_2<3> CFG_2<2> CFG_2<1> CFG_2<0> CLK CODE<5> 
+ CODE<4> CODE<3> CODE<2> CODE<1> CODE<0> DIN<15> DIN<14> DIN<13> DIN<12> 
+ DIN<11> DIN<10> DIN<9> DIN<8> DIN<7> DIN<6> DIN<5> DIN<4> DIN<3> DIN<2> 
+ DIN<1> DIN<0> EN_LDO MODE SEL<1> SEL<0> VDD VSS 
*.PININFO BOOST:I CFG_1<5>:I CFG_1<4>:I CFG_1<3>:I CFG_1<2>:I CFG_1<1>:I 
*.PININFO CFG_1<0>:I CFG_2<5>:I CFG_2<4>:I CFG_2<3>:I CFG_2<2>:I CFG_2<1>:I 
*.PININFO CFG_2<0>:I CLK:I DIN<15>:I DIN<14>:I DIN<13>:I DIN<12>:I DIN<11>:I 
*.PININFO DIN<10>:I DIN<9>:I DIN<8>:I DIN<7>:I DIN<6>:I DIN<5>:I DIN<4>:I 
*.PININFO DIN<3>:I DIN<2>:I DIN<1>:I DIN<0>:I EN_LDO:I MODE:I SEL<1>:I 
*.PININFO SEL<0>:I CODE<5>:O CODE<4>:O CODE<3>:O CODE<2>:O CODE<1>:O CODE<0>:O 
*.PININFO thm2bin<4>:O thm2bin<3>:O thm2bin<2>:O thm2bin<1>:O thm2bin<0>:O 
*.PININFO VDD:B VSS:B
XU123 N935 N157 VDD VSS N45 / CKND2D1
XU124 CFG_2<5> N157 VDD VSS N140 / CKND2D1
XU155 N941 N940 VDD VSS N942 / CKND2D1
XU115 CFG_2<4> N157 VDD VSS N139 / CKND2D1
XU114 N927 N157 VDD VSS N44 / CKND2D1
XU47 N52 N1 VDD VSS N930 / CKND2D1
XU51 N936 N894 VDD VSS N896 / CKND2D1
XU103 CFG_2<0> N157 VDD VSS N179 / CKND2D1
XU102 N917 N157 VDD VSS N178 / CKND2D1
XU76 N903 N1 VDD VSS N907 / CKND2D1
XU110 N157 CFG_2<1> VDD VSS N181 / CKND2D1
XU109 N157 N922 VDD VSS N180 / CKND2D1
XU99 CFG_2<3> N157 VDD VSS N138 / CKND2D1
XU97 N915 N157 VDD VSS N43 / CKND2D1
XU80 N157 CFG_2<2> VDD VSS N137 / CKND2D1
XU79 N157 N906 VDD VSS N46 / CKND2D1
XU87 N908 N907 VDD VSS N909 / CKND2D1
XU170 N951 N950 VDD VSS N381 / CKND2D1
XU67 N177 N900 VDD VSS N918 / CKND2D1
XU168 N951 N949 VDD VSS CODE<4> / CKND2D1
XU166 N951 N948 VDD VSS CODE<3> / CKND2D1
XU164 N951 N947 VDD VSS CODE<2> / CKND2D1
XU162 N951 N946 VDD VSS CODE<1> / CKND2D1
XU160 N951 N945 VDD VSS CODE<0> / CKND2D1
XU57 N889 N952 VDD VSS N57 / CKND2D1
XU158 MODE CODE_REG<6> VDD VSS N951 / CKND2D1
XU118 N937 VDD VSS N928 / CKND1
XU116 CODE_REG<4> VDD VSS N929 / CKND1
XU172 CFG_1<0> VDD VSS N957 / CKND1
XU122 CFG_2<5> VDD VSS N935 / CKND1
XU60 N27 VDD VSS N938 / CKND1
XU113 CFG_2<4> VDD VSS N927 / CKND1
XU50 CODE_REG<6> VDD VSS N894 / CKND1
XU171 CFG_1<1> VDD VSS N956 / CKND1
XU173 CFG_1<2> VDD VSS N955 / CKND1
XU174 CFG_1<3> VDD VSS N954 / CKND1
XU49 CODE_REG<5> VDD VSS N936 / CKND1
XU2 N930 VDD VSS N2 / CKND1
XU74 N54 VDD VSS N901 / CKND1
XU78 CFG_2<2> VDD VSS N906 / CKND1
XU58 N57 VDD VSS N899 / CKND1
XU59 N177 VDD VSS N898 / CKND1
XU45 N62 VDD VSS N952 / CKND1
XU66 N58 VDD VSS N900 / CKND1
XU56 N52 VDD VSS N895 / CKND1
XU100 CFG_2<0> VDD VSS N917 / CKND1
XU1 BOOST VDD VSS N1 / CKND1
XU68 N918 VDD VSS N924 / CKND1
XU104 CFG_2<1> VDD VSS N922 / CKND1
XU84 CFG_2<3> VDD VSS N915 / CKND1
XU54 CODE_REG<1> VDD VSS N897 / CKND1
XU53 CODE_REG<3> VDD VSS N911 / CKND1
XU52 CODE_REG<2> VDD VSS N912 / CKND1
XU117 CODE_REG<4> N890 N2 VDD VSS N937 / ND3D1
XU65 N63 N62 N889 VDD VSS N58 / ND3D1
XU55 N912 N911 N897 VDD VSS N923 / ND3D1
XU153 N937 N936 VDD VSS N943 / NR2XD0
XU69 N52 N924 VDD VSS N902 / NR2XD0
XU105 BOOST N918 VDD VSS N919 / NR2XD0
XU111 N924 N923 VDD VSS N925 / NR2XD0
XU121 N933 N941 CODE_REG<5> VDD VSS N934 / MUX2ND0
XU154 N2 N938 CODE_REG<5> VDD VSS N940 / MUX2ND0
XU156 N943 N942 CODE_REG<6> VDD VSS N944 / MUX2ND0
XU120 N930 N27 CODE_REG<4> VDD VSS N932 / MUX2ND0
XU75 N902 N901 CODE_REG<1> VDD VSS N903 / MUX2ND0
XU106 N2 N919 CODE_REG<1> VDD VSS N921 / MUX2ND0
XU77 N904 N907 CODE_REG<2> VDD VSS N905 / MUX2ND0
XU86 N2 N938 CODE_REG<2> VDD VSS N908 / MUX2ND0
XU90 N910 N909 CODE_REG<3> VDD VSS N914 / MUX2ND0
XU169 CFG_1<5> CODE_REG<5> MODE VDD VSS N950 / MUX2ND0
XU167 CFG_1<4> CODE_REG<4> MODE VDD VSS N949 / MUX2ND0
XU165 CFG_1<3> CODE_REG<3> MODE VDD VSS N948 / MUX2ND0
XU163 CFG_1<2> CODE_REG<2> MODE VDD VSS N947 / MUX2ND0
XU161 CFG_1<1> CODE_REG<1> MODE VDD VSS N946 / MUX2ND0
XU159 CFG_1<0> N177 MODE VDD VSS N945 / MUX2ND0
XU7 N896 CODE_REG<4> N923 N895 VDD VSS N889 / OA31D1
XU44 N381 VDD VSS CODE<5> / CKBD1
XU4 BOOST N952 N63 N52 VDD VSS N886 / NR4D0
XU8 CODE_REG<3> CODE_REG<1> CODE_REG<2> VDD VSS N890 / AN3XD1
XU5 N888 N912 N911 VDD VSS N887 / AN3XD1
XU85 CODE_REG<2> CODE_REG<1> N2 VDD VSS N910 / AN3XD1
XU6 N899 N898 N938 N897 VDD VSS N888 / OA211D1
XCODE_REG_REG_5_ N45 CLK N136 CODE_REG<5> N140 VDD VSS / DFCSNQD1
XCODE_REG_REG_4_ N44 CLK N230 CODE_REG<4> N139 VDD VSS / DFCSNQD1
XCODE_REG_REG_0_ N178 CLK N226 N177 N179 VDD VSS / DFCSNQD1
XCODE_REG_REG_1_ N180 CLK N227 CODE_REG<1> N181 VDD VSS / DFCSNQD1
XCODE_REG_REG_3_ N43 CLK N229 CODE_REG<3> N138 VDD VSS / DFCSNQD1
XCODE_REG_REG_2_ N46 CLK N228 CODE_REG<2> N137 VDD VSS / DFCSNQD1
XU119 N887 N929 N928 VDD VSS N933 / AOI21D1
XU15 N79 N109 N80 VDD VSS N106 / AOI21D1
XU21 DIN<15> DIN<9> N112 VDD VSS N111 / AOI21D1
XU107 N203 N886 N888 VDD VSS N920 / AOI21D1
XU91 N205 N886 N887 VDD VSS N913 / AOI21D1
XU64 N2 CODE_REG<1> N888 VDD VSS N904 / AOI21D1
XU3 N206 N886 CFG_2<4> BOOST N926 VDD VSS N230 / AO221D0
XU31 N207 N886 CFG_2<5> BOOST N934 VDD VSS N136 / AO221D0
XU32 N177 N2 N202 N886 N916 VDD VSS N226 / AO221D0
XU28 N204 N886 CFG_2<2> BOOST N905 VDD VSS N228 / AO221D0
XU108 N1 N922 N921 N920 VDD VSS N227 / OAI211D1
XU95 N1 N915 N914 N913 VDD VSS N229 / OAI211D1
XU11 N65 N734 VDD VSS N71 / ND2D1
XU14 N54 N1 VDD VSS N27 / ND2D1
XU10 N58 N57 VDD VSS N54 / ND2D1
XU101 N58 N57 N917 N177 BOOST VDD VSS N916 / MUX3ND0
XU22 DIN<1> N15 DIN<3> N78 VDD VSS N791 / OAI22D1
XU20 DIN<13> N76 DIN<7> N77 VDD VSS N777 / OAI22D1
XU27 DIN<0> N81 DIN<10> N82 VDD VSS N768 / OAI22D1
XU112 N27 N925 N890 N930 VDD VSS N931 / OAI22D1
XADD_46 CODE_REG<6> CODE_REG<5> CODE_REG<4> CODE_REG<3> CODE_REG<2> 
+ CODE_REG<1> N177 N208 N207 N206 N205 N204 N203 N202 VDD VSS / 
+ DLDO_LOGIC_V1_DW01_inc_0
XU139 N105 N103 VDD VSS N116 / CKXOR2D1
XU138 N94 N93 VDD VSS N779 / CKXOR2D1
XU136 N777 N112 VDD VSS N94 / CKXOR2D1
XU137 N110 N95 VDD VSS N93 / CKXOR2D1
XU135 N733 N791 VDD VSS N95 / CKXOR2D1
XU150 N88 N87 VDD VSS N108 / CKXOR2D1
XU148 DIN<13> DIN<12> VDD VSS N88 / CKXOR2D1
XU149 DIN<7> DIN<2> VDD VSS N87 / CKXOR2D1
XU134 N97 N96 VDD VSS N741 / CKXOR2D1
XU132 N768 N113 VDD VSS N97 / CKXOR2D1
XU133 N109 N98 VDD VSS N96 / CKXOR2D1
XU131 N731 N767 VDD VSS N98 / CKXOR2D1
XU146 N90 N89 VDD VSS N114 / CKXOR2D1
XU144 DIN<10> DIN<8> VDD VSS N90 / CKXOR2D1
XU145 DIN<4> DIN<0> VDD VSS N89 / CKXOR2D1
XU143 N92 N91 VDD VSS N107 / CKXOR2D1
XU141 DIN<14> DIN<11> VDD VSS N92 / CKXOR2D1
XU142 DIN<6> DIN<5> VDD VSS N91 / CKXOR2D1
XU63 N70 N71 VDD VSS N885 / CKXOR2D1
XU128 N101 N100 VDD VSS N18 / CKXOR2D1
XU126 N728 N732 VDD VSS N101 / CKXOR2D1
XU127 N106 N102 VDD VSS N100 / CKXOR2D1
XU125 N739 N734 VDD VSS N102 / CKXOR2D1
XU130 N741 N99 VDD VSS N115 / CKXOR2D1
XU129 N104 N779 VDD VSS N99 / CKXOR2D1
XU152 N111 N86 VDD VSS N736 / CKXOR2D1
XU151 DIN<3> DIN<1> VDD VSS N86 / CKXOR2D1
XU147 N736 N108 VDD VSS N105 / CKXOR2D1
XU140 N114 N107 VDD VSS N103 / CKXOR2D1
XU93 N731 N767 VDD VSS N79 / CKXOR2D1
XU73 N791 N112 VDD VSS N74 / CKXOR2D1
XU96 DIN<6> DIN<14> VDD VSS N84 / CKXOR2D1
XU23 N111 VDD VSS N15 / INVD1
XU9 N739 VDD VSS N14 / INVD1
XU37 DIN<11> VDD VSS N17 / INVD1
XU30 N2 N890 N887 VDD VSS N891 / AO21D1
XU62 N956 N115 N116 VDD VSS N69 / AO21D1
XU89 DIN<4> DIN<8> N113 VDD VSS N81 / AO21D1
XU71 DIN<2> DIN<12> VDD VSS N76 / XNR2D1
XU83 N106 N734 VDD VSS N72 / XNR2D1
XU19 N65 N732 N66 N734 VDD VSS N62 / ND4D1
XU41 N113 DIN<0> DIN<10> VDD VSS N65 / INR3D0
XU40 N731 DIN<11> DIN<5> VDD VSS N734 / INR3D0
XU38 N112 DIN<1> DIN<3> VDD VSS N732 / INR3D0
XU39 N733 DIN<13> DIN<7> VDD VSS N66 / INR3D0
XU70 N76 DIN<13> VDD VSS N77 / AN2XD1
XU88 N81 DIN<0> VDD VSS N82 / AN2XD1
XU82 N105 N103 VDD VSS N104 / AN2XD1
XU72 N108 N736 VDD VSS N110 / AN2XD1
XU92 N114 N107 VDD VSS N109 / AN2XD1
XU36 N84 N17 VDD VSS N83 / NR2D1
XU33 N932 N931 VDD VSS N941 / NR2D1
XU25 DIN<9> DIN<15> VDD VSS N112 / NR2D1
XU42 DIN<12> DIN<2> VDD VSS N733 / NR2D1
XU26 DIN<4> DIN<8> VDD VSS N113 / NR2D1
XU43 DIN<14> DIN<6> VDD VSS N731 / NR2D1
XU81 N779 N104 N741 VDD VSS N739 / MAOI222D1
XU94 DIN<5> N83 N17 N84 VDD VSS N767 / MOAI22D1
XU16 N79 N109 N65 N113 N768 VDD VSS N80 / OA32D0
XU157 N208 N886 N944 VDD VSS N377 / IOA21D1
XU17 N74 N110 N75 VDD VSS N728 / IOA21D1
XU18 N74 N110 N66 N777 N733 VDD VSS N75 / OAI32D1
XU98 SEL<0> SEL<1> VDD VSS N52 / OR2D1
XU24 DIN<1> N111 VDD VSS N78 / INR2D1
XU35 N954 N885 N955 N18 N68 VDD VSS N892 / AOI221D0
XU12 N72 N14 N732 N66 N73 VDD VSS N70 / AOI221D0
XU13 N72 N14 N728 N732 VDD VSS N73 / OA22D0
XU29 N891 N931 CODE_REG<4> VDD VSS N926 / MUX2D0
XCODE_REG_REG_6_ EN_LDO_REG CLK N377 CODE_REG<6> VDD VSS / DFCNQD1
XEN_LDO_REG_REG CLK EN_LDO EN_LDO_REG N157 VDD VSS / DFD1
XU61 N115 N956 N957 N69 N18 N955 VDD VSS N68 / OA222D1
XU34 N885 N954 N892 VDD VSS N63 / IAO21D1
.ENDS

************************************************************************
* Library Name: civicR
* Cell Name:    DLDO_TOP
* View Name:    schematic
************************************************************************

.SUBCKT Sanitized_civiR_DLDO_TOP BOOST CFG_1<5> CFG_1<4> CFG_1<3> CFG_1<2> CFG_1<1> CFG_1<0> 
+ CFG_2<5> CFG_2<4> CFG_2<3> CFG_2<2> CFG_2<1> CFG_2<0> CODE<5> CODE<4> 
+ CODE<3> CODE<2> CODE<1> CODE<0> LDO_EN MODE NRO<2> NRO<1> NRO<0> SYS_CLK 
+ SYS_CLK_cts_0 VDD VOUT VSS
*.PININFO BOOST:I CFG_1<5>:I CFG_1<4>:I CFG_1<3>:I CFG_1<2>:I CFG_1<1>:I 
*.PININFO CFG_1<0>:I CFG_2<5>:I CFG_2<4>:I CFG_2<3>:I CFG_2<2>:I CFG_2<1>:I 
*.PININFO CFG_2<0>:I LDO_EN:I MODE:I NRO<2>:I NRO<1>:I NRO<0>:I SYS_CLK:I 
*.PININFO SYS_CLK_cts_0:I CODE<5>:O CODE<4>:O CODE<3>:O CODE<2>:O CODE<1>:O 
*.PININFO CODE<0>:O VDD:B VOUT:B VSS:B
XI5 SYS_CLK LDO_EN net012 VDD VSS / DFQD1
XI3 net012 VDD VSS net014 / INVD1
Xloop0 CODE<5> CODE<4> CODE<3> CODE<2> CODE<1> CODE<0> net22<0> net22<1> 
+ net22<2> net22<3> net22<4> net22<5> net22<6> net22<7> net22<8> net22<9> 
+ net22<10> net22<11> net22<12> net22<13> net22<14> net22<15> net011 NRO<2> 
+ NRO<1> NRO<0> SEL<1> SEL<0> SYS_CLK_cts_0 VDD VOUT VSS / DLDO_LOOP
XI4 net014 VDD VSS net011 / CKND3
Xlogic1 BOOST CFG_1<5> CFG_1<4> CFG_1<3> CFG_1<2> CFG_1<1> CFG_1<0> CFG_2<5> 
+ CFG_2<4> CFG_2<3> CFG_2<2> CFG_2<1> CFG_2<0> SYS_CLK CODE<5> CODE<4> CODE<3> 
+ CODE<2> CODE<1> CODE<0> net22<0> net22<1> net22<2> net22<3> net22<4> 
+ net22<5> net22<6> net22<7> net22<8> net22<9> net22<10> net22<11> net22<12> 
+ net22<13> net22<14> net22<15> net011 MODE SEL<1> SEL<0> VDD VSS / DLDO_LOGIC_V1
.ENDS

