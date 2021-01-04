*.BIPOLAR
*.RESI = 2000
*.SCALE METER
*.MEGA
*.RESVAL
*.CAPVAL
*.DIOPERI
*.DIOAREA
*.EQUATION
.PARAM



.SUBCKT nmos4_18 B D G S
*.PININFO B:B D:B G:B S:B
MM0 D G S B n2svt l=l nfin=w nf=nf m=1
.ENDS

.SUBCKT nmos4_svt B D G S
*.PININFO B:B D:B G:B S:B
MM0 D G S B n1svt l=l nfin=w nf=nf m=1
.ENDS

.SUBCKT nmos4_lvt B D G S
*.PININFO B:B D:B G:B S:B
MM0 D G S B n1lvt l=l nfin=w nf=nf m=1
.ENDS

.SUBCKT nmos4_hvt B D G S
*.PININFO B:B D:B G:B S:B
MM0 D G S B n1hvt l=l nfin=w nf=nf m=1
.ENDS

.SUBCKT nmos4_standard B D G S
*.PININFO B:B D:B G:B S:B
MM0 D G S B n1svt l=l nfin=w nf=nf m=1
.ENDS

.SUBCKT nmos4_fast B D G S
*.PININFO B:B D:B G:B S:B
MM0 D G S B n1lvt l=l nfin=w nf=nf m=1
.ENDS

.SUBCKT nmos4_low_power B D G S
*.PININFO B:B D:B G:B S:B
MM0 D G S B n1hvt l=l nfin=w nf=nf m=1
.ENDS

.SUBCKT pmos4_18 B D G S
*.PININFO B:B D:B G:B S:B
MM0 D G S B p2svt l=l nfin=w nf=nf m=1
.ENDS

.SUBCKT pmos4_svt B D G S
*.PININFO B:B D:B G:B S:B
MM0 D G S B p1svt l=l nfin=w nf=nf m=1
.ENDS

.SUBCKT pmos4_lvt B D G S
*.PININFO B:B D:B G:B S:B
MM0 D G S B p1lvt l=l nfin=w nf=nf m=1
.ENDS

.SUBCKT pmos4_hvt B D G S
*.PININFO B:B D:B G:B S:B
MM0 D G S B p1hvt l=l nfin=w nf=nf m=1
.ENDS

.SUBCKT pmos4_standard B D G S
*.PININFO B:B D:B G:B S:B
MM0 D G S B p1svt l=l nfin=w nf=nf m=1
.ENDS

.SUBCKT pmos4_fast B D G S
*.PININFO B:B D:B G:B S:B
MM0 D G S B p1lvt l=l nfin=w nf=nf m=1
.ENDS

.SUBCKT pmos4_low_power B D G S
*.PININFO B:B D:B G:B S:B
MM0 D G S B p1hvt l=l nfin=w nf=nf m=1
.ENDS

.SUBCKT res_metal_1 MINUS PLUS
*.PININFO MINUS:B PLUS:B
RR0 PLUS MINUS $[resm1]  l=l w=w r=0.0736*l/w
.ENDS

.SUBCKT res_metal_2 MINUS PLUS
*.PININFO MINUS:B PLUS:B
RR0 PLUS MINUS $[resm2]  l=l w=w r=0.0604*l/w
.ENDS

.SUBCKT res_metal_3 MINUS PLUS
*.PININFO MINUS:B PLUS:B
RR0 PLUS MINUS $[resm3]  l=l w=w r=0.0604*l/w
.ENDS

.SUBCKT res_metal_4 MINUS PLUS
*.PININFO MINUS:B PLUS:B
RR0 PLUS MINUS $[resm4]  l=l w=w r=0.0604*l/w
.ENDS

.SUBCKT res_metal_5 MINUS PLUS
*.PININFO MINUS:B PLUS:B
RR0 PLUS MINUS $[resm5]  l=l w=w r=0.0604*l/w
.ENDS

.SUBCKT res_metal_6 MINUS PLUS
*.PININFO MINUS:B PLUS:B
RR0 PLUS MINUS $[resm6]  l=l w=w r=0.0604*l/w
.ENDS

.SUBCKT res_metal_7 MINUS PLUS
*.PININFO MINUS:B PLUS:B
RR0 PLUS MINUS $[resm7]  l=l w=w r=0.0604*l/w
.ENDS

.SUBCKT res_metal_8 MINUS PLUS
*.PININFO MINUS:B PLUS:B
RR0 PLUS MINUS $[resmt]  l=l w=w r=0.0214*l/w
.ENDS


.SUBCKT nmos4_lvt_w4_l36_seg1 b d g s
*.PININFO b:B d:B g:B s:B
XN b d g s / nmos4_lvt l=18n nf=1 w=4
.ENDS


.SUBCKT pmos4_lvt_w4_l36_seg1 b d g s
*.PININFO b:B d:B g:B s:B
XP b d g s / pmos4_lvt l=18n nf=1 w=4
.ENDS


.SUBCKT inv in out VDD VSS
*.PININFO in:I out:O VDD:B VSS:B
XN VSS out in VSS / nmos4_lvt_w4_l36_seg1
XP VDD out in VDD / pmos4_lvt_w4_l36_seg1
.ENDS


.SUBCKT nmos4_lvt_stack2_w4_l36_seg1 b d g<1> g<0> s
*.PININFO b:B d:B g<1>:B g<0>:B s:B
XN_0 b m g<0> s / nmos4_lvt l=18n nf=1 w=4
XN_1 b d g<1> m / nmos4_lvt l=18n nf=1 w=4
.ENDS


.SUBCKT nand in<1> in<0> out VDD VSS
*.PININFO in<1>:I in<0>:I out:O VDD:B VSS:B
XN VSS out in<1> in<0> VSS / nmos4_lvt_stack2_w4_l36_seg1
XP_1 VDD out in<1> VDD / pmos4_lvt_w4_l36_seg1
XP_0 VDD out in<0> VDD / pmos4_lvt_w4_l36_seg1
.ENDS


.SUBCKT aib_dlycell_core bk1 ci_p in_p co_p out_p VDD VSS
*.PININFO bk1:I ci_p:I in_p:I co_p:O out_p:O VDD:B VSS:B
XNAND_SR0 sr1_o bk1 sr0_o VDD VSS / nand
XNAND_SR1 sr0_o in_p sr1_o VDD VSS / nand
XNAND_in bk1 in_p co_p VDD VSS / nand
XNAND_out sr1_o ci_p out_p VDD VSS / nand
.ENDS


.SUBCKT aib_dlycell_no_flop bk ci_p in_p co_p out_p VDD VSS
*.PININFO bk:I ci_p:I in_p:I co_p:O out_p:O VDD:B VSS:B
XBKInv0 bk bk_mid VDD VSS / inv
XBKInv1 bk_mid bk1 VDD VSS / inv
XCore bk1 ci_p in_p co_p out_p VDD VSS / aib_dlycell_core
.ENDS


.SUBCKT aib_dlycell_no_flop_1 bk ci_p in_p co_p out_p VDD VSS
*.PININFO bk:I ci_p:I in_p:I co_p:O out_p:O VDD:B VSS:B
XBKInv0 bk bk_mid VDD VSS / inv
XBKInv1 bk_mid bk1 VDD VSS / inv
XCore bk1 ci_p in_p co_p out_p VDD VSS / aib_dlycell_core
.ENDS


.SUBCKT dcc_delay_line b63 bk<63> bk<62> bk<61> bk<60> bk<59> bk<58> bk<57>
+ bk<56> bk<55> bk<54> bk<53> bk<52> bk<51> bk<50> bk<49> bk<48> bk<47> bk<46>
+ bk<45> bk<44> bk<43> bk<42> bk<41> bk<40> bk<39> bk<38> bk<37> bk<36> bk<35>
+ bk<34> bk<33> bk<32> bk<31> bk<30> bk<29> bk<28> bk<27> bk<26> bk<25> bk<24>
+ bk<23> bk<22> bk<21> bk<20> bk<19> bk<18> bk<17> bk<16> bk<15> bk<14> bk<13>
+ bk<12> bk<11> bk<10> bk<9> bk<8> bk<7> bk<6> bk<5> bk<4> bk<3> bk<2> bk<1>
+ bk<0> dlyin a63 dlyout VDD VSS
*.PININFO b63:I bk<63>:I bk<62>:I bk<61>:I bk<60>:I bk<59>:I bk<58>:I bk<57>:I
*+ bk<56>:I bk<55>:I bk<54>:I bk<53>:I bk<52>:I bk<51>:I bk<50>:I bk<49>:I
*+ bk<48>:I bk<47>:I bk<46>:I bk<45>:I bk<44>:I bk<43>:I bk<42>:I bk<41>:I
*+ bk<40>:I bk<39>:I bk<38>:I bk<37>:I bk<36>:I bk<35>:I bk<34>:I bk<33>:I
*+ bk<32>:I bk<31>:I bk<30>:I bk<29>:I bk<28>:I bk<27>:I bk<26>:I bk<25>:I
*+ bk<24>:I bk<23>:I bk<22>:I bk<21>:I bk<20>:I bk<19>:I bk<18>:I bk<17>:I
*+ bk<16>:I bk<15>:I bk<14>:I bk<13>:I bk<12>:I bk<11>:I bk<10>:I bk<9>:I bk<8>:I
*+ bk<7>:I bk<6>:I bk<5>:I bk<4>:I bk<3>:I bk<2>:I bk<1>:I bk<0>:I dlyin:I a63:O
*+ dlyout:O VDD:B VSS:B
XCELL_63 bk<63> b63 a<62> a63 b<62> VDD VSS / aib_dlycell_no_flop
XCELL_62 bk<62> b<62> a<61> a<62> b<61> VDD VSS / aib_dlycell_no_flop
XCELL_61 bk<61> b<61> a<60> a<61> b<60> VDD VSS / aib_dlycell_no_flop
XCELL_60 bk<60> b<60> a<59> a<60> b<59> VDD VSS / aib_dlycell_no_flop
XCELL_59 bk<59> b<59> a<58> a<59> b<58> VDD VSS / aib_dlycell_no_flop
XCELL_58 bk<58> b<58> a<57> a<58> b<57> VDD VSS / aib_dlycell_no_flop
XCELL_57 bk<57> b<57> a<56> a<57> b<56> VDD VSS / aib_dlycell_no_flop
XCELL_56 bk<56> b<56> a<55> a<56> b<55> VDD VSS / aib_dlycell_no_flop
XCELL_55 bk<55> b<55> a<54> a<55> b<54> VDD VSS / aib_dlycell_no_flop
XCELL_54 bk<54> b<54> a<53> a<54> b<53> VDD VSS / aib_dlycell_no_flop
XCELL_53 bk<53> b<53> a<52> a<53> b<52> VDD VSS / aib_dlycell_no_flop
XCELL_52 bk<52> b<52> a<51> a<52> b<51> VDD VSS / aib_dlycell_no_flop
XCELL_51 bk<51> b<51> a<50> a<51> b<50> VDD VSS / aib_dlycell_no_flop
XCELL_50 bk<50> b<50> a<49> a<50> b<49> VDD VSS / aib_dlycell_no_flop
XCELL_49 bk<49> b<49> a<48> a<49> b<48> VDD VSS / aib_dlycell_no_flop
XCELL_48 bk<48> b<48> a<47> a<48> b<47> VDD VSS / aib_dlycell_no_flop
XCELL_47 bk<47> b<47> a<46> a<47> b<46> VDD VSS / aib_dlycell_no_flop
XCELL_46 bk<46> b<46> a<45> a<46> b<45> VDD VSS / aib_dlycell_no_flop
XCELL_45 bk<45> b<45> a<44> a<45> b<44> VDD VSS / aib_dlycell_no_flop
XCELL_44 bk<44> b<44> a<43> a<44> b<43> VDD VSS / aib_dlycell_no_flop
XCELL_43 bk<43> b<43> a<42> a<43> b<42> VDD VSS / aib_dlycell_no_flop
XCELL_42 bk<42> b<42> a<41> a<42> b<41> VDD VSS / aib_dlycell_no_flop
XCELL_41 bk<41> b<41> a<40> a<41> b<40> VDD VSS / aib_dlycell_no_flop
XCELL_40 bk<40> b<40> a<39> a<40> b<39> VDD VSS / aib_dlycell_no_flop
XCELL_39 bk<39> b<39> a<38> a<39> b<38> VDD VSS / aib_dlycell_no_flop
XCELL_38 bk<38> b<38> a<37> a<38> b<37> VDD VSS / aib_dlycell_no_flop
XCELL_37 bk<37> b<37> a<36> a<37> b<36> VDD VSS / aib_dlycell_no_flop
XCELL_36 bk<36> b<36> a<35> a<36> b<35> VDD VSS / aib_dlycell_no_flop
XCELL_35 bk<35> b<35> a<34> a<35> b<34> VDD VSS / aib_dlycell_no_flop
XCELL_34 bk<34> b<34> a<33> a<34> b<33> VDD VSS / aib_dlycell_no_flop
XCELL_33 bk<33> b<33> a<32> a<33> b<32> VDD VSS / aib_dlycell_no_flop
XCELL_32 bk<32> b<32> a<31> a<32> b<31> VDD VSS / aib_dlycell_no_flop
XCELL_31 bk<31> b<31> a<30> a<31> b<30> VDD VSS / aib_dlycell_no_flop
XCELL_30 bk<30> b<30> a<29> a<30> b<29> VDD VSS / aib_dlycell_no_flop
XCELL_29 bk<29> b<29> a<28> a<29> b<28> VDD VSS / aib_dlycell_no_flop
XCELL_28 bk<28> b<28> a<27> a<28> b<27> VDD VSS / aib_dlycell_no_flop
XCELL_27 bk<27> b<27> a<26> a<27> b<26> VDD VSS / aib_dlycell_no_flop
XCELL_26 bk<26> b<26> a<25> a<26> b<25> VDD VSS / aib_dlycell_no_flop
XCELL_25 bk<25> b<25> a<24> a<25> b<24> VDD VSS / aib_dlycell_no_flop
XCELL_24 bk<24> b<24> a<23> a<24> b<23> VDD VSS / aib_dlycell_no_flop
XCELL_23 bk<23> b<23> a<22> a<23> b<22> VDD VSS / aib_dlycell_no_flop
XCELL_22 bk<22> b<22> a<21> a<22> b<21> VDD VSS / aib_dlycell_no_flop
XCELL_21 bk<21> b<21> a<20> a<21> b<20> VDD VSS / aib_dlycell_no_flop
XCELL_20 bk<20> b<20> a<19> a<20> b<19> VDD VSS / aib_dlycell_no_flop
XCELL_19 bk<19> b<19> a<18> a<19> b<18> VDD VSS / aib_dlycell_no_flop
XCELL_18 bk<18> b<18> a<17> a<18> b<17> VDD VSS / aib_dlycell_no_flop
XCELL_17 bk<17> b<17> a<16> a<17> b<16> VDD VSS / aib_dlycell_no_flop
XCELL_16 bk<16> b<16> a<15> a<16> b<15> VDD VSS / aib_dlycell_no_flop
XCELL_15 bk<15> b<15> a<14> a<15> b<14> VDD VSS / aib_dlycell_no_flop
XCELL_14 bk<14> b<14> a<13> a<14> b<13> VDD VSS / aib_dlycell_no_flop
XCELL_13 bk<13> b<13> a<12> a<13> b<12> VDD VSS / aib_dlycell_no_flop
XCELL_12 bk<12> b<12> a<11> a<12> b<11> VDD VSS / aib_dlycell_no_flop
XCELL_11 bk<11> b<11> a<10> a<11> b<10> VDD VSS / aib_dlycell_no_flop
XCELL_10 bk<10> b<10> a<9> a<10> b<9> VDD VSS / aib_dlycell_no_flop
XCELL_9 bk<9> b<9> a<8> a<9> b<8> VDD VSS / aib_dlycell_no_flop
XCELL_8 bk<8> b<8> a<7> a<8> b<7> VDD VSS / aib_dlycell_no_flop
XCELL_7 bk<7> b<7> a<6> a<7> b<6> VDD VSS / aib_dlycell_no_flop
XCELL_6 bk<6> b<6> a<5> a<6> b<5> VDD VSS / aib_dlycell_no_flop
XCELL_5 bk<5> b<5> a<4> a<5> b<4> VDD VSS / aib_dlycell_no_flop
XCELL_4 bk<4> b<4> a<3> a<4> b<3> VDD VSS / aib_dlycell_no_flop
XCELL_3 bk<3> b<3> a<2> a<3> b<2> VDD VSS / aib_dlycell_no_flop
XCELL_2 bk<2> b<2> a<1> a<2> b<1> VDD VSS / aib_dlycell_no_flop
XCELL_1 bk<1> b<1> a<0> a<1> b<0> VDD VSS / aib_dlycell_no_flop
XCELL_0 bk<0> b<0> dlyin a<0> dlyout VDD VSS / aib_dlycell_no_flop
XDUM_1 VSS VSS VSS NC_co<1> NC_out<1> VDD VSS / aib_dlycell_no_flop_1
XDUM_0 VSS VSS VSS NC_co<0> NC_out<0> VDD VSS / aib_dlycell_no_flop_1
.ENDS
