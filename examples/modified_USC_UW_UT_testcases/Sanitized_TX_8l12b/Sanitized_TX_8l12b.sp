************************************************************************
* auCdl Netlist:
*
* Library Name:  AP_SerDes
* Top Cell Name: TX_8l12b
* View Name:     schematic
* Netlisted on:  Apr 12 16:58:00 2019
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
* Library Name: AP_SerDes
* Cell Name:    Bias_v2
* View Name:    schematic
************************************************************************

.SUBCKT Bias_v2 AVDD AVSS CALIN1_3_ CALIN1_2_ CALIN1_1_ CALIN1_0_ CALIN3_3_
+ CALIN3_2_ CALIN3_1_ CALIN3_0_ CALIN5_3_ CALIN5_2_ CALIN5_1_ CALIN5_0_
+ CALIN7_3_ CALIN7_2_ CALIN7_1_ CALIN7_0_ CALIP1_3_ CALIP1_2_ CALIP1_1_
+ CALIP1_0_ CALIP3_3_ CALIP3_2_ CALIP3_1_ CALIP3_0_ CALIP5_3_ CALIP5_2_
+ CALIP5_1_ CALIP5_0_ CALIP7_3_ CALIP7_2_ CALIP7_1_ CALIP7_0_ Ibg In_1m In_3m
+ In_5m In_7m Ip_1m Ip_3m Ip_5m Ip_7m
*.PININFO CALIN1_3_:I CALIN1_2_:I CALIN1_1_:I CALIN1_0_:I CALIN3_3_:I
*.PININFO CALIN3_2_:I CALIN3_1_:I CALIN3_0_:I CALIN5_3_:I CALIN5_2_:I
*.PININFO CALIN5_1_:I CALIN5_0_:I CALIN7_3_:I CALIN7_2_:I CALIN7_1_:I
*.PININFO CALIN7_0_:I CALIP1_3_:I CALIP1_2_:I CALIP1_1_:I CALIP1_0_:I
*.PININFO CALIP3_3_:I CALIP3_2_:I CALIP3_1_:I CALIP3_0_:I CALIP5_3_:I
*.PININFO CALIP5_2_:I CALIP5_1_:I CALIP5_0_:I CALIP7_3_:I CALIP7_2_:I
*.PININFO CALIP7_1_:I CALIP7_0_:I AVDD:B AVSS:B Ibg:B In_1m:B In_3m:B In_5m:B
*.PININFO In_7m:B Ip_1m:B Ip_3m:B Ip_5m:B Ip_7m:B
MM24<19> In_1m net0159 net0136_0_ AVSS nch l=LA w=w3
MM24<18> In_1m net0159 net0136_1_ AVSS nch l=LA w=w3
MM24<17> In_1m net0159 net0136_2_ AVSS nch l=LA w=w3
MM24<16> In_1m net0159 net0136_3_ AVSS nch l=LA w=w3
MM24<15> In_1m net0159 net0136_4_ AVSS nch l=LA w=w3
MM24<14> In_1m net0159 net0136_5_ AVSS nch l=LA w=w3
MM24<13> In_1m net0159 net0136_6_ AVSS nch l=LA w=w3
MM24<12> In_1m net0159 net0136_7_ AVSS nch l=LA w=w3
MM24<11> In_1m net0159 net0136_8_ AVSS nch l=LA w=w3
MM24<10> In_1m net0159 net0136_9_ AVSS nch l=LA w=w3
MM29<9> net0184_0_ net0159 AVSS AVSS nch l=LA w=w4
MM29<8> net0184_1_ net0159 AVSS AVSS nch l=LA w=w4
MM29<7> net0184_2_ net0159 AVSS AVSS nch l=LA w=w4
MM29<6> net0184_3_ net0159 AVSS AVSS nch l=LA w=w4
MM27<0> net073 net0159 AVSS AVSS nch l=LA w=w4
MM26<5> net0220_0_ net0159 net0165_0_ AVSS nch l=LA w=w3
MM26<4> net0220_1_ net0159 net0165_1_ AVSS nch l=LA w=w3
MM26<3> net0220_2_ net0159 net0165_2_ AVSS nch l=LA w=w3
MM25<9> net0162_0_ net0159 AVSS AVSS nch l=LA w=w4
MM25<8> net0162_1_ net0159 AVSS AVSS nch l=LA w=w4
MM25<7> net0162_2_ net0159 AVSS AVSS nch l=LA w=w4
MM25<6> net0162_3_ net0159 AVSS AVSS nch l=LA w=w4
MM23<0> net081 net0159 AVSS AVSS nch l=LA w=w4
MM29<5> net0187_0_ net0159 AVSS AVSS nch l=LA w=w4
MM29<4> net0187_1_ net0159 AVSS AVSS nch l=LA w=w4
MM29<3> net0187_2_ net0159 AVSS AVSS nch l=LA w=w4
MM28<0> net0228 net0159 net073 AVSS nch l=LA w=w3
MM24<2> net0232_0_ net0159 net0154_0_ AVSS nch l=LA w=w3
MM24<1> net0232_1_ net0159 net0154_1_ AVSS nch l=LA w=w3
MM28<2> net0200_0_ net0159 net0179_0_ AVSS nch l=LA w=w3
MM28<1> net0200_1_ net0159 net0179_1_ AVSS nch l=LA w=w3
MM95<5> In_5m CALIN5_2_ net0196_0_ AVSS nch l=LD w=w1mn
MM95<4> In_5m CALIN5_2_ net0196_1_ AVSS nch l=LD w=w1mn
MM95<3> In_5m CALIN5_2_ net0196_2_ AVSS nch l=LD w=w1mn
MM24<5> net0227_0_ net0159 net0145_0_ AVSS nch l=LA w=w3
MM24<4> net0227_1_ net0159 net0145_1_ AVSS nch l=LA w=w3
MM24<3> net0227_2_ net0159 net0145_2_ AVSS nch l=LA w=w3
MM23<9> net0140_0_ net0159 AVSS AVSS nch l=LA w=w4
MM23<8> net0140_1_ net0159 AVSS AVSS nch l=LA w=w4
MM23<7> net0140_2_ net0159 AVSS AVSS nch l=LA w=w4
MM23<6> net0140_3_ net0159 AVSS AVSS nch l=LA w=w4
MM27<9> net0173_0_ net0159 AVSS AVSS nch l=LA w=w4
MM27<8> net0173_1_ net0159 AVSS AVSS nch l=LA w=w4
MM27<7> net0173_2_ net0159 AVSS AVSS nch l=LA w=w4
MM27<6> net0173_3_ net0159 AVSS AVSS nch l=LA w=w4
MM25<0> net077 net0159 AVSS AVSS nch l=LA w=w4
MM100<5> In_7m CALIN7_2_ net0210_0_ AVSS nch l=LD w=w1mn
MM100<4> In_7m CALIN7_2_ net0210_1_ AVSS nch l=LD w=w1mn
MM100<3> In_7m CALIN7_2_ net0210_2_ AVSS nch l=LD w=w1mn
MM99<2> In_7m CALIN7_1_ net0214_0_ AVSS nch l=LD w=w1mn
MM99<1> In_7m CALIN7_1_ net0214_1_ AVSS nch l=LD w=w1mn
MM98<0> In_7m CALIN7_0_ net062 AVSS nch l=LD w=w1mn
MM97<0> In_5m CALIN5_0_ net0228 AVSS nch l=LD w=w1mn
MM30<0> net062 net0159 net069 AVSS nch l=LA w=w3
MM23<5> net0145_0_ net0159 AVSS AVSS nch l=LA w=w4
MM23<4> net0145_1_ net0159 AVSS AVSS nch l=LA w=w4
MM23<3> net0145_2_ net0159 AVSS AVSS nch l=LA w=w4
MM96<2> In_5m CALIN5_1_ net0200_0_ AVSS nch l=LD w=w1mn
MM96<1> In_5m CALIN5_1_ net0200_1_ AVSS nch l=LD w=w1mn
MM93<9> In_3m CALIN3_3_ net0178_0_ AVSS nch l=LD w=w1mn
MM93<8> In_3m CALIN3_3_ net0178_1_ AVSS nch l=LD w=w1mn
MM93<7> In_3m CALIN3_3_ net0178_2_ AVSS nch l=LD w=w1mn
MM93<6> In_3m CALIN3_3_ net0178_3_ AVSS nch l=LD w=w1mn
MM94<9> In_5m CALIN5_3_ net0192_0_ AVSS nch l=LD w=w1mn
MM94<8> In_5m CALIN5_3_ net0192_1_ AVSS nch l=LD w=w1mn
MM94<7> In_5m CALIN5_3_ net0192_2_ AVSS nch l=LD w=w1mn
MM94<6> In_5m CALIN5_3_ net0192_3_ AVSS nch l=LD w=w1mn
MM25<5> net0165_0_ net0159 AVSS AVSS nch l=LA w=w4
MM25<4> net0165_1_ net0159 AVSS AVSS nch l=LA w=w4
MM25<3> net0165_2_ net0159 AVSS AVSS nch l=LA w=w4
MM74<9> In_1m CALIN1_3_ net0157_0_ AVSS nch l=LD w=w1mn
MM74<8> In_1m CALIN1_3_ net0157_1_ AVSS nch l=LD w=w1mn
MM74<7> In_1m CALIN1_3_ net0157_2_ AVSS nch l=LD w=w1mn
MM74<6> In_1m CALIN1_3_ net0157_3_ AVSS nch l=LD w=w1mn
MM90<0> In_3m CALIN3_0_ net078 AVSS nch l=LD w=w1mn
MM30<19> In_7m net0159 net0182_0_ AVSS nch l=LA w=w3
MM30<18> In_7m net0159 net0182_1_ AVSS nch l=LA w=w3
MM30<17> In_7m net0159 net0182_2_ AVSS nch l=LA w=w3
MM30<16> In_7m net0159 net0182_3_ AVSS nch l=LA w=w3
MM30<15> In_7m net0159 net0182_4_ AVSS nch l=LA w=w3
MM30<14> In_7m net0159 net0182_5_ AVSS nch l=LA w=w3
MM30<13> In_7m net0159 net0182_6_ AVSS nch l=LA w=w3
MM30<12> In_7m net0159 net0182_7_ AVSS nch l=LA w=w3
MM30<11> In_7m net0159 net0182_8_ AVSS nch l=LA w=w3
MM30<10> In_7m net0159 net0182_9_ AVSS nch l=LA w=w3
MM91<2> In_3m CALIN3_1_ net0186_0_ AVSS nch l=LD w=w1mn
MM91<1> In_3m CALIN3_1_ net0186_1_ AVSS nch l=LD w=w1mn
MM30<5> net0210_0_ net0159 net0187_0_ AVSS nch l=LA w=w3
MM30<4> net0210_1_ net0159 net0187_1_ AVSS nch l=LA w=w3
MM30<3> net0210_2_ net0159 net0187_2_ AVSS nch l=LA w=w3
MM28<19> In_5m net0159 net0171_0_ AVSS nch l=LA w=w3
MM28<18> In_5m net0159 net0171_1_ AVSS nch l=LA w=w3
MM28<17> In_5m net0159 net0171_2_ AVSS nch l=LA w=w3
MM28<16> In_5m net0159 net0171_3_ AVSS nch l=LA w=w3
MM28<15> In_5m net0159 net0171_4_ AVSS nch l=LA w=w3
MM28<14> In_5m net0159 net0171_5_ AVSS nch l=LA w=w3
MM28<13> In_5m net0159 net0171_6_ AVSS nch l=LA w=w3
MM28<12> In_5m net0159 net0171_7_ AVSS nch l=LA w=w3
MM28<11> In_5m net0159 net0171_8_ AVSS nch l=LA w=w3
MM28<10> In_5m net0159 net0171_9_ AVSS nch l=LA w=w3
MM28<5> net0196_0_ net0159 net0176_0_ AVSS nch l=LA w=w3
MM28<4> net0196_1_ net0159 net0176_1_ AVSS nch l=LA w=w3
MM28<3> net0196_2_ net0159 net0176_2_ AVSS nch l=LA w=w3
MM26<19> In_3m net0159 net0160_0_ AVSS nch l=LA w=w3
MM26<18> In_3m net0159 net0160_1_ AVSS nch l=LA w=w3
MM26<17> In_3m net0159 net0160_2_ AVSS nch l=LA w=w3
MM26<16> In_3m net0159 net0160_3_ AVSS nch l=LA w=w3
MM26<15> In_3m net0159 net0160_4_ AVSS nch l=LA w=w3
MM26<14> In_3m net0159 net0160_5_ AVSS nch l=LA w=w3
MM26<13> In_3m net0159 net0160_6_ AVSS nch l=LA w=w3
MM26<12> In_3m net0159 net0160_7_ AVSS nch l=LA w=w3
MM26<11> In_3m net0159 net0160_8_ AVSS nch l=LA w=w3
MM26<10> In_3m net0159 net0160_9_ AVSS nch l=LA w=w3
MM92<5> In_3m CALIN3_2_ net0220_0_ AVSS nch l=LD w=w1mn
MM92<4> In_3m CALIN3_2_ net0220_1_ AVSS nch l=LD w=w1mn
MM92<3> In_3m CALIN3_2_ net0220_2_ AVSS nch l=LD w=w1mn
MM29<0> net069 net0159 AVSS AVSS nch l=LA w=w4
MM23<2> net0154_0_ net0159 AVSS AVSS nch l=LA w=w4
MM23<1> net0154_1_ net0159 AVSS AVSS nch l=LA w=w4
MM30<2> net0214_0_ net0159 net0190_0_ AVSS nch l=LA w=w3
MM30<1> net0214_1_ net0159 net0190_1_ AVSS nch l=LA w=w3
MM27<2> net0179_0_ net0159 AVSS AVSS nch l=LA w=w4
MM27<1> net0179_1_ net0159 AVSS AVSS nch l=LA w=w4
MM101<9> In_7m CALIN7_3_ net0206_0_ AVSS nch l=LD w=w1mn
MM101<8> In_7m CALIN7_3_ net0206_1_ AVSS nch l=LD w=w1mn
MM101<7> In_7m CALIN7_3_ net0206_2_ AVSS nch l=LD w=w1mn
MM101<6> In_7m CALIN7_3_ net0206_3_ AVSS nch l=LD w=w1mn
MM26<2> net0186_0_ net0159 net0168_0_ AVSS nch l=LA w=w3
MM26<1> net0186_1_ net0159 net0168_1_ AVSS nch l=LA w=w3
MM27<5> net0176_0_ net0159 AVSS AVSS nch l=LA w=w4
MM27<4> net0176_1_ net0159 AVSS AVSS nch l=LA w=w4
MM27<3> net0176_2_ net0159 AVSS AVSS nch l=LA w=w4
MM26<0> net078 net0159 net077 AVSS nch l=LA w=w3
MM24<0> net0222 net0159 net081 AVSS nch l=LA w=w3
MM102<5> In_1m CALIN1_2_ net0227_0_ AVSS nch l=LD w=w1mn
MM102<4> In_1m CALIN1_2_ net0227_1_ AVSS nch l=LD w=w1mn
MM102<3> In_1m CALIN1_2_ net0227_2_ AVSS nch l=LD w=w1mn
MM25<2> net0168_0_ net0159 AVSS AVSS nch l=LA w=w4
MM25<1> net0168_1_ net0159 AVSS AVSS nch l=LA w=w4
MM104<0> In_1m CALIN1_0_ net0222 AVSS nch l=LD w=w1mn
MM29<2> net0190_0_ net0159 AVSS AVSS nch l=LA w=w4
MM29<1> net0190_1_ net0159 AVSS AVSS nch l=LA w=w4
MM103<2> In_1m CALIN1_1_ net0232_0_ AVSS nch l=LD w=w1mn
MM103<1> In_1m CALIN1_1_ net0232_1_ AVSS nch l=LD w=w1mn
MM30<9> net0206_0_ net0159 net0184_0_ AVSS nch l=LA w=w3
MM30<8> net0206_1_ net0159 net0184_1_ AVSS nch l=LA w=w3
MM30<7> net0206_2_ net0159 net0184_2_ AVSS nch l=LA w=w3
MM30<6> net0206_3_ net0159 net0184_3_ AVSS nch l=LA w=w3
MM28<9> net0192_0_ net0159 net0173_0_ AVSS nch l=LA w=w3
MM28<8> net0192_1_ net0159 net0173_1_ AVSS nch l=LA w=w3
MM28<7> net0192_2_ net0159 net0173_2_ AVSS nch l=LA w=w3
MM28<6> net0192_3_ net0159 net0173_3_ AVSS nch l=LA w=w3
MM29<19> net0182_0_ net0159 AVSS AVSS nch l=LA w=w4
MM29<18> net0182_1_ net0159 AVSS AVSS nch l=LA w=w4
MM29<17> net0182_2_ net0159 AVSS AVSS nch l=LA w=w4
MM29<16> net0182_3_ net0159 AVSS AVSS nch l=LA w=w4
MM29<15> net0182_4_ net0159 AVSS AVSS nch l=LA w=w4
MM29<14> net0182_5_ net0159 AVSS AVSS nch l=LA w=w4
MM29<13> net0182_6_ net0159 AVSS AVSS nch l=LA w=w4
MM29<12> net0182_7_ net0159 AVSS AVSS nch l=LA w=w4
MM29<11> net0182_8_ net0159 AVSS AVSS nch l=LA w=w4
MM29<10> net0182_9_ net0159 AVSS AVSS nch l=LA w=w4
MM26<9> net0178_0_ net0159 net0162_0_ AVSS nch l=LA w=w3
MM26<8> net0178_1_ net0159 net0162_1_ AVSS nch l=LA w=w3
MM26<7> net0178_2_ net0159 net0162_2_ AVSS nch l=LA w=w3
MM26<6> net0178_3_ net0159 net0162_3_ AVSS nch l=LA w=w3
MM27<19> net0171_0_ net0159 AVSS AVSS nch l=LA w=w4
MM27<18> net0171_1_ net0159 AVSS AVSS nch l=LA w=w4
MM27<17> net0171_2_ net0159 AVSS AVSS nch l=LA w=w4
MM27<16> net0171_3_ net0159 AVSS AVSS nch l=LA w=w4
MM27<15> net0171_4_ net0159 AVSS AVSS nch l=LA w=w4
MM27<14> net0171_5_ net0159 AVSS AVSS nch l=LA w=w4
MM27<13> net0171_6_ net0159 AVSS AVSS nch l=LA w=w4
MM27<12> net0171_7_ net0159 AVSS AVSS nch l=LA w=w4
MM27<11> net0171_8_ net0159 AVSS AVSS nch l=LA w=w4
MM27<10> net0171_9_ net0159 AVSS AVSS nch l=LA w=w4
MM24<9> net0157_0_ net0159 net0140_0_ AVSS nch l=LA w=w3
MM24<8> net0157_1_ net0159 net0140_1_ AVSS nch l=LA w=w3
MM24<7> net0157_2_ net0159 net0140_2_ AVSS nch l=LA w=w3
MM24<6> net0157_3_ net0159 net0140_3_ AVSS nch l=LA w=w3
MM25<19> net0160_0_ net0159 AVSS AVSS nch l=LA w=w4
MM25<18> net0160_1_ net0159 AVSS AVSS nch l=LA w=w4
MM25<17> net0160_2_ net0159 AVSS AVSS nch l=LA w=w4
MM25<16> net0160_3_ net0159 AVSS AVSS nch l=LA w=w4
MM25<15> net0160_4_ net0159 AVSS AVSS nch l=LA w=w4
MM25<14> net0160_5_ net0159 AVSS AVSS nch l=LA w=w4
MM25<13> net0160_6_ net0159 AVSS AVSS nch l=LA w=w4
MM25<12> net0160_7_ net0159 AVSS AVSS nch l=LA w=w4
MM25<11> net0160_8_ net0159 AVSS AVSS nch l=LA w=w4
MM25<10> net0160_9_ net0159 AVSS AVSS nch l=LA w=w4
MM13<19> net0159 net0159 net067_0_ AVSS nch l=LA w=w3
MM13<18> net0159 net0159 net067_1_ AVSS nch l=LA w=w3
MM13<17> net0159 net0159 net067_2_ AVSS nch l=LA w=w3
MM13<16> net0159 net0159 net067_3_ AVSS nch l=LA w=w3
MM13<15> net0159 net0159 net067_4_ AVSS nch l=LA w=w3
MM13<14> net0159 net0159 net067_5_ AVSS nch l=LA w=w3
MM13<13> net0159 net0159 net067_6_ AVSS nch l=LA w=w3
MM13<12> net0159 net0159 net067_7_ AVSS nch l=LA w=w3
MM13<11> net0159 net0159 net067_8_ AVSS nch l=LA w=w3
MM13<10> net0159 net0159 net067_9_ AVSS nch l=LA w=w3
MM13<9> net0159 net0159 net067_10_ AVSS nch l=LA w=w3
MM13<8> net0159 net0159 net067_11_ AVSS nch l=LA w=w3
MM13<7> net0159 net0159 net067_12_ AVSS nch l=LA w=w3
MM13<6> net0159 net0159 net067_13_ AVSS nch l=LA w=w3
MM13<5> net0159 net0159 net067_14_ AVSS nch l=LA w=w3
MM13<4> net0159 net0159 net067_15_ AVSS nch l=LA w=w3
MM13<3> net0159 net0159 net067_16_ AVSS nch l=LA w=w3
MM13<2> net0159 net0159 net067_17_ AVSS nch l=LA w=w3
MM13<1> net0159 net0159 net067_18_ AVSS nch l=LA w=w3
MM13<0> net0159 net0159 net067_19_ AVSS nch l=LA w=w3
MM23<19> net0136_0_ net0159 AVSS AVSS nch l=LA w=w4
MM23<18> net0136_1_ net0159 AVSS AVSS nch l=LA w=w4
MM23<17> net0136_2_ net0159 AVSS AVSS nch l=LA w=w4
MM23<16> net0136_3_ net0159 AVSS AVSS nch l=LA w=w4
MM23<15> net0136_4_ net0159 AVSS AVSS nch l=LA w=w4
MM23<14> net0136_5_ net0159 AVSS AVSS nch l=LA w=w4
MM23<13> net0136_6_ net0159 AVSS AVSS nch l=LA w=w4
MM23<12> net0136_7_ net0159 AVSS AVSS nch l=LA w=w4
MM23<11> net0136_8_ net0159 AVSS AVSS nch l=LA w=w4
MM23<10> net0136_9_ net0159 AVSS AVSS nch l=LA w=w4
MM14<19> net067_0_ net0159 AVSS AVSS nch l=LA w=w4
MM14<18> net067_1_ net0159 AVSS AVSS nch l=LA w=w4
MM14<17> net067_2_ net0159 AVSS AVSS nch l=LA w=w4
MM14<16> net067_3_ net0159 AVSS AVSS nch l=LA w=w4
MM14<15> net067_4_ net0159 AVSS AVSS nch l=LA w=w4
MM14<14> net067_5_ net0159 AVSS AVSS nch l=LA w=w4
MM14<13> net067_6_ net0159 AVSS AVSS nch l=LA w=w4
MM14<12> net067_7_ net0159 AVSS AVSS nch l=LA w=w4
MM14<11> net067_8_ net0159 AVSS AVSS nch l=LA w=w4
MM14<10> net067_9_ net0159 AVSS AVSS nch l=LA w=w4
MM14<9> net067_10_ net0159 AVSS AVSS nch l=LA w=w4
MM14<8> net067_11_ net0159 AVSS AVSS nch l=LA w=w4
MM14<7> net067_12_ net0159 AVSS AVSS nch l=LA w=w4
MM14<6> net067_13_ net0159 AVSS AVSS nch l=LA w=w4
MM14<5> net067_14_ net0159 AVSS AVSS nch l=LA w=w4
MM14<4> net067_15_ net0159 AVSS AVSS nch l=LA w=w4
MM14<3> net067_16_ net0159 AVSS AVSS nch l=LA w=w4
MM14<2> net067_17_ net0159 AVSS AVSS nch l=LA w=w4
MM14<1> net067_18_ net0159 AVSS AVSS nch l=LA w=w4
MM14<0> net067_19_ net0159 AVSS AVSS nch l=LA w=w4
MM4 net011 Ibg AVSS AVSS nch l=LE w=w
MM3 Ibg Ibg AVSS AVSS nch l=LE w=w
MM33<9> net0163_0_ net011 net089_0_ AVDD pch l=LA w=w2p
MM33<8> net0163_1_ net011 net089_1_ AVDD pch l=LA w=w2p
MM33<7> net0163_2_ net011 net089_2_ AVDD pch l=LA w=w2p
MM33<6> net0163_3_ net011 net089_3_ AVDD pch l=LA w=w2p
MM82<2> Ip_5m CALIP5_1_ net0180_0_ AVDD pch l=LB w=w1m
MM82<1> Ip_5m CALIP5_1_ net0180_1_ AVDD pch l=LB w=w1m
MM31<0> net0107 net011 AVDD AVDD pch l=LA w=w3p
MM33<2> net0169_0_ net011 net091_0_ AVDD pch l=LA w=w2p
MM33<1> net0169_1_ net011 net091_1_ AVDD pch l=LA w=w2p
MM86<5> Ip_7m CALIP7_2_ net0188_0_ AVDD pch l=LB w=w1m
MM86<4> Ip_7m CALIP7_2_ net0188_1_ AVDD pch l=LB w=w1m
MM86<3> Ip_7m CALIP7_2_ net0188_2_ AVDD pch l=LB w=w1m
MM85<2> Ip_7m CALIP7_1_ net0191_0_ AVDD pch l=LB w=w1m
MM85<1> Ip_7m CALIP7_1_ net0191_1_ AVDD pch l=LB w=w1m
MM84<0> Ip_7m CALIP7_0_ net057 AVDD pch l=LB w=w1m
MM83<0> Ip_5m CALIP5_0_ net0195 AVDD pch l=LB w=w1m
MM38<0> net041 net011 AVDD AVDD pch l=LA w=w3p
MM31<5> net085_0_ net011 AVDD AVDD pch l=LA w=w3p
MM31<4> net085_1_ net011 AVDD AVDD pch l=LA w=w3p
MM31<3> net085_2_ net011 AVDD AVDD pch l=LA w=w3p
MM37<2> net0191_0_ net011 net0101_0_ AVDD pch l=LA w=w2p
MM37<1> net0191_1_ net011 net0101_1_ AVDD pch l=LA w=w2p
MM36<5> net0177_0_ net011 net096_0_ AVDD pch l=LA w=w2p
MM36<4> net0177_1_ net011 net096_1_ AVDD pch l=LA w=w2p
MM36<3> net0177_2_ net011 net096_2_ AVDD pch l=LA w=w2p
MM87<9> Ip_7m CALIP7_3_ net0185_0_ AVDD pch l=LB w=w1m
MM87<8> Ip_7m CALIP7_3_ net0185_1_ AVDD pch l=LB w=w1m
MM87<7> Ip_7m CALIP7_3_ net0185_2_ AVDD pch l=LB w=w1m
MM87<6> Ip_7m CALIP7_3_ net0185_3_ AVDD pch l=LB w=w1m
MM32<2> net0113_0_ net011 net086_0_ AVDD pch l=LA w=w2p
MM32<1> net0113_1_ net011 net086_1_ AVDD pch l=LA w=w2p
MM81<5> Ip_5m CALIP5_2_ net0177_0_ AVDD pch l=LB w=w1m
MM81<4> Ip_5m CALIP5_2_ net0177_1_ AVDD pch l=LB w=w1m
MM81<3> Ip_5m CALIP5_2_ net0177_2_ AVDD pch l=LB w=w1m
MM80<9> Ip_5m CALIP5_3_ net0174_0_ AVDD pch l=LB w=w1m
MM80<8> Ip_5m CALIP5_3_ net0174_1_ AVDD pch l=LB w=w1m
MM80<7> Ip_5m CALIP5_3_ net0174_2_ AVDD pch l=LB w=w1m
MM80<6> Ip_5m CALIP5_3_ net0174_3_ AVDD pch l=LB w=w1m
MM79<9> Ip_3m CALIP3_3_ net0163_0_ AVDD pch l=LB w=w1m
MM79<8> Ip_3m CALIP3_3_ net0163_1_ AVDD pch l=LB w=w1m
MM79<7> Ip_3m CALIP3_3_ net0163_2_ AVDD pch l=LB w=w1m
MM79<6> Ip_3m CALIP3_3_ net0163_3_ AVDD pch l=LB w=w1m
MM36<9> net0174_0_ net011 net095_0_ AVDD pch l=LA w=w2p
MM36<8> net0174_1_ net011 net095_1_ AVDD pch l=LA w=w2p
MM36<7> net0174_2_ net011 net095_2_ AVDD pch l=LA w=w2p
MM36<6> net0174_3_ net011 net095_3_ AVDD pch l=LA w=w2p
MM78<5> Ip_3m CALIP3_2_ net0166_0_ AVDD pch l=LB w=w1m
MM78<4> Ip_3m CALIP3_2_ net0166_1_ AVDD pch l=LB w=w1m
MM78<3> Ip_3m CALIP3_2_ net0166_2_ AVDD pch l=LB w=w1m
MM37<0> net057 net011 net041 AVDD pch l=LA w=w2p
MM32<0> net0117 net011 net0107 AVDD pch l=LA w=w2p
MM35<5> net096_0_ net011 AVDD AVDD pch l=LA w=w3p
MM35<4> net096_1_ net011 AVDD AVDD pch l=LA w=w3p
MM35<3> net096_2_ net011 AVDD AVDD pch l=LA w=w3p
MM33<0> net033 net011 net0105 AVDD pch l=LA w=w2p
MM31<2> net086_0_ net011 AVDD AVDD pch l=LA w=w3p
MM31<1> net086_1_ net011 AVDD AVDD pch l=LA w=w3p
MM36<2> net0180_0_ net011 net097_0_ AVDD pch l=LA w=w2p
MM36<1> net0180_1_ net011 net097_1_ AVDD pch l=LA w=w2p
MM34<2> net091_0_ net011 AVDD AVDD pch l=LA w=w3p
MM34<1> net091_1_ net011 AVDD AVDD pch l=LA w=w3p
MM31<9> net084_0_ net011 AVDD AVDD pch l=LA w=w3p
MM31<8> net084_1_ net011 AVDD AVDD pch l=LA w=w3p
MM31<7> net084_2_ net011 AVDD AVDD pch l=LA w=w3p
MM31<6> net084_3_ net011 AVDD AVDD pch l=LA w=w3p
MM35<2> net097_0_ net011 AVDD AVDD pch l=LA w=w3p
MM35<1> net097_1_ net011 AVDD AVDD pch l=LA w=w3p
MM34<0> net0105 net011 AVDD AVDD pch l=LA w=w3p
MM38<2> net0101_0_ net011 AVDD AVDD pch l=LA w=w3p
MM38<1> net0101_1_ net011 AVDD AVDD pch l=LA w=w3p
MM32<5> net0125_0_ net011 net085_0_ AVDD pch l=LA w=w2p
MM32<4> net0125_1_ net011 net085_1_ AVDD pch l=LA w=w2p
MM32<3> net0125_2_ net011 net085_2_ AVDD pch l=LA w=w2p
MM37<5> net0188_0_ net011 net0100_0_ AVDD pch l=LA w=w2p
MM37<4> net0188_1_ net011 net0100_1_ AVDD pch l=LA w=w2p
MM37<3> net0188_2_ net011 net0100_2_ AVDD pch l=LA w=w2p
MM35<0> net0106 net011 AVDD AVDD pch l=LA w=w3p
MM33<5> net0166_0_ net011 net090_0_ AVDD pch l=LA w=w2p
MM33<4> net0166_1_ net011 net090_1_ AVDD pch l=LA w=w2p
MM33<3> net0166_2_ net011 net090_2_ AVDD pch l=LA w=w2p
MM32<9> net0124_0_ net011 net084_0_ AVDD pch l=LA w=w2p
MM32<8> net0124_1_ net011 net084_1_ AVDD pch l=LA w=w2p
MM32<7> net0124_2_ net011 net084_2_ AVDD pch l=LA w=w2p
MM32<6> net0124_3_ net011 net084_3_ AVDD pch l=LA w=w2p
MM35<19> net093_0_ net011 AVDD AVDD pch l=LA w=w3p
MM35<18> net093_1_ net011 AVDD AVDD pch l=LA w=w3p
MM35<17> net093_2_ net011 AVDD AVDD pch l=LA w=w3p
MM35<16> net093_3_ net011 AVDD AVDD pch l=LA w=w3p
MM35<15> net093_4_ net011 AVDD AVDD pch l=LA w=w3p
MM35<14> net093_5_ net011 AVDD AVDD pch l=LA w=w3p
MM35<13> net093_6_ net011 AVDD AVDD pch l=LA w=w3p
MM35<12> net093_7_ net011 AVDD AVDD pch l=LA w=w3p
MM35<11> net093_8_ net011 AVDD AVDD pch l=LA w=w3p
MM35<10> net093_9_ net011 AVDD AVDD pch l=LA w=w3p
MM31<19> net083_0_ net011 AVDD AVDD pch l=LA w=w3p
MM31<18> net083_1_ net011 AVDD AVDD pch l=LA w=w3p
MM31<17> net083_2_ net011 AVDD AVDD pch l=LA w=w3p
MM31<16> net083_3_ net011 AVDD AVDD pch l=LA w=w3p
MM31<15> net083_4_ net011 AVDD AVDD pch l=LA w=w3p
MM31<14> net083_5_ net011 AVDD AVDD pch l=LA w=w3p
MM31<13> net083_6_ net011 AVDD AVDD pch l=LA w=w3p
MM31<12> net083_7_ net011 AVDD AVDD pch l=LA w=w3p
MM31<11> net083_8_ net011 AVDD AVDD pch l=LA w=w3p
MM31<10> net083_9_ net011 AVDD AVDD pch l=LA w=w3p
MM72<9> Ip_1m CALIP1_3_ net0124_0_ AVDD pch l=LB w=w1m
MM72<8> Ip_1m CALIP1_3_ net0124_1_ AVDD pch l=LB w=w1m
MM72<7> Ip_1m CALIP1_3_ net0124_2_ AVDD pch l=LB w=w1m
MM72<6> Ip_1m CALIP1_3_ net0124_3_ AVDD pch l=LB w=w1m
MM76<0> Ip_3m CALIP3_0_ net033 AVDD pch l=LB w=w1m
MM72<0> Ip_1m CALIP1_0_ net0117 AVDD pch l=LB w=w1m
MM72<2> Ip_1m CALIP1_1_ net0113_0_ AVDD pch l=LB w=w1m
MM72<1> Ip_1m CALIP1_1_ net0113_1_ AVDD pch l=LB w=w1m
MM72<5> Ip_1m CALIP1_2_ net0125_0_ AVDD pch l=LB w=w1m
MM72<4> Ip_1m CALIP1_2_ net0125_1_ AVDD pch l=LB w=w1m
MM72<3> Ip_1m CALIP1_2_ net0125_2_ AVDD pch l=LB w=w1m
MM38<19> net098_0_ net011 AVDD AVDD pch l=LA w=w3p
MM38<18> net098_1_ net011 AVDD AVDD pch l=LA w=w3p
MM38<17> net098_2_ net011 AVDD AVDD pch l=LA w=w3p
MM38<16> net098_3_ net011 AVDD AVDD pch l=LA w=w3p
MM38<15> net098_4_ net011 AVDD AVDD pch l=LA w=w3p
MM38<14> net098_5_ net011 AVDD AVDD pch l=LA w=w3p
MM38<13> net098_6_ net011 AVDD AVDD pch l=LA w=w3p
MM38<12> net098_7_ net011 AVDD AVDD pch l=LA w=w3p
MM38<11> net098_8_ net011 AVDD AVDD pch l=LA w=w3p
MM38<10> net098_9_ net011 AVDD AVDD pch l=LA w=w3p
MM77<2> Ip_3m CALIP3_1_ net0169_0_ AVDD pch l=LB w=w1m
MM77<1> Ip_3m CALIP3_1_ net0169_1_ AVDD pch l=LB w=w1m
MM37<9> net0185_0_ net011 net099_0_ AVDD pch l=LA w=w2p
MM37<8> net0185_1_ net011 net099_1_ AVDD pch l=LA w=w2p
MM37<7> net0185_2_ net011 net099_2_ AVDD pch l=LA w=w2p
MM37<6> net0185_3_ net011 net099_3_ AVDD pch l=LA w=w2p
MM36<0> net0195 net011 net0106 AVDD pch l=LA w=w2p
MM38<5> net0100_0_ net011 AVDD AVDD pch l=LA w=w3p
MM38<4> net0100_1_ net011 AVDD AVDD pch l=LA w=w3p
MM38<3> net0100_2_ net011 AVDD AVDD pch l=LA w=w3p
MM34<19> net088_0_ net011 AVDD AVDD pch l=LA w=w3p
MM34<18> net088_1_ net011 AVDD AVDD pch l=LA w=w3p
MM34<17> net088_2_ net011 AVDD AVDD pch l=LA w=w3p
MM34<16> net088_3_ net011 AVDD AVDD pch l=LA w=w3p
MM34<15> net088_4_ net011 AVDD AVDD pch l=LA w=w3p
MM34<14> net088_5_ net011 AVDD AVDD pch l=LA w=w3p
MM34<13> net088_6_ net011 AVDD AVDD pch l=LA w=w3p
MM34<12> net088_7_ net011 AVDD AVDD pch l=LA w=w3p
MM34<11> net088_8_ net011 AVDD AVDD pch l=LA w=w3p
MM34<10> net088_9_ net011 AVDD AVDD pch l=LA w=w3p
MM38<9> net099_0_ net011 AVDD AVDD pch l=LA w=w3p
MM38<8> net099_1_ net011 AVDD AVDD pch l=LA w=w3p
MM38<7> net099_2_ net011 AVDD AVDD pch l=LA w=w3p
MM38<6> net099_3_ net011 AVDD AVDD pch l=LA w=w3p
MM37<19> Ip_7m net011 net098_0_ AVDD pch l=LA w=w2p
MM37<18> Ip_7m net011 net098_1_ AVDD pch l=LA w=w2p
MM37<17> Ip_7m net011 net098_2_ AVDD pch l=LA w=w2p
MM37<16> Ip_7m net011 net098_3_ AVDD pch l=LA w=w2p
MM37<15> Ip_7m net011 net098_4_ AVDD pch l=LA w=w2p
MM37<14> Ip_7m net011 net098_5_ AVDD pch l=LA w=w2p
MM37<13> Ip_7m net011 net098_6_ AVDD pch l=LA w=w2p
MM37<12> Ip_7m net011 net098_7_ AVDD pch l=LA w=w2p
MM37<11> Ip_7m net011 net098_8_ AVDD pch l=LA w=w2p
MM37<10> Ip_7m net011 net098_9_ AVDD pch l=LA w=w2p
MM35<9> net095_0_ net011 AVDD AVDD pch l=LA w=w3p
MM35<8> net095_1_ net011 AVDD AVDD pch l=LA w=w3p
MM35<7> net095_2_ net011 AVDD AVDD pch l=LA w=w3p
MM35<6> net095_3_ net011 AVDD AVDD pch l=LA w=w3p
MM34<9> net089_0_ net011 AVDD AVDD pch l=LA w=w3p
MM34<8> net089_1_ net011 AVDD AVDD pch l=LA w=w3p
MM34<7> net089_2_ net011 AVDD AVDD pch l=LA w=w3p
MM34<6> net089_3_ net011 AVDD AVDD pch l=LA w=w3p
MM36<19> Ip_5m net011 net093_0_ AVDD pch l=LA w=w2p
MM36<18> Ip_5m net011 net093_1_ AVDD pch l=LA w=w2p
MM36<17> Ip_5m net011 net093_2_ AVDD pch l=LA w=w2p
MM36<16> Ip_5m net011 net093_3_ AVDD pch l=LA w=w2p
MM36<15> Ip_5m net011 net093_4_ AVDD pch l=LA w=w2p
MM36<14> Ip_5m net011 net093_5_ AVDD pch l=LA w=w2p
MM36<13> Ip_5m net011 net093_6_ AVDD pch l=LA w=w2p
MM36<12> Ip_5m net011 net093_7_ AVDD pch l=LA w=w2p
MM36<11> Ip_5m net011 net093_8_ AVDD pch l=LA w=w2p
MM36<10> Ip_5m net011 net093_9_ AVDD pch l=LA w=w2p
MM33<19> Ip_3m net011 net088_0_ AVDD pch l=LA w=w2p
MM33<18> Ip_3m net011 net088_1_ AVDD pch l=LA w=w2p
MM33<17> Ip_3m net011 net088_2_ AVDD pch l=LA w=w2p
MM33<16> Ip_3m net011 net088_3_ AVDD pch l=LA w=w2p
MM33<15> Ip_3m net011 net088_4_ AVDD pch l=LA w=w2p
MM33<14> Ip_3m net011 net088_5_ AVDD pch l=LA w=w2p
MM33<13> Ip_3m net011 net088_6_ AVDD pch l=LA w=w2p
MM33<12> Ip_3m net011 net088_7_ AVDD pch l=LA w=w2p
MM33<11> Ip_3m net011 net088_8_ AVDD pch l=LA w=w2p
MM33<10> Ip_3m net011 net088_9_ AVDD pch l=LA w=w2p
MM34<5> net090_0_ net011 AVDD AVDD pch l=LA w=w3p
MM34<4> net090_1_ net011 AVDD AVDD pch l=LA w=w3p
MM34<3> net090_2_ net011 AVDD AVDD pch l=LA w=w3p
MM32<19> Ip_1m net011 net083_0_ AVDD pch l=LA w=w2p
MM32<18> Ip_1m net011 net083_1_ AVDD pch l=LA w=w2p
MM32<17> Ip_1m net011 net083_2_ AVDD pch l=LA w=w2p
MM32<16> Ip_1m net011 net083_3_ AVDD pch l=LA w=w2p
MM32<15> Ip_1m net011 net083_4_ AVDD pch l=LA w=w2p
MM32<14> Ip_1m net011 net083_5_ AVDD pch l=LA w=w2p
MM32<13> Ip_1m net011 net083_6_ AVDD pch l=LA w=w2p
MM32<12> Ip_1m net011 net083_7_ AVDD pch l=LA w=w2p
MM32<11> Ip_1m net011 net083_8_ AVDD pch l=LA w=w2p
MM32<10> Ip_1m net011 net083_9_ AVDD pch l=LA w=w2p
MM10<19> net0159 net011 net046_0_ AVDD pch l=LA w=w2p
MM10<18> net0159 net011 net046_1_ AVDD pch l=LA w=w2p
MM10<17> net0159 net011 net046_2_ AVDD pch l=LA w=w2p
MM10<16> net0159 net011 net046_3_ AVDD pch l=LA w=w2p
MM10<15> net0159 net011 net046_4_ AVDD pch l=LA w=w2p
MM10<14> net0159 net011 net046_5_ AVDD pch l=LA w=w2p
MM10<13> net0159 net011 net046_6_ AVDD pch l=LA w=w2p
MM10<12> net0159 net011 net046_7_ AVDD pch l=LA w=w2p
MM10<11> net0159 net011 net046_8_ AVDD pch l=LA w=w2p
MM10<10> net0159 net011 net046_9_ AVDD pch l=LA w=w2p
MM10<9> net0159 net011 net046_10_ AVDD pch l=LA w=w2p
MM10<8> net0159 net011 net046_11_ AVDD pch l=LA w=w2p
MM10<7> net0159 net011 net046_12_ AVDD pch l=LA w=w2p
MM10<6> net0159 net011 net046_13_ AVDD pch l=LA w=w2p
MM10<5> net0159 net011 net046_14_ AVDD pch l=LA w=w2p
MM10<4> net0159 net011 net046_15_ AVDD pch l=LA w=w2p
MM10<3> net0159 net011 net046_16_ AVDD pch l=LA w=w2p
MM10<2> net0159 net011 net046_17_ AVDD pch l=LA w=w2p
MM10<1> net0159 net011 net046_18_ AVDD pch l=LA w=w2p
MM10<0> net0159 net011 net046_19_ AVDD pch l=LA w=w2p
MM7<19> net011 net011 net045_0_ AVDD pch l=LA w=w2p
MM7<18> net011 net011 net045_1_ AVDD pch l=LA w=w2p
MM7<17> net011 net011 net045_2_ AVDD pch l=LA w=w2p
MM7<16> net011 net011 net045_3_ AVDD pch l=LA w=w2p
MM7<15> net011 net011 net045_4_ AVDD pch l=LA w=w2p
MM7<14> net011 net011 net045_5_ AVDD pch l=LA w=w2p
MM7<13> net011 net011 net045_6_ AVDD pch l=LA w=w2p
MM7<12> net011 net011 net045_7_ AVDD pch l=LA w=w2p
MM7<11> net011 net011 net045_8_ AVDD pch l=LA w=w2p
MM7<10> net011 net011 net045_9_ AVDD pch l=LA w=w2p
MM7<9> net011 net011 net045_10_ AVDD pch l=LA w=w2p
MM7<8> net011 net011 net045_11_ AVDD pch l=LA w=w2p
MM7<7> net011 net011 net045_12_ AVDD pch l=LA w=w2p
MM7<6> net011 net011 net045_13_ AVDD pch l=LA w=w2p
MM7<5> net011 net011 net045_14_ AVDD pch l=LA w=w2p
MM7<4> net011 net011 net045_15_ AVDD pch l=LA w=w2p
MM7<3> net011 net011 net045_16_ AVDD pch l=LA w=w2p
MM7<2> net011 net011 net045_17_ AVDD pch l=LA w=w2p
MM7<1> net011 net011 net045_18_ AVDD pch l=LA w=w2p
MM7<0> net011 net011 net045_19_ AVDD pch l=LA w=w2p
MM9<19> net046_0_ net011 AVDD AVDD pch l=LA w=w3p
MM9<18> net046_1_ net011 AVDD AVDD pch l=LA w=w3p
MM9<17> net046_2_ net011 AVDD AVDD pch l=LA w=w3p
MM9<16> net046_3_ net011 AVDD AVDD pch l=LA w=w3p
MM9<15> net046_4_ net011 AVDD AVDD pch l=LA w=w3p
MM9<14> net046_5_ net011 AVDD AVDD pch l=LA w=w3p
MM9<13> net046_6_ net011 AVDD AVDD pch l=LA w=w3p
MM9<12> net046_7_ net011 AVDD AVDD pch l=LA w=w3p
MM9<11> net046_8_ net011 AVDD AVDD pch l=LA w=w3p
MM9<10> net046_9_ net011 AVDD AVDD pch l=LA w=w3p
MM9<9> net046_10_ net011 AVDD AVDD pch l=LA w=w3p
MM9<8> net046_11_ net011 AVDD AVDD pch l=LA w=w3p
MM9<7> net046_12_ net011 AVDD AVDD pch l=LA w=w3p
MM9<6> net046_13_ net011 AVDD AVDD pch l=LA w=w3p
MM9<5> net046_14_ net011 AVDD AVDD pch l=LA w=w3p
MM9<4> net046_15_ net011 AVDD AVDD pch l=LA w=w3p
MM9<3> net046_16_ net011 AVDD AVDD pch l=LA w=w3p
MM9<2> net046_17_ net011 AVDD AVDD pch l=LA w=w3p
MM9<1> net046_18_ net011 AVDD AVDD pch l=LA w=w3p
MM9<0> net046_19_ net011 AVDD AVDD pch l=LA w=w3p
MM8<19> net045_0_ net011 AVDD AVDD pch l=LA w=w3p
MM8<18> net045_1_ net011 AVDD AVDD pch l=LA w=w3p
MM8<17> net045_2_ net011 AVDD AVDD pch l=LA w=w3p
MM8<16> net045_3_ net011 AVDD AVDD pch l=LA w=w3p
MM8<15> net045_4_ net011 AVDD AVDD pch l=LA w=w3p
MM8<14> net045_5_ net011 AVDD AVDD pch l=LA w=w3p
MM8<13> net045_6_ net011 AVDD AVDD pch l=LA w=w3p
MM8<12> net045_7_ net011 AVDD AVDD pch l=LA w=w3p
MM8<11> net045_8_ net011 AVDD AVDD pch l=LA w=w3p
MM8<10> net045_9_ net011 AVDD AVDD pch l=LA w=w3p
MM8<9> net045_10_ net011 AVDD AVDD pch l=LA w=w3p
MM8<8> net045_11_ net011 AVDD AVDD pch l=LA w=w3p
MM8<7> net045_12_ net011 AVDD AVDD pch l=LA w=w3p
MM8<6> net045_13_ net011 AVDD AVDD pch l=LA w=w3p
MM8<5> net045_14_ net011 AVDD AVDD pch l=LA w=w3p
MM8<4> net045_15_ net011 AVDD AVDD pch l=LA w=w3p
MM8<3> net045_16_ net011 AVDD AVDD pch l=LA w=w3p
MM8<2> net045_17_ net011 AVDD AVDD pch l=LA w=w3p
MM8<1> net045_18_ net011 AVDD AVDD pch l=LA w=w3p
MM8<0> net045_19_ net011 AVDD AVDD pch l=LA w=w3p
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    ND2D1LVT
* View Name:    schematic
************************************************************************

.SUBCKT ND2D1LVT A1 A2 VDD VSS ZN
*.PININFO A1:I A2:I ZN:O VDD:B VSS:B
MMI1-M_u3 ZN A1 net1 VSS lvtnfet l=LF w=WE
MMI1-M_u4 net1 A2 VSS VSS lvtnfet l=LF w=WE
MMI1-M_u1 ZN A1 VDD VDD lvtpfet l=LF w=WF
MMI1-M_u2 ZN A2 VDD VDD lvtpfet l=LF w=WF
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    INVD4LVT
* View Name:    schematic
************************************************************************

.SUBCKT INVD4LVT I VDD VSS ZN
*.PININFO I:I ZN:O VDD:B VSS:B
MMU1_0-M_u2 ZN I VSS VSS lvtnfet l=LF w=WE
MMU1_3-M_u2 ZN I VSS VSS lvtnfet l=LF w=WE
MMU1_1-M_u2 ZN I VSS VSS lvtnfet l=LF w=WE
MMU1_2-M_u2 ZN I VSS VSS lvtnfet l=LF w=WE
MMU1_0-M_u3 ZN I VDD VDD lvtpfet l=LF w=WF
MMU1_1-M_u3 ZN I VDD VDD lvtpfet l=LF w=WF
MMU1_3-M_u3 ZN I VDD VDD lvtpfet l=LF w=WF
MMU1_2-M_u3 ZN I VDD VDD lvtpfet l=LF w=WF
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    INVD2LVT
* View Name:    schematic
************************************************************************

.SUBCKT INVD2LVT I VDD VSS ZN
*.PININFO I:I ZN:O VDD:B VSS:B
MMU1_0-M_u2 ZN I VSS VSS lvtnfet l=LF w=WE
MMU1_1-M_u2 ZN I VSS VSS lvtnfet l=LF w=WE
MMU1_0-M_u3 ZN I VDD VDD lvtpfet l=LF w=WF
MMU1_1-M_u3 ZN I VDD VDD lvtpfet l=LF w=WF
.ENDS

************************************************************************
* Library Name: AP_SerDes
* Cell Name:    mux
* View Name:    schematic
************************************************************************

.SUBCKT mux DVDD DVSS IN0 IN1 OUT S SZ
*.PININFO IN0:I IN1:I S:I SZ:I OUT:O DVDD:B DVSS:B
XI3 S IN1 DVDD DVSS net8 ND2D1LVT
XI4 SZ IN0 DVDD DVSS net7 ND2D1LVT
XI5 net8 net7 DVDD DVSS net08 ND2D1LVT
XI7 net07 DVDD DVSS OUT INVD4LVT
XI6 net08 DVDD DVSS net07 INVD2LVT
.ENDS

************************************************************************
* Library Name: AP_SerDes
* Cell Name:    MUX2to1_dig
* View Name:    schematic
************************************************************************

.SUBCKT MUX2to1_dig A_7_ A_6_ A_5_ A_4_ A_3_ A_2_ A_1_ A_0_ AE_7_ AE_6_ AE_5_
+ AE_4_ AE_3_ AE_2_ AE_1_ AE_0_ AO_7_ AO_6_ AO_5_ AO_4_ AO_3_ AO_2_ AO_1_
+ AO_0_ B_7_ B_6_ B_5_ B_4_ B_3_ B_2_ B_1_ B_0_ BE_7_ BE_6_ BE_5_ BE_4_ BE_3_
+ BE_2_ BE_1_ BE_0_ BO_7_ BO_6_ BO_5_ BO_4_ BO_3_ BO_2_ BO_1_ BO_0_ C_7_ C_6_
+ C_5_ C_4_ C_3_ C_2_ C_1_ C_0_ CE_7_ CE_6_ CE_5_ CE_4_ CE_3_ CE_2_ CE_1_
+ CE_0_ CLKE CLKO CO_7_ CO_6_ CO_5_ CO_4_ CO_3_ CO_2_ CO_1_ CO_0_ D_7_ D_6_
+ D_5_ D_4_ D_3_ D_2_ D_1_ D_0_ DE_7_ DE_6_ DE_5_ DE_4_ DE_3_ DE_2_ DE_1_
+ DE_0_ DO_7_ DO_6_ DO_5_ DO_4_ DO_3_ DO_2_ DO_1_ DO_0_ DVDD DVSS E_7_ E_6_
+ E_5_ E_4_ E_3_ E_2_ E_1_ E_0_ EE_7_ EE_6_ EE_5_ EE_4_ EE_3_ EE_2_ EE_1_
+ EE_0_ EO_7_ EO_6_ EO_5_ EO_4_ EO_3_ EO_2_ EO_1_ EO_0_ F_7_ F_6_ F_5_ F_4_
+ F_3_ F_2_ F_1_ F_0_ FE_7_ FE_6_ FE_5_ FE_4_ FE_3_ FE_2_ FE_1_ FE_0_ FO_7_
+ FO_6_ FO_5_ FO_4_ FO_3_ FO_2_ FO_1_ FO_0_ G_7_ G_6_ G_5_ G_4_ G_3_ G_2_ G_1_
+ G_0_ GE_7_ GE_6_ GE_5_ GE_4_ GE_3_ GE_2_ GE_1_ GE_0_ GO_7_ GO_6_ GO_5_ GO_4_
+ GO_3_ GO_2_ GO_1_ GO_0_ H_7_ H_6_ H_5_ H_4_ H_3_ H_2_ H_1_ H_0_ HE_7_ HE_6_
+ HE_5_ HE_4_ HE_3_ HE_2_ HE_1_ HE_0_ HO_7_ HO_6_ HO_5_ HO_4_ HO_3_ HO_2_
+ HO_1_ HO_0_
*.PININFO AE_7_:I AE_6_:I AE_5_:I AE_4_:I AE_3_:I AE_2_:I AE_1_:I AE_0_:I
*.PININFO AO_7_:I AO_6_:I AO_5_:I AO_4_:I AO_3_:I AO_2_:I AO_1_:I AO_0_:I
*.PININFO BE_7_:I BE_6_:I BE_5_:I BE_4_:I BE_3_:I BE_2_:I BE_1_:I BE_0_:I
*.PININFO BO_7_:I BO_6_:I BO_5_:I BO_4_:I BO_3_:I BO_2_:I BO_1_:I BO_0_:I
*.PININFO CE_7_:I CE_6_:I CE_5_:I CE_4_:I CE_3_:I CE_2_:I CE_1_:I CE_0_:I
*.PININFO CLKE:I CLKO:I CO_7_:I CO_6_:I CO_5_:I CO_4_:I CO_3_:I CO_2_:I
*.PININFO CO_1_:I CO_0_:I DE_7_:I DE_6_:I DE_5_:I DE_4_:I DE_3_:I DE_2_:I
*.PININFO DE_1_:I DE_0_:I DO_7_:I DO_6_:I DO_5_:I DO_4_:I DO_3_:I DO_2_:I
*.PININFO DO_1_:I DO_0_:I EE_7_:I EE_6_:I EE_5_:I EE_4_:I EE_3_:I EE_2_:I
*.PININFO EE_1_:I EE_0_:I EO_7_:I EO_6_:I EO_5_:I EO_4_:I EO_3_:I EO_2_:I
*.PININFO EO_1_:I EO_0_:I FE_7_:I FE_6_:I FE_5_:I FE_4_:I FE_3_:I FE_2_:I
*.PININFO FE_1_:I FE_0_:I FO_7_:I FO_6_:I FO_5_:I FO_4_:I FO_3_:I FO_2_:I
*.PININFO FO_1_:I FO_0_:I GE_7_:I GE_6_:I GE_5_:I GE_4_:I GE_3_:I GE_2_:I
*.PININFO GE_1_:I GE_0_:I GO_7_:I GO_6_:I GO_5_:I GO_4_:I GO_3_:I GO_2_:I
*.PININFO GO_1_:I GO_0_:I HE_7_:I HE_6_:I HE_5_:I HE_4_:I HE_3_:I HE_2_:I
*.PININFO HE_1_:I HE_0_:I HO_7_:I HO_6_:I HO_5_:I HO_4_:I HO_3_:I HO_2_:I
*.PININFO HO_1_:I HO_0_:I A_7_:O A_6_:O A_5_:O A_4_:O A_3_:O A_2_:O A_1_:O
*.PININFO A_0_:O B_7_:O B_6_:O B_5_:O B_4_:O B_3_:O B_2_:O B_1_:O B_0_:O
*.PININFO C_7_:O C_6_:O C_5_:O C_4_:O C_3_:O C_2_:O C_1_:O C_0_:O D_7_:O
*.PININFO D_6_:O D_5_:O D_4_:O D_3_:O D_2_:O D_1_:O D_0_:O E_7_:O E_6_:O
*.PININFO E_5_:O E_4_:O E_3_:O E_2_:O E_1_:O E_0_:O F_7_:O F_6_:O F_5_:O
*.PININFO F_4_:O F_3_:O F_2_:O F_1_:O F_0_:O G_7_:O G_6_:O G_5_:O G_4_:O
*.PININFO G_3_:O G_2_:O G_1_:O G_0_:O H_7_:O H_6_:O H_5_:O H_4_:O H_3_:O
*.PININFO H_2_:O H_1_:O H_0_:O DVDD:B DVSS:B
XI8<7> DVDD DVSS AE_7_ AO_7_ A_7_ CLKE CLKO mux
XI8<6> DVDD DVSS AE_6_ AO_6_ A_6_ CLKE CLKO mux
XI8<5> DVDD DVSS AE_5_ AO_5_ A_5_ CLKE CLKO mux
XI8<4> DVDD DVSS AE_4_ AO_4_ A_4_ CLKE CLKO mux
XI8<3> DVDD DVSS AE_3_ AO_3_ A_3_ CLKE CLKO mux
XI8<2> DVDD DVSS AE_2_ AO_2_ A_2_ CLKE CLKO mux
XI8<1> DVDD DVSS AE_1_ AO_1_ A_1_ CLKE CLKO mux
XI8<0> DVDD DVSS AE_0_ AO_0_ A_0_ CLKE CLKO mux
XI15<7> DVDD DVSS HE_7_ HO_7_ H_7_ CLKE CLKO mux
XI15<6> DVDD DVSS HE_6_ HO_6_ H_6_ CLKE CLKO mux
XI15<5> DVDD DVSS HE_5_ HO_5_ H_5_ CLKE CLKO mux
XI15<4> DVDD DVSS HE_4_ HO_4_ H_4_ CLKE CLKO mux
XI15<3> DVDD DVSS HE_3_ HO_3_ H_3_ CLKE CLKO mux
XI15<2> DVDD DVSS HE_2_ HO_2_ H_2_ CLKE CLKO mux
XI15<1> DVDD DVSS HE_1_ HO_1_ H_1_ CLKE CLKO mux
XI15<0> DVDD DVSS HE_0_ HO_0_ H_0_ CLKE CLKO mux
XI14<7> DVDD DVSS GE_7_ GO_7_ G_7_ CLKE CLKO mux
XI14<6> DVDD DVSS GE_6_ GO_6_ G_6_ CLKE CLKO mux
XI14<5> DVDD DVSS GE_5_ GO_5_ G_5_ CLKE CLKO mux
XI14<4> DVDD DVSS GE_4_ GO_4_ G_4_ CLKE CLKO mux
XI14<3> DVDD DVSS GE_3_ GO_3_ G_3_ CLKE CLKO mux
XI14<2> DVDD DVSS GE_2_ GO_2_ G_2_ CLKE CLKO mux
XI14<1> DVDD DVSS GE_1_ GO_1_ G_1_ CLKE CLKO mux
XI14<0> DVDD DVSS GE_0_ GO_0_ G_0_ CLKE CLKO mux
XI13<7> DVDD DVSS FE_7_ FO_7_ F_7_ CLKE CLKO mux
XI13<6> DVDD DVSS FE_6_ FO_6_ F_6_ CLKE CLKO mux
XI13<5> DVDD DVSS FE_5_ FO_5_ F_5_ CLKE CLKO mux
XI13<4> DVDD DVSS FE_4_ FO_4_ F_4_ CLKE CLKO mux
XI13<3> DVDD DVSS FE_3_ FO_3_ F_3_ CLKE CLKO mux
XI13<2> DVDD DVSS FE_2_ FO_2_ F_2_ CLKE CLKO mux
XI13<1> DVDD DVSS FE_1_ FO_1_ F_1_ CLKE CLKO mux
XI13<0> DVDD DVSS FE_0_ FO_0_ F_0_ CLKE CLKO mux
XI12<7> DVDD DVSS EE_7_ EO_7_ E_7_ CLKE CLKO mux
XI12<6> DVDD DVSS EE_6_ EO_6_ E_6_ CLKE CLKO mux
XI12<5> DVDD DVSS EE_5_ EO_5_ E_5_ CLKE CLKO mux
XI12<4> DVDD DVSS EE_4_ EO_4_ E_4_ CLKE CLKO mux
XI12<3> DVDD DVSS EE_3_ EO_3_ E_3_ CLKE CLKO mux
XI12<2> DVDD DVSS EE_2_ EO_2_ E_2_ CLKE CLKO mux
XI12<1> DVDD DVSS EE_1_ EO_1_ E_1_ CLKE CLKO mux
XI12<0> DVDD DVSS EE_0_ EO_0_ E_0_ CLKE CLKO mux
XI11<7> DVDD DVSS DE_7_ DO_7_ D_7_ CLKE CLKO mux
XI11<6> DVDD DVSS DE_6_ DO_6_ D_6_ CLKE CLKO mux
XI11<5> DVDD DVSS DE_5_ DO_5_ D_5_ CLKE CLKO mux
XI11<4> DVDD DVSS DE_4_ DO_4_ D_4_ CLKE CLKO mux
XI11<3> DVDD DVSS DE_3_ DO_3_ D_3_ CLKE CLKO mux
XI11<2> DVDD DVSS DE_2_ DO_2_ D_2_ CLKE CLKO mux
XI11<1> DVDD DVSS DE_1_ DO_1_ D_1_ CLKE CLKO mux
XI11<0> DVDD DVSS DE_0_ DO_0_ D_0_ CLKE CLKO mux
XI10<7> DVDD DVSS CE_7_ CO_7_ C_7_ CLKE CLKO mux
XI10<6> DVDD DVSS CE_6_ CO_6_ C_6_ CLKE CLKO mux
XI10<5> DVDD DVSS CE_5_ CO_5_ C_5_ CLKE CLKO mux
XI10<4> DVDD DVSS CE_4_ CO_4_ C_4_ CLKE CLKO mux
XI10<3> DVDD DVSS CE_3_ CO_3_ C_3_ CLKE CLKO mux
XI10<2> DVDD DVSS CE_2_ CO_2_ C_2_ CLKE CLKO mux
XI10<1> DVDD DVSS CE_1_ CO_1_ C_1_ CLKE CLKO mux
XI10<0> DVDD DVSS CE_0_ CO_0_ C_0_ CLKE CLKO mux
XI9<7> DVDD DVSS BE_7_ BO_7_ B_7_ CLKE CLKO mux
XI9<6> DVDD DVSS BE_6_ BO_6_ B_6_ CLKE CLKO mux
XI9<5> DVDD DVSS BE_5_ BO_5_ B_5_ CLKE CLKO mux
XI9<4> DVDD DVSS BE_4_ BO_4_ B_4_ CLKE CLKO mux
XI9<3> DVDD DVSS BE_3_ BO_3_ B_3_ CLKE CLKO mux
XI9<2> DVDD DVSS BE_2_ BO_2_ B_2_ CLKE CLKO mux
XI9<1> DVDD DVSS BE_1_ BO_1_ B_1_ CLKE CLKO mux
XI9<0> DVDD DVSS BE_0_ BO_0_ B_0_ CLKE CLKO mux
.ENDS

************************************************************************
* Library Name: AP_SerDes
* Cell Name:    CML_Driver_PAM8_woCS_v3
* View Name:    schematic
************************************************************************

.SUBCKT CML_Driver_PAM8_woCS_v3 A_7_ A_6_ A_5_ A_4_ A_3_ A_2_ A_1_ A_0_ AVDD
+ AVSS B_7_ B_6_ B_5_ B_4_ B_3_ B_2_ B_1_ B_0_ C_7_ C_6_ C_5_ C_4_ C_3_ C_2_
+ C_1_ C_0_ D_7_ D_6_ D_5_ D_4_ D_3_ D_2_ D_1_ D_0_ E_7_ E_6_ E_5_ E_4_ E_3_
+ E_2_ E_1_ E_0_ F_7_ F_6_ F_5_ F_4_ F_3_ F_2_ F_1_ F_0_ G_7_ G_6_ G_5_ G_4_
+ G_3_ G_2_ G_1_ G_0_ H_7_ H_6_ H_5_ H_4_ H_3_ H_2_ H_1_ H_0_ In_1m In_3m
+ In_5m In_7m Ip_1m Ip_3m Ip_5m Ip_7m ntx outa outb outc outd oute outf outg
+ outh
*.PININFO A_7_:I A_6_:I A_5_:I A_4_:I A_3_:I A_2_:I A_1_:I A_0_:I B_7_:I
*.PININFO B_6_:I B_5_:I B_4_:I B_3_:I B_2_:I B_1_:I B_0_:I C_7_:I C_6_:I
*.PININFO C_5_:I C_4_:I C_3_:I C_2_:I C_1_:I C_0_:I D_7_:I D_6_:I D_5_:I
*.PININFO D_4_:I D_3_:I D_2_:I D_1_:I D_0_:I E_7_:I E_6_:I E_5_:I E_4_:I
*.PININFO E_3_:I E_2_:I E_1_:I E_0_:I F_7_:I F_6_:I F_5_:I F_4_:I F_3_:I
*.PININFO F_2_:I F_1_:I F_0_:I G_7_:I G_6_:I G_5_:I G_4_:I G_3_:I G_2_:I
*.PININFO G_1_:I G_0_:I H_7_:I H_6_:I H_5_:I H_4_:I H_3_:I H_2_:I H_1_:I
*.PININFO H_0_:I outa:O outb:O outc:O outd:O oute:O outf:O outg:O outh:O
*.PININFO AVDD:B AVSS:B In_1m:B In_3m:B In_5m:B In_7m:B Ip_1m:B Ip_3m:B
*.PININFO Ip_5m:B Ip_7m:B ntx:B
MM56 outa A_0_ In_7m AVSS lvtnfet l=LF w=wnswitch
MM54 outa A_1_ In_5m AVSS lvtnfet l=LF w=wnswitch
MM50 outa A_3_ In_1m AVSS lvtnfet l=LF w=wnswitch
MM52 outa A_2_ In_3m AVSS lvtnfet l=LF w=wnswitch
MM115 outg G_3_ In_1m AVSS lvtnfet l=LF w=wnswitch
MM111 oute E_3_ In_1m AVSS lvtnfet l=LF w=wnswitch
MM97 oute E_2_ In_3m AVSS lvtnfet l=LF w=wnswitch
MM83 oute E_1_ In_5m AVSS lvtnfet l=LF w=wnswitch
MM64 oute E_0_ In_7m AVSS lvtnfet l=LF w=wnswitch
MM113 outf F_3_ In_1m AVSS lvtnfet l=LF w=wnswitch
MM109 outd D_3_ In_1m AVSS lvtnfet l=LF w=wnswitch
MM95 outd D_2_ In_3m AVSS lvtnfet l=LF w=wnswitch
MM81 outd D_1_ In_5m AVSS lvtnfet l=LF w=wnswitch
MM62 outd D_0_ In_7m AVSS lvtnfet l=LF w=wnswitch
MM107 outc C_3_ In_1m AVSS lvtnfet l=LF w=wnswitch
MM93 outc C_2_ In_3m AVSS lvtnfet l=LF w=wnswitch
MM79 outc C_1_ In_5m AVSS lvtnfet l=LF w=wnswitch
MM60 outc C_0_ In_7m AVSS lvtnfet l=LF w=wnswitch
MM101 outg G_2_ In_3m AVSS lvtnfet l=LF w=wnswitch
MM87 outg G_1_ In_5m AVSS lvtnfet l=LF w=wnswitch
MM99 outf F_2_ In_3m AVSS lvtnfet l=LF w=wnswitch
MM105 outb B_3_ In_1m AVSS lvtnfet l=LF w=wnswitch
MM91 outb B_2_ In_3m AVSS lvtnfet l=LF w=wnswitch
MM73 outb B_1_ In_5m AVSS lvtnfet l=LF w=wnswitch
MM58 outb B_0_ In_7m AVSS lvtnfet l=LF w=wnswitch
MM117 outh H_3_ In_1m AVSS lvtnfet l=LF w=wnswitch
MM103 outh H_2_ In_3m AVSS lvtnfet l=LF w=wnswitch
MM85 outf F_1_ In_5m AVSS lvtnfet l=LF w=wnswitch
MM68 outg G_0_ In_7m AVSS lvtnfet l=LF w=wnswitch
MM89 outh H_1_ In_5m AVSS lvtnfet l=LF w=wnswitch
MM70 outh H_0_ In_7m AVSS lvtnfet l=LF w=wnswitch
MM66 outf F_0_ In_7m AVSS lvtnfet l=LF w=wnswitch
MM53 outa A_6_ Ip_5m AVDD lvtpfet l=LF w=wpswitch
MM49 outa A_4_ Ip_1m AVDD lvtpfet l=LF w=wpswitch
MM51 outa A_5_ Ip_3m AVDD lvtpfet l=LF w=wpswitch
MM55 outa A_7_ Ip_7m AVDD lvtpfet l=LF w=wpswitch
MM104 outb B_4_ Ip_1m AVDD lvtpfet l=LF w=wpswitch
MM100 outg G_5_ Ip_3m AVDD lvtpfet l=LF w=wpswitch
MM98 outf F_5_ Ip_3m AVDD lvtpfet l=LF w=wpswitch
MM112 outf F_4_ Ip_1m AVDD lvtpfet l=LF w=wpswitch
MM86 outg G_6_ Ip_5m AVDD lvtpfet l=LF w=wpswitch
MM96 oute E_5_ Ip_3m AVDD lvtpfet l=LF w=wpswitch
MM82 oute E_6_ Ip_5m AVDD lvtpfet l=LF w=wpswitch
MM63 oute E_7_ Ip_7m AVDD lvtpfet l=LF w=wpswitch
MM110 oute E_4_ Ip_1m AVDD lvtpfet l=LF w=wpswitch
MM94 outd D_5_ Ip_3m AVDD lvtpfet l=LF w=wpswitch
MM80 outd D_6_ Ip_5m AVDD lvtpfet l=LF w=wpswitch
MM108 outd D_4_ Ip_1m AVDD lvtpfet l=LF w=wpswitch
MM61 outd D_7_ Ip_7m AVDD lvtpfet l=LF w=wpswitch
MM116 outh H_4_ Ip_1m AVDD lvtpfet l=LF w=wpswitch
MM92 outc C_5_ Ip_3m AVDD lvtpfet l=LF w=wpswitch
MM75 outc C_6_ Ip_5m AVDD lvtpfet l=LF w=wpswitch
MM59 outc C_7_ Ip_7m AVDD lvtpfet l=LF w=wpswitch
MM106 outc C_4_ Ip_1m AVDD lvtpfet l=LF w=wpswitch
MM67 outg G_7_ Ip_7m AVDD lvtpfet l=LF w=wpswitch
MM114 outg G_4_ Ip_1m AVDD lvtpfet l=LF w=wpswitch
MM102 outh H_5_ Ip_3m AVDD lvtpfet l=LF w=wpswitch
MM90 outb B_5_ Ip_3m AVDD lvtpfet l=LF w=wpswitch
MM71 outb B_6_ Ip_5m AVDD lvtpfet l=LF w=wpswitch
MM57 outb B_7_ Ip_7m AVDD lvtpfet l=LF w=wpswitch
MM88 outh H_6_ Ip_5m AVDD lvtpfet l=LF w=wpswitch
MM84 outf F_6_ Ip_5m AVDD lvtpfet l=LF w=wpswitch
MM65 outf F_7_ Ip_7m AVDD lvtpfet l=LF w=wpswitch
MM69 outh H_7_ Ip_7m AVDD lvtpfet l=LF w=wpswitch
XR23 outa ntx rppolyl l=LC w=WG
XR3 oute ntx rppolyl l=LC w=WG
XR4 outf ntx rppolyl l=LC w=WG
XR5 outg ntx rppolyl l=LC w=WG
XR1 outc ntx rppolyl l=LC w=WG
XR6 outh ntx rppolyl l=LC w=WG
XR2 outd ntx rppolyl l=LC w=WG
XR0 outb ntx rppolyl l=LC w=WG
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    INVD1LVT
* View Name:    schematic
************************************************************************

.SUBCKT INVD1LVT I VDD VSS ZN
*.PININFO I:I ZN:O VDD:B VSS:B
MMU1-M_u2 ZN I VSS VSS lvtnfet l=LF w=WE
MMU1-M_u3 ZN I VDD VDD lvtpfet l=LF w=WF
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    INVD16LVT
* View Name:    schematic
************************************************************************

.SUBCKT INVD16LVT I VDD VSS ZN
*.PININFO I:I ZN:O VDD:B VSS:B
MMI2_9-M_u3 ZN I VDD VDD lvtpfet l=LF w=WF
MMI2_6-M_u3 ZN I VDD VDD lvtpfet l=LF w=WF
MMI2_1-M_u3 ZN I VDD VDD lvtpfet l=LF w=WF
MMI2_4-M_u3 ZN I VDD VDD lvtpfet l=LF w=WF
MMI2_12-M_u3 ZN I VDD VDD lvtpfet l=LF w=WF
MMI2_13-M_u3 ZN I VDD VDD lvtpfet l=LF w=WF
MMI2_3-M_u3 ZN I VDD VDD lvtpfet l=LF w=WF
MMI2_10-M_u3 ZN I VDD VDD lvtpfet l=LF w=WF
MMI2_0-M_u3 ZN I VDD VDD lvtpfet l=LF w=WF
MMI2_11-M_u3 ZN I VDD VDD lvtpfet l=LF w=WF
MMI2_7-M_u3 ZN I VDD VDD lvtpfet l=LF w=WF
MMI2_5-M_u3 ZN I VDD VDD lvtpfet l=LF w=WF
MMI2_2-M_u3 ZN I VDD VDD lvtpfet l=LF w=WF
MMI2_8-M_u3 ZN I VDD VDD lvtpfet l=LF w=WF
MMI2_15-M_u3 ZN I VDD VDD lvtpfet l=LF w=WF
MMI2_14-M_u3 ZN I VDD VDD lvtpfet l=LF w=WF
MMI2_12-M_u2 ZN I VSS VSS lvtnfet l=LF w=WE
MMI2_15-M_u2 ZN I VSS VSS lvtnfet l=LF w=WE
MMI2_3-M_u2 ZN I VSS VSS lvtnfet l=LF w=WE
MMI2_14-M_u2 ZN I VSS VSS lvtnfet l=LF w=WE
MMI2_4-M_u2 ZN I VSS VSS lvtnfet l=LF w=WE
MMI2_1-M_u2 ZN I VSS VSS lvtnfet l=LF w=WE
MMI2_0-M_u2 ZN I VSS VSS lvtnfet l=LF w=WE
MMI2_13-M_u2 ZN I VSS VSS lvtnfet l=LF w=WE
MMI2_8-M_u2 ZN I VSS VSS lvtnfet l=LF w=WE
MMI2_5-M_u2 ZN I VSS VSS lvtnfet l=LF w=WE
MMI2_7-M_u2 ZN I VSS VSS lvtnfet l=LF w=WE
MMI2_6-M_u2 ZN I VSS VSS lvtnfet l=LF w=WE
MMI2_9-M_u2 ZN I VSS VSS lvtnfet l=LF w=WE
MMI2_2-M_u2 ZN I VSS VSS lvtnfet l=LF w=WE
MMI2_11-M_u2 ZN I VSS VSS lvtnfet l=LF w=WE
MMI2_10-M_u2 ZN I VSS VSS lvtnfet l=LF w=WE
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    INVD8LVT
* View Name:    schematic
************************************************************************

.SUBCKT INVD8LVT I VDD VSS ZN
*.PININFO I:I ZN:O VDD:B VSS:B
MMU1_5-M_u2 ZN I VSS VSS lvtnfet l=LF w=WE
MMU1_0-M_u2 ZN I VSS VSS lvtnfet l=LF w=WE
MMU1_3-M_u2 ZN I VSS VSS lvtnfet l=LF w=WE
MMU1_7-M_u2 ZN I VSS VSS lvtnfet l=LF w=WE
MMU1_4-M_u2 ZN I VSS VSS lvtnfet l=LF w=WE
MMU1_1-M_u2 ZN I VSS VSS lvtnfet l=LF w=WE
MMU1_6-M_u2 ZN I VSS VSS lvtnfet l=LF w=WE
MMU1_2-M_u2 ZN I VSS VSS lvtnfet l=LF w=WE
MMU1_0-M_u3 ZN I VDD VDD lvtpfet l=LF w=WF
MMU1_4-M_u3 ZN I VDD VDD lvtpfet l=LF w=WF
MMU1_5-M_u3 ZN I VDD VDD lvtpfet l=LF w=WF
MMU1_1-M_u3 ZN I VDD VDD lvtpfet l=LF w=WF
MMU1_3-M_u3 ZN I VDD VDD lvtpfet l=LF w=WF
MMU1_7-M_u3 ZN I VDD VDD lvtpfet l=LF w=WF
MMU1_6-M_u3 ZN I VDD VDD lvtpfet l=LF w=WF
MMU1_2-M_u3 ZN I VDD VDD lvtpfet l=LF w=WF
.ENDS

************************************************************************
* Library Name: AP_SerDes
* Cell Name:    PreDriver_PAM8_v4
* View Name:    schematic
************************************************************************

.SUBCKT PreDriver_PAM8_v4 A_7_ A_6_ A_5_ A_4_ A_3_ A_2_ A_1_ A_0_ Ain_7_
+ Ain_6_ Ain_5_ Ain_4_ Ain_3_ Ain_2_ Ain_1_ Ain_0_ B_7_ B_6_ B_5_ B_4_ B_3_
+ B_2_ B_1_ B_0_ Bin_7_ Bin_6_ Bin_5_ Bin_4_ Bin_3_ Bin_2_ Bin_1_ Bin_0_ C_7_
+ C_6_ C_5_ C_4_ C_3_ C_2_ C_1_ C_0_ Cin_7_ Cin_6_ Cin_5_ Cin_4_ Cin_3_ Cin_2_
+ Cin_1_ Cin_0_ D_7_ D_6_ D_5_ D_4_ D_3_ D_2_ D_1_ D_0_ DVDD DVSS Din_7_
+ Din_6_ Din_5_ Din_4_ Din_3_ Din_2_ Din_1_ Din_0_ E_7_ E_6_ E_5_ E_4_ E_3_
+ E_2_ E_1_ E_0_ Ein_7_ Ein_6_ Ein_5_ Ein_4_ Ein_3_ Ein_2_ Ein_1_ Ein_0_ F_7_
+ F_6_ F_5_ F_4_ F_3_ F_2_ F_1_ F_0_ Fin_7_ Fin_6_ Fin_5_ Fin_4_ Fin_3_ Fin_2_
+ Fin_1_ Fin_0_ G_7_ G_6_ G_5_ G_4_ G_3_ G_2_ G_1_ G_0_ Gin_7_ Gin_6_ Gin_5_
+ Gin_4_ Gin_3_ Gin_2_ Gin_1_ Gin_0_ H_7_ H_6_ H_5_ H_4_ H_3_ H_2_ H_1_ H_0_
+ Hin_7_ Hin_6_ Hin_5_ Hin_4_ Hin_3_ Hin_2_ Hin_1_ Hin_0_
*.PININFO Ain_7_:I Ain_6_:I Ain_5_:I Ain_4_:I Ain_3_:I Ain_2_:I Ain_1_:I
*.PININFO Ain_0_:I Bin_7_:I Bin_6_:I Bin_5_:I Bin_4_:I Bin_3_:I Bin_2_:I
*.PININFO Bin_1_:I Bin_0_:I Cin_7_:I Cin_6_:I Cin_5_:I Cin_4_:I Cin_3_:I
*.PININFO Cin_2_:I Cin_1_:I Cin_0_:I Din_7_:I Din_6_:I Din_5_:I Din_4_:I
*.PININFO Din_3_:I Din_2_:I Din_1_:I Din_0_:I Ein_7_:I Ein_6_:I Ein_5_:I
*.PININFO Ein_4_:I Ein_3_:I Ein_2_:I Ein_1_:I Ein_0_:I Fin_7_:I Fin_6_:I
*.PININFO Fin_5_:I Fin_4_:I Fin_3_:I Fin_2_:I Fin_1_:I Fin_0_:I Gin_7_:I
*.PININFO Gin_6_:I Gin_5_:I Gin_4_:I Gin_3_:I Gin_2_:I Gin_1_:I Gin_0_:I
*.PININFO Hin_7_:I Hin_6_:I Hin_5_:I Hin_4_:I Hin_3_:I Hin_2_:I Hin_1_:I
*.PININFO Hin_0_:I A_7_:O A_6_:O A_5_:O A_4_:O A_3_:O A_2_:O A_1_:O A_0_:O
*.PININFO B_7_:O B_6_:O B_5_:O B_4_:O B_3_:O B_2_:O B_1_:O B_0_:O C_7_:O
*.PININFO C_6_:O C_5_:O C_4_:O C_3_:O C_2_:O C_1_:O C_0_:O D_7_:O D_6_:O
*.PININFO D_5_:O D_4_:O D_3_:O D_2_:O D_1_:O D_0_:O E_7_:O E_6_:O E_5_:O
*.PININFO E_4_:O E_3_:O E_2_:O E_1_:O E_0_:O F_7_:O F_6_:O F_5_:O F_4_:O
*.PININFO F_3_:O F_2_:O F_1_:O F_0_:O G_7_:O G_6_:O G_5_:O G_4_:O G_3_:O
*.PININFO G_2_:O G_1_:O G_0_:O H_7_:O H_6_:O H_5_:O H_4_:O H_3_:O H_2_:O
*.PININFO H_1_:O H_0_:O DVDD:B DVSS:B
XI0<31> Ain_7_ net053 DVSS net024_0_ INVD1LVT
XI0<30> Ain_6_ net053 DVSS net024_1_ INVD1LVT
XI0<29> Ain_5_ net053 DVSS net024_2_ INVD1LVT
XI0<28> Ain_4_ net053 DVSS net024_3_ INVD1LVT
XI0<27> Bin_7_ net053 DVSS net024_4_ INVD1LVT
XI0<26> Bin_6_ net053 DVSS net024_5_ INVD1LVT
XI0<25> Bin_5_ net053 DVSS net024_6_ INVD1LVT
XI0<24> Bin_4_ net053 DVSS net024_7_ INVD1LVT
XI0<23> Cin_7_ net053 DVSS net024_8_ INVD1LVT
XI0<22> Cin_6_ net053 DVSS net024_9_ INVD1LVT
XI0<21> Cin_5_ net053 DVSS net024_10_ INVD1LVT
XI0<20> Cin_4_ net053 DVSS net024_11_ INVD1LVT
XI0<19> Din_7_ net053 DVSS net024_12_ INVD1LVT
XI0<18> Din_6_ net053 DVSS net024_13_ INVD1LVT
XI0<17> Din_5_ net053 DVSS net024_14_ INVD1LVT
XI0<16> Din_4_ net053 DVSS net024_15_ INVD1LVT
XI0<15> Ein_7_ net053 DVSS net024_16_ INVD1LVT
XI0<14> Ein_6_ net053 DVSS net024_17_ INVD1LVT
XI0<13> Ein_5_ net053 DVSS net024_18_ INVD1LVT
XI0<12> Ein_4_ net053 DVSS net024_19_ INVD1LVT
XI0<11> Fin_7_ net053 DVSS net024_20_ INVD1LVT
XI0<10> Fin_6_ net053 DVSS net024_21_ INVD1LVT
XI0<9> Fin_5_ net053 DVSS net024_22_ INVD1LVT
XI0<8> Fin_4_ net053 DVSS net024_23_ INVD1LVT
XI0<7> Gin_7_ net053 DVSS net024_24_ INVD1LVT
XI0<6> Gin_6_ net053 DVSS net024_25_ INVD1LVT
XI0<5> Gin_5_ net053 DVSS net024_26_ INVD1LVT
XI0<4> Gin_4_ net053 DVSS net024_27_ INVD1LVT
XI0<3> Hin_7_ net053 DVSS net024_28_ INVD1LVT
XI0<2> Hin_6_ net053 DVSS net024_29_ INVD1LVT
XI0<1> Hin_5_ net053 DVSS net024_30_ INVD1LVT
XI0<0> Hin_4_ net053 DVSS net024_31_ INVD1LVT
XI16<31> Ain_3_ net022 DVSS net010_0_ INVD1LVT
XI16<30> Ain_2_ net022 DVSS net010_1_ INVD1LVT
XI16<29> Ain_1_ net022 DVSS net010_2_ INVD1LVT
XI16<28> Ain_0_ net022 DVSS net010_3_ INVD1LVT
XI16<27> Bin_3_ net022 DVSS net010_4_ INVD1LVT
XI16<26> Bin_2_ net022 DVSS net010_5_ INVD1LVT
XI16<25> Bin_1_ net022 DVSS net010_6_ INVD1LVT
XI16<24> Bin_0_ net022 DVSS net010_7_ INVD1LVT
XI16<23> Cin_3_ net022 DVSS net010_8_ INVD1LVT
XI16<22> Cin_2_ net022 DVSS net010_9_ INVD1LVT
XI16<21> Cin_1_ net022 DVSS net010_10_ INVD1LVT
XI16<20> Cin_0_ net022 DVSS net010_11_ INVD1LVT
XI16<19> Din_3_ net022 DVSS net010_12_ INVD1LVT
XI16<18> Din_2_ net022 DVSS net010_13_ INVD1LVT
XI16<17> Din_1_ net022 DVSS net010_14_ INVD1LVT
XI16<16> Din_0_ net022 DVSS net010_15_ INVD1LVT
XI16<15> Ein_3_ net022 DVSS net010_16_ INVD1LVT
XI16<14> Ein_2_ net022 DVSS net010_17_ INVD1LVT
XI16<13> Ein_1_ net022 DVSS net010_18_ INVD1LVT
XI16<12> Ein_0_ net022 DVSS net010_19_ INVD1LVT
XI16<11> Fin_3_ net022 DVSS net010_20_ INVD1LVT
XI16<10> Fin_2_ net022 DVSS net010_21_ INVD1LVT
XI16<9> Fin_1_ net022 DVSS net010_22_ INVD1LVT
XI16<8> Fin_0_ net022 DVSS net010_23_ INVD1LVT
XI16<7> Gin_3_ net022 DVSS net010_24_ INVD1LVT
XI16<6> Gin_2_ net022 DVSS net010_25_ INVD1LVT
XI16<5> Gin_1_ net022 DVSS net010_26_ INVD1LVT
XI16<4> Gin_0_ net022 DVSS net010_27_ INVD1LVT
XI16<3> Hin_3_ net022 DVSS net010_28_ INVD1LVT
XI16<2> Hin_2_ net022 DVSS net010_29_ INVD1LVT
XI16<1> Hin_1_ net022 DVSS net010_30_ INVD1LVT
XI16<0> Hin_0_ net022 DVSS net010_31_ INVD1LVT
XI13<31> net010_0_ net028 DVSS net012_0_ INVD1LVT
XI13<30> net010_1_ net028 DVSS net012_1_ INVD1LVT
XI13<29> net010_2_ net028 DVSS net012_2_ INVD1LVT
XI13<28> net010_3_ net028 DVSS net012_3_ INVD1LVT
XI13<27> net010_4_ net028 DVSS net012_4_ INVD1LVT
XI13<26> net010_5_ net028 DVSS net012_5_ INVD1LVT
XI13<25> net010_6_ net028 DVSS net012_6_ INVD1LVT
XI13<24> net010_7_ net028 DVSS net012_7_ INVD1LVT
XI13<23> net010_8_ net028 DVSS net012_8_ INVD1LVT
XI13<22> net010_9_ net028 DVSS net012_9_ INVD1LVT
XI13<21> net010_10_ net028 DVSS net012_10_ INVD1LVT
XI13<20> net010_11_ net028 DVSS net012_11_ INVD1LVT
XI13<19> net010_12_ net028 DVSS net012_12_ INVD1LVT
XI13<18> net010_13_ net028 DVSS net012_13_ INVD1LVT
XI13<17> net010_14_ net028 DVSS net012_14_ INVD1LVT
XI13<16> net010_15_ net028 DVSS net012_15_ INVD1LVT
XI13<15> net010_16_ net028 DVSS net012_16_ INVD1LVT
XI13<14> net010_17_ net028 DVSS net012_17_ INVD1LVT
XI13<13> net010_18_ net028 DVSS net012_18_ INVD1LVT
XI13<12> net010_19_ net028 DVSS net012_19_ INVD1LVT
XI13<11> net010_20_ net028 DVSS net012_20_ INVD1LVT
XI13<10> net010_21_ net028 DVSS net012_21_ INVD1LVT
XI13<9> net010_22_ net028 DVSS net012_22_ INVD1LVT
XI13<8> net010_23_ net028 DVSS net012_23_ INVD1LVT
XI13<7> net010_24_ net028 DVSS net012_24_ INVD1LVT
XI13<6> net010_25_ net028 DVSS net012_25_ INVD1LVT
XI13<5> net010_26_ net028 DVSS net012_26_ INVD1LVT
XI13<4> net010_27_ net028 DVSS net012_27_ INVD1LVT
XI13<3> net010_28_ net028 DVSS net012_28_ INVD1LVT
XI13<2> net010_29_ net028 DVSS net012_29_ INVD1LVT
XI13<1> net010_30_ net028 DVSS net012_30_ INVD1LVT
XI13<0> net010_31_ net028 DVSS net012_31_ INVD1LVT
XI3<31> net012_0_ net033 DVSS net014_0_ INVD2LVT
XI3<30> net012_1_ net033 DVSS net014_1_ INVD2LVT
XI3<29> net012_2_ net033 DVSS net014_2_ INVD2LVT
XI3<28> net012_3_ net033 DVSS net014_3_ INVD2LVT
XI3<27> net012_4_ net033 DVSS net014_4_ INVD2LVT
XI3<26> net012_5_ net033 DVSS net014_5_ INVD2LVT
XI3<25> net012_6_ net033 DVSS net014_6_ INVD2LVT
XI3<24> net012_7_ net033 DVSS net014_7_ INVD2LVT
XI3<23> net012_8_ net033 DVSS net014_8_ INVD2LVT
XI3<22> net012_9_ net033 DVSS net014_9_ INVD2LVT
XI3<21> net012_10_ net033 DVSS net014_10_ INVD2LVT
XI3<20> net012_11_ net033 DVSS net014_11_ INVD2LVT
XI3<19> net012_12_ net033 DVSS net014_12_ INVD2LVT
XI3<18> net012_13_ net033 DVSS net014_13_ INVD2LVT
XI3<17> net012_14_ net033 DVSS net014_14_ INVD2LVT
XI3<16> net012_15_ net033 DVSS net014_15_ INVD2LVT
XI3<15> net012_16_ net033 DVSS net014_16_ INVD2LVT
XI3<14> net012_17_ net033 DVSS net014_17_ INVD2LVT
XI3<13> net012_18_ net033 DVSS net014_18_ INVD2LVT
XI3<12> net012_19_ net033 DVSS net014_19_ INVD2LVT
XI3<11> net012_20_ net033 DVSS net014_20_ INVD2LVT
XI3<10> net012_21_ net033 DVSS net014_21_ INVD2LVT
XI3<9> net012_22_ net033 DVSS net014_22_ INVD2LVT
XI3<8> net012_23_ net033 DVSS net014_23_ INVD2LVT
XI3<7> net012_24_ net033 DVSS net014_24_ INVD2LVT
XI3<6> net012_25_ net033 DVSS net014_25_ INVD2LVT
XI3<5> net012_26_ net033 DVSS net014_26_ INVD2LVT
XI3<4> net012_27_ net033 DVSS net014_27_ INVD2LVT
XI3<3> net012_28_ net033 DVSS net014_28_ INVD2LVT
XI3<2> net012_29_ net033 DVSS net014_29_ INVD2LVT
XI3<1> net012_30_ net033 DVSS net014_30_ INVD2LVT
XI3<0> net012_31_ net033 DVSS net014_31_ INVD2LVT
XI1<31> net024_0_ net031 DVSS net025_0_ INVD2LVT
XI1<30> net024_1_ net031 DVSS net025_1_ INVD2LVT
XI1<29> net024_2_ net031 DVSS net025_2_ INVD2LVT
XI1<28> net024_3_ net031 DVSS net025_3_ INVD2LVT
XI1<27> net024_4_ net031 DVSS net025_4_ INVD2LVT
XI1<26> net024_5_ net031 DVSS net025_5_ INVD2LVT
XI1<25> net024_6_ net031 DVSS net025_6_ INVD2LVT
XI1<24> net024_7_ net031 DVSS net025_7_ INVD2LVT
XI1<23> net024_8_ net031 DVSS net025_8_ INVD2LVT
XI1<22> net024_9_ net031 DVSS net025_9_ INVD2LVT
XI1<21> net024_10_ net031 DVSS net025_10_ INVD2LVT
XI1<20> net024_11_ net031 DVSS net025_11_ INVD2LVT
XI1<19> net024_12_ net031 DVSS net025_12_ INVD2LVT
XI1<18> net024_13_ net031 DVSS net025_13_ INVD2LVT
XI1<17> net024_14_ net031 DVSS net025_14_ INVD2LVT
XI1<16> net024_15_ net031 DVSS net025_15_ INVD2LVT
XI1<15> net024_16_ net031 DVSS net025_16_ INVD2LVT
XI1<14> net024_17_ net031 DVSS net025_17_ INVD2LVT
XI1<13> net024_18_ net031 DVSS net025_18_ INVD2LVT
XI1<12> net024_19_ net031 DVSS net025_19_ INVD2LVT
XI1<11> net024_20_ net031 DVSS net025_20_ INVD2LVT
XI1<10> net024_21_ net031 DVSS net025_21_ INVD2LVT
XI1<9> net024_22_ net031 DVSS net025_22_ INVD2LVT
XI1<8> net024_23_ net031 DVSS net025_23_ INVD2LVT
XI1<7> net024_24_ net031 DVSS net025_24_ INVD2LVT
XI1<6> net024_25_ net031 DVSS net025_25_ INVD2LVT
XI1<5> net024_26_ net031 DVSS net025_26_ INVD2LVT
XI1<4> net024_27_ net031 DVSS net025_27_ INVD2LVT
XI1<3> net024_28_ net031 DVSS net025_28_ INVD2LVT
XI1<2> net024_29_ net031 DVSS net025_29_ INVD2LVT
XI1<1> net024_30_ net031 DVSS net025_30_ INVD2LVT
XI1<0> net024_31_ net031 DVSS net025_31_ INVD2LVT
XI4<31> net014_0_ net039 DVSS net015_0_ INVD4LVT
XI4<30> net014_1_ net039 DVSS net015_1_ INVD4LVT
XI4<29> net014_2_ net039 DVSS net015_2_ INVD4LVT
XI4<28> net014_3_ net039 DVSS net015_3_ INVD4LVT
XI4<27> net014_4_ net039 DVSS net015_4_ INVD4LVT
XI4<26> net014_5_ net039 DVSS net015_5_ INVD4LVT
XI4<25> net014_6_ net039 DVSS net015_6_ INVD4LVT
XI4<24> net014_7_ net039 DVSS net015_7_ INVD4LVT
XI4<23> net014_8_ net039 DVSS net015_8_ INVD4LVT
XI4<22> net014_9_ net039 DVSS net015_9_ INVD4LVT
XI4<21> net014_10_ net039 DVSS net015_10_ INVD4LVT
XI4<20> net014_11_ net039 DVSS net015_11_ INVD4LVT
XI4<19> net014_12_ net039 DVSS net015_12_ INVD4LVT
XI4<18> net014_13_ net039 DVSS net015_13_ INVD4LVT
XI4<17> net014_14_ net039 DVSS net015_14_ INVD4LVT
XI4<16> net014_15_ net039 DVSS net015_15_ INVD4LVT
XI4<15> net014_16_ net039 DVSS net015_16_ INVD4LVT
XI4<14> net014_17_ net039 DVSS net015_17_ INVD4LVT
XI4<13> net014_18_ net039 DVSS net015_18_ INVD4LVT
XI4<12> net014_19_ net039 DVSS net015_19_ INVD4LVT
XI4<11> net014_20_ net039 DVSS net015_20_ INVD4LVT
XI4<10> net014_21_ net039 DVSS net015_21_ INVD4LVT
XI4<9> net014_22_ net039 DVSS net015_22_ INVD4LVT
XI4<8> net014_23_ net039 DVSS net015_23_ INVD4LVT
XI4<7> net014_24_ net039 DVSS net015_24_ INVD4LVT
XI4<6> net014_25_ net039 DVSS net015_25_ INVD4LVT
XI4<5> net014_26_ net039 DVSS net015_26_ INVD4LVT
XI4<4> net014_27_ net039 DVSS net015_27_ INVD4LVT
XI4<3> net014_28_ net039 DVSS net015_28_ INVD4LVT
XI4<2> net014_29_ net039 DVSS net015_29_ INVD4LVT
XI4<1> net014_30_ net039 DVSS net015_30_ INVD4LVT
XI4<0> net014_31_ net039 DVSS net015_31_ INVD4LVT
XI6<31> net017_0_ net051 DVSS A_3_ INVD16LVT
XI6<30> net017_1_ net051 DVSS A_2_ INVD16LVT
XI6<29> net017_2_ net051 DVSS A_1_ INVD16LVT
XI6<28> net017_3_ net051 DVSS A_0_ INVD16LVT
XI6<27> net017_4_ net051 DVSS B_3_ INVD16LVT
XI6<26> net017_5_ net051 DVSS B_2_ INVD16LVT
XI6<25> net017_6_ net051 DVSS B_1_ INVD16LVT
XI6<24> net017_7_ net051 DVSS B_0_ INVD16LVT
XI6<23> net017_8_ net051 DVSS C_3_ INVD16LVT
XI6<22> net017_9_ net051 DVSS C_2_ INVD16LVT
XI6<21> net017_10_ net051 DVSS C_1_ INVD16LVT
XI6<20> net017_11_ net051 DVSS C_0_ INVD16LVT
XI6<19> net017_12_ net051 DVSS D_3_ INVD16LVT
XI6<18> net017_13_ net051 DVSS D_2_ INVD16LVT
XI6<17> net017_14_ net051 DVSS D_1_ INVD16LVT
XI6<16> net017_15_ net051 DVSS D_0_ INVD16LVT
XI6<15> net017_16_ net051 DVSS E_3_ INVD16LVT
XI6<14> net017_17_ net051 DVSS E_2_ INVD16LVT
XI6<13> net017_18_ net051 DVSS E_1_ INVD16LVT
XI6<12> net017_19_ net051 DVSS E_0_ INVD16LVT
XI6<11> net017_20_ net051 DVSS F_3_ INVD16LVT
XI6<10> net017_21_ net051 DVSS F_2_ INVD16LVT
XI6<9> net017_22_ net051 DVSS F_1_ INVD16LVT
XI6<8> net017_23_ net051 DVSS F_0_ INVD16LVT
XI6<7> net017_24_ net051 DVSS G_3_ INVD16LVT
XI6<6> net017_25_ net051 DVSS G_2_ INVD16LVT
XI6<5> net017_26_ net051 DVSS G_1_ INVD16LVT
XI6<4> net017_27_ net051 DVSS G_0_ INVD16LVT
XI6<3> net017_28_ net051 DVSS H_3_ INVD16LVT
XI6<2> net017_29_ net051 DVSS H_2_ INVD16LVT
XI6<1> net017_30_ net051 DVSS H_1_ INVD16LVT
XI6<0> net017_31_ net051 DVSS H_0_ INVD16LVT
XI62<31> net026_0_ net044 DVSS A_7_ INVD16LVT
XI62<30> net026_1_ net044 DVSS A_6_ INVD16LVT
XI62<29> net026_2_ net044 DVSS A_5_ INVD16LVT
XI62<28> net026_3_ net044 DVSS A_4_ INVD16LVT
XI62<27> net026_4_ net044 DVSS B_7_ INVD16LVT
XI62<26> net026_5_ net044 DVSS B_6_ INVD16LVT
XI62<25> net026_6_ net044 DVSS B_5_ INVD16LVT
XI62<24> net026_7_ net044 DVSS B_4_ INVD16LVT
XI62<23> net026_8_ net044 DVSS C_7_ INVD16LVT
XI62<22> net026_9_ net044 DVSS C_6_ INVD16LVT
XI62<21> net026_10_ net044 DVSS C_5_ INVD16LVT
XI62<20> net026_11_ net044 DVSS C_4_ INVD16LVT
XI62<19> net026_12_ net044 DVSS D_7_ INVD16LVT
XI62<18> net026_13_ net044 DVSS D_6_ INVD16LVT
XI62<17> net026_14_ net044 DVSS D_5_ INVD16LVT
XI62<16> net026_15_ net044 DVSS D_4_ INVD16LVT
XI62<15> net026_16_ net044 DVSS E_7_ INVD16LVT
XI62<14> net026_17_ net044 DVSS E_6_ INVD16LVT
XI62<13> net026_18_ net044 DVSS E_5_ INVD16LVT
XI62<12> net026_19_ net044 DVSS E_4_ INVD16LVT
XI62<11> net026_20_ net044 DVSS F_7_ INVD16LVT
XI62<10> net026_21_ net044 DVSS F_6_ INVD16LVT
XI62<9> net026_22_ net044 DVSS F_5_ INVD16LVT
XI62<8> net026_23_ net044 DVSS F_4_ INVD16LVT
XI62<7> net026_24_ net044 DVSS G_7_ INVD16LVT
XI62<6> net026_25_ net044 DVSS G_6_ INVD16LVT
XI62<5> net026_26_ net044 DVSS G_5_ INVD16LVT
XI62<4> net026_27_ net044 DVSS G_4_ INVD16LVT
XI62<3> net026_28_ net044 DVSS H_7_ INVD16LVT
XI62<2> net026_29_ net044 DVSS H_6_ INVD16LVT
XI62<1> net026_30_ net044 DVSS H_5_ INVD16LVT
XI62<0> net026_31_ net044 DVSS H_4_ INVD16LVT
XI28<31> net026_0_ net046 DVSS A_7_ INVD16LVT
XI28<30> net026_1_ net046 DVSS A_6_ INVD16LVT
XI28<29> net026_2_ net046 DVSS A_5_ INVD16LVT
XI28<28> net026_3_ net046 DVSS A_4_ INVD16LVT
XI28<27> net026_4_ net046 DVSS B_7_ INVD16LVT
XI28<26> net026_5_ net046 DVSS B_6_ INVD16LVT
XI28<25> net026_6_ net046 DVSS B_5_ INVD16LVT
XI28<24> net026_7_ net046 DVSS B_4_ INVD16LVT
XI28<23> net026_8_ net046 DVSS C_7_ INVD16LVT
XI28<22> net026_9_ net046 DVSS C_6_ INVD16LVT
XI28<21> net026_10_ net046 DVSS C_5_ INVD16LVT
XI28<20> net026_11_ net046 DVSS C_4_ INVD16LVT
XI28<19> net026_12_ net046 DVSS D_7_ INVD16LVT
XI28<18> net026_13_ net046 DVSS D_6_ INVD16LVT
XI28<17> net026_14_ net046 DVSS D_5_ INVD16LVT
XI28<16> net026_15_ net046 DVSS D_4_ INVD16LVT
XI28<15> net026_16_ net046 DVSS E_7_ INVD16LVT
XI28<14> net026_17_ net046 DVSS E_6_ INVD16LVT
XI28<13> net026_18_ net046 DVSS E_5_ INVD16LVT
XI28<12> net026_19_ net046 DVSS E_4_ INVD16LVT
XI28<11> net026_20_ net046 DVSS F_7_ INVD16LVT
XI28<10> net026_21_ net046 DVSS F_6_ INVD16LVT
XI28<9> net026_22_ net046 DVSS F_5_ INVD16LVT
XI28<8> net026_23_ net046 DVSS F_4_ INVD16LVT
XI28<7> net026_24_ net046 DVSS G_7_ INVD16LVT
XI28<6> net026_25_ net046 DVSS G_6_ INVD16LVT
XI28<5> net026_26_ net046 DVSS G_5_ INVD16LVT
XI28<4> net026_27_ net046 DVSS G_4_ INVD16LVT
XI28<3> net026_28_ net046 DVSS H_7_ INVD16LVT
XI28<2> net026_29_ net046 DVSS H_6_ INVD16LVT
XI28<1> net026_30_ net046 DVSS H_5_ INVD16LVT
XI28<0> net026_31_ net046 DVSS H_4_ INVD16LVT
XI5<31> net015_0_ net048 DVSS net017_0_ INVD8LVT
XI5<30> net015_1_ net048 DVSS net017_1_ INVD8LVT
XI5<29> net015_2_ net048 DVSS net017_2_ INVD8LVT
XI5<28> net015_3_ net048 DVSS net017_3_ INVD8LVT
XI5<27> net015_4_ net048 DVSS net017_4_ INVD8LVT
XI5<26> net015_5_ net048 DVSS net017_5_ INVD8LVT
XI5<25> net015_6_ net048 DVSS net017_6_ INVD8LVT
XI5<24> net015_7_ net048 DVSS net017_7_ INVD8LVT
XI5<23> net015_8_ net048 DVSS net017_8_ INVD8LVT
XI5<22> net015_9_ net048 DVSS net017_9_ INVD8LVT
XI5<21> net015_10_ net048 DVSS net017_10_ INVD8LVT
XI5<20> net015_11_ net048 DVSS net017_11_ INVD8LVT
XI5<19> net015_12_ net048 DVSS net017_12_ INVD8LVT
XI5<18> net015_13_ net048 DVSS net017_13_ INVD8LVT
XI5<17> net015_14_ net048 DVSS net017_14_ INVD8LVT
XI5<16> net015_15_ net048 DVSS net017_15_ INVD8LVT
XI5<15> net015_16_ net048 DVSS net017_16_ INVD8LVT
XI5<14> net015_17_ net048 DVSS net017_17_ INVD8LVT
XI5<13> net015_18_ net048 DVSS net017_18_ INVD8LVT
XI5<12> net015_19_ net048 DVSS net017_19_ INVD8LVT
XI5<11> net015_20_ net048 DVSS net017_20_ INVD8LVT
XI5<10> net015_21_ net048 DVSS net017_21_ INVD8LVT
XI5<9> net015_22_ net048 DVSS net017_22_ INVD8LVT
XI5<8> net015_23_ net048 DVSS net017_23_ INVD8LVT
XI5<7> net015_24_ net048 DVSS net017_24_ INVD8LVT
XI5<6> net015_25_ net048 DVSS net017_25_ INVD8LVT
XI5<5> net015_26_ net048 DVSS net017_26_ INVD8LVT
XI5<4> net015_27_ net048 DVSS net017_27_ INVD8LVT
XI5<3> net015_28_ net048 DVSS net017_28_ INVD8LVT
XI5<2> net015_29_ net048 DVSS net017_29_ INVD8LVT
XI5<1> net015_30_ net048 DVSS net017_30_ INVD8LVT
XI5<0> net015_31_ net048 DVSS net017_31_ INVD8LVT
XI63<31> net025_0_ net041 DVSS net026_0_ INVD8LVT
XI63<30> net025_1_ net041 DVSS net026_1_ INVD8LVT
XI63<29> net025_2_ net041 DVSS net026_2_ INVD8LVT
XI63<28> net025_3_ net041 DVSS net026_3_ INVD8LVT
XI63<27> net025_4_ net041 DVSS net026_4_ INVD8LVT
XI63<26> net025_5_ net041 DVSS net026_5_ INVD8LVT
XI63<25> net025_6_ net041 DVSS net026_6_ INVD8LVT
XI63<24> net025_7_ net041 DVSS net026_7_ INVD8LVT
XI63<23> net025_8_ net041 DVSS net026_8_ INVD8LVT
XI63<22> net025_9_ net041 DVSS net026_9_ INVD8LVT
XI63<21> net025_10_ net041 DVSS net026_10_ INVD8LVT
XI63<20> net025_11_ net041 DVSS net026_11_ INVD8LVT
XI63<19> net025_12_ net041 DVSS net026_12_ INVD8LVT
XI63<18> net025_13_ net041 DVSS net026_13_ INVD8LVT
XI63<17> net025_14_ net041 DVSS net026_14_ INVD8LVT
XI63<16> net025_15_ net041 DVSS net026_15_ INVD8LVT
XI63<15> net025_16_ net041 DVSS net026_16_ INVD8LVT
XI63<14> net025_17_ net041 DVSS net026_17_ INVD8LVT
XI63<13> net025_18_ net041 DVSS net026_18_ INVD8LVT
XI63<12> net025_19_ net041 DVSS net026_19_ INVD8LVT
XI63<11> net025_20_ net041 DVSS net026_20_ INVD8LVT
XI63<10> net025_21_ net041 DVSS net026_21_ INVD8LVT
XI63<9> net025_22_ net041 DVSS net026_22_ INVD8LVT
XI63<8> net025_23_ net041 DVSS net026_23_ INVD8LVT
XI63<7> net025_24_ net041 DVSS net026_24_ INVD8LVT
XI63<6> net025_25_ net041 DVSS net026_25_ INVD8LVT
XI63<5> net025_26_ net041 DVSS net026_26_ INVD8LVT
XI63<4> net025_27_ net041 DVSS net026_27_ INVD8LVT
XI63<3> net025_28_ net041 DVSS net026_28_ INVD8LVT
XI63<2> net025_29_ net041 DVSS net026_29_ INVD8LVT
XI63<1> net025_30_ net041 DVSS net026_30_ INVD8LVT
XI63<0> net025_31_ net041 DVSS net026_31_ INVD8LVT
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    NR2D1LVT
* View Name:    schematic
************************************************************************

.SUBCKT NR2D1LVT A1 A2 VDD VSS ZN
*.PININFO A1:I A2:I ZN:O VDD:B VSS:B
MMI1-M_u3 ZN A2 VSS VSS lvtnfet l=LF w=WE
MMI1-M_u4 ZN A1 VSS VSS lvtnfet l=LF w=WE
MMI1-M_u1 net13 A2 VDD VDD lvtpfet l=LF w=WF
MMI1-M_u2 ZN A1 net13 VDD lvtpfet l=LF w=WF
.ENDS

************************************************************************
* Library Name: AP_SerDes
* Cell Name:    DFF_LVT
* View Name:    schematic
************************************************************************

.SUBCKT DFF_LVT CK D DGND DVDD Q QN
*.PININFO CK:I D:I Q:O QN:O DGND:B DVDD:B
MM7 Q QN DGND DGND lvtnfet l=LF w=WE
MM2 QN CK NET4 DGND lvtnfet l=LF w=WB
MM13 N1 D DGND DGND lvtnfet l=LF w=WB
MM4 NET2 N1 NET3 DGND lvtnfet l=LF w=WB
MM3 NET4 NET2 DGND DGND lvtnfet l=LF w=WE
MM14 NET3 CK DGND DGND lvtnfet l=LF w=WB
MM9 NET2 CK DVDD DVDD lvtpfet l=LF w=WB
MM8 NET1 D DVDD DVDD lvtpfet l=LF w=WB
MM12 Q QN DVDD DVDD lvtpfet l=LF w=WF
MM11 QN NET2 DVDD DVDD lvtpfet l=LF w=WF
MM15 N1 CK NET1 DVDD lvtpfet l=LF w=WB
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    AN2D1LVT
* View Name:    schematic
************************************************************************

.SUBCKT AN2D1LVT A1 A2 VDD VSS Z
*.PININFO A1:I A2:I Z:O VDD:B VSS:B
MM_u3-M_u3 Z net5 VDD VDD lvtpfet l=LF w=WF
MM_u2-M_u1 net5 A1 VDD VDD lvtpfet l=LF w=WD
MM_u2-M_u2 net5 A2 VDD VDD lvtpfet l=LF w=WD
MM_u3-M_u2 Z net5 VSS VSS lvtnfet l=LF w=WE
MM_u2-M_u4 net17 A2 VSS VSS lvtnfet l=LF w=WC
MM_u2-M_u3 net5 A1 net17 VSS lvtnfet l=LF w=WC
.ENDS

************************************************************************
* Library Name: AP_SerDes
* Cell Name:    ENC_8l12b_v2_tspc_stage2_v2
* View Name:    schematic
************************************************************************

.SUBCKT ENC_8l12b_v2_tspc_stage2_v2 CLK DEC20_3_ DEC20_2_ DEC20_1_ DEC20_0_
+ DEC21_3_ DEC21_2_ DEC21_1_ DEC21_0_ DEC64_3_ DEC64_2_ DEC64_1_ DEC64_0_
+ DEC65_3_ DEC65_2_ DEC65_1_ DEC65_0_ DEC83_3_ DEC83_2_ DEC83_1_ DEC83_0_
+ DEC87_3_ DEC87_2_ DEC87_1_ DEC87_0_ DEC93_3_ DEC93_2_ DEC93_1_ DEC93_0_
+ DEC97_3_ DEC97_2_ DEC97_1_ DEC97_0_ DEC103_3_ DEC103_2_ DEC103_1_ DEC103_0_
+ DEC107_3_ DEC107_2_ DEC107_1_ DEC107_0_ DEC113_3_ DEC113_2_ DEC113_1_
+ DEC113_0_ DEC117_3_ DEC117_2_ DEC117_1_ DEC117_0_ DIN_11_ DIN_10_ DIN_9_
+ DIN_8_ DIN_7_ DIN_6_ DIN_5_ DIN_4_ DIN_3_ DIN_2_ DIN_1_ DIN_0_ DVDD DVSS
*.PININFO CLK:I DIN_11_:I DIN_10_:I DIN_9_:I DIN_8_:I DIN_7_:I DIN_6_:I
*.PININFO DIN_5_:I DIN_4_:I DIN_3_:I DIN_2_:I DIN_1_:I DIN_0_:I DEC20_3_:O
*.PININFO DEC20_2_:O DEC20_1_:O DEC20_0_:O DEC21_3_:O DEC21_2_:O DEC21_1_:O
*.PININFO DEC21_0_:O DEC64_3_:O DEC64_2_:O DEC64_1_:O DEC64_0_:O DEC65_3_:O
*.PININFO DEC65_2_:O DEC65_1_:O DEC65_0_:O DEC83_3_:O DEC83_2_:O DEC83_1_:O
*.PININFO DEC83_0_:O DEC87_3_:O DEC87_2_:O DEC87_1_:O DEC87_0_:O DEC93_3_:O
*.PININFO DEC93_2_:O DEC93_1_:O DEC93_0_:O DEC97_3_:O DEC97_2_:O DEC97_1_:O
*.PININFO DEC97_0_:O DEC103_3_:O DEC103_2_:O DEC103_1_:O DEC103_0_:O
*.PININFO DEC107_3_:O DEC107_2_:O DEC107_1_:O DEC107_0_:O DEC113_3_:O
*.PININFO DEC113_2_:O DEC113_1_:O DEC113_0_:O DEC117_3_:O DEC117_2_:O
*.PININFO DEC117_1_:O DEC117_0_:O DVDD:B DVSS:B
XI313<3> net065_0_ DVDD DVSS DEC64_3_ INVD2LVT
XI313<2> net065_1_ DVDD DVSS DEC64_2_ INVD2LVT
XI313<1> net065_2_ DVDD DVSS DEC64_1_ INVD2LVT
XI313<0> net065_3_ DVDD DVSS DEC64_0_ INVD2LVT
XI312<3> net066_0_ DVDD DVSS DEC65_3_ INVD2LVT
XI312<2> net066_1_ DVDD DVSS DEC65_2_ INVD2LVT
XI312<1> net066_2_ DVDD DVSS DEC65_1_ INVD2LVT
XI312<0> net066_3_ DVDD DVSS DEC65_0_ INVD2LVT
XI309<1> bf_4_ DVDD DVSS bzfd_4_ INVD2LVT
XI309<0> bzf_4_ DVDD DVSS bfd_4_ INVD2LVT
XI308<1> bf_10_ DVDD DVSS bzfd_10_ INVD2LVT
XI308<0> bzf_10_ DVDD DVSS bfd_10_ INVD2LVT
XI307<1> bf_6_ DVDD DVSS bzfd_6_ INVD2LVT
XI307<0> bzf_6_ DVDD DVSS bfd_6_ INVD2LVT
XI306<1> bf_5_ DVDD DVSS bzfd_5_ INVD2LVT
XI306<0> bzf_5_ DVDD DVSS bfd_5_ INVD2LVT
XI305<1> bf_9_ DVDD DVSS bzfd_9_ INVD2LVT
XI305<0> bzf_9_ DVDD DVSS bfd_9_ INVD2LVT
XI304<1> bf_0_ DVDD DVSS bzfd_0_ INVD2LVT
XI304<0> bzf_0_ DVDD DVSS bfd_0_ INVD2LVT
XI303<1> BF_8_ DVDD DVSS BZFD_8_ INVD2LVT
XI303<0> BZF_8_ DVDD DVSS BFD_8_ INVD2LVT
XI302<1> bf_2_ DVDD DVSS bzfd_2_ INVD2LVT
XI302<0> bzf_2_ DVDD DVSS bfd_2_ INVD2LVT
XI301<1> bf_1_ DVDD DVSS bzfd_1_ INVD2LVT
XI301<0> bzf_1_ DVDD DVSS bfd_1_ INVD2LVT
XI300<1> bf_11_ DVDD DVSS bzfd_11_ INVD2LVT
XI300<0> bzf_11_ DVDD DVSS bfd_11_ INVD2LVT
XI311<3> net067_0_ DVDD DVSS DEC20_3_ INVD2LVT
XI311<2> net067_1_ DVDD DVSS DEC20_2_ INVD2LVT
XI311<1> net067_2_ DVDD DVSS DEC20_1_ INVD2LVT
XI311<0> net067_3_ DVDD DVSS DEC20_0_ INVD2LVT
XI299<1> bf_3_ DVDD DVSS BZFD_3_ INVD2LVT
XI299<0> bzf_3_ DVDD DVSS BFD_3_ INVD2LVT
XI310<3> net068_0_ DVDD DVSS DEC21_3_ INVD2LVT
XI310<2> net068_1_ DVDD DVSS DEC21_2_ INVD2LVT
XI310<1> net068_2_ DVDD DVSS DEC21_1_ INVD2LVT
XI310<0> net068_3_ DVDD DVSS DEC21_0_ INVD2LVT
XI249<1> bf_7_ DVDD DVSS bzfd_7_ INVD2LVT
XI249<0> bzf_7_ DVDD DVSS bfd_7_ INVD2LVT
XI288 CLK DIN_2_ DVSS DVDD bf_2_ bzf_2_ DFF_LVT
XI298 CLK DIN_3_ DVSS DVDD bf_3_ bzf_3_ DFF_LVT
XI253<3> CLK net080_0_ DVSS DVDD DEC113_3_ net076_0_ DFF_LVT
XI253<2> CLK net080_1_ DVSS DVDD DEC113_2_ net076_1_ DFF_LVT
XI253<1> CLK net080_2_ DVSS DVDD DEC113_1_ net076_2_ DFF_LVT
XI253<0> CLK net080_3_ DVSS DVDD DEC113_0_ net076_3_ DFF_LVT
XI259<3> CLK net049_0_ DVSS DVDD DEC87_3_ net069_0_ DFF_LVT
XI259<2> CLK net049_1_ DVSS DVDD DEC87_2_ net069_1_ DFF_LVT
XI259<1> CLK net049_2_ DVSS DVDD DEC87_1_ net069_2_ DFF_LVT
XI259<0> CLK net049_3_ DVSS DVDD DEC87_0_ net069_3_ DFF_LVT
XI255<3> CLK net051_0_ DVSS DVDD DEC107_3_ net073_0_ DFF_LVT
XI255<2> CLK net051_1_ DVSS DVDD DEC107_2_ net073_1_ DFF_LVT
XI255<1> CLK net051_2_ DVSS DVDD DEC107_1_ net073_2_ DFF_LVT
XI255<0> CLK net051_3_ DVSS DVDD DEC107_0_ net073_3_ DFF_LVT
XI263<3> CLK net047_0_ DVSS DVDD net062_0_ net065_0_ DFF_LVT
XI263<2> CLK net047_1_ DVSS DVDD net062_1_ net065_1_ DFF_LVT
XI263<1> CLK net047_2_ DVSS DVDD net062_2_ net065_2_ DFF_LVT
XI263<0> CLK net047_3_ DVSS DVDD net062_3_ net065_3_ DFF_LVT
XI261<3> CLK net048_0_ DVSS DVDD net042_0_ net067_0_ DFF_LVT
XI261<2> CLK net048_1_ DVSS DVDD net042_1_ net067_1_ DFF_LVT
XI261<1> CLK net048_2_ DVSS DVDD net042_2_ net067_2_ DFF_LVT
XI261<0> CLK net048_3_ DVSS DVDD net042_3_ net067_3_ DFF_LVT
XI238<3> CLK net037_0_ DVSS DVDD net061_0_ net066_0_ DFF_LVT
XI238<2> CLK net037_1_ DVSS DVDD net061_1_ net066_1_ DFF_LVT
XI238<1> CLK net037_2_ DVSS DVDD net061_2_ net066_2_ DFF_LVT
XI238<0> CLK net037_3_ DVSS DVDD net061_3_ net066_3_ DFF_LVT
XI237<3> CLK net038_0_ DVSS DVDD net044_0_ net068_0_ DFF_LVT
XI237<2> CLK net038_1_ DVSS DVDD net044_1_ net068_1_ DFF_LVT
XI237<1> CLK net038_2_ DVSS DVDD net044_2_ net068_2_ DFF_LVT
XI237<0> CLK net038_3_ DVSS DVDD net044_3_ net068_3_ DFF_LVT
XI236<3> CLK net045_0_ DVSS DVDD DEC83_3_ net070_0_ DFF_LVT
XI236<2> CLK net045_1_ DVSS DVDD DEC83_2_ net070_1_ DFF_LVT
XI236<1> CLK net045_2_ DVSS DVDD DEC83_1_ net070_2_ DFF_LVT
XI236<0> CLK net045_3_ DVSS DVDD DEC83_0_ net070_3_ DFF_LVT
XI235<3> CLK net046_0_ DVSS DVDD DEC93_3_ net072_0_ DFF_LVT
XI235<2> CLK net046_1_ DVSS DVDD DEC93_2_ net072_1_ DFF_LVT
XI235<1> CLK net046_2_ DVSS DVDD DEC93_1_ net072_2_ DFF_LVT
XI235<0> CLK net046_3_ DVSS DVDD DEC93_0_ net072_3_ DFF_LVT
XI296 CLK DIN_6_ DVSS DVDD bf_6_ bzf_6_ DFF_LVT
XI295 CLK DIN_5_ DVSS DVDD bf_5_ bzf_5_ DFF_LVT
XI294 CLK DIN_7_ DVSS DVDD bf_7_ bzf_7_ DFF_LVT
XI293 CLK DIN_9_ DVSS DVDD bf_9_ bzf_9_ DFF_LVT
XI292 CLK DIN_0_ DVSS DVDD bf_0_ bzf_0_ DFF_LVT
XI291 CLK DIN_8_ DVSS DVDD BF_8_ BZF_8_ DFF_LVT
XI257<3> CLK net050_0_ DVSS DVDD DEC97_3_ net071_0_ DFF_LVT
XI257<2> CLK net050_1_ DVSS DVDD DEC97_2_ net071_1_ DFF_LVT
XI257<1> CLK net050_2_ DVSS DVDD DEC97_1_ net071_2_ DFF_LVT
XI257<0> CLK net050_3_ DVSS DVDD DEC97_0_ net071_3_ DFF_LVT
XI290 CLK DIN_10_ DVSS DVDD bf_10_ bzf_10_ DFF_LVT
XI289 CLK DIN_1_ DVSS DVDD bf_1_ bzf_1_ DFF_LVT
XI21 CLK DIN_11_ DVSS DVDD bf_11_ bzf_11_ DFF_LVT
XI233<3> CLK net052_0_ DVSS DVDD DEC117_3_ net075_0_ DFF_LVT
XI233<2> CLK net052_1_ DVSS DVDD DEC117_2_ net075_1_ DFF_LVT
XI233<1> CLK net052_2_ DVSS DVDD DEC117_1_ net075_2_ DFF_LVT
XI233<0> CLK net052_3_ DVSS DVDD DEC117_0_ net075_3_ DFF_LVT
XI234<3> CLK net079_0_ DVSS DVDD DEC103_3_ net074_0_ DFF_LVT
XI234<2> CLK net079_1_ DVSS DVDD DEC103_2_ net074_1_ DFF_LVT
XI234<1> CLK net079_2_ DVSS DVDD DEC103_1_ net074_2_ DFF_LVT
XI234<0> CLK net079_3_ DVSS DVDD DEC103_0_ net074_3_ DFF_LVT
XI297 CLK DIN_4_ DVSS DVDD bf_4_ bzf_4_ DFF_LVT
XI166<3> BFD_3_ bfd_10_ DVDD DVSS net079_0_ AN2D1LVT
XI166<2> BZFD_3_ bfd_10_ DVDD DVSS net079_1_ AN2D1LVT
XI166<1> BFD_3_ bzfd_10_ DVDD DVSS net079_2_ AN2D1LVT
XI166<0> BZFD_3_ bzfd_10_ DVDD DVSS net079_3_ AN2D1LVT
XI262<3> bfd_4_ bfd_6_ DVDD DVSS net047_0_ AN2D1LVT
XI262<2> bzfd_4_ bfd_6_ DVDD DVSS net047_1_ AN2D1LVT
XI262<1> bfd_4_ bzfd_6_ DVDD DVSS net047_2_ AN2D1LVT
XI262<0> bzfd_4_ bzfd_6_ DVDD DVSS net047_3_ AN2D1LVT
XI260<3> bfd_0_ bfd_2_ DVDD DVSS net048_0_ AN2D1LVT
XI260<2> bzfd_0_ bfd_2_ DVDD DVSS net048_1_ AN2D1LVT
XI260<1> bfd_0_ bzfd_2_ DVDD DVSS net048_2_ AN2D1LVT
XI260<0> bzfd_0_ bzfd_2_ DVDD DVSS net048_3_ AN2D1LVT
XI258<3> bfd_7_ BFD_8_ DVDD DVSS net049_0_ AN2D1LVT
XI258<2> bzfd_7_ BFD_8_ DVDD DVSS net049_1_ AN2D1LVT
XI258<1> bfd_7_ BZFD_8_ DVDD DVSS net049_2_ AN2D1LVT
XI258<0> bzfd_7_ BZFD_8_ DVDD DVSS net049_3_ AN2D1LVT
XI256<3> bfd_9_ bfd_7_ DVDD DVSS net050_0_ AN2D1LVT
XI256<2> bfd_9_ bzfd_7_ DVDD DVSS net050_1_ AN2D1LVT
XI256<1> bzfd_9_ bfd_7_ DVDD DVSS net050_2_ AN2D1LVT
XI256<0> bzfd_9_ bzfd_7_ DVDD DVSS net050_3_ AN2D1LVT
XI254<3> bfd_10_ bfd_7_ DVDD DVSS net051_0_ AN2D1LVT
XI254<2> bfd_10_ bzfd_7_ DVDD DVSS net051_1_ AN2D1LVT
XI254<1> bzfd_10_ bfd_7_ DVDD DVSS net051_2_ AN2D1LVT
XI254<0> bzfd_10_ bzfd_7_ DVDD DVSS net051_3_ AN2D1LVT
XI165<3> bfd_11_ bfd_7_ DVDD DVSS net052_0_ AN2D1LVT
XI165<2> bfd_11_ bzfd_7_ DVDD DVSS net052_1_ AN2D1LVT
XI165<1> bzfd_11_ bfd_7_ DVDD DVSS net052_2_ AN2D1LVT
XI165<0> bzfd_11_ bzfd_7_ DVDD DVSS net052_3_ AN2D1LVT
XI252<3> bfd_11_ BFD_3_ DVDD DVSS net080_0_ AN2D1LVT
XI252<2> bfd_11_ BZFD_3_ DVDD DVSS net080_1_ AN2D1LVT
XI252<1> bzfd_11_ BFD_3_ DVDD DVSS net080_2_ AN2D1LVT
XI252<0> bzfd_11_ BZFD_3_ DVDD DVSS net080_3_ AN2D1LVT
XI176<3> bfd_6_ bfd_5_ DVDD DVSS net037_0_ AN2D1LVT
XI176<2> bfd_6_ bzfd_5_ DVDD DVSS net037_1_ AN2D1LVT
XI176<1> bzfd_6_ bfd_5_ DVDD DVSS net037_2_ AN2D1LVT
XI176<0> bzfd_6_ bzfd_5_ DVDD DVSS net037_3_ AN2D1LVT
XI173<3> bfd_2_ bfd_1_ DVDD DVSS net038_0_ AN2D1LVT
XI173<2> bfd_2_ bzfd_1_ DVDD DVSS net038_1_ AN2D1LVT
XI173<1> bzfd_2_ bfd_1_ DVDD DVSS net038_2_ AN2D1LVT
XI173<0> bzfd_2_ bzfd_1_ DVDD DVSS net038_3_ AN2D1LVT
XI168<3> BFD_8_ BFD_3_ DVDD DVSS net045_0_ AN2D1LVT
XI168<2> BFD_8_ BZFD_3_ DVDD DVSS net045_1_ AN2D1LVT
XI168<1> BZFD_8_ BFD_3_ DVDD DVSS net045_2_ AN2D1LVT
XI168<0> BZFD_8_ BZFD_3_ DVDD DVSS net045_3_ AN2D1LVT
XI167<3> bfd_9_ BFD_3_ DVDD DVSS net046_0_ AN2D1LVT
XI167<2> bfd_9_ BZFD_3_ DVDD DVSS net046_1_ AN2D1LVT
XI167<1> bzfd_9_ BFD_3_ DVDD DVSS net046_2_ AN2D1LVT
XI167<0> bzfd_9_ BZFD_3_ DVDD DVSS net046_3_ AN2D1LVT
.ENDS

************************************************************************
* Library Name: AP_SerDes
* Cell Name:    ENC_8l12b_v2_tspc
* View Name:    schematic
************************************************************************

.SUBCKT ENC_8l12b_v2_tspc A_7_ A_6_ A_5_ A_4_ A_3_ A_2_ A_1_ A_0_ B_7_ B_6_
+ B_5_ B_4_ B_3_ B_2_ B_1_ B_0_ C_7_ C_6_ C_5_ C_4_ C_3_ C_2_ C_1_ C_0_ CLK
+ D_7_ D_6_ D_5_ D_4_ D_3_ D_2_ D_1_ D_0_ DIN_11_ DIN_10_ DIN_9_ DIN_8_ DIN_7_
+ DIN_6_ DIN_5_ DIN_4_ DIN_3_ DIN_2_ DIN_1_ DIN_0_ DVDD DVSS E_7_ E_6_ E_5_
+ E_4_ E_3_ E_2_ E_1_ E_0_ F_7_ F_6_ F_5_ F_4_ F_3_ F_2_ F_1_ F_0_ G_7_ G_6_
+ G_5_ G_4_ G_3_ G_2_ G_1_ G_0_ H_7_ H_6_ H_5_ H_4_ H_3_ H_2_ H_1_ H_0_
*.PININFO CLK:I DIN_11_:I DIN_10_:I DIN_9_:I DIN_8_:I DIN_7_:I DIN_6_:I
*.PININFO DIN_5_:I DIN_4_:I DIN_3_:I DIN_2_:I DIN_1_:I DIN_0_:I A_7_:O A_6_:O
*.PININFO A_5_:O A_4_:O A_3_:O A_2_:O A_1_:O A_0_:O B_7_:O B_6_:O B_5_:O
*.PININFO B_4_:O B_3_:O B_2_:O B_1_:O B_0_:O C_7_:O C_6_:O C_5_:O C_4_:O
*.PININFO C_3_:O C_2_:O C_1_:O C_0_:O D_7_:O D_6_:O D_5_:O D_4_:O D_3_:O
*.PININFO D_2_:O D_1_:O D_0_:O E_7_:O E_6_:O E_5_:O E_4_:O E_3_:O E_2_:O
*.PININFO E_1_:O E_0_:O F_7_:O F_6_:O F_5_:O F_4_:O F_3_:O F_2_:O F_1_:O
*.PININFO F_0_:O G_7_:O G_6_:O G_5_:O G_4_:O G_3_:O G_2_:O G_1_:O G_0_:O
*.PININFO H_7_:O H_6_:O H_5_:O H_4_:O H_3_:O H_2_:O H_1_:O H_0_:O DVDD:B DVSS:B
XI281<3> net064_0_ net063_0_ DVDD DVSS BZ_3_ NR2D1LVT
XI281<2> net064_1_ net063_1_ DVDD DVSS BZ_2_ NR2D1LVT
XI281<1> net064_2_ net063_2_ DVDD DVSS BZ_1_ NR2D1LVT
XI281<0> net064_3_ net063_3_ DVDD DVSS BZ_0_ NR2D1LVT
XI282<3> net0105_0_ net0110_0_ DVDD DVSS CZ_3_ NR2D1LVT
XI282<2> net0105_1_ net0110_1_ DVDD DVSS CZ_2_ NR2D1LVT
XI282<1> net0105_2_ net0110_2_ DVDD DVSS CZ_1_ NR2D1LVT
XI282<0> net0105_3_ net0110_3_ DVDD DVSS CZ_0_ NR2D1LVT
XI280<3> net0109_0_ net0111_0_ DVDD DVSS AZ_3_ NR2D1LVT
XI280<2> net0109_1_ net0111_1_ DVDD DVSS AZ_2_ NR2D1LVT
XI280<1> net0109_2_ net0111_2_ DVDD DVSS AZ_1_ NR2D1LVT
XI280<0> net0109_3_ net0111_3_ DVDD DVSS AZ_0_ NR2D1LVT
XI284<3> net0119_0_ net0115_0_ DVDD DVSS EZ_3_ NR2D1LVT
XI284<2> net0119_1_ net0115_1_ DVDD DVSS EZ_2_ NR2D1LVT
XI284<1> net0119_2_ net0115_2_ DVDD DVSS EZ_1_ NR2D1LVT
XI284<0> net0119_3_ net0115_3_ DVDD DVSS EZ_0_ NR2D1LVT
XI216<3> net084_0_ net083_0_ DVDD DVSS H_7_ NR2D1LVT
XI216<2> net084_1_ net083_1_ DVDD DVSS H_6_ NR2D1LVT
XI216<1> net084_2_ net083_2_ DVDD DVSS H_5_ NR2D1LVT
XI216<0> net084_3_ net083_3_ DVDD DVSS H_4_ NR2D1LVT
XI215<3> net086_0_ net085_0_ DVDD DVSS G_7_ NR2D1LVT
XI215<2> net086_1_ net085_1_ DVDD DVSS G_6_ NR2D1LVT
XI215<1> net086_2_ net085_2_ DVDD DVSS G_5_ NR2D1LVT
XI215<0> net086_3_ net085_3_ DVDD DVSS G_4_ NR2D1LVT
XI214<3> net0107_0_ net0117_0_ DVDD DVSS F_7_ NR2D1LVT
XI214<2> net0107_1_ net0117_1_ DVDD DVSS F_6_ NR2D1LVT
XI214<1> net0107_2_ net0117_2_ DVDD DVSS F_5_ NR2D1LVT
XI214<0> net0107_3_ net0117_3_ DVDD DVSS F_4_ NR2D1LVT
XI212<3> net082_0_ net081_0_ DVDD DVSS D_7_ NR2D1LVT
XI212<2> net082_1_ net081_1_ DVDD DVSS D_6_ NR2D1LVT
XI212<1> net082_2_ net081_2_ DVDD DVSS D_5_ NR2D1LVT
XI212<0> net082_3_ net081_3_ DVDD DVSS D_4_ NR2D1LVT
XI213<3> net078_0_ net077_0_ DVDD DVSS E_7_ NR2D1LVT
XI213<2> net078_1_ net077_1_ DVDD DVSS E_6_ NR2D1LVT
XI213<1> net078_2_ net077_2_ DVDD DVSS E_5_ NR2D1LVT
XI213<0> net078_3_ net077_3_ DVDD DVSS E_4_ NR2D1LVT
XI283<3> net058_0_ net057_0_ DVDD DVSS DZ_3_ NR2D1LVT
XI283<2> net058_1_ net057_1_ DVDD DVSS DZ_2_ NR2D1LVT
XI283<1> net058_2_ net057_2_ DVDD DVSS DZ_1_ NR2D1LVT
XI283<0> net058_3_ net057_3_ DVDD DVSS DZ_0_ NR2D1LVT
XI285<3> net062_0_ net061_0_ DVDD DVSS FZ_3_ NR2D1LVT
XI285<2> net062_1_ net061_1_ DVDD DVSS FZ_2_ NR2D1LVT
XI285<1> net062_2_ net061_2_ DVDD DVSS FZ_1_ NR2D1LVT
XI285<0> net062_3_ net061_3_ DVDD DVSS FZ_0_ NR2D1LVT
XI286<3> net0113_0_ net0108_0_ DVDD DVSS GZ_3_ NR2D1LVT
XI286<2> net0113_1_ net0108_1_ DVDD DVSS GZ_2_ NR2D1LVT
XI286<1> net0113_2_ net0108_2_ DVDD DVSS GZ_1_ NR2D1LVT
XI286<0> net0113_3_ net0108_3_ DVDD DVSS GZ_0_ NR2D1LVT
XI287<3> net060_0_ net059_0_ DVDD DVSS HZ_3_ NR2D1LVT
XI287<2> net060_1_ net059_1_ DVDD DVSS HZ_2_ NR2D1LVT
XI287<1> net060_2_ net059_2_ DVDD DVSS HZ_1_ NR2D1LVT
XI287<0> net060_3_ net059_3_ DVDD DVSS HZ_0_ NR2D1LVT
XI209<3> net0106_0_ net0104_0_ DVDD DVSS A_7_ NR2D1LVT
XI209<2> net0106_1_ net0104_1_ DVDD DVSS A_6_ NR2D1LVT
XI209<1> net0106_2_ net0104_2_ DVDD DVSS A_5_ NR2D1LVT
XI209<0> net0106_3_ net0104_3_ DVDD DVSS A_4_ NR2D1LVT
XI211<3> net088_0_ net087_0_ DVDD DVSS C_7_ NR2D1LVT
XI211<2> net088_1_ net087_1_ DVDD DVSS C_6_ NR2D1LVT
XI211<1> net088_2_ net087_2_ DVDD DVSS C_5_ NR2D1LVT
XI211<0> net088_3_ net087_3_ DVDD DVSS C_4_ NR2D1LVT
XI210<3> net0102_0_ net0114_0_ DVDD DVSS B_7_ NR2D1LVT
XI210<2> net0102_1_ net0114_1_ DVDD DVSS B_6_ NR2D1LVT
XI210<1> net0102_2_ net0114_2_ DVDD DVSS B_5_ NR2D1LVT
XI210<0> net0102_3_ net0114_3_ DVDD DVSS B_4_ NR2D1LVT
XI224<3> HZ_3_ DVDD DVSS H_3_ INVD1LVT
XI224<2> HZ_2_ DVDD DVSS H_2_ INVD1LVT
XI224<1> HZ_1_ DVDD DVSS H_1_ INVD1LVT
XI224<0> HZ_0_ DVDD DVSS H_0_ INVD1LVT
XI223<3> GZ_3_ DVDD DVSS G_3_ INVD1LVT
XI223<2> GZ_2_ DVDD DVSS G_2_ INVD1LVT
XI223<1> GZ_1_ DVDD DVSS G_1_ INVD1LVT
XI223<0> GZ_0_ DVDD DVSS G_0_ INVD1LVT
XI222<3> FZ_3_ DVDD DVSS F_3_ INVD1LVT
XI222<2> FZ_2_ DVDD DVSS F_2_ INVD1LVT
XI222<1> FZ_1_ DVDD DVSS F_1_ INVD1LVT
XI222<0> FZ_0_ DVDD DVSS F_0_ INVD1LVT
XI221<3> EZ_3_ DVDD DVSS E_3_ INVD1LVT
XI221<2> EZ_2_ DVDD DVSS E_2_ INVD1LVT
XI221<1> EZ_1_ DVDD DVSS E_1_ INVD1LVT
XI221<0> EZ_0_ DVDD DVSS E_0_ INVD1LVT
XI217<3> AZ_3_ DVDD DVSS A_3_ INVD1LVT
XI217<2> AZ_2_ DVDD DVSS A_2_ INVD1LVT
XI217<1> AZ_1_ DVDD DVSS A_1_ INVD1LVT
XI217<0> AZ_0_ DVDD DVSS A_0_ INVD1LVT
XI220<3> DZ_3_ DVDD DVSS D_3_ INVD1LVT
XI220<2> DZ_2_ DVDD DVSS D_2_ INVD1LVT
XI220<1> DZ_1_ DVDD DVSS D_1_ INVD1LVT
XI220<0> DZ_0_ DVDD DVSS D_0_ INVD1LVT
XI219<3> CZ_3_ DVDD DVSS C_3_ INVD1LVT
XI219<2> CZ_2_ DVDD DVSS C_2_ INVD1LVT
XI219<1> CZ_1_ DVDD DVSS C_1_ INVD1LVT
XI219<0> CZ_0_ DVDD DVSS C_0_ INVD1LVT
XI218<3> BZ_3_ DVDD DVSS B_3_ INVD1LVT
XI218<2> BZ_2_ DVDD DVSS B_2_ INVD1LVT
XI218<1> BZ_1_ DVDD DVSS B_1_ INVD1LVT
XI218<0> BZ_0_ DVDD DVSS B_0_ INVD1LVT
XI0 CLK DEC20_3_ DEC20_2_ DEC20_1_ DEC20_0_ DEC21_3_ DEC21_2_ DEC21_1_
+ DEC21_0_ DEC64_3_ DEC64_2_ DEC64_1_ DEC64_0_ DEC65_3_ DEC65_2_ DEC65_1_
+ DEC65_0_ DEC83_3_ DEC83_2_ DEC83_1_ DEC83_0_ DEC87_3_ DEC87_2_ DEC87_1_
+ DEC87_0_ DEC93_3_ DEC93_2_ DEC93_1_ DEC93_0_ DEC97_3_ DEC97_2_ DEC97_1_
+ DEC97_0_ DEC103_3_ DEC103_2_ DEC103_1_ DEC103_0_ DEC107_3_ DEC107_2_
+ DEC107_1_ DEC107_0_ DEC113_3_ DEC113_2_ DEC113_1_ DEC113_0_ DEC117_3_
+ DEC117_2_ DEC117_1_ DEC117_0_ DIN_11_ DIN_10_ DIN_9_ DIN_8_ DIN_7_ DIN_6_
+ DIN_5_ DIN_4_ DIN_3_ DIN_2_ DIN_1_ DIN_0_ DVDD DVSS
+ ENC_8l12b_v2_tspc_stage2_v2
XI268<3> DEC97_0_ DEC64_1_ DVDD DVSS net0105_0_ AN2D1LVT
XI268<2> DEC97_0_ DEC64_0_ DVDD DVSS net0105_1_ AN2D1LVT
XI268<1> DEC97_1_ DEC64_1_ DVDD DVSS net0105_2_ AN2D1LVT
XI268<0> DEC97_1_ DEC64_0_ DVDD DVSS net0105_3_ AN2D1LVT
XI276<3> DEC97_2_ DEC64_2_ DVDD DVSS net0108_0_ AN2D1LVT
XI276<2> DEC97_2_ DEC64_3_ DVDD DVSS net0108_1_ AN2D1LVT
XI276<1> DEC97_3_ DEC64_2_ DVDD DVSS net0108_2_ AN2D1LVT
XI276<0> DEC97_3_ DEC64_3_ DVDD DVSS net0108_3_ AN2D1LVT
XI265<3> DEC87_0_ DEC64_0_ DVDD DVSS net058_0_ AN2D1LVT
XI265<2> DEC87_0_ DEC64_1_ DVDD DVSS net058_1_ AN2D1LVT
XI265<1> DEC87_0_ DEC65_3_ DVDD DVSS net058_2_ AN2D1LVT
XI265<0> DEC87_0_ DEC65_2_ DVDD DVSS net058_3_ AN2D1LVT
XI177<3> DEC113_3_ DEC21_1_ DVDD DVSS net0106_0_ AN2D1LVT
XI177<2> DEC113_3_ DEC21_0_ DVDD DVSS net0106_1_ AN2D1LVT
XI177<1> DEC113_2_ DEC21_1_ DVDD DVSS net0106_2_ AN2D1LVT
XI177<0> DEC113_2_ DEC21_0_ DVDD DVSS net0106_3_ AN2D1LVT
XI181<3> DEC93_2_ DEC20_1_ DVDD DVSS net088_0_ AN2D1LVT
XI181<2> DEC93_2_ DEC20_0_ DVDD DVSS net088_1_ AN2D1LVT
XI181<1> DEC93_3_ DEC20_1_ DVDD DVSS net088_2_ AN2D1LVT
XI181<0> DEC93_3_ DEC20_0_ DVDD DVSS net088_3_ AN2D1LVT
XI271<3> DEC117_1_ DEC65_1_ DVDD DVSS net0109_0_ AN2D1LVT
XI271<2> DEC117_1_ DEC65_0_ DVDD DVSS net0109_1_ AN2D1LVT
XI271<1> DEC117_0_ DEC65_1_ DVDD DVSS net0109_2_ AN2D1LVT
XI271<0> DEC117_0_ DEC65_0_ DVDD DVSS net0109_3_ AN2D1LVT
XI183<3> DEC83_2_ DEC20_0_ DVDD DVSS net082_0_ AN2D1LVT
XI183<2> DEC83_2_ DEC20_1_ DVDD DVSS net082_1_ AN2D1LVT
XI183<1> DEC83_2_ DEC21_3_ DVDD DVSS net082_2_ AN2D1LVT
XI183<0> DEC83_2_ DEC21_2_ DVDD DVSS net082_3_ AN2D1LVT
XI179<3> DEC103_2_ DEC20_3_ DVDD DVSS net0102_0_ AN2D1LVT
XI179<2> DEC103_2_ DEC20_2_ DVDD DVSS net0102_1_ AN2D1LVT
XI179<1> DEC103_2_ DEC21_0_ DVDD DVSS net0102_2_ AN2D1LVT
XI179<0> DEC103_2_ DEC21_1_ DVDD DVSS net0102_3_ AN2D1LVT
XI192<3> DEC83_0_ DEC20_0_ DVDD DVSS net084_0_ AN2D1LVT
XI192<2> DEC83_0_ DEC20_1_ DVDD DVSS net084_1_ AN2D1LVT
XI192<1> DEC83_0_ DEC21_3_ DVDD DVSS net084_2_ AN2D1LVT
XI192<0> DEC83_0_ DEC21_2_ DVDD DVSS net084_3_ AN2D1LVT
XI190<3> DEC93_0_ DEC20_1_ DVDD DVSS net086_0_ AN2D1LVT
XI190<2> DEC93_0_ DEC20_0_ DVDD DVSS net086_1_ AN2D1LVT
XI190<1> DEC93_1_ DEC20_1_ DVDD DVSS net086_2_ AN2D1LVT
XI190<0> DEC93_1_ DEC20_0_ DVDD DVSS net086_3_ AN2D1LVT
XI187<3> DEC103_0_ DEC20_3_ DVDD DVSS net0107_0_ AN2D1LVT
XI187<2> DEC103_0_ DEC20_2_ DVDD DVSS net0107_1_ AN2D1LVT
XI187<1> DEC103_0_ DEC21_0_ DVDD DVSS net0107_2_ AN2D1LVT
XI187<0> DEC103_0_ DEC21_1_ DVDD DVSS net0107_3_ AN2D1LVT
XI184<3> DEC113_1_ DEC21_1_ DVDD DVSS net078_0_ AN2D1LVT
XI184<2> DEC113_1_ DEC21_0_ DVDD DVSS net078_1_ AN2D1LVT
XI184<1> DEC113_0_ DEC21_1_ DVDD DVSS net078_2_ AN2D1LVT
XI184<0> DEC113_0_ DEC21_0_ DVDD DVSS net078_3_ AN2D1LVT
XI273<3> DEC87_1_ DEC65_3_ DVDD DVSS net057_0_ AN2D1LVT
XI273<2> DEC87_1_ DEC65_2_ DVDD DVSS net057_1_ AN2D1LVT
XI273<1> DEC87_1_ DEC64_0_ DVDD DVSS net057_2_ AN2D1LVT
XI273<0> DEC87_1_ DEC64_1_ DVDD DVSS net057_3_ AN2D1LVT
XI267<3> DEC97_0_ DEC64_2_ DVDD DVSS net0110_0_ AN2D1LVT
XI267<2> DEC97_0_ DEC64_3_ DVDD DVSS net0110_1_ AN2D1LVT
XI267<1> DEC97_1_ DEC64_2_ DVDD DVSS net0110_2_ AN2D1LVT
XI267<0> DEC97_1_ DEC64_3_ DVDD DVSS net0110_3_ AN2D1LVT
XI272<3> DEC117_3_ DEC65_2_ DVDD DVSS net0115_0_ AN2D1LVT
XI272<2> DEC117_3_ DEC65_3_ DVDD DVSS net0115_1_ AN2D1LVT
XI272<1> DEC117_2_ DEC65_2_ DVDD DVSS net0115_2_ AN2D1LVT
XI272<0> DEC117_2_ DEC65_3_ DVDD DVSS net0115_3_ AN2D1LVT
XI270<3> DEC117_1_ DEC65_2_ DVDD DVSS net0111_0_ AN2D1LVT
XI270<2> DEC117_1_ DEC65_3_ DVDD DVSS net0111_1_ AN2D1LVT
XI270<1> DEC117_0_ DEC65_2_ DVDD DVSS net0111_2_ AN2D1LVT
XI270<0> DEC117_0_ DEC65_3_ DVDD DVSS net0111_3_ AN2D1LVT
XI191<3> DEC83_1_ DEC21_3_ DVDD DVSS net083_0_ AN2D1LVT
XI191<2> DEC83_1_ DEC21_2_ DVDD DVSS net083_1_ AN2D1LVT
XI191<1> DEC83_1_ DEC20_0_ DVDD DVSS net083_2_ AN2D1LVT
XI191<0> DEC83_1_ DEC20_1_ DVDD DVSS net083_3_ AN2D1LVT
XI189<3> DEC93_0_ DEC20_2_ DVDD DVSS net085_0_ AN2D1LVT
XI189<2> DEC93_0_ DEC20_3_ DVDD DVSS net085_1_ AN2D1LVT
XI189<1> DEC93_1_ DEC20_2_ DVDD DVSS net085_2_ AN2D1LVT
XI189<0> DEC93_1_ DEC20_3_ DVDD DVSS net085_3_ AN2D1LVT
XI188<3> DEC103_1_ DEC21_0_ DVDD DVSS net0117_0_ AN2D1LVT
XI188<2> DEC103_1_ DEC21_1_ DVDD DVSS net0117_1_ AN2D1LVT
XI188<1> DEC103_1_ DEC20_3_ DVDD DVSS net0117_2_ AN2D1LVT
XI188<0> DEC103_1_ DEC20_2_ DVDD DVSS net0117_3_ AN2D1LVT
XI178<3> DEC113_3_ DEC21_2_ DVDD DVSS net0104_0_ AN2D1LVT
XI178<2> DEC113_3_ DEC21_3_ DVDD DVSS net0104_1_ AN2D1LVT
XI178<1> DEC113_2_ DEC21_2_ DVDD DVSS net0104_2_ AN2D1LVT
XI178<0> DEC113_2_ DEC21_3_ DVDD DVSS net0104_3_ AN2D1LVT
XI264<3> DEC107_1_ DEC65_0_ DVDD DVSS net063_0_ AN2D1LVT
XI264<2> DEC107_1_ DEC65_1_ DVDD DVSS net063_1_ AN2D1LVT
XI264<1> DEC107_1_ DEC64_3_ DVDD DVSS net063_2_ AN2D1LVT
XI264<0> DEC107_1_ DEC64_2_ DVDD DVSS net063_3_ AN2D1LVT
XI275<3> DEC107_3_ DEC65_0_ DVDD DVSS net061_0_ AN2D1LVT
XI275<2> DEC107_3_ DEC65_1_ DVDD DVSS net061_1_ AN2D1LVT
XI275<1> DEC107_3_ DEC64_3_ DVDD DVSS net061_2_ AN2D1LVT
XI275<0> DEC107_3_ DEC64_2_ DVDD DVSS net061_3_ AN2D1LVT
XI278<3> DEC87_3_ DEC65_3_ DVDD DVSS net059_0_ AN2D1LVT
XI278<2> DEC87_3_ DEC65_2_ DVDD DVSS net059_1_ AN2D1LVT
XI278<1> DEC87_3_ DEC64_0_ DVDD DVSS net059_2_ AN2D1LVT
XI278<0> DEC87_3_ DEC64_1_ DVDD DVSS net059_3_ AN2D1LVT
XI269<3> DEC117_3_ DEC65_1_ DVDD DVSS net0119_0_ AN2D1LVT
XI269<2> DEC117_3_ DEC65_0_ DVDD DVSS net0119_1_ AN2D1LVT
XI269<1> DEC117_2_ DEC65_1_ DVDD DVSS net0119_2_ AN2D1LVT
XI269<0> DEC117_2_ DEC65_0_ DVDD DVSS net0119_3_ AN2D1LVT
XI185<3> DEC113_1_ DEC21_2_ DVDD DVSS net077_0_ AN2D1LVT
XI185<2> DEC113_1_ DEC21_3_ DVDD DVSS net077_1_ AN2D1LVT
XI185<1> DEC113_0_ DEC21_2_ DVDD DVSS net077_2_ AN2D1LVT
XI185<0> DEC113_0_ DEC21_3_ DVDD DVSS net077_3_ AN2D1LVT
XI182<3> DEC93_2_ DEC20_2_ DVDD DVSS net087_0_ AN2D1LVT
XI182<2> DEC93_2_ DEC20_3_ DVDD DVSS net087_1_ AN2D1LVT
XI182<1> DEC93_3_ DEC20_2_ DVDD DVSS net087_2_ AN2D1LVT
XI182<0> DEC93_3_ DEC20_3_ DVDD DVSS net087_3_ AN2D1LVT
XI180<3> DEC103_3_ DEC21_0_ DVDD DVSS net0114_0_ AN2D1LVT
XI180<2> DEC103_3_ DEC21_1_ DVDD DVSS net0114_1_ AN2D1LVT
XI180<1> DEC103_3_ DEC20_3_ DVDD DVSS net0114_2_ AN2D1LVT
XI180<0> DEC103_3_ DEC20_2_ DVDD DVSS net0114_3_ AN2D1LVT
XI274<3> DEC107_2_ DEC64_3_ DVDD DVSS net062_0_ AN2D1LVT
XI274<2> DEC107_2_ DEC64_2_ DVDD DVSS net062_1_ AN2D1LVT
XI274<1> DEC107_2_ DEC65_0_ DVDD DVSS net062_2_ AN2D1LVT
XI274<0> DEC107_2_ DEC65_1_ DVDD DVSS net062_3_ AN2D1LVT
XI186<3> DEC83_3_ DEC21_3_ DVDD DVSS net081_0_ AN2D1LVT
XI186<2> DEC83_3_ DEC21_2_ DVDD DVSS net081_1_ AN2D1LVT
XI186<1> DEC83_3_ DEC20_0_ DVDD DVSS net081_2_ AN2D1LVT
XI186<0> DEC83_3_ DEC20_1_ DVDD DVSS net081_3_ AN2D1LVT
XI277<3> DEC97_2_ DEC64_1_ DVDD DVSS net0113_0_ AN2D1LVT
XI277<2> DEC97_2_ DEC64_0_ DVDD DVSS net0113_1_ AN2D1LVT
XI277<1> DEC97_3_ DEC64_1_ DVDD DVSS net0113_2_ AN2D1LVT
XI277<0> DEC97_3_ DEC64_0_ DVDD DVSS net0113_3_ AN2D1LVT
XI279<3> DEC87_2_ DEC64_0_ DVDD DVSS net060_0_ AN2D1LVT
XI279<2> DEC87_2_ DEC64_1_ DVDD DVSS net060_1_ AN2D1LVT
XI279<1> DEC87_2_ DEC65_3_ DVDD DVSS net060_2_ AN2D1LVT
XI279<0> DEC87_2_ DEC65_2_ DVDD DVSS net060_3_ AN2D1LVT
XI266<3> DEC107_0_ DEC64_3_ DVDD DVSS net064_0_ AN2D1LVT
XI266<2> DEC107_0_ DEC64_2_ DVDD DVSS net064_1_ AN2D1LVT
XI266<1> DEC107_0_ DEC65_0_ DVDD DVSS net064_2_ AN2D1LVT
XI266<0> DEC107_0_ DEC65_1_ DVDD DVSS net064_3_ AN2D1LVT
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    AN3D1LVT
* View Name:    schematic
************************************************************************

.SUBCKT AN3D1LVT A1 A2 A3 VDD VSS Z
*.PININFO A1:I A2:I A3:I Z:O VDD:B VSS:B
MM_u4-M_u6 net13 A3 VSS VSS lvtnfet l=LF w=WC
MM_u3-M_u2 Z net11 VSS VSS lvtnfet l=LF w=WE
MM_u4-M_u5 net5 A2 net13 VSS lvtnfet l=LF w=WC
MM_u4-M_u4 net11 A1 net5 VSS lvtnfet l=LF w=WC
MM_u3-M_u3 Z net11 VDD VDD lvtpfet l=LF w=WF
MM_u4-M_u3 net11 A3 VDD VDD lvtpfet l=LF w=WD
MM_u4-M_u1 net11 A1 VDD VDD lvtpfet l=LF w=WD
MM_u4-M_u2 net11 A2 VDD VDD lvtpfet l=LF w=WD
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    ND2D2LVT
* View Name:    schematic
************************************************************************

.SUBCKT ND2D2LVT A1 A2 VDD VSS ZN
*.PININFO A1:I A2:I ZN:O VDD:B VSS:B
MMU3_1-M_u1 ZN A1 VDD VDD lvtpfet l=LF w=WF
MMU3_1-M_u2 ZN A2 VDD VDD lvtpfet l=LF w=WF
MMU3_0-M_u2 ZN A2 VDD VDD lvtpfet l=LF w=WF
MMU3_0-M_u1 ZN A1 VDD VDD lvtpfet l=LF w=WF
MMU3_0-M_u4 net20 A2 VSS VSS lvtnfet l=LF w=WE
MMU3_1-M_u3 ZN A1 net28 VSS lvtnfet l=LF w=WE
MMU3_1-M_u4 net28 A2 VSS VSS lvtnfet l=LF w=WE
MMU3_0-M_u3 ZN A1 net20 VSS lvtnfet l=LF w=WE
.ENDS

************************************************************************
* Library Name: AP_SerDes
* Cell Name:    Equalizer_8l12b_v7_enable
* View Name:    schematic
************************************************************************

.SUBCKT Equalizer_8l12b_v7_enable DVDD DVSS X_0_ X_1_ X_2_ X_4_ X_5_ X_6_ X_7_
+ ctop_6_ ctop_5_ ctop_4_ ctop_3_ ctop_2_ ctop_1_ ctop_0_ en outx
*.PININFO X_0_:I X_1_:I X_2_:I X_4_:I X_5_:I X_6_:I X_7_:I en:I outx:O DVDD:B
*.PININFO DVSS:B ctop_6_:B ctop_5_:B ctop_4_:B ctop_3_:B ctop_2_:B ctop_1_:B
*.PININFO ctop_0_:B
XI6 net6 DVDD DVSS net020 INVD1LVT
XI3 net8 DVDD DVSS net030 INVD1LVT
C0 ctop_5_ outx cap_mom nv=32 nh=18 w=WA s=100n stm=3 spm=5
C1 ctop_4_ outx cap_mom nv=32 nh=18 w=WA s=100n stm=3 spm=5
C2 ctop_3_ outx cap_mom nv=32 nh=18 w=WA s=100n stm=3 spm=5
C5 ctop_6_ outx cap_mom nv=32 nh=18 w=WA s=100n stm=3 spm=5
C3 ctop_2_ outx cap_mom nv=32 nh=18 w=WA s=100n stm=3 spm=5
C4 ctop_1_ outx cap_mom nv=32 nh=18 w=WA s=100n stm=3 spm=5
C6 ctop_0_ outx cap_mom nv=32 nh=18 w=WA s=100n stm=3 spm=5
XI57 X_1_ en DVDD DVSS net026 ND2D1LVT
XI56 X_2_ en DVDD DVSS net027 ND2D1LVT
XI55 X_4_ en DVDD DVSS net028 ND2D1LVT
XI58 X_0_ en DVDD DVSS net6 ND2D1LVT
XI43 X_7_ en DVDD DVSS net8 ND2D1LVT
XI66 net025 DVDD DVSS Xeq_4_ INVD8LVT
XI30 net085 DVDD DVSS Xeq_5_ INVD8LVT
XI26 net066 DVDD DVSS Xeq_2_ INVD8LVT
XI47 net033 DVDD DVSS Xeq_3_ INVD8LVT
XI23 net090 DVDD DVSS Xeq_1_ INVD8LVT
XI19 net092 DVDD DVSS net094 INVD8LVT
XI16 net098 DVDD DVSS net096 INVD8LVT
XI53<1> X_7_ X_6_ en DVDD DVSS net04 AN3D1LVT
XI53<0> X_7_ X_6_ en DVDD DVSS net04 AN3D1LVT
XI0 Xeq_6_ DVDD DVSS ctop_6_ INVD16LVT
XI63 Xeq_1_ DVDD DVSS ctop_1_ INVD16LVT
XI60 Xeq_4_ DVDD DVSS ctop_4_ INVD16LVT
XI59 Xeq_5_ DVDD DVSS ctop_5_ INVD16LVT
XI52 net094 DVDD DVSS Xeq_0_ INVD16LVT
XI44 net096 DVDD DVSS Xeq_6_ INVD16LVT
XI61 Xeq_3_ DVDD DVSS ctop_3_ INVD16LVT
XI64 Xeq_0_ DVDD DVSS ctop_0_ INVD16LVT
XI62 Xeq_2_ DVDD DVSS ctop_2_ INVD16LVT
XI54 X_5_ en DVDD DVSS net029 AN2D1LVT
XI40<1> Xeq_4_ net023 DVDD DVSS net033 ND2D2LVT
XI40<0> Xeq_4_ net023 DVDD DVSS net033 ND2D2LVT
XI65 net04 net029 DVDD DVSS net025 ND2D2LVT
XI73 net015 net090 DVDD DVSS net021 ND2D2LVT
XI10 net026 net6 DVDD DVSS net063 ND2D2LVT
XI69 net021 DVDD DVSS net066 INVD4LVT
XI21 net063 DVDD DVSS net090 INVD4LVT
XI17 net095 DVDD DVSS net092 INVD4LVT
XI13 net099 DVDD DVSS net098 INVD4LVT
XI68 net028 DVDD DVSS net023 INVD2LVT
XI72 net027 DVDD DVSS net015 INVD2LVT
XI27 net04 DVDD DVSS net085 INVD2LVT
XI20 net020 DVDD DVSS net095 INVD2LVT
XI14 net030 DVDD DVSS net099 INVD2LVT
.ENDS

************************************************************************
* Library Name: AP_SerDes
* Cell Name:    Equalizer_8l12b_v7_ctrl
* View Name:    schematic
************************************************************************

.SUBCKT Equalizer_8l12b_v7_ctrl Ain_2_ Ain_1_ Ain_0_ Ain_7_ Ain_6_ Ain_5_
+ Ain_4_ Bin_2_ Bin_1_ Bin_0_ Bin_7_ Bin_6_ Bin_5_ Bin_4_ Cin_2_ Cin_1_ Cin_0_
+ Cin_7_ Cin_6_ Cin_5_ Cin_4_ DVDD DVSS Din_2_ Din_1_ Din_0_ Din_7_ Din_6_
+ Din_5_ Din_4_ EN_3_ EN_2_ EN_1_ EN_0_ Ein_2_ Ein_1_ Ein_0_ Ein_7_ Ein_6_
+ Ein_5_ Ein_4_ Fin_2_ Fin_1_ Fin_0_ Fin_7_ Fin_6_ Fin_5_ Fin_4_ Gin_2_ Gin_1_
+ Gin_0_ Gin_7_ Gin_6_ Gin_5_ Gin_4_ Hin_2_ Hin_1_ Hin_0_ Hin_7_ Hin_6_ Hin_5_
+ Hin_4_ Ta Tb Tc Td Te Tf Tg Th
*.PININFO Ain_2_:I Ain_1_:I Ain_0_:I Ain_7_:I Ain_6_:I Ain_5_:I Ain_4_:I
*.PININFO Bin_2_:I Bin_1_:I Bin_0_:I Bin_7_:I Bin_6_:I Bin_5_:I Bin_4_:I
*.PININFO Cin_2_:I Cin_1_:I Cin_0_:I Cin_7_:I Cin_6_:I Cin_5_:I Cin_4_:I
*.PININFO Din_2_:I Din_1_:I Din_0_:I Din_7_:I Din_6_:I Din_5_:I Din_4_:I
*.PININFO EN_3_:I EN_2_:I EN_1_:I EN_0_:I Ein_2_:I Ein_1_:I Ein_0_:I Ein_7_:I
*.PININFO Ein_6_:I Ein_5_:I Ein_4_:I Fin_2_:I Fin_1_:I Fin_0_:I Fin_7_:I
*.PININFO Fin_6_:I Fin_5_:I Fin_4_:I Gin_2_:I Gin_1_:I Gin_0_:I Gin_7_:I
*.PININFO Gin_6_:I Gin_5_:I Gin_4_:I Hin_2_:I Hin_1_:I Hin_0_:I Hin_7_:I
*.PININFO Hin_6_:I Hin_5_:I Hin_4_:I Ta:O Tb:O Tc:O Td:O Te:O Tf:O Tg:O Th:O
*.PININFO DVDD:B DVSS:B
XI3<7> DVDD DVSS Ain_0_ Ain_1_ Ain_2_ Ain_4_ Ain_5_ Ain_6_ Ain_7_ At0_6_
+ At0_5_ At0_4_ At0_3_ At0_2_ At0_1_ At0_0_ EN_0_ Ta
+ Equalizer_8l12b_v7_enable
XI3<6> DVDD DVSS Bin_0_ Bin_1_ Bin_2_ Bin_4_ Bin_5_ Bin_6_ Bin_7_ Bt0_6_
+ Bt0_5_ Bt0_4_ Bt0_3_ Bt0_2_ Bt0_1_ Bt0_0_ EN_0_ Tb
+ Equalizer_8l12b_v7_enable
XI3<5> DVDD DVSS Cin_0_ Cin_1_ Cin_2_ Cin_4_ Cin_5_ Cin_6_ Cin_7_ Ct0_6_
+ Ct0_5_ Ct0_4_ Ct0_3_ Ct0_2_ Ct0_1_ Ct0_0_ EN_0_ Tc
+ Equalizer_8l12b_v7_enable
XI3<4> DVDD DVSS Din_0_ Din_1_ Din_2_ Din_4_ Din_5_ Din_6_ Din_7_ Dt0_6_
+ Dt0_5_ Dt0_4_ Dt0_3_ Dt0_2_ Dt0_1_ Dt0_0_ EN_0_ Td
+ Equalizer_8l12b_v7_enable
XI3<3> DVDD DVSS Ein_0_ Ein_1_ Ein_2_ Ein_4_ Ein_5_ Ein_6_ Ein_7_ Et0_6_
+ Et0_5_ Et0_4_ Et0_3_ Et0_2_ Et0_1_ Et0_0_ EN_0_ Te
+ Equalizer_8l12b_v7_enable
XI3<2> DVDD DVSS Fin_0_ Fin_1_ Fin_2_ Fin_4_ Fin_5_ Fin_6_ Fin_7_ Ft0_6_
+ Ft0_5_ Ft0_4_ Ft0_3_ Ft0_2_ Ft0_1_ Ft0_0_ EN_0_ Tf
+ Equalizer_8l12b_v7_enable
XI3<1> DVDD DVSS Gin_0_ Gin_1_ Gin_2_ Gin_4_ Gin_5_ Gin_6_ Gin_7_ Gt0_6_
+ Gt0_5_ Gt0_4_ Gt0_3_ Gt0_2_ Gt0_1_ Gt0_0_ EN_0_ Tg
+ Equalizer_8l12b_v7_enable
XI3<0> DVDD DVSS Hin_0_ Hin_1_ Hin_2_ Hin_4_ Hin_5_ Hin_6_ Hin_7_ Ht0_6_
+ Ht0_5_ Ht0_4_ Ht0_3_ Ht0_2_ Ht0_1_ Ht0_0_ EN_0_ Th
+ Equalizer_8l12b_v7_enable
XI2<7> DVDD DVSS Ain_0_ Ain_1_ Ain_2_ Ain_4_ Ain_5_ Ain_6_ Ain_7_ At1_6_
+ At1_5_ At1_4_ At1_3_ At1_2_ At1_1_ At1_0_ EN_1_ Ta
+ Equalizer_8l12b_v7_enable
XI2<6> DVDD DVSS Bin_0_ Bin_1_ Bin_2_ Bin_4_ Bin_5_ Bin_6_ Bin_7_ Bt1_6_
+ Bt1_5_ Bt1_4_ Bt1_3_ Bt1_2_ Bt1_1_ Bt1_0_ EN_1_ Tb
+ Equalizer_8l12b_v7_enable
XI2<5> DVDD DVSS Cin_0_ Cin_1_ Cin_2_ Cin_4_ Cin_5_ Cin_6_ Cin_7_ Ct1_6_
+ Ct1_5_ Ct1_4_ Ct1_3_ Ct1_2_ Ct1_1_ Ct1_0_ EN_1_ Tc
+ Equalizer_8l12b_v7_enable
XI2<4> DVDD DVSS Din_0_ Din_1_ Din_2_ Din_4_ Din_5_ Din_6_ Din_7_ Dt1_6_
+ Dt1_5_ Dt1_4_ Dt1_3_ Dt1_2_ Dt1_1_ Dt1_0_ EN_1_ Td
+ Equalizer_8l12b_v7_enable
XI2<3> DVDD DVSS Ein_0_ Ein_1_ Ein_2_ Ein_4_ Ein_5_ Ein_6_ Ein_7_ Et1_6_
+ Et1_5_ Et1_4_ Et1_3_ Et1_2_ Et1_1_ Et1_0_ EN_1_ Te
+ Equalizer_8l12b_v7_enable
XI2<2> DVDD DVSS Fin_0_ Fin_1_ Fin_2_ Fin_4_ Fin_5_ Fin_6_ Fin_7_ Ft1_6_
+ Ft1_5_ Ft1_4_ Ft1_3_ Ft1_2_ Ft1_1_ Ft1_0_ EN_1_ Tf
+ Equalizer_8l12b_v7_enable
XI2<1> DVDD DVSS Gin_0_ Gin_1_ Gin_2_ Gin_4_ Gin_5_ Gin_6_ Gin_7_ Gt1_6_
+ Gt1_5_ Gt1_4_ Gt1_3_ Gt1_2_ Gt1_1_ Gt1_0_ EN_1_ Tg
+ Equalizer_8l12b_v7_enable
XI2<0> DVDD DVSS Hin_0_ Hin_1_ Hin_2_ Hin_4_ Hin_5_ Hin_6_ Hin_7_ Ht1_6_
+ Ht1_5_ Ht1_4_ Ht1_3_ Ht1_2_ Ht1_1_ Ht1_0_ EN_1_ Th
+ Equalizer_8l12b_v7_enable
XI0<7> DVDD DVSS Ain_0_ Ain_1_ Ain_2_ Ain_4_ Ain_5_ Ain_6_ Ain_7_ At3_6_
+ At3_5_ At3_4_ At3_3_ At3_2_ At3_1_ At3_0_ EN_3_ Ta
+ Equalizer_8l12b_v7_enable
XI0<6> DVDD DVSS Bin_0_ Bin_1_ Bin_2_ Bin_4_ Bin_5_ Bin_6_ Bin_7_ Bt3_6_
+ Bt3_5_ Bt3_4_ Bt3_3_ Bt3_2_ Bt3_1_ Bt3_0_ EN_3_ Tb
+ Equalizer_8l12b_v7_enable
XI0<5> DVDD DVSS Cin_0_ Cin_1_ Cin_2_ Cin_4_ Cin_5_ Cin_6_ Cin_7_ Ct3_6_
+ Ct3_5_ Ct3_4_ Ct3_3_ Ct3_2_ Ct3_1_ Ct3_0_ EN_3_ Tc
+ Equalizer_8l12b_v7_enable
XI0<4> DVDD DVSS Din_0_ Din_1_ Din_2_ Din_4_ Din_5_ Din_6_ Din_7_ Dt3_6_
+ Dt3_5_ Dt3_4_ Dt3_3_ Dt3_2_ Dt3_1_ Dt3_0_ EN_3_ Td
+ Equalizer_8l12b_v7_enable
XI0<3> DVDD DVSS Ein_0_ Ein_1_ Ein_2_ Ein_4_ Ein_5_ Ein_6_ Ein_7_ Et3_6_
+ Et3_5_ Et3_4_ Et3_3_ Et3_2_ Et3_1_ Et3_0_ EN_3_ Te
+ Equalizer_8l12b_v7_enable
XI0<2> DVDD DVSS Fin_0_ Fin_1_ Fin_2_ Fin_4_ Fin_5_ Fin_6_ Fin_7_ Ft3_6_
+ Ft3_5_ Ft3_4_ Ft3_3_ Ft3_2_ Ft3_1_ Ft3_0_ EN_3_ Tf
+ Equalizer_8l12b_v7_enable
XI0<1> DVDD DVSS Gin_0_ Gin_1_ Gin_2_ Gin_4_ Gin_5_ Gin_6_ Gin_7_ Gt3_6_
+ Gt3_5_ Gt3_4_ Gt3_3_ Gt3_2_ Gt3_1_ Gt3_0_ EN_3_ Tg
+ Equalizer_8l12b_v7_enable
XI0<0> DVDD DVSS Hin_0_ Hin_1_ Hin_2_ Hin_4_ Hin_5_ Hin_6_ Hin_7_ Ht3_6_
+ Ht3_5_ Ht3_4_ Ht3_3_ Ht3_2_ Ht3_1_ Ht3_0_ EN_3_ Th
+ Equalizer_8l12b_v7_enable
XI1<7> DVDD DVSS Ain_0_ Ain_1_ Ain_2_ Ain_4_ Ain_5_ Ain_6_ Ain_7_ At2_6_
+ At2_5_ At2_4_ At2_3_ At2_2_ At2_1_ At2_0_ EN_2_ Ta
+ Equalizer_8l12b_v7_enable
XI1<6> DVDD DVSS Bin_0_ Bin_1_ Bin_2_ Bin_4_ Bin_5_ Bin_6_ Bin_7_ Bt2_6_
+ Bt2_5_ Bt2_4_ Bt2_3_ Bt2_2_ Bt2_1_ Bt2_0_ EN_2_ Tb
+ Equalizer_8l12b_v7_enable
XI1<5> DVDD DVSS Cin_0_ Cin_1_ Cin_2_ Cin_4_ Cin_5_ Cin_6_ Cin_7_ Ct2_6_
+ Ct2_5_ Ct2_4_ Ct2_3_ Ct2_2_ Ct2_1_ Ct2_0_ EN_2_ Tc
+ Equalizer_8l12b_v7_enable
XI1<4> DVDD DVSS Din_0_ Din_1_ Din_2_ Din_4_ Din_5_ Din_6_ Din_7_ Dt2_6_
+ Dt2_5_ Dt2_4_ Dt2_3_ Dt2_2_ Dt2_1_ Dt2_0_ EN_2_ Td
+ Equalizer_8l12b_v7_enable
XI1<3> DVDD DVSS Ein_0_ Ein_1_ Ein_2_ Ein_4_ Ein_5_ Ein_6_ Ein_7_ Et2_6_
+ Et2_5_ Et2_4_ Et2_3_ Et2_2_ Et2_1_ Et2_0_ EN_2_ Te
+ Equalizer_8l12b_v7_enable
XI1<2> DVDD DVSS Fin_0_ Fin_1_ Fin_2_ Fin_4_ Fin_5_ Fin_6_ Fin_7_ Ft2_6_
+ Ft2_5_ Ft2_4_ Ft2_3_ Ft2_2_ Ft2_1_ Ft2_0_ EN_2_ Tf
+ Equalizer_8l12b_v7_enable
XI1<1> DVDD DVSS Gin_0_ Gin_1_ Gin_2_ Gin_4_ Gin_5_ Gin_6_ Gin_7_ Gt2_6_
+ Gt2_5_ Gt2_4_ Gt2_3_ Gt2_2_ Gt2_1_ Gt2_0_ EN_2_ Tg
+ Equalizer_8l12b_v7_enable
XI1<0> DVDD DVSS Hin_0_ Hin_1_ Hin_2_ Hin_4_ Hin_5_ Hin_6_ Hin_7_ Ht2_6_
+ Ht2_5_ Ht2_4_ Ht2_3_ Ht2_2_ Ht2_1_ Ht2_0_ EN_2_ Th
+ Equalizer_8l12b_v7_enable
.ENDS

************************************************************************
* Library Name: AP_SerDes
* Cell Name:    TX_8l12b
* View Name:    schematic
************************************************************************

.SUBCKT Sanitized_TX_8l12b AVDD AVSS CALIN1_3_ CALIN1_2_ CALIN1_1_ CALIN1_0_ CALIN3_3_
+ CALIN3_2_ CALIN3_1_ CALIN3_0_ CALIN5_3_ CALIN5_2_ CALIN5_1_ CALIN5_0_
+ CALIN7_3_ CALIN7_2_ CALIN7_1_ CALIN7_0_ CALIP1_3_ CALIP1_2_ CALIP1_1_
+ CALIP1_0_ CALIP3_3_ CALIP3_2_ CALIP3_1_ CALIP3_0_ CALIP5_3_ CALIP5_2_
+ CALIP5_1_ CALIP5_0_ CALIP7_3_ CALIP7_2_ CALIP7_1_ CALIP7_0_ CLKTXe CLKTXo
+ DINe_11_ DINe_10_ DINe_9_ DINe_8_ DINe_7_ DINe_6_ DINe_5_ DINe_4_ DINe_3_
+ DINe_2_ DINe_1_ DINe_0_ DINo_11_ DINo_10_ DINo_9_ DINo_8_ DINo_7_ DINo_6_
+ DINo_5_ DINo_4_ DINo_3_ DINo_2_ DINo_1_ DINo_0_ DVDD DVSS EQUA_EN_3_
+ EQUA_EN_2_ EQUA_EN_1_ EQUA_EN_0_ Ibg Ta Tb Tc Td Te Tf Tg Th ntx
*.PININFO CALIN1_3_:I CALIN1_2_:I CALIN1_1_:I CALIN1_0_:I CALIN3_3_:I
*.PININFO CALIN3_2_:I CALIN3_1_:I CALIN3_0_:I CALIN5_3_:I CALIN5_2_:I
*.PININFO CALIN5_1_:I CALIN5_0_:I CALIN7_3_:I CALIN7_2_:I CALIN7_1_:I
*.PININFO CALIN7_0_:I CALIP1_3_:I CALIP1_2_:I CALIP1_1_:I CALIP1_0_:I
*.PININFO CALIP3_3_:I CALIP3_2_:I CALIP3_1_:I CALIP3_0_:I CALIP5_3_:I
*.PININFO CALIP5_2_:I CALIP5_1_:I CALIP5_0_:I CALIP7_3_:I CALIP7_2_:I
*.PININFO CALIP7_1_:I CALIP7_0_:I CLKTXe:I CLKTXo:I DINe_11_:I DINe_10_:I
*.PININFO DINe_9_:I DINe_8_:I DINe_7_:I DINe_6_:I DINe_5_:I DINe_4_:I
*.PININFO DINe_3_:I DINe_2_:I DINe_1_:I DINe_0_:I DINo_11_:I DINo_10_:I
*.PININFO DINo_9_:I DINo_8_:I DINo_7_:I DINo_6_:I DINo_5_:I DINo_4_:I
*.PININFO DINo_3_:I DINo_2_:I DINo_1_:I DINo_0_:I EQUA_EN_3_:I EQUA_EN_2_:I
*.PININFO EQUA_EN_1_:I EQUA_EN_0_:I Ibg:I Ta:O Tb:O Tc:O Td:O Te:O Tf:O Tg:O
*.PININFO Th:O AVDD:B AVSS:B DVDD:B DVSS:B ntx:B
XI3 AVDD_Bias AVSS CALIN1_3_ CALIN1_2_ CALIN1_1_ CALIN1_0_ CALIN3_3_ CALIN3_2_
+ CALIN3_1_ CALIN3_0_ CALIN5_3_ CALIN5_2_ CALIN5_1_ CALIN5_0_ CALIN7_3_
+ CALIN7_2_ CALIN7_1_ CALIN7_0_ CALIP1_3_ CALIP1_2_ CALIP1_1_ CALIP1_0_
+ CALIP3_3_ CALIP3_2_ CALIP3_1_ CALIP3_0_ CALIP5_3_ CALIP5_2_ CALIP5_1_
+ CALIP5_0_ CALIP7_3_ CALIP7_2_ CALIP7_1_ CALIP7_0_ Ibg In_1m In_3m In_5m
+ In_7m Ip_1m Ip_3m Ip_5m Ip_7m Bias_v2
XI59 Ain_7_ Ain_6_ Ain_5_ Ain_4_ Ain_3_ Ain_2_ Ain_1_ Ain_0_ Ae_7_ Ae_6_ Ae_5_
+ Ae_4_ Ae_3_ Ae_2_ Ae_1_ Ae_0_ Ao_7_ Ao_6_ Ao_5_ Ao_4_ Ao_3_ Ao_2_ Ao_1_
+ Ao_0_ Bin_7_ Bin_6_ Bin_5_ Bin_4_ Bin_3_ Bin_2_ Bin_1_ Bin_0_ Be_7_ Be_6_
+ Be_5_ Be_4_ Be_3_ Be_2_ Be_1_ Be_0_ Bo_7_ Bo_6_ Bo_5_ Bo_4_ Bo_3_ Bo_2_
+ Bo_1_ Bo_0_ Cin_7_ Cin_6_ Cin_5_ Cin_4_ Cin_3_ Cin_2_ Cin_1_ Cin_0_ Ce_7_
+ Ce_6_ Ce_5_ Ce_4_ Ce_3_ Ce_2_ Ce_1_ Ce_0_ CLKTXo CLKTXe Co_7_ Co_6_ Co_5_
+ Co_4_ Co_3_ Co_2_ Co_1_ Co_0_ Din_7_ Din_6_ Din_5_ Din_4_ Din_3_ Din_2_
+ Din_1_ Din_0_ De_7_ De_6_ De_5_ De_4_ De_3_ De_2_ De_1_ De_0_ Do_7_ Do_6_
+ Do_5_ Do_4_ Do_3_ Do_2_ Do_1_ Do_0_ DVDD_MUX DVSS Ein_7_ Ein_6_ Ein_5_
+ Ein_4_ Ein_3_ Ein_2_ Ein_1_ Ein_0_ Ee_7_ Ee_6_ Ee_5_ Ee_4_ Ee_3_ Ee_2_ Ee_1_
+ Ee_0_ Eo_7_ Eo_6_ Eo_5_ Eo_4_ Eo_3_ Eo_2_ Eo_1_ Eo_0_ Fin_7_ Fin_6_ Fin_5_
+ Fin_4_ Fin_3_ Fin_2_ Fin_1_ Fin_0_ Fe_7_ Fe_6_ Fe_5_ Fe_4_ Fe_3_ Fe_2_ Fe_1_
+ Fe_0_ Fo_7_ Fo_6_ Fo_5_ Fo_4_ Fo_3_ Fo_2_ Fo_1_ Fo_0_ Gin_7_ Gin_6_ Gin_5_
+ Gin_4_ Gin_3_ Gin_2_ Gin_1_ Gin_0_ Ge_7_ Ge_6_ Ge_5_ Ge_4_ Ge_3_ Ge_2_ Ge_1_
+ Ge_0_ Go_7_ Go_6_ Go_5_ Go_4_ Go_3_ Go_2_ Go_1_ Go_0_ Hin_7_ Hin_6_ Hin_5_
+ Hin_4_ Hin_3_ Hin_2_ Hin_1_ Hin_0_ He_7_ He_6_ He_5_ He_4_ He_3_ He_2_ He_1_
+ He_0_ Ho_7_ Ho_6_ Ho_5_ Ho_4_ Ho_3_ Ho_2_ Ho_1_ Ho_0_ MUX2to1_dig
XI2 A_7_ A_6_ A_5_ A_4_ A_3_ A_2_ A_1_ A_0_ AVDD AVSS B_7_ B_6_ B_5_ B_4_
+ B_3_ B_2_ B_1_ B_0_ C_7_ C_6_ C_5_ C_4_ C_3_ C_2_ C_1_ C_0_ D_7_ D_6_ D_5_
+ D_4_ D_3_ D_2_ D_1_ D_0_ E_7_ E_6_ E_5_ E_4_ E_3_ E_2_ E_1_ E_0_ F_7_ F_6_
+ F_5_ F_4_ F_3_ F_2_ F_1_ F_0_ G_7_ G_6_ G_5_ G_4_ G_3_ G_2_ G_1_ G_0_ H_7_
+ H_6_ H_5_ H_4_ H_3_ H_2_ H_1_ H_0_ In_1m In_3m In_5m In_7m Ip_1m Ip_3m Ip_5m
+ Ip_7m ntx Ta Tb Tc Td Te Tf Tg Th CML_Driver_PAM8_woCS_v3
XI51 A_7_ A_6_ A_5_ A_4_ A_3_ A_2_ A_1_ A_0_ Ain_7_ Ain_6_ Ain_5_ Ain_4_
+ Ain_3_ Ain_2_ Ain_1_ Ain_0_ B_7_ B_6_ B_5_ B_4_ B_3_ B_2_ B_1_ B_0_ Bin_7_
+ Bin_6_ Bin_5_ Bin_4_ Bin_3_ Bin_2_ Bin_1_ Bin_0_ C_7_ C_6_ C_5_ C_4_ C_3_
+ C_2_ C_1_ C_0_ Cin_7_ Cin_6_ Cin_5_ Cin_4_ Cin_3_ Cin_2_ Cin_1_ Cin_0_ D_7_
+ D_6_ D_5_ D_4_ D_3_ D_2_ D_1_ D_0_ DVDD_PreDriver DVSS Din_7_ Din_6_ Din_5_
+ Din_4_ Din_3_ Din_2_ Din_1_ Din_0_ E_7_ E_6_ E_5_ E_4_ E_3_ E_2_ E_1_ E_0_
+ Ein_7_ Ein_6_ Ein_5_ Ein_4_ Ein_3_ Ein_2_ Ein_1_ Ein_0_ F_7_ F_6_ F_5_ F_4_
+ F_3_ F_2_ F_1_ F_0_ Fin_7_ Fin_6_ Fin_5_ Fin_4_ Fin_3_ Fin_2_ Fin_1_ Fin_0_
+ G_7_ G_6_ G_5_ G_4_ G_3_ G_2_ G_1_ G_0_ Gin_7_ Gin_6_ Gin_5_ Gin_4_ Gin_3_
+ Gin_2_ Gin_1_ Gin_0_ H_7_ H_6_ H_5_ H_4_ H_3_ H_2_ H_1_ H_0_ Hin_7_ Hin_6_
+ Hin_5_ Hin_4_ Hin_3_ Hin_2_ Hin_1_ Hin_0_ PreDriver_PAM8_v4
XI0<1> Ae_7_ Ae_6_ Ae_5_ Ae_4_ Ae_3_ Ae_2_ Ae_1_ Ae_0_ Be_7_ Be_6_ Be_5_ Be_4_
+ Be_3_ Be_2_ Be_1_ Be_0_ Ce_7_ Ce_6_ Ce_5_ Ce_4_ Ce_3_ Ce_2_ Ce_1_ Ce_0_
+ CLKTXe De_7_ De_6_ De_5_ De_4_ De_3_ De_2_ De_1_ De_0_ DINe_11_ DINe_10_
+ DINe_9_ DINe_8_ DINe_7_ DINe_6_ DINe_5_ DINe_4_ DINe_3_ DINe_2_ DINe_1_
+ DINe_0_ DVDD_ENC DVSS Ee_7_ Ee_6_ Ee_5_ Ee_4_ Ee_3_ Ee_2_ Ee_1_ Ee_0_ Fe_7_
+ Fe_6_ Fe_5_ Fe_4_ Fe_3_ Fe_2_ Fe_1_ Fe_0_ Ge_7_ Ge_6_ Ge_5_ Ge_4_ Ge_3_
+ Ge_2_ Ge_1_ Ge_0_ He_7_ He_6_ He_5_ He_4_ He_3_ He_2_ He_1_ He_0_
+ ENC_8l12b_v2_tspc
XI0<0> Ao_7_ Ao_6_ Ao_5_ Ao_4_ Ao_3_ Ao_2_ Ao_1_ Ao_0_ Bo_7_ Bo_6_ Bo_5_ Bo_4_
+ Bo_3_ Bo_2_ Bo_1_ Bo_0_ Co_7_ Co_6_ Co_5_ Co_4_ Co_3_ Co_2_ Co_1_ Co_0_
+ CLKTXo Do_7_ Do_6_ Do_5_ Do_4_ Do_3_ Do_2_ Do_1_ Do_0_ DINo_11_ DINo_10_
+ DINo_9_ DINo_8_ DINo_7_ DINo_6_ DINo_5_ DINo_4_ DINo_3_ DINo_2_ DINo_1_
+ DINo_0_ DVDD_ENC DVSS Eo_7_ Eo_6_ Eo_5_ Eo_4_ Eo_3_ Eo_2_ Eo_1_ Eo_0_ Fo_7_
+ Fo_6_ Fo_5_ Fo_4_ Fo_3_ Fo_2_ Fo_1_ Fo_0_ Go_7_ Go_6_ Go_5_ Go_4_ Go_3_
+ Go_2_ Go_1_ Go_0_ Ho_7_ Ho_6_ Ho_5_ Ho_4_ Ho_3_ Ho_2_ Ho_1_ Ho_0_
+ ENC_8l12b_v2_tspc
XI4 Ain_2_ Ain_1_ Ain_0_ Ain_7_ Ain_6_ Ain_5_ Ain_4_ Bin_2_ Bin_1_ Bin_0_
+ Bin_7_ Bin_6_ Bin_5_ Bin_4_ Cin_2_ Cin_1_ Cin_0_ Cin_7_ Cin_6_ Cin_5_ Cin_4_
+ DVDD_Equal DVSS Din_2_ Din_1_ Din_0_ Din_7_ Din_6_ Din_5_ Din_4_ EQUA_EN_3_
+ EQUA_EN_2_ EQUA_EN_1_ EQUA_EN_0_ Ein_2_ Ein_1_ Ein_0_ Ein_7_ Ein_6_ Ein_5_
+ Ein_4_ Fin_2_ Fin_1_ Fin_0_ Fin_7_ Fin_6_ Fin_5_ Fin_4_ Gin_2_ Gin_1_ Gin_0_
+ Gin_7_ Gin_6_ Gin_5_ Gin_4_ Hin_2_ Hin_1_ Hin_0_ Hin_7_ Hin_6_ Hin_5_ Hin_4_
+ Ta Tb Tc Td Te Tf Tg Th Equalizer_8l12b_v7_ctrl
.ENDS

