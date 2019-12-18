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

.SUBCKT Bias_v2 AVDD AVSS CALIN1[3] CALIN1[2] CALIN1[1] CALIN1[0] CALIN3[3] 
+ CALIN3[2] CALIN3[1] CALIN3[0] CALIN5[3] CALIN5[2] CALIN5[1] CALIN5[0] 
+ CALIN7[3] CALIN7[2] CALIN7[1] CALIN7[0] CALIP1[3] CALIP1[2] CALIP1[1] 
+ CALIP1[0] CALIP3[3] CALIP3[2] CALIP3[1] CALIP3[0] CALIP5[3] CALIP5[2] 
+ CALIP5[1] CALIP5[0] CALIP7[3] CALIP7[2] CALIP7[1] CALIP7[0] Ibg In_1m In_3m 
+ In_5m In_7m Ip_1m Ip_3m Ip_5m Ip_7m
*.PININFO CALIN1[3]:I CALIN1[2]:I CALIN1[1]:I CALIN1[0]:I CALIN3[3]:I 
*.PININFO CALIN3[2]:I CALIN3[1]:I CALIN3[0]:I CALIN5[3]:I CALIN5[2]:I 
*.PININFO CALIN5[1]:I CALIN5[0]:I CALIN7[3]:I CALIN7[2]:I CALIN7[1]:I 
*.PININFO CALIN7[0]:I CALIP1[3]:I CALIP1[2]:I CALIP1[1]:I CALIP1[0]:I 
*.PININFO CALIP3[3]:I CALIP3[2]:I CALIP3[1]:I CALIP3[0]:I CALIP5[3]:I 
*.PININFO CALIP5[2]:I CALIP5[1]:I CALIP5[0]:I CALIP7[3]:I CALIP7[2]:I 
*.PININFO CALIP7[1]:I CALIP7[0]:I AVDD:B AVSS:B Ibg:B In_1m:B In_3m:B In_5m:B 
*.PININFO In_7m:B Ip_1m:B Ip_3m:B Ip_5m:B Ip_7m:B
MM24<19> In_1m net0159 net0136[0] AVSS nch l=LA w=w3 m=20
MM24<18> In_1m net0159 net0136[1] AVSS nch l=LA w=w3 m=20
MM24<17> In_1m net0159 net0136[2] AVSS nch l=LA w=w3 m=20
MM24<16> In_1m net0159 net0136[3] AVSS nch l=LA w=w3 m=20
MM24<15> In_1m net0159 net0136[4] AVSS nch l=LA w=w3 m=20
MM24<14> In_1m net0159 net0136[5] AVSS nch l=LA w=w3 m=20
MM24<13> In_1m net0159 net0136[6] AVSS nch l=LA w=w3 m=20
MM24<12> In_1m net0159 net0136[7] AVSS nch l=LA w=w3 m=20
MM24<11> In_1m net0159 net0136[8] AVSS nch l=LA w=w3 m=20
MM24<10> In_1m net0159 net0136[9] AVSS nch l=LA w=w3 m=20
MM29<9> net0184[0] net0159 AVSS AVSS nch l=LA w=w4 m=140
MM29<8> net0184[1] net0159 AVSS AVSS nch l=LA w=w4 m=140
MM29<7> net0184[2] net0159 AVSS AVSS nch l=LA w=w4 m=140
MM29<6> net0184[3] net0159 AVSS AVSS nch l=LA w=w4 m=140
MM27<0> net073 net0159 AVSS AVSS nch l=LA w=w4 m=100
MM26<5> net0220[0] net0159 net0165[0] AVSS nch l=LA w=w3 m=60
MM26<4> net0220[1] net0159 net0165[1] AVSS nch l=LA w=w3 m=60
MM26<3> net0220[2] net0159 net0165[2] AVSS nch l=LA w=w3 m=60
MM25<9> net0162[0] net0159 AVSS AVSS nch l=LA w=w4 m=60
MM25<8> net0162[1] net0159 AVSS AVSS nch l=LA w=w4 m=60
MM25<7> net0162[2] net0159 AVSS AVSS nch l=LA w=w4 m=60
MM25<6> net0162[3] net0159 AVSS AVSS nch l=LA w=w4 m=60
MM23<0> net081 net0159 AVSS AVSS nch l=LA w=w4 m=20
MM29<5> net0187[0] net0159 AVSS AVSS nch l=LA w=w4 m=140
MM29<4> net0187[1] net0159 AVSS AVSS nch l=LA w=w4 m=140
MM29<3> net0187[2] net0159 AVSS AVSS nch l=LA w=w4 m=140
MM28<0> net0228 net0159 net073 AVSS nch l=LA w=w3 m=100
MM24<2> net0232[0] net0159 net0154[0] AVSS nch l=LA w=w3 m=20
MM24<1> net0232[1] net0159 net0154[1] AVSS nch l=LA w=w3 m=20
MM28<2> net0200[0] net0159 net0179[0] AVSS nch l=LA w=w3 m=100
MM28<1> net0200[1] net0159 net0179[1] AVSS nch l=LA w=w3 m=100
MM95<5> In_5m CALIN5[2] net0196[0] AVSS nch l=LD w=w1mn m=100
MM95<4> In_5m CALIN5[2] net0196[1] AVSS nch l=LD w=w1mn m=100
MM95<3> In_5m CALIN5[2] net0196[2] AVSS nch l=LD w=w1mn m=100
MM24<5> net0227[0] net0159 net0145[0] AVSS nch l=LA w=w3 m=20
MM24<4> net0227[1] net0159 net0145[1] AVSS nch l=LA w=w3 m=20
MM24<3> net0227[2] net0159 net0145[2] AVSS nch l=LA w=w3 m=20
MM23<9> net0140[0] net0159 AVSS AVSS nch l=LA w=w4 m=20
MM23<8> net0140[1] net0159 AVSS AVSS nch l=LA w=w4 m=20
MM23<7> net0140[2] net0159 AVSS AVSS nch l=LA w=w4 m=20
MM23<6> net0140[3] net0159 AVSS AVSS nch l=LA w=w4 m=20
MM27<9> net0173[0] net0159 AVSS AVSS nch l=LA w=w4 m=100
MM27<8> net0173[1] net0159 AVSS AVSS nch l=LA w=w4 m=100
MM27<7> net0173[2] net0159 AVSS AVSS nch l=LA w=w4 m=100
MM27<6> net0173[3] net0159 AVSS AVSS nch l=LA w=w4 m=100
MM25<0> net077 net0159 AVSS AVSS nch l=LA w=w4 m=60
MM100<5> In_7m CALIN7[2] net0210[0] AVSS nch l=LD w=w1mn m=140
MM100<4> In_7m CALIN7[2] net0210[1] AVSS nch l=LD w=w1mn m=140
MM100<3> In_7m CALIN7[2] net0210[2] AVSS nch l=LD w=w1mn m=140
MM99<2> In_7m CALIN7[1] net0214[0] AVSS nch l=LD w=w1mn m=140
MM99<1> In_7m CALIN7[1] net0214[1] AVSS nch l=LD w=w1mn m=140
MM98<0> In_7m CALIN7[0] net062 AVSS nch l=LD w=w1mn m=140
MM97<0> In_5m CALIN5[0] net0228 AVSS nch l=LD w=w1mn m=100
MM30<0> net062 net0159 net069 AVSS nch l=LA w=w3 m=140
MM23<5> net0145[0] net0159 AVSS AVSS nch l=LA w=w4 m=20
MM23<4> net0145[1] net0159 AVSS AVSS nch l=LA w=w4 m=20
MM23<3> net0145[2] net0159 AVSS AVSS nch l=LA w=w4 m=20
MM96<2> In_5m CALIN5[1] net0200[0] AVSS nch l=LD w=w1mn m=100
MM96<1> In_5m CALIN5[1] net0200[1] AVSS nch l=LD w=w1mn m=100
MM93<9> In_3m CALIN3[3] net0178[0] AVSS nch l=LD w=w1mn m=60
MM93<8> In_3m CALIN3[3] net0178[1] AVSS nch l=LD w=w1mn m=60
MM93<7> In_3m CALIN3[3] net0178[2] AVSS nch l=LD w=w1mn m=60
MM93<6> In_3m CALIN3[3] net0178[3] AVSS nch l=LD w=w1mn m=60
MM94<9> In_5m CALIN5[3] net0192[0] AVSS nch l=LD w=w1mn m=100
MM94<8> In_5m CALIN5[3] net0192[1] AVSS nch l=LD w=w1mn m=100
MM94<7> In_5m CALIN5[3] net0192[2] AVSS nch l=LD w=w1mn m=100
MM94<6> In_5m CALIN5[3] net0192[3] AVSS nch l=LD w=w1mn m=100
MM25<5> net0165[0] net0159 AVSS AVSS nch l=LA w=w4 m=60
MM25<4> net0165[1] net0159 AVSS AVSS nch l=LA w=w4 m=60
MM25<3> net0165[2] net0159 AVSS AVSS nch l=LA w=w4 m=60
MM74<9> In_1m CALIN1[3] net0157[0] AVSS nch l=LD w=w1mn m=20
MM74<8> In_1m CALIN1[3] net0157[1] AVSS nch l=LD w=w1mn m=20
MM74<7> In_1m CALIN1[3] net0157[2] AVSS nch l=LD w=w1mn m=20
MM74<6> In_1m CALIN1[3] net0157[3] AVSS nch l=LD w=w1mn m=20
MM90<0> In_3m CALIN3[0] net078 AVSS nch l=LD w=w1mn m=60
MM30<19> In_7m net0159 net0182[0] AVSS nch l=LA w=w3 m=140
MM30<18> In_7m net0159 net0182[1] AVSS nch l=LA w=w3 m=140
MM30<17> In_7m net0159 net0182[2] AVSS nch l=LA w=w3 m=140
MM30<16> In_7m net0159 net0182[3] AVSS nch l=LA w=w3 m=140
MM30<15> In_7m net0159 net0182[4] AVSS nch l=LA w=w3 m=140
MM30<14> In_7m net0159 net0182[5] AVSS nch l=LA w=w3 m=140
MM30<13> In_7m net0159 net0182[6] AVSS nch l=LA w=w3 m=140
MM30<12> In_7m net0159 net0182[7] AVSS nch l=LA w=w3 m=140
MM30<11> In_7m net0159 net0182[8] AVSS nch l=LA w=w3 m=140
MM30<10> In_7m net0159 net0182[9] AVSS nch l=LA w=w3 m=140
MM91<2> In_3m CALIN3[1] net0186[0] AVSS nch l=LD w=w1mn m=60
MM91<1> In_3m CALIN3[1] net0186[1] AVSS nch l=LD w=w1mn m=60
MM30<5> net0210[0] net0159 net0187[0] AVSS nch l=LA w=w3 m=140
MM30<4> net0210[1] net0159 net0187[1] AVSS nch l=LA w=w3 m=140
MM30<3> net0210[2] net0159 net0187[2] AVSS nch l=LA w=w3 m=140
MM28<19> In_5m net0159 net0171[0] AVSS nch l=LA w=w3 m=100
MM28<18> In_5m net0159 net0171[1] AVSS nch l=LA w=w3 m=100
MM28<17> In_5m net0159 net0171[2] AVSS nch l=LA w=w3 m=100
MM28<16> In_5m net0159 net0171[3] AVSS nch l=LA w=w3 m=100
MM28<15> In_5m net0159 net0171[4] AVSS nch l=LA w=w3 m=100
MM28<14> In_5m net0159 net0171[5] AVSS nch l=LA w=w3 m=100
MM28<13> In_5m net0159 net0171[6] AVSS nch l=LA w=w3 m=100
MM28<12> In_5m net0159 net0171[7] AVSS nch l=LA w=w3 m=100
MM28<11> In_5m net0159 net0171[8] AVSS nch l=LA w=w3 m=100
MM28<10> In_5m net0159 net0171[9] AVSS nch l=LA w=w3 m=100
MM28<5> net0196[0] net0159 net0176[0] AVSS nch l=LA w=w3 m=100
MM28<4> net0196[1] net0159 net0176[1] AVSS nch l=LA w=w3 m=100
MM28<3> net0196[2] net0159 net0176[2] AVSS nch l=LA w=w3 m=100
MM26<19> In_3m net0159 net0160[0] AVSS nch l=LA w=w3 m=60
MM26<18> In_3m net0159 net0160[1] AVSS nch l=LA w=w3 m=60
MM26<17> In_3m net0159 net0160[2] AVSS nch l=LA w=w3 m=60
MM26<16> In_3m net0159 net0160[3] AVSS nch l=LA w=w3 m=60
MM26<15> In_3m net0159 net0160[4] AVSS nch l=LA w=w3 m=60
MM26<14> In_3m net0159 net0160[5] AVSS nch l=LA w=w3 m=60
MM26<13> In_3m net0159 net0160[6] AVSS nch l=LA w=w3 m=60
MM26<12> In_3m net0159 net0160[7] AVSS nch l=LA w=w3 m=60
MM26<11> In_3m net0159 net0160[8] AVSS nch l=LA w=w3 m=60
MM26<10> In_3m net0159 net0160[9] AVSS nch l=LA w=w3 m=60
MM92<5> In_3m CALIN3[2] net0220[0] AVSS nch l=LD w=w1mn m=60
MM92<4> In_3m CALIN3[2] net0220[1] AVSS nch l=LD w=w1mn m=60
MM92<3> In_3m CALIN3[2] net0220[2] AVSS nch l=LD w=w1mn m=60
MM29<0> net069 net0159 AVSS AVSS nch l=LA w=w4 m=140
MM23<2> net0154[0] net0159 AVSS AVSS nch l=LA w=w4 m=20
MM23<1> net0154[1] net0159 AVSS AVSS nch l=LA w=w4 m=20
MM30<2> net0214[0] net0159 net0190[0] AVSS nch l=LA w=w3 m=140
MM30<1> net0214[1] net0159 net0190[1] AVSS nch l=LA w=w3 m=140
MM27<2> net0179[0] net0159 AVSS AVSS nch l=LA w=w4 m=100
MM27<1> net0179[1] net0159 AVSS AVSS nch l=LA w=w4 m=100
MM101<9> In_7m CALIN7[3] net0206[0] AVSS nch l=LD w=w1mn m=140
MM101<8> In_7m CALIN7[3] net0206[1] AVSS nch l=LD w=w1mn m=140
MM101<7> In_7m CALIN7[3] net0206[2] AVSS nch l=LD w=w1mn m=140
MM101<6> In_7m CALIN7[3] net0206[3] AVSS nch l=LD w=w1mn m=140
MM26<2> net0186[0] net0159 net0168[0] AVSS nch l=LA w=w3 m=60
MM26<1> net0186[1] net0159 net0168[1] AVSS nch l=LA w=w3 m=60
MM27<5> net0176[0] net0159 AVSS AVSS nch l=LA w=w4 m=100
MM27<4> net0176[1] net0159 AVSS AVSS nch l=LA w=w4 m=100
MM27<3> net0176[2] net0159 AVSS AVSS nch l=LA w=w4 m=100
MM26<0> net078 net0159 net077 AVSS nch l=LA w=w3 m=60
MM24<0> net0222 net0159 net081 AVSS nch l=LA w=w3 m=20
MM102<5> In_1m CALIN1[2] net0227[0] AVSS nch l=LD w=w1mn m=20
MM102<4> In_1m CALIN1[2] net0227[1] AVSS nch l=LD w=w1mn m=20
MM102<3> In_1m CALIN1[2] net0227[2] AVSS nch l=LD w=w1mn m=20
MM25<2> net0168[0] net0159 AVSS AVSS nch l=LA w=w4 m=60
MM25<1> net0168[1] net0159 AVSS AVSS nch l=LA w=w4 m=60
MM104<0> In_1m CALIN1[0] net0222 AVSS nch l=LD w=w1mn m=20
MM29<2> net0190[0] net0159 AVSS AVSS nch l=LA w=w4 m=140
MM29<1> net0190[1] net0159 AVSS AVSS nch l=LA w=w4 m=140
MM103<2> In_1m CALIN1[1] net0232[0] AVSS nch l=LD w=w1mn m=20
MM103<1> In_1m CALIN1[1] net0232[1] AVSS nch l=LD w=w1mn m=20
MM30<9> net0206[0] net0159 net0184[0] AVSS nch l=LA w=w3 m=140
MM30<8> net0206[1] net0159 net0184[1] AVSS nch l=LA w=w3 m=140
MM30<7> net0206[2] net0159 net0184[2] AVSS nch l=LA w=w3 m=140
MM30<6> net0206[3] net0159 net0184[3] AVSS nch l=LA w=w3 m=140
MM28<9> net0192[0] net0159 net0173[0] AVSS nch l=LA w=w3 m=100
MM28<8> net0192[1] net0159 net0173[1] AVSS nch l=LA w=w3 m=100
MM28<7> net0192[2] net0159 net0173[2] AVSS nch l=LA w=w3 m=100
MM28<6> net0192[3] net0159 net0173[3] AVSS nch l=LA w=w3 m=100
MM29<19> net0182[0] net0159 AVSS AVSS nch l=LA w=w4 m=140
MM29<18> net0182[1] net0159 AVSS AVSS nch l=LA w=w4 m=140
MM29<17> net0182[2] net0159 AVSS AVSS nch l=LA w=w4 m=140
MM29<16> net0182[3] net0159 AVSS AVSS nch l=LA w=w4 m=140
MM29<15> net0182[4] net0159 AVSS AVSS nch l=LA w=w4 m=140
MM29<14> net0182[5] net0159 AVSS AVSS nch l=LA w=w4 m=140
MM29<13> net0182[6] net0159 AVSS AVSS nch l=LA w=w4 m=140
MM29<12> net0182[7] net0159 AVSS AVSS nch l=LA w=w4 m=140
MM29<11> net0182[8] net0159 AVSS AVSS nch l=LA w=w4 m=140
MM29<10> net0182[9] net0159 AVSS AVSS nch l=LA w=w4 m=140
MM26<9> net0178[0] net0159 net0162[0] AVSS nch l=LA w=w3 m=60
MM26<8> net0178[1] net0159 net0162[1] AVSS nch l=LA w=w3 m=60
MM26<7> net0178[2] net0159 net0162[2] AVSS nch l=LA w=w3 m=60
MM26<6> net0178[3] net0159 net0162[3] AVSS nch l=LA w=w3 m=60
MM27<19> net0171[0] net0159 AVSS AVSS nch l=LA w=w4 m=100
MM27<18> net0171[1] net0159 AVSS AVSS nch l=LA w=w4 m=100
MM27<17> net0171[2] net0159 AVSS AVSS nch l=LA w=w4 m=100
MM27<16> net0171[3] net0159 AVSS AVSS nch l=LA w=w4 m=100
MM27<15> net0171[4] net0159 AVSS AVSS nch l=LA w=w4 m=100
MM27<14> net0171[5] net0159 AVSS AVSS nch l=LA w=w4 m=100
MM27<13> net0171[6] net0159 AVSS AVSS nch l=LA w=w4 m=100
MM27<12> net0171[7] net0159 AVSS AVSS nch l=LA w=w4 m=100
MM27<11> net0171[8] net0159 AVSS AVSS nch l=LA w=w4 m=100
MM27<10> net0171[9] net0159 AVSS AVSS nch l=LA w=w4 m=100
MM24<9> net0157[0] net0159 net0140[0] AVSS nch l=LA w=w3 m=20
MM24<8> net0157[1] net0159 net0140[1] AVSS nch l=LA w=w3 m=20
MM24<7> net0157[2] net0159 net0140[2] AVSS nch l=LA w=w3 m=20
MM24<6> net0157[3] net0159 net0140[3] AVSS nch l=LA w=w3 m=20
MM25<19> net0160[0] net0159 AVSS AVSS nch l=LA w=w4 m=60
MM25<18> net0160[1] net0159 AVSS AVSS nch l=LA w=w4 m=60
MM25<17> net0160[2] net0159 AVSS AVSS nch l=LA w=w4 m=60
MM25<16> net0160[3] net0159 AVSS AVSS nch l=LA w=w4 m=60
MM25<15> net0160[4] net0159 AVSS AVSS nch l=LA w=w4 m=60
MM25<14> net0160[5] net0159 AVSS AVSS nch l=LA w=w4 m=60
MM25<13> net0160[6] net0159 AVSS AVSS nch l=LA w=w4 m=60
MM25<12> net0160[7] net0159 AVSS AVSS nch l=LA w=w4 m=60
MM25<11> net0160[8] net0159 AVSS AVSS nch l=LA w=w4 m=60
MM25<10> net0160[9] net0159 AVSS AVSS nch l=LA w=w4 m=60
MM13<19> net0159 net0159 net067[0] AVSS nch l=LA w=w3 m=1
MM13<18> net0159 net0159 net067[1] AVSS nch l=LA w=w3 m=1
MM13<17> net0159 net0159 net067[2] AVSS nch l=LA w=w3 m=1
MM13<16> net0159 net0159 net067[3] AVSS nch l=LA w=w3 m=1
MM13<15> net0159 net0159 net067[4] AVSS nch l=LA w=w3 m=1
MM13<14> net0159 net0159 net067[5] AVSS nch l=LA w=w3 m=1
MM13<13> net0159 net0159 net067[6] AVSS nch l=LA w=w3 m=1
MM13<12> net0159 net0159 net067[7] AVSS nch l=LA w=w3 m=1
MM13<11> net0159 net0159 net067[8] AVSS nch l=LA w=w3 m=1
MM13<10> net0159 net0159 net067[9] AVSS nch l=LA w=w3 m=1
MM13<9> net0159 net0159 net067[10] AVSS nch l=LA w=w3 m=1
MM13<8> net0159 net0159 net067[11] AVSS nch l=LA w=w3 m=1
MM13<7> net0159 net0159 net067[12] AVSS nch l=LA w=w3 m=1
MM13<6> net0159 net0159 net067[13] AVSS nch l=LA w=w3 m=1
MM13<5> net0159 net0159 net067[14] AVSS nch l=LA w=w3 m=1
MM13<4> net0159 net0159 net067[15] AVSS nch l=LA w=w3 m=1
MM13<3> net0159 net0159 net067[16] AVSS nch l=LA w=w3 m=1
MM13<2> net0159 net0159 net067[17] AVSS nch l=LA w=w3 m=1
MM13<1> net0159 net0159 net067[18] AVSS nch l=LA w=w3 m=1
MM13<0> net0159 net0159 net067[19] AVSS nch l=LA w=w3 m=1
MM23<19> net0136[0] net0159 AVSS AVSS nch l=LA w=w4 m=20
MM23<18> net0136[1] net0159 AVSS AVSS nch l=LA w=w4 m=20
MM23<17> net0136[2] net0159 AVSS AVSS nch l=LA w=w4 m=20
MM23<16> net0136[3] net0159 AVSS AVSS nch l=LA w=w4 m=20
MM23<15> net0136[4] net0159 AVSS AVSS nch l=LA w=w4 m=20
MM23<14> net0136[5] net0159 AVSS AVSS nch l=LA w=w4 m=20
MM23<13> net0136[6] net0159 AVSS AVSS nch l=LA w=w4 m=20
MM23<12> net0136[7] net0159 AVSS AVSS nch l=LA w=w4 m=20
MM23<11> net0136[8] net0159 AVSS AVSS nch l=LA w=w4 m=20
MM23<10> net0136[9] net0159 AVSS AVSS nch l=LA w=w4 m=20
MM14<19> net067[0] net0159 AVSS AVSS nch l=LA w=w4 m=1
MM14<18> net067[1] net0159 AVSS AVSS nch l=LA w=w4 m=1
MM14<17> net067[2] net0159 AVSS AVSS nch l=LA w=w4 m=1
MM14<16> net067[3] net0159 AVSS AVSS nch l=LA w=w4 m=1
MM14<15> net067[4] net0159 AVSS AVSS nch l=LA w=w4 m=1
MM14<14> net067[5] net0159 AVSS AVSS nch l=LA w=w4 m=1
MM14<13> net067[6] net0159 AVSS AVSS nch l=LA w=w4 m=1
MM14<12> net067[7] net0159 AVSS AVSS nch l=LA w=w4 m=1
MM14<11> net067[8] net0159 AVSS AVSS nch l=LA w=w4 m=1
MM14<10> net067[9] net0159 AVSS AVSS nch l=LA w=w4 m=1
MM14<9> net067[10] net0159 AVSS AVSS nch l=LA w=w4 m=1
MM14<8> net067[11] net0159 AVSS AVSS nch l=LA w=w4 m=1
MM14<7> net067[12] net0159 AVSS AVSS nch l=LA w=w4 m=1
MM14<6> net067[13] net0159 AVSS AVSS nch l=LA w=w4 m=1
MM14<5> net067[14] net0159 AVSS AVSS nch l=LA w=w4 m=1
MM14<4> net067[15] net0159 AVSS AVSS nch l=LA w=w4 m=1
MM14<3> net067[16] net0159 AVSS AVSS nch l=LA w=w4 m=1
MM14<2> net067[17] net0159 AVSS AVSS nch l=LA w=w4 m=1
MM14<1> net067[18] net0159 AVSS AVSS nch l=LA w=w4 m=1
MM14<0> net067[19] net0159 AVSS AVSS nch l=LA w=w4 m=1
MM4 net011 Ibg AVSS AVSS nch l=LE w=w m=1
MM3 Ibg Ibg AVSS AVSS nch l=LE w=w m=1
MM33<9> net0163[0] net011 net089[0] AVDD pch l=LA w=w2p m=60
MM33<8> net0163[1] net011 net089[1] AVDD pch l=LA w=w2p m=60
MM33<7> net0163[2] net011 net089[2] AVDD pch l=LA w=w2p m=60
MM33<6> net0163[3] net011 net089[3] AVDD pch l=LA w=w2p m=60
MM82<2> Ip_5m CALIP5[1] net0180[0] AVDD pch l=LB w=w1m m=100
MM82<1> Ip_5m CALIP5[1] net0180[1] AVDD pch l=LB w=w1m m=100
MM31<0> net0107 net011 AVDD AVDD pch l=LA w=w3p m=20
MM33<2> net0169[0] net011 net091[0] AVDD pch l=LA w=w2p m=60
MM33<1> net0169[1] net011 net091[1] AVDD pch l=LA w=w2p m=60
MM86<5> Ip_7m CALIP7[2] net0188[0] AVDD pch l=LB w=w1m m=140
MM86<4> Ip_7m CALIP7[2] net0188[1] AVDD pch l=LB w=w1m m=140
MM86<3> Ip_7m CALIP7[2] net0188[2] AVDD pch l=LB w=w1m m=140
MM85<2> Ip_7m CALIP7[1] net0191[0] AVDD pch l=LB w=w1m m=140
MM85<1> Ip_7m CALIP7[1] net0191[1] AVDD pch l=LB w=w1m m=140
MM84<0> Ip_7m CALIP7[0] net057 AVDD pch l=LB w=w1m m=140
MM83<0> Ip_5m CALIP5[0] net0195 AVDD pch l=LB w=w1m m=100
MM38<0> net041 net011 AVDD AVDD pch l=LA w=w3p m=140
MM31<5> net085[0] net011 AVDD AVDD pch l=LA w=w3p m=20
MM31<4> net085[1] net011 AVDD AVDD pch l=LA w=w3p m=20
MM31<3> net085[2] net011 AVDD AVDD pch l=LA w=w3p m=20
MM37<2> net0191[0] net011 net0101[0] AVDD pch l=LA w=w2p m=140
MM37<1> net0191[1] net011 net0101[1] AVDD pch l=LA w=w2p m=140
MM36<5> net0177[0] net011 net096[0] AVDD pch l=LA w=w2p m=100
MM36<4> net0177[1] net011 net096[1] AVDD pch l=LA w=w2p m=100
MM36<3> net0177[2] net011 net096[2] AVDD pch l=LA w=w2p m=100
MM87<9> Ip_7m CALIP7[3] net0185[0] AVDD pch l=LB w=w1m m=140
MM87<8> Ip_7m CALIP7[3] net0185[1] AVDD pch l=LB w=w1m m=140
MM87<7> Ip_7m CALIP7[3] net0185[2] AVDD pch l=LB w=w1m m=140
MM87<6> Ip_7m CALIP7[3] net0185[3] AVDD pch l=LB w=w1m m=140
MM32<2> net0113[0] net011 net086[0] AVDD pch l=LA w=w2p m=20
MM32<1> net0113[1] net011 net086[1] AVDD pch l=LA w=w2p m=20
MM81<5> Ip_5m CALIP5[2] net0177[0] AVDD pch l=LB w=w1m m=100
MM81<4> Ip_5m CALIP5[2] net0177[1] AVDD pch l=LB w=w1m m=100
MM81<3> Ip_5m CALIP5[2] net0177[2] AVDD pch l=LB w=w1m m=100
MM80<9> Ip_5m CALIP5[3] net0174[0] AVDD pch l=LB w=w1m m=100
MM80<8> Ip_5m CALIP5[3] net0174[1] AVDD pch l=LB w=w1m m=100
MM80<7> Ip_5m CALIP5[3] net0174[2] AVDD pch l=LB w=w1m m=100
MM80<6> Ip_5m CALIP5[3] net0174[3] AVDD pch l=LB w=w1m m=100
MM79<9> Ip_3m CALIP3[3] net0163[0] AVDD pch l=LB w=w1m m=60
MM79<8> Ip_3m CALIP3[3] net0163[1] AVDD pch l=LB w=w1m m=60
MM79<7> Ip_3m CALIP3[3] net0163[2] AVDD pch l=LB w=w1m m=60
MM79<6> Ip_3m CALIP3[3] net0163[3] AVDD pch l=LB w=w1m m=60
MM36<9> net0174[0] net011 net095[0] AVDD pch l=LA w=w2p m=100
MM36<8> net0174[1] net011 net095[1] AVDD pch l=LA w=w2p m=100
MM36<7> net0174[2] net011 net095[2] AVDD pch l=LA w=w2p m=100
MM36<6> net0174[3] net011 net095[3] AVDD pch l=LA w=w2p m=100
MM78<5> Ip_3m CALIP3[2] net0166[0] AVDD pch l=LB w=w1m m=60
MM78<4> Ip_3m CALIP3[2] net0166[1] AVDD pch l=LB w=w1m m=60
MM78<3> Ip_3m CALIP3[2] net0166[2] AVDD pch l=LB w=w1m m=60
MM37<0> net057 net011 net041 AVDD pch l=LA w=w2p m=140
MM32<0> net0117 net011 net0107 AVDD pch l=LA w=w2p m=20
MM35<5> net096[0] net011 AVDD AVDD pch l=LA w=w3p m=100
MM35<4> net096[1] net011 AVDD AVDD pch l=LA w=w3p m=100
MM35<3> net096[2] net011 AVDD AVDD pch l=LA w=w3p m=100
MM33<0> net033 net011 net0105 AVDD pch l=LA w=w2p m=60
MM31<2> net086[0] net011 AVDD AVDD pch l=LA w=w3p m=20
MM31<1> net086[1] net011 AVDD AVDD pch l=LA w=w3p m=20
MM36<2> net0180[0] net011 net097[0] AVDD pch l=LA w=w2p m=100
MM36<1> net0180[1] net011 net097[1] AVDD pch l=LA w=w2p m=100
MM34<2> net091[0] net011 AVDD AVDD pch l=LA w=w3p m=60
MM34<1> net091[1] net011 AVDD AVDD pch l=LA w=w3p m=60
MM31<9> net084[0] net011 AVDD AVDD pch l=LA w=w3p m=20
MM31<8> net084[1] net011 AVDD AVDD pch l=LA w=w3p m=20
MM31<7> net084[2] net011 AVDD AVDD pch l=LA w=w3p m=20
MM31<6> net084[3] net011 AVDD AVDD pch l=LA w=w3p m=20
MM35<2> net097[0] net011 AVDD AVDD pch l=LA w=w3p m=100
MM35<1> net097[1] net011 AVDD AVDD pch l=LA w=w3p m=100
MM34<0> net0105 net011 AVDD AVDD pch l=LA w=w3p m=60
MM38<2> net0101[0] net011 AVDD AVDD pch l=LA w=w3p m=140
MM38<1> net0101[1] net011 AVDD AVDD pch l=LA w=w3p m=140
MM32<5> net0125[0] net011 net085[0] AVDD pch l=LA w=w2p m=20
MM32<4> net0125[1] net011 net085[1] AVDD pch l=LA w=w2p m=20
MM32<3> net0125[2] net011 net085[2] AVDD pch l=LA w=w2p m=20
MM37<5> net0188[0] net011 net0100[0] AVDD pch l=LA w=w2p m=140
MM37<4> net0188[1] net011 net0100[1] AVDD pch l=LA w=w2p m=140
MM37<3> net0188[2] net011 net0100[2] AVDD pch l=LA w=w2p m=140
MM35<0> net0106 net011 AVDD AVDD pch l=LA w=w3p m=100
MM33<5> net0166[0] net011 net090[0] AVDD pch l=LA w=w2p m=60
MM33<4> net0166[1] net011 net090[1] AVDD pch l=LA w=w2p m=60
MM33<3> net0166[2] net011 net090[2] AVDD pch l=LA w=w2p m=60
MM32<9> net0124[0] net011 net084[0] AVDD pch l=LA w=w2p m=20
MM32<8> net0124[1] net011 net084[1] AVDD pch l=LA w=w2p m=20
MM32<7> net0124[2] net011 net084[2] AVDD pch l=LA w=w2p m=20
MM32<6> net0124[3] net011 net084[3] AVDD pch l=LA w=w2p m=20
MM35<19> net093[0] net011 AVDD AVDD pch l=LA w=w3p m=100
MM35<18> net093[1] net011 AVDD AVDD pch l=LA w=w3p m=100
MM35<17> net093[2] net011 AVDD AVDD pch l=LA w=w3p m=100
MM35<16> net093[3] net011 AVDD AVDD pch l=LA w=w3p m=100
MM35<15> net093[4] net011 AVDD AVDD pch l=LA w=w3p m=100
MM35<14> net093[5] net011 AVDD AVDD pch l=LA w=w3p m=100
MM35<13> net093[6] net011 AVDD AVDD pch l=LA w=w3p m=100
MM35<12> net093[7] net011 AVDD AVDD pch l=LA w=w3p m=100
MM35<11> net093[8] net011 AVDD AVDD pch l=LA w=w3p m=100
MM35<10> net093[9] net011 AVDD AVDD pch l=LA w=w3p m=100
MM31<19> net083[0] net011 AVDD AVDD pch l=LA w=w3p m=20
MM31<18> net083[1] net011 AVDD AVDD pch l=LA w=w3p m=20
MM31<17> net083[2] net011 AVDD AVDD pch l=LA w=w3p m=20
MM31<16> net083[3] net011 AVDD AVDD pch l=LA w=w3p m=20
MM31<15> net083[4] net011 AVDD AVDD pch l=LA w=w3p m=20
MM31<14> net083[5] net011 AVDD AVDD pch l=LA w=w3p m=20
MM31<13> net083[6] net011 AVDD AVDD pch l=LA w=w3p m=20
MM31<12> net083[7] net011 AVDD AVDD pch l=LA w=w3p m=20
MM31<11> net083[8] net011 AVDD AVDD pch l=LA w=w3p m=20
MM31<10> net083[9] net011 AVDD AVDD pch l=LA w=w3p m=20
MM72<9> Ip_1m CALIP1[3] net0124[0] AVDD pch l=LB w=w1m m=20
MM72<8> Ip_1m CALIP1[3] net0124[1] AVDD pch l=LB w=w1m m=20
MM72<7> Ip_1m CALIP1[3] net0124[2] AVDD pch l=LB w=w1m m=20
MM72<6> Ip_1m CALIP1[3] net0124[3] AVDD pch l=LB w=w1m m=20
MM76<0> Ip_3m CALIP3[0] net033 AVDD pch l=LB w=w1m m=60
MM72<0> Ip_1m CALIP1[0] net0117 AVDD pch l=LB w=w1m m=20
MM72<2> Ip_1m CALIP1[1] net0113[0] AVDD pch l=LB w=w1m m=20
MM72<1> Ip_1m CALIP1[1] net0113[1] AVDD pch l=LB w=w1m m=20
MM72<5> Ip_1m CALIP1[2] net0125[0] AVDD pch l=LB w=w1m m=20
MM72<4> Ip_1m CALIP1[2] net0125[1] AVDD pch l=LB w=w1m m=20
MM72<3> Ip_1m CALIP1[2] net0125[2] AVDD pch l=LB w=w1m m=20
MM38<19> net098[0] net011 AVDD AVDD pch l=LA w=w3p m=140
MM38<18> net098[1] net011 AVDD AVDD pch l=LA w=w3p m=140
MM38<17> net098[2] net011 AVDD AVDD pch l=LA w=w3p m=140
MM38<16> net098[3] net011 AVDD AVDD pch l=LA w=w3p m=140
MM38<15> net098[4] net011 AVDD AVDD pch l=LA w=w3p m=140
MM38<14> net098[5] net011 AVDD AVDD pch l=LA w=w3p m=140
MM38<13> net098[6] net011 AVDD AVDD pch l=LA w=w3p m=140
MM38<12> net098[7] net011 AVDD AVDD pch l=LA w=w3p m=140
MM38<11> net098[8] net011 AVDD AVDD pch l=LA w=w3p m=140
MM38<10> net098[9] net011 AVDD AVDD pch l=LA w=w3p m=140
MM77<2> Ip_3m CALIP3[1] net0169[0] AVDD pch l=LB w=w1m m=60
MM77<1> Ip_3m CALIP3[1] net0169[1] AVDD pch l=LB w=w1m m=60
MM37<9> net0185[0] net011 net099[0] AVDD pch l=LA w=w2p m=140
MM37<8> net0185[1] net011 net099[1] AVDD pch l=LA w=w2p m=140
MM37<7> net0185[2] net011 net099[2] AVDD pch l=LA w=w2p m=140
MM37<6> net0185[3] net011 net099[3] AVDD pch l=LA w=w2p m=140
MM36<0> net0195 net011 net0106 AVDD pch l=LA w=w2p m=100
MM38<5> net0100[0] net011 AVDD AVDD pch l=LA w=w3p m=140
MM38<4> net0100[1] net011 AVDD AVDD pch l=LA w=w3p m=140
MM38<3> net0100[2] net011 AVDD AVDD pch l=LA w=w3p m=140
MM34<19> net088[0] net011 AVDD AVDD pch l=LA w=w3p m=60
MM34<18> net088[1] net011 AVDD AVDD pch l=LA w=w3p m=60
MM34<17> net088[2] net011 AVDD AVDD pch l=LA w=w3p m=60
MM34<16> net088[3] net011 AVDD AVDD pch l=LA w=w3p m=60
MM34<15> net088[4] net011 AVDD AVDD pch l=LA w=w3p m=60
MM34<14> net088[5] net011 AVDD AVDD pch l=LA w=w3p m=60
MM34<13> net088[6] net011 AVDD AVDD pch l=LA w=w3p m=60
MM34<12> net088[7] net011 AVDD AVDD pch l=LA w=w3p m=60
MM34<11> net088[8] net011 AVDD AVDD pch l=LA w=w3p m=60
MM34<10> net088[9] net011 AVDD AVDD pch l=LA w=w3p m=60
MM38<9> net099[0] net011 AVDD AVDD pch l=LA w=w3p m=140
MM38<8> net099[1] net011 AVDD AVDD pch l=LA w=w3p m=140
MM38<7> net099[2] net011 AVDD AVDD pch l=LA w=w3p m=140
MM38<6> net099[3] net011 AVDD AVDD pch l=LA w=w3p m=140
MM37<19> Ip_7m net011 net098[0] AVDD pch l=LA w=w2p m=140
MM37<18> Ip_7m net011 net098[1] AVDD pch l=LA w=w2p m=140
MM37<17> Ip_7m net011 net098[2] AVDD pch l=LA w=w2p m=140
MM37<16> Ip_7m net011 net098[3] AVDD pch l=LA w=w2p m=140
MM37<15> Ip_7m net011 net098[4] AVDD pch l=LA w=w2p m=140
MM37<14> Ip_7m net011 net098[5] AVDD pch l=LA w=w2p m=140
MM37<13> Ip_7m net011 net098[6] AVDD pch l=LA w=w2p m=140
MM37<12> Ip_7m net011 net098[7] AVDD pch l=LA w=w2p m=140
MM37<11> Ip_7m net011 net098[8] AVDD pch l=LA w=w2p m=140
MM37<10> Ip_7m net011 net098[9] AVDD pch l=LA w=w2p m=140
MM35<9> net095[0] net011 AVDD AVDD pch l=LA w=w3p m=100
MM35<8> net095[1] net011 AVDD AVDD pch l=LA w=w3p m=100
MM35<7> net095[2] net011 AVDD AVDD pch l=LA w=w3p m=100
MM35<6> net095[3] net011 AVDD AVDD pch l=LA w=w3p m=100
MM34<9> net089[0] net011 AVDD AVDD pch l=LA w=w3p m=60
MM34<8> net089[1] net011 AVDD AVDD pch l=LA w=w3p m=60
MM34<7> net089[2] net011 AVDD AVDD pch l=LA w=w3p m=60
MM34<6> net089[3] net011 AVDD AVDD pch l=LA w=w3p m=60
MM36<19> Ip_5m net011 net093[0] AVDD pch l=LA w=w2p m=100
MM36<18> Ip_5m net011 net093[1] AVDD pch l=LA w=w2p m=100
MM36<17> Ip_5m net011 net093[2] AVDD pch l=LA w=w2p m=100
MM36<16> Ip_5m net011 net093[3] AVDD pch l=LA w=w2p m=100
MM36<15> Ip_5m net011 net093[4] AVDD pch l=LA w=w2p m=100
MM36<14> Ip_5m net011 net093[5] AVDD pch l=LA w=w2p m=100
MM36<13> Ip_5m net011 net093[6] AVDD pch l=LA w=w2p m=100
MM36<12> Ip_5m net011 net093[7] AVDD pch l=LA w=w2p m=100
MM36<11> Ip_5m net011 net093[8] AVDD pch l=LA w=w2p m=100
MM36<10> Ip_5m net011 net093[9] AVDD pch l=LA w=w2p m=100
MM33<19> Ip_3m net011 net088[0] AVDD pch l=LA w=w2p m=60
MM33<18> Ip_3m net011 net088[1] AVDD pch l=LA w=w2p m=60
MM33<17> Ip_3m net011 net088[2] AVDD pch l=LA w=w2p m=60
MM33<16> Ip_3m net011 net088[3] AVDD pch l=LA w=w2p m=60
MM33<15> Ip_3m net011 net088[4] AVDD pch l=LA w=w2p m=60
MM33<14> Ip_3m net011 net088[5] AVDD pch l=LA w=w2p m=60
MM33<13> Ip_3m net011 net088[6] AVDD pch l=LA w=w2p m=60
MM33<12> Ip_3m net011 net088[7] AVDD pch l=LA w=w2p m=60
MM33<11> Ip_3m net011 net088[8] AVDD pch l=LA w=w2p m=60
MM33<10> Ip_3m net011 net088[9] AVDD pch l=LA w=w2p m=60
MM34<5> net090[0] net011 AVDD AVDD pch l=LA w=w3p m=60
MM34<4> net090[1] net011 AVDD AVDD pch l=LA w=w3p m=60
MM34<3> net090[2] net011 AVDD AVDD pch l=LA w=w3p m=60
MM32<19> Ip_1m net011 net083[0] AVDD pch l=LA w=w2p m=20
MM32<18> Ip_1m net011 net083[1] AVDD pch l=LA w=w2p m=20
MM32<17> Ip_1m net011 net083[2] AVDD pch l=LA w=w2p m=20
MM32<16> Ip_1m net011 net083[3] AVDD pch l=LA w=w2p m=20
MM32<15> Ip_1m net011 net083[4] AVDD pch l=LA w=w2p m=20
MM32<14> Ip_1m net011 net083[5] AVDD pch l=LA w=w2p m=20
MM32<13> Ip_1m net011 net083[6] AVDD pch l=LA w=w2p m=20
MM32<12> Ip_1m net011 net083[7] AVDD pch l=LA w=w2p m=20
MM32<11> Ip_1m net011 net083[8] AVDD pch l=LA w=w2p m=20
MM32<10> Ip_1m net011 net083[9] AVDD pch l=LA w=w2p m=20
MM10<19> net0159 net011 net046[0] AVDD pch l=LA w=w2p m=1
MM10<18> net0159 net011 net046[1] AVDD pch l=LA w=w2p m=1
MM10<17> net0159 net011 net046[2] AVDD pch l=LA w=w2p m=1
MM10<16> net0159 net011 net046[3] AVDD pch l=LA w=w2p m=1
MM10<15> net0159 net011 net046[4] AVDD pch l=LA w=w2p m=1
MM10<14> net0159 net011 net046[5] AVDD pch l=LA w=w2p m=1
MM10<13> net0159 net011 net046[6] AVDD pch l=LA w=w2p m=1
MM10<12> net0159 net011 net046[7] AVDD pch l=LA w=w2p m=1
MM10<11> net0159 net011 net046[8] AVDD pch l=LA w=w2p m=1
MM10<10> net0159 net011 net046[9] AVDD pch l=LA w=w2p m=1
MM10<9> net0159 net011 net046[10] AVDD pch l=LA w=w2p m=1
MM10<8> net0159 net011 net046[11] AVDD pch l=LA w=w2p m=1
MM10<7> net0159 net011 net046[12] AVDD pch l=LA w=w2p m=1
MM10<6> net0159 net011 net046[13] AVDD pch l=LA w=w2p m=1
MM10<5> net0159 net011 net046[14] AVDD pch l=LA w=w2p m=1
MM10<4> net0159 net011 net046[15] AVDD pch l=LA w=w2p m=1
MM10<3> net0159 net011 net046[16] AVDD pch l=LA w=w2p m=1
MM10<2> net0159 net011 net046[17] AVDD pch l=LA w=w2p m=1
MM10<1> net0159 net011 net046[18] AVDD pch l=LA w=w2p m=1
MM10<0> net0159 net011 net046[19] AVDD pch l=LA w=w2p m=1
MM7<19> net011 net011 net045[0] AVDD pch l=LA w=w2p m=1
MM7<18> net011 net011 net045[1] AVDD pch l=LA w=w2p m=1
MM7<17> net011 net011 net045[2] AVDD pch l=LA w=w2p m=1
MM7<16> net011 net011 net045[3] AVDD pch l=LA w=w2p m=1
MM7<15> net011 net011 net045[4] AVDD pch l=LA w=w2p m=1
MM7<14> net011 net011 net045[5] AVDD pch l=LA w=w2p m=1
MM7<13> net011 net011 net045[6] AVDD pch l=LA w=w2p m=1
MM7<12> net011 net011 net045[7] AVDD pch l=LA w=w2p m=1
MM7<11> net011 net011 net045[8] AVDD pch l=LA w=w2p m=1
MM7<10> net011 net011 net045[9] AVDD pch l=LA w=w2p m=1
MM7<9> net011 net011 net045[10] AVDD pch l=LA w=w2p m=1
MM7<8> net011 net011 net045[11] AVDD pch l=LA w=w2p m=1
MM7<7> net011 net011 net045[12] AVDD pch l=LA w=w2p m=1
MM7<6> net011 net011 net045[13] AVDD pch l=LA w=w2p m=1
MM7<5> net011 net011 net045[14] AVDD pch l=LA w=w2p m=1
MM7<4> net011 net011 net045[15] AVDD pch l=LA w=w2p m=1
MM7<3> net011 net011 net045[16] AVDD pch l=LA w=w2p m=1
MM7<2> net011 net011 net045[17] AVDD pch l=LA w=w2p m=1
MM7<1> net011 net011 net045[18] AVDD pch l=LA w=w2p m=1
MM7<0> net011 net011 net045[19] AVDD pch l=LA w=w2p m=1
MM9<19> net046[0] net011 AVDD AVDD pch l=LA w=w3p m=1
MM9<18> net046[1] net011 AVDD AVDD pch l=LA w=w3p m=1
MM9<17> net046[2] net011 AVDD AVDD pch l=LA w=w3p m=1
MM9<16> net046[3] net011 AVDD AVDD pch l=LA w=w3p m=1
MM9<15> net046[4] net011 AVDD AVDD pch l=LA w=w3p m=1
MM9<14> net046[5] net011 AVDD AVDD pch l=LA w=w3p m=1
MM9<13> net046[6] net011 AVDD AVDD pch l=LA w=w3p m=1
MM9<12> net046[7] net011 AVDD AVDD pch l=LA w=w3p m=1
MM9<11> net046[8] net011 AVDD AVDD pch l=LA w=w3p m=1
MM9<10> net046[9] net011 AVDD AVDD pch l=LA w=w3p m=1
MM9<9> net046[10] net011 AVDD AVDD pch l=LA w=w3p m=1
MM9<8> net046[11] net011 AVDD AVDD pch l=LA w=w3p m=1
MM9<7> net046[12] net011 AVDD AVDD pch l=LA w=w3p m=1
MM9<6> net046[13] net011 AVDD AVDD pch l=LA w=w3p m=1
MM9<5> net046[14] net011 AVDD AVDD pch l=LA w=w3p m=1
MM9<4> net046[15] net011 AVDD AVDD pch l=LA w=w3p m=1
MM9<3> net046[16] net011 AVDD AVDD pch l=LA w=w3p m=1
MM9<2> net046[17] net011 AVDD AVDD pch l=LA w=w3p m=1
MM9<1> net046[18] net011 AVDD AVDD pch l=LA w=w3p m=1
MM9<0> net046[19] net011 AVDD AVDD pch l=LA w=w3p m=1
MM8<19> net045[0] net011 AVDD AVDD pch l=LA w=w3p m=1
MM8<18> net045[1] net011 AVDD AVDD pch l=LA w=w3p m=1
MM8<17> net045[2] net011 AVDD AVDD pch l=LA w=w3p m=1
MM8<16> net045[3] net011 AVDD AVDD pch l=LA w=w3p m=1
MM8<15> net045[4] net011 AVDD AVDD pch l=LA w=w3p m=1
MM8<14> net045[5] net011 AVDD AVDD pch l=LA w=w3p m=1
MM8<13> net045[6] net011 AVDD AVDD pch l=LA w=w3p m=1
MM8<12> net045[7] net011 AVDD AVDD pch l=LA w=w3p m=1
MM8<11> net045[8] net011 AVDD AVDD pch l=LA w=w3p m=1
MM8<10> net045[9] net011 AVDD AVDD pch l=LA w=w3p m=1
MM8<9> net045[10] net011 AVDD AVDD pch l=LA w=w3p m=1
MM8<8> net045[11] net011 AVDD AVDD pch l=LA w=w3p m=1
MM8<7> net045[12] net011 AVDD AVDD pch l=LA w=w3p m=1
MM8<6> net045[13] net011 AVDD AVDD pch l=LA w=w3p m=1
MM8<5> net045[14] net011 AVDD AVDD pch l=LA w=w3p m=1
MM8<4> net045[15] net011 AVDD AVDD pch l=LA w=w3p m=1
MM8<3> net045[16] net011 AVDD AVDD pch l=LA w=w3p m=1
MM8<2> net045[17] net011 AVDD AVDD pch l=LA w=w3p m=1
MM8<1> net045[18] net011 AVDD AVDD pch l=LA w=w3p m=1
MM8<0> net045[19] net011 AVDD AVDD pch l=LA w=w3p m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    ND2D1LVT
* View Name:    schematic
************************************************************************

.SUBCKT ND2D1LVT A1 A2 VDD VSS ZN
*.PININFO A1:I A2:I ZN:O VDD:B VSS:B
MMI1-M_u3 ZN A1 net1 VSS nch_lvt l=LF w=WE m=1
MMI1-M_u4 net1 A2 VSS VSS nch_lvt l=LF w=WE m=1
MMI1-M_u1 ZN A1 VDD VDD pch_lvt l=LF w=WF m=1
MMI1-M_u2 ZN A2 VDD VDD pch_lvt l=LF w=WF m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    INVD4LVT
* View Name:    schematic
************************************************************************

.SUBCKT INVD4LVT I VDD VSS ZN
*.PININFO I:I ZN:O VDD:B VSS:B
MMU1_0-M_u2 ZN I VSS VSS nch_lvt l=LF w=WE m=1
MMU1_3-M_u2 ZN I VSS VSS nch_lvt l=LF w=WE m=1
MMU1_1-M_u2 ZN I VSS VSS nch_lvt l=LF w=WE m=1
MMU1_2-M_u2 ZN I VSS VSS nch_lvt l=LF w=WE m=1
MMU1_0-M_u3 ZN I VDD VDD pch_lvt l=LF w=WF m=1
MMU1_1-M_u3 ZN I VDD VDD pch_lvt l=LF w=WF m=1
MMU1_3-M_u3 ZN I VDD VDD pch_lvt l=LF w=WF m=1
MMU1_2-M_u3 ZN I VDD VDD pch_lvt l=LF w=WF m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    INVD2LVT
* View Name:    schematic
************************************************************************

.SUBCKT INVD2LVT I VDD VSS ZN
*.PININFO I:I ZN:O VDD:B VSS:B
MMU1_0-M_u2 ZN I VSS VSS nch_lvt l=LF w=WE m=1
MMU1_1-M_u2 ZN I VSS VSS nch_lvt l=LF w=WE m=1
MMU1_0-M_u3 ZN I VDD VDD pch_lvt l=LF w=WF m=1
MMU1_1-M_u3 ZN I VDD VDD pch_lvt l=LF w=WF m=1
.ENDS

************************************************************************
* Library Name: AP_SerDes
* Cell Name:    mux
* View Name:    schematic
************************************************************************

.SUBCKT mux DVDD DVSS IN0 IN1 OUT S SZ
*.PININFO IN0:I IN1:I S:I SZ:I OUT:O DVDD:B DVSS:B
XI3 S IN1 DVDD DVSS net8 / ND2D1LVT
XI4 SZ IN0 DVDD DVSS net7 / ND2D1LVT
XI5 net8 net7 DVDD DVSS net08 / ND2D1LVT
XI7 net07 DVDD DVSS OUT / INVD4LVT
XI6 net08 DVDD DVSS net07 / INVD2LVT
.ENDS

************************************************************************
* Library Name: AP_SerDes
* Cell Name:    MUX2to1_dig
* View Name:    schematic
************************************************************************

.SUBCKT MUX2to1_dig A[7] A[6] A[5] A[4] A[3] A[2] A[1] A[0] AE[7] AE[6] AE[5] 
+ AE[4] AE[3] AE[2] AE[1] AE[0] AO[7] AO[6] AO[5] AO[4] AO[3] AO[2] AO[1] 
+ AO[0] B[7] B[6] B[5] B[4] B[3] B[2] B[1] B[0] BE[7] BE[6] BE[5] BE[4] BE[3] 
+ BE[2] BE[1] BE[0] BO[7] BO[6] BO[5] BO[4] BO[3] BO[2] BO[1] BO[0] C[7] C[6] 
+ C[5] C[4] C[3] C[2] C[1] C[0] CE[7] CE[6] CE[5] CE[4] CE[3] CE[2] CE[1] 
+ CE[0] CLKE CLKO CO[7] CO[6] CO[5] CO[4] CO[3] CO[2] CO[1] CO[0] D[7] D[6] 
+ D[5] D[4] D[3] D[2] D[1] D[0] DE[7] DE[6] DE[5] DE[4] DE[3] DE[2] DE[1] 
+ DE[0] DO[7] DO[6] DO[5] DO[4] DO[3] DO[2] DO[1] DO[0] DVDD DVSS E[7] E[6] 
+ E[5] E[4] E[3] E[2] E[1] E[0] EE[7] EE[6] EE[5] EE[4] EE[3] EE[2] EE[1] 
+ EE[0] EO[7] EO[6] EO[5] EO[4] EO[3] EO[2] EO[1] EO[0] F[7] F[6] F[5] F[4] 
+ F[3] F[2] F[1] F[0] FE[7] FE[6] FE[5] FE[4] FE[3] FE[2] FE[1] FE[0] FO[7] 
+ FO[6] FO[5] FO[4] FO[3] FO[2] FO[1] FO[0] G[7] G[6] G[5] G[4] G[3] G[2] G[1] 
+ G[0] GE[7] GE[6] GE[5] GE[4] GE[3] GE[2] GE[1] GE[0] GO[7] GO[6] GO[5] GO[4] 
+ GO[3] GO[2] GO[1] GO[0] H[7] H[6] H[5] H[4] H[3] H[2] H[1] H[0] HE[7] HE[6] 
+ HE[5] HE[4] HE[3] HE[2] HE[1] HE[0] HO[7] HO[6] HO[5] HO[4] HO[3] HO[2] 
+ HO[1] HO[0]
*.PININFO AE[7]:I AE[6]:I AE[5]:I AE[4]:I AE[3]:I AE[2]:I AE[1]:I AE[0]:I 
*.PININFO AO[7]:I AO[6]:I AO[5]:I AO[4]:I AO[3]:I AO[2]:I AO[1]:I AO[0]:I 
*.PININFO BE[7]:I BE[6]:I BE[5]:I BE[4]:I BE[3]:I BE[2]:I BE[1]:I BE[0]:I 
*.PININFO BO[7]:I BO[6]:I BO[5]:I BO[4]:I BO[3]:I BO[2]:I BO[1]:I BO[0]:I 
*.PININFO CE[7]:I CE[6]:I CE[5]:I CE[4]:I CE[3]:I CE[2]:I CE[1]:I CE[0]:I 
*.PININFO CLKE:I CLKO:I CO[7]:I CO[6]:I CO[5]:I CO[4]:I CO[3]:I CO[2]:I 
*.PININFO CO[1]:I CO[0]:I DE[7]:I DE[6]:I DE[5]:I DE[4]:I DE[3]:I DE[2]:I 
*.PININFO DE[1]:I DE[0]:I DO[7]:I DO[6]:I DO[5]:I DO[4]:I DO[3]:I DO[2]:I 
*.PININFO DO[1]:I DO[0]:I EE[7]:I EE[6]:I EE[5]:I EE[4]:I EE[3]:I EE[2]:I 
*.PININFO EE[1]:I EE[0]:I EO[7]:I EO[6]:I EO[5]:I EO[4]:I EO[3]:I EO[2]:I 
*.PININFO EO[1]:I EO[0]:I FE[7]:I FE[6]:I FE[5]:I FE[4]:I FE[3]:I FE[2]:I 
*.PININFO FE[1]:I FE[0]:I FO[7]:I FO[6]:I FO[5]:I FO[4]:I FO[3]:I FO[2]:I 
*.PININFO FO[1]:I FO[0]:I GE[7]:I GE[6]:I GE[5]:I GE[4]:I GE[3]:I GE[2]:I 
*.PININFO GE[1]:I GE[0]:I GO[7]:I GO[6]:I GO[5]:I GO[4]:I GO[3]:I GO[2]:I 
*.PININFO GO[1]:I GO[0]:I HE[7]:I HE[6]:I HE[5]:I HE[4]:I HE[3]:I HE[2]:I 
*.PININFO HE[1]:I HE[0]:I HO[7]:I HO[6]:I HO[5]:I HO[4]:I HO[3]:I HO[2]:I 
*.PININFO HO[1]:I HO[0]:I A[7]:O A[6]:O A[5]:O A[4]:O A[3]:O A[2]:O A[1]:O 
*.PININFO A[0]:O B[7]:O B[6]:O B[5]:O B[4]:O B[3]:O B[2]:O B[1]:O B[0]:O 
*.PININFO C[7]:O C[6]:O C[5]:O C[4]:O C[3]:O C[2]:O C[1]:O C[0]:O D[7]:O 
*.PININFO D[6]:O D[5]:O D[4]:O D[3]:O D[2]:O D[1]:O D[0]:O E[7]:O E[6]:O 
*.PININFO E[5]:O E[4]:O E[3]:O E[2]:O E[1]:O E[0]:O F[7]:O F[6]:O F[5]:O 
*.PININFO F[4]:O F[3]:O F[2]:O F[1]:O F[0]:O G[7]:O G[6]:O G[5]:O G[4]:O 
*.PININFO G[3]:O G[2]:O G[1]:O G[0]:O H[7]:O H[6]:O H[5]:O H[4]:O H[3]:O 
*.PININFO H[2]:O H[1]:O H[0]:O DVDD:B DVSS:B
XI8<7> DVDD DVSS AE[7] AO[7] A[7] CLKE CLKO / mux
XI8<6> DVDD DVSS AE[6] AO[6] A[6] CLKE CLKO / mux
XI8<5> DVDD DVSS AE[5] AO[5] A[5] CLKE CLKO / mux
XI8<4> DVDD DVSS AE[4] AO[4] A[4] CLKE CLKO / mux
XI8<3> DVDD DVSS AE[3] AO[3] A[3] CLKE CLKO / mux
XI8<2> DVDD DVSS AE[2] AO[2] A[2] CLKE CLKO / mux
XI8<1> DVDD DVSS AE[1] AO[1] A[1] CLKE CLKO / mux
XI8<0> DVDD DVSS AE[0] AO[0] A[0] CLKE CLKO / mux
XI15<7> DVDD DVSS HE[7] HO[7] H[7] CLKE CLKO / mux
XI15<6> DVDD DVSS HE[6] HO[6] H[6] CLKE CLKO / mux
XI15<5> DVDD DVSS HE[5] HO[5] H[5] CLKE CLKO / mux
XI15<4> DVDD DVSS HE[4] HO[4] H[4] CLKE CLKO / mux
XI15<3> DVDD DVSS HE[3] HO[3] H[3] CLKE CLKO / mux
XI15<2> DVDD DVSS HE[2] HO[2] H[2] CLKE CLKO / mux
XI15<1> DVDD DVSS HE[1] HO[1] H[1] CLKE CLKO / mux
XI15<0> DVDD DVSS HE[0] HO[0] H[0] CLKE CLKO / mux
XI14<7> DVDD DVSS GE[7] GO[7] G[7] CLKE CLKO / mux
XI14<6> DVDD DVSS GE[6] GO[6] G[6] CLKE CLKO / mux
XI14<5> DVDD DVSS GE[5] GO[5] G[5] CLKE CLKO / mux
XI14<4> DVDD DVSS GE[4] GO[4] G[4] CLKE CLKO / mux
XI14<3> DVDD DVSS GE[3] GO[3] G[3] CLKE CLKO / mux
XI14<2> DVDD DVSS GE[2] GO[2] G[2] CLKE CLKO / mux
XI14<1> DVDD DVSS GE[1] GO[1] G[1] CLKE CLKO / mux
XI14<0> DVDD DVSS GE[0] GO[0] G[0] CLKE CLKO / mux
XI13<7> DVDD DVSS FE[7] FO[7] F[7] CLKE CLKO / mux
XI13<6> DVDD DVSS FE[6] FO[6] F[6] CLKE CLKO / mux
XI13<5> DVDD DVSS FE[5] FO[5] F[5] CLKE CLKO / mux
XI13<4> DVDD DVSS FE[4] FO[4] F[4] CLKE CLKO / mux
XI13<3> DVDD DVSS FE[3] FO[3] F[3] CLKE CLKO / mux
XI13<2> DVDD DVSS FE[2] FO[2] F[2] CLKE CLKO / mux
XI13<1> DVDD DVSS FE[1] FO[1] F[1] CLKE CLKO / mux
XI13<0> DVDD DVSS FE[0] FO[0] F[0] CLKE CLKO / mux
XI12<7> DVDD DVSS EE[7] EO[7] E[7] CLKE CLKO / mux
XI12<6> DVDD DVSS EE[6] EO[6] E[6] CLKE CLKO / mux
XI12<5> DVDD DVSS EE[5] EO[5] E[5] CLKE CLKO / mux
XI12<4> DVDD DVSS EE[4] EO[4] E[4] CLKE CLKO / mux
XI12<3> DVDD DVSS EE[3] EO[3] E[3] CLKE CLKO / mux
XI12<2> DVDD DVSS EE[2] EO[2] E[2] CLKE CLKO / mux
XI12<1> DVDD DVSS EE[1] EO[1] E[1] CLKE CLKO / mux
XI12<0> DVDD DVSS EE[0] EO[0] E[0] CLKE CLKO / mux
XI11<7> DVDD DVSS DE[7] DO[7] D[7] CLKE CLKO / mux
XI11<6> DVDD DVSS DE[6] DO[6] D[6] CLKE CLKO / mux
XI11<5> DVDD DVSS DE[5] DO[5] D[5] CLKE CLKO / mux
XI11<4> DVDD DVSS DE[4] DO[4] D[4] CLKE CLKO / mux
XI11<3> DVDD DVSS DE[3] DO[3] D[3] CLKE CLKO / mux
XI11<2> DVDD DVSS DE[2] DO[2] D[2] CLKE CLKO / mux
XI11<1> DVDD DVSS DE[1] DO[1] D[1] CLKE CLKO / mux
XI11<0> DVDD DVSS DE[0] DO[0] D[0] CLKE CLKO / mux
XI10<7> DVDD DVSS CE[7] CO[7] C[7] CLKE CLKO / mux
XI10<6> DVDD DVSS CE[6] CO[6] C[6] CLKE CLKO / mux
XI10<5> DVDD DVSS CE[5] CO[5] C[5] CLKE CLKO / mux
XI10<4> DVDD DVSS CE[4] CO[4] C[4] CLKE CLKO / mux
XI10<3> DVDD DVSS CE[3] CO[3] C[3] CLKE CLKO / mux
XI10<2> DVDD DVSS CE[2] CO[2] C[2] CLKE CLKO / mux
XI10<1> DVDD DVSS CE[1] CO[1] C[1] CLKE CLKO / mux
XI10<0> DVDD DVSS CE[0] CO[0] C[0] CLKE CLKO / mux
XI9<7> DVDD DVSS BE[7] BO[7] B[7] CLKE CLKO / mux
XI9<6> DVDD DVSS BE[6] BO[6] B[6] CLKE CLKO / mux
XI9<5> DVDD DVSS BE[5] BO[5] B[5] CLKE CLKO / mux
XI9<4> DVDD DVSS BE[4] BO[4] B[4] CLKE CLKO / mux
XI9<3> DVDD DVSS BE[3] BO[3] B[3] CLKE CLKO / mux
XI9<2> DVDD DVSS BE[2] BO[2] B[2] CLKE CLKO / mux
XI9<1> DVDD DVSS BE[1] BO[1] B[1] CLKE CLKO / mux
XI9<0> DVDD DVSS BE[0] BO[0] B[0] CLKE CLKO / mux
.ENDS

************************************************************************
* Library Name: AP_SerDes
* Cell Name:    CML_Driver_PAM8_woCS_v3
* View Name:    schematic
************************************************************************

.SUBCKT CML_Driver_PAM8_woCS_v3 A[7] A[6] A[5] A[4] A[3] A[2] A[1] A[0] AVDD 
+ AVSS B[7] B[6] B[5] B[4] B[3] B[2] B[1] B[0] C[7] C[6] C[5] C[4] C[3] C[2] 
+ C[1] C[0] D[7] D[6] D[5] D[4] D[3] D[2] D[1] D[0] E[7] E[6] E[5] E[4] E[3] 
+ E[2] E[1] E[0] F[7] F[6] F[5] F[4] F[3] F[2] F[1] F[0] G[7] G[6] G[5] G[4] 
+ G[3] G[2] G[1] G[0] H[7] H[6] H[5] H[4] H[3] H[2] H[1] H[0] In_1m In_3m 
+ In_5m In_7m Ip_1m Ip_3m Ip_5m Ip_7m ntx outa outb outc outd oute outf outg 
+ outh
*.PININFO A[7]:I A[6]:I A[5]:I A[4]:I A[3]:I A[2]:I A[1]:I A[0]:I B[7]:I 
*.PININFO B[6]:I B[5]:I B[4]:I B[3]:I B[2]:I B[1]:I B[0]:I C[7]:I C[6]:I 
*.PININFO C[5]:I C[4]:I C[3]:I C[2]:I C[1]:I C[0]:I D[7]:I D[6]:I D[5]:I 
*.PININFO D[4]:I D[3]:I D[2]:I D[1]:I D[0]:I E[7]:I E[6]:I E[5]:I E[4]:I 
*.PININFO E[3]:I E[2]:I E[1]:I E[0]:I F[7]:I F[6]:I F[5]:I F[4]:I F[3]:I 
*.PININFO F[2]:I F[1]:I F[0]:I G[7]:I G[6]:I G[5]:I G[4]:I G[3]:I G[2]:I 
*.PININFO G[1]:I G[0]:I H[7]:I H[6]:I H[5]:I H[4]:I H[3]:I H[2]:I H[1]:I 
*.PININFO H[0]:I outa:O outb:O outc:O outd:O oute:O outf:O outg:O outh:O 
*.PININFO AVDD:B AVSS:B In_1m:B In_3m:B In_5m:B In_7m:B Ip_1m:B Ip_3m:B 
*.PININFO Ip_5m:B Ip_7m:B ntx:B
MM56 outa A[0] In_7m AVSS nch_lvt l=LF w=wnswitch m=M*4
MM54 outa A[1] In_5m AVSS nch_lvt l=LF w=wnswitch m=M*4
MM50 outa A[3] In_1m AVSS nch_lvt l=LF w=wnswitch m=M*4
MM52 outa A[2] In_3m AVSS nch_lvt l=LF w=wnswitch m=(M*3)*4
MM115 outg G[3] In_1m AVSS nch_lvt l=LF w=wnswitch m=M*4
MM111 oute E[3] In_1m AVSS nch_lvt l=LF w=wnswitch m=M*4
MM97 oute E[2] In_3m AVSS nch_lvt l=LF w=wnswitch m=(M*3)*4
MM83 oute E[1] In_5m AVSS nch_lvt l=LF w=wnswitch m=M*4
MM64 oute E[0] In_7m AVSS nch_lvt l=LF w=wnswitch m=M*4
MM113 outf F[3] In_1m AVSS nch_lvt l=LF w=wnswitch m=M*4
MM109 outd D[3] In_1m AVSS nch_lvt l=LF w=wnswitch m=M*4
MM95 outd D[2] In_3m AVSS nch_lvt l=LF w=wnswitch m=(M*3)*4
MM81 outd D[1] In_5m AVSS nch_lvt l=LF w=wnswitch m=M*4
MM62 outd D[0] In_7m AVSS nch_lvt l=LF w=wnswitch m=M*4
MM107 outc C[3] In_1m AVSS nch_lvt l=LF w=wnswitch m=M*4
MM93 outc C[2] In_3m AVSS nch_lvt l=LF w=wnswitch m=(M*3)*4
MM79 outc C[1] In_5m AVSS nch_lvt l=LF w=wnswitch m=M*4
MM60 outc C[0] In_7m AVSS nch_lvt l=LF w=wnswitch m=M*4
MM101 outg G[2] In_3m AVSS nch_lvt l=LF w=wnswitch m=(M*3)*4
MM87 outg G[1] In_5m AVSS nch_lvt l=LF w=wnswitch m=M*4
MM99 outf F[2] In_3m AVSS nch_lvt l=LF w=wnswitch m=(M*3)*4
MM105 outb B[3] In_1m AVSS nch_lvt l=LF w=wnswitch m=M*4
MM91 outb B[2] In_3m AVSS nch_lvt l=LF w=wnswitch m=(M*3)*4
MM73 outb B[1] In_5m AVSS nch_lvt l=LF w=wnswitch m=M*4
MM58 outb B[0] In_7m AVSS nch_lvt l=LF w=wnswitch m=M*4
MM117 outh H[3] In_1m AVSS nch_lvt l=LF w=wnswitch m=M*4
MM103 outh H[2] In_3m AVSS nch_lvt l=LF w=wnswitch m=(M*3)*4
MM85 outf F[1] In_5m AVSS nch_lvt l=LF w=wnswitch m=M*4
MM68 outg G[0] In_7m AVSS nch_lvt l=LF w=wnswitch m=M*4
MM89 outh H[1] In_5m AVSS nch_lvt l=LF w=wnswitch m=M*4
MM70 outh H[0] In_7m AVSS nch_lvt l=LF w=wnswitch m=M*4
MM66 outf F[0] In_7m AVSS nch_lvt l=LF w=wnswitch m=M*4
MM53 outa A[6] Ip_5m AVDD pch_lvt l=LF w=wpswitch m=(M*5)*4
MM49 outa A[4] Ip_1m AVDD pch_lvt l=LF w=wpswitch m=M*4
MM51 outa A[5] Ip_3m AVDD pch_lvt l=LF w=wpswitch m=(M*3)*4
MM55 outa A[7] Ip_7m AVDD pch_lvt l=LF w=wpswitch m=(M*7)*4
MM104 outb B[4] Ip_1m AVDD pch_lvt l=LF w=wpswitch m=M*4
MM100 outg G[5] Ip_3m AVDD pch_lvt l=LF w=wpswitch m=M*4
MM98 outf F[5] Ip_3m AVDD pch_lvt l=LF w=wpswitch m=M*4
MM112 outf F[4] Ip_1m AVDD pch_lvt l=LF w=wpswitch m=M*4
MM86 outg G[6] Ip_5m AVDD pch_lvt l=LF w=wpswitch m=(M*5)*4
MM96 oute E[5] Ip_3m AVDD pch_lvt l=LF w=wpswitch m=M*4
MM82 oute E[6] Ip_5m AVDD pch_lvt l=LF w=wpswitch m=(M*5)*4
MM63 oute E[7] Ip_7m AVDD pch_lvt l=LF w=wpswitch m=(M*7)*4
MM110 oute E[4] Ip_1m AVDD pch_lvt l=LF w=wpswitch m=M*4
MM94 outd D[5] Ip_3m AVDD pch_lvt l=LF w=wpswitch m=M*4
MM80 outd D[6] Ip_5m AVDD pch_lvt l=LF w=wpswitch m=(M*5)*4
MM108 outd D[4] Ip_1m AVDD pch_lvt l=LF w=wpswitch m=M*4
MM61 outd D[7] Ip_7m AVDD pch_lvt l=LF w=wpswitch m=(M*7)*4
MM116 outh H[4] Ip_1m AVDD pch_lvt l=LF w=wpswitch m=M*4
MM92 outc C[5] Ip_3m AVDD pch_lvt l=LF w=wpswitch m=M*4
MM75 outc C[6] Ip_5m AVDD pch_lvt l=LF w=wpswitch m=(M*5)*4
MM59 outc C[7] Ip_7m AVDD pch_lvt l=LF w=wpswitch m=(M*7)*4
MM106 outc C[4] Ip_1m AVDD pch_lvt l=LF w=wpswitch m=M*4
MM67 outg G[7] Ip_7m AVDD pch_lvt l=LF w=wpswitch m=(M*7)*4
MM114 outg G[4] Ip_1m AVDD pch_lvt l=LF w=wpswitch m=M*4
MM102 outh H[5] Ip_3m AVDD pch_lvt l=LF w=wpswitch m=M*4
MM90 outb B[5] Ip_3m AVDD pch_lvt l=LF w=wpswitch m=(M*3)*4
MM71 outb B[6] Ip_5m AVDD pch_lvt l=LF w=wpswitch m=(M*5)*4
MM57 outb B[7] Ip_7m AVDD pch_lvt l=LF w=wpswitch m=(M*7)*4
MM88 outh H[6] Ip_5m AVDD pch_lvt l=LF w=wpswitch m=(M*5)*4
MM84 outf F[6] Ip_5m AVDD pch_lvt l=LF w=wpswitch m=(M*5)*4
MM65 outf F[7] Ip_7m AVDD pch_lvt l=LF w=wpswitch m=(M*7)*4
MM69 outh H[7] Ip_7m AVDD pch_lvt l=LF w=wpswitch m=(M*7)*4
XR23 outa ntx rppolyl l=LC w=WG m=1
XR3 oute ntx rppolyl l=LC w=WG m=1
XR4 outf ntx rppolyl l=LC w=WG m=1
XR5 outg ntx rppolyl l=LC w=WG m=1
XR1 outc ntx rppolyl l=LC w=WG m=1
XR6 outh ntx rppolyl l=LC w=WG m=1
XR2 outd ntx rppolyl l=LC w=WG m=1
XR0 outb ntx rppolyl l=LC w=WG m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    INVD1LVT
* View Name:    schematic
************************************************************************

.SUBCKT INVD1LVT I VDD VSS ZN
*.PININFO I:I ZN:O VDD:B VSS:B
MMU1-M_u2 ZN I VSS VSS nch_lvt l=LF w=WE m=1
MMU1-M_u3 ZN I VDD VDD pch_lvt l=LF w=WF m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    INVD16LVT
* View Name:    schematic
************************************************************************

.SUBCKT INVD16LVT I VDD VSS ZN
*.PININFO I:I ZN:O VDD:B VSS:B
MMI2_9-M_u3 ZN I VDD VDD pch_lvt l=LF w=WF m=1
MMI2_6-M_u3 ZN I VDD VDD pch_lvt l=LF w=WF m=1
MMI2_1-M_u3 ZN I VDD VDD pch_lvt l=LF w=WF m=1
MMI2_4-M_u3 ZN I VDD VDD pch_lvt l=LF w=WF m=1
MMI2_12-M_u3 ZN I VDD VDD pch_lvt l=LF w=WF m=1
MMI2_13-M_u3 ZN I VDD VDD pch_lvt l=LF w=WF m=1
MMI2_3-M_u3 ZN I VDD VDD pch_lvt l=LF w=WF m=1
MMI2_10-M_u3 ZN I VDD VDD pch_lvt l=LF w=WF m=1
MMI2_0-M_u3 ZN I VDD VDD pch_lvt l=LF w=WF m=1
MMI2_11-M_u3 ZN I VDD VDD pch_lvt l=LF w=WF m=1
MMI2_7-M_u3 ZN I VDD VDD pch_lvt l=LF w=WF m=1
MMI2_5-M_u3 ZN I VDD VDD pch_lvt l=LF w=WF m=1
MMI2_2-M_u3 ZN I VDD VDD pch_lvt l=LF w=WF m=1
MMI2_8-M_u3 ZN I VDD VDD pch_lvt l=LF w=WF m=1
MMI2_15-M_u3 ZN I VDD VDD pch_lvt l=LF w=WF m=1
MMI2_14-M_u3 ZN I VDD VDD pch_lvt l=LF w=WF m=1
MMI2_12-M_u2 ZN I VSS VSS nch_lvt l=LF w=WE m=1
MMI2_15-M_u2 ZN I VSS VSS nch_lvt l=LF w=WE m=1
MMI2_3-M_u2 ZN I VSS VSS nch_lvt l=LF w=WE m=1
MMI2_14-M_u2 ZN I VSS VSS nch_lvt l=LF w=WE m=1
MMI2_4-M_u2 ZN I VSS VSS nch_lvt l=LF w=WE m=1
MMI2_1-M_u2 ZN I VSS VSS nch_lvt l=LF w=WE m=1
MMI2_0-M_u2 ZN I VSS VSS nch_lvt l=LF w=WE m=1
MMI2_13-M_u2 ZN I VSS VSS nch_lvt l=LF w=WE m=1
MMI2_8-M_u2 ZN I VSS VSS nch_lvt l=LF w=WE m=1
MMI2_5-M_u2 ZN I VSS VSS nch_lvt l=LF w=WE m=1
MMI2_7-M_u2 ZN I VSS VSS nch_lvt l=LF w=WE m=1
MMI2_6-M_u2 ZN I VSS VSS nch_lvt l=LF w=WE m=1
MMI2_9-M_u2 ZN I VSS VSS nch_lvt l=LF w=WE m=1
MMI2_2-M_u2 ZN I VSS VSS nch_lvt l=LF w=WE m=1
MMI2_11-M_u2 ZN I VSS VSS nch_lvt l=LF w=WE m=1
MMI2_10-M_u2 ZN I VSS VSS nch_lvt l=LF w=WE m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    INVD8LVT
* View Name:    schematic
************************************************************************

.SUBCKT INVD8LVT I VDD VSS ZN
*.PININFO I:I ZN:O VDD:B VSS:B
MMU1_5-M_u2 ZN I VSS VSS nch_lvt l=LF w=WE m=1
MMU1_0-M_u2 ZN I VSS VSS nch_lvt l=LF w=WE m=1
MMU1_3-M_u2 ZN I VSS VSS nch_lvt l=LF w=WE m=1
MMU1_7-M_u2 ZN I VSS VSS nch_lvt l=LF w=WE m=1
MMU1_4-M_u2 ZN I VSS VSS nch_lvt l=LF w=WE m=1
MMU1_1-M_u2 ZN I VSS VSS nch_lvt l=LF w=WE m=1
MMU1_6-M_u2 ZN I VSS VSS nch_lvt l=LF w=WE m=1
MMU1_2-M_u2 ZN I VSS VSS nch_lvt l=LF w=WE m=1
MMU1_0-M_u3 ZN I VDD VDD pch_lvt l=LF w=WF m=1
MMU1_4-M_u3 ZN I VDD VDD pch_lvt l=LF w=WF m=1
MMU1_5-M_u3 ZN I VDD VDD pch_lvt l=LF w=WF m=1
MMU1_1-M_u3 ZN I VDD VDD pch_lvt l=LF w=WF m=1
MMU1_3-M_u3 ZN I VDD VDD pch_lvt l=LF w=WF m=1
MMU1_7-M_u3 ZN I VDD VDD pch_lvt l=LF w=WF m=1
MMU1_6-M_u3 ZN I VDD VDD pch_lvt l=LF w=WF m=1
MMU1_2-M_u3 ZN I VDD VDD pch_lvt l=LF w=WF m=1
.ENDS

************************************************************************
* Library Name: AP_SerDes
* Cell Name:    PreDriver_PAM8_v4
* View Name:    schematic
************************************************************************

.SUBCKT PreDriver_PAM8_v4 A[7] A[6] A[5] A[4] A[3] A[2] A[1] A[0] Ain[7] 
+ Ain[6] Ain[5] Ain[4] Ain[3] Ain[2] Ain[1] Ain[0] B[7] B[6] B[5] B[4] B[3] 
+ B[2] B[1] B[0] Bin[7] Bin[6] Bin[5] Bin[4] Bin[3] Bin[2] Bin[1] Bin[0] C[7] 
+ C[6] C[5] C[4] C[3] C[2] C[1] C[0] Cin[7] Cin[6] Cin[5] Cin[4] Cin[3] Cin[2] 
+ Cin[1] Cin[0] D[7] D[6] D[5] D[4] D[3] D[2] D[1] D[0] DVDD DVSS Din[7] 
+ Din[6] Din[5] Din[4] Din[3] Din[2] Din[1] Din[0] E[7] E[6] E[5] E[4] E[3] 
+ E[2] E[1] E[0] Ein[7] Ein[6] Ein[5] Ein[4] Ein[3] Ein[2] Ein[1] Ein[0] F[7] 
+ F[6] F[5] F[4] F[3] F[2] F[1] F[0] Fin[7] Fin[6] Fin[5] Fin[4] Fin[3] Fin[2] 
+ Fin[1] Fin[0] G[7] G[6] G[5] G[4] G[3] G[2] G[1] G[0] Gin[7] Gin[6] Gin[5] 
+ Gin[4] Gin[3] Gin[2] Gin[1] Gin[0] H[7] H[6] H[5] H[4] H[3] H[2] H[1] H[0] 
+ Hin[7] Hin[6] Hin[5] Hin[4] Hin[3] Hin[2] Hin[1] Hin[0]
*.PININFO Ain[7]:I Ain[6]:I Ain[5]:I Ain[4]:I Ain[3]:I Ain[2]:I Ain[1]:I 
*.PININFO Ain[0]:I Bin[7]:I Bin[6]:I Bin[5]:I Bin[4]:I Bin[3]:I Bin[2]:I 
*.PININFO Bin[1]:I Bin[0]:I Cin[7]:I Cin[6]:I Cin[5]:I Cin[4]:I Cin[3]:I 
*.PININFO Cin[2]:I Cin[1]:I Cin[0]:I Din[7]:I Din[6]:I Din[5]:I Din[4]:I 
*.PININFO Din[3]:I Din[2]:I Din[1]:I Din[0]:I Ein[7]:I Ein[6]:I Ein[5]:I 
*.PININFO Ein[4]:I Ein[3]:I Ein[2]:I Ein[1]:I Ein[0]:I Fin[7]:I Fin[6]:I 
*.PININFO Fin[5]:I Fin[4]:I Fin[3]:I Fin[2]:I Fin[1]:I Fin[0]:I Gin[7]:I 
*.PININFO Gin[6]:I Gin[5]:I Gin[4]:I Gin[3]:I Gin[2]:I Gin[1]:I Gin[0]:I 
*.PININFO Hin[7]:I Hin[6]:I Hin[5]:I Hin[4]:I Hin[3]:I Hin[2]:I Hin[1]:I 
*.PININFO Hin[0]:I A[7]:O A[6]:O A[5]:O A[4]:O A[3]:O A[2]:O A[1]:O A[0]:O 
*.PININFO B[7]:O B[6]:O B[5]:O B[4]:O B[3]:O B[2]:O B[1]:O B[0]:O C[7]:O 
*.PININFO C[6]:O C[5]:O C[4]:O C[3]:O C[2]:O C[1]:O C[0]:O D[7]:O D[6]:O 
*.PININFO D[5]:O D[4]:O D[3]:O D[2]:O D[1]:O D[0]:O E[7]:O E[6]:O E[5]:O 
*.PININFO E[4]:O E[3]:O E[2]:O E[1]:O E[0]:O F[7]:O F[6]:O F[5]:O F[4]:O 
*.PININFO F[3]:O F[2]:O F[1]:O F[0]:O G[7]:O G[6]:O G[5]:O G[4]:O G[3]:O 
*.PININFO G[2]:O G[1]:O G[0]:O H[7]:O H[6]:O H[5]:O H[4]:O H[3]:O H[2]:O 
*.PININFO H[1]:O H[0]:O DVDD:B DVSS:B
XI0<31> Ain[7] net053 DVSS net024[0] / INVD1LVT
XI0<30> Ain[6] net053 DVSS net024[1] / INVD1LVT
XI0<29> Ain[5] net053 DVSS net024[2] / INVD1LVT
XI0<28> Ain[4] net053 DVSS net024[3] / INVD1LVT
XI0<27> Bin[7] net053 DVSS net024[4] / INVD1LVT
XI0<26> Bin[6] net053 DVSS net024[5] / INVD1LVT
XI0<25> Bin[5] net053 DVSS net024[6] / INVD1LVT
XI0<24> Bin[4] net053 DVSS net024[7] / INVD1LVT
XI0<23> Cin[7] net053 DVSS net024[8] / INVD1LVT
XI0<22> Cin[6] net053 DVSS net024[9] / INVD1LVT
XI0<21> Cin[5] net053 DVSS net024[10] / INVD1LVT
XI0<20> Cin[4] net053 DVSS net024[11] / INVD1LVT
XI0<19> Din[7] net053 DVSS net024[12] / INVD1LVT
XI0<18> Din[6] net053 DVSS net024[13] / INVD1LVT
XI0<17> Din[5] net053 DVSS net024[14] / INVD1LVT
XI0<16> Din[4] net053 DVSS net024[15] / INVD1LVT
XI0<15> Ein[7] net053 DVSS net024[16] / INVD1LVT
XI0<14> Ein[6] net053 DVSS net024[17] / INVD1LVT
XI0<13> Ein[5] net053 DVSS net024[18] / INVD1LVT
XI0<12> Ein[4] net053 DVSS net024[19] / INVD1LVT
XI0<11> Fin[7] net053 DVSS net024[20] / INVD1LVT
XI0<10> Fin[6] net053 DVSS net024[21] / INVD1LVT
XI0<9> Fin[5] net053 DVSS net024[22] / INVD1LVT
XI0<8> Fin[4] net053 DVSS net024[23] / INVD1LVT
XI0<7> Gin[7] net053 DVSS net024[24] / INVD1LVT
XI0<6> Gin[6] net053 DVSS net024[25] / INVD1LVT
XI0<5> Gin[5] net053 DVSS net024[26] / INVD1LVT
XI0<4> Gin[4] net053 DVSS net024[27] / INVD1LVT
XI0<3> Hin[7] net053 DVSS net024[28] / INVD1LVT
XI0<2> Hin[6] net053 DVSS net024[29] / INVD1LVT
XI0<1> Hin[5] net053 DVSS net024[30] / INVD1LVT
XI0<0> Hin[4] net053 DVSS net024[31] / INVD1LVT
XI16<31> Ain[3] net022 DVSS net010[0] / INVD1LVT
XI16<30> Ain[2] net022 DVSS net010[1] / INVD1LVT
XI16<29> Ain[1] net022 DVSS net010[2] / INVD1LVT
XI16<28> Ain[0] net022 DVSS net010[3] / INVD1LVT
XI16<27> Bin[3] net022 DVSS net010[4] / INVD1LVT
XI16<26> Bin[2] net022 DVSS net010[5] / INVD1LVT
XI16<25> Bin[1] net022 DVSS net010[6] / INVD1LVT
XI16<24> Bin[0] net022 DVSS net010[7] / INVD1LVT
XI16<23> Cin[3] net022 DVSS net010[8] / INVD1LVT
XI16<22> Cin[2] net022 DVSS net010[9] / INVD1LVT
XI16<21> Cin[1] net022 DVSS net010[10] / INVD1LVT
XI16<20> Cin[0] net022 DVSS net010[11] / INVD1LVT
XI16<19> Din[3] net022 DVSS net010[12] / INVD1LVT
XI16<18> Din[2] net022 DVSS net010[13] / INVD1LVT
XI16<17> Din[1] net022 DVSS net010[14] / INVD1LVT
XI16<16> Din[0] net022 DVSS net010[15] / INVD1LVT
XI16<15> Ein[3] net022 DVSS net010[16] / INVD1LVT
XI16<14> Ein[2] net022 DVSS net010[17] / INVD1LVT
XI16<13> Ein[1] net022 DVSS net010[18] / INVD1LVT
XI16<12> Ein[0] net022 DVSS net010[19] / INVD1LVT
XI16<11> Fin[3] net022 DVSS net010[20] / INVD1LVT
XI16<10> Fin[2] net022 DVSS net010[21] / INVD1LVT
XI16<9> Fin[1] net022 DVSS net010[22] / INVD1LVT
XI16<8> Fin[0] net022 DVSS net010[23] / INVD1LVT
XI16<7> Gin[3] net022 DVSS net010[24] / INVD1LVT
XI16<6> Gin[2] net022 DVSS net010[25] / INVD1LVT
XI16<5> Gin[1] net022 DVSS net010[26] / INVD1LVT
XI16<4> Gin[0] net022 DVSS net010[27] / INVD1LVT
XI16<3> Hin[3] net022 DVSS net010[28] / INVD1LVT
XI16<2> Hin[2] net022 DVSS net010[29] / INVD1LVT
XI16<1> Hin[1] net022 DVSS net010[30] / INVD1LVT
XI16<0> Hin[0] net022 DVSS net010[31] / INVD1LVT
XI13<31> net010[0] net028 DVSS net012[0] / INVD1LVT
XI13<30> net010[1] net028 DVSS net012[1] / INVD1LVT
XI13<29> net010[2] net028 DVSS net012[2] / INVD1LVT
XI13<28> net010[3] net028 DVSS net012[3] / INVD1LVT
XI13<27> net010[4] net028 DVSS net012[4] / INVD1LVT
XI13<26> net010[5] net028 DVSS net012[5] / INVD1LVT
XI13<25> net010[6] net028 DVSS net012[6] / INVD1LVT
XI13<24> net010[7] net028 DVSS net012[7] / INVD1LVT
XI13<23> net010[8] net028 DVSS net012[8] / INVD1LVT
XI13<22> net010[9] net028 DVSS net012[9] / INVD1LVT
XI13<21> net010[10] net028 DVSS net012[10] / INVD1LVT
XI13<20> net010[11] net028 DVSS net012[11] / INVD1LVT
XI13<19> net010[12] net028 DVSS net012[12] / INVD1LVT
XI13<18> net010[13] net028 DVSS net012[13] / INVD1LVT
XI13<17> net010[14] net028 DVSS net012[14] / INVD1LVT
XI13<16> net010[15] net028 DVSS net012[15] / INVD1LVT
XI13<15> net010[16] net028 DVSS net012[16] / INVD1LVT
XI13<14> net010[17] net028 DVSS net012[17] / INVD1LVT
XI13<13> net010[18] net028 DVSS net012[18] / INVD1LVT
XI13<12> net010[19] net028 DVSS net012[19] / INVD1LVT
XI13<11> net010[20] net028 DVSS net012[20] / INVD1LVT
XI13<10> net010[21] net028 DVSS net012[21] / INVD1LVT
XI13<9> net010[22] net028 DVSS net012[22] / INVD1LVT
XI13<8> net010[23] net028 DVSS net012[23] / INVD1LVT
XI13<7> net010[24] net028 DVSS net012[24] / INVD1LVT
XI13<6> net010[25] net028 DVSS net012[25] / INVD1LVT
XI13<5> net010[26] net028 DVSS net012[26] / INVD1LVT
XI13<4> net010[27] net028 DVSS net012[27] / INVD1LVT
XI13<3> net010[28] net028 DVSS net012[28] / INVD1LVT
XI13<2> net010[29] net028 DVSS net012[29] / INVD1LVT
XI13<1> net010[30] net028 DVSS net012[30] / INVD1LVT
XI13<0> net010[31] net028 DVSS net012[31] / INVD1LVT
XI3<31> net012[0] net033 DVSS net014[0] / INVD2LVT
XI3<30> net012[1] net033 DVSS net014[1] / INVD2LVT
XI3<29> net012[2] net033 DVSS net014[2] / INVD2LVT
XI3<28> net012[3] net033 DVSS net014[3] / INVD2LVT
XI3<27> net012[4] net033 DVSS net014[4] / INVD2LVT
XI3<26> net012[5] net033 DVSS net014[5] / INVD2LVT
XI3<25> net012[6] net033 DVSS net014[6] / INVD2LVT
XI3<24> net012[7] net033 DVSS net014[7] / INVD2LVT
XI3<23> net012[8] net033 DVSS net014[8] / INVD2LVT
XI3<22> net012[9] net033 DVSS net014[9] / INVD2LVT
XI3<21> net012[10] net033 DVSS net014[10] / INVD2LVT
XI3<20> net012[11] net033 DVSS net014[11] / INVD2LVT
XI3<19> net012[12] net033 DVSS net014[12] / INVD2LVT
XI3<18> net012[13] net033 DVSS net014[13] / INVD2LVT
XI3<17> net012[14] net033 DVSS net014[14] / INVD2LVT
XI3<16> net012[15] net033 DVSS net014[15] / INVD2LVT
XI3<15> net012[16] net033 DVSS net014[16] / INVD2LVT
XI3<14> net012[17] net033 DVSS net014[17] / INVD2LVT
XI3<13> net012[18] net033 DVSS net014[18] / INVD2LVT
XI3<12> net012[19] net033 DVSS net014[19] / INVD2LVT
XI3<11> net012[20] net033 DVSS net014[20] / INVD2LVT
XI3<10> net012[21] net033 DVSS net014[21] / INVD2LVT
XI3<9> net012[22] net033 DVSS net014[22] / INVD2LVT
XI3<8> net012[23] net033 DVSS net014[23] / INVD2LVT
XI3<7> net012[24] net033 DVSS net014[24] / INVD2LVT
XI3<6> net012[25] net033 DVSS net014[25] / INVD2LVT
XI3<5> net012[26] net033 DVSS net014[26] / INVD2LVT
XI3<4> net012[27] net033 DVSS net014[27] / INVD2LVT
XI3<3> net012[28] net033 DVSS net014[28] / INVD2LVT
XI3<2> net012[29] net033 DVSS net014[29] / INVD2LVT
XI3<1> net012[30] net033 DVSS net014[30] / INVD2LVT
XI3<0> net012[31] net033 DVSS net014[31] / INVD2LVT
XI1<31> net024[0] net031 DVSS net025[0] / INVD2LVT
XI1<30> net024[1] net031 DVSS net025[1] / INVD2LVT
XI1<29> net024[2] net031 DVSS net025[2] / INVD2LVT
XI1<28> net024[3] net031 DVSS net025[3] / INVD2LVT
XI1<27> net024[4] net031 DVSS net025[4] / INVD2LVT
XI1<26> net024[5] net031 DVSS net025[5] / INVD2LVT
XI1<25> net024[6] net031 DVSS net025[6] / INVD2LVT
XI1<24> net024[7] net031 DVSS net025[7] / INVD2LVT
XI1<23> net024[8] net031 DVSS net025[8] / INVD2LVT
XI1<22> net024[9] net031 DVSS net025[9] / INVD2LVT
XI1<21> net024[10] net031 DVSS net025[10] / INVD2LVT
XI1<20> net024[11] net031 DVSS net025[11] / INVD2LVT
XI1<19> net024[12] net031 DVSS net025[12] / INVD2LVT
XI1<18> net024[13] net031 DVSS net025[13] / INVD2LVT
XI1<17> net024[14] net031 DVSS net025[14] / INVD2LVT
XI1<16> net024[15] net031 DVSS net025[15] / INVD2LVT
XI1<15> net024[16] net031 DVSS net025[16] / INVD2LVT
XI1<14> net024[17] net031 DVSS net025[17] / INVD2LVT
XI1<13> net024[18] net031 DVSS net025[18] / INVD2LVT
XI1<12> net024[19] net031 DVSS net025[19] / INVD2LVT
XI1<11> net024[20] net031 DVSS net025[20] / INVD2LVT
XI1<10> net024[21] net031 DVSS net025[21] / INVD2LVT
XI1<9> net024[22] net031 DVSS net025[22] / INVD2LVT
XI1<8> net024[23] net031 DVSS net025[23] / INVD2LVT
XI1<7> net024[24] net031 DVSS net025[24] / INVD2LVT
XI1<6> net024[25] net031 DVSS net025[25] / INVD2LVT
XI1<5> net024[26] net031 DVSS net025[26] / INVD2LVT
XI1<4> net024[27] net031 DVSS net025[27] / INVD2LVT
XI1<3> net024[28] net031 DVSS net025[28] / INVD2LVT
XI1<2> net024[29] net031 DVSS net025[29] / INVD2LVT
XI1<1> net024[30] net031 DVSS net025[30] / INVD2LVT
XI1<0> net024[31] net031 DVSS net025[31] / INVD2LVT
XI4<31> net014[0] net039 DVSS net015[0] / INVD4LVT
XI4<30> net014[1] net039 DVSS net015[1] / INVD4LVT
XI4<29> net014[2] net039 DVSS net015[2] / INVD4LVT
XI4<28> net014[3] net039 DVSS net015[3] / INVD4LVT
XI4<27> net014[4] net039 DVSS net015[4] / INVD4LVT
XI4<26> net014[5] net039 DVSS net015[5] / INVD4LVT
XI4<25> net014[6] net039 DVSS net015[6] / INVD4LVT
XI4<24> net014[7] net039 DVSS net015[7] / INVD4LVT
XI4<23> net014[8] net039 DVSS net015[8] / INVD4LVT
XI4<22> net014[9] net039 DVSS net015[9] / INVD4LVT
XI4<21> net014[10] net039 DVSS net015[10] / INVD4LVT
XI4<20> net014[11] net039 DVSS net015[11] / INVD4LVT
XI4<19> net014[12] net039 DVSS net015[12] / INVD4LVT
XI4<18> net014[13] net039 DVSS net015[13] / INVD4LVT
XI4<17> net014[14] net039 DVSS net015[14] / INVD4LVT
XI4<16> net014[15] net039 DVSS net015[15] / INVD4LVT
XI4<15> net014[16] net039 DVSS net015[16] / INVD4LVT
XI4<14> net014[17] net039 DVSS net015[17] / INVD4LVT
XI4<13> net014[18] net039 DVSS net015[18] / INVD4LVT
XI4<12> net014[19] net039 DVSS net015[19] / INVD4LVT
XI4<11> net014[20] net039 DVSS net015[20] / INVD4LVT
XI4<10> net014[21] net039 DVSS net015[21] / INVD4LVT
XI4<9> net014[22] net039 DVSS net015[22] / INVD4LVT
XI4<8> net014[23] net039 DVSS net015[23] / INVD4LVT
XI4<7> net014[24] net039 DVSS net015[24] / INVD4LVT
XI4<6> net014[25] net039 DVSS net015[25] / INVD4LVT
XI4<5> net014[26] net039 DVSS net015[26] / INVD4LVT
XI4<4> net014[27] net039 DVSS net015[27] / INVD4LVT
XI4<3> net014[28] net039 DVSS net015[28] / INVD4LVT
XI4<2> net014[29] net039 DVSS net015[29] / INVD4LVT
XI4<1> net014[30] net039 DVSS net015[30] / INVD4LVT
XI4<0> net014[31] net039 DVSS net015[31] / INVD4LVT
XI6<31> net017[0] net051 DVSS A[3] / INVD16LVT
XI6<30> net017[1] net051 DVSS A[2] / INVD16LVT
XI6<29> net017[2] net051 DVSS A[1] / INVD16LVT
XI6<28> net017[3] net051 DVSS A[0] / INVD16LVT
XI6<27> net017[4] net051 DVSS B[3] / INVD16LVT
XI6<26> net017[5] net051 DVSS B[2] / INVD16LVT
XI6<25> net017[6] net051 DVSS B[1] / INVD16LVT
XI6<24> net017[7] net051 DVSS B[0] / INVD16LVT
XI6<23> net017[8] net051 DVSS C[3] / INVD16LVT
XI6<22> net017[9] net051 DVSS C[2] / INVD16LVT
XI6<21> net017[10] net051 DVSS C[1] / INVD16LVT
XI6<20> net017[11] net051 DVSS C[0] / INVD16LVT
XI6<19> net017[12] net051 DVSS D[3] / INVD16LVT
XI6<18> net017[13] net051 DVSS D[2] / INVD16LVT
XI6<17> net017[14] net051 DVSS D[1] / INVD16LVT
XI6<16> net017[15] net051 DVSS D[0] / INVD16LVT
XI6<15> net017[16] net051 DVSS E[3] / INVD16LVT
XI6<14> net017[17] net051 DVSS E[2] / INVD16LVT
XI6<13> net017[18] net051 DVSS E[1] / INVD16LVT
XI6<12> net017[19] net051 DVSS E[0] / INVD16LVT
XI6<11> net017[20] net051 DVSS F[3] / INVD16LVT
XI6<10> net017[21] net051 DVSS F[2] / INVD16LVT
XI6<9> net017[22] net051 DVSS F[1] / INVD16LVT
XI6<8> net017[23] net051 DVSS F[0] / INVD16LVT
XI6<7> net017[24] net051 DVSS G[3] / INVD16LVT
XI6<6> net017[25] net051 DVSS G[2] / INVD16LVT
XI6<5> net017[26] net051 DVSS G[1] / INVD16LVT
XI6<4> net017[27] net051 DVSS G[0] / INVD16LVT
XI6<3> net017[28] net051 DVSS H[3] / INVD16LVT
XI6<2> net017[29] net051 DVSS H[2] / INVD16LVT
XI6<1> net017[30] net051 DVSS H[1] / INVD16LVT
XI6<0> net017[31] net051 DVSS H[0] / INVD16LVT
XI62<31> net026[0] net044 DVSS A[7] / INVD16LVT
XI62<30> net026[1] net044 DVSS A[6] / INVD16LVT
XI62<29> net026[2] net044 DVSS A[5] / INVD16LVT
XI62<28> net026[3] net044 DVSS A[4] / INVD16LVT
XI62<27> net026[4] net044 DVSS B[7] / INVD16LVT
XI62<26> net026[5] net044 DVSS B[6] / INVD16LVT
XI62<25> net026[6] net044 DVSS B[5] / INVD16LVT
XI62<24> net026[7] net044 DVSS B[4] / INVD16LVT
XI62<23> net026[8] net044 DVSS C[7] / INVD16LVT
XI62<22> net026[9] net044 DVSS C[6] / INVD16LVT
XI62<21> net026[10] net044 DVSS C[5] / INVD16LVT
XI62<20> net026[11] net044 DVSS C[4] / INVD16LVT
XI62<19> net026[12] net044 DVSS D[7] / INVD16LVT
XI62<18> net026[13] net044 DVSS D[6] / INVD16LVT
XI62<17> net026[14] net044 DVSS D[5] / INVD16LVT
XI62<16> net026[15] net044 DVSS D[4] / INVD16LVT
XI62<15> net026[16] net044 DVSS E[7] / INVD16LVT
XI62<14> net026[17] net044 DVSS E[6] / INVD16LVT
XI62<13> net026[18] net044 DVSS E[5] / INVD16LVT
XI62<12> net026[19] net044 DVSS E[4] / INVD16LVT
XI62<11> net026[20] net044 DVSS F[7] / INVD16LVT
XI62<10> net026[21] net044 DVSS F[6] / INVD16LVT
XI62<9> net026[22] net044 DVSS F[5] / INVD16LVT
XI62<8> net026[23] net044 DVSS F[4] / INVD16LVT
XI62<7> net026[24] net044 DVSS G[7] / INVD16LVT
XI62<6> net026[25] net044 DVSS G[6] / INVD16LVT
XI62<5> net026[26] net044 DVSS G[5] / INVD16LVT
XI62<4> net026[27] net044 DVSS G[4] / INVD16LVT
XI62<3> net026[28] net044 DVSS H[7] / INVD16LVT
XI62<2> net026[29] net044 DVSS H[6] / INVD16LVT
XI62<1> net026[30] net044 DVSS H[5] / INVD16LVT
XI62<0> net026[31] net044 DVSS H[4] / INVD16LVT
XI28<31> net026[0] net046 DVSS A[7] / INVD16LVT
XI28<30> net026[1] net046 DVSS A[6] / INVD16LVT
XI28<29> net026[2] net046 DVSS A[5] / INVD16LVT
XI28<28> net026[3] net046 DVSS A[4] / INVD16LVT
XI28<27> net026[4] net046 DVSS B[7] / INVD16LVT
XI28<26> net026[5] net046 DVSS B[6] / INVD16LVT
XI28<25> net026[6] net046 DVSS B[5] / INVD16LVT
XI28<24> net026[7] net046 DVSS B[4] / INVD16LVT
XI28<23> net026[8] net046 DVSS C[7] / INVD16LVT
XI28<22> net026[9] net046 DVSS C[6] / INVD16LVT
XI28<21> net026[10] net046 DVSS C[5] / INVD16LVT
XI28<20> net026[11] net046 DVSS C[4] / INVD16LVT
XI28<19> net026[12] net046 DVSS D[7] / INVD16LVT
XI28<18> net026[13] net046 DVSS D[6] / INVD16LVT
XI28<17> net026[14] net046 DVSS D[5] / INVD16LVT
XI28<16> net026[15] net046 DVSS D[4] / INVD16LVT
XI28<15> net026[16] net046 DVSS E[7] / INVD16LVT
XI28<14> net026[17] net046 DVSS E[6] / INVD16LVT
XI28<13> net026[18] net046 DVSS E[5] / INVD16LVT
XI28<12> net026[19] net046 DVSS E[4] / INVD16LVT
XI28<11> net026[20] net046 DVSS F[7] / INVD16LVT
XI28<10> net026[21] net046 DVSS F[6] / INVD16LVT
XI28<9> net026[22] net046 DVSS F[5] / INVD16LVT
XI28<8> net026[23] net046 DVSS F[4] / INVD16LVT
XI28<7> net026[24] net046 DVSS G[7] / INVD16LVT
XI28<6> net026[25] net046 DVSS G[6] / INVD16LVT
XI28<5> net026[26] net046 DVSS G[5] / INVD16LVT
XI28<4> net026[27] net046 DVSS G[4] / INVD16LVT
XI28<3> net026[28] net046 DVSS H[7] / INVD16LVT
XI28<2> net026[29] net046 DVSS H[6] / INVD16LVT
XI28<1> net026[30] net046 DVSS H[5] / INVD16LVT
XI28<0> net026[31] net046 DVSS H[4] / INVD16LVT
XI5<31> net015[0] net048 DVSS net017[0] / INVD8LVT
XI5<30> net015[1] net048 DVSS net017[1] / INVD8LVT
XI5<29> net015[2] net048 DVSS net017[2] / INVD8LVT
XI5<28> net015[3] net048 DVSS net017[3] / INVD8LVT
XI5<27> net015[4] net048 DVSS net017[4] / INVD8LVT
XI5<26> net015[5] net048 DVSS net017[5] / INVD8LVT
XI5<25> net015[6] net048 DVSS net017[6] / INVD8LVT
XI5<24> net015[7] net048 DVSS net017[7] / INVD8LVT
XI5<23> net015[8] net048 DVSS net017[8] / INVD8LVT
XI5<22> net015[9] net048 DVSS net017[9] / INVD8LVT
XI5<21> net015[10] net048 DVSS net017[10] / INVD8LVT
XI5<20> net015[11] net048 DVSS net017[11] / INVD8LVT
XI5<19> net015[12] net048 DVSS net017[12] / INVD8LVT
XI5<18> net015[13] net048 DVSS net017[13] / INVD8LVT
XI5<17> net015[14] net048 DVSS net017[14] / INVD8LVT
XI5<16> net015[15] net048 DVSS net017[15] / INVD8LVT
XI5<15> net015[16] net048 DVSS net017[16] / INVD8LVT
XI5<14> net015[17] net048 DVSS net017[17] / INVD8LVT
XI5<13> net015[18] net048 DVSS net017[18] / INVD8LVT
XI5<12> net015[19] net048 DVSS net017[19] / INVD8LVT
XI5<11> net015[20] net048 DVSS net017[20] / INVD8LVT
XI5<10> net015[21] net048 DVSS net017[21] / INVD8LVT
XI5<9> net015[22] net048 DVSS net017[22] / INVD8LVT
XI5<8> net015[23] net048 DVSS net017[23] / INVD8LVT
XI5<7> net015[24] net048 DVSS net017[24] / INVD8LVT
XI5<6> net015[25] net048 DVSS net017[25] / INVD8LVT
XI5<5> net015[26] net048 DVSS net017[26] / INVD8LVT
XI5<4> net015[27] net048 DVSS net017[27] / INVD8LVT
XI5<3> net015[28] net048 DVSS net017[28] / INVD8LVT
XI5<2> net015[29] net048 DVSS net017[29] / INVD8LVT
XI5<1> net015[30] net048 DVSS net017[30] / INVD8LVT
XI5<0> net015[31] net048 DVSS net017[31] / INVD8LVT
XI63<31> net025[0] net041 DVSS net026[0] / INVD8LVT
XI63<30> net025[1] net041 DVSS net026[1] / INVD8LVT
XI63<29> net025[2] net041 DVSS net026[2] / INVD8LVT
XI63<28> net025[3] net041 DVSS net026[3] / INVD8LVT
XI63<27> net025[4] net041 DVSS net026[4] / INVD8LVT
XI63<26> net025[5] net041 DVSS net026[5] / INVD8LVT
XI63<25> net025[6] net041 DVSS net026[6] / INVD8LVT
XI63<24> net025[7] net041 DVSS net026[7] / INVD8LVT
XI63<23> net025[8] net041 DVSS net026[8] / INVD8LVT
XI63<22> net025[9] net041 DVSS net026[9] / INVD8LVT
XI63<21> net025[10] net041 DVSS net026[10] / INVD8LVT
XI63<20> net025[11] net041 DVSS net026[11] / INVD8LVT
XI63<19> net025[12] net041 DVSS net026[12] / INVD8LVT
XI63<18> net025[13] net041 DVSS net026[13] / INVD8LVT
XI63<17> net025[14] net041 DVSS net026[14] / INVD8LVT
XI63<16> net025[15] net041 DVSS net026[15] / INVD8LVT
XI63<15> net025[16] net041 DVSS net026[16] / INVD8LVT
XI63<14> net025[17] net041 DVSS net026[17] / INVD8LVT
XI63<13> net025[18] net041 DVSS net026[18] / INVD8LVT
XI63<12> net025[19] net041 DVSS net026[19] / INVD8LVT
XI63<11> net025[20] net041 DVSS net026[20] / INVD8LVT
XI63<10> net025[21] net041 DVSS net026[21] / INVD8LVT
XI63<9> net025[22] net041 DVSS net026[22] / INVD8LVT
XI63<8> net025[23] net041 DVSS net026[23] / INVD8LVT
XI63<7> net025[24] net041 DVSS net026[24] / INVD8LVT
XI63<6> net025[25] net041 DVSS net026[25] / INVD8LVT
XI63<5> net025[26] net041 DVSS net026[26] / INVD8LVT
XI63<4> net025[27] net041 DVSS net026[27] / INVD8LVT
XI63<3> net025[28] net041 DVSS net026[28] / INVD8LVT
XI63<2> net025[29] net041 DVSS net026[29] / INVD8LVT
XI63<1> net025[30] net041 DVSS net026[30] / INVD8LVT
XI63<0> net025[31] net041 DVSS net026[31] / INVD8LVT
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    NR2D1LVT
* View Name:    schematic
************************************************************************

.SUBCKT NR2D1LVT A1 A2 VDD VSS ZN
*.PININFO A1:I A2:I ZN:O VDD:B VSS:B
MMI1-M_u3 ZN A2 VSS VSS nch_lvt l=LF w=WE m=1
MMI1-M_u4 ZN A1 VSS VSS nch_lvt l=LF w=WE m=1
MMI1-M_u1 net13 A2 VDD VDD pch_lvt l=LF w=WF m=1
MMI1-M_u2 ZN A1 net13 VDD pch_lvt l=LF w=WF m=1
.ENDS

************************************************************************
* Library Name: AP_SerDes
* Cell Name:    DFF_LVT
* View Name:    schematic
************************************************************************

.SUBCKT DFF_LVT CK D DGND DVDD Q QN
*.PININFO CK:I D:I Q:O QN:O DGND:B DVDD:B
MM7 Q QN DGND DGND nch_lvt l=LF w=WE m=1
MM2 QN CK NET4 DGND nch_lvt l=LF w=WB m=1
MM13 N1 D DGND DGND nch_lvt l=LF w=WB m=1
MM4 NET2 N1 NET3 DGND nch_lvt l=LF w=WB m=1
MM3 NET4 NET2 DGND DGND nch_lvt l=LF w=WE m=1
MM14 NET3 CK DGND DGND nch_lvt l=LF w=WB m=1
MM9 NET2 CK DVDD DVDD pch_lvt l=LF w=WB m=1
MM8 NET1 D DVDD DVDD pch_lvt l=LF w=WB m=1
MM12 Q QN DVDD DVDD pch_lvt l=LF w=WF m=1
MM11 QN NET2 DVDD DVDD pch_lvt l=LF w=WF m=1
MM15 N1 CK NET1 DVDD pch_lvt l=LF w=WB m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    AN2D1LVT
* View Name:    schematic
************************************************************************

.SUBCKT AN2D1LVT A1 A2 VDD VSS Z
*.PININFO A1:I A2:I Z:O VDD:B VSS:B
MM_u3-M_u3 Z net5 VDD VDD pch_lvt l=LF w=WF m=1
MM_u2-M_u1 net5 A1 VDD VDD pch_lvt l=LF w=WD m=1
MM_u2-M_u2 net5 A2 VDD VDD pch_lvt l=LF w=WD m=1
MM_u3-M_u2 Z net5 VSS VSS nch_lvt l=LF w=WE m=1
MM_u2-M_u4 net17 A2 VSS VSS nch_lvt l=LF w=WC m=1
MM_u2-M_u3 net5 A1 net17 VSS nch_lvt l=LF w=WC m=1
.ENDS

************************************************************************
* Library Name: AP_SerDes
* Cell Name:    ENC_8l12b_v2_tspc_stage2_v2
* View Name:    schematic
************************************************************************

.SUBCKT ENC_8l12b_v2_tspc_stage2_v2 CLK DEC20[3] DEC20[2] DEC20[1] DEC20[0] 
+ DEC21[3] DEC21[2] DEC21[1] DEC21[0] DEC64[3] DEC64[2] DEC64[1] DEC64[0] 
+ DEC65[3] DEC65[2] DEC65[1] DEC65[0] DEC83[3] DEC83[2] DEC83[1] DEC83[0] 
+ DEC87[3] DEC87[2] DEC87[1] DEC87[0] DEC93[3] DEC93[2] DEC93[1] DEC93[0] 
+ DEC97[3] DEC97[2] DEC97[1] DEC97[0] DEC103[3] DEC103[2] DEC103[1] DEC103[0] 
+ DEC107[3] DEC107[2] DEC107[1] DEC107[0] DEC113[3] DEC113[2] DEC113[1] 
+ DEC113[0] DEC117[3] DEC117[2] DEC117[1] DEC117[0] DIN[11] DIN[10] DIN[9] 
+ DIN[8] DIN[7] DIN[6] DIN[5] DIN[4] DIN[3] DIN[2] DIN[1] DIN[0] DVDD DVSS
*.PININFO CLK:I DIN[11]:I DIN[10]:I DIN[9]:I DIN[8]:I DIN[7]:I DIN[6]:I 
*.PININFO DIN[5]:I DIN[4]:I DIN[3]:I DIN[2]:I DIN[1]:I DIN[0]:I DEC20[3]:O 
*.PININFO DEC20[2]:O DEC20[1]:O DEC20[0]:O DEC21[3]:O DEC21[2]:O DEC21[1]:O 
*.PININFO DEC21[0]:O DEC64[3]:O DEC64[2]:O DEC64[1]:O DEC64[0]:O DEC65[3]:O 
*.PININFO DEC65[2]:O DEC65[1]:O DEC65[0]:O DEC83[3]:O DEC83[2]:O DEC83[1]:O 
*.PININFO DEC83[0]:O DEC87[3]:O DEC87[2]:O DEC87[1]:O DEC87[0]:O DEC93[3]:O 
*.PININFO DEC93[2]:O DEC93[1]:O DEC93[0]:O DEC97[3]:O DEC97[2]:O DEC97[1]:O 
*.PININFO DEC97[0]:O DEC103[3]:O DEC103[2]:O DEC103[1]:O DEC103[0]:O 
*.PININFO DEC107[3]:O DEC107[2]:O DEC107[1]:O DEC107[0]:O DEC113[3]:O 
*.PININFO DEC113[2]:O DEC113[1]:O DEC113[0]:O DEC117[3]:O DEC117[2]:O 
*.PININFO DEC117[1]:O DEC117[0]:O DVDD:B DVSS:B
XI313<3> net065[0] DVDD DVSS DEC64[3] / INVD2LVT
XI313<2> net065[1] DVDD DVSS DEC64[2] / INVD2LVT
XI313<1> net065[2] DVDD DVSS DEC64[1] / INVD2LVT
XI313<0> net065[3] DVDD DVSS DEC64[0] / INVD2LVT
XI312<3> net066[0] DVDD DVSS DEC65[3] / INVD2LVT
XI312<2> net066[1] DVDD DVSS DEC65[2] / INVD2LVT
XI312<1> net066[2] DVDD DVSS DEC65[1] / INVD2LVT
XI312<0> net066[3] DVDD DVSS DEC65[0] / INVD2LVT
XI309<1> bf[4] DVDD DVSS bzfd[4] / INVD2LVT
XI309<0> bzf[4] DVDD DVSS bfd[4] / INVD2LVT
XI308<1> bf[10] DVDD DVSS bzfd[10] / INVD2LVT
XI308<0> bzf[10] DVDD DVSS bfd[10] / INVD2LVT
XI307<1> bf[6] DVDD DVSS bzfd[6] / INVD2LVT
XI307<0> bzf[6] DVDD DVSS bfd[6] / INVD2LVT
XI306<1> bf[5] DVDD DVSS bzfd[5] / INVD2LVT
XI306<0> bzf[5] DVDD DVSS bfd[5] / INVD2LVT
XI305<1> bf[9] DVDD DVSS bzfd[9] / INVD2LVT
XI305<0> bzf[9] DVDD DVSS bfd[9] / INVD2LVT
XI304<1> bf[0] DVDD DVSS bzfd[0] / INVD2LVT
XI304<0> bzf[0] DVDD DVSS bfd[0] / INVD2LVT
XI303<1> BF[8] DVDD DVSS BZFD[8] / INVD2LVT
XI303<0> BZF[8] DVDD DVSS BFD[8] / INVD2LVT
XI302<1> bf[2] DVDD DVSS bzfd[2] / INVD2LVT
XI302<0> bzf[2] DVDD DVSS bfd[2] / INVD2LVT
XI301<1> bf[1] DVDD DVSS bzfd[1] / INVD2LVT
XI301<0> bzf[1] DVDD DVSS bfd[1] / INVD2LVT
XI300<1> bf[11] DVDD DVSS bzfd[11] / INVD2LVT
XI300<0> bzf[11] DVDD DVSS bfd[11] / INVD2LVT
XI311<3> net067[0] DVDD DVSS DEC20[3] / INVD2LVT
XI311<2> net067[1] DVDD DVSS DEC20[2] / INVD2LVT
XI311<1> net067[2] DVDD DVSS DEC20[1] / INVD2LVT
XI311<0> net067[3] DVDD DVSS DEC20[0] / INVD2LVT
XI299<1> bf[3] DVDD DVSS BZFD[3] / INVD2LVT
XI299<0> bzf[3] DVDD DVSS BFD[3] / INVD2LVT
XI310<3> net068[0] DVDD DVSS DEC21[3] / INVD2LVT
XI310<2> net068[1] DVDD DVSS DEC21[2] / INVD2LVT
XI310<1> net068[2] DVDD DVSS DEC21[1] / INVD2LVT
XI310<0> net068[3] DVDD DVSS DEC21[0] / INVD2LVT
XI249<1> bf[7] DVDD DVSS bzfd[7] / INVD2LVT
XI249<0> bzf[7] DVDD DVSS bfd[7] / INVD2LVT
XI288 CLK DIN[2] DVSS DVDD bf[2] bzf[2] / DFF_LVT
XI298 CLK DIN[3] DVSS DVDD bf[3] bzf[3] / DFF_LVT
XI253<3> CLK net080[0] DVSS DVDD DEC113[3] net076[0] / DFF_LVT
XI253<2> CLK net080[1] DVSS DVDD DEC113[2] net076[1] / DFF_LVT
XI253<1> CLK net080[2] DVSS DVDD DEC113[1] net076[2] / DFF_LVT
XI253<0> CLK net080[3] DVSS DVDD DEC113[0] net076[3] / DFF_LVT
XI259<3> CLK net049[0] DVSS DVDD DEC87[3] net069[0] / DFF_LVT
XI259<2> CLK net049[1] DVSS DVDD DEC87[2] net069[1] / DFF_LVT
XI259<1> CLK net049[2] DVSS DVDD DEC87[1] net069[2] / DFF_LVT
XI259<0> CLK net049[3] DVSS DVDD DEC87[0] net069[3] / DFF_LVT
XI255<3> CLK net051[0] DVSS DVDD DEC107[3] net073[0] / DFF_LVT
XI255<2> CLK net051[1] DVSS DVDD DEC107[2] net073[1] / DFF_LVT
XI255<1> CLK net051[2] DVSS DVDD DEC107[1] net073[2] / DFF_LVT
XI255<0> CLK net051[3] DVSS DVDD DEC107[0] net073[3] / DFF_LVT
XI263<3> CLK net047[0] DVSS DVDD net062[0] net065[0] / DFF_LVT
XI263<2> CLK net047[1] DVSS DVDD net062[1] net065[1] / DFF_LVT
XI263<1> CLK net047[2] DVSS DVDD net062[2] net065[2] / DFF_LVT
XI263<0> CLK net047[3] DVSS DVDD net062[3] net065[3] / DFF_LVT
XI261<3> CLK net048[0] DVSS DVDD net042[0] net067[0] / DFF_LVT
XI261<2> CLK net048[1] DVSS DVDD net042[1] net067[1] / DFF_LVT
XI261<1> CLK net048[2] DVSS DVDD net042[2] net067[2] / DFF_LVT
XI261<0> CLK net048[3] DVSS DVDD net042[3] net067[3] / DFF_LVT
XI238<3> CLK net037[0] DVSS DVDD net061[0] net066[0] / DFF_LVT
XI238<2> CLK net037[1] DVSS DVDD net061[1] net066[1] / DFF_LVT
XI238<1> CLK net037[2] DVSS DVDD net061[2] net066[2] / DFF_LVT
XI238<0> CLK net037[3] DVSS DVDD net061[3] net066[3] / DFF_LVT
XI237<3> CLK net038[0] DVSS DVDD net044[0] net068[0] / DFF_LVT
XI237<2> CLK net038[1] DVSS DVDD net044[1] net068[1] / DFF_LVT
XI237<1> CLK net038[2] DVSS DVDD net044[2] net068[2] / DFF_LVT
XI237<0> CLK net038[3] DVSS DVDD net044[3] net068[3] / DFF_LVT
XI236<3> CLK net045[0] DVSS DVDD DEC83[3] net070[0] / DFF_LVT
XI236<2> CLK net045[1] DVSS DVDD DEC83[2] net070[1] / DFF_LVT
XI236<1> CLK net045[2] DVSS DVDD DEC83[1] net070[2] / DFF_LVT
XI236<0> CLK net045[3] DVSS DVDD DEC83[0] net070[3] / DFF_LVT
XI235<3> CLK net046[0] DVSS DVDD DEC93[3] net072[0] / DFF_LVT
XI235<2> CLK net046[1] DVSS DVDD DEC93[2] net072[1] / DFF_LVT
XI235<1> CLK net046[2] DVSS DVDD DEC93[1] net072[2] / DFF_LVT
XI235<0> CLK net046[3] DVSS DVDD DEC93[0] net072[3] / DFF_LVT
XI296 CLK DIN[6] DVSS DVDD bf[6] bzf[6] / DFF_LVT
XI295 CLK DIN[5] DVSS DVDD bf[5] bzf[5] / DFF_LVT
XI294 CLK DIN[7] DVSS DVDD bf[7] bzf[7] / DFF_LVT
XI293 CLK DIN[9] DVSS DVDD bf[9] bzf[9] / DFF_LVT
XI292 CLK DIN[0] DVSS DVDD bf[0] bzf[0] / DFF_LVT
XI291 CLK DIN[8] DVSS DVDD BF[8] BZF[8] / DFF_LVT
XI257<3> CLK net050[0] DVSS DVDD DEC97[3] net071[0] / DFF_LVT
XI257<2> CLK net050[1] DVSS DVDD DEC97[2] net071[1] / DFF_LVT
XI257<1> CLK net050[2] DVSS DVDD DEC97[1] net071[2] / DFF_LVT
XI257<0> CLK net050[3] DVSS DVDD DEC97[0] net071[3] / DFF_LVT
XI290 CLK DIN[10] DVSS DVDD bf[10] bzf[10] / DFF_LVT
XI289 CLK DIN[1] DVSS DVDD bf[1] bzf[1] / DFF_LVT
XI21 CLK DIN[11] DVSS DVDD bf[11] bzf[11] / DFF_LVT
XI233<3> CLK net052[0] DVSS DVDD DEC117[3] net075[0] / DFF_LVT
XI233<2> CLK net052[1] DVSS DVDD DEC117[2] net075[1] / DFF_LVT
XI233<1> CLK net052[2] DVSS DVDD DEC117[1] net075[2] / DFF_LVT
XI233<0> CLK net052[3] DVSS DVDD DEC117[0] net075[3] / DFF_LVT
XI234<3> CLK net079[0] DVSS DVDD DEC103[3] net074[0] / DFF_LVT
XI234<2> CLK net079[1] DVSS DVDD DEC103[2] net074[1] / DFF_LVT
XI234<1> CLK net079[2] DVSS DVDD DEC103[1] net074[2] / DFF_LVT
XI234<0> CLK net079[3] DVSS DVDD DEC103[0] net074[3] / DFF_LVT
XI297 CLK DIN[4] DVSS DVDD bf[4] bzf[4] / DFF_LVT
XI166<3> BFD[3] bfd[10] DVDD DVSS net079[0] / AN2D1LVT
XI166<2> BZFD[3] bfd[10] DVDD DVSS net079[1] / AN2D1LVT
XI166<1> BFD[3] bzfd[10] DVDD DVSS net079[2] / AN2D1LVT
XI166<0> BZFD[3] bzfd[10] DVDD DVSS net079[3] / AN2D1LVT
XI262<3> bfd[4] bfd[6] DVDD DVSS net047[0] / AN2D1LVT
XI262<2> bzfd[4] bfd[6] DVDD DVSS net047[1] / AN2D1LVT
XI262<1> bfd[4] bzfd[6] DVDD DVSS net047[2] / AN2D1LVT
XI262<0> bzfd[4] bzfd[6] DVDD DVSS net047[3] / AN2D1LVT
XI260<3> bfd[0] bfd[2] DVDD DVSS net048[0] / AN2D1LVT
XI260<2> bzfd[0] bfd[2] DVDD DVSS net048[1] / AN2D1LVT
XI260<1> bfd[0] bzfd[2] DVDD DVSS net048[2] / AN2D1LVT
XI260<0> bzfd[0] bzfd[2] DVDD DVSS net048[3] / AN2D1LVT
XI258<3> bfd[7] BFD[8] DVDD DVSS net049[0] / AN2D1LVT
XI258<2> bzfd[7] BFD[8] DVDD DVSS net049[1] / AN2D1LVT
XI258<1> bfd[7] BZFD[8] DVDD DVSS net049[2] / AN2D1LVT
XI258<0> bzfd[7] BZFD[8] DVDD DVSS net049[3] / AN2D1LVT
XI256<3> bfd[9] bfd[7] DVDD DVSS net050[0] / AN2D1LVT
XI256<2> bfd[9] bzfd[7] DVDD DVSS net050[1] / AN2D1LVT
XI256<1> bzfd[9] bfd[7] DVDD DVSS net050[2] / AN2D1LVT
XI256<0> bzfd[9] bzfd[7] DVDD DVSS net050[3] / AN2D1LVT
XI254<3> bfd[10] bfd[7] DVDD DVSS net051[0] / AN2D1LVT
XI254<2> bfd[10] bzfd[7] DVDD DVSS net051[1] / AN2D1LVT
XI254<1> bzfd[10] bfd[7] DVDD DVSS net051[2] / AN2D1LVT
XI254<0> bzfd[10] bzfd[7] DVDD DVSS net051[3] / AN2D1LVT
XI165<3> bfd[11] bfd[7] DVDD DVSS net052[0] / AN2D1LVT
XI165<2> bfd[11] bzfd[7] DVDD DVSS net052[1] / AN2D1LVT
XI165<1> bzfd[11] bfd[7] DVDD DVSS net052[2] / AN2D1LVT
XI165<0> bzfd[11] bzfd[7] DVDD DVSS net052[3] / AN2D1LVT
XI252<3> bfd[11] BFD[3] DVDD DVSS net080[0] / AN2D1LVT
XI252<2> bfd[11] BZFD[3] DVDD DVSS net080[1] / AN2D1LVT
XI252<1> bzfd[11] BFD[3] DVDD DVSS net080[2] / AN2D1LVT
XI252<0> bzfd[11] BZFD[3] DVDD DVSS net080[3] / AN2D1LVT
XI176<3> bfd[6] bfd[5] DVDD DVSS net037[0] / AN2D1LVT
XI176<2> bfd[6] bzfd[5] DVDD DVSS net037[1] / AN2D1LVT
XI176<1> bzfd[6] bfd[5] DVDD DVSS net037[2] / AN2D1LVT
XI176<0> bzfd[6] bzfd[5] DVDD DVSS net037[3] / AN2D1LVT
XI173<3> bfd[2] bfd[1] DVDD DVSS net038[0] / AN2D1LVT
XI173<2> bfd[2] bzfd[1] DVDD DVSS net038[1] / AN2D1LVT
XI173<1> bzfd[2] bfd[1] DVDD DVSS net038[2] / AN2D1LVT
XI173<0> bzfd[2] bzfd[1] DVDD DVSS net038[3] / AN2D1LVT
XI168<3> BFD[8] BFD[3] DVDD DVSS net045[0] / AN2D1LVT
XI168<2> BFD[8] BZFD[3] DVDD DVSS net045[1] / AN2D1LVT
XI168<1> BZFD[8] BFD[3] DVDD DVSS net045[2] / AN2D1LVT
XI168<0> BZFD[8] BZFD[3] DVDD DVSS net045[3] / AN2D1LVT
XI167<3> bfd[9] BFD[3] DVDD DVSS net046[0] / AN2D1LVT
XI167<2> bfd[9] BZFD[3] DVDD DVSS net046[1] / AN2D1LVT
XI167<1> bzfd[9] BFD[3] DVDD DVSS net046[2] / AN2D1LVT
XI167<0> bzfd[9] BZFD[3] DVDD DVSS net046[3] / AN2D1LVT
.ENDS

************************************************************************
* Library Name: AP_SerDes
* Cell Name:    ENC_8l12b_v2_tspc
* View Name:    schematic
************************************************************************

.SUBCKT ENC_8l12b_v2_tspc A[7] A[6] A[5] A[4] A[3] A[2] A[1] A[0] B[7] B[6] 
+ B[5] B[4] B[3] B[2] B[1] B[0] C[7] C[6] C[5] C[4] C[3] C[2] C[1] C[0] CLK 
+ D[7] D[6] D[5] D[4] D[3] D[2] D[1] D[0] DIN[11] DIN[10] DIN[9] DIN[8] DIN[7] 
+ DIN[6] DIN[5] DIN[4] DIN[3] DIN[2] DIN[1] DIN[0] DVDD DVSS E[7] E[6] E[5] 
+ E[4] E[3] E[2] E[1] E[0] F[7] F[6] F[5] F[4] F[3] F[2] F[1] F[0] G[7] G[6] 
+ G[5] G[4] G[3] G[2] G[1] G[0] H[7] H[6] H[5] H[4] H[3] H[2] H[1] H[0]
*.PININFO CLK:I DIN[11]:I DIN[10]:I DIN[9]:I DIN[8]:I DIN[7]:I DIN[6]:I 
*.PININFO DIN[5]:I DIN[4]:I DIN[3]:I DIN[2]:I DIN[1]:I DIN[0]:I A[7]:O A[6]:O 
*.PININFO A[5]:O A[4]:O A[3]:O A[2]:O A[1]:O A[0]:O B[7]:O B[6]:O B[5]:O 
*.PININFO B[4]:O B[3]:O B[2]:O B[1]:O B[0]:O C[7]:O C[6]:O C[5]:O C[4]:O 
*.PININFO C[3]:O C[2]:O C[1]:O C[0]:O D[7]:O D[6]:O D[5]:O D[4]:O D[3]:O 
*.PININFO D[2]:O D[1]:O D[0]:O E[7]:O E[6]:O E[5]:O E[4]:O E[3]:O E[2]:O 
*.PININFO E[1]:O E[0]:O F[7]:O F[6]:O F[5]:O F[4]:O F[3]:O F[2]:O F[1]:O 
*.PININFO F[0]:O G[7]:O G[6]:O G[5]:O G[4]:O G[3]:O G[2]:O G[1]:O G[0]:O 
*.PININFO H[7]:O H[6]:O H[5]:O H[4]:O H[3]:O H[2]:O H[1]:O H[0]:O DVDD:B DVSS:B
XI281<3> net064[0] net063[0] DVDD DVSS BZ[3] / NR2D1LVT
XI281<2> net064[1] net063[1] DVDD DVSS BZ[2] / NR2D1LVT
XI281<1> net064[2] net063[2] DVDD DVSS BZ[1] / NR2D1LVT
XI281<0> net064[3] net063[3] DVDD DVSS BZ[0] / NR2D1LVT
XI282<3> net0105[0] net0110[0] DVDD DVSS CZ[3] / NR2D1LVT
XI282<2> net0105[1] net0110[1] DVDD DVSS CZ[2] / NR2D1LVT
XI282<1> net0105[2] net0110[2] DVDD DVSS CZ[1] / NR2D1LVT
XI282<0> net0105[3] net0110[3] DVDD DVSS CZ[0] / NR2D1LVT
XI280<3> net0109[0] net0111[0] DVDD DVSS AZ[3] / NR2D1LVT
XI280<2> net0109[1] net0111[1] DVDD DVSS AZ[2] / NR2D1LVT
XI280<1> net0109[2] net0111[2] DVDD DVSS AZ[1] / NR2D1LVT
XI280<0> net0109[3] net0111[3] DVDD DVSS AZ[0] / NR2D1LVT
XI284<3> net0119[0] net0115[0] DVDD DVSS EZ[3] / NR2D1LVT
XI284<2> net0119[1] net0115[1] DVDD DVSS EZ[2] / NR2D1LVT
XI284<1> net0119[2] net0115[2] DVDD DVSS EZ[1] / NR2D1LVT
XI284<0> net0119[3] net0115[3] DVDD DVSS EZ[0] / NR2D1LVT
XI216<3> net084[0] net083[0] DVDD DVSS H[7] / NR2D1LVT
XI216<2> net084[1] net083[1] DVDD DVSS H[6] / NR2D1LVT
XI216<1> net084[2] net083[2] DVDD DVSS H[5] / NR2D1LVT
XI216<0> net084[3] net083[3] DVDD DVSS H[4] / NR2D1LVT
XI215<3> net086[0] net085[0] DVDD DVSS G[7] / NR2D1LVT
XI215<2> net086[1] net085[1] DVDD DVSS G[6] / NR2D1LVT
XI215<1> net086[2] net085[2] DVDD DVSS G[5] / NR2D1LVT
XI215<0> net086[3] net085[3] DVDD DVSS G[4] / NR2D1LVT
XI214<3> net0107[0] net0117[0] DVDD DVSS F[7] / NR2D1LVT
XI214<2> net0107[1] net0117[1] DVDD DVSS F[6] / NR2D1LVT
XI214<1> net0107[2] net0117[2] DVDD DVSS F[5] / NR2D1LVT
XI214<0> net0107[3] net0117[3] DVDD DVSS F[4] / NR2D1LVT
XI212<3> net082[0] net081[0] DVDD DVSS D[7] / NR2D1LVT
XI212<2> net082[1] net081[1] DVDD DVSS D[6] / NR2D1LVT
XI212<1> net082[2] net081[2] DVDD DVSS D[5] / NR2D1LVT
XI212<0> net082[3] net081[3] DVDD DVSS D[4] / NR2D1LVT
XI213<3> net078[0] net077[0] DVDD DVSS E[7] / NR2D1LVT
XI213<2> net078[1] net077[1] DVDD DVSS E[6] / NR2D1LVT
XI213<1> net078[2] net077[2] DVDD DVSS E[5] / NR2D1LVT
XI213<0> net078[3] net077[3] DVDD DVSS E[4] / NR2D1LVT
XI283<3> net058[0] net057[0] DVDD DVSS DZ[3] / NR2D1LVT
XI283<2> net058[1] net057[1] DVDD DVSS DZ[2] / NR2D1LVT
XI283<1> net058[2] net057[2] DVDD DVSS DZ[1] / NR2D1LVT
XI283<0> net058[3] net057[3] DVDD DVSS DZ[0] / NR2D1LVT
XI285<3> net062[0] net061[0] DVDD DVSS FZ[3] / NR2D1LVT
XI285<2> net062[1] net061[1] DVDD DVSS FZ[2] / NR2D1LVT
XI285<1> net062[2] net061[2] DVDD DVSS FZ[1] / NR2D1LVT
XI285<0> net062[3] net061[3] DVDD DVSS FZ[0] / NR2D1LVT
XI286<3> net0113[0] net0108[0] DVDD DVSS GZ[3] / NR2D1LVT
XI286<2> net0113[1] net0108[1] DVDD DVSS GZ[2] / NR2D1LVT
XI286<1> net0113[2] net0108[2] DVDD DVSS GZ[1] / NR2D1LVT
XI286<0> net0113[3] net0108[3] DVDD DVSS GZ[0] / NR2D1LVT
XI287<3> net060[0] net059[0] DVDD DVSS HZ[3] / NR2D1LVT
XI287<2> net060[1] net059[1] DVDD DVSS HZ[2] / NR2D1LVT
XI287<1> net060[2] net059[2] DVDD DVSS HZ[1] / NR2D1LVT
XI287<0> net060[3] net059[3] DVDD DVSS HZ[0] / NR2D1LVT
XI209<3> net0106[0] net0104[0] DVDD DVSS A[7] / NR2D1LVT
XI209<2> net0106[1] net0104[1] DVDD DVSS A[6] / NR2D1LVT
XI209<1> net0106[2] net0104[2] DVDD DVSS A[5] / NR2D1LVT
XI209<0> net0106[3] net0104[3] DVDD DVSS A[4] / NR2D1LVT
XI211<3> net088[0] net087[0] DVDD DVSS C[7] / NR2D1LVT
XI211<2> net088[1] net087[1] DVDD DVSS C[6] / NR2D1LVT
XI211<1> net088[2] net087[2] DVDD DVSS C[5] / NR2D1LVT
XI211<0> net088[3] net087[3] DVDD DVSS C[4] / NR2D1LVT
XI210<3> net0102[0] net0114[0] DVDD DVSS B[7] / NR2D1LVT
XI210<2> net0102[1] net0114[1] DVDD DVSS B[6] / NR2D1LVT
XI210<1> net0102[2] net0114[2] DVDD DVSS B[5] / NR2D1LVT
XI210<0> net0102[3] net0114[3] DVDD DVSS B[4] / NR2D1LVT
XI224<3> HZ[3] DVDD DVSS H[3] / INVD1LVT
XI224<2> HZ[2] DVDD DVSS H[2] / INVD1LVT
XI224<1> HZ[1] DVDD DVSS H[1] / INVD1LVT
XI224<0> HZ[0] DVDD DVSS H[0] / INVD1LVT
XI223<3> GZ[3] DVDD DVSS G[3] / INVD1LVT
XI223<2> GZ[2] DVDD DVSS G[2] / INVD1LVT
XI223<1> GZ[1] DVDD DVSS G[1] / INVD1LVT
XI223<0> GZ[0] DVDD DVSS G[0] / INVD1LVT
XI222<3> FZ[3] DVDD DVSS F[3] / INVD1LVT
XI222<2> FZ[2] DVDD DVSS F[2] / INVD1LVT
XI222<1> FZ[1] DVDD DVSS F[1] / INVD1LVT
XI222<0> FZ[0] DVDD DVSS F[0] / INVD1LVT
XI221<3> EZ[3] DVDD DVSS E[3] / INVD1LVT
XI221<2> EZ[2] DVDD DVSS E[2] / INVD1LVT
XI221<1> EZ[1] DVDD DVSS E[1] / INVD1LVT
XI221<0> EZ[0] DVDD DVSS E[0] / INVD1LVT
XI217<3> AZ[3] DVDD DVSS A[3] / INVD1LVT
XI217<2> AZ[2] DVDD DVSS A[2] / INVD1LVT
XI217<1> AZ[1] DVDD DVSS A[1] / INVD1LVT
XI217<0> AZ[0] DVDD DVSS A[0] / INVD1LVT
XI220<3> DZ[3] DVDD DVSS D[3] / INVD1LVT
XI220<2> DZ[2] DVDD DVSS D[2] / INVD1LVT
XI220<1> DZ[1] DVDD DVSS D[1] / INVD1LVT
XI220<0> DZ[0] DVDD DVSS D[0] / INVD1LVT
XI219<3> CZ[3] DVDD DVSS C[3] / INVD1LVT
XI219<2> CZ[2] DVDD DVSS C[2] / INVD1LVT
XI219<1> CZ[1] DVDD DVSS C[1] / INVD1LVT
XI219<0> CZ[0] DVDD DVSS C[0] / INVD1LVT
XI218<3> BZ[3] DVDD DVSS B[3] / INVD1LVT
XI218<2> BZ[2] DVDD DVSS B[2] / INVD1LVT
XI218<1> BZ[1] DVDD DVSS B[1] / INVD1LVT
XI218<0> BZ[0] DVDD DVSS B[0] / INVD1LVT
XI0 CLK DEC20[3] DEC20[2] DEC20[1] DEC20[0] DEC21[3] DEC21[2] DEC21[1] 
+ DEC21[0] DEC64[3] DEC64[2] DEC64[1] DEC64[0] DEC65[3] DEC65[2] DEC65[1] 
+ DEC65[0] DEC83[3] DEC83[2] DEC83[1] DEC83[0] DEC87[3] DEC87[2] DEC87[1] 
+ DEC87[0] DEC93[3] DEC93[2] DEC93[1] DEC93[0] DEC97[3] DEC97[2] DEC97[1] 
+ DEC97[0] DEC103[3] DEC103[2] DEC103[1] DEC103[0] DEC107[3] DEC107[2] 
+ DEC107[1] DEC107[0] DEC113[3] DEC113[2] DEC113[1] DEC113[0] DEC117[3] 
+ DEC117[2] DEC117[1] DEC117[0] DIN[11] DIN[10] DIN[9] DIN[8] DIN[7] DIN[6] 
+ DIN[5] DIN[4] DIN[3] DIN[2] DIN[1] DIN[0] DVDD DVSS / 
+ ENC_8l12b_v2_tspc_stage2_v2
XI268<3> DEC97[0] DEC64[1] DVDD DVSS net0105[0] / AN2D1LVT
XI268<2> DEC97[0] DEC64[0] DVDD DVSS net0105[1] / AN2D1LVT
XI268<1> DEC97[1] DEC64[1] DVDD DVSS net0105[2] / AN2D1LVT
XI268<0> DEC97[1] DEC64[0] DVDD DVSS net0105[3] / AN2D1LVT
XI276<3> DEC97[2] DEC64[2] DVDD DVSS net0108[0] / AN2D1LVT
XI276<2> DEC97[2] DEC64[3] DVDD DVSS net0108[1] / AN2D1LVT
XI276<1> DEC97[3] DEC64[2] DVDD DVSS net0108[2] / AN2D1LVT
XI276<0> DEC97[3] DEC64[3] DVDD DVSS net0108[3] / AN2D1LVT
XI265<3> DEC87[0] DEC64[0] DVDD DVSS net058[0] / AN2D1LVT
XI265<2> DEC87[0] DEC64[1] DVDD DVSS net058[1] / AN2D1LVT
XI265<1> DEC87[0] DEC65[3] DVDD DVSS net058[2] / AN2D1LVT
XI265<0> DEC87[0] DEC65[2] DVDD DVSS net058[3] / AN2D1LVT
XI177<3> DEC113[3] DEC21[1] DVDD DVSS net0106[0] / AN2D1LVT
XI177<2> DEC113[3] DEC21[0] DVDD DVSS net0106[1] / AN2D1LVT
XI177<1> DEC113[2] DEC21[1] DVDD DVSS net0106[2] / AN2D1LVT
XI177<0> DEC113[2] DEC21[0] DVDD DVSS net0106[3] / AN2D1LVT
XI181<3> DEC93[2] DEC20[1] DVDD DVSS net088[0] / AN2D1LVT
XI181<2> DEC93[2] DEC20[0] DVDD DVSS net088[1] / AN2D1LVT
XI181<1> DEC93[3] DEC20[1] DVDD DVSS net088[2] / AN2D1LVT
XI181<0> DEC93[3] DEC20[0] DVDD DVSS net088[3] / AN2D1LVT
XI271<3> DEC117[1] DEC65[1] DVDD DVSS net0109[0] / AN2D1LVT
XI271<2> DEC117[1] DEC65[0] DVDD DVSS net0109[1] / AN2D1LVT
XI271<1> DEC117[0] DEC65[1] DVDD DVSS net0109[2] / AN2D1LVT
XI271<0> DEC117[0] DEC65[0] DVDD DVSS net0109[3] / AN2D1LVT
XI183<3> DEC83[2] DEC20[0] DVDD DVSS net082[0] / AN2D1LVT
XI183<2> DEC83[2] DEC20[1] DVDD DVSS net082[1] / AN2D1LVT
XI183<1> DEC83[2] DEC21[3] DVDD DVSS net082[2] / AN2D1LVT
XI183<0> DEC83[2] DEC21[2] DVDD DVSS net082[3] / AN2D1LVT
XI179<3> DEC103[2] DEC20[3] DVDD DVSS net0102[0] / AN2D1LVT
XI179<2> DEC103[2] DEC20[2] DVDD DVSS net0102[1] / AN2D1LVT
XI179<1> DEC103[2] DEC21[0] DVDD DVSS net0102[2] / AN2D1LVT
XI179<0> DEC103[2] DEC21[1] DVDD DVSS net0102[3] / AN2D1LVT
XI192<3> DEC83[0] DEC20[0] DVDD DVSS net084[0] / AN2D1LVT
XI192<2> DEC83[0] DEC20[1] DVDD DVSS net084[1] / AN2D1LVT
XI192<1> DEC83[0] DEC21[3] DVDD DVSS net084[2] / AN2D1LVT
XI192<0> DEC83[0] DEC21[2] DVDD DVSS net084[3] / AN2D1LVT
XI190<3> DEC93[0] DEC20[1] DVDD DVSS net086[0] / AN2D1LVT
XI190<2> DEC93[0] DEC20[0] DVDD DVSS net086[1] / AN2D1LVT
XI190<1> DEC93[1] DEC20[1] DVDD DVSS net086[2] / AN2D1LVT
XI190<0> DEC93[1] DEC20[0] DVDD DVSS net086[3] / AN2D1LVT
XI187<3> DEC103[0] DEC20[3] DVDD DVSS net0107[0] / AN2D1LVT
XI187<2> DEC103[0] DEC20[2] DVDD DVSS net0107[1] / AN2D1LVT
XI187<1> DEC103[0] DEC21[0] DVDD DVSS net0107[2] / AN2D1LVT
XI187<0> DEC103[0] DEC21[1] DVDD DVSS net0107[3] / AN2D1LVT
XI184<3> DEC113[1] DEC21[1] DVDD DVSS net078[0] / AN2D1LVT
XI184<2> DEC113[1] DEC21[0] DVDD DVSS net078[1] / AN2D1LVT
XI184<1> DEC113[0] DEC21[1] DVDD DVSS net078[2] / AN2D1LVT
XI184<0> DEC113[0] DEC21[0] DVDD DVSS net078[3] / AN2D1LVT
XI273<3> DEC87[1] DEC65[3] DVDD DVSS net057[0] / AN2D1LVT
XI273<2> DEC87[1] DEC65[2] DVDD DVSS net057[1] / AN2D1LVT
XI273<1> DEC87[1] DEC64[0] DVDD DVSS net057[2] / AN2D1LVT
XI273<0> DEC87[1] DEC64[1] DVDD DVSS net057[3] / AN2D1LVT
XI267<3> DEC97[0] DEC64[2] DVDD DVSS net0110[0] / AN2D1LVT
XI267<2> DEC97[0] DEC64[3] DVDD DVSS net0110[1] / AN2D1LVT
XI267<1> DEC97[1] DEC64[2] DVDD DVSS net0110[2] / AN2D1LVT
XI267<0> DEC97[1] DEC64[3] DVDD DVSS net0110[3] / AN2D1LVT
XI272<3> DEC117[3] DEC65[2] DVDD DVSS net0115[0] / AN2D1LVT
XI272<2> DEC117[3] DEC65[3] DVDD DVSS net0115[1] / AN2D1LVT
XI272<1> DEC117[2] DEC65[2] DVDD DVSS net0115[2] / AN2D1LVT
XI272<0> DEC117[2] DEC65[3] DVDD DVSS net0115[3] / AN2D1LVT
XI270<3> DEC117[1] DEC65[2] DVDD DVSS net0111[0] / AN2D1LVT
XI270<2> DEC117[1] DEC65[3] DVDD DVSS net0111[1] / AN2D1LVT
XI270<1> DEC117[0] DEC65[2] DVDD DVSS net0111[2] / AN2D1LVT
XI270<0> DEC117[0] DEC65[3] DVDD DVSS net0111[3] / AN2D1LVT
XI191<3> DEC83[1] DEC21[3] DVDD DVSS net083[0] / AN2D1LVT
XI191<2> DEC83[1] DEC21[2] DVDD DVSS net083[1] / AN2D1LVT
XI191<1> DEC83[1] DEC20[0] DVDD DVSS net083[2] / AN2D1LVT
XI191<0> DEC83[1] DEC20[1] DVDD DVSS net083[3] / AN2D1LVT
XI189<3> DEC93[0] DEC20[2] DVDD DVSS net085[0] / AN2D1LVT
XI189<2> DEC93[0] DEC20[3] DVDD DVSS net085[1] / AN2D1LVT
XI189<1> DEC93[1] DEC20[2] DVDD DVSS net085[2] / AN2D1LVT
XI189<0> DEC93[1] DEC20[3] DVDD DVSS net085[3] / AN2D1LVT
XI188<3> DEC103[1] DEC21[0] DVDD DVSS net0117[0] / AN2D1LVT
XI188<2> DEC103[1] DEC21[1] DVDD DVSS net0117[1] / AN2D1LVT
XI188<1> DEC103[1] DEC20[3] DVDD DVSS net0117[2] / AN2D1LVT
XI188<0> DEC103[1] DEC20[2] DVDD DVSS net0117[3] / AN2D1LVT
XI178<3> DEC113[3] DEC21[2] DVDD DVSS net0104[0] / AN2D1LVT
XI178<2> DEC113[3] DEC21[3] DVDD DVSS net0104[1] / AN2D1LVT
XI178<1> DEC113[2] DEC21[2] DVDD DVSS net0104[2] / AN2D1LVT
XI178<0> DEC113[2] DEC21[3] DVDD DVSS net0104[3] / AN2D1LVT
XI264<3> DEC107[1] DEC65[0] DVDD DVSS net063[0] / AN2D1LVT
XI264<2> DEC107[1] DEC65[1] DVDD DVSS net063[1] / AN2D1LVT
XI264<1> DEC107[1] DEC64[3] DVDD DVSS net063[2] / AN2D1LVT
XI264<0> DEC107[1] DEC64[2] DVDD DVSS net063[3] / AN2D1LVT
XI275<3> DEC107[3] DEC65[0] DVDD DVSS net061[0] / AN2D1LVT
XI275<2> DEC107[3] DEC65[1] DVDD DVSS net061[1] / AN2D1LVT
XI275<1> DEC107[3] DEC64[3] DVDD DVSS net061[2] / AN2D1LVT
XI275<0> DEC107[3] DEC64[2] DVDD DVSS net061[3] / AN2D1LVT
XI278<3> DEC87[3] DEC65[3] DVDD DVSS net059[0] / AN2D1LVT
XI278<2> DEC87[3] DEC65[2] DVDD DVSS net059[1] / AN2D1LVT
XI278<1> DEC87[3] DEC64[0] DVDD DVSS net059[2] / AN2D1LVT
XI278<0> DEC87[3] DEC64[1] DVDD DVSS net059[3] / AN2D1LVT
XI269<3> DEC117[3] DEC65[1] DVDD DVSS net0119[0] / AN2D1LVT
XI269<2> DEC117[3] DEC65[0] DVDD DVSS net0119[1] / AN2D1LVT
XI269<1> DEC117[2] DEC65[1] DVDD DVSS net0119[2] / AN2D1LVT
XI269<0> DEC117[2] DEC65[0] DVDD DVSS net0119[3] / AN2D1LVT
XI185<3> DEC113[1] DEC21[2] DVDD DVSS net077[0] / AN2D1LVT
XI185<2> DEC113[1] DEC21[3] DVDD DVSS net077[1] / AN2D1LVT
XI185<1> DEC113[0] DEC21[2] DVDD DVSS net077[2] / AN2D1LVT
XI185<0> DEC113[0] DEC21[3] DVDD DVSS net077[3] / AN2D1LVT
XI182<3> DEC93[2] DEC20[2] DVDD DVSS net087[0] / AN2D1LVT
XI182<2> DEC93[2] DEC20[3] DVDD DVSS net087[1] / AN2D1LVT
XI182<1> DEC93[3] DEC20[2] DVDD DVSS net087[2] / AN2D1LVT
XI182<0> DEC93[3] DEC20[3] DVDD DVSS net087[3] / AN2D1LVT
XI180<3> DEC103[3] DEC21[0] DVDD DVSS net0114[0] / AN2D1LVT
XI180<2> DEC103[3] DEC21[1] DVDD DVSS net0114[1] / AN2D1LVT
XI180<1> DEC103[3] DEC20[3] DVDD DVSS net0114[2] / AN2D1LVT
XI180<0> DEC103[3] DEC20[2] DVDD DVSS net0114[3] / AN2D1LVT
XI274<3> DEC107[2] DEC64[3] DVDD DVSS net062[0] / AN2D1LVT
XI274<2> DEC107[2] DEC64[2] DVDD DVSS net062[1] / AN2D1LVT
XI274<1> DEC107[2] DEC65[0] DVDD DVSS net062[2] / AN2D1LVT
XI274<0> DEC107[2] DEC65[1] DVDD DVSS net062[3] / AN2D1LVT
XI186<3> DEC83[3] DEC21[3] DVDD DVSS net081[0] / AN2D1LVT
XI186<2> DEC83[3] DEC21[2] DVDD DVSS net081[1] / AN2D1LVT
XI186<1> DEC83[3] DEC20[0] DVDD DVSS net081[2] / AN2D1LVT
XI186<0> DEC83[3] DEC20[1] DVDD DVSS net081[3] / AN2D1LVT
XI277<3> DEC97[2] DEC64[1] DVDD DVSS net0113[0] / AN2D1LVT
XI277<2> DEC97[2] DEC64[0] DVDD DVSS net0113[1] / AN2D1LVT
XI277<1> DEC97[3] DEC64[1] DVDD DVSS net0113[2] / AN2D1LVT
XI277<0> DEC97[3] DEC64[0] DVDD DVSS net0113[3] / AN2D1LVT
XI279<3> DEC87[2] DEC64[0] DVDD DVSS net060[0] / AN2D1LVT
XI279<2> DEC87[2] DEC64[1] DVDD DVSS net060[1] / AN2D1LVT
XI279<1> DEC87[2] DEC65[3] DVDD DVSS net060[2] / AN2D1LVT
XI279<0> DEC87[2] DEC65[2] DVDD DVSS net060[3] / AN2D1LVT
XI266<3> DEC107[0] DEC64[3] DVDD DVSS net064[0] / AN2D1LVT
XI266<2> DEC107[0] DEC64[2] DVDD DVSS net064[1] / AN2D1LVT
XI266<1> DEC107[0] DEC65[0] DVDD DVSS net064[2] / AN2D1LVT
XI266<0> DEC107[0] DEC65[1] DVDD DVSS net064[3] / AN2D1LVT
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    AN3D1LVT
* View Name:    schematic
************************************************************************

.SUBCKT AN3D1LVT A1 A2 A3 VDD VSS Z
*.PININFO A1:I A2:I A3:I Z:O VDD:B VSS:B
MM_u4-M_u6 net13 A3 VSS VSS nch_lvt l=LF w=WC m=1
MM_u3-M_u2 Z net11 VSS VSS nch_lvt l=LF w=WE m=1
MM_u4-M_u5 net5 A2 net13 VSS nch_lvt l=LF w=WC m=1
MM_u4-M_u4 net11 A1 net5 VSS nch_lvt l=LF w=WC m=1
MM_u3-M_u3 Z net11 VDD VDD pch_lvt l=LF w=WF m=1
MM_u4-M_u3 net11 A3 VDD VDD pch_lvt l=LF w=WD m=1
MM_u4-M_u1 net11 A1 VDD VDD pch_lvt l=LF w=WD m=1
MM_u4-M_u2 net11 A2 VDD VDD pch_lvt l=LF w=WD m=1
.ENDS

************************************************************************
* Library Name: tcbn65lplvt
* Cell Name:    ND2D2LVT
* View Name:    schematic
************************************************************************

.SUBCKT ND2D2LVT A1 A2 VDD VSS ZN
*.PININFO A1:I A2:I ZN:O VDD:B VSS:B
MMU3_1-M_u1 ZN A1 VDD VDD pch_lvt l=LF w=WF m=1
MMU3_1-M_u2 ZN A2 VDD VDD pch_lvt l=LF w=WF m=1
MMU3_0-M_u2 ZN A2 VDD VDD pch_lvt l=LF w=WF m=1
MMU3_0-M_u1 ZN A1 VDD VDD pch_lvt l=LF w=WF m=1
MMU3_0-M_u4 net20 A2 VSS VSS nch_lvt l=LF w=WE m=1
MMU3_1-M_u3 ZN A1 net28 VSS nch_lvt l=LF w=WE m=1
MMU3_1-M_u4 net28 A2 VSS VSS nch_lvt l=LF w=WE m=1
MMU3_0-M_u3 ZN A1 net20 VSS nch_lvt l=LF w=WE m=1
.ENDS

************************************************************************
* Library Name: AP_SerDes
* Cell Name:    Equalizer_8l12b_v7_enable
* View Name:    schematic
************************************************************************

.SUBCKT Equalizer_8l12b_v7_enable DVDD DVSS X[0] X[1] X[2] X[4] X[5] X[6] X[7] 
+ ctop[6] ctop[5] ctop[4] ctop[3] ctop[2] ctop[1] ctop[0] en outx
*.PININFO X[0]:I X[1]:I X[2]:I X[4]:I X[5]:I X[6]:I X[7]:I en:I outx:O DVDD:B 
*.PININFO DVSS:B ctop[6]:B ctop[5]:B ctop[4]:B ctop[3]:B ctop[2]:B ctop[1]:B 
*.PININFO ctop[0]:B
XI6 net6 DVDD DVSS net020 / INVD1LVT
XI3 net8 DVDD DVSS net030 / INVD1LVT
XC0 ctop[5] outx DVDD crtmom nv=32 nh=18 w=WA s=100n stm=3 spm=5 m=1
XC1 ctop[4] outx DVDD crtmom nv=32 nh=18 w=WA s=100n stm=3 spm=5 m=1
XC2 ctop[3] outx DVDD crtmom nv=32 nh=18 w=WA s=100n stm=3 spm=5 m=1
XC5 ctop[6] outx DVDD crtmom nv=32 nh=18 w=WA s=100n stm=3 spm=5 m=1
XC3 ctop[2] outx DVDD crtmom nv=32 nh=18 w=WA s=100n stm=3 spm=5 m=1
XC4 ctop[1] outx DVDD crtmom nv=32 nh=18 w=WA s=100n stm=3 spm=5 m=1
XC6 ctop[0] outx DVDD crtmom nv=32 nh=18 w=WA s=100n stm=3 spm=5 m=1
XI57 X[1] en DVDD DVSS net026 / ND2D1LVT
XI56 X[2] en DVDD DVSS net027 / ND2D1LVT
XI55 X[4] en DVDD DVSS net028 / ND2D1LVT
XI58 X[0] en DVDD DVSS net6 / ND2D1LVT
XI43 X[7] en DVDD DVSS net8 / ND2D1LVT
XI66 net025 DVDD DVSS Xeq[4] / INVD8LVT
XI30 net085 DVDD DVSS Xeq[5] / INVD8LVT
XI26 net066 DVDD DVSS Xeq[2] / INVD8LVT
XI47 net033 DVDD DVSS Xeq[3] / INVD8LVT
XI23 net090 DVDD DVSS Xeq[1] / INVD8LVT
XI19 net092 DVDD DVSS net094 / INVD8LVT
XI16 net098 DVDD DVSS net096 / INVD8LVT
XI53<1> X[7] X[6] en DVDD DVSS net04 / AN3D1LVT
XI53<0> X[7] X[6] en DVDD DVSS net04 / AN3D1LVT
XI0 Xeq[6] DVDD DVSS ctop[6] / INVD16LVT
XI63 Xeq[1] DVDD DVSS ctop[1] / INVD16LVT
XI60 Xeq[4] DVDD DVSS ctop[4] / INVD16LVT
XI59 Xeq[5] DVDD DVSS ctop[5] / INVD16LVT
XI52 net094 DVDD DVSS Xeq[0] / INVD16LVT
XI44 net096 DVDD DVSS Xeq[6] / INVD16LVT
XI61 Xeq[3] DVDD DVSS ctop[3] / INVD16LVT
XI64 Xeq[0] DVDD DVSS ctop[0] / INVD16LVT
XI62 Xeq[2] DVDD DVSS ctop[2] / INVD16LVT
XI54 X[5] en DVDD DVSS net029 / AN2D1LVT
XI40<1> Xeq[4] net023 DVDD DVSS net033 / ND2D2LVT
XI40<0> Xeq[4] net023 DVDD DVSS net033 / ND2D2LVT
XI65 net04 net029 DVDD DVSS net025 / ND2D2LVT
XI73 net015 net090 DVDD DVSS net021 / ND2D2LVT
XI10 net026 net6 DVDD DVSS net063 / ND2D2LVT
XI69 net021 DVDD DVSS net066 / INVD4LVT
XI21 net063 DVDD DVSS net090 / INVD4LVT
XI17 net095 DVDD DVSS net092 / INVD4LVT
XI13 net099 DVDD DVSS net098 / INVD4LVT
XI68 net028 DVDD DVSS net023 / INVD2LVT
XI72 net027 DVDD DVSS net015 / INVD2LVT
XI27 net04 DVDD DVSS net085 / INVD2LVT
XI20 net020 DVDD DVSS net095 / INVD2LVT
XI14 net030 DVDD DVSS net099 / INVD2LVT
.ENDS

************************************************************************
* Library Name: AP_SerDes
* Cell Name:    Equalizer_8l12b_v7_ctrl
* View Name:    schematic
************************************************************************

.SUBCKT Equalizer_8l12b_v7_ctrl Ain[2] Ain[1] Ain[0] Ain[7] Ain[6] Ain[5] 
+ Ain[4] Bin[2] Bin[1] Bin[0] Bin[7] Bin[6] Bin[5] Bin[4] Cin[2] Cin[1] Cin[0] 
+ Cin[7] Cin[6] Cin[5] Cin[4] DVDD DVSS Din[2] Din[1] Din[0] Din[7] Din[6] 
+ Din[5] Din[4] EN[3] EN[2] EN[1] EN[0] Ein[2] Ein[1] Ein[0] Ein[7] Ein[6] 
+ Ein[5] Ein[4] Fin[2] Fin[1] Fin[0] Fin[7] Fin[6] Fin[5] Fin[4] Gin[2] Gin[1] 
+ Gin[0] Gin[7] Gin[6] Gin[5] Gin[4] Hin[2] Hin[1] Hin[0] Hin[7] Hin[6] Hin[5] 
+ Hin[4] Ta Tb Tc Td Te Tf Tg Th
*.PININFO Ain[2]:I Ain[1]:I Ain[0]:I Ain[7]:I Ain[6]:I Ain[5]:I Ain[4]:I 
*.PININFO Bin[2]:I Bin[1]:I Bin[0]:I Bin[7]:I Bin[6]:I Bin[5]:I Bin[4]:I 
*.PININFO Cin[2]:I Cin[1]:I Cin[0]:I Cin[7]:I Cin[6]:I Cin[5]:I Cin[4]:I 
*.PININFO Din[2]:I Din[1]:I Din[0]:I Din[7]:I Din[6]:I Din[5]:I Din[4]:I 
*.PININFO EN[3]:I EN[2]:I EN[1]:I EN[0]:I Ein[2]:I Ein[1]:I Ein[0]:I Ein[7]:I 
*.PININFO Ein[6]:I Ein[5]:I Ein[4]:I Fin[2]:I Fin[1]:I Fin[0]:I Fin[7]:I 
*.PININFO Fin[6]:I Fin[5]:I Fin[4]:I Gin[2]:I Gin[1]:I Gin[0]:I Gin[7]:I 
*.PININFO Gin[6]:I Gin[5]:I Gin[4]:I Hin[2]:I Hin[1]:I Hin[0]:I Hin[7]:I 
*.PININFO Hin[6]:I Hin[5]:I Hin[4]:I Ta:O Tb:O Tc:O Td:O Te:O Tf:O Tg:O Th:O 
*.PININFO DVDD:B DVSS:B
XI3<7> DVDD DVSS Ain[0] Ain[1] Ain[2] Ain[4] Ain[5] Ain[6] Ain[7] At0[6] 
+ At0[5] At0[4] At0[3] At0[2] At0[1] At0[0] EN[0] Ta / 
+ Equalizer_8l12b_v7_enable
XI3<6> DVDD DVSS Bin[0] Bin[1] Bin[2] Bin[4] Bin[5] Bin[6] Bin[7] Bt0[6] 
+ Bt0[5] Bt0[4] Bt0[3] Bt0[2] Bt0[1] Bt0[0] EN[0] Tb / 
+ Equalizer_8l12b_v7_enable
XI3<5> DVDD DVSS Cin[0] Cin[1] Cin[2] Cin[4] Cin[5] Cin[6] Cin[7] Ct0[6] 
+ Ct0[5] Ct0[4] Ct0[3] Ct0[2] Ct0[1] Ct0[0] EN[0] Tc / 
+ Equalizer_8l12b_v7_enable
XI3<4> DVDD DVSS Din[0] Din[1] Din[2] Din[4] Din[5] Din[6] Din[7] Dt0[6] 
+ Dt0[5] Dt0[4] Dt0[3] Dt0[2] Dt0[1] Dt0[0] EN[0] Td / 
+ Equalizer_8l12b_v7_enable
XI3<3> DVDD DVSS Ein[0] Ein[1] Ein[2] Ein[4] Ein[5] Ein[6] Ein[7] Et0[6] 
+ Et0[5] Et0[4] Et0[3] Et0[2] Et0[1] Et0[0] EN[0] Te / 
+ Equalizer_8l12b_v7_enable
XI3<2> DVDD DVSS Fin[0] Fin[1] Fin[2] Fin[4] Fin[5] Fin[6] Fin[7] Ft0[6] 
+ Ft0[5] Ft0[4] Ft0[3] Ft0[2] Ft0[1] Ft0[0] EN[0] Tf / 
+ Equalizer_8l12b_v7_enable
XI3<1> DVDD DVSS Gin[0] Gin[1] Gin[2] Gin[4] Gin[5] Gin[6] Gin[7] Gt0[6] 
+ Gt0[5] Gt0[4] Gt0[3] Gt0[2] Gt0[1] Gt0[0] EN[0] Tg / 
+ Equalizer_8l12b_v7_enable
XI3<0> DVDD DVSS Hin[0] Hin[1] Hin[2] Hin[4] Hin[5] Hin[6] Hin[7] Ht0[6] 
+ Ht0[5] Ht0[4] Ht0[3] Ht0[2] Ht0[1] Ht0[0] EN[0] Th / 
+ Equalizer_8l12b_v7_enable
XI2<7> DVDD DVSS Ain[0] Ain[1] Ain[2] Ain[4] Ain[5] Ain[6] Ain[7] At1[6] 
+ At1[5] At1[4] At1[3] At1[2] At1[1] At1[0] EN[1] Ta / 
+ Equalizer_8l12b_v7_enable
XI2<6> DVDD DVSS Bin[0] Bin[1] Bin[2] Bin[4] Bin[5] Bin[6] Bin[7] Bt1[6] 
+ Bt1[5] Bt1[4] Bt1[3] Bt1[2] Bt1[1] Bt1[0] EN[1] Tb / 
+ Equalizer_8l12b_v7_enable
XI2<5> DVDD DVSS Cin[0] Cin[1] Cin[2] Cin[4] Cin[5] Cin[6] Cin[7] Ct1[6] 
+ Ct1[5] Ct1[4] Ct1[3] Ct1[2] Ct1[1] Ct1[0] EN[1] Tc / 
+ Equalizer_8l12b_v7_enable
XI2<4> DVDD DVSS Din[0] Din[1] Din[2] Din[4] Din[5] Din[6] Din[7] Dt1[6] 
+ Dt1[5] Dt1[4] Dt1[3] Dt1[2] Dt1[1] Dt1[0] EN[1] Td / 
+ Equalizer_8l12b_v7_enable
XI2<3> DVDD DVSS Ein[0] Ein[1] Ein[2] Ein[4] Ein[5] Ein[6] Ein[7] Et1[6] 
+ Et1[5] Et1[4] Et1[3] Et1[2] Et1[1] Et1[0] EN[1] Te / 
+ Equalizer_8l12b_v7_enable
XI2<2> DVDD DVSS Fin[0] Fin[1] Fin[2] Fin[4] Fin[5] Fin[6] Fin[7] Ft1[6] 
+ Ft1[5] Ft1[4] Ft1[3] Ft1[2] Ft1[1] Ft1[0] EN[1] Tf / 
+ Equalizer_8l12b_v7_enable
XI2<1> DVDD DVSS Gin[0] Gin[1] Gin[2] Gin[4] Gin[5] Gin[6] Gin[7] Gt1[6] 
+ Gt1[5] Gt1[4] Gt1[3] Gt1[2] Gt1[1] Gt1[0] EN[1] Tg / 
+ Equalizer_8l12b_v7_enable
XI2<0> DVDD DVSS Hin[0] Hin[1] Hin[2] Hin[4] Hin[5] Hin[6] Hin[7] Ht1[6] 
+ Ht1[5] Ht1[4] Ht1[3] Ht1[2] Ht1[1] Ht1[0] EN[1] Th / 
+ Equalizer_8l12b_v7_enable
XI0<7> DVDD DVSS Ain[0] Ain[1] Ain[2] Ain[4] Ain[5] Ain[6] Ain[7] At3[6] 
+ At3[5] At3[4] At3[3] At3[2] At3[1] At3[0] EN[3] Ta / 
+ Equalizer_8l12b_v7_enable
XI0<6> DVDD DVSS Bin[0] Bin[1] Bin[2] Bin[4] Bin[5] Bin[6] Bin[7] Bt3[6] 
+ Bt3[5] Bt3[4] Bt3[3] Bt3[2] Bt3[1] Bt3[0] EN[3] Tb / 
+ Equalizer_8l12b_v7_enable
XI0<5> DVDD DVSS Cin[0] Cin[1] Cin[2] Cin[4] Cin[5] Cin[6] Cin[7] Ct3[6] 
+ Ct3[5] Ct3[4] Ct3[3] Ct3[2] Ct3[1] Ct3[0] EN[3] Tc / 
+ Equalizer_8l12b_v7_enable
XI0<4> DVDD DVSS Din[0] Din[1] Din[2] Din[4] Din[5] Din[6] Din[7] Dt3[6] 
+ Dt3[5] Dt3[4] Dt3[3] Dt3[2] Dt3[1] Dt3[0] EN[3] Td / 
+ Equalizer_8l12b_v7_enable
XI0<3> DVDD DVSS Ein[0] Ein[1] Ein[2] Ein[4] Ein[5] Ein[6] Ein[7] Et3[6] 
+ Et3[5] Et3[4] Et3[3] Et3[2] Et3[1] Et3[0] EN[3] Te / 
+ Equalizer_8l12b_v7_enable
XI0<2> DVDD DVSS Fin[0] Fin[1] Fin[2] Fin[4] Fin[5] Fin[6] Fin[7] Ft3[6] 
+ Ft3[5] Ft3[4] Ft3[3] Ft3[2] Ft3[1] Ft3[0] EN[3] Tf / 
+ Equalizer_8l12b_v7_enable
XI0<1> DVDD DVSS Gin[0] Gin[1] Gin[2] Gin[4] Gin[5] Gin[6] Gin[7] Gt3[6] 
+ Gt3[5] Gt3[4] Gt3[3] Gt3[2] Gt3[1] Gt3[0] EN[3] Tg / 
+ Equalizer_8l12b_v7_enable
XI0<0> DVDD DVSS Hin[0] Hin[1] Hin[2] Hin[4] Hin[5] Hin[6] Hin[7] Ht3[6] 
+ Ht3[5] Ht3[4] Ht3[3] Ht3[2] Ht3[1] Ht3[0] EN[3] Th / 
+ Equalizer_8l12b_v7_enable
XI1<7> DVDD DVSS Ain[0] Ain[1] Ain[2] Ain[4] Ain[5] Ain[6] Ain[7] At2[6] 
+ At2[5] At2[4] At2[3] At2[2] At2[1] At2[0] EN[2] Ta / 
+ Equalizer_8l12b_v7_enable
XI1<6> DVDD DVSS Bin[0] Bin[1] Bin[2] Bin[4] Bin[5] Bin[6] Bin[7] Bt2[6] 
+ Bt2[5] Bt2[4] Bt2[3] Bt2[2] Bt2[1] Bt2[0] EN[2] Tb / 
+ Equalizer_8l12b_v7_enable
XI1<5> DVDD DVSS Cin[0] Cin[1] Cin[2] Cin[4] Cin[5] Cin[6] Cin[7] Ct2[6] 
+ Ct2[5] Ct2[4] Ct2[3] Ct2[2] Ct2[1] Ct2[0] EN[2] Tc / 
+ Equalizer_8l12b_v7_enable
XI1<4> DVDD DVSS Din[0] Din[1] Din[2] Din[4] Din[5] Din[6] Din[7] Dt2[6] 
+ Dt2[5] Dt2[4] Dt2[3] Dt2[2] Dt2[1] Dt2[0] EN[2] Td / 
+ Equalizer_8l12b_v7_enable
XI1<3> DVDD DVSS Ein[0] Ein[1] Ein[2] Ein[4] Ein[5] Ein[6] Ein[7] Et2[6] 
+ Et2[5] Et2[4] Et2[3] Et2[2] Et2[1] Et2[0] EN[2] Te / 
+ Equalizer_8l12b_v7_enable
XI1<2> DVDD DVSS Fin[0] Fin[1] Fin[2] Fin[4] Fin[5] Fin[6] Fin[7] Ft2[6] 
+ Ft2[5] Ft2[4] Ft2[3] Ft2[2] Ft2[1] Ft2[0] EN[2] Tf / 
+ Equalizer_8l12b_v7_enable
XI1<1> DVDD DVSS Gin[0] Gin[1] Gin[2] Gin[4] Gin[5] Gin[6] Gin[7] Gt2[6] 
+ Gt2[5] Gt2[4] Gt2[3] Gt2[2] Gt2[1] Gt2[0] EN[2] Tg / 
+ Equalizer_8l12b_v7_enable
XI1<0> DVDD DVSS Hin[0] Hin[1] Hin[2] Hin[4] Hin[5] Hin[6] Hin[7] Ht2[6] 
+ Ht2[5] Ht2[4] Ht2[3] Ht2[2] Ht2[1] Ht2[0] EN[2] Th / 
+ Equalizer_8l12b_v7_enable
.ENDS

************************************************************************
* Library Name: AP_SerDes
* Cell Name:    TX_8l12b
* View Name:    schematic
************************************************************************

.SUBCKT Sanitized_TX_8l12b AVDD AVSS CALIN1[3] CALIN1[2] CALIN1[1] CALIN1[0] CALIN3[3] 
+ CALIN3[2] CALIN3[1] CALIN3[0] CALIN5[3] CALIN5[2] CALIN5[1] CALIN5[0] 
+ CALIN7[3] CALIN7[2] CALIN7[1] CALIN7[0] CALIP1[3] CALIP1[2] CALIP1[1] 
+ CALIP1[0] CALIP3[3] CALIP3[2] CALIP3[1] CALIP3[0] CALIP5[3] CALIP5[2] 
+ CALIP5[1] CALIP5[0] CALIP7[3] CALIP7[2] CALIP7[1] CALIP7[0] CLKTXe CLKTXo 
+ DINe[11] DINe[10] DINe[9] DINe[8] DINe[7] DINe[6] DINe[5] DINe[4] DINe[3] 
+ DINe[2] DINe[1] DINe[0] DINo[11] DINo[10] DINo[9] DINo[8] DINo[7] DINo[6] 
+ DINo[5] DINo[4] DINo[3] DINo[2] DINo[1] DINo[0] DVDD DVSS EQUA_EN[3] 
+ EQUA_EN[2] EQUA_EN[1] EQUA_EN[0] Ibg Ta Tb Tc Td Te Tf Tg Th ntx
*.PININFO CALIN1[3]:I CALIN1[2]:I CALIN1[1]:I CALIN1[0]:I CALIN3[3]:I 
*.PININFO CALIN3[2]:I CALIN3[1]:I CALIN3[0]:I CALIN5[3]:I CALIN5[2]:I 
*.PININFO CALIN5[1]:I CALIN5[0]:I CALIN7[3]:I CALIN7[2]:I CALIN7[1]:I 
*.PININFO CALIN7[0]:I CALIP1[3]:I CALIP1[2]:I CALIP1[1]:I CALIP1[0]:I 
*.PININFO CALIP3[3]:I CALIP3[2]:I CALIP3[1]:I CALIP3[0]:I CALIP5[3]:I 
*.PININFO CALIP5[2]:I CALIP5[1]:I CALIP5[0]:I CALIP7[3]:I CALIP7[2]:I 
*.PININFO CALIP7[1]:I CALIP7[0]:I CLKTXe:I CLKTXo:I DINe[11]:I DINe[10]:I 
*.PININFO DINe[9]:I DINe[8]:I DINe[7]:I DINe[6]:I DINe[5]:I DINe[4]:I 
*.PININFO DINe[3]:I DINe[2]:I DINe[1]:I DINe[0]:I DINo[11]:I DINo[10]:I 
*.PININFO DINo[9]:I DINo[8]:I DINo[7]:I DINo[6]:I DINo[5]:I DINo[4]:I 
*.PININFO DINo[3]:I DINo[2]:I DINo[1]:I DINo[0]:I EQUA_EN[3]:I EQUA_EN[2]:I 
*.PININFO EQUA_EN[1]:I EQUA_EN[0]:I Ibg:I Ta:O Tb:O Tc:O Td:O Te:O Tf:O Tg:O 
*.PININFO Th:O AVDD:B AVSS:B DVDD:B DVSS:B ntx:B
XI3 AVDD_Bias AVSS CALIN1[3] CALIN1[2] CALIN1[1] CALIN1[0] CALIN3[3] CALIN3[2] 
+ CALIN3[1] CALIN3[0] CALIN5[3] CALIN5[2] CALIN5[1] CALIN5[0] CALIN7[3] 
+ CALIN7[2] CALIN7[1] CALIN7[0] CALIP1[3] CALIP1[2] CALIP1[1] CALIP1[0] 
+ CALIP3[3] CALIP3[2] CALIP3[1] CALIP3[0] CALIP5[3] CALIP5[2] CALIP5[1] 
+ CALIP5[0] CALIP7[3] CALIP7[2] CALIP7[1] CALIP7[0] Ibg In_1m In_3m In_5m 
+ In_7m Ip_1m Ip_3m Ip_5m Ip_7m / Bias_v2
XI59 Ain[7] Ain[6] Ain[5] Ain[4] Ain[3] Ain[2] Ain[1] Ain[0] Ae[7] Ae[6] Ae[5] 
+ Ae[4] Ae[3] Ae[2] Ae[1] Ae[0] Ao[7] Ao[6] Ao[5] Ao[4] Ao[3] Ao[2] Ao[1] 
+ Ao[0] Bin[7] Bin[6] Bin[5] Bin[4] Bin[3] Bin[2] Bin[1] Bin[0] Be[7] Be[6] 
+ Be[5] Be[4] Be[3] Be[2] Be[1] Be[0] Bo[7] Bo[6] Bo[5] Bo[4] Bo[3] Bo[2] 
+ Bo[1] Bo[0] Cin[7] Cin[6] Cin[5] Cin[4] Cin[3] Cin[2] Cin[1] Cin[0] Ce[7] 
+ Ce[6] Ce[5] Ce[4] Ce[3] Ce[2] Ce[1] Ce[0] CLKTXo CLKTXe Co[7] Co[6] Co[5] 
+ Co[4] Co[3] Co[2] Co[1] Co[0] Din[7] Din[6] Din[5] Din[4] Din[3] Din[2] 
+ Din[1] Din[0] De[7] De[6] De[5] De[4] De[3] De[2] De[1] De[0] Do[7] Do[6] 
+ Do[5] Do[4] Do[3] Do[2] Do[1] Do[0] DVDD_MUX DVSS Ein[7] Ein[6] Ein[5] 
+ Ein[4] Ein[3] Ein[2] Ein[1] Ein[0] Ee[7] Ee[6] Ee[5] Ee[4] Ee[3] Ee[2] Ee[1] 
+ Ee[0] Eo[7] Eo[6] Eo[5] Eo[4] Eo[3] Eo[2] Eo[1] Eo[0] Fin[7] Fin[6] Fin[5] 
+ Fin[4] Fin[3] Fin[2] Fin[1] Fin[0] Fe[7] Fe[6] Fe[5] Fe[4] Fe[3] Fe[2] Fe[1] 
+ Fe[0] Fo[7] Fo[6] Fo[5] Fo[4] Fo[3] Fo[2] Fo[1] Fo[0] Gin[7] Gin[6] Gin[5] 
+ Gin[4] Gin[3] Gin[2] Gin[1] Gin[0] Ge[7] Ge[6] Ge[5] Ge[4] Ge[3] Ge[2] Ge[1] 
+ Ge[0] Go[7] Go[6] Go[5] Go[4] Go[3] Go[2] Go[1] Go[0] Hin[7] Hin[6] Hin[5] 
+ Hin[4] Hin[3] Hin[2] Hin[1] Hin[0] He[7] He[6] He[5] He[4] He[3] He[2] He[1] 
+ He[0] Ho[7] Ho[6] Ho[5] Ho[4] Ho[3] Ho[2] Ho[1] Ho[0] / MUX2to1_dig
XI2 A[7] A[6] A[5] A[4] A[3] A[2] A[1] A[0] AVDD_CML AVSS B[7] B[6] B[5] B[4] 
+ B[3] B[2] B[1] B[0] C[7] C[6] C[5] C[4] C[3] C[2] C[1] C[0] D[7] D[6] D[5] 
+ D[4] D[3] D[2] D[1] D[0] E[7] E[6] E[5] E[4] E[3] E[2] E[1] E[0] F[7] F[6] 
+ F[5] F[4] F[3] F[2] F[1] F[0] G[7] G[6] G[5] G[4] G[3] G[2] G[1] G[0] H[7] 
+ H[6] H[5] H[4] H[3] H[2] H[1] H[0] In_1m In_3m In_5m In_7m Ip_1m Ip_3m Ip_5m 
+ Ip_7m ntx Ta Tb Tc Td Te Tf Tg Th / CML_Driver_PAM8_woCS_v3
XI51 A[7] A[6] A[5] A[4] A[3] A[2] A[1] A[0] Ain[7] Ain[6] Ain[5] Ain[4] 
+ Ain[3] Ain[2] Ain[1] Ain[0] B[7] B[6] B[5] B[4] B[3] B[2] B[1] B[0] Bin[7] 
+ Bin[6] Bin[5] Bin[4] Bin[3] Bin[2] Bin[1] Bin[0] C[7] C[6] C[5] C[4] C[3] 
+ C[2] C[1] C[0] Cin[7] Cin[6] Cin[5] Cin[4] Cin[3] Cin[2] Cin[1] Cin[0] D[7] 
+ D[6] D[5] D[4] D[3] D[2] D[1] D[0] DVDD_PreDriver DVSS Din[7] Din[6] Din[5] 
+ Din[4] Din[3] Din[2] Din[1] Din[0] E[7] E[6] E[5] E[4] E[3] E[2] E[1] E[0] 
+ Ein[7] Ein[6] Ein[5] Ein[4] Ein[3] Ein[2] Ein[1] Ein[0] F[7] F[6] F[5] F[4] 
+ F[3] F[2] F[1] F[0] Fin[7] Fin[6] Fin[5] Fin[4] Fin[3] Fin[2] Fin[1] Fin[0] 
+ G[7] G[6] G[5] G[4] G[3] G[2] G[1] G[0] Gin[7] Gin[6] Gin[5] Gin[4] Gin[3] 
+ Gin[2] Gin[1] Gin[0] H[7] H[6] H[5] H[4] H[3] H[2] H[1] H[0] Hin[7] Hin[6] 
+ Hin[5] Hin[4] Hin[3] Hin[2] Hin[1] Hin[0] / PreDriver_PAM8_v4
XI0<1> Ae[7] Ae[6] Ae[5] Ae[4] Ae[3] Ae[2] Ae[1] Ae[0] Be[7] Be[6] Be[5] Be[4] 
+ Be[3] Be[2] Be[1] Be[0] Ce[7] Ce[6] Ce[5] Ce[4] Ce[3] Ce[2] Ce[1] Ce[0] 
+ CLKTXe De[7] De[6] De[5] De[4] De[3] De[2] De[1] De[0] DINe[11] DINe[10] 
+ DINe[9] DINe[8] DINe[7] DINe[6] DINe[5] DINe[4] DINe[3] DINe[2] DINe[1] 
+ DINe[0] DVDD_ENC DVSS Ee[7] Ee[6] Ee[5] Ee[4] Ee[3] Ee[2] Ee[1] Ee[0] Fe[7] 
+ Fe[6] Fe[5] Fe[4] Fe[3] Fe[2] Fe[1] Fe[0] Ge[7] Ge[6] Ge[5] Ge[4] Ge[3] 
+ Ge[2] Ge[1] Ge[0] He[7] He[6] He[5] He[4] He[3] He[2] He[1] He[0] / 
+ ENC_8l12b_v2_tspc
XI0<0> Ao[7] Ao[6] Ao[5] Ao[4] Ao[3] Ao[2] Ao[1] Ao[0] Bo[7] Bo[6] Bo[5] Bo[4] 
+ Bo[3] Bo[2] Bo[1] Bo[0] Co[7] Co[6] Co[5] Co[4] Co[3] Co[2] Co[1] Co[0] 
+ CLKTXo Do[7] Do[6] Do[5] Do[4] Do[3] Do[2] Do[1] Do[0] DINo[11] DINo[10] 
+ DINo[9] DINo[8] DINo[7] DINo[6] DINo[5] DINo[4] DINo[3] DINo[2] DINo[1] 
+ DINo[0] DVDD_ENC DVSS Eo[7] Eo[6] Eo[5] Eo[4] Eo[3] Eo[2] Eo[1] Eo[0] Fo[7] 
+ Fo[6] Fo[5] Fo[4] Fo[3] Fo[2] Fo[1] Fo[0] Go[7] Go[6] Go[5] Go[4] Go[3] 
+ Go[2] Go[1] Go[0] Ho[7] Ho[6] Ho[5] Ho[4] Ho[3] Ho[2] Ho[1] Ho[0] / 
+ ENC_8l12b_v2_tspc
XI4 Ain[2] Ain[1] Ain[0] Ain[7] Ain[6] Ain[5] Ain[4] Bin[2] Bin[1] Bin[0] 
+ Bin[7] Bin[6] Bin[5] Bin[4] Cin[2] Cin[1] Cin[0] Cin[7] Cin[6] Cin[5] Cin[4] 
+ DVDD_Equal DVSS Din[2] Din[1] Din[0] Din[7] Din[6] Din[5] Din[4] EQUA_EN[3] 
+ EQUA_EN[2] EQUA_EN[1] EQUA_EN[0] Ein[2] Ein[1] Ein[0] Ein[7] Ein[6] Ein[5] 
+ Ein[4] Fin[2] Fin[1] Fin[0] Fin[7] Fin[6] Fin[5] Fin[4] Gin[2] Gin[1] Gin[0] 
+ Gin[7] Gin[6] Gin[5] Gin[4] Hin[2] Hin[1] Hin[0] Hin[7] Hin[6] Hin[5] Hin[4] 
+ Ta Tb Tc Td Te Tf Tg Th / Equalizer_8l12b_v7_ctrl
.ENDS

