.PARAM av=500 c1=100f c2=0.183854p c21=129.48f c22=190.667f c3=200.0f c41=209.575f c42=567.396f ca=1387.171f cb=1.111901p cc=1.446156p  cd=1.443078p ce=827.441f cl=100.0f co1=177.112f co2=120.275f co3=100.0f co4=100.0f co5=114.172f co6=152.861f co7=202.212f co8=100.0f

.subckt two_stage_ota_schematic id vdd vinn vinp vout vss
M6 net3 id vss vss nfet nf=4 l=14e-9 nfin=2 stack=2
Mn3 id id vss vss nfet nf=2 l=14e-9 nfin=2 stack=2
Mn7 vout id vss vss nfet nf=6 l=14e-9 nfin=2 stack=2
Mn1 net33 vinp net3 vss nfet nf=8 l=14e-9 nfin=4 stack=2
Mn0 net1 vinn net3 vss nfet nf=8 l=14e-9 nfin=4 stack=2
Mp2 vout net33 vdd vdd pfet nf=10 l=14e-9 nfin=6 stack=2
Mp1 net33 net1 vdd vdd pfet nf=2 l=14e-9 nfin=4 stack=2
Mp0 net1 net1 vdd vdd pfet nf=2 l=14e-9 nfin=4 stack=2
c0 net2 vout 1e-12
r0 net33 net2 1.5e3
.ends two_stage_ota_schematic


.subckt switch d nb ng pb pg s
Mn0 d ng s nb nfet m=1 l=14e-9 nfin=8 nf=8
Mp0 d pg s pb pfet m=1 l=14e-9 nfin=8 nf=8
.ends switch

.subckt ladder_filter avss vss id phi1 phi1_bar phi2 phi2_bar vdd vin vout
c17 out3 in3 cc
c20 net14 net10 cl
c19 vout in5 ce
c18 in4 out4 cd
c16 in2 out2 cb
c15 out3 in5 c42
c14 in3 vout c41
c13 net17 net10 co7
c12 net16 net17 co5
c11 net18 net14 co8
c10 net19 net18 co6
c9 net20 net19 co4
c8 net15 net20 co2
c7 net1 net16 co3
c6 in1 out3 c22
c5 out1 in3 c21
c4 net044 net1 co1
c3 net15 net044 c2
c2 out1 in1 ca
c1 net044 net21 c3
c0 net31 vin c1
xi7 id vdd in1 avss out1 vss two_stage_ota_schematic
xi6 id vdd in5 avss vout vss two_stage_ota_schematic
xi5 id vdd in4 avss out4 vss two_stage_ota_schematic
xi4 id vdd in3 avss out3 vss two_stage_ota_schematic
xi2 id vdd in2 avss out2 vss two_stage_ota_schematic
xi30 net14 vss phi2 vdd phi2_bar vout switch
xi29 avss vss phi1 vdd phi1_bar net14 switch
xi28 in5 vss phi2 vdd phi2_bar net10 switch
xi27 net10 vss phi1 vdd phi1_bar agnd switch
xi26 out4 vss phi2 vdd phi2_bar net17 switch
xi25 net17 vss phi1 vdd phi1_bar agnd switch
xi24 in3 vss phi2 vdd phi2_bar net16 switch
xi23 net16 vss phi1 vdd phi1_bar agnd switch
xi22 net18 vss phi1 vdd phi1_bar in4 switch
xi21 avss vss phi2 vdd phi2_bar net18 switch
xi20 avss vss phi1 vdd phi1_bar net19 switch
xi19 net19 vss phi2 vdd phi2_bar out3 switch
xi18 net20 vss phi1 vdd phi1_bar in2 switch
xi17 avss vss phi2 vdd phi2_bar net20 switch
xi16 avss vss phi1 vdd phi1_bar net15 switch
xi15 net15 vss phi2 vdd phi2_bar out1 switch
xi14 out2 vss phi2 vdd phi2_bar net1 switch
xi13 net1 vss phi1 vdd phi1_bar agnd switch
xi12 in1 vss phi2 vdd phi2_bar net044 switch
xi11 in1 vss phi2 vdd phi2_bar net31 switch
xi10 net044 vss phi1 vdd phi1_bar agnd switch
xi9 net21 vss phi2 vdd phi2_bar agnd switch
xi8 net21 vss phi1 vdd phi1_bar vin switch
.ends ladder_filter


