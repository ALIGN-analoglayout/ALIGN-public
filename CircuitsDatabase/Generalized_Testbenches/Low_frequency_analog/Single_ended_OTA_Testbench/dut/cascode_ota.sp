** Library name: MyProjects
** Cell name: cascode_ota
.subckt DUT vp vn vout vdd vss ibias vb2
m7 net2 net2 vdd vdd pch_lvt l=m7_l w='m7_w*1' m=1 nf=1 
m5 net6 net6 net2 net2 pch_lvt l=m5_l w='m5_w*1' m=1 nf=1 
m6 vout net6 net4 net4 pch_lvt l=m6_l w='m6_w*1' m=1 nf=1 
m8 net4 net2 vdd vdd pch_lvt l=m8_l w='m8_w*1' m=1 nf=1 
m10 ibias ibias vss vss nch_lvt l=m10_l w='m10_w*1' m=1 nf=1 
m9 net10 ibias vss vss nch_lvt l=m9_l w='m9_w*1' m=1 nf=1 
m2 net1 vp net10 net10 nch_lvt l=m2_l w='m2_w*1' m=1 nf=1 
m1 net13 vn net10 net10 nch_lvt l=m1_l w='m1_w*1' m=1 nf=1 
m3 net6 vb2 net13 net13 nch_lvt l=m3_l w='m3_w*1' m=1 nf=1 
m4 vout vb2 net1 net1 nch_lvt l=m4_l w='m4_w*1' m=1 nf=1 
.ends DUT


