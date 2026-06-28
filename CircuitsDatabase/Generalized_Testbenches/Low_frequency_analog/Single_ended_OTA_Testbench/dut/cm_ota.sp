** Library name: MyProjects
** Cell name: CM_OTA
.subckt DUT vp vn vout vdd vss ibias
m10 net2 net2 vss vss nch_lvt l=m10_l w='m10_w*1' m=1 nf=1 
m6 vout net2 vss vss nch_lvt l=m6_l w='m6_w*1' m=1 nf=1 
m3 ibias ibias vss vss nch_lvt l=m3_l w='m3_w*1' m=1 nf=1 
m2 net4 ibias vss vss nch_lvt l=m2_l w='m2_w*1' m=1 nf=1 
m1 net3 vp net4 net4 nch_lvt l=m1_l w='m1_w*1' m=1 nf=1 
m0 net1 vn net4 net4 nch_lvt l=m0_l w='m0_w*1' m=1 nf=1 
m8 net3 net3 vdd vdd pch_lvt l=m8_l w='m8_w*1' m=1 nf=1 
m7 vout net3 vdd vdd pch_lvt l=m7_l w='m7_w*1' m=1 nf=1 
m5 net2 net1 vdd vdd pch_lvt l=m5_l w='m5_w*1' m=1 nf=1 
m4 net1 net1 vdd vdd pch_lvt l=m4_l w='m4_w*1' m=1 nf=1 
.ends DUT


