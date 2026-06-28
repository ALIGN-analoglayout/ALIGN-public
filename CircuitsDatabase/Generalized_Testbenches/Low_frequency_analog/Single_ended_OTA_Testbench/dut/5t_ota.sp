** Library name: MyProjects
** Cell name: 5T_OTA
.subckt DUT vp vn vout vdd vss ibias
m5 ibias ibias vss vss nch_lvt l=m5_l w='m5_w*1' m=1 nf=1 
m4 net2 ibias vss vss nch_lvt l=m4_l w='m4_w*1' m=1 nf=1 
m2 vout vn net2 net2 nch_lvt l=m2_l w='m2_w*1' m=1 nf=1 
m0 net3 vp net2 net2 nch_lvt l=m0_l w='m0_w*1' m=1 nf=1 
m3 vout net3 vdd vdd pch_lvt l=m3_l w='m3_w*1' m=1 nf=1 
m1 net3 net3 vdd vdd pch_lvt l=m1_l w='m1_w*1' m=1 nf=1 
.ends DUT
