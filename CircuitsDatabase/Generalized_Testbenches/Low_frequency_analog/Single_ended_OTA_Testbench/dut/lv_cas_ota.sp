** Library name: MyProjects
** Cell name: LV_CAS_CM
.subckt DUT vp vn vout vdd vss ibias vb2
m3 net2 vb2 net12 vdd pch_lvt l=m3_l w='m3_w*1' m=1 nf=1 
m5 net12 net2 vdd vdd pch_lvt l=m5_l w='m5_w*1' m=1 nf=1 
m4 vout vb2 net4 vdd pch_lvt l=m4_l w='m4_w*1' m=1 nf=1 
m6 net4 net2 vdd vdd pch_lvt l=m6_l w='m6_w*1' m=1 nf=1 
m8 ibias ibias vss vss nch_lvt l=m8_l w='m8_w*1' m=1 nf=1 
m7 net5 ibias vss vss nch_lvt l=m7_l w='m7_w*1' m=1 nf=1 
m2 vout vp net5 net5 nch_lvt l=m2_l w='m2_w*1' m=1 nf=1 
m1 net2 vn net5 net5 nch_lvt l=m1_l w='m1_w*1' m=1 nf=1 
.ends DUT
