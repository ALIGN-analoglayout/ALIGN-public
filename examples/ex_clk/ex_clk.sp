.subckt ex_clk v1 v2 v3 v4 vb vss vdd tail0 tail1 tail2 tail3 tail4
mn0 clk vb tail0  vss n w=270e-9 l=20e-9 nfin=4 nf=2 m=16
mn1 v1 clk tail1 vss n w=270e-9 l=20e-9 nfin=4 nf=2 m=16
mn2 v2 clk tail2 vss n w=270e-9 l=20e-9 nfin=4 nf=2 m=16
mn3 v3 clk tail3 vss n w=270e-9 l=20e-9 nfin=4 nf=2 m=16
mn4 v4 clk tail4 vss n w=270e-9 l=20e-9 nfin=4 nf=2 m=16
.ends ex_clk
