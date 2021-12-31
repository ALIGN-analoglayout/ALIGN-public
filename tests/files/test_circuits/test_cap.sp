.subckt test_cap in out1 out2 vss
m0 d g s vss nmos_rvt w=270e-9 l=20e-9 nfin=12 nf=2
c2 d out1 30e-15
c1 s out2 30e-15
c0 in g 60e-15
.ends test_cap
