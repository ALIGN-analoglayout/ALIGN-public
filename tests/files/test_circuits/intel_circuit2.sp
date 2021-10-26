.SUBCKT stack3_p_cell  d g s b
.param m=1
Mi[0] d  g  n0 b p w=180e-9 m=1 nf=1
Mi[1] n0 g  n1 b p w=180e-9 m=1 nf=1
Mi[2] n1 g  s  b p w=180e-9 m=1 nf=1
.ENDS

.SUBCKT stack2_psvt_cell  d g s b
.param m=1
Mi[0] d  g  n0 b psvt w=180e-9 m=1 nf=1
Mi[1] n0 g  s  b psvt w=180e-9 m=1 nf=1
.ENDS

.SUBCKT stack3_psvt_cell  d g s b
.param m=1
Mi[0] d  g  n0 b psvt w=180e-9 m=1 nf=1
Mi[1] n0 g  n1 b psvt w=180e-9 m=1 nf=1
Mi[2] n1 g  s  b psvt w=180e-9 m=1 nf=1
.ENDS

.SUBCKT intel_circuit2 vcc

Xi0 d0 g0 s0 vcc stack3_p_cell m=4
Xi1 d1 g1 s1 vcc stack3_psvt_cell m=4
Xi2 d2 g2 s2 vcc stack2_psvt_cell m=4

Xi3 db da s vcc stack3_psvt_cell m=3
Xi4 da da s vcc stack3_psvt_cell m=3

Mn1 dn1 gn1 sn1 vcc plvt  w=270n  m=3  nf=4
Mn2 dn2 gn2 sn2 vcc p     w=270n  m=3  nf=4

Mn3 d3 g3 s vss nhvt  w=360e-9  m=5   nf=2
Mn4 d4 g4 s vss nhvt  w=360e-9  m=5   nf=2

.ENDS
