.SUBCKT stack_of_three d g s b
Mi[0] d g  n0 b psvt w=180e-9 m=1 nf=1
Mi[1] n0 g  n1 b psvt w=180e-9 m=1 nf=1
Mi[2] n1 g  s   b  psvt w=180e-9 m=1 nf=1
.ENDS

.subckt intel_circuit3 dk g s b da a db d1 g1 d2 g1 g2
Xi0 dk g s b stack_of_three m=4
Xi1 da da s b stack_of_three m=1
Xi2 da db s b stack_of_three m=3
Mn1 a b c gnd plvt  w=270n  m=3   nf=4
Mn2 d1 g1 s gnd nhvt  w=360e-9  m=5   nf=2
Mn3 d2 g2 s gnd nhvt  w=360e-9  m=5   nf=2
.ENDS

