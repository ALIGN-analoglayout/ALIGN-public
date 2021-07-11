.subckt phvt_s_pcell_0 d g s b
.param m=1
mi6 inet5 g s b phvt w=270n l=40n m=1
mi1 d g inet5 b phvt w=270n l=40n m=1
.ends

.subckt intel_circuit d g s
xmp6 d g s vcc phvt_s_pcell_0 m=4
.ends
