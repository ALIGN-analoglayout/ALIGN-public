.subckt phvt_s_pcell_0 d g s b
mi6 inet5 g s b phvt w=270n l=40n m=1
mi5 inet4 g inet5 b phvt w=270n l=40n m=1
mi4 inet3 g inet4 b phvt w=270n l=40n m=1
mi3 inet2 g inet3 b phvt w=270n l=40n m=1
mi2 inet1 g inet2 b phvt w=270n l=40n m=1
mi1 d g inet1 b phvt w=270n l=40n m=1
.ends

.subckt intel_circuit1
xmp6 vcm vcm net021 vcc phvt_s_pcell_0 m=4
.ends
