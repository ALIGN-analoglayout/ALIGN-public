
.subckt phvt_cell_4 d g s b
mi4 inet3 g s b phvt w=180n l=40n m=1
mi3 inet2 g inet3 b phvt w=180n l=40n m=1
mi2 inet1 g inet2 b phvt w=180n l=40n m=1
mi1 d g inet1 b phvt w=180n l=40n m=1
.ends

.subckt phvt_cell_3 d g s b
mi4 inet3 g s b phvt w=180n l=40n m=1
mi3 inet2 g inet3 b phvt w=180n l=40n m=1
mi2 inet1 g inet2 b phvt w=180n l=40n m=1
mi1 d g inet1 b phvt w=180n l=40n m=1
.ends

.subckt n_cell_3 d g s b
mi1 d g inet1 b nhvt w=270n l=40n m=1
mi2 inet1 g inet2 b nhvt w=270n l=40n m=1
mi3 inet2 g inet3 b nhvt w=270n l=40n m=1
mi4 inet3 g inet4 b nhvt w=270n l=40n m=1
mi5 inet4 g inet5 b nhvt w=270n l=40n m=1
mi6 inet5 g s b nhvt w=270n l=40n m=1
.ends

.subckt n_cell_2 d g s b
mi1 d g inet1 b n w=270n l=40n m=1
mi2 inet1 g inet2 b n w=270n l=40n m=1
mi3 inet2 g inet3 b n w=270n l=40n m=1
mi4 inet3 g inet4 b n w=270n l=40n m=1
mi5 inet4 g inet5 b n w=270n l=40n m=1
mi6 inet5 g s b n w=270n l=40n m=1
.ends

.subckt n_cell_1 d g s b
mi1 d g inet1 b n w=270n l=40n m=1
mi2 inet1 g inet2 b n w=270n l=40n m=1
mi3 inet2 g inet3 b n w=270n l=40n m=1
mi4 inet3 g inet4 b n w=270n l=40n m=1
mi5 inet4 g inet5 b n w=270n l=40n m=1
mi6 inet5 g s b n w=270n l=40n m=1
.ends

.subckt plvt_cell_0 d g s b
mi6 inet5 g s b plvt w=270n l=40n m=1
mi5 inet4 g inet5 b plvt w=270n l=40n m=1
mi4 inet3 g inet4 b plvt w=270n l=40n m=1
mi3 inet2 g inet3 b plvt w=270n l=40n m=1
mi2 inet1 g inet2 b plvt w=270n l=40n m=1
mi1 d g inet1 b plvt w=270n l=40n m=1
.ends

.subckt intel_circuit4 iref vcca vcm vinn vinp voun voup vssa
xmp3 vcm vcm net021 vcca plvt_cell_0 m=4
xmp0 voun vinp net36 vcca plvt_cell_0 m=4
xmp1 voup vinn net36 vcca plvt_cell_0 m=4
xmn3 vcm vcm vssa vssa n_cell_1 m=4
xmn0 voun vinp vssa vssa n_cell_2 m=4
xmn1 voup vinn vssa vssa n_cell_3 m=4
xmp13 net021 iref vcca vcca phvt_cell_3 m=16
xmp12 net36 iref vcca vcca phvt_cell_4 m=32
xmp11 iref iref vcca vcca phvt_cell_3 m=16
.ends


