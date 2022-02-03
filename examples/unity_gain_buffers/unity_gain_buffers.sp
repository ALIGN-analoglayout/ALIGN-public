.subckt p_stack_4 d g s b
.param m=1
mi4 inet3 g s b p w=180n l=40n nfin=4 nf=2
mi3 inet2 g inet3 b p w=180n l=40n nfin=4 nf=2
mi2 inet1 g inet2 b p w=180n l=40n nfin=4 nf=2
mi1 d g inet1 b p w=180n l=40n nfin=4 nf=2
.ends

.subckt p_stack_2 d g s b
.param m=1
mi2 inet1 g s b p w=180n l=40n nfin=4 nf=2
mi1 d g inet1 b p w=180n l=40n nfin=4 nf=2
.ends

.subckt n_stack_4 d g s b
.param m=1
mi1 d g inet1 b n w=180n l=40n nfin=4 nf=2
mi2 inet1 g inet2 b n w=180n l=40n nfin=4 nf=2
mi3 inet2 g inet3 b n w=180n l=40n nfin=4 nf=2
mi4 inet3 g s b n w=180n l=40n nfin=4 nf=2
.ends

.subckt n_stack_2 d g s b
.param m=1
mi1 d g inet1 b n w=180n l=40n nfin=4 nf=2
mi2 inet1 g s b n w=180n l=40n nfin=4 nf=2
.ends

.subckt unity_gain_buffers vbias_an vcc vo_hs vo_ls vref_hs vref_ls vss
xmn1 v_p1 v_p2 vss vss n_stack_4 m=4
xmn0 v_p2 v_p2 vss vss n_stack_4 m=4
xmn43 vo_ls v_p1 vss vss n_stack_2 m=2
xmn22 v_n1 vo_hs vcom_n vss n_stack_2 m=10
xmn23 v_n2 vref_hs vcom_n vss n_stack_2 m=10
xmn41 vbias4 vbias_an vss vss n_stack_4 m=2
xmn3 vss vbias_an vss vss n_stack_4 m=2
xmn2 vcom_n vbias_an vss vss n_stack_4 m=4
mmn42 vbias_m vbias_m vbias4 vss n w=180n l=40n nfin=4 nf=2 m=16
mmp33 vbias_m vbias_m vbias_n1 vcc p w=180n l=40n nfin=4 nf=2 m=16
xmp10 vcom_p vbias_n1 vcc vcc p_stack_4 m=2
xmp8 v_p2 vo_ls vcom_p vcc p_stack_2 m=10
xmp22 v_n2 v_n1 vcc vcc p_stack_4 m=4
xmp28 v_n1 v_n1 vcc vcc p_stack_4 m=4
xmp7 vo_hs v_n2 vcc vcc p_stack_2 m=2
xmp34 vbias_n1 vbias_n1 vcc vcc p_stack_4 m=2
xmp9 v_p1 vref_ls vcom_p vcc p_stack_2 m=10
.ends

