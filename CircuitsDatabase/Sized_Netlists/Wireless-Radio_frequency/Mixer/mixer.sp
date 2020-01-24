** Generated for: hspiceD
** Generated on: Jan  5 21:03:07 2020
** Design library name: PhasedArray_WB_copy
** Design cell name: Mixer
** Design view name: schematic


.TEMP 25.0
.OPTION
+    ARTIST=2
+    INGOLD=2
+    PARHIER=LOCAL
+    PSF=2


** Library name: test_qmeng
** Cell name: MIXER_RFBIAS_RES
** View name: schematic
.subckt MIXER_RFBIAS_RES m p tail_bias
xr3  p net9   resistor l=6e-6 w=1e-6 m=1 mf=1 

xr0  net9 tail_bias   resistor l=6e-6 w=1e-6 m=1 mf=1 

xr1  tail_bias net05   resistor l=6e-6 w=1e-6 m=1 mf=1 

xr2  net05 m   resistor l=6e-6 w=1e-6 m=1 mf=1 

.ends MIXER_RFBIAS_RES
** End of subcircuit definition.

** Library name: test_qmeng
** Cell name: MIXER_LOSWBIAS_RES
** View name: schematic
.subckt MIXER_LOSWBIAS_RES mixer_lobias vdd vss
xr5  vdd net050   resistor l=4e-6 w=1e-6 m=1 mf=1 

xr4  net031 net034   resistor l=4e-6 w=1e-6 m=1 mf=1 

xr9  net049 net031   resistor l=4e-6 w=1e-6 m=1 mf=1 

xr6  net050 net051   resistor l=4e-6 w=1e-6 m=1 mf=1 

xr7  net051 mixer_lobias   resistor l=4e-6 w=1e-6 m=1 mf=1 

xr8  mixer_lobias net049   resistor l=4e-6 w=1e-6 m=1 mf=1 

xr0  net039 vss   resistor l=4e-6 w=1e-6 m=1 mf=1 

xr1  net033 net039   resistor l=4e-6 w=1e-6 m=1 mf=1 

xr3  net034 net036   resistor l=4e-6 w=1e-6 m=1 mf=1 

xr2  net036 net033   resistor l=4e-6 w=1e-6 m=1 mf=1 

.ends MIXER_LOSWBIAS_RES
** End of subcircuit definition.

** Library name: PhasedArray_WB_copy
** Cell name: MIXER_LOAD_RES_HBW
** View name: schematic
.subckt MIXER_LOAD_RES_HBW a b
xr4  b b   resistor l=13e-6 w=1e-6 m=1 mf=1 

xr0  a net06   resistor l=13e-6 w=1e-6 m=1 mf=1 

xr1  net06 net05   resistor l=13e-6 w=1e-6 m=1 mf=1 

xr3  net05 b   resistor l=13e-6 w=1e-6 m=1 mf=1 

.ends MIXER_LOAD_RES_HBW
** End of subcircuit definition.

** Library name: PhasedArray_WB_copy
** Cell name: Mixer
** View name: schematic
xm35 net051 tailm vss vss nmos lr=240e-9 wr=3.6e-6 nr=12 sigma=1 m=1 
xm34 net039 tailp vss vss nmos lr=240e-9 wr=3.6e-6 nr=12 sigma=1 m=1 
xm44<1> vss mixer_tail_iin vss vss nmos lr=240e-9 wr=3.6e-6 nr=2 sigma=1 m=1 
xm44<2> vss mixer_tail_iin vss vss nmos lr=240e-9 wr=3.6e-6 nr=2 sigma=1 m=1 
xm44<3> vss mixer_tail_iin vss vss nmos lr=240e-9 wr=3.6e-6 nr=2 sigma=1 m=1 
xm44<4> vss mixer_tail_iin vss vss nmos lr=240e-9 wr=3.6e-6 nr=2 sigma=1 m=1 
xm44<5> vss mixer_tail_iin vss vss nmos lr=240e-9 wr=3.6e-6 nr=2 sigma=1 m=1 
xm44<6> vss mixer_tail_iin vss vss nmos lr=240e-9 wr=3.6e-6 nr=2 sigma=1 m=1 
xm44<7> vss mixer_tail_iin vss vss nmos lr=240e-9 wr=3.6e-6 nr=2 sigma=1 m=1 
xm44<8> vss mixer_tail_iin vss vss nmos lr=240e-9 wr=3.6e-6 nr=2 sigma=1 m=1 
xm43 vss vss vss vss nmos lr=60e-9 wr=2e-6 nr=4 sigma=1 m=2 
xm38 mixer_tail_iin mixer_tail_iin vss vss nmos lr=240e-9 wr=3.6e-6 nr=2 sigma=1 m=1 
xm39 pbias mixer_tail_iin vss vss nmos lr=240e-9 wr=3.6e-6 nr=2 sigma=1 m=1 
xm7 ifm oscp net039 net039 nmos lr=60e-9 wr=2e-6 nr=4 sigma=1 m=1 
xm13 ifp oscp net051 net051 nmos lr=60e-9 wr=2e-6 nr=4 sigma=1 m=1 
xm12 ifm oscm net051 net051 nmos lr=60e-9 wr=2e-6 nr=4 sigma=1 m=1 
xm11 ifp oscm net039 net039 nmos lr=60e-9 wr=2e-6 nr=4 sigma=1 m=1 
xm29 vdd vdd vdd vdd pmos lr=240e-9 wr=2.05e-6 nr=8 sigma=1 m=2 
xm16 pbias pbias vdd vdd pmos lr=240e-9 wr=2.05e-6 nr=8 sigma=1 m=2 
xm24 ifp pbias vdd vdd pmos lr=240e-9 wr=2.05e-6 nr=24 sigma=1 m=2 
xm23 ifm pbias vdd vdd pmos lr=240e-9 wr=2.05e-6 nr=24 sigma=1 m=2 
xi29 tailm tailp mixer_tail_iin MIXER_RFBIAS_RES
xi12 oscp vdd vss MIXER_LOSWBIAS_RES
xi21 oscm vdd vss MIXER_LOSWBIAS_RES
xi33 ifp vdd MIXER_LOAD_RES_HBW
xi17 ifm vdd MIXER_LOAD_RES_HBW
xr1<1>  vss net040<0>   resistor l=13e-6 w=1e-6 m=1 mf=1 

xr1<2>  vss net040<1>   resistor l=13e-6 w=1e-6 m=1 mf=1 

xr1<3>  vss net040<2>   resistor l=13e-6 w=1e-6 m=1 mf=1 

xr1<4>  vss net040<3>   resistor l=13e-6 w=1e-6 m=1 mf=1 

xc15 lop oscp vss mimcap lt=32e-6 wt=16e-6 
xc7 rfp tailp vss mimcap lt=22e-6 wt=22e-6 
xc14 lom oscm vss mimcap lt=32e-6 wt=16e-6 
xr2  ifp outp   resistor l=6e-6 w=1e-6 m=1 mf=1 

xr5<1>  vss net043<0>   resistor l=6e-6 w=1e-6 m=1 mf=1 

xr5<2>  vss net043<1>   resistor l=6e-6 w=1e-6 m=1 mf=1 

xr5<3>  vss net043<2>   resistor l=6e-6 w=1e-6 m=1 mf=1 

xr5<4>  vss net043<3>   resistor l=6e-6 w=1e-6 m=1 mf=1 

xr0  outm ifm   resistor l=6e-6 w=1e-6 m=1 mf=1 

.END
