** Generated for: hspiceD
** Generated on: Jun 19 10:29:58 2019
** Design library name: ALIGN_circuits
** Design cell name: switched_capacitor_filter_spice
** Design view name: schematic


.TEMP 25.0
.OPTION INGOLD=2 ARTIST=2 PSF=2 MEASOUT=1 PARHIER=LOCAL PROBE=0 MARCH=2 ACCURACY=1 POST

** Library name: ALIGN_circuits
** Cell name: telescopic_ota
** View name: schematic
.subckt telescopic_ota d1 vdd vinn vinp vss vout
m9 vpgate vbiasn net8 vss nmos w=270e-9 l=20e-9 nfin=35
m8 vout vbiasn net014 vss nmos w=270e-9 l=20e-9 nfin=35
m5 D1 D1 vss vss nmos w=270e-9 l=20e-9 nfin=5
m4 net10 D1 vss vss nmos w=270e-9 l=20e-9 nfin=25
m3 net014 vinn net10 vss nmos w=270e-9 l=20e-9 nfin=70
m0 net8 vinp net10 vss nmos w=270e-9 l=20e-9 nfin=70
m7 vout vbiasp net012 vdd pmos w=270e-9 l=20e-9 nfin=55
m6 vpgate vbiasp net06 vdd pmos w=270e-9 l=20e-9 nfin=55
m2 net012 vpgate vdd vdd pmos w=270e-9 l=20e-9 nfin=20
m1 net06 vpgate vdd vdd pmos w=270e-9 l=20e-9 nfin=20
m10 vbiasn vbiasn net5 vss nmos w=270e-9 l=20e-9 nfin=4
m11 net5 vbiasn net10 vss nmos w=270e-9 l=20e-9 nfin=5
m15 net9 d1 vss vss nmos w=270e-9 l=20e-9 nfin=5
m16 net9 net9 vdd vdd pmos w=270e-9 l=20e-9 nfin=5
m17 vbiasn net9 vdd vdd pmos w=270e-9 l=20e-9 nfin=5
m12 vbiasp d1 vss vss nmos w=270e-9 l=20e-9 nfin=5
m13 vbiasp vbiasp net7 vdd pmos w=270e-9 l=20e-9 nfin=4
m14 net7 vbiasp vdd vdd pmos w=270e-9 l=20e-9 nfin=5
.ends telescopic_ota
** End of subcircuit definition.

i5 vdd d1 DC=20e-6
xi15 d1 vdd vinn vinp vss vout telescopic_ota
v2 vinn 0 DC=550e-3 AC 500e-3 180
v1 vinp 0 DC=550e-3 AC 500e-3
v8 vss 0 DC=0
v9 vdd 0 DC=1
c1 vout vss 175e-15
.OP
.DC vdd! 1000e-3 1100e-3 200e-3
.AC DEC 100 1.0 1e11
.meas dc current avg i(v9)
.meas ac GAIN find vdb(vout) at = 1       			
.meas ac UGF when vdb(vout)=0
.meas ac threeDB when par('vdb(vout)+3')=gain			
.meas ac PM find par('180+vp(vout)') when vdb(vout)=0		        
.END
