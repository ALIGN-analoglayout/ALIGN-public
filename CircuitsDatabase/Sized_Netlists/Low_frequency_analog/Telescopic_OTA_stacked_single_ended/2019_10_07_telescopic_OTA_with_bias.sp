** Generated for: hspiceD
** Generated on: Jun 19 10:29:58 2019
** Design library name: ALIGN_circuitsnm
** Design cell name: switched_capacitor_filter_spice
** Design view name: schematic


.TEMP 25.0
.OPTION INGOLD=2 ARTIST=2 PSF=2 MEASOUT=1 PARHIER=LOCAL PROBE=0 MARCH=2 ACCURACY=1 POST

** Library name: ALIGN_circuitsnm
** Cell name: telescopic_ota
** View name: schematic
.subckt telescopic_ota d1 vdd vinn vinp vss vout
m9 vpgate vbiasn net8s vss nmos w=270e-9 l=20e-9 nfin=70
m9s net8s vbiasn net8 vss nmos w=270e-9 l=20e-9 nfin=70
m8 vout vbiasn net014s vss nmos w=270e-9 l=20e-9 nfin=70
m8s net014s vbiasn net014 vss nmos w=270e-9 l=20e-9 nfin=70
m5 D1 D1 netm5s vss nmos w=270e-9 l=20e-9 nfin=20
m5s netm5s D1 vss vss nmos w=270e-9 l=20e-9 nfin=20
m4 net10 D1 netm4s vss nmos w=270e-9 l=20e-9 nfin=100
m4s netm4s D1 vss vss nmos w=270e-9 l=20e-9 nfin=100
m3 net014 vinn netm3s vss nmos w=270e-9 l=20e-9 nfin=140
m3s netm3s vinn net10 vss nmos w=270e-9 l=20e-9 nfin=140
m0 net8 vinp netm0s vss nmos w=270e-9 l=20e-9 nfin=140
m0s netm0s vinp net10 vss nmos w=270e-9 l=20e-9 nfin=140
m7 vout vbiasp net012s vdd pmos w=270e-9 l=20e-9 nfin=110
m7s net012s vbiasp net012 vdd pmos w=270e-9 l=20e-9 nfin=110
m6 vpgate vbiasp net06s vdd pmos w=270e-9 l=20e-9 nfin=110
m6s net06s vbiasp net06 vdd pmos w=270e-9 l=20e-9 nfin=110
m2 net012 vpgate netm2s vdd pmos w=270e-9 l=20e-9 nfin=45
m2s netm2s vpgate vdd vdd pmos w=270e-9 l=20e-9 nfin=45
m1 net06 vpgate netm1s vdd pmos w=270e-9 l=20e-9 nfin=45
m1s netm1s vpgate vdd vdd pmos w=270e-9 l=20e-9 nfin=45
m10 vbiasn vbiasn net5s vss nmos w=270e-9 l=20e-9 nfin=5
m10s net5s vbiasn net5 vss nmos w=270e-9 l=20e-9 nfin=5
m11 net5 vbiasn netm11s vss nmos w=270e-9 l=20e-9 nfin=10
m11s netm11s vbiasn net10 vss nmos w=270e-9 l=20e-9 nfin=10
m15 net9 d1 netm15s vss nmos w=270e-9 l=20e-9 nfin=10
m15s netm15s d1 vss vss nmos w=270e-9 l=20e-9 nfin=10
m16 net9 net9 netm16s vdd pmos w=270e-9 l=20e-9 nfin=10
m16s netm16s net9 vdd vdd pmos w=270e-9 l=20e-9 nfin=10
m17 vbiasn net9 netm17s vdd pmos w=270e-9 l=20e-9 nfin=10
m17s netm17s net9 vdd vdd pmos w=270e-9 l=20e-9 nfin=10
m12 vbiasp d1 netm12s vss nmos w=270e-9 l=20e-9 nfin=10
m12s netm12s d1 vss vss nmos w=270e-9 l=20e-9 nfin=10
m13 vbiasp vbiasp netm13s vdd pmos w=270e-9 l=20e-9 nfin=5
m13s netm13s vbiasp net7 vdd pmos w=270e-9 l=20e-9 nfin=5
m14 net7 vbiasp netm14s vdd pmos w=270e-9 l=20e-9 nfin=10
m14s netm14s vbiasp vdd vdd pmos w=270e-9 l=20e-9 nfin=10
.ends telescopic_ota
** End of subcircuit definition.

i5 vdd d1 DC=40e-6
xi15 d1 vdd vinn vinp vss vout telescopic_ota
v2 vinn 0 DC=550e-3 AC 500e-3 180
v1 vinp 0 DC=550e-3 AC 500e-3
v8 vss 0 DC=0
v9 vdd 0 DC=1
c1 vout vss 350e-15
.OP

.AC DEC 100 1.0 1e11

.meas ac GAIN find vdb(vout) at = 1       			$ Measure Open-loop Gain    (Gain) 	(dB)
.meas ac UGF when vdb(vout)=0
.meas ac threeDB_gain find vdb(vout) at = 3.16e6
.meas ac threeDB when par('vdb(vout)+3')=gain				$ Measure Unity-gain Frequency 	(UGF) 	(Hz)
.meas ac PM find par('180+vp(vout)') when vdb(vout)=0		        $ Measure Phase margin	(PM) 	(deg)

.END
