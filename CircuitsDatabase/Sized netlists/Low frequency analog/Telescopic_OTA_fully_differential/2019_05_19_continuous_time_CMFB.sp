** Generated for: hspiceD
** Generated on: May 19 14:10:16 2019
** Design library name: ALIGN_circuitsnm
** Design cell name: continuous_time_CMFB
** Design view name: schematic


.GLOBAL vdd!

.AC DEC 100 1.0 1e11

**.TRAN 1e-9 50e-6 START=1e-9

.OP

.DC vcm 550e-3 560e-3 0.5

.TEMP 25.0
.OPTION INGOLD=2 ARTIST=2 PSF=2 MEASOUT=1 PARHIER=LOCAL PROBE=0 MARCH=2 ACCURACY=1 POST

.subckt telescopic_ota vbiasnd vbiasn vbiasp2 vbiasp1 vinn vinp voutn voutp D1

m9 voutn vbiasn net8 0 nmos w=270e-9 l=20e-9 nfin=25
m8 voutp vbiasn net014 0 nmos w=270e-9 l=20e-9 nfin=25
m5 D1 D1 0 0 nmos w=270e-9 l=20e-9 nfin=10
m4 net10 vbiasnd 0 0 nmos w=270e-9 l=20e-9 nfin=50
m3 net014 vinn net10 0 nmos w=270e-9 l=20e-9 nfin=70
m0 net8 vinp net10 0 nmos w=270e-9 l=20e-9 nfin=70
m7 voutp vbiasp2 net012 net012 pmos w=270e-9 l=20e-9 nfin=15
m6 voutn vbiasp2 net06 net06 pmos w=270e-9 l=20e-9 nfin=15
m2 net012 vbiasp1 vdd! vdd! pmos w=270e-9 l=20e-9 nfin=10
m1 net06 vbiasp1 vdd! vdd! pmos w=270e-9 l=20e-9 nfin=10

.ends


** Library name: ALIGN_circuitsnm
** Cell name: continuous_time_CMFB
** View name: schematic
.subckt continuous_time_CMFB va vb vcm vg vgout vss
r1 net11 net9 10e3
r0 net9 net12 10e3
e2 vgout vg VCVS net9 vcm 1
e1 net11 vss VCVS vb vss 1
e0 net12 vss VCVS va vss 1
.ends


i5 vdd! id DC=40e-6
**xi0 vg vbiasn net08 net09 vbiasp1 vbiasp2 id vss vdd voutn voutp telescopic_ota_DR
**xi3 clk vdd! 0 phi1 phi2 DC_converter_2018_11_09_non_overlapping_clock_generator_schematic
**v0 clk 0 PULSE 0 1 0 0 0 115e-9 250e-9
xi15 vbiasnd vbiasn vbiasp2 vbiasp1 vinn vinp voutn voutp id telescopic_ota
v11 vdd! 0 DC=1
v6 vcm 0 DC=550e-3
**v5 vbias_cm 0 DC=375e-3
**v2 net09 0 SIN 550e-3 1e-4 50e+3 0 0 0
**v1 net08 0 SIN 550e-3 1e-4 50e+3 0 0 180
v2 vinn 0 DC=550e-3 AC 500e-3 180
v1 vinp 0 DC=550e-3 AC 500e-3
v3 vbiasn 0 DC=700e-3
v4 vbiasp2 0 DC=300e-3
v7 vbiasp1 0 DC=490e-3
v8 vss 0 DC=0
v9 vdd 0 DC=1
c1 voutn vss 350e-15
c2 voutp vss 350e-15
**xi13 voutn voutp id vcm vg phi1 phi2 DC_converter_2018_11_09_cmfb_schematic
xi14 voutn voutp vcm id vbiasnd vss continuous_time_CMFB
.probe vdiff1=par('v(voutn)-v(voutp)')
.probe vdiff=par('v(vinn)-v(vinp)')
.END
