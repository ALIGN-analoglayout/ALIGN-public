** Generated for: hspiceD
** Generated on: Nov 16 15:51:50 2018
** Design library name: DC_converter
** Design cell name: 
** Design view name: schematic
.GLOBAL vdd!

.OP

.AC DEC 100 1.0 1e11

.DC v1 600e-3 700e-3 100e-3

.TEMP 25.0

.OPTION INGOLD=2 ARTIST=2 PSF=2 MEASOUT=1 PARHIER=LOCAL PROBE=0 MARCH=2 ACCURACY=1 POST

** Library name: DC_converter
** Cell name: 2018_11_09_current_mirror_ota
** View name: schematic
i4 vdd! net17 DC=200e-6
c2 voutp 0 357e-15
m25 voutp vbiasn net034 0 nmos w=27e-9 l=20e-9 nfin=24
m24 vbiasnd vbiasn net033 0 nmos w=27e-9 l=20e-9 nfin=24
m17 net16 vinn net24 0 nmos w=27e-9 l=20e-9 nfin=30
m16 net24 net17 0 0 nmos w=27e-9 l=20e-9 nfin=15
m15 net27 vinp net24 0 nmos w=27e-9 l=20e-9 nfin=30
m14 net17 net17 0 0 nmos w=27e-9 l=20e-9 nfin=15
m11 net033 vbiasnd 0 0 nmos w=27e-9 l=20e-9 nfin=30
m10 net034 vbiasnd 0 0 nmos w=27e-9 l=20e-9 nfin=30
**v1 vbiasp 0 DC=300e-3
v0 vdd! 0 DC=1000e-3
**v2 vbiasn 0 DC=700e-3

i1 vdd! vbiasn DC=10e-6
m1nup vbiasn vbiasn net9b 0 nmos w=270e-9 l=20e-9 nfin=3
m1ndown net9b net9b 0 0 nmos w=270e-9 l=20e-9 nfin=5

i2 vbiasp 0 DC=10e-6
m1pup net8b net8b vdd! vdd! pmos w=270e-9 l=20e-9 nfin=5
m1pdown vbiasp vbiasp net8b net8b pmos w=270e-9 l=20e-9 nfin=5


v3 vinn 0 DC=0.55 AC 500e-3 180
v4 vinp 0 DC=0.55 AC 500e-3 
m27 net27 vbiasp net021 net021 pmos w=27e-9 l=20e-9 nfin=60
m26 net16 vbiasp net015 net015 pmos w=27e-9 l=20e-9 nfin=60
m23 voutp vbiasp net024 net024 pmos w=27e-9 l=20e-9 nfin=120
m22 vbiasnd vbiasp net06 net06 pmos w=27e-9 l=20e-9 nfin=120
m21 net015 net16 vdd! vdd! pmos w=27e-9 l=20e-9 nfin=5
m20 net06 net16 vdd! vdd! pmos w=27e-9 l=20e-9 nfin=10
m19 net021 net27 vdd! vdd! pmos w=27e-9 l=20e-9 nfin=5
m18 net024 net27 vdd! vdd! pmos w=27e-9 l=20e-9 nfin=10
.END
