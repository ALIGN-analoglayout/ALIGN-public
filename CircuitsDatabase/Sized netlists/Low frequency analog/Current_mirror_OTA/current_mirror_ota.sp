** Generated for: hspiceD
** Generated on: Nov 16 11:57:00 2018
** Design library name: DC_converter
** Design cell name: 
** Design view name: schematic
.GLOBAL vdd!



.AC DEC 100 1.0 1e11

.DC v1 600e-3 700e-3 100e-3

.TEMP 25.0

.OPTION INGOLD=2 ARTIST=2 PSF=2 MEASOUT=1 PARHIER=LOCAL PROBE=0 MARCH=2 ACCURACY=1 POST

i4 vdd! id DC=200e-6
c2 voutp 0 357e-15
m17 net16 vinn net24 0 nmos w=27e-9 l=20e-9 nfin=28
m16 net24 id 0 0 nmos w=27e-9 l=20e-9 nfin=10
m15 net27 vinp net24 0 nmos w=27e-9 l=20e-9 nfin=28
m14 id id 0 0 nmos w=27e-9 l=20e-9 nfin=10
m11 vbiasnd vbiasnd 0 0 nmos w=27e-9 l=20e-9 nfin=24
m10 voutp vbiasnd 0 0 nmos w=27e-9 l=20e-9 nfin=24
v3 vdd! 0 DC=0.8
v4 vinn 0 DC=0.7 AC 500e-3  
v5 vinp 0 DC=0.7 AC 500e-3 180
m21 net16 net16 vdd! vdd! pmos w=27e-9 l=20e-9 nfin=60
m20 m20stack net16 vdd! vdd! pmos w=27e-9 l=20e-9 nfin=240
m20s vbiasnd net16 m20stack vdd! pmos w=27e-9 l=20e-9 nfin=240
m19 net27 net27 vdd! vdd! pmos w=27e-9 l=20e-9 nfin=60
m18 m18stack net27 vdd! vdd! pmos w=27e-9 l=20e-9 nfin=240
m18s voutp net27 m18stack vdd! pmos w=27e-9 l=20e-9 nfin=240
.END
