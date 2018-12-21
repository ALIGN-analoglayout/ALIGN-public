** Generated for: hspiceD
** Generated on: Nov 19 16:37:16 2018
** Design library name: DC_converter
** Design cell name: 2018_11_09_ASAP7_SCFilter
** Design view name: schematic
.GLOBAL vdd!

.AC DEC 100 1.0 1e11

.TRAN 1e-9 50e-6 START=1e-9

.OP

.PSS

.TEMP 25.0
.OPTION INGOLD=2 ARTIST=2 PSF=2 MEASOUT=1 PARHIER=LOCAL PROBE=0 MARCH=2 ACCURACY=1 POST
.INCLUDE "/project/analog-group04/Meghna/Design_Work/ASAP7nm/asap7PDK_r1p3/models/hspice/7nm_TT_160803.pm"

** Library name: DC_converter
** Cell name: 2018_11_09_ASAP7_current_mirror_ota
** View name: schematic
.subckt DC_converter_2018_11_09_ASAP7_current_mirror_ota_schematic vbiasnd vinn vinp voutn voutp id
m11 net1 net2 net3 0 nmos_rvt w=270e-9 l=20e-9 nfin=25
.ends DC_converter_2018_11_09_ASAP7_current_mirror_ota_schematic
** End of subcircuit definition.


** Library name: DC_converter
** Cell name: 2018_11_09_ASAP7_SCFilter
** View name: schematic
**i4 vdd! net17 DC=10e-6
**i10 vbiasp 0 DC=10e-6
**i9 vdd! vbiasn DC=10e-6
xi0 vg net08 net09 voutn voutp id DC_converter_2018_11_09_ASAP7_current_mirror_ota_schematic
m10 voutn vbiasn net8 0 nmos_rvt w=270e-9 l=20e-9 nfin=25
m2 voutp vbiasn net014 0 nmos_rvt w=270e-9 l=20e-9 nfin=25
m4 id id 0 0 nmos_rvt w=270e-9 l=20e-9 nfin=10
m3 net10 vbiasnd 0 0 nmos_rvt w=270e-9 l=20e-9 nfin=50
m0 net014 vinn net10 0 nmos_rvt w=270e-9 l=20e-9 nfin=75
m1 net8 vinp net10 0 nmos_rvt w=270e-9 l=20e-9 nfin=75
m6 voutp vbiasp net012 net012 pmos_rvt w=270e-9 l=20e-9 nfin=15
m7 voutn vbiasp net06 net06 pmos_rvt w=270e-9 l=20e-9 nfin=15
m8 net012 vbiasp1 vdd! vdd! pmos_rvt w=270e-9 l=20e-9 nfin=10
m9 net06 vbiasp1 vdd! vdd! pmos_rvt w=270e-9 l=20e-9 nfin=10
m17 vbiasn vbiasn net10 0 nmos_rvt w=270e-9 l=20e-9 nfin=5
m16 vbiasn vbiasp1 vdd! vdd! pmos_rvt w=270e-9 l=20e-9 nfin=10
**v4 vbiasp 0 DC=300e-3
m14 net8_bias net8_bias vdd! vdd! pmos_rvt w=270e-9 l=20e-9 nfin=20
m13 vbiasp vbiasp net8_bias net8_bias pmos_rvt w=270e-9 l=20e-9 nfin=20
m15 vbiasp id 0 0 nmos_rvt w=270e-9 l=20e-9 nfin=10
**v5 vbiasp1 0 DC=575e-3
m12 vbiasp1 id 0 0 nmos_rvt w=270e-9 l=20e-9 nfin=10
m11 vbiasp1 vbiasp1 vdd! vdd! pmos_rvt w=270e-9 l=20e-9 nfin=10
**v0 vdd! 0 DC=1000e-3
**i5 vdd! id DC=40e-6

.END
