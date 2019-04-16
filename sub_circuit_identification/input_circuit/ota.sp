.subckt DC_converter_2018_11_09_ASAP7_current_mirror_ota_schematic vbiasnd vinn vinp voutn voutp id
m11 net1 net2 net3 0 nmos_rvt w=270e-9 l=20e-9 nfin=25
.ends DC_converter_2018_11_09_ASAP7_current_mirror_ota_schematic

.subckt cascode_current_mirror_ota vbiasn vbiasp1 vbiasp2 vinn vinp voutn voutp
xi0 vg net08 net09 voutn voutp id DC_converter_2018_11_09_ASAP7_current_mirror_ota_schematic
m4 id id 0 0 nmos_rvt w=270e-9 l=20e-9 nfin=10
m3 net10 id 0 0 nmos_rvt w=270e-9 l=20e-9 nfin=50
m10 voutn vbiasn net8 0 nmos_rvt w=270e-9 l=20e-9 nfin=25
m2 voutp vbiasn net014 0 nmos_rvt w=270e-9 l=20e-9 nfin=25
m6 voutp vbiasp net012 net012 pmos_rvt w=270e-9 l=20e-9 nfin=15
m7 voutn vbiasp net06 net06 pmos_rvt w=270e-9 l=20e-9 nfin=15
m8 net012 vbiasp1 vdd! vdd! pmos_rvt w=270e-9 l=20e-9 nfin=10
m9 net06 vbiasp1 vdd! vdd! pmos_rvt w=270e-9 l=20e-9 nfin=10
m0 net014 vinn net10 0 nmos_rvt w=270e-9 l=20e-9 nfin=75
m1 net8 vinp net10 0 nmos_rvt w=270e-9 l=20e-9 nfin=75
.ends cascode_current_mirror_ota
** End of subcircuit definition.
