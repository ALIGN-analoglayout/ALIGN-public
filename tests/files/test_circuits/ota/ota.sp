.subckt ota vbiasn vbiasp1 vbiasp2 vinn vinp voutn voutp
.param no_of_fin = 10
m4 id id 0 0 nmos_rvt w=270e-9 l=20e-9 nfin=no_of_fin
m3 net10 id 0 0 nmos_rvt w=270e-9 l=20e-9 nfin=10
m10 voutn vbiasn net8 0 nmos_rvt w=270e-9 l=20e-9 nfin=25
m2 voutp vbiasn net014 0 nmos_rvt w=270e-9 l=20e-9 nfin=25
m6 voutp vbiasp net012 net012 pmos_rvt w=270e-9 l=20e-9 nfin=15
m7 voutn vbiasp net06 net06 pmos_rvt w=270e-9 l=20e-9 nfin=15
m8 net012 vbiasp1 vdd! vdd! pmos_rvt w=270e-9 l=20e-9 nfin=no_of_fin
m9 net06 vbiasp1 vdd! vdd! pmos_rvt w=270e-9 l=20e-9 nfin=no_of_fin
m0 net014 vinn net10 0 nmos_rvt w=270e-9 l=20e-9 nfin=75
m1 net8 vinp net10 0 nmos_rvt w=270e-9 l=20e-9 nfin=75
.ends ota
** End of subcircuit definition.
