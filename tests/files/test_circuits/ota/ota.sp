.subckt ota vbiasn vbiasp1 vinn vinp voutn voutp
* .param no_of_fin = 10
m4 id id 0 0 nmos_rvt w=270e-9 l=20e-9 nfin=5 nf=2
m3 net10 id 0 0 nmos_rvt w=270e-9 l=20e-9 nfin=5 nf=2
m10 voutn vbiasn net8 0 nmos_rvt w=270e-9 l=20e-9 nfin=12 nf=2
m2 voutp vbiasn net014 0 nmos_rvt w=270e-9 l=20e-9 nfin=12 nf=2
m6 voutp vbiasp net012 net012 pmos_rvt w=270e-9 l=20e-9 nfin=7 nf=2
m7 voutn vbiasp net06 net06 pmos_rvt w=270e-9 l=20e-9 nfin=7 nf=2
m8 net012 vbiasp1 vdd! vdd! pmos_rvt w=270e-9 l=20e-9 nfin=5 nf=2
m9 net06 vbiasp1 vdd! vdd! pmos_rvt w=270e-9 l=20e-9 nfin=5 nf=2
m0 net014 vinn net10 0 nmos_rvt w=270e-9 l=20e-9 nfin=12 nf=6
m1 net8 vinp net10 0 nmos_rvt w=270e-9 l=20e-9 nfin=12 nf=6
.ends ota
** End of subcircuit definition.
