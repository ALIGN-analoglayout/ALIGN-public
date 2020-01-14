
.subckt telescopic_ota_12nm vdd vss vinn vinp vout ibiasn inh_hsup inh_lsup
xn10 net020 ibiasn vss inh_lsup nmos m=1 l=14e-9 nfin=6 nf=2 par=1 
xn9 vbiasn vbiasn net018 inh_lsup nmos m=1 l=14e-9 nfin=25 nf=2 par=1
xn8 net018 vbiasn vss inh_lsup nmos m=1 l=14e-9 nfin=2 nf=1 par=1 
xn6 vbiasp ibiasn vss inh_lsup nmos m=1 l=14e-9 nfin=12 nf=2 par=1 
xn5 vout vbiasn net19 inh_lsup nmos m=1 l=14e-9 nfin=25 nf=2 par=1 
xn4 net030 vbiasn net20 inh_lsup nmos m=1 l=14e-9 nfin=25 nf=2 par=1 
xn3 ibiasn ibiasn vss inh_lsup nmos m=1 l=14e-9 nfin=5 nf=2 par=1 
xn2 net025 ibiasn vss inh_lsup nmos m=1 l=14e-9 nfin=40 nf=2 par=1 
xn1 net19 vinn net025 inh_lsup nmos m=1 l=14e-9 nfin=40 nf=2 par=1 
xn0 net20 vinp net025 inh_lsup nmos m=1 l=14e-9 nfin=40 nf=2 par=1 
xp9 net020 net020 vdd inh_hsup pmos m=1 l=14e-9 nfin=8 nf=2 par=1 
xp7 net010 net020 vdd inh_hsup pmos m=1 l=14e-9 nfin=15 nf=2 par=1 
xp8 vbiasn vbiasp net010 inh_hsup pmos m=1 l=14e-9 nfin=10 nf=2 par=1 
xp5 net015 vbiasp vdd inh_hsup pmos m=1 l=14e-9 nfin=2 nf=2 par=1 
xp4 vbiasp vbiasp net015 inh_hsup pmos m=1 l=14e-9 nfin=5 nf=2 par=1 
xp3 net18 net030 vdd inh_hsup pmos m=1 l=14e-9 nfin=15 nf=2 par=1 
xp2 net21 net030 vdd inh_hsup pmos m=1 l=14e-9 nfin=15 nf=2 par=1 
xp1 vout vbiasp net18 inh_hsup pmos m=1 l=14e-9 nfin=10 nf=2 par=1 
xp0 net030 vbiasp net21 inh_hsup pmos m=1 l=14e-9 nfin=10 nf=2 par=1
.ends telescopic_ota_12nm
** End of subcircuit definition.

