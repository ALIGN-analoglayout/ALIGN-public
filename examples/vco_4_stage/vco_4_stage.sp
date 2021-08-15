
.subckt inv_unit_latch1 gnd in out top vdd
    M0 out in gnd gnd nmos_slvt m=1 l=14n nfin=8 nf=6
    M1 out in top vdd pmos_slvt m=1 l=14n nfin=10 nf=6
.ends inv_unit_latch

.subckt inv_unit1 gnd in out top vdd
    M0 out in gnd gnd nmos_slvt m=1 l=14n nfin=4 nf=6
    M1 out in top vdd pmos_slvt m=1 l=14n nfin=5 nf=6
.ends inv_unit

.subckt vco_unit gnd inn inp outn outnp outp outpn top vdd
    I3 gnd outp outpn top vdd inv_unit_latch1
    I2 gnd outn outnp top vdd inv_unit_latch1
    I1 gnd inn outp top vdd inv_unit1
    I0 gnd inp outn top vdd inv_unit1
.ends vco_unit

.subckt vco_4_stage gnd phin\<3\> phin\<2\> phin\<1\> phin\<0\> phip\<3\> phip\<2\> phip\<1\> phip\<0\> vctrl vdd
    M1 top vctrl vdd vdd lvtpfet m=1 l=14n nfin=10 nf=8 stack=8
    I3 gnd phip\<2\> phin\<2\> phip\<3\> phin\<3\> phin\<3\> phip\<3\> top vdd vco_unit
    I2 gnd phin\<1\> phip\<1\> phin\<2\> phip\<2\> phip\<2\> phin\<2\> top vdd vco_unit
    I1 gnd phip\<0\> phin\<0\> phip\<1\> phin\<1\> phin\<1\> phip\<1\> top vdd vco_unit
    I0 gnd phip\<3\> phin\<3\> phin\<0\> phip\<0\> phip\<0\> phin\<0\> top vdd vco_unit
.ends vco_4_stage
