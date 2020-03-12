** Generated for: hspiceD
** Generated on: Nov 19 16:37:16 2018
** Design library name: DC_converter
** Design cell name: 2018_11_09_SCFilter
** Design view name: schematic
.GLOBAL vdd!

.AC DEC 100 1.0 1e11

.TRAN 1e-9 50e-6 START=1e-9

.OP

.TEMP 25.0
.OPTION INGOLD=2 ARTIST=2 PSF=2 MEASOUT=1 PARHIER=LOCAL PROBE=0 MARCH=2 ACCURACY=1 POST

** Library name: DC_converter
** Cell name: 2018_11_09_telescopic_ota
** View name: schematic
.subckt telescopic_ota D1 vdd vinn vinp vss vbiasn vbiasnd vbiasp1 vbiasp2 voutn voutp
m9 voutn vbiasn net8 vss nmos w=270e-9 l=20e-9 nfin=25
m8 voutp vbiasn net014 vss nmos w=270e-9 l=20e-9 nfin=25
m5 D1 D1 vss vss nmos w=270e-9 l=20e-9 nfin=10
m4 net10 vbiasnd vss vss nmos w=270e-9 l=20e-9 nfin=50
m3 net014 vinn net10 vss nmos w=270e-9 l=20e-9 nfin=70
m0 net8 vinp net10 vss nmos w=270e-9 l=20e-9 nfin=70
m7 voutp vbiasp2 net012 net012 pmos w=270e-9 l=20e-9 nfin=15
m6 voutn vbiasp2 net06 net06 pmos w=270e-9 l=20e-9 nfin=15
m2 net012 vbiasp1 vdd vdd pmos w=270e-9 l=20e-9 nfin=10
m1 net06 vbiasp1 vdd vdd pmos w=270e-9 l=20e-9 nfin=10
.ends telescopic_ota
** End of subcircuit definition.


** Library name: asap7ssc7p5t
** Cell name: INVx1_75t_R
** View name: schematic
.subckt INVx1_75t_R a y vdd vss
m0 y a vss vss nmos w=81e-9 l=20e-9 nfin=3
m1 y a vdd vdd pmos w=81e-9 l=20e-9 nfin=3
.ends INVx1_75t_R
** End of subcircuit definition.

** Library name: asap7ssc7p5t
** Cell name: INVx1_75t_R_21
** View name: schematic
.subckt INVx1_75t_R_21 a y vdd vss
m0 y a vss vss nmos w=81e-9 l=20e-9 nfin=21
m1 y a vdd vdd pmos w=81e-9 l=20e-9 nfin=21
.ends INVx1_75t_R_21
** End of subcircuit definition.

** Library name: DC_converter
** Cell name: 2018_12_03_transmission_gate
** View name: schematic
.subckt DC_converter_2018_12_03_transmission_gate a y vdd vss
m0 y vdd a 0 nmos w=81e-9 l=20e-9 nfin=3
m1 y vss a a pmos w=81e-9 l=20e-9 nfin=3
.ends DC_converter_2018_12_03_transmission_gate
** End of subcircuit definition.

** Library name: DC_converter
** Cell name: 2018_11_09_NAND_gate
** View name: schematic
.subckt DC_converter_2018_11_09_NAND_gate_schematic a b out vdd vss
m2 out a net22 vss nmos w=54e-9 l=20e-9 nfin=2
m3 net22 b vss vss nmos w=54e-9 l=20e-9 nfin=2
m0 out a vdd vdd pmos w=27e-9 l=20e-9 nfin=1
m1 out b vdd vdd pmos w=27e-9 l=20e-9 nfin=1
.ends DC_converter_2018_11_09_NAND_gate_schematic
** End of subcircuit definition.

** Library name: DC_converter
** Cell name: 2018_11_09_non_overlapping_clock_generator
** View name: schematic
.subckt DC_converter_2018_11_09_non_overlapping_clock_generator_schematic clk d_vdd d_gnd phi1 phi2
xi6 clk net9 d_vdd d_gnd INVx1_75t_R
xi6_tg clk net9_tg d_dd d_gnd DC_converter_2018_12_03_transmission_gate
xi5 net12 phi2 d_vdd d_gnd INVx1_75t_R_21
xi4 net17 net12 d_vdd d_gnd INVx1_75t_R
xi3 net8 phi1 d_vdd d_gnd INVx1_75t_R_21
xi2 net15 net8 d_vdd d_gnd INVx1_75t_R
xi1 net16 net15 d_vdd d_gnd INVx1_75t_R
xi0 net18 net17 d_vdd d_gnd INVx1_75t_R
xi8 net9 net8 net18 d_vdd d_gnd DC_converter_2018_11_09_NAND_gate_schematic
xi7 net12 net9_tg net16 d_vdd d_gnd DC_converter_2018_11_09_NAND_gate_schematic
.ends DC_converter_2018_11_09_non_overlapping_clock_generator_schematic
** End of subcircuit definition.


** Library name: DC_converter
** Cell name: 2018_11_09_cmfb
** View name: schematic
.subckt DC_converter_2018_11_09_cmfb_schematic va vb vbias vcm vg phi1 phi2
c3 net10 vg 20e-15
c2 vg net8 20e-15
m4 vbias phi2 vg 0 nmos w=27e-9 l=20e-9 nfin=50
m3 vcm phi2 net10 0 nmos w=27e-9 l=20e-9 nfin=50
m2 vb phi1 net10 0 nmos w=27e-9 l=20e-9 nfin=50
m1 net8 phi2 vcm 0 nmos w=27e-9 l=20e-9 nfin=50
m0 net8 phi1 va 0 nmos w=27e-9 l=20e-9 nfin=50
.ends DC_converter_2018_11_09_cmfb_schematic
** End of subcircuit definition.


** Library name: DC_converter
** Cell name: 2018_11_09_SCFilter
** View name: schematic
i5 vdd! id DC=40e-6
m0 voutn phi1 net67 vss nmos w=270e-9 l=20e-9 nfin=5
m7 net66 phi1 net63 vss nmos w=270e-9 l=20e-9 nfin=5
m6 net72 phi1 vinn vss nmos w=270e-9 l=20e-9 nfin=5
m3 agnd phi2 net67 vss nmos w=270e-9 l=20e-9 nfin=5
m5 agnd phi2 net63 vss nmos w=270e-9 l=20e-9 nfin=5
m4 net72 phi2 agnd vss nmos w=270e-9 l=20e-9 nfin=5
m8 net60 phi2 agnd vss nmos w=270e-9 l=20e-9 nfin=5
m11 agnd phi2 net68 vss nmos w=270e-9 l=20e-9 nfin=5
m9 agnd phi2 net62 vss nmos w=270e-9 l=20e-9 nfin=5
m10 net64 phi1 net62 vss nmos w=270e-9 l=20e-9 nfin=5
m12 net60 phi1 vinp vss nmos w=270e-9 l=20e-9 nfin=5
m14 voutp phi1 net68 vss nmos w=270e-9 l=20e-9 nfin=5
xi0 id vdd net64 net66 vss vbiasn id vbiasp1 vbiasp2 voutn voutp telescopic_ota
c9 voutp vss 60e-15
c8 voutn vss 60e-15
c7 net62 net68 30e-15
c6 net64 voutp 60e-15
c5 vinn net64 30e-15
c4 net60 net62 60e-15
c3 net66 voutn 60e-15
c2 vinp net66 30e-15
c1 net63 net67 30e-15
c0 net72 net63 60e-15
xi3 clk vdd! 0 phi1 phi2 DC_converter_2018_11_09_non_overlapping_clock_generator_schematic
v0 clk 0 PULSE 0 1 0 0 0 115e-9 250e-9
v11 vdd! 0 DC=1
v7 agnd 0 DC=550e-3
v6 vcm 0 DC=550e-3
v5 vbias_cm 0 DC=375e-3
v2 vinp 0 SIN 550e-3 10e-3 50e+3 0 0 0
v1 vinn 0 SIN 550e-3 10e-3 50e+3 0 0 180
v3 vbiasn 0 DC=700e-3
v4 vbiasp2 0 DC=300e-3
v10 vbiasp1 0 DC=490e-3
v8 vss 0 DC=0
v9 vdd 0 DC=1
xi13 voutn voutp id vcm vg phi1 phi2 DC_converter_2018_11_09_cmfb_schematic
**xi13 voutn voutp vbias_cm vcm vg phi1 phi2 DC_converter_2018_11_09_cmfb_schematic
.probe vdiff1=par('v(voutn)-v(voutp)')
.probe vdiff=par('v(vinn)-v(vinp)')
**.probe hb voutn
.END
