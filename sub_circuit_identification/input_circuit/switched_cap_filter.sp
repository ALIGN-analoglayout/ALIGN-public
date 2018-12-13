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
**i4 vdd! net17 DC=10e-6
**i10 vbiasp 0 DC=10e-6
**i9 vdd! vbiasn DC=10e-6

m9 voutn vbiasn net8 0 nmos_rvt w=270e-9 l=20e-9 nfin=25
m8 voutp vbiasn net014 0 nmos_rvt w=270e-9 l=20e-9 nfin=25
m5 id id 0 0 nmos_rvt w=270e-9 l=20e-9 nfin=10
m4 net10 vbiasnd 0 0 nmos_rvt w=270e-9 l=20e-9 nfin=50
m3 net014 vinn net10 0 nmos_rvt w=270e-9 l=20e-9 nfin=70
m0 net8 vinp net10 0 nmos_rvt w=270e-9 l=20e-9 nfin=70
m7 voutp vbiasp net012 net012 pmos_rvt w=270e-9 l=20e-9 nfin=15
m6 voutn vbiasp net06 net06 pmos_rvt w=270e-9 l=20e-9 nfin=15
m2 net012 vbiasp1 vdd! vdd! pmos_rvt w=270e-9 l=20e-9 nfin=10
m1 net06 vbiasp1 vdd! vdd! pmos_rvt w=270e-9 l=20e-9 nfin=10
**v2 net15 0 DC=550e-3 AC 500e-3 180
**v1 net17 0 DC=550e-3 AC 500e-3
**v3 vbiasn 0 DC=700e-3
m3nbias vbiasn vbiasn net10 0 nmos_rvt w=270e-9 l=20e-9 nfin=5
m3pbias vbiasn vbiasp1 vdd! vdd! pmos_rvt w=270e-9 l=20e-9 nfin=10
**v4 vbiasp 0 DC=300e-3
m1pup net8_bias net8_bias vdd! vdd! pmos_rvt w=270e-9 l=20e-9 nfin=20
m1pdown vbiasp vbiasp net8_bias net8_bias pmos_rvt w=270e-9 l=20e-9 nfin=20
m1n vbiasp id 0 0 nmos_rvt w=270e-9 l=20e-9 nfin=10
**v5 vbiasp1 0 DC=575e-3
m2n vbiasp1 id 0 0 nmos_rvt w=270e-9 l=20e-9 nfin=10
m2p vbiasp1 vbiasp1 vdd! vdd! pmos_rvt w=270e-9 l=20e-9 nfin=10
**v0 vdd! 0 DC=1000e-3
**i5 vdd! id DC=40e-6
c2 voutp 0 60e-15
c3 voutn 0 60e-15
.ends DC_converter_2018_11_09_ASAP7_current_mirror_ota_schematic
** End of subcircuit definition.


** Library name: asap7ssc7p5t
** Cell name: INVx1_ASAP7_75t_R
** View name: schematic
.subckt INVx1_ASAP7_75t_R a y vdd vss
m0 y a vss vss nmos_rvt w=81e-9 l=20e-9 nfin=3
m1 y a vdd vdd pmos_rvt w=81e-9 l=20e-9 nfin=3
.ends INVx1_ASAP7_75t_R
** End of subcircuit definition.

** Library name: asap7ssc7p5t
** Cell name: INVx1_ASAP7_75t_R_21
** View name: schematic
.subckt INVx1_ASAP7_75t_R_21 a y vdd vss
m0 y a vss vss nmos_rvt w=81e-9 l=20e-9 nfin=21
m1 y a vdd vdd pmos_rvt w=81e-9 l=20e-9 nfin=21
.ends INVx1_ASAP7_75t_R_21
** End of subcircuit definition.

** Library name: DC_converter
** Cell name: 2018_12_03_ASAP7_transmission_gate
** View name: schematic
.subckt DC_converter_2018_12_03_ASAP7_transmission_gate a y vdd vss
m0 y vdd a 0 nmos_rvt w=81e-9 l=20e-9 nfin=3
m1 y vss a a pmos_rvt w=81e-9 l=20e-9 nfin=3
.ends DC_converter_2018_12_03_ASAP7_transmission_gate
** End of subcircuit definition.

** Library name: DC_converter
** Cell name: 2018_11_09_ASAP7_NAND_gate
** View name: schematic
.subckt DC_converter_2018_11_09_ASAP7_NAND_gate_schematic a b out vdd vss
m2 out a net22 vss nmos_rvt w=54e-9 l=20e-9 nfin=2
m3 net22 b vss vss nmos_rvt w=54e-9 l=20e-9 nfin=2
m0 out a vdd vdd pmos_rvt w=27e-9 l=20e-9 nfin=1
m1 out b vdd vdd pmos_rvt w=27e-9 l=20e-9 nfin=1
.ends DC_converter_2018_11_09_ASAP7_NAND_gate_schematic
** End of subcircuit definition.

** Library name: DC_converter
** Cell name: 2018_11_09_ASAP7_non_overlapping_clock_generator
** View name: schematic
.subckt DC_converter_2018_11_09_ASAP7_non_overlapping_clock_generator_schematic clk d_vdd d_gnd phi1 phi2
xi6 clk net9 d_vdd d_gnd INVx1_ASAP7_75t_R
xi6_tg clk net9_tg d_dd d_gnd DC_converter_2018_12_03_ASAP7_transmission_gate
xi5 net12 phi2 d_vdd d_gnd INVx1_ASAP7_75t_R_21
xi4 net17 net12 d_vdd d_gnd INVx1_ASAP7_75t_R
xi3 net8 phi1 d_vdd d_gnd INVx1_ASAP7_75t_R_21
xi2 net15 net8 d_vdd d_gnd INVx1_ASAP7_75t_R
xi1 net16 net15 d_vdd d_gnd INVx1_ASAP7_75t_R
xi0 net18 net17 d_vdd d_gnd INVx1_ASAP7_75t_R
xi8 net9 net8 net18 d_vdd d_gnd DC_converter_2018_11_09_ASAP7_NAND_gate_schematic
xi7 net12 net9_tg net16 d_vdd d_gnd DC_converter_2018_11_09_ASAP7_NAND_gate_schematic
.ends DC_converter_2018_11_09_ASAP7_non_overlapping_clock_generator_schematic
** End of subcircuit definition.


** Library name: DC_converter
** Cell name: 2018_11_09_ASAP7_cmfb
** View name: schematic
.subckt DC_converter_2018_11_09_ASAP7_cmfb_schematic va vb vbias vcm vg phi1 phi2
c3 net10 vg 20e-15
c2 vg net8 20e-15
m4 vbias phi2 vg 0 nmos_rvt w=27e-9 l=20e-9 nfin=50
m3 vcm phi2 net10 0 nmos_rvt w=27e-9 l=20e-9 nfin=50
m2 vb phi1 net10 0 nmos_rvt w=27e-9 l=20e-9 nfin=50
m1 net8 phi2 vcm 0 nmos_rvt w=27e-9 l=20e-9 nfin=50
m0 net8 phi1 va 0 nmos_rvt w=27e-9 l=20e-9 nfin=50
.ends DC_converter_2018_11_09_ASAP7_cmfb_schematic
** End of subcircuit definition.


** Library name: DC_converter
** Cell name: 2018_11_09_ASAP7_SCFilter
** View name: schematic
i5 vdd! id DC=40e-6
xi0 vg net08 net09 voutn voutp id DC_converter_2018_11_09_ASAP7_current_mirror_ota_schematic
c11 net11 net13 30e-15
c10 net3 net1 60e-15
c9 net09 voutn 50e-15
c8 net09 vinn 30e-15
c7 net08 voutp 50e-15
c6 net4 net2 60e-15
c5 net08 vinp 30e-15
c4 net12 net14 30e-15
xi3 clk vdd! 0 phi1 phi2 DC_converter_2018_11_09_ASAP7_non_overlapping_clock_generator_schematic
v0 clk 0 PULSE 0 1 0 0 0 115e-9 250e-9
v11 vdd! 0 DC=1
v7 agnd 0 DC=550e-3
v6 vcm 0 DC=550e-3
v5 vbias_cm 0 DC=375e-3
v2 vinp 0 SIN 550e-3 10e-3 50e+3 0 0 0
v1 vinn 0 SIN 550e-3 10e-3 50e+3 0 0 180
m15 net11 phi1 net09 0 nmos_rvt w=27e-9 l=20e-9 nfin=10
m14 voutn phi1 net13 0 nmos_rvt w=27e-9 l=20e-9 nfin=10
m13 net09 phi1 net3 0 nmos_rvt w=27e-9 l=20e-9 nfin=10
m12 net1 phi1 vinp 0 nmos_rvt w=27e-9 l=20e-9 nfin=10
m11 agnd phi2 net13 0 nmos_rvt w=27e-9 l=20e-9 nfin=10
m10 net11 phi2 agnd 0 nmos_rvt w=27e-9 l=20e-9 nfin=10
m9 agnd phi2 net3 0 nmos_rvt w=27e-9 l=20e-9 nfin=10
m8 net1 phi2 agnd 0 nmos_rvt w=27e-9 l=20e-9 nfin=10
m7 net08 phi1 net4 0 nmos_rvt w=27e-9 l=20e-9 nfin=10
m6 net2 phi1 vinn 0 nmos_rvt w=27e-9 l=20e-9 nfin=10
m5 agnd phi2 net4 0 nmos_rvt w=27e-9 l=20e-9 nfin=10
m4 net2 phi2 agnd 0 nmos_rvt w=27e-9 l=20e-9 nfin=10
m3 agnd phi2 net14 0 nmos_rvt w=27e-9 l=20e-9 nfin=10
m2 net12 phi2 agnd 0 nmos_rvt w=27e-9 l=20e-9 nfin=10
m1 net12 phi1 net08 0 nmos_rvt w=27e-9 l=20e-9 nfin=10
m0 voutp phi1 net14 0 nmos_rvt w=27e-9 l=20e-9 nfin=10

xi13 voutn voutp id vcm vg phi1 phi2 DC_converter_2018_11_09_ASAP7_cmfb_schematic
**xi13 voutn voutp vbias_cm vcm vg phi1 phi2 DC_converter_2018_11_09_ASAP7_cmfb_schematic
.probe vdiff1=par('v(voutn)-v(voutp)')
.probe vdiff=par('v(vinn)-v(vinp)')
.END