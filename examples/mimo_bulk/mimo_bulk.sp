** Generated for: hspiceD
** Generated on: Mar  6 10:41:14 2021
** Design library name: TO65_20200429
** Design cell name: mimo_bulk
** Design view name: schematic


.model nmos_lvt nmos l=1 w=1 nfin=1 nf=1 m=1  stack=1 parallel=1

.TEMP 25.0
.OPTION
+    ARTIST=2
+    INGOLD=2
+    PARHIER=LOCAL
+    PSF=2

** Library name: TO65_20200429
** Cell name: TIA_1
** View name: schematic
.subckt TIA_1 _net3 _net1 _net0 _net2 vdda vssa
m1 _net0 _net1 vssa vssa nmos_lvt l=400e-9 w=64e-6 m=1 nf=8
m0 _net2 _net3 vssa vssa nmos_lvt l=400e-9 w=64e-6 m=1 nf=8
m5 net13 _net0 vdda vdda pmos_rvt l=200e-9 w=32e-6 m=1 nf=8
m4 net13 _net2 vdda vdda pmos_rvt l=200e-9 w=32e-6 m=1 nf=8
m3 _net0 _net1 net13 net13 pmos_rvt l=200e-9 w=192e-6 m=1 nf=32
m2 _net2 _net3 net13 net13 pmos_rvt l=200e-9 w=192e-6 m=1 nf=32
.ends TIA_1
** End of subcircuit definition.

** Library name: TO65_20200429
** Cell name: bottom_plate_4path_beamforming
** View name: schematic
.subckt bottom_plate_4path_beamforming clk_x1 clk_x1_b clk_x2 clk_x2_b clk_x3 clk_x3_b clk_x4 clk_x4_b _net19 _net17 vcmbias vdda vssa _net11 _net6 _net10 _net4 _net9 _net2 _net8 _net0
m15 _net0 clk_x4 _net1 _net1 nmos_rvt l=60e-9 w=2e-6 nf=16
m14 _net2 clk_x3 _net3 _net3 nmos_rvt l=60e-9 w=2e-6 nf=16
m13 _net4 clk_x2 _net5 _net5 nmos_rvt l=60e-9 w=2e-6 nf=16
m12 _net6 clk_x1 _net7 _net7 nmos_rvt l=60e-9 w=2e-6 nf=16
m11 _net8 clk_x4_b _net1 _net1 nmos_rvt l=60e-9 w=2e-6 nf=16
m10 _net9 clk_x3_b _net3 _net3 nmos_rvt l=60e-9 w=2e-6 nf=16
m9 _net10 clk_x2_b _net5 _net5 nmos_rvt l=60e-9 w=2e-6 nf=16
m8 _net11 clk_x1_b _net7 _net7 nmos_rvt l=60e-9 w=2e-6 nf=16
m7 _net0 clk_x4_b _net12 _net12 nmos_rvt l=60e-9 w=2e-6 nf=16
m6 _net2 clk_x3_b _net13 _net13 nmos_rvt l=60e-9 w=2e-6 nf=16
m5 _net4 clk_x2_b _net14 _net14 nmos_rvt l=60e-9 w=2e-6 nf=16
m4 _net6 clk_x1_b _net15 _net15 nmos_rvt l=60e-9 w=2e-6 nf=16
m3 _net8 clk_x4 _net12 _net12 nmos_rvt l=60e-9 w=2e-6 nf=16
m2 _net9 clk_x3 _net13 _net13 nmos_rvt l=60e-9 w=2e-6 nf=16
m1 _net10 clk_x2 _net14 _net14 nmos_rvt l=60e-9 w=2e-6 nf=16
m0 _net11 clk_x1 _net15 _net15 nmos_rvt l=60e-9 w=2e-6 nf=16
**Series configuration of R18
r18_1__dmy0  _net16 xr18_1__dmy0  100
r18_2__dmy0  xr18_1__dmy0 xr18_2__dmy0  100
r18_3__dmy0  xr18_2__dmy0 xr18_3__dmy0  100
r18_4__dmy0  xr18_3__dmy0 xr18_4__dmy0  100
r18_5__dmy0  xr18_4__dmy0 xr18_5__dmy0  100
r18_6__dmy0  xr18_5__dmy0 xr18_6__dmy0  100
r18_7__dmy0  xr18_6__dmy0 xr18_7__dmy0  100
r18_8__dmy0  xr18_7__dmy0 _net17  100
**End of R18

**Series configuration of R16
r16_1__dmy0  _net18 xr16_1__dmy0  100
r16_2__dmy0  xr16_1__dmy0 xr16_2__dmy0  100
r16_3__dmy0  xr16_2__dmy0 xr16_3__dmy0  100
r16_4__dmy0  xr16_3__dmy0 xr16_4__dmy0  100
r16_5__dmy0  xr16_4__dmy0 xr16_5__dmy0  100
r16_6__dmy0  xr16_5__dmy0 xr16_6__dmy0  100
r16_7__dmy0  xr16_6__dmy0 xr16_7__dmy0  100
r16_8__dmy0  xr16_7__dmy0 _net19  100
**End of R16
r11  _net1 _net18   140
r10  _net3 _net18   140
r9  _net5 _net18   140
r8  _net7 _net18   140
r3  _net12 _net16   140
r2  _net13 _net16   140
r1  _net14 _net16   140
r0  _net15 _net16   140

c8 _net16 _net17 2e-12
c9 _net18 _net19 2e-12
c4 _net7 vcmbias 2e-12
c5 _net5 vcmbias 2e-12
c7 _net1 vcmbias 2e-12
c6 _net3 vcmbias 2e-12
c2 _net13 vcmbias 2e-12
c3 _net12 vcmbias 2e-12
c1 _net15 vcmbias 2e-12
c0 _net14 vcmbias 2e-12
xi0 _net16 _net18 _net19 _net17 vdda vssa TIA_1
.ends bottom_plate_4path_beamforming
** End of subcircuit definition.

** Library name: TO65_20200429
** Cell name: bottom_plate_4path_BB_beamformer
** View name: schematic
.subckt bottom_plate_4path_BB_beamformer _net18 _net19 _net0 _net1 _net20 _net21 _net2 _net3 _net22 _net23 _net4 _net5 _net24 _net25 _net6 _net7 _net27 _net26 _net9 _net8 vcmbias _net10 _net11 _net12 _net13 _net14 _net15 _net16 _net17 vdda_bb vssa_bb
xi1 _net0 _net1 _net2 _net3 _net4 _net5 _net6 _net7 _net8 _net9 vcmbias vdda_bb vssa_bb _net10 _net11 _net12 _net13 _net14 _net15 _net16 _net17 bottom_plate_4path_beamforming
xi0 _net18 _net19 _net20 _net21 _net22 _net23 _net24 _net25 _net26 _net27 vcmbias vdda_bb vssa_bb _net10 _net11 _net12 _net13 _net14 _net15 _net16 _net17 bottom_plate_4path_beamforming
.ends bottom_plate_4path_BB_beamformer
** End of subcircuit definition.

** Library name: Tape_Jan20
** Cell name: INVx1_8Phase
** View name: schematic
.subckt INVx1_8Phase in out vdd vss
m1 out in vdd vdd pmos_rvt l=60e-9 w=1.2e-6 nf=4
m0 out in vss vss nmos_rvt l=60e-9 w=600e-9 nf=4
.ends INVx1_8Phase
** End of subcircuit definition.

** Library name: TO65_20200429
** Cell name: CLK_IO
** View name: schematic
** Digital
.subckt CLK_IO inn inp outn outp vdd vss
c0 net3 inp 2e-13
c1 net2 inn 2e-13
**Series configuration of R2
r2_1__dmy0  bias xr2_1__dmy0  200
r2_2__dmy0  xr2_1__dmy0 xr2_2__dmy0  200
r2_3__dmy0  xr2_2__dmy0 xr2_3__dmy0  200
r2_4__dmy0  xr2_3__dmy0 xr2_4__dmy0  200
r2_5__dmy0  xr2_4__dmy0 xr2_5__dmy0  200
r2_6__dmy0  xr2_5__dmy0 xr2_6__dmy0  200
r2_7__dmy0  xr2_6__dmy0 xr2_7__dmy0  200
r2_8__dmy0  xr2_7__dmy0 xr2_8__dmy0  200
r2_9__dmy0  xr2_8__dmy0 xr2_9__dmy0  200
r2_10__dmy0  xr2_9__dmy0 xr2_10__dmy0  200
r2_11__dmy0  xr2_10__dmy0 xr2_11__dmy0  200
r2_12__dmy0  xr2_11__dmy0 xr2_12__dmy0  200
r2_13__dmy0  xr2_12__dmy0 xr2_13__dmy0  200
r2_14__dmy0  xr2_13__dmy0 xr2_14__dmy0  200
r2_15__dmy0  xr2_14__dmy0 xr2_15__dmy0  200
r2_16__dmy0  xr2_15__dmy0 xr2_16__dmy0  200
r2_17__dmy0  xr2_16__dmy0 xr2_17__dmy0  200
r2_18__dmy0  xr2_17__dmy0 net3  200
**End of R2

**Series configuration of R0
r0_1__dmy0  net2 xr0_1__dmy0  200
r0_2__dmy0  xr0_1__dmy0 xr0_2__dmy0  200
r0_3__dmy0  xr0_2__dmy0 xr0_3__dmy0  200
r0_4__dmy0  xr0_3__dmy0 xr0_4__dmy0  200
r0_5__dmy0  xr0_4__dmy0 xr0_5__dmy0  200
r0_6__dmy0  xr0_5__dmy0 xr0_6__dmy0  200
r0_7__dmy0  xr0_6__dmy0 xr0_7__dmy0  200
r0_8__dmy0  xr0_7__dmy0 xr0_8__dmy0  200
r0_9__dmy0  xr0_8__dmy0 xr0_9__dmy0  200
r0_10__dmy0  xr0_9__dmy0 xr0_10__dmy0  200
r0_11__dmy0  xr0_10__dmy0 xr0_11__dmy0  200
r0_12__dmy0  xr0_11__dmy0 xr0_12__dmy0  200
r0_13__dmy0  xr0_12__dmy0 xr0_13__dmy0  200
r0_14__dmy0  xr0_13__dmy0 xr0_14__dmy0  200
r0_15__dmy0  xr0_14__dmy0 xr0_15__dmy0  200
r0_16__dmy0  xr0_15__dmy0 xr0_16__dmy0  200
r0_17__dmy0  xr0_16__dmy0 xr0_17__dmy0  200
r0_18__dmy0  xr0_17__dmy0 bias  200
**End of R0

xi3 net1b outn vdd vss INVx1_8Phase
xi2 net1 outp vdd vss INVx1_8Phase
xi1 net2 net1b vdd vss INVx1_8Phase
xi0 net3 net1 vdd vss INVx1_8Phase
m6 net1 net1b vss vss nmos_rvt l=60e-9 w=600e-9 nf=1
m4 net1b net1 vss vss nmos_rvt l=60e-9 w=600e-9 nf=1
m0 bias bias net026 vss nmos_rvt l=60e-9 w=600e-9 nf=1
m2 net026 vdd vss vss nmos_rvt l=60e-9 w=600e-9 nf=1
m7 net1 net1b vdd vdd pmos_rvt l=60e-9 w=600e-9 nf=1
m5 net1b net1 vdd vdd pmos_rvt l=60e-9 w=600e-9 nf=1
m3 net011 vss vdd vdd pmos_rvt l=60e-9 w=1.5e-6 nf=1
m1 bias bias net011 vdd pmos_rvt l=60e-9 w=1.5e-6 nf=1
.ends CLK_IO
** End of subcircuit definition.

** Library name: TO65_20200429
** Cell name: INVx1_8Phase
** View name: schematic
.subckt INVx1_8Phase_schematic in out vdd vss
m1 out in vdd vdd pmos_rvt l=60e-9 w=1.2e-6 nf=4
m0 out in vss vss nmos_rvt l=60e-9 w=600e-9 nf=4
.ends INVx1_8Phase_schematic
** End of subcircuit definition.

** Library name: TO65_20200429
** Cell name: INVx4_8Phase
** View name: schematic
.subckt INVx4_8Phase in out vdd vss
m1 out in vdd vdd pmos_rvt l=60e-9 w=1.2e-6 nf=16
m0 out in vss vss nmos_rvt l=60e-9 w=600e-9 nf=16
.ends INVx4_8Phase
** End of subcircuit definition.

** Library name: TO65_20200429
** Cell name: AND2
** View name: schematic
.subckt AND2 a b out vdd vss
m4 net26 b vss vss nmos_rvt l=60e-9 w=600e-9 nf=4
m6 out net21 vss vss nmos_rvt l=60e-9 w=600e-9 nf=4
m5 net21 a net26 vss nmos_rvt l=60e-9 w=600e-9 nf=4
m13 net21 b vdd vdd pmos_rvt l=60e-9 w=1.2e-6 nf=4
m14 net21 a vdd vdd pmos_rvt l=60e-9 w=1.2e-6 nf=4
m1 out net21 vdd vdd pmos_rvt l=60e-9 w=1.2e-6 nf=4
.ends AND2
** End of subcircuit definition.

** Library name: TO65_20200429
** Cell name: FF_DTG
** View name: schematic
** Digital
.subckt FF_DTG clk clkb in out0 out90 out180 out270 set setb vdd vss
m1 in setb vss vss nmos_rvt l=60e-9 w=600e-9 nf=4
m2 net59 in vss vss nmos_rvt l=60e-9 w=600e-9 nf=4
m3 net_l1 out90 vss vss nmos_rvt l=60e-9 w=600e-9 nf=4
m5 net023 net_l1 vss vss nmos_rvt l=60e-9 w=600e-9 nf=4
m14 net59 clkb out90 vss nmos_rvt l=60e-9 w=600e-9 nf=4
m12 net_l1 clk out0 vss nmos_rvt l=60e-9 w=600e-9 nf=4
m11 net023 clk out180 vss nmos_rvt l=60e-9 w=600e-9 nf=4
m6 net026 net59 vss vss nmos_rvt l=60e-9 w=600e-9 nf=4
m10 net026 clkb out270 vss nmos_rvt l=60e-9 w=600e-9 nf=4
m20 out90 clk net59 vdd pmos_rvt l=60e-9 w=1.2e-6 nf=4
m0 in set vdd vdd pmos_rvt l=60e-9 w=1.2e-6 nf=4
m4 net59 in vdd vdd pmos_rvt l=60e-9 w=1.2e-6 nf=4
m8 net023 net_l1 vdd vdd pmos_rvt l=60e-9 w=1.2e-6 nf=4
m7 net_l1 out90 vdd vdd pmos_rvt l=60e-9 w=1.2e-6 nf=4
m17 out0 clkb net_l1 vdd pmos_rvt l=60e-9 w=1.2e-6 nf=4
m13 out270 clk net026 vdd pmos_rvt l=60e-9 w=1.2e-6 nf=4
m16 out180 clkb net023 vdd pmos_rvt l=60e-9 w=1.2e-6 nf=4
m9 net026 net59 vdd vdd pmos_rvt l=60e-9 w=1.2e-6 nf=4
.ends FF_DTG
** End of subcircuit definition.

** Library name: TO65_20200429
** Cell name: Divider
** View name: schematic
** Digital
.subckt Divider clk clkb out<0> out<90> out<180> out<270> set setb vdd vss
xi0 clk clkb d<180> d<0> d<90> d<180> d<270> set setb vdd vss FF_DTG
m3<0> out<0> net012<0> vss vss nmos_rvt l=60e-9 w=600e-9 nf=4
m3<1> out<90> net012<1> vss vss nmos_rvt l=60e-9 w=600e-9 nf=4
m3<2> out<180> net012<2> vss vss nmos_rvt l=60e-9 w=600e-9 nf=4
m3<3> out<270> net012<3> vss vss nmos_rvt l=60e-9 w=600e-9 nf=4
m2<0> net012<0> d<0> vss vss nmos_rvt l=60e-9 w=600e-9 nf=4
m2<1> net012<1> d<90> vss vss nmos_rvt l=60e-9 w=600e-9 nf=4
m2<2> net012<2> d<180> vss vss nmos_rvt l=60e-9 w=600e-9 nf=4
m2<3> net012<3> d<270> vss vss nmos_rvt l=60e-9 w=600e-9 nf=4
m0<0> net012<0> d<0> vdd vdd pmos_rvt l=60e-9 w=1.2e-6 nf=4
m0<1> net012<1> d<90> vdd vdd pmos_rvt l=60e-9 w=1.2e-6 nf=4
m0<2> net012<2> d<180> vdd vdd pmos_rvt l=60e-9 w=1.2e-6 nf=4
m0<3> net012<3> d<270> vdd vdd pmos_rvt l=60e-9 w=1.2e-6 nf=4
m1<0> out<0> net012<0> vdd vdd pmos_rvt l=60e-9 w=1.2e-6 nf=4
m1<1> out<90> net012<1> vdd vdd pmos_rvt l=60e-9 w=1.2e-6 nf=4
m1<2> out<180> net012<2> vdd vdd pmos_rvt l=60e-9 w=1.2e-6 nf=4
m1<3> out<270> net012<3> vdd vdd pmos_rvt l=60e-9 w=1.2e-6 nf=4
.ends Divider
** End of subcircuit definition.

** Library name: TO65_20200429
** Cell name: 4Phase
** View name: schematic
** Digital
.subckt TO65_20200429_4Phase_schematic clk clkb ph<0> ph<1> ph<2> ph<3> set setb vdd vss
xi27<0> d1<0> clkb ph<0> vdd vss AND2
xi27<1> d1<90> clk ph<1> vdd vss AND2
xi27<2> d1<180> clkb ph<2> vdd vss AND2
xi27<3> d1<270> clk ph<3> vdd vss AND2
xi17 clk clkb d1<0> d1<90> d1<180> d1<270> set setb vdd vss Divider
.ends TO65_20200429_4Phase_schematic
** End of subcircuit definition.

** Library name: TO65_20200429
** Cell name: CLK_DIST_NW1
** View name: schematic
** Digital
.subckt CLK_DIST_NW1 clk clk0 clk180 clk270 clk90 clkb set setb vddd vssd
xi3 ph<3> net11 vddd vssd INVx1_8Phase_schematic
xi2 ph<2> net10 vddd vssd INVx1_8Phase_schematic
xi1 ph<1> net9 vddd vssd INVx1_8Phase_schematic
xi0 ph<0> net8 vddd vssd INVx1_8Phase_schematic
xi4 net8 clk0 vddd vssd INVx4_8Phase
xi5 net9 clk90 vddd vssd INVx4_8Phase
xi6 net10 clk180 vddd vssd INVx4_8Phase
xi7 net11 clk270 vddd vssd INVx4_8Phase
xi28 clk clkb ph<0> ph<1> ph<2> ph<3> set setb vddd vssd TO65_20200429_4Phase_schematic
.ends CLK_DIST_NW1
** End of subcircuit definition.

** Library name: TO65_20200429
** Cell name: CLK_BUFFER_4X
** View name: schematic
** Digital
.subckt CLK_BUFFER_4X in out vdd vss
xi0<0> in net2 vdd vss INVx4_8Phase
xi0<1> in net2 vdd vss INVx4_8Phase
xi0<2> in net2 vdd vss INVx4_8Phase
xi0<3> in net2 vdd vss INVx4_8Phase
xi1<0> net2 out vdd vss INVx4_8Phase
xi1<1> net2 out vdd vss INVx4_8Phase
xi1<2> net2 out vdd vss INVx4_8Phase
xi1<3> net2 out vdd vss INVx4_8Phase
.ends CLK_BUFFER_4X
** End of subcircuit definition.

** Library name: TO65_20200429
** Cell name: CLK_DIST_NW2
** View name: schematic
** Digital
.subckt CLK_DIST_NW2 clk clk0 clk180 clk270 clk90 clkb set setb vddd vssd
xi0 clk clk1 clk3 clk4 clk2 clkb set setb vddd vssd CLK_DIST_NW1
xi5 clk4 clk270 vddd vssd CLK_BUFFER_4X
xi4 clk3 clk180 vddd vssd CLK_BUFFER_4X
xi3 clk2 clk90 vddd vssd CLK_BUFFER_4X
xi1 clk1 clk0 vddd vssd CLK_BUFFER_4X
.ends CLK_DIST_NW2
** End of subcircuit definition.

** Library name: TO65_20200429
** Cell name: CLK_IO_DIST_NW1
** View name: schematic
** Digital
.subckt CLK_IO_DIST_NW1 clk0 clk180 clk270 clk90 _net1 _net0 set vddd vssd
xi0 _net0 _net1 net15 net16 vddd vssd CLK_IO
xi1 net16 clk0 clk180 clk270 clk90 net15 set net14 vddd vssd CLK_DIST_NW2
xi2 set net14 vddd vssd INVx1_8Phase_schematic
.ends CLK_IO_DIST_NW1
** End of subcircuit definition.

** Library name: TO65_20200429
** Cell name: CLK4Phase_BUFFER_4X
** View name: schematic
** Digital
.subckt CLK4Phase_BUFFER_4X clk1 clk1_buf clk2 clk2_buf clk3 clk3_buf clk4 clk4_buf vdd vss
xi4 clk3 clk3_buf vdd vss CLK_BUFFER_4X
xi3 clk4 clk4_buf vdd vss CLK_BUFFER_4X
xi2 clk2 clk2_buf vdd vss CLK_BUFFER_4X
xi0 clk1 clk1_buf vdd vss CLK_BUFFER_4X
.ends CLK4Phase_BUFFER_4X
** End of subcircuit definition.

** Library name: TO65_20200429
** Cell name: MIMO_Beamformers_CLK_NW2
** View name: schematic
.subckt MIMO_Beamformers_CLK_NW2 clk0 clk180 clk270 clk90 _net12 _net13 _net14 _net15 _net0 _net1 _net2 _net3 _net20 _net21 _net22 _net23 _net16 _net17 _net18 _net19 _net24 _net25 set vcmbias vdda_bb vddd vssa_bb vssd _net4 _net5 _net6 _net7 _net8 _net9 _net10 _net11
xi11 clk0_k01 clk180_k01 clk90_k01 clk270_k01 clk90_k01 clk270_k01 clk180_k01 clk0_k01 clk180_k01 clk0_k01 clk270_k01 clk90_k01 clk270_k01 clk90_k01 clk0_k01 clk180_k01 _net0 _net1 _net2 _net3 vcmbias _net4 _net5 _net6 _net7 _net8 _net9 _net10 _net11 vdda_bb vssa_bb bottom_plate_4path_BB_beamformer
xi9 clk0_k01 clk180_k01 clk90_k01 clk270_k01 clk0_k01 clk180_k01 clk90_k01 clk270_k01 clk0_k01 clk180_k01 clk90_k01 clk270_k01 clk0_k01 clk180_k01 clk90_k01 clk270_k01 _net12 _net13 _net14 _net15 vcmbias _net4 _net5 _net6 _net7 _net8 _net9 _net10 _net11 vdda_bb vssa_bb bottom_plate_4path_BB_beamformer
xi12 clk0_k23 clk180_k23 clk90_k23 clk270_k23 clk270_k23 clk90_k23 clk0_k23 clk180_k23 clk180_k23 clk0_k23 clk270_k23 clk90_k23 clk90_k23 clk270_k23 clk180_k23 clk0_k23 _net16 _net17 _net18 _net19 vcmbias _net4 _net5 _net6 _net7 _net8 _net9 _net10 _net11 vdda_bb vssa_bb bottom_plate_4path_BB_beamformer
xi10 clk0_k23 clk180_k23 clk90_k23 clk270_k23 clk180_k23 clk0_k23 clk270_k23 clk90_k23 clk0_k23 clk180_k23 clk90_k23 clk270_k23 clk180_k23 clk0_k23 clk270_k23 clk90_k23 _net20 _net21 _net22 _net23 vcmbias _net4 _net5 _net6 _net7 _net8 _net9 _net10 _net11 vdda_bb vssa_bb bottom_plate_4path_BB_beamformer
xi0 clk0 clk180 clk270 clk90 _net24 _net25 set vddd vssd CLK_IO_DIST_NW1
xi3 clk0 clk0_k23 clk90 clk90_k23 clk180 clk180_k23 clk270 clk270_k23 vddd vssd CLK4Phase_BUFFER_4X
xi2 clk0 clk0_k01 clk90 clk90_k01 clk180 clk180_k01 clk270 clk270_k01 vddd vssd CLK4Phase_BUFFER_4X
.ends MIMO_Beamformers_CLK_NW2
** End of subcircuit definition.

** Library name: TO65_20200429
** Cell name: bottom_plate_4path_mixer_diff_end
** View name: schematic
.subckt bottom_plate_4path_mixer_diff_end clk0 clk90 clk180 clk270 _net1 _net0 vcmbias vdda_q
c7 n5 _net0 13e-12
c3 n1 _net1 13e-12
c8 n6 _net0 13e-12
c9 n7 _net0 13e-12
c5 n3 _net1 13e-12
c4 n2 _net1 13e-12
c6 n4 _net1 13e-12
c10 n8 _net0 13e-12
m0 n1 clk0 n5 vcmbias nmos_rvt l=60e-9 w=4e-6 nf=16
m1 n2 clk90 n6 vcmbias nmos_rvt l=60e-9 w=4e-6 nf=16
m2 n3 clk180 n7 vcmbias nmos_rvt l=60e-9 w=4e-6 nf=16
m3 n4 clk270 n8 vcmbias nmos_rvt l=60e-9 w=4e-6 nf=16
m4 n1 clk0 vcmbias vcmbias nmos_rvt l=60e-9 w=4e-6 nf=16
m5 n2 clk90 vcmbias vcmbias nmos_rvt l=60e-9 w=4e-6 nf=16
m6 n3 clk180 vcmbias vcmbias nmos_rvt l=60e-9 w=4e-6 nf=16
m7 n4 clk270 vcmbias vcmbias nmos_rvt l=60e-9 w=4e-6 nf=16
m8 n5 clk0 vcmbias vcmbias nmos_rvt l=60e-9 w=4e-6 nf=16
m9 n6 clk90 vcmbias vcmbias nmos_rvt l=60e-9 w=4e-6 nf=16
m10 n7 clk180 vcmbias vcmbias nmos_rvt l=60e-9 w=4e-6 nf=16
m11 n8 clk270 vcmbias vdda_q nmos_rvt l=60e-9 w=4e-6 nf=16
** vdda_q was floating add to one port @jitesh to fix it
.ends bottom_plate_4path_mixer_diff_end
** End of subcircuit definition.

** Library name: TO65_20200429
** Cell name: MIMO_mixers_bottom_plate
** View name: schematic
.subckt MIMO_mixers_bottom_plate clk0 clk180 clk270 clk90 vcmbias vdda_q _net0 _net1 _net2 _net3 _net4 _net5 _net6 _net7
xi0 clk0 clk90 clk180 clk270 _net0 _net1 vcmbias vdda_q bottom_plate_4path_mixer_diff_end
xi1 clk0 clk90 clk180 clk270 _net2 _net3 vcmbias vdda_q bottom_plate_4path_mixer_diff_end
xi2 clk0 clk90 clk180 clk270 _net4 _net5 vcmbias vdda_q bottom_plate_4path_mixer_diff_end
xi3 clk0 clk90 clk180 clk270 _net6 _net7 vcmbias vdda_q bottom_plate_4path_mixer_diff_end
.ends MIMO_mixers_bottom_plate
** End of subcircuit definition.

** Library name: TO65_20200429
** Cell name: MIMO_MIXER_CLK_BUFFER
** View name: schematic
.subckt MIMO_MIXER_CLK_BUFFER clk1 clk2 clk3 clk4 vcmbias vdda_q vddd vssd _net0 _net1 _net2 _net3 _net4 _net5 _net6 _net7
xi0 clk0 clk180 clk270 clk90 vcmbias vdda_q _net0 _net1 _net2 _net3 _net4 _net5 _net6 _net7 MIMO_mixers_bottom_plate
xi3<1> clk3 clk180 vddd vssd CLK_BUFFER_4X
xi3<0> clk3 clk180 vddd vssd CLK_BUFFER_4X
xi2<1> clk1 clk0 vddd vssd CLK_BUFFER_4X
xi2<0> clk1 clk0 vddd vssd CLK_BUFFER_4X
xi1<1> clk2 clk90 vddd vssd CLK_BUFFER_4X
xi1<0> clk2 clk90 vddd vssd CLK_BUFFER_4X
xi4<1> clk4 clk270 vddd vssd CLK_BUFFER_4X
xi4<0> clk4 clk270 vddd vssd CLK_BUFFER_4X
.ends MIMO_MIXER_CLK_BUFFER
** End of subcircuit definition.

** Library name: TO65_20200429
** Cell name: mimo_bulk
** View name: schematic
.subckt mimo_bulk _net7 _net25 _net11 _net10 _net9 _net14 _net13 _net12 _net6 _net5 _net4 _net3 _net2 _net1 _net0 _net8 _net16 _net15 set vcmbias vdda_bb vddd vssa_bb vssd _net17 _net24 _net22 _net23 _net20 _net21 _net18 _net19
xi0 clk0 clk180 clk270 clk90 _net7 _net25 _net11 _net10 _net9 _net14 _net13 _net12 _net6 _net5 _net4 _net3 _net2 _net1 _net0 _net8 _net16 _net15 set vcmbias vdda_bb vddd vssa_bb vssd _net17 _net24 _net22 _net23 _net20 _net21 _net18 _net19 MIMO_Beamformers_CLK_NW2
xi1 clk0 clk90 clk180 clk270 vcmbias vdda_bb vddd vssd _net17 _net24 _net22 _net23 _net20 _net21 _net18 _net19 MIMO_MIXER_CLK_BUFFER
.ends mimo_bulk
** End of subcircuit definition.
.END
