** Generated for: hspiceD
** Generated on: Jun 12 13:28:57 2020
** Design library name: high_speed_comparator_v1
** Design cell name: high_speed_comparator_hspice
** Design view name: schematic


** Library name: high_speed_comparator_v1
** Cell name: inv1
** View name: schematic
.subckt inv1 in out vddi vssi
xn0 out in vssi vssi nfet m=1 l=14e-9 nfin=2 nf=1 pre_layout_local=-1
xn1 out in vddi vddi pfet m=1 l=14e-9 nfin=2 nf=1 pre_layout_local=-1
.ends inv1
** End of subcircuit definition.

** Library name: high_speed_comparator_v1
** Cell name: strong_arm_latch
** View name: schematic
.subckt strong_arm_latch clk vcc vin vip von vop vss
xp5 net42 clk vcc vcc pfet m=1 l=14e-9 nfin=4 nf=2 pre_layout_local=-1
xp4 net8 clk vcc vcc pfet m=1 l=14e-9 nfin=4 nf=2 pre_layout_local=-1
xp3 net44 clk vcc vcc pfet m=1 l=14e-9 nfin=4 nf=2 pre_layout_local=-1
xp2 net16 net44 vcc vcc pfet m=1 l=14e-9 nfin=4 nf=8 pre_layout_local=-1
xp1 net16 clk vcc vcc pfet m=1 l=14e-9 nfin=4 nf=2 pre_layout_local=-1
xp0 net44 net16 vcc vcc pfet m=1 l=14e-9 nfin=4 nf=8 pre_layout_local=-1
xn4 net34 clk vss vss nfet m=1 l=14e-9 nfin=4 nf=16 pre_layout_local=-1
xn3 net42 vin net34 vss nfet m=1 l=14e-9 nfin=4 nf=32 pre_layout_local=-1
xn2 net8 vip net34 vss nfet m=1 l=14e-9 nfin=4 nf=32 pre_layout_local=-1
xn1 net16 net44 net8 vss nfet m=1 l=14e-9 nfin=4 nf=16 pre_layout_local=-1
xn0 net44 net16 net42 vss nfet m=1 l=14e-9 nfin=4 nf=16 pre_layout_local=-1
xi1 net16 von vcc vss inv1
xi0 net44 vop vcc vss inv1
.ends strong_arm_latch
** End of subcircuit definition.

** Library name: high_speed_comparator_v1
** Cell name: nor
** View name: schematic
.subckt nor a b o1 vcc vssx
xp1 o1 a net010 vcc pfet m=1 l=14e-9 nfin=12 nf=1 pre_layout_local=-1
xp0 net010 b vcc vcc pfet m=1 l=14e-9 nfin=12 nf=1 pre_layout_local=-1
xn1 o1 a vssx vssx nfet m=1 l=14e-9 nfin=8 nf=1 pre_layout_local=-1
xn0 o1 b vssx vssx nfet m=1 l=14e-9 nfin=8 nf=1 pre_layout_local=-1
.ends nor
** End of subcircuit definition.

** Library name: high_speed_comparator_v1
** Cell name: inv2
** View name: schematic
.subckt inv2 in out vddi vssi
xn0 out in vssi vssi nfet m=1 l=14e-9 nfin=4 nf=1 pre_layout_local=-1
xn1 out in vddi vddi pfet m=1 l=14e-9 nfin=4 nf=1 pre_layout_local=-1
.ends inv2
** End of subcircuit definition.

** Library name: high_speed_comparator_v1
** Cell name: inv3
** View name: schematic
.subckt inv3 in out vddi vssi
xn0 out in vssi vssi nfet m=1 l=14e-9 nfin=8 nf=1 pre_layout_local=-1
xn1 out in vddi vddi pfet m=1 l=14e-9 nfin=8 nf=1 pre_layout_local=-1
.ends inv3
** End of subcircuit definition.

** Library name: high_speed_comparator_v1
** Cell name: inv4
** View name: schematic
.subckt inv4 in out vddi vssi
xn0 out in vssi vssi nfet m=1 l=14e-9 nfin=16 nf=1 pre_layout_local=-1
xn1 out in vddi vddi pfet m=1 l=14e-9 nfin=16 nf=1 pre_layout_local=-1
.ends inv4
** End of subcircuit definition.

** Library name: high_speed_comparator_v1
** Cell name: high_speed_comparator_hspice
** View name: schematic
.subckt high_speed_comparator clk_ideal vip vin clk von vop von_latch vop_latch vcc vss
xi0 clk vcc vin vip von vop vss strong_arm_latch
xi1 clk_ideal net12 vcc vss inv1
xi6 vop_latch von von_latch vcc vss nor
xi5 vop von_latch vop_latch vcc vss nor
xi2 net12 net11 vcc vss inv2
xi3 net11 net10 vcc vss inv3
xi4 net10 clk vcc vss inv4
.ends high_speed_comparator
