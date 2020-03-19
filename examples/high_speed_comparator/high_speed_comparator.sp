.subckt high_speed_comparator clk vdd_nom_123 v_in vip von vop vss
mmp5 vy clk vdd_nom_123 vdd_nom_123 p w=270e-9 l=20e-9 nfin=12
mmp1 vxx vyy vdd_nom_123 vdd_nom_123 p w=270e-9 l=20e-9 nfin=48
mmp7 vop vyy vdd_nom_123 vdd_nom_123 p w=270e-9 l=20e-9 nfin=12
mmp4 vyy clk vdd_nom_123 vdd_nom_123 p w=270e-9 l=20e-9 nfin=12
mmp6 von vxx vdd_nom_123 vdd_nom_123 p w=270e-9 l=20e-9 nfin=12
mmp3 vx clk vdd_nom_123 vdd_nom_123 p w=270e-9 l=20e-9 nfin=12
mmp2 vxx clk vdd_nom_123 vdd_nom_123 p w=270e-9 l=20e-9 nfin=12
mmp0 vyy vxx vdd_nom_123 vdd_nom_123 p w=270e-9 l=20e-9 nfin=48
mmn2 vcom clk vss vss n w=270e-9 l=20e-9 nfin=96
mmn5 von vxx vss vss n w=270e-9 l=20e-9 nfin=12
mmn6 vop vyy vss vss n w=270e-9 l=20e-9 nfin=12
mmn1 vy vip vcom vss n w=270e-9 l=20e-9 nfin=192
mmn4 vxx vyy vx vss n w=270e-9 l=20e-9 nfin=96
mmn3 vyy vxx vy vss n w=270e-9 l=20e-9 nfin=96
mmn0 vx v_in vcom vss n w=270e-9 l=20e-9 nfin=192
.ends high_speed_comparator

