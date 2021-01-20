.subckt high_speed_comparator clk vcc vin vip von vop vss
mmp5 vy clk vcc vcc p nfin=12 l=14e-9 m=1
mmp4 vyy clk vcc vcc p nfin=12 l=14e-9 m=1
mmp3 vx clk vcc vcc p nfin=12 l=14e-9 m=1
mmp2 vxx clk vcc vcc p nfin=12 l=14e-9 m=1
mmn2 vcom clk vss vss n nfin=12 l=14e-9 m=8
mmn0 vx vin vcom vss n nfin=12 l=14e-9 m=16
mmn1 vy vip vcom vss n nfin=12 l=14e-9 m=16
mmn4 vxx vyy vx vss n nfin=12 l=14e-9 m=8
mmn3 vyy vxx vy vss n nfin=12 l=14e-9 m=8
mmp1 vxx vyy vcc vcc p nfin=12 l=14e-9 m=4
mmp0 vyy vxx vcc vcc p nfin=12 l=14e-9 m=4
mmp7 vop vyy vcc vcc p nfin=12 l=14e-9 m=1
mmp6 von vxx vcc vcc p nfin=12 l=14e-9 m=1
mmn5 von vxx vss vss n nfin=12 l=14e-9 m=1
mmn6 vop vyy vss vss n nfin=12 l=14e-9 m=1


.ends high_speed_comparator

