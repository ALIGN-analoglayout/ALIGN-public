.subckt high_speed_comparator clk vcc vin vip von vop vss
mmp5 vip_d clk vcc vcc p nfin=12 l=14e-9 m=1
mmp4 vip_o clk vcc vcc p nfin=12 l=14e-9 m=1
mmp3 vin_d clk vcc vcc p nfin=12 l=14e-9 m=1
mmp2 vin_o clk vcc vcc p nfin=12 l=14e-9 m=1
mmn2 vcom clk vss vss n nfin=12 l=14e-9 m=8
mmn0 vin_d vin vcom vss n nfin=12 l=14e-9 m=16
mmn1 vip_d vip vcom vss n nfin=12 l=14e-9 m=16
mmn4 vin_o vip_o vin_d vss n nfin=12 l=14e-9 m=8
mmn3 vip_o vin_o vip_d vss n nfin=12 l=14e-9 m=8
mmp1 vin_o vip_o vcc vcc p nfin=12 l=14e-9 m=4
mmp0 vip_o vin_o vcc vcc p nfin=12 l=14e-9 m=4
mmp7 vop vip_o vcc vcc p nfin=12 l=14e-9 m=1
mmp6 von vin_o vcc vcc p nfin=12 l=14e-9 m=1
mmn5 von vin_o vss vss n nfin=12 l=14e-9 m=1
mmn6 vop vip_o vss vss n nfin=12 l=14e-9 m=1
.ends high_speed_comparator
