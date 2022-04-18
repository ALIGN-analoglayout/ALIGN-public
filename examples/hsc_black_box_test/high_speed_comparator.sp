.subckt invhs vo vi vcc vss
mp0 vo vi vcc vcc p nfin=6 nf=2 l=14e-9 m=1
mn1 vo vi vss vss n nfin=6 nf=2 l=14e-9 m=1
.ends invhs

.subckt dp vind vipd vin vip vcom vss
mn1 vind vin vcom vss n nfin=6 nf=2 l=14e-9 m=16
mn2 vipd vip vcom vss n nfin=6 nf=2 l=14e-9 m=16
.ends dp

.subckt high_speed_comparator clk vcc vin vip von vop vss

mn0 vcom clk vss vss n nfin=6 nf=2 l=14e-9 m=8

dp0 vin_d vip_d vin vip vcom vss dp

mn3 vin_o vip_o vin_d vss n nfin=6 nf=2 l=14e-9 m=8
mn4 vip_o vin_o vip_d vss n nfin=6 nf=2 l=14e-9 m=8

mp5 vin_o vip_o vcc vcc p nfin=6 nf=2 l=14e-9 m=4
mp6 vip_o vin_o vcc vcc p nfin=6 nf=2 l=14e-9 m=4

mp7 vin_d clk vcc vcc p nfin=6 nf=2 l=14e-9 m=1
mp8 vip_d clk vcc vcc p nfin=6 nf=2 l=14e-9 m=1

mp9 vin_o clk vcc vcc p nfin=6 nf=2 l=14e-9 m=1
mp10 vip_o clk vcc vcc p nfin=6 nf=2 l=14e-9 m=1

xi0 vop vip_o vcc vss invhs
xi1 von vin_o vcc vss invhs

.ends high_speed_comparator
