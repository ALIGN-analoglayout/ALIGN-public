.subckt comparator clk vcc vin vip von vop vss

mn0 vcom clk vss vss n nfin=6 nf=2 l=14e-9 m=8

mn1 vin_d vin vcom vss n nfin=6 nf=2 l=14e-9 m=16
mn2 vip_d vip vcom vss n nfin=6 nf=2 l=14e-9 m=16

mn3 vin_o vip_o vin_d vss n nfin=6 nf=2 l=14e-9 m=8
mn4 vip_o vin_o vip_d vss n nfin=6 nf=2 l=14e-9 m=8

mp5 vin_o vip_o vcc vcc p nfin=6 nf=2 l=14e-9 m=4
mp6 vip_o vin_o vcc vcc p nfin=6 nf=2 l=14e-9 m=4

mp7 vin_d clk vcc vcc p nfin=6 nf=2 l=14e-9 m=1
mp8 vip_d clk vcc vcc p nfin=6 nf=2 l=14e-9 m=1

mp9 vin_o clk vcc vcc p nfin=6 nf=2 l=14e-9 m=1
mp10 vip_o clk vcc vcc p nfin=6 nf=2 l=14e-9 m=1

mp11 vop vip_o vcc vcc p nfin=6 nf=2 l=14e-9 m=1
mn13 vop vip_o vss vss n nfin=6 nf=2 l=14e-9 m=1

mp12 von vin_o vcc vcc p nfin=6 nf=2 l=14e-9 m=1
mn14 von vin_o vss vss n nfin=6 nf=2 l=14e-9 m=1

.ends comparator
