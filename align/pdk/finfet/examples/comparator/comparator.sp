.subckt comparator clk vccx vin vip von vop vssx
mp8 vip_d clk vccx vccx p w=360e-9 m=1 nf=2
mp5 vin_o vip_o vccx vccx p w=360e-9 m=6 nf=2
mp14 vop vip_o vccx vccx p w=360e-9 m=1 nf=2
mp10 vip_o clk vccx vccx p w=360e-9 m=2 nf=2
mp13 von vin_o vccx vccx p w=360e-9 m=1 nf=2
mp7 vin_d clk vccx vccx p w=360e-9 m=1 nf=2
mp9 vin_o clk vccx vccx p w=360e-9 m=2 nf=2
mp6 vip_o vin_o vccx vccx p w=360e-9 m=6 nf=2
mn0 vcom clk vssx vssx n w=2.88e-6 m=1 nf=16
mn11 von vin_o vssx vssx n w=360e-9 m=1 nf=2
mn12 vop vip_o vssx vssx n w=360e-9 m=1 nf=2
mn2 vip_d vip vcom vssx n w=360e-9 m=18 nf=2
mn3 vin_o vip_o vin_d vssx n w=360e-9 m=8 nf=2
mn4 vip_o vin_o vip_d vssx n w=360e-9 m=8 nf=2
mn1 vin_d vin vcom vssx n w=360e-9 m=18 nf=2
.ends comparator
