

def comparator(name):
    netlist = f"""
.subckt {name} clk vccx vin vip von vop vssx
mmp8 vip_d clk vccx vccx p w=360e-9 l=40e-9 m=1 nf=2
mmp5 vin_o vip_o vccx vccx p w=360e-9 l=40e-9 m=5 nf=2
mmp14 vop vip_o vccx vccx p w=360e-9 l=40e-9 m=1 nf=2
mmp10 vip_o clk vccx vccx p w=360e-9 l=40e-9 m=2 nf=2
mmp13 von vin_o vccx vccx p w=360e-9 l=40e-9 m=1 nf=2
mmp7 vin_d clk vccx vccx p w=360e-9 l=40e-9 m=1 nf=2
mmp9 vin_o clk vccx vccx p w=360e-9 l=40e-9 m=2 nf=2
mmp6 vip_o vin_o vccx vccx p w=360e-9 l=40e-9 m=5 nf=2
mmn0 vcom clk vssx vssx n w=2.88e-6 l=40e-9 m=1 nf=16
mmn11 von vin_o vssx vssx n w=360e-9 l=40e-9 m=1 nf=2
mmn12 vop vip_o vssx vssx n w=360e-9 l=40e-9 m=1 nf=2
mmn2 vip_d vip vcom vssx n w=360e-9 l=40e-9 m=18 nf=2
mmn3 vin_o vip_o vin_d vssx n w=360e-9 l=40e-9 m=8 nf=2
mmn4 vip_o vin_o vip_d vssx n w=360e-9 l=40e-9 m=8 nf=2
mmn1 vin_d vin vcom vssx n w=360e-9 l=40e-9 m=18 nf=2
.ends {name}
"""
    return netlist


def ota_six(name):
    netlist = f"""
.subckt {name} ibias vccx vssx  von vin vip
    *mn1 ibias ibias vssx vssx  n nfin=4 nf=2 m=1
    mn1 ibias ibias vssx vssx  n nfin=4 nf=2 m=8
    mn2 tail  ibias vssx vssx  n nfin=4 nf=2 m=8
    mn3 vop vip tail vssx n nfin=4 nf=2 m=16
    mn4 von vin tail vssx n nfin=4 nf=2 m=16
    mp5 vop vop vccx vccx p nfin=4 nf=2 m=4
    mp6 von vop vccx vccx p nfin=4 nf=2 m=4
.ends {name}
"""
    return netlist
