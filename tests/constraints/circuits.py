import textwrap


def comparator(name):
    netlist = textwrap.dedent(f"""\
        .subckt {name} clk vccx vin vip von vop vssx
        mp8 vip_d clk vccx vccx p w=360e-9 m=1 nf=2
        mp5 vin_o vip_o vccx vccx p w=360e-9 m=6 nf=2
        mp14 vop vip_o vccx vccx p w=360e-9 m=1 nf=2
        mp10 vip_o clk vccx vccx p w=360e-9 m=2 nf=2
        mp13 von vin_o vccx vccx p w=360e-9 m=1 nf=2
        mp7 vin_d clk vccx vccx p w=360e-9 m=1 nf=2
        mp9 vin_o clk vccx vccx p w=360e-9 m=2 nf=2
        mp6 vip_o vin_o vccx vccx p w=360e-9 m=5 nf=2
        mn0 vcom clk vssx vssx n w=2.88e-6 m=1 nf=16
        mn11 von vin_o vssx vssx n w=360e-9 m=1 nf=2
        mn12 vop vip_o vssx vssx n w=360e-9 m=1 nf=2
        mn2 vip_d vip vcom vssx n w=360e-9 m=18 nf=2
        mn3 vin_o vip_o vin_d vssx n w=360e-9 m=8 nf=2
        mn4 vip_o vin_o vip_d vssx n w=360e-9 m=8 nf=2
        mn1 vin_d vin vcom vssx n w=360e-9 m=18 nf=2
        .ends {name}
    """)
    return netlist


def ota_six(name):
    netlist = textwrap.dedent(f"""\
        .subckt {name} ibias vccx vssx  von vin vip
        //mn1 ibias ibias vssx vssx n w=360e-9 nf=2 m=1
        mn1 ibias ibias vssx vssx n w=360e-9 nf=2 m=8
        mn2 tail  ibias vssx vssx n w=360e-9 nf=2 m=8
        mn3 vop vip tail vssx n w=360e-9 nf=2 m=16
        mn4 von vin tail vssx n w=360e-9 nf=2 m=16
        mp5 vop vop vccx vccx p w=360e-9 nf=2 m=4
        mp6 von vop vccx vccx p w=360e-9 nf=2 m=4
        .ends {name}
    """)
    return netlist


def common_source(name):
    netlist = textwrap.dedent(f"""\
        .subckt {name} vin vop vccx vssx
        mp0 vop vop vccx vccx p w=720e-9 nf=4 m=4
        mn0 vop vin vssx vssx n w=720e-9 nf=4 m=4
        .ends {name}
    """)
    return netlist


def tia(name):
    netlist = textwrap.dedent(f"""\
        .subckt pcell_tfr_0 a b
        xi0 a b tfr_prim w=1e-6 l=1e-6
        .ends pcell_tfr_0
        .subckt {name} vin vop vccx vss
        mp0 vop vin vccx vccx p w=720e-9 nf=4 m=4
        mn0 vop vin vssx vssx n w=720e-9 nf=4 m=4
        xi0 vin vop pcell_tfr_0
        .ends {name}
    """)
    return netlist


def cascode_amplifier(name):
    netlist = textwrap.dedent(f"""\
        .subckt {name} vin vop vcc vss nbs pbs
        mp1 vop pbs vcc vcc p w=720e-9 nf=4 m=5
        mn1 vop nbs vmd vss n w=720e-9 nf=4 m=5
        mn0 vmd vin vss vss n w=720e-9 nf=4 m=5
        .ends {name}
        """)
    return netlist


def ota_five(name):
    netlist = textwrap.dedent(f"""\
        .subckt {name} vin vip vop vccx vssx vbn
        mp1 von von vccx vccx p w=720e-9 nf=4 m=5
        mp2 vop von vccx vccx p w=720e-9 nf=4 m=5
        mn1 von vip vcom vssx n w=720e-9 nf=4 m=5
        mn2 vop vin vcom vssx n w=720e-9 nf=4 m=5
        mn0 vcom vbn vssx vssx n w=720e-9 nf=4 m=5
        .ends {name}
        """)
    return netlist
