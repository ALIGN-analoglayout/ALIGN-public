import textwrap


def common_source(name):
    netlist = textwrap.dedent(f"""\
        .subckt {name} vin vop vccx vssx
        mp0 vop vop vccx vccx p w=720e-9 nf=4 m=4
        mn0 vop vin vssx vssx n w=720e-9 nf=4 m=4
        .ends {name}
    """)
    return netlist
