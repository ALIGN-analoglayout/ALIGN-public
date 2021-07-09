import textwrap
try:
    from .utils import get_test_id, build_example, run_example
    from . import circuits
except BaseException:
    from utils import get_test_id, build_example, run_example
    import circuits
import shutil


def test_1():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
        .subckt pcell_tfr_0 n1 n2
            xi0 n1 n2 tfr_prim w=1e-6 l=1e-6
        .ends pcell_tfr_0
        .subckt {name} vin vop vccx vssx
            mp0 vop vin vccx vccx p w=720e-9 nf=4 m=4
            mn0 vop vin vssx vssx n w=720e-9 nf=4 m=4
            xi0 vin vop pcell_tfr_0
            xi1 vop vssx pcell_tfr_0
        .ends {name}
    """)
    setup = textwrap.dedent("""\
        POWER = vccx
        GND = vssx
        """)
    constraints = []
    example = build_example(name, netlist, setup, constraints)
    run_example(example, cleanup=False)


def test_2():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
        .subckt pcell_tfr_0 n1 n2
            xi0 n1 n3 tfr_prim w=1e-6 l=1e-6
            xi1 n3 n2 tfr_prim w=1e-6 l=1e-6
        .ends pcell_tfr_0
        .subckt {name} vin vop vccx vssx
            mp0 vop vin vccx vccx p w=720e-9 nf=4 m=4
            mn0 vop vin vssx vssx n w=720e-9 nf=4 m=4
            xi0 vin vop pcell_tfr_0
        .ends {name}
    """)
    setup = textwrap.dedent("""\
        POWER = vccx
        GND = vssx
        """)
    constraints = []
    example = build_example(name, netlist, setup, constraints)
    run_example(example, cleanup=False)


def test_3():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
        .subckt pcell_tfr_0 n1 n2
            xi0 n1 n3 tfr_prim w=1e-6 l=1e-6
            xi1 n3 n2 tfr_prim w=1e-6 l=1e-6
        .ends pcell_tfr_0
        .subckt {name} vin vop vccx vssx
            mp0 vop vin vccx vccx p w=720e-9 nf=4 m=4
            mn0 vop vin vssx vssx n w=720e-9 nf=4 m=4
            xi0 vin vop pcell_tfr_0
            xi1 vop vssx pcell_tfr_0
        .ends {name}
    """)
    setup = textwrap.dedent("""\
        POWER = vccx
        GND = vssx
        """)
    constraints = []
    example = build_example(name, netlist, setup, constraints)
    run_example(example, cleanup=False)


def test_4():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
        .subckt pcell_tfr_0 n1 n2
            xi0 n1 n3 tfr_prim w=1e-6 l=1e-6
            xi1 n3 n2 tfr_prim w=2e-6 l=1e-6
        .ends pcell_tfr_0
        .subckt {name} vin vop vccx vssx
            mp0 vop vin vccx vccx p w=720e-9 nf=4 m=4
            mn0 vop vin vssx vssx n w=720e-9 nf=4 m=4
            xi0 vin vop pcell_tfr_0
            xi1 vop vssx pcell_tfr_0
        .ends {name}
    """)
    setup = textwrap.dedent("""\
        POWER = vccx
        GND = vssx
        """)
    constraints = []
    example = build_example(name, netlist, setup, constraints)
    run_example(example, cleanup=False)


def test_stacked_device():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
        .subckt p_pcell_0 d g s b
            mn0 d g s1 b p w=180e-9 nf=1 m=1
            mn1 s1 g s b p w=180e-9 nf=1 m=1
        .ends p_pcell_0
        .subckt {name} vin vop vccx vss
            xi1 vop vin vccx vccx p_pcell_0 m=4
            mn0 vop vin vssx vssx n w=720e-9 nf=4 m=4
        .ends {name}
    """)
    setup = textwrap.dedent("""\
        POWER = vccx
        GND = vssx
        """)
    constraints = []
    example = build_example(name, netlist, setup, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False)

    p = run_dir / '2_primitives' / 'Switch_PMOS_p_w180_m4_st2_x2_y2.json'
    assert p.is_file(), f'Stacked transistor primitive not generated: {p}'

    shutil.rmtree(run_dir)
    shutil.rmtree(ckt_dir)
