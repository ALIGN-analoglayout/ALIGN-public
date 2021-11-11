import textwrap
try:
    from .utils import get_test_id, build_example, run_example
    from . import circuits
except BaseException:
    from utils import get_test_id, build_example, run_example
    import circuits

cleanup = False


def test_cs_grid():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.common_source_mini(name)
    setup = textwrap.dedent("""\
        POWER = vccx
        GND = vssx
        """)
    constraints = [{"constraint": "AlignInOrder", "line": "left", "instances": ["mp0", "mn0"]}]
    example = build_example(name, netlist, setup, constraints)
    run_example(example, cleanup=cleanup)
