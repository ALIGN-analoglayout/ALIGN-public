import textwrap
try:
    from .helper import get_test_id, build_example, run_example
    from . import circuits
except BaseException:
    from helper import *
    import circuits


def test_comparator_1():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    setup = textwrap.dedent(f"""\
        POWER = vccx
        GND = vssx
        """)
    constraints = textwrap.dedent(f"""[\
        {{"constraint": "GroupBlocks", "instances": ["mn1", "mn2"], "name": "dp"}},
        {{"constraint": "GroupBlocks", "instances": ["mn3", "mn4"], "name": "ccn"}},
        {{"constraint": "GroupBlocks", "instances": ["mp5", "mp6"], "name": "ccp"}},
        {{"constraint": "SymmetricBlocks", "direction" : "V", "pairs": [["mn0"], ["dp"]]}},
        {{"constraint": "Order", "direction": "top_to_bottom", "instances": ["mn0", "dp"]}},
        {{"constraint": "SymmetricBlocks", "direction" : "V", "pairs": [["ccp"], ["ccn"]]}},
        {{"constraint": "Order", "direction": "top_to_bottom", "instances": ["ccp", "ccn"]}},
        {{"constraint": "AlignInOrder", "line": "bottom", "instances": ["dp",   "ccn"]}}
        ]""")
    example = build_example(name, netlist, setup, constraints)
    run_example(example)


def test_comparator_2():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    setup = textwrap.dedent(f"""\
        POWER = vccx
        GND = vssx
        CLOCK = clk
        """)
    constraints = textwrap.dedent(f"""[\
        {{"constraint": "GroupBlocks", "instances": ["mn1", "mn2"], "name": "dp"}},
        {{"constraint": "GroupBlocks", "instances": ["mn3", "mn4"], "name": "ccn"}},
        {{"constraint": "GroupBlocks", "instances": ["mp5", "mp6"], "name": "ccp"}},
        {{"constraint": "SymmetricBlocks", "direction" : "V", "pairs": [["mn0"], ["dp"]]}},
        {{"constraint": "Order", "direction": "top_to_bottom", "instances": ["mn0", "dp"]}},
        {{"constraint": "SymmetricBlocks", "direction" : "V", "pairs": [["ccp"], ["ccn"]]}},
        {{"constraint": "Order", "direction": "top_to_bottom", "instances": ["ccp", "ccn"]}},
        {{"constraint": "AlignInOrder", "line": "bottom", "instances": ["dp",   "ccn"]}}
        ]""")
    example = build_example(name, netlist, setup, constraints)
    run_example(example)


def test_comparator_noconst_1():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    setup = textwrap.dedent(f"""\
        POWER = vccx
        GND = vssx
        NO_CONST = {name}
        """)
    constraints = textwrap.dedent(f"""[]""")
    example = build_example(name, netlist, setup, constraints)
    run_example(example)


def test_comparator_noconst_2():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    setup = textwrap.dedent(f"""\
        POWER = vccx
        GND = vssx
        NO_CONST = {name}
        """)
    constraints = textwrap.dedent(f"""[\
        {{"constraint": "GroupBlocks", "instances": ["mn1", "mn2"], "name": "dp"}},
        {{"constraint": "SymmetricBlocks", "direction" : "V", "pairs": [["mn0"], ["dp"]]}}
        ]""")
    example = build_example(name, netlist, setup, constraints)
    run_example(example)


def test_ota_six():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.ota_six(name)
    setup = constraints = """[]"""
    example = build_example(name, netlist, setup, constraints)
    run_example(example)


def test_tia():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.tia(name)
    setup = constraints = """[]"""
    example = build_example(name, netlist, setup, constraints)
    run_example(example)
