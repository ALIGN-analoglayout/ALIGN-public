import pytest
import textwrap
try:
    from .helper import *
    from . import circuits
except:
    from helper import *
    import circuits


def test_comparator_1():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    ckt_setup = textwrap.dedent(f"""\
        POWER = vccx
        GND = vssx
        """)
    ckt_const = textwrap.dedent(f"""[\
        {{"constraint": "GroupBlocks", "instances": ["mn1", "mn2"], "name": "dp"}},
        {{"constraint": "GroupBlocks", "instances": ["mn3", "mn4"], "name": "ccn"}},
        {{"constraint": "GroupBlocks", "instances": ["mp5", "mp6"], "name": "ccp"}},
        {{"constraint": "SymmetricBlocks", "direction" : "V", "pairs": [["mn0"], ["dp"]]}},
        {{"constraint": "Order", "direction": "top_to_bottom", "instances": ["mn0", "dp"]}},
        {{"constraint": "SymmetricBlocks", "direction" : "V", "pairs": [["ccp"], ["ccn"]]}},
        {{"constraint": "Order", "direction": "top_to_bottom", "instances": ["ccp", "ccn"]}},
        {{"constraint": "AlignInOrder", "line": "bottom", "instances": ["dp",   "ccn"]}}
        ]""")
    example = build_example(my_dir, name, netlist, ckt_setup, ckt_const)
    run_example(example, n=8, cleanup=False)


def test_comparator_2():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    ckt_setup = textwrap.dedent(f"""\
        POWER = vccx
        GND = vssx
        CLOCK = clk
        """)
    ckt_const = textwrap.dedent(f"""[\
        {{"constraint": "GroupBlocks", "instances": ["mn1", "mn2"], "name": "dp"}},
        {{"constraint": "GroupBlocks", "instances": ["mn3", "mn4"], "name": "ccn"}},
        {{"constraint": "GroupBlocks", "instances": ["mp5", "mp6"], "name": "ccp"}},
        {{"constraint": "SymmetricBlocks", "direction" : "V", "pairs": [["mn0"], ["dp"]]}},
        {{"constraint": "Order", "direction": "top_to_bottom", "instances": ["mn0", "dp"]}},
        {{"constraint": "SymmetricBlocks", "direction" : "V", "pairs": [["ccp"], ["ccn"]]}},
        {{"constraint": "Order", "direction": "top_to_bottom", "instances": ["ccp", "ccn"]}},
        {{"constraint": "AlignInOrder", "line": "bottom", "instances": ["dp",   "ccn"]}}
        ]""")
    example = build_example(my_dir, name, netlist, ckt_setup, ckt_const)
    run_example(example, n=8, cleanup=False)


def test_comparator_noconst_1():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    ckt_setup = textwrap.dedent(f"""\
        POWER = vccx
        GND = vssx
        NO_CONST = {name}
        """)
    ckt_const = textwrap.dedent(f"""[]""")
    example = build_example(my_dir, name, netlist, ckt_setup, ckt_const)
    run_example(example, n=8, cleanup=False)


def test_comparator_noconst_2():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    ckt_setup = textwrap.dedent(f"""\
        POWER = vccx
        GND = vssx
        NO_CONST = {name}
        """)
    ckt_const = textwrap.dedent(f"""[\
        {{"constraint": "GroupBlocks", "instances": ["mn1", "mn2"], "name": "dp"}},
        {{"constraint": "SymmetricBlocks", "direction" : "V", "pairs": [["mn0"], ["dp"]]}}
        ]""")
    example = build_example(my_dir, name, netlist, ckt_setup, ckt_const)
    run_example(example, n=8, cleanup=False)
