import pytest
try:
    from .helper import *
except:
    from helper import *


@pytest.mark.nightly
def test_no_constraints():
    constraints = """[]"""
    name = f'ckt_{get_test_id()}'
    netlist, netlist_setup = comparator(name)
    example = build_example(my_dir, name, netlist, netlist_setup, constraints)
    run_example(example, n=1, cleanup=False)


@pytest.mark.nightly
def test_order_1():
    """ mp7 and mp8 should not bypass subcircuit identification """
    constraints = """[
    {"constraint": "Order", "direction": "left_to_right", "instances": ["mmp7", "mmp8"]}
]"""
    name = f'ckt_{get_test_id()}'
    netlist, netlist_setup = comparator(name)
    example = build_example(my_dir, name, netlist, netlist_setup, constraints)
    run_example(example, n=1, cleanup=False)


@pytest.mark.nightly
def test_comp_1():
    constraints = """[
    {"constraint": "GroupBlocks", "instances": ["mmn1", "mmn2"], "name": "dp"},
    {"constraint": "GroupBlocks", "instances": ["mmn3", "mmn4"], "name": "ccn"},
    {"constraint": "GroupBlocks", "instances": ["mmp5", "mmp6"], "name": "ccp"},
    {"constraint": "GroupBlocks", "instances": ["mmn11","mmp13"], "name": "invp"},
    {"constraint": "GroupBlocks", "instances": ["mmn12","mmp14"], "name": "invn"},
    {"constraint": "SymmetricBlocks", "direction" : "V", "pairs": [["mmn0"], ["dp"], ["ccp"], ["ccn"], ["mmp7", "mmp8"], ["mmp9", "mmp10"]]},
    {"constraint": "Order", "direction": "top_to_bottom", "instances": ["ccp", "ccn", "dp", "mmn0"]},
    {"constraint": "AlignInOrder", "line": "bottom", "instances": ["invn", "ccp", "invp"]}
]"""
    name = f'ckt_{get_test_id()}'
    netlist, netlist_setup = comparator(name)
    example = build_example(my_dir, name, netlist, netlist_setup, constraints)
    run_example(example, n=8, cleanup=False)


@pytest.mark.nightly
def test_comp_2():
    constraints = """[
    {"constraint": "GroupBlocks", "instances": ["mmn1", "mmn2"], "name": "dp"},
    {"constraint": "GroupBlocks", "instances": ["mmn3", "mmn4"], "name": "ccn"},
    {"constraint": "GroupBlocks", "instances": ["mmp5", "mmp6"], "name": "ccp"},
    {"constraint": "AlignInOrder", "line": "left",   "instances": ["mmn0", "dp"]},
    {"constraint": "AlignInOrder", "line": "left",   "instances": ["ccp",  "ccn"]},
    {"constraint": "AlignInOrder", "line": "bottom", "instances": ["dp",   "ccn"]}
]"""
    name = f'ckt_{get_test_id()}'
    netlist, netlist_setup = comparator(name)
    example = build_example(my_dir, name, netlist, netlist_setup, constraints)
    run_example(example, n=8, cleanup=False)
